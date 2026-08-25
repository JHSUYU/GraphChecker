package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourceSelectorContract;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.Goal;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;

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
import java.util.TreeMap;
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
 * <p>The scheduler only groups statically declared protocol equalities.
 * Runtime read-from and handoff evidence remain exact edge/session records
 * for the composer; no offline channel-local order is synthesized here.</p>
 */
public final class ConcolicScheduler {
    private static final Pattern LOCAL_CELL = Pattern.compile(
            "^(<.+>)::([^#]+)(?:#.*)?$");
    private ConcolicScheduler() {
    }

    public static void main(String[] args) throws Exception {
        Arguments arguments = Arguments.parse(args);
        Result result = arguments.targetFirst
                ? scheduleTargetFirst(arguments) : schedule(arguments);
        if (result.executionTasks.isEmpty()) {
            throw new IllegalStateException(noCandidateDiagnostic(arguments,
                    RuntimePlanArtifact.read(arguments.regionPlan).plans()));
        }
    }

    public static Result schedule(Arguments arguments) throws IOException {
        if (arguments.targetFirst) {
            return scheduleTargetFirst(arguments);
        }
        LoadedInputs loaded = loadInputs(arguments);
        Result result = scheduleLoaded(arguments, loaded, null);
        loaded.symbolicInputs.bindSourceSelectors(result.executionTasks);
        loaded.symbolicInputs.validateSourceCoverage(result.executionTasks);
        writeResult(arguments.outputDirectory, result);
        return result;
    }

    private static LoadedInputs loadInputs(Arguments arguments)
            throws IOException {
        requireFile(arguments.regionPlan, "region plan");
        requireFile(arguments.refinedGraph, "runtime-refined graph");
        Files.createDirectories(arguments.outputDirectory);

        JsonObject regionPlanIdentity = arguments.targetFirst
                ? artifactIdentity(arguments.regionPlan) : null;
        RuntimePlanArtifact runtimePlan = RuntimePlanArtifact.read(
                arguments.regionPlan);
        List<JsonObject> regions = runtimePlan.regions();
        if (regions.isEmpty()) {
            throw new IOException("runtime plan has no region port catalog: "
                    + arguments.regionPlan);
        }
        List<JsonObject> regionPlans = runtimePlan.plans();
        if (regionPlans.isEmpty()) {
            throw new IOException("runtime plan contains no region plans: "
                    + arguments.regionPlan);
        }
        List<JsonObject> summaries = arguments.summaries == null
                ? Collections.<JsonObject>emptyList()
                : readJsonl(arguments.summaries);
        List<JsonObject> refinedGraph = readJsonl(arguments.refinedGraph);
        requireRefinedGraph(refinedGraph);
        DefinitionIndex definitions = DefinitionIndex.from(refinedGraph);
        SymbolicInputSelection symbolicInputs =
                SymbolicInputSelection.read(arguments.symbolicInputs,
                        regions);

        Map<String, Region> regionIndex = regionIndex(regions);
        if (regionPlanIdentity != null) {
            requireArtifactIdentity(arguments.regionPlan,
                    regionPlanIdentity, "region plan changed while loading");
        }
        return new LoadedInputs(regionPlans, summaries, regionIndex,
                definitions, regionPlanIdentity, symbolicInputs);
    }

    private static Result scheduleLoaded(
            Arguments arguments, LoadedInputs loaded,
            ProducerOutputProjection producerProjection) throws IOException {
        List<Candidate> candidates = candidates(arguments,
                loaded.regionPlans, loaded.regionIndex,
                loaded.definitions, producerProjection);
        Collections.sort(candidates, Candidate.ORDER);

        LoopBoundPolicy loopBound = declaredLoopBounds(
                arguments.maxLoopIterations, loaded.regionPlans);
        Result result = new Result();
        Set<String> scheduledOutputOccurrences = new LinkedHashSet<>();
        for (Candidate candidate : candidates) {
            JsonArray taskInputActions = loaded.symbolicInputs
                    .includeTargetSourceFrontier(
                            candidate.goal.plan().regionId(),
                            candidate.inputActions,
                            candidate.targetSourceFrontier);
            JsonArray selectedInputs = loaded.symbolicInputs.select(
                    candidate.goal.plan().regionId(), taskInputActions);
            String taskId = candidate.seedTaskId(selectedInputs);
            JsonObject taskQueryOccurrence = queryOccurrenceWithInputs(
                    candidate.queryOccurrence, selectedInputs);
            OutputClosureContract outputContract = candidate.outputContract();
            JsonObject captured = outputContract != null ? null
                    : exactTargetSummary(candidate, loaded.summaries);
            // A summary is evidence a previous replay already produced; making
            // its solver query consumes no replay-job slot.  In particular,
            // the pass-two scheduler sees the whole occurrence catalog, and a
            // target occurrence may sort after maxJobs unrelated candidates.
            // Stopping the scan at that cap silently discarded its exact
            // TARGET_REACH_EVENT and left the closed target worklist with no
            // seed query.  The cap bounds newly scheduled VM work only.
            if (captured != null && outputContract == null) {
                result.queries.add(branchQuery(candidate, captured,
                        taskId, taskQueryOccurrence));
            }
            if (result.executionTasks.size() >= arguments.maxJobs) {
                continue;
            }
            JsonArray edgeBindings = objectRows(
                    candidate.goal.edgeBindingsView());
            if (candidate.targetEdgeBindings != null) {
                edgeBindings = candidate.targetEdgeBindings.deepCopy();
            }
            edgeBindings = mergeEdgeBindings(edgeBindings);
            if (producerProjection != null) {
                edgeBindings = selectedProducerEdgeBindings(edgeBindings,
                        producerProjection.edgeIds());
            }
            // Output alternatives are case obligations inside one coarse
            // occurrence task.  Seeing a second candidate here means a plan
            // producer failed to publish their union; never recover by
            // inventing a second VM task or instrumentation selector.
            if (outputContract != null && !scheduledOutputOccurrences.add(
                    candidate.goal.plan().occurrenceId())) {
                throw new IllegalStateException(
                        "producer occurrence emitted more than one union task: "
                                + candidate.goal.plan().occurrenceId());
            }
            ExecutionTask scheduled = ExecutionTask.create(candidate.goal,
                    taskId, selectedInputs,
                    candidate.branches, edgeBindings,
                    loopBound, candidate.ready,
                    outputContract);
            JsonObject executionTask = scheduled.json();
            promoteSelectedReplayEntry(executionTask, outputContract);
            loaded.symbolicInputs.annotate(executionTask,
                    taskInputActions, selectedInputs);
            loaded.symbolicInputs.annotateSources(executionTask,
                    candidate.goal.plan().regionId(), outputContract,
                    taskInputActions);
            if (outputContract != null) {
                // The timeline annotation is derived after the immutable
                // planner goal was decoded.  Replace only that canonical
                // envelope; the VM task semantics and captures are unchanged.
                executionTask.add(OutputClosureContract.FIELD,
                        outputContract.toJson());
            }
            declareMapStateCarriers(executionTask, selectedInputs, candidate,
                    loaded.regionIndex.get(
                            candidate.goal.plan().regionId()));
            declareReadFromCarriers(executionTask, edgeBindings,
                    candidate.goal.plan().occurrenceId());
            if (candidate.goal.kind().capturesTargetReach()) {
                // The branch event this occurrence must decide.  Deciding it
                // is evidence the case records; the occurrence still runs to
                // its own terminal so the effects after it are not lost.
                JsonObject target = new JsonObject();
                target.addProperty("siteId", candidate.target.siteId);
                target.addProperty("occurrence",
                        candidate.target.selectedOccurrence);
                executionTask.add("targetBranch", target);
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

    /**
     * Promotes the one exact continuation shared by selected output members.
     * Missing metadata keeps the region root; disagreement is not a task.
     */
    static void promoteSelectedReplayEntry(
            JsonObject task, OutputClosureContract closure) {
        if (task == null || closure == null) return;
        JsonObject selected = null;
        String selectedPort = "";
        boolean missing = false;
        for (OutputClosureContract.Member member : closure.members()) {
            JsonObject entry = object(member.slice(),
                    ExecutionTask.REPLAY_ENTRY);
            if (entry.size() == 0) {
                missing = true;
                continue;
            }
            String method = string(entry, "method");
            String receiver = string(entry, "receiverClass");
            if (method.isEmpty() || receiver.isEmpty()) {
                throw new IllegalArgumentException(
                        "selected output replay entry is incomplete: "
                                + member.portId());
            }
            if (selected == null) {
                selected = entry.deepCopy();
                selectedPort = member.portId();
            } else if (!selected.equals(entry)) {
                throw new IllegalArgumentException(
                        "selected outputs require incompatible replay "
                                + "continuations: task="
                                + string(task, "taskId") + " port="
                                + member.portId() + " selectedPort="
                                + selectedPort + " selected=" + selected
                                + " conflicting=" + entry);
            }
        }
        if (selected == null) return;
        if (missing) {
            throw new IllegalArgumentException(
                    "selected outputs mix declared and undeclared replay "
                            + "continuations");
        }
        JsonObject held = object(task, ExecutionTask.REPLAY_ENTRY);
        if (held.size() > 0 && !held.equals(selected)) {
            throw new IllegalArgumentException(
                    "selected output continuation conflicts with goal "
                            + "replay entry");
        }
        task.add(ExecutionTask.REPLAY_ENTRY, selected);
        rebaseSelectedAccessorOccurrences(task);
    }

    /**
     * Re-addresses repeated accessor reads from the selected continuation.
     *
     * <p>The runtime occurrence counter starts at one when the promoted
     * replay entry opens.  Planner rows also retain the absolute occurrence
     * observed in the enclosing coarse activation for provenance; using that
     * absolute ordinal in a continuation task makes every selected accessor
     * miss.  The final execution task therefore carries only the local
     * selector as {@code replayOccurrence}.</p>
     */
    private static void rebaseSelectedAccessorOccurrences(JsonObject task) {
        for (JsonElement element : array(task, InputActionCatalog.FIELD)) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            if (!"SYMBOLIC".equals(string(action, "mode"))
                    || !"FIELD_ACCESS".equals(
                    string(action, "bindingMode"))
                    || string(action, "accessorCallerMethod").isEmpty()
                    || string(action,
                    "accessorImplementationMethod").isEmpty()) {
                continue;
            }
            int localOccurrence = integer(action,
                    "helperActivationBoundedOccurrence", -1);
            if (localOccurrence > 0) {
                action.addProperty("replayOccurrence", localOccurrence);
            }
        }
    }

    /** Keeps exactly the causal ledger selected with a producer projection. */
    private static JsonArray selectedProducerEdgeBindings(
            JsonArray bindings, Set<String> selectedEdgeIds) {
        JsonArray selected = new JsonArray();
        Set<String> found = new LinkedHashSet<>();
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String edgeId = string(binding, "edgeId");
            if (selectedEdgeIds.contains(edgeId) && found.add(edgeId)) {
                selected.add(binding.deepCopy());
            }
        }
        if (!found.equals(selectedEdgeIds)) {
            Set<String> missing = new LinkedHashSet<>(selectedEdgeIds);
            missing.removeAll(found);
            throw new IllegalArgumentException(
                    "selected producer edge bindings are absent: "
                            + missing);
        }
        return selected;
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
                        loaded.regionPlans,
                        loaded.symbolicInputs::selectedForDiscovery,
                        loaded.symbolicInputs::sourceOutputCellsForDiscovery);
        if (workflow.scheduledTaskCount() > arguments.maxJobs) {
            throw new IOException("selected exact closure exceeds max jobs: "
                    + workflow.scheduledTaskCount() + " > "
                    + arguments.maxJobs);
        }

        Map<String, JsonObject> tasks = new LinkedHashMap<>();
        Map<String, JsonObject> queries = new LinkedHashMap<>();
        for (RuntimeWorkflowDiscovery.Selection selection
                : workflow.selections()) {
            Result selected;
            try {
                selected = scheduleLoaded(
                        arguments.forSelection(selection), loaded,
                        selection.producerProjection);
            } catch (IllegalArgumentException failure) {
                String projection = selection.producerProjection == null
                        ? "TARGET" : CanonicalJson.render(
                        selection.producerProjection.json());
                throw new IOException("target-first selection is not "
                        + "executable: campaign=" + selection.campaignId
                        + " projection=" + projection, failure);
            }
            if (selected.executionTasks.size() != 1) {
                throw new IOException("target-first selection emitted "
                        + selected.executionTasks.size()
                        + " execution tasks; campaign="
                        + selection.campaignId);
            }
            JsonObject task = selected.executionTasks.get(0);
            putUnique(tasks, task, "taskId");
            for (JsonObject query : selected.queries) {
                indexTargetQuery(queries, query);
            }
        }
        Result result = new Result();
        result.executionTasks.addAll(sortedValues(tasks));
        result.queries.addAll(sortedValues(queries));
        loaded.symbolicInputs.bindSourceSelectors(result.executionTasks);
        loaded.symbolicInputs.validateSourceCoverage(result.executionTasks);
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
        // The integrity-checked index is the commit record.  Publish it only
        // after every artifact it describes is durable. Target and producer
        // selections live only in this index; parallel TSV mirrors used to
        // repeat the same identities without adding authority.
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

    /** The exact target-query aggregation seam used by target-first. */
    static void indexTargetQuery(Map<String, JsonObject> queries,
                                 JsonObject query) throws IOException {
        putUnique(queries, query, "queryKey");
    }

    private static List<JsonObject> sortedValues(
            Map<String, JsonObject> values) {
        List<String> keys = new ArrayList<>(values.keySet());
        Collections.sort(keys);
        List<JsonObject> result = new ArrayList<>();
        for (String key : keys) result.add(values.get(key));
        return result;
    }

    /**
     * Declares this task's selected associative containers as
     * {@code MAP_STATE} shared carriers.
     *
     * <p>README Step 2 asks a selected {@code Map} mutation to publish an
     * immutable whole-map state and a selected {@code Map.get} to bind to the
     * state it may have observed.  The VM does that only for a map some task
     * <em>selected</em>, and it accepts a selection only from inside a region:
     * an application that selects its map before the map's first write - which
     * is the only ordering under which the version chain starts at the map's
     * initial state - is necessarily outside every region at that moment and
     * is refused.  Both properties survive when the task plan declares the
     * carrier: {@code selectDeclaredSharedCarriers} runs at region entry,
     * before the region's own work, which is inside a region and still before
     * the writes this activation performs.</p>
     *
     * <p>What is declared is not searched for.  A port is a carrier only when
     * the region catalog already says its value is an associative container
     * and already states the receiver-rooted path the replay walks to reach
     * it; the declaring field on that path is the cross-run join, not the
     * location.  A port with a container type but no such path declares
     * nothing, because a carrier the replay cannot reach would be a guess
     * about which map was meant.</p>
     *
     * <p>Reads and writes are declared alike.  A writer that does not select
     * publishes no version, so a reader that selects alone would resolve
     * against a store missing exactly the write it took; the region's own
     * container outputs for this occurrence are therefore declared next to its
     * inputs.</p>
     */
    private static void declareMapStateCarriers(JsonObject task,
                                                JsonArray selectedInputs,
                                                Candidate candidate,
                                                Region region) {
        Map<String, JsonObject> declared = new LinkedHashMap<>();
        // Planner carriers describe the occurrence catalog.  A selected task
        // derives its carriers again from its projected inputs, outputs and
        // exact edge ledger below; copying the catalog would retain concrete
        // setup fields belonging only to an unselected producer phase.
        for (JsonElement element : selectedInputs) {
            if (!element.isJsonObject()) continue;
            JsonObject input = element.getAsJsonObject();
            if (InputActionCatalog.Mode.SYMBOLIC.name().equals(
                    string(input, "mode"))) {
                declareMapStateCarrier(declared, input);
            }
        }
        OutputClosureContract selectedClosure = candidate.outputContract();
        if (region != null && selectedClosure != null) {
            String occurrence = candidate.goal.plan().occurrenceId();
            for (JsonObject output : region.outputRows()) {
                if (occurrence.equals(string(output, "occurrenceId"))
                        && selectedClosure.outputPorts().contains(
                        string(output, "portId"))) {
                    declareMapStateCarrier(declared, output);
                }
            }
        }
        JsonArray carriers = new JsonArray();
        for (JsonObject carrier : declared.values()) {
            carriers.add(carrier.deepCopy());
        }
        if (carriers.size() == 0) {
            task.remove(ExecutionTask.SHARED_CARRIERS);
        } else {
            task.add(ExecutionTask.SHARED_CARRIERS, carriers);
        }
    }

    /**
     * Declares the shared locations this task's recorded read-from edges name.
     *
     * <p>A location publishes versions and answers reads only while some task
     * has selected it, and its store is read back when a selecting activation
     * finishes. Declaring the writers alone therefore records the writes and
     * never the read: the writer's read-out happens before the reader ran, so
     * its version store shows an empty read log, every candidate stays a
     * candidate, and the composition refuses the edge as
     * {@code SelectedEdgeCandidateOnly} - a read whose writer universe is
     * open for no reason but bookkeeping.</p>
     *
     * <p>The admission key is the edge the trace recorded, not a roster of
     * activations an earlier stage nominated. A roster can only fail by
     * omission, and an omitted endpoint publishes nothing to notice: no
     * version, no read, and therefore no gap either. Every candidate
     * read-from binding this task carries declares its own leaf field on
     * whichever end of the edge this occurrence sits, so both ends select and
     * the store the last of them reads back holds the whole history.</p>
     *
     * <p>An associative leaf is selected here from the exact read-from edge,
     * because an output relation may mutate a map without making that map a
     * symbolic input.  Both endpoints then bind {@code MAP_STATE} at the
     * instrumented field access.  No receiver path or same-named heap search
     * is inferred.</p>
     */
    static void declareReadFromCarriers(JsonObject task,
                                        JsonArray edgeBindings,
                                        String occurrence) {
        if (occurrence == null || occurrence.isEmpty()) return;
        Map<String, JsonObject> declared = new LinkedHashMap<>();
        for (JsonElement element
                : array(task, ExecutionTask.SHARED_CARRIERS)) {
            if (element.isJsonObject()) {
                JsonObject carrier = element.getAsJsonObject();
                declared.put(mapCarrierKey(carrier), carrier);
            }
        }
        int before = declared.size();
        for (JsonElement element : edgeBindings) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String field = string(binding, RecordedReadFrom.EDGE_FIELD);
            if (field.isEmpty()
                    || !occurrence.equals(string(binding, "fromOccurrenceId"))
                    && !occurrence.equals(
                    string(binding, "toOccurrenceId"))) {
                continue;
            }
            JsonArray declarations = array(binding,
                    "fieldPathDeclarations");
            if (declarations.size() == 0) continue;
            FieldPathSpec.DeclaredField leaf = FieldPathSpec.declaredField(
                    declarations.get(declarations.size() - 1).getAsString());
            if (leaf == null || !field.equals(RecordedReadFrom.fieldKey(
                    leaf.owner(), leaf.name()))) {
                continue;
            }
            JavaContainerTypes.Shape shape = JavaContainerTypes.shape(
                    leaf.type());
            if (shape != JavaContainerTypes.Shape.NONE
                    && shape != JavaContainerTypes.Shape.ASSOCIATIVE) {
                continue;
            }
            String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                    leaf.type());
            if (descriptor.isEmpty()) continue;
            JsonObject carrier = new JsonObject();
            carrier.addProperty("kind",
                    shape == JavaContainerTypes.Shape.ASSOCIATIVE
                            ? SharedStateEvidence.LOCATION_KIND_MAP_STATE
                            : "DECLARED_FIELD");
            carrier.addProperty("declaringClass", leaf.owner());
            carrier.addProperty("fieldName", leaf.name());
            carrier.addProperty("descriptor", descriptor);
            // The owner is the object the instrumented access in this
            // activation touched, and nothing else: the runtime binds this
            // shape at the exact field access rather than searching the heap
            // for a same-named receiver.
            carrier.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
            carrier.add("fieldPath", new JsonArray());
            declared.putIfAbsent(mapCarrierKey(carrier), carrier);
        }
        if (declared.size() == before) return;
        JsonArray carriers = new JsonArray();
        for (JsonObject carrier : declared.values()) {
            carriers.add(carrier.deepCopy());
        }
        task.add(ExecutionTask.SHARED_CARRIERS, carriers);
    }

    /** One declaration per (location kind, declaring field, receiver path). */
    private static String mapCarrierKey(JsonObject carrier) {
        return string(carrier, "kind") + "\n"
                + string(carrier, "declaringClass") + "#"
                + string(carrier, "fieldName") + ":"
                + string(carrier, "descriptor") + "\n"
                + array(carrier, "fieldPath");
    }

    static void declareMapStateCarrier(
            Map<String, JsonObject> declared, JsonObject port) {
        String javaType = firstNonBlank(string(port, "javaType"),
                string(port, "materializedJavaType"));
        if (JavaContainerTypes.shape(javaType)
                != JavaContainerTypes.Shape.ASSOCIATIVE) {
            return;
        }
        // A receiver-rooted port is reachable at region entry.  An observed
        // field receiver is equally exact but becomes reachable only at the
        // instrumented access itself; the runtime binds that form through
        // sourceKind=ACTIVATION_FIELD_RECEIVER and never searches the heap.
        // These are distinct addresses and therefore carry distinct paths.
        String rootKind = string(port, "rootKind");
        boolean accessOwner = "OBSERVED_FIELD_RECEIVER".equals(rootKind)
                && "ACTIVATION_FIELD_RECEIVER".equals(
                string(port, "sourceKind"));
        if (!"RECEIVER".equals(rootKind) && !accessOwner) {
            return;
        }
        JsonArray path = array(port, "fieldPath");
        JsonArray declarations = array(port, "fieldPathDeclarations");
        if (path.size() == 0 || declarations.size() == 0) {
            // No receiver-rooted path is no address: the replay would have to
            // find the map, and finding it is what this design forbids.
            return;
        }
        JsonElement last = declarations.get(declarations.size() - 1);
        FieldPathSpec.DeclaredField field = last.isJsonPrimitive()
                ? FieldPathSpec.declaredField(last.getAsString()) : null;
        if (field == null) {
            return;
        }
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                field.type());
        if (descriptor.isEmpty()) {
            return;
        }
        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        carrier.addProperty("declaringClass", field.owner());
        carrier.addProperty("fieldName", field.name());
        carrier.addProperty("descriptor", descriptor);
        if (accessOwner) {
            carrier.addProperty("sourceKind",
                    "ACTIVATION_FIELD_RECEIVER");
            carrier.add("fieldPath", new JsonArray());
        } else {
            carrier.add("fieldPath", path.deepCopy());
        }
        declared.putIfAbsent(mapCarrierKey(carrier), carrier);
    }

    /**
     * One causal edge can be represented by a refined runtime row and by a
     * compact closure row.  They share an edgeId and may carry complementary
     * fields, so join compatible views without weakening conflict checks.
     */
    private static JsonArray objectRows(JsonArray source) {
        JsonArray result = new JsonArray();
        for (JsonElement element : source) {
            if (element.isJsonObject()) {
                result.add(element.deepCopy());
            }
        }
        return result;
    }

    private static JsonArray mergeEdgeBindings(JsonArray bindings)
            throws IOException {
        Map<String, JsonObject> rows = new LinkedHashMap<>();
        mergeEdgeBindings(rows, bindings);
        JsonArray result = new JsonArray();
        for (JsonObject row : rows.values()) result.add(row.deepCopy());
        return result;
    }

    private static void mergeEdgeBindings(
            Map<String, JsonObject> rows, JsonArray bindings)
            throws IOException {
        for (JsonElement element : bindings) {
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
            for (Map.Entry<String, JsonElement> field : row.entrySet()) {
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

    private static List<Candidate> candidates(Arguments arguments,
                                              List<JsonObject> regionPlans,
                                              Map<String, Region> regions,
                                              DefinitionIndex definitions,
                                              ProducerOutputProjection
                                                      producerProjection)
            throws IOException {
        List<Candidate> result = new ArrayList<>();
        for (JsonObject encoded : regionPlans) {
            // Target-first scheduling selects one exact occurrence at a
            // time.  Filter on the plan row's top-level identity before
            // decoding its potentially large output-closure envelope; doing
            // the filter afterwards re-hashes every unrelated closure for
            // every selected occurrence.
            if (!arguments.occurrenceId.isEmpty()
                    && !arguments.occurrenceId.equals(
                    string(encoded, "occurrenceId"))) {
                continue;
            }
            if (!arguments.regionId.isEmpty()
                    && !arguments.regionId.equals(
                    string(encoded, "regionId"))) {
                continue;
            }
            RegionInstancePlan plan = RegionInstancePlan.decode(encoded);
            Region region = regions.get(plan.regionId());
            if (region == null) {
                continue;
            }
            if (!arguments.occurrenceId.isEmpty()
                    && !plan.containsOccurrence(
                    arguments.occurrenceId)) {
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
                        definitions, producerProjection, encoded);
            }
        }
        return result;
    }

    /**
     * The per-loop {@code K_L} the region plan declares, as one contract.
     *
     * <p>A loop that declares the inherited bound is not recorded: it runs to
     * the same {@code K_L} either way, and recording it would move the
     * contract identity of every campaign that declares nothing.  Two plan
     * rows that state different bounds for one loop are refused - one loop
     * has one prefix, and picking either would be resolving a declaration by
     * which row was read first.</p>
     */
    static LoopBoundPolicy declaredLoopBounds(
            int inheritedBound, List<JsonObject> regionPlans) {
        Map<String, Integer> declared = new TreeMap<>();
        for (JsonObject row : regionPlans) {
            for (JsonElement element : array(row,
                    BoundedLoopComposition.PLAN_FIELD)) {
                if (!element.isJsonObject()) continue;
                JsonObject loop = element.getAsJsonObject();
                String loopSiteId = string(loop,
                        LoopBoundPolicy.LOOP_SITE_ID);
                int bound = integer(loop, LoopBoundPolicy.LOOP_BODY_BOUND, 0);
                if (loopSiteId.isEmpty() || bound < 1) continue;
                Integer held = declared.put(loopSiteId, bound);
                if (held != null && held.intValue() != bound) {
                    throw new IllegalStateException(
                            BoundedLoopComposition.LOOP_BODY_BOUND_DISAGREES
                                    + ": loop " + loopSiteId + " is planned"
                                    + " under K_L=" + held + " and K_L="
                                    + bound + "; one loop has one prefix");
                }
            }
        }
        declared.values().removeIf(bound -> bound == inheritedBound);
        return LoopBoundPolicy.cfgBackedges(inheritedBound, declared);
    }

    private static void appendGoalCandidates(
            Arguments arguments, List<Candidate> result,
            Goal goal, Region region, DefinitionIndex definitions,
            ProducerOutputProjection producerProjection,
            JsonObject planRow)
            throws IOException {
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
                if (producerProjection != null
                        && !selectsProducerOccurrence(
                        goal, producerProjection)) {
                    return;
                }
                if (producerProjection != null) {
                    outputClosure = OutputClosureCodec.project(outputClosure,
                            producerProjection.outputPorts());
                }
                JsonArray branches = goal.branches();
                JsonArray inputActions = materializationPlan(
                        goal, goal.symbolize(), definitions, definitionMethods,
                        outputClosure, branches,
                        goal.plan().occurrenceId(),
                        Collections.<String>emptySet());
                result.add(new Candidate(goal, branches,
                        TargetBranch.outputCapture(), true,
                        inputActions, true,
                        goal.plan().occurrenceId(),
                        new JsonObject(), null, outputClosure,
                        new JsonArray()));
                return;
            }
            if (producerProjection != null) {
                throw new IllegalArgumentException("producer projection "
                        + "cannot select a target reach goal");
            }
            goal.rejectOutputClosure();
            JsonArray branches = goal.branches();
            int eligibleFailureTargets = 0;
            Set<String> guardedTargets = new LinkedHashSet<>();
            for (JsonElement element : branches) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (!eligibleFailureTarget(branch)) continue;
                eligibleFailureTargets++;
                for (JsonElement cell : array(branch,
                        RuntimeSelectedRegionFinalizer
                                .FAILURE_TARGET_CELLS)) {
                    if (cell.isJsonPrimitive()) {
                        guardedTargets.add(cell.getAsString());
                    }
                }
            }
            // What may not be ambiguous is the failure this occurrence is
            // planned for, not how many conditional sites decide it.
            // `if (p && q) throw` is lowered to two sites, both eligible,
            // both carrying an exception guard into the same throw: they are
            // the conjuncts of one target predicate, and counting sites read
            // that as two targets and refused the workflow.  The rule is the
            // one the planner already publishes the evidence for - the
            // distinct throws the eligible guards control.
            if (eligibleFailureTargets == 0 || guardedTargets.size() > 1) {
                throw new IllegalArgumentException(
                        "UNSUPPORTED_AMBIGUOUS_TARGET_PATH: expected one "
                                + "guarded failure target; found "
                                + (guardedTargets.size() > 1
                                ? guardedTargets.size()
                                + " guarded failure targets"
                                : eligibleFailureTargets
                                + " eligible failure targets"));
            }
            String queryInstance = targetQueryInstance(arguments, goal);
            // One target task drives the bounded path worklist for the whole
            // guarded throw.  Ordinary inputs remain branch-local below, but
            // manually declared source fields that can move any conjunct of
            // this fatal predicate must be present from the first replay: the
            // worklist does not mint a new task when a shallower flip exposes
            // a deeper guard.
            JsonArray targetSourceFrontier = materializationPlan(goal,
                    goal.symbolize(), definitions, definitionMethods, null,
                    branches, queryInstance, arguments.targetEdgeIds);
            for (int index = 0; index < branches.size(); index++) {
                JsonElement element = branches.get(index);
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject branch = element.getAsJsonObject();
                String siteId = string(branch, "siteId");
                if (!bool(branch, "failureTarget", false)) {
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
                boolean explore = "EXPLORE".equals(string(branch, "policy"));
                if (hasWitness && !explore) {
                    continue;
                }
                // A target task explores exactly one branch; the rest of the
                // slice is replayed prefix.  Materialization is decided
                // against that slice so a leaf is not kept symbolic for a
                // decision this task never reopens.
                JsonArray reachSlice = targetReachBranchSlice(branches,
                        target);
                JsonArray inputActions = materializationPlan(goal,
                        goal.symbolize(), definitions,
                        definitionMethods, null, reachSlice,
                        queryInstance, arguments.targetEdgeIds);
                inputActions = targetSymbolicFrontier(goal, inputActions,
                        queryInstance);
                JsonArray targetBindings = targetInputBindings(goal,
                        inputActions, queryInstance,
                        arguments.targetEdgeIds);
                result.add(new Candidate(goal,
                        reachSlice, target,
                        hasWitness, inputActions, true,
                        queryInstance,
                        targetQueryOccurrence(arguments, goal,
                                inputActions, targetBindings),
                        targetBindings, null, targetSourceFrontier));
            }
    }

    private static boolean eligibleFailureTarget(JsonObject branch) {
        if (!bool(branch, "failureTarget", false)
                || bool(branch, "loopControlGuard", false)
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
        return arguments.occurrenceId.isEmpty()
                ? goal.plan().occurrenceId()
                : arguments.occurrenceId;
    }

    private static JsonObject targetQueryOccurrence(
            Arguments arguments, Goal goal, JsonArray actions,
            JsonArray bindings) {
        String selected = targetQueryInstance(arguments, goal);
        if (!selected.equals(goal.plan().occurrenceId())) {
            throw new IllegalArgumentException(
                    "target goal does not match selected occurrence "
                            + selected);
        }
        JsonObject result = new JsonObject();
        result.addProperty("occurrenceId", selected);
        Set<String> selectedPorts = new LinkedHashSet<>();
        for (JsonElement element : actions) {
            if (!element.isJsonObject()) continue;
            String port = string(element.getAsJsonObject(), "symbol");
            if (!port.isEmpty()) selectedPorts.add(port);
        }
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            String port = string(element.getAsJsonObject(), "toInputPort");
            if (!port.isEmpty()) selectedPorts.add(port);
        }
        JsonArray ports = new JsonArray();
        for (String port : selectedPorts) ports.add(port);
        result.add("inputPorts", ports);
        JsonArray ids = new JsonArray();
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            String edgeId = string(element.getAsJsonObject(), "edgeId");
            if (!edgeId.isEmpty()) ids.add(edgeId);
        }
        result.add("bindingIds", ids);
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
        for (JsonElement element : goal.edgeBindingsView()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (queryInstance.equals(string(binding, "toOccurrenceId"))
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
        if (queryInstance.equals(goal.plan().occurrenceId())
                && canonicalInput != null
                && !canonicalInput.trim().isEmpty()) {
            result.add(canonicalInput);
        }
        return result;
    }

    /** Package-visible for the focused target-component admission contract. */
    static JsonArray targetInputBindings(
            Goal goal, JsonArray actions, String queryInstance,
            Set<String> selectedEdgeIds) {
        Set<String> exactPorts = new LinkedHashSet<>();
        for (JsonElement element : actions) {
            if (!element.isJsonObject()) continue;
            exactPorts.addAll(exactInputPorts(goal,
                    string(element.getAsJsonObject(), "symbol"),
                    queryInstance));
        }
        JsonArray result = new JsonArray();
        for (JsonElement element : goal.edgeBindingsView()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            boolean selectedHandoff = selectedEdgeIds.contains(
                    string(binding, "edgeId"))
                    && selectedWorkflowHandoffBinding(binding);
            if (queryInstance.equals(string(binding,
                    "toOccurrenceId"))
                    && (exactPorts.contains(string(binding, "toInputPort"))
                    || selectedHandoff)
                    && (selectedEdgeIds.isEmpty()
                    || selectedEdgeIds.contains(string(binding, "edgeId")))
                    && (selectedHandoff
                    ? AutomaticRegionEdge.schedulableProducerBinding(binding)
                    : AutomaticRegionEdge
                    .trustedRuntimeCompositionBinding(binding))) {
                result.add(binding.deepCopy());
            }
        }
        return result;
    }

    /**
     * An exact component edge is target topology, not a local symbolic root.
     * It therefore survives target task selection even though the component
     * has no Java input action; only the replayed VM VALUE_HANDOFF may later
     * authorize its value.
     */
    private static boolean handoffComponentBinding(JsonObject binding) {
        return !string(binding,
                CommunicationCatalogContract.PORT_COMPONENT_OF).isEmpty()
                && !string(binding,
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH)
                .isEmpty()
                && !string(binding,
                CommunicationCatalogContract.PORT_ENCODING_AUTHORITY)
                .isEmpty();
    }

    /**
     * A selected response delivery remains part of the replay topology even
     * when the branch currently being reopened does not consume its value.
     *
     * <p>This distinction matters for a nested target such as
     * {@code if (localGate) if (rpcValue > limit) throw}: the seed replay can
     * observe only the outer local gate, but the two RPC calls have already
     * executed and the ranked workflow has selected their exact producers.
     * Dropping those response edges with the local symbolic frontier removes
     * the caller-side scheduling arm and makes the selected producer tasks
     * impossible to admit.  Retaining the edge does not make the response a
     * symbolic root of the outer branch; it only preserves the exact cut that
     * the replayed VM handoff must attest before a later inner case can use
     * the value.</p>
     */
    private static boolean selectedWorkflowHandoffBinding(
            JsonObject binding) {
        if (handoffComponentBinding(binding)) return true;
        return "RUNTIME_PROTOCOL_FLOW".equals(string(binding, "kind"))
                && "RESPONSE".equalsIgnoreCase(
                string(binding, "direction"))
                && !string(binding, "fromOutputPort").isEmpty()
                && !string(binding, "toInputPort").isEmpty();
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

    /**
     * Bounded control metadata needed to distinguish a terminal exception
     * guard from an observed frontier leading to a still-unobserved guard.
     * Predicates and occurrence histories stay in the task/summary; copying
     * them here would recreate the large branch-catalog artifact this query
     * replaced.
     */
    private static JsonArray targetGuardCatalog(JsonArray branches) {
        JsonArray result = new JsonArray();
        for (JsonElement element : branches) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (!bool(branch, "failureTarget", false)) continue;
            JsonObject compact = new JsonObject();
            for (String field : new String[]{
                    "siteId", "failureTarget", "requiredOutcome",
                    RuntimeSelectedRegionFinalizer.FAILURE_TARGET_CELLS,
                    "guardedSiteOutcomes"}) {
                JsonElement value = branch.get(field);
                if (value != null && !value.isJsonNull()) {
                    compact.add(field, value.deepCopy());
                }
            }
            result.add(compact);
        }
        return result;
    }

    private static JsonArray materializationPlan(
            Goal goal, JsonArray sourceActions,
            DefinitionIndex definitions,
            Set<String> regionMethods,
            OutputClosureContract outputClosure,
            JsonArray demandedBranches,
            String bindingInstance,
            Set<String> selectedTargetEdgeIds) {
        JsonArray result = new JsonArray();
        Set<String> represented = new LinkedHashSet<>();
        // The frame the root-entry hooks are injected into.  An action that
        // names its own defining method decides between the two argument
        // hooks against this, and nothing else: a position alone cannot say
        // which frame it is a position in.
        String planRootMethod = string(object(goal.plan().json(),
                "rootSelector"), "method");
        OutputClosureContract.ExecutionScope scope = outputClosure == null
                ? null : outputClosure.executionScope();
        Set<String> captureAnchors = outputCaptureAnchors(outputClosure);
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
            JsonObject action = outputClosure == null
                    ? projectExactIncomingAtomicState(goal,
                    element.getAsJsonObject(), bindingInstance,
                    selectedTargetEdgeIds)
                    : element.getAsJsonObject();
            JsonObject binding = action.deepCopy();
            String location = string(action, "location");
            String cell = string(action, "cell");
            String dependencyRole = DependencyRole.normalize(
                    action.get("dependencyRole"));
            if (concreteOnlyInput(action)
                    || !DependencyRole.VALUE_FRONTIER.equals(
                    dependencyRole)) {
                addConcreteInputAction(result, represented, binding,
                        concreteOnlyInputReason(action, dependencyRole));
                continue;
            }
            boolean boundedContainerState =
                    supportedBoundedContainerState(action, location, cell);
            String unsupportedLeaf = boundedContainerState ? ""
                    : unsupportedSymbolicLeafReason(action, location, cell);
            if (!unsupportedLeaf.isEmpty()) {
                addConcreteInputAction(result, represented, binding,
                        unsupportedLeaf);
                continue;
            }
            if (staticSyntheticConstant(action)) {
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_STATIC_SYNTHETIC_CONSTANT");
                continue;
            }
            String structureControl = structureControlReason(action);
            if (!structureControl.isEmpty()) {
                // These values describe the concrete execution structure
                // selected for replay.  They may remain in path conditions,
                // but changing them would vary dispatch/container shape
                // rather than a failure-relevant value leaf.
                binding.addProperty("structureControlReason",
                        structureControl);
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_STRUCTURE_CONTROL");
                continue;
            }
            String outputDemand = scope == null ? ""
                    : outputSymbolicDemand(goal, action, definitions,
                    exactOutputGuardDependent, captureAnchors,
                    bindingInstance);
            if (scope != null && outputDemand.isEmpty()) {
                // Output capture is demand-first.  A broad static slice may
                // still contain replay-local payload and library state, but
                // absence of an exact incoming binding, explored guard use,
                // or authored state demand is not authority to turn that
                // value into a new solver dimension.
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_UNDEMANDED_OUTPUT_PAYLOAD");
                continue;
            }
            if (scope != null
                    && string(binding, "symbolicDemand").isEmpty()) {
                binding.addProperty("symbolicDemand", outputDemand);
            }
            if (scope == null
                    && !"EXACT_INCOMING_COMPOSITION".equals(
                    string(action, "symbolicDemand"))
                    && unguardedPayloadLeaf(action, definitions,
                    guardDependent)) {
                // Symbolic freedom is only worth its cost when some explored
                // decision can read the value.  A leaf that is merely carried
                // into an encoding or a payload opens no new outcome, while
                // symbolising it turns every expression built from it
                // symbolic as well.
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_UNGUARDED_PAYLOAD");
                continue;
            }
            if (scope != null && !scope.inputPorts().contains(
                    string(action, "symbol"))) {
                // The output closure is the authority for symbolic demand.
                // Keep the declaration for rooted output capture, but do not
                // let unrelated region live-ins enter the VM/SMT state.
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_OUTSIDE_OUTPUT_CLOSURE_SCOPE");
                continue;
            }
            if (action.has("observed")
                    && !bool(action, "observed", false)
                    && !bool(action, "deferredResolution", false)) {
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_UNOBSERVED_INPUT");
                continue;
            }
            if ("ARGUMENT".equals(location)
                    || "ARGUMENT_FIELD".equals(location)
                    || "RECEIVER_FIELD".equals(location)) {
                String argumentMethod = string(action, "method");
                int argumentIndex = integer(action, "index", -1);
                if ("ARGUMENT".equals(location)
                        && !argumentMethod.isEmpty()
                        && !argumentMethod.equals(planRootMethod)
                        && argumentIndex >= 0) {
                    // The value is an argument of a frame that is not this
                    // plan's root, so the root-entry hook cannot see it: that
                    // hook is injected at the root and matches by position
                    // alone, and the root of a server fragment is the serving
                    // thread's own entry, which has no arguments at all.
                    // README section 3's Req_in is parameter <n> of the
                    // resolved server entry, one frame above the delivery, so
                    // the in-region method-argument hook is what addresses it.
                    // The method and the position are the declaration's own,
                    // never re-derived here.
                    binding.addProperty("bindingMode", "METHOD_ARGUMENT");
                    binding.addProperty("method", argumentMethod);
                    binding.addProperty("index", argumentIndex);
                } else {
                    binding.addProperty("bindingMode", "ROOT_ENTRY");
                }
            } else if ("ARGUMENT_FIELD_PATH".equals(location)) {
                if (validFieldPaths(action)) {
                    binding.addProperty("bindingMode", "ROOT_ENTRY");
                } else {
                    addConcreteInputAction(result, represented, binding,
                            "CONCRETE_UNRESOLVED_ARGUMENT_FIELD_PATH");
                    continue;
                }
            } else if ("CALL_RETURN".equals(location)) {
                if (!boundedContainerState
                        && JavaPrimitiveBoxing.deterministicValueOfReturn(
                        cell)) {
                    addConcreteInputAction(result, represented, binding,
                            "CONCRETE_DETERMINISTIC_BOXING_RETURN");
                    continue;
                }
                if (!boundedContainerState
                        && JavaContainerTypes.symbolicResultReturn(cell)) {
                    addConcreteInputAction(result, represented, binding,
                            "CONCRETE_CONTAINER_RESULT_RETURN");
                    continue;
                }
                JsonArray sites = definitions.returnSites(cell,
                        scope == null ? regionMethods : scope.methods(),
                        scope);
                sites = exactExplicitFaultReturnSite(action, sites);
                if (sites.size() == 0) {
                    addConcreteInputAction(result, represented, binding,
                            "CONCRETE_NO_RESOLVED_RETURN_SITE");
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
            } else if ("HEAP_OBJECT_FIELD".equals(location)) {
                binding.addProperty("bindingMode", "FIELD_ACCESS");
                List<String> path = fieldPath(cell);
                JsonObject declaredLeaf = exactDeclaredFieldPathLeaf(
                        action, path);
                if (path.size() > 2 && declaredLeaf == null) {
                    addConcreteInputAction(result, represented, binding,
                            "CONCRETE_UNDECLARED_HEAP_FIELD_PATH");
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
                    addConcreteInputAction(result, represented, binding,
                            "CONCRETE_NULL_PROJECTED_REFERENCE");
                    continue;
                }
            } else {
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_UNSUPPORTED_INPUT_LOCATION");
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

    /**
     * Projects an exact Atomic mutation read-from carrier to the primitive
     * state actually consumed by the target branch.  The projection is
     * admitted only by the existing trusted runtime edge and the small RMW
     * API surface implemented by the VM; ordinary reference inputs remain
     * concrete structure carriers.
     */
    private static JsonObject projectExactIncomingAtomicState(
            Goal goal, JsonObject source, String bindingInstance,
            Set<String> selectedEdgeIds) {
        String symbol = string(source, "symbol");
        if (!"HEAP_OBJECT_FIELD".equals(string(source, "location"))
                || symbol.isEmpty() || bindingInstance.isEmpty()) {
            return source;
        }
        FieldPathSpec.DeclaredField root = FieldPathSpec.declaredField(
                firstNonBlank(string(source, "accessFieldSignature"),
                        string(source, "leafFieldSignature")));
        List<String> sourcePath = exactActionFieldPath(source,
                string(source, "cell"));
        if (root == null || sourcePath.size() != 1
                || !root.name().equals(sourcePath.get(0))) {
            return source;
        }

        Set<String> acceptedPorts = exactInputPorts(goal, symbol,
                bindingInstance);
        String selectedLeaf = "";
        JsonObject selectedEdge = null;
        for (JsonElement element : goal.edgeBindingsView()) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            if (!bindingInstance.equals(string(edge, "toOccurrenceId"))
                    || !acceptedPorts.contains(string(edge, "toInputPort"))
                    || !selectedEdgeIds.isEmpty()
                    && !selectedEdgeIds.contains(string(edge, "edgeId"))
                    || !AutomaticRegionEdge
                    .trustedRuntimeReadFromBinding(edge)) {
                continue;
            }
            String leaf = OutputCaptureSpec
                    .atomicArithmeticValueFieldSignature(
                            string(edge, "mutatorDeclaredCallee"));
            FieldPathSpec.DeclaredField declaredLeaf =
                    FieldPathSpec.declaredField(leaf);
            JsonArray declarations = array(edge,
                    "fieldPathDeclarations");
            if (declaredLeaf == null
                    || !root.type().equals(declaredLeaf.owner())
                    || declarations.size() != 1
                    || !declarations.get(0).isJsonPrimitive()
                    || !root.signature().equals(
                    declarations.get(0).getAsString())) {
                continue;
            }
            if (selectedEdge != null && !string(selectedEdge, "edgeId")
                    .equals(string(edge, "edgeId"))) {
                return source;
            }
            selectedLeaf = leaf;
            selectedEdge = edge;
        }
        if (selectedLeaf.isEmpty() || selectedEdge == null) return source;

        long readerEventSeq = longInteger(selectedEdge,
                "readerEventSeq", -1L);
        JsonObject selectedAccess = null;
        for (JsonElement element : array(source, "runtimeAccesses")) {
            if (!element.isJsonObject()) continue;
            JsonObject access = element.getAsJsonObject();
            if (readerEventSeq != longInteger(access, "eventSeq", -2L)) {
                continue;
            }
            if (selectedAccess != null) return source;
            selectedAccess = access;
        }
        int replayOccurrence = selectedAccess == null ? -1
                : integer(selectedAccess,
                "activationLocalStaticSiteOccurrence", -1);
        if (readerEventSeq < 0L || replayOccurrence < 1) return source;

        FieldPathSpec.DeclaredField leaf =
                FieldPathSpec.declaredField(selectedLeaf);
        JsonObject projected = source.deepCopy();
        JsonArray path = new JsonArray();
        path.add(root.name());
        path.add(leaf.name());
        projected.add("fieldPath", path.deepCopy());
        JsonArray paths = new JsonArray();
        paths.add(path.deepCopy());
        projected.add("fieldPaths", paths);
        JsonArray declarations = new JsonArray();
        declarations.add(root.signature());
        declarations.add(leaf.signature());
        projected.add("fieldPathDeclarations", declarations);
        projected.addProperty("accessFieldSignature", root.signature());
        projected.addProperty("leafFieldSignature", leaf.signature());
        projected.addProperty("javaType", leaf.type());
        projected.addProperty("dependencyRole",
                DependencyRole.VALUE_FRONTIER);
        projected.addProperty("symbolicDemand",
                "EXACT_INCOMING_COMPOSITION");
        projected.addProperty("replayOccurrence", replayOccurrence);
        projected.addProperty("selectedRuntimeEventSeq", readerEventSeq);
        projected.addProperty("selectedIncomingEdgeId",
                string(selectedEdge, "edgeId"));
        projected.addProperty("atomicStateProjectionAuthority",
                "EXACT_RUNTIME_ATOMIC_RMW_READ_FROM_V1");
        return projected;
    }

    /** Positive authority for one producer-side symbolic leaf. */
    private static String outputSymbolicDemand(
            Goal goal, JsonObject action, DefinitionIndex definitions,
            Set<String> guardDependent, Set<String> captureAnchors,
            String bindingInstance) {
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
        if (captureAnchors.contains(string(action, "symbol"))) {
            return "EXACT_OUTPUT_CAPTURE_ANCHOR";
        }
        String location = string(action, "location");
        if ("ARGUMENT".equals(location)
                || "ARGUMENT_FIELD".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location)) {
            return "EXACT_ROOT_INPUT_TO_OUTPUT";
        }
        return "";
    }

    /**
     * Input ports a demanded output capture is anchored on.
     *
     * <p>Three kinds of anchor exist and all are the closure's own statement
     * about which live-in the capture reads.  A heap member names the exact
     * accessor slot that identifies its state transition
     * ({@code captureAnchorPort}).  A handoff-bound leaf needs no Java anchor:
     * its expression is captured from the live VM export and may have arrived
     * through an earlier interaction in the same session.</p>
     *
     * <p>A declared cut argument names no single slot, because it is not read
     * from one: it is the value this occurrence computes and hands across the
     * cut, so what the capture reads is whatever live-ins its own value slice
     * ended on.  Those are its anchors.  Without them the producer relation is
     * admitted with every input concrete, the export presents a constant, and
     * the broker refuses it as {@code RPC_HANDOFF_NOT_SYMBOLIC} - the request
     * that crosses the cut could then never differ from the seed's, which is
     * the same emptiness the planner already refuses by name as
     * {@code CUT_ARGUMENT_RELATION_HAS_NO_INPUT}.  Structure carriers among
     * them stay concrete: their dependency role is decided before any demand
     * is asked for.</p>
     */
    static Set<String> outputCaptureAnchors(
            OutputClosureContract outputClosure) {
        if (outputClosure == null) return Collections.emptySet();
        Set<String> result = new LinkedHashSet<>();
        for (OutputClosureContract.Member member : outputClosure.members()) {
            String anchor = string(member.slice(), "captureAnchorPort");
            if (!anchor.isEmpty()) result.add(anchor);
            boolean cutArgument = false;
            for (JsonElement element : member.captures()) {
                if (!element.isJsonObject()) continue;
                JsonObject capture = element.getAsJsonObject();
                cutArgument |= OutputCaptureSpec.CALL_ARGUMENT.equals(
                        string(capture, "captureKind"));
            }
            if (!cutArgument) continue;
            for (JsonElement port : array(member.slice(), "inputPorts")) {
                if (port.isJsonPrimitive()) result.add(port.getAsString());
            }
        }
        return result;
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
     *
     * <p>Returns the empty string when the leaf is supported, and otherwise
     * the name of the exact contract the leaf failed.  A refusal here is the
     * difference between a value the solver can move and a replay constant,
     * so it is reported rather than returned as a bare {@code false}.</p>
     */
    static String unsupportedSymbolicLeafReason(
            JsonObject action, String location, String cell) {
        String javaType = string(action, "javaType");
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
        if (!supportedScalar && !supportedPrimitiveArray) {
            return "CONCRETE_UNSUPPORTED_LEAF_TYPE";
        }

        if (!("RECEIVER_FIELD".equals(location)
                || "ARGUMENT_FIELD".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location)
                || "HEAP_OBJECT_FIELD".equals(location))) {
            return "";
        }

        List<String> path = exactActionFieldPath(action, cell);
        if (path.isEmpty()) {
            return "CONCRETE_AMBIGUOUS_FIELD_PATH";
        }
        FieldPathSpec.DeclaredField leaf = declaredLeaf(action, cell);
        if (leaf == null) {
            return "CONCRETE_UNDECLARED_FIELD_LEAF";
        }
        if (!leaf.name().equals(path.get(path.size() - 1))) {
            return "CONCRETE_FIELD_LEAF_NAME_MISMATCH";
        }
        if (!descriptor.equals(
                JavaPrimitiveSmtSemantics.javaTypeDescriptor(leaf.type()))) {
            return "CONCRETE_FIELD_LEAF_TYPE_MISMATCH";
        }
        return "";
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
        if (JavaContainerTypes.shape(javaType)
                == JavaContainerTypes.Shape.NONE) {
            return false;
        }
        return "ARGUMENT".equals(location)
                || "RECEIVER_FIELD".equals(location)
                || "ARGUMENT_FIELD".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location)
                || "HEAP_OBJECT_FIELD".equals(location)
                || "CALL_RETURN".equals(location);
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
                string(action, "accessFieldSignature"),
                pathLeafFieldSignature(action, cell), cell}) {
            FieldPathSpec.DeclaredField declared =
                    FieldPathSpec.declaredField(signature);
            if (declared != null) return declared;
        }
        return null;
    }

    /**
     * The declaration of the last hop of a receiver/heap field path.
     *
     * <p>Some accesses carry their declaration in {@code leafFieldSignature}
     * or {@code accessFieldSignature}, and a cell that itself names a field
     * carries it in the cell. A path reached from a region root -- {@code
     * receiver.raiseRequest}, or {@code receiver.channel.response} -- carries
     * none of those: its cell names the root ({@code <...run()>.receiver}),
     * which is not a field signature, and its declarations live per hop in
     * {@code fieldPathDeclarations}, which the recorder wrote alongside
     * {@code fieldPath} from the same observed accesses. Without this the
     * leaf of every such path is undeclared, and the callers that exist to
     * check a declaration against the path read a missing declaration as an
     * unsupported leaf, so a genuine scalar frontier is silently demoted to a
     * concrete replay value.</p>
     *
     * <p>This holds at every path length, one hop included. A one-hop path is
     * exactly the case where {@code fieldPathDeclarations} is the only source
     * that exists, so excluding it left a declared primitive frontier with no
     * declaration at all.</p>
     *
     * <p>The declarations are used only when they describe this path hop for
     * hop. A list of a different length describes some other access, and
     * taking its last entry would attach one path's declaration to another
     * path's leaf. That length equality is the whole admission rule here; the
     * callers still check the resolved leaf's name and type against the path
     * and the action's own type.</p>
     */
    private static String pathLeafFieldSignature(JsonObject action,
                                                 String cell) {
        JsonArray declarations = array(action, "fieldPathDeclarations");
        List<String> path = exactActionFieldPath(action, cell);
        if (declarations.size() == 0 || declarations.size() != path.size()) {
            return "";
        }
        JsonElement last = declarations.get(declarations.size() - 1);
        return last != null && last.isJsonPrimitive()
                ? last.getAsString() : "";
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

    private static void addInputAction(
            JsonArray result, Set<String> represented,
            JsonObject action, InputActionCatalog.Mode mode) {
        dischargeDeferredResolution(action);
        action.addProperty("mode", mode.name());
        represented.add(string(action, "symbol"));
        result.add(action);
    }

    /**
     * The only way an input leaves {@link #materializationPlan} concrete.
     *
     * <p>A concrete input is a refusal to give the solver a dimension the
     * upstream evidence would otherwise support, so it is a claim that must
     * carry its own name.  An unnamed refusal is indistinguishable from an
     * input that was never considered, and the next reader has nothing to
     * check.  The reason overwrites any positive demand the action carried:
     * once the decision is CONCRETE, a surviving symbolic-demand name would
     * describe an authority that was not honoured.</p>
     */
    static void addConcreteInputAction(
            JsonArray result, Set<String> represented,
            JsonObject binding, String reason) {
        binding.addProperty("symbolicDemand",
                reason == null || reason.trim().isEmpty()
                        ? "CONCRETE_UNNAMED_REFUSAL" : reason.trim());
        addInputAction(result, represented, binding,
                InputActionCatalog.Mode.CONCRETE);
    }

    /**
     * Names why an action was concrete before any leaf support was examined:
     * either the producing stage already declared it concrete-only, or its
     * dependency role is not a value frontier at all.
     */
    static String concreteOnlyInputReason(
            JsonObject action, String dependencyRole) {
        String authored = string(action, "symbolicDemand");
        if (authored.startsWith("CONCRETE_")) {
            return authored;
        }
        if (bool(action, "captureRootOnly", false)) {
            return "CONCRETE_CAPTURE_ROOT_ONLY";
        }
        if (bool(action, "loopControlOnly", false)) {
            return "CONCRETE_LOOP_CONTROL_ONLY";
        }
        if (bool(action, "controlOnly", false)) {
            return "CONCRETE_CONTROL_ONLY";
        }
        if (bool(action, "pathAssumptionOnly", false)) {
            return "CONCRETE_PATH_ASSUMPTION_ONLY";
        }
        return "CONCRETE_NON_VALUE_FRONTIER_ROLE:"
                + (dependencyRole == null || dependencyRole.isEmpty()
                ? "NONE" : dependencyRole);
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

    private static boolean validFieldPaths(JsonObject action) {
        return FieldPathSpec.hasNonEmptyPaths(action, "fieldPaths");
    }

    private static List<String> fieldPath(String cell) {
        return FieldPathSpec.path(cell);
    }

    /** The region port catalog of one campaign, keyed by region id. */
    private static Map<String, Region> regionIndex(List<JsonObject> regions) {
        Map<String, Region> index = new LinkedHashMap<>();
        for (JsonObject row : regions) {
            Region region = new Region(row);
            if (!region.regionId.isEmpty()) {
                index.put(region.regionId, region);
            }
        }
        return index;
    }

    private static JsonObject branchQuery(Candidate candidate,
                                          JsonObject summary,
                                          String seedTaskId,
                                          JsonObject queryOccurrence) {
        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 1);
        query.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        // scheduleTargetFirst indexes every selected query by this stable
        // semantic identity before the builder consumes its fields.
        query.addProperty("queryKey",
                targetBranchQueryKey(seedTaskId));
        query.addProperty("goalId", candidate.goal.goalId());
        query.addProperty("regionId", candidate.goal.plan().regionId());
        query.addProperty("sourceKey", candidate.goal.plan().sourceKey());
        query.addProperty("occurrenceId",
                candidate.queryOccurrenceId);
        query.add("selectedTargetOccurrence",
                queryOccurrence.deepCopy());
        query.addProperty("targetSiteId", candidate.target.siteId);
        query.addProperty("fatalRequiredTakenOutcome",
                candidate.target.requiredOutcome);
        query.add("targetGuardCatalog",
                targetGuardCatalog(candidate.branches));
        // The query is the target relation consumed by composition. Preserve
        // the canonical task bound the importer validated; runtime plan rows
        // intentionally do not duplicate execution authority.
        LoopBoundPolicy.decode(summary).writeTo(query);
        try {
            BranchReplayContract contract;
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
            }
            // This artifact is consumed by the target path-set builder, not
            // by the local path-flip solver.  Carry the replay identity and
            // polarity, but do not publish an unused solverPathContext that
            // no target-stage consumer validates.
            query.add("replayContract", contract.toJson());
            query.addProperty("readyForSolver", true);
        } catch (IllegalArgumentException incompleteWitness) {
            query.addProperty("readyForSolver", false);
            query.addProperty("blocker", incompleteWitness.getMessage());
        }
        JsonObject symbolicContext = new JsonObject();
        symbolicContext.addProperty("occurrenceId",
                candidate.queryOccurrenceId);
        query.add("symbolicContext", symbolicContext);
        return query;
    }

    /** The solver query names every input frozen into the effective task. */
    private static JsonObject queryOccurrenceWithInputs(
            JsonObject encoded, JsonArray taskInputActions) {
        JsonObject result = encoded == null
                ? new JsonObject() : encoded.deepCopy();
        Set<String> inputs = new java.util.TreeSet<>();
        for (JsonElement element : array(result, "inputPorts")) {
            if (element.isJsonPrimitive()
                    && !element.getAsString().trim().isEmpty()) {
                inputs.add(element.getAsString());
            }
        }
        for (JsonElement element : taskInputActions == null
                ? new JsonArray() : taskInputActions) {
            if (!element.isJsonObject()) continue;
            String input = firstNonBlank(string(
                    element.getAsJsonObject(), "symbol"),
                    string(element.getAsJsonObject(), "portId"));
            if (!input.isEmpty()) inputs.add(input);
        }
        JsonArray ports = new JsonArray();
        for (String input : inputs) ports.add(input);
        result.add("inputPorts", ports);
        return result;
    }

    /** Stable identity shared by target query publication and aggregation. */
    static String targetBranchQueryKey(String seedTaskId) {
        String task = seedTaskId == null ? "" : seedTaskId.trim();
        if (task.isEmpty()) {
            throw new IllegalArgumentException(
                    "target branch query requires a seed task identity");
        }
        return task + "/target-branch";
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

    /**
     * Selects target-PC provenance only from the exact runtime region
     * instance and closure goal.
     */
    private static JsonObject exactTargetSummary(
            Candidate candidate, List<JsonObject> summaries) {
        String expectedInstance = candidate.goal.plan().occurrenceId();
        if (expectedInstance.isEmpty()) return null;
        JsonObject selected = null;
        for (JsonObject summary : summaries) {
            if (!candidate.goal.goalId().equals(string(summary, "goalId"))
                    || !candidate.goal.plan().regionId().equals(
                    string(summary, "regionId"))
                    || !expectedInstance.equals(string(summary,
                    "occurrenceId"))
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
                if (!localCell.group(1).equals(method) || unitIndex < 0
                        || !bool(edge, "definitionSite", false)) {
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
        private final String regionId;
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
            indexPorts(array(row, "outputs"), outputRowsByPort);
        }

        /** The declared output port rows of this region, in catalog order. */
        private Collection<JsonObject> outputRows() {
            return outputRowsByPort.values();
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

    }

    private static final class TargetBranch {
        private final String siteId;
        private final int selectedOccurrence;
        private final boolean observedOutcome;
        private final boolean requiredOutcome;
        private final boolean desiredOutcome;

        private TargetBranch(String siteId, int selectedOccurrence,
                             boolean observedOutcome,
                             boolean requiredOutcome,
                             boolean desiredOutcome) {
            this.siteId = safe(siteId);
            this.selectedOccurrence = Math.max(1, selectedOccurrence);
            this.observedOutcome = observedOutcome;
            this.requiredOutcome = requiredOutcome;
            this.desiredOutcome = desiredOutcome;
        }

        private static TargetBranch outputCapture() {
            return new TargetBranch("", 1, false, false, false);
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
                        observed, required,
                        observed == required ? !observed : required);
                if (observed == required) return selected;
                if (mismatch == null) mismatch = selected;
            }
            return mismatch;
        }

    }

    /**
     * Validates the target-first demand and uses it only to select a producer
     * occurrence.  The selected task still carries the occurrence's complete
     * output closure, symbolic inputs, branches and causal bindings.
     */
    private static boolean selectsProducerOccurrence(
            Goal goal, ProducerOutputProjection projection) {
        projection.requireMatches(goal);
        Set<String> foundEdges = new LinkedHashSet<>();
        Set<String> foundOutputs = new LinkedHashSet<>();
        Set<String> occurrences = new LinkedHashSet<>();
        for (JsonElement element : goal.edgeBindingsView()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String edgeId = string(binding, "edgeId");
            if (!projection.edgeIds().contains(edgeId)) continue;
            if (!AutomaticRegionEdge.schedulableProducerBinding(binding)) {
                throw new IllegalArgumentException("selected producer edge is "
                        + "not schedulable runtime evidence: " + edgeId);
            }
            foundEdges.add(edgeId);
            String output = string(binding, "fromOutputPort");
            if (projection.outputPorts().contains(output)) {
                foundOutputs.add(output);
                occurrences.add(string(binding, "fromOccurrenceId"));
            }
        }
        if (!foundEdges.equals(projection.edgeIds())) {
            Set<String> missing = new LinkedHashSet<>(projection.edgeIds());
            missing.removeAll(foundEdges);
            throw new IllegalArgumentException("selected producer edges are "
                    + "absent from goal ledger: " + missing);
        }
        if (!foundOutputs.equals(projection.outputPorts())) {
            Set<String> missing = new LinkedHashSet<>(projection.outputPorts());
            missing.removeAll(foundOutputs);
            throw new IllegalArgumentException("selected producer outputs are "
                    + "absent from goal ledger: " + missing);
        }
        if (occurrences.size() != 1 || occurrences.contains("")) {
            throw new IllegalArgumentException("producer selection must name "
                    + "one occurrence: " + occurrences);
        }
        return occurrences.contains(goal.plan().occurrenceId());
    }

    private static final class Candidate {
        private static final Comparator<Candidate> ORDER =
                Comparator.comparing((Candidate value) -> !value.directed)
                        .thenComparing(value -> !value.ready)
                        .thenComparing(value -> value.target.siteId)
                        .thenComparing(value ->
                                value.goal.plan().occurrenceId())
                        .thenComparing(value -> value.goal.goalId());

        private final Goal goal;
        private final JsonArray branches;
        private final TargetBranch target;
        private final boolean directed;
        private final JsonArray inputActions;
        private final boolean ready;
        private final String queryOccurrenceId;
        private final JsonObject queryOccurrence;
        private final JsonArray targetEdgeBindings;
        private final OutputClosureContract selectedOutputContract;
        private final JsonArray targetSourceFrontier;

        private Candidate(Goal goal, JsonArray branches,
                          TargetBranch target,
                          boolean hasRequiredWitness,
                          JsonArray inputActions, boolean ready,
                          String queryOccurrenceId,
                          JsonObject queryOccurrence) {
            this(goal, branches, target, hasRequiredWitness, inputActions,
                    ready, queryOccurrenceId, queryOccurrence, null, null,
                    new JsonArray());
        }

        private Candidate(Goal goal, JsonArray branches,
                          TargetBranch target,
                          boolean hasRequiredWitness,
                          JsonArray inputActions, boolean ready,
                          String queryOccurrenceId,
                          JsonObject queryOccurrence,
                          JsonArray targetEdgeBindings,
                          OutputClosureContract selectedOutputContract,
                          JsonArray targetSourceFrontier) {
            this.goal = goal;
            this.branches = branches;
            this.target = target;
            this.directed = goal.kind().capturesOutputRelation()
                    || !hasRequiredWitness;
            this.inputActions = inputActions;
            this.ready = ready;
            this.queryOccurrenceId = firstNonBlank(
                    queryOccurrenceId,
                    goal.plan().occurrenceId());
            this.queryOccurrence = queryOccurrence == null
                    ? new JsonObject() : queryOccurrence.deepCopy();
            this.targetEdgeBindings = targetEdgeBindings == null
                    ? null : targetEdgeBindings.deepCopy();
            this.selectedOutputContract = selectedOutputContract;
            this.targetSourceFrontier = targetSourceFrontier == null
                    ? new JsonArray() : targetSourceFrontier.deepCopy();
        }

        private OutputClosureContract outputContract() {
            return goal.kind().capturesOutputRelation()
                    ? selectedOutputContract : null;
        }

        /**
         * Stable task identity: source occurrence x relation content x exact
         * port set (x target predicate for reach goals).
         *
         * <p>Transient trace ids do not participate.  The source key and
         * structural occurrence id do: two occurrences may instantiate the
         * same reusable relation, but they are distinct replay tasks.</p>
         */
        private String seedTaskId(JsonArray taskInputActions) {
            StringBuilder identity = new StringBuilder(
                    "TASK.SEED.SEMANTIC.V3");
            identity.append('\n').append(goal.plan().sourceKey());
            identity.append('\n').append(goal.plan().occurrenceId());
            identity.append('\n').append(goal.plan().regionId());
            identity.append('\n').append(goal.kind().name());
            identity.append('\n').append(regionContentHash());
            identity.append('\n').append(portSetHash(taskInputActions));
            identity.append('\n').append(target.siteId)
                    .append('\n').append(target.selectedOccurrence)
                    .append('\n').append(target.observedOutcome)
                    .append('\n').append(target.requiredOutcome)
                    .append('\n').append(target.desiredOutcome);
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
        private String portSetHash(JsonArray taskInputActions) {
            java.util.TreeSet<String> descriptors = new java.util.TreeSet<>();
            for (JsonElement element : taskInputActions) {
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
                    JsonObject replay = object(member.slice(),
                            ExecutionTask.REPLAY_ENTRY);
                    if (replay.size() > 0) {
                        descriptor.append("\n--REPLAY-ENTRY--\n")
                                .append(CanonicalJson.render(replay));
                    }
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
                    descriptors.add(descriptor.toString());
                }
            }
            return ArtifactIO.sha256(String.join(
                    "\n==PORT==\n", descriptors));
        }

        /** Static, replay-stable fields of one port/capture row. */
        private static final String[] SEMANTIC_PORT_FIELDS = {
                "accessFieldSignature", "accessSites", "argumentIndex",
                "captureKind", "cell",
                "containerCapacity", "declaredCallee", "definitionMethod",
                "definitionUnitIndex", "dependencyRole", "fieldPath",
                "fieldPathDeclarations", "fieldPaths", "fieldSignature",
                "helperActivationBoundedOccurrence", "javaType",
                "leafFieldSignature", "location", "outputCell",
                "outputOccurrence", "outputSiteId", "protocolDirection",
                "replayOccurrence", "rootKind", "rootMethod", "siteId",
                "sourceKind", "symbolicDemand"};

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

    /**
     * Describes the existing selection/admission decision without adding one.
     *
     * <p>The occurrence this reports on is found by the goal it was asked
     * about, not by the {@code (region, occurrence)} pair alone, so a goal
     * that is present, admitted and merely not {@code READY} is not reported
     * as {@code GOAL_NOT_FOUND} with no state and no blockers.</p>
     */
    static String noCandidateDiagnostic(
            Arguments arguments, List<JsonObject> rows) {
        JsonObject selected = null;
        RegionInstancePlan selectedPlan = null;
        Goal selectedGoal = null;
        boolean regionFound = false;
        for (JsonObject row : rows) {
            // A refusal describes the rows it inspected; it does not re-refuse
            // them.  The plan artifact already validated every executable row,
            // and a row it could not is exactly the one a reader needs named.
            RegionInstancePlan plan = RegionInstancePlan.decode(row);
            if (!arguments.regionId.isEmpty()
                    && !arguments.regionId.equals(plan.regionId())) continue;
            regionFound = true;
            if (!arguments.occurrenceId.isEmpty()
                    && !plan.containsOccurrence(
                    arguments.occurrenceId)) continue;
            if (selected == null) {
                // Remembered only so an unmatched goal still reports which
                // fragments were searched.
                selected = row;
                selectedPlan = plan;
            }
            Goal found = null;
            for (Goal goal : plan.goals()) {
                if (!arguments.goalId.isEmpty()
                        && !arguments.goalId.equals(goal.goalId())) continue;
                found = goal;
                break;
            }
            if (found == null) continue;
            selected = row;
            selectedPlan = plan;
            selectedGoal = found;
            break;
        }
        String reason;
        if (!regionFound) {
            reason = "REGION_NOT_FOUND";
        } else if (selected == null) {
            reason = "REGION_INSTANCE_NOT_FOUND";
        } else if (selectedGoal == null) {
            reason = "GOAL_NOT_FOUND";
        } else {
            reason = !selectedGoal.replayable() ? "GOAL_NOT_REPLAYABLE"
                    : selectedGoal.kind().capturesOutputRelation()
                    && !"READY".equals(selectedGoal.admissionState())
                    ? "OUTPUT_GOAL_NOT_READY"
                    : selectedGoal.kind().capturesOutputRelation()
                    && selectedGoal.outputClosure() == null
                    ? "OUTPUT_CLOSURE_MISSING"
                    : "NO_ELIGIBLE_CANDIDATE";
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
                + " instance=" + display(arguments.occurrenceId)
                + " goal=" + display(arguments.goalId)
                + " targetMethod=" + display(targetMethod)
                + " root=" + display(root.size() == 0 ? ""
                : CanonicalJson.render(root))
                + " admissionState=" + display(state)
                + " blockers=" + display(blockers)
                + " outputClosure=" + (selectedGoal == null ? "<none>"
                : selectedGoal.outputClosure() == null
                ? "ABSENT" : "PRESENT")
                + " artifacts={runtimePlan=" + artifact(arguments.regionPlan)
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

    /**
     * Optional experiment-owned allowlist of symbolic roots.
     *
     * <p>The runtime plan remains the causal/topology authority.  This file
     * only decides which of that plan's input actions may mint a VM symbolic
     * root.  When a file is configured it is a complete allowlist: regions
     * and inputs it does not name stay concrete.  Missing value authority is
     * still rejected by composition, so a smaller selection cannot turn into
     * a free SMT variable.</p>
     */
    static final class SymbolicInputSelection {
        private static final String TASK_FIELD = "symbolicInputSelection";
        private static final String CONFIGURED_AUTHORITY =
                "CONFIGURED_REGION_SYMBOLIC_INPUTS_V1";
        private static final String DISCOVERED_AUTHORITY =
                "STATIC_SYMBOLIZE_HOOK_SELECTION_V1";

        private final boolean configured;
        private final String authority;
        private final String digest;
        private final Map<String, RegionSelection> regions;

        private SymbolicInputSelection(boolean configured, String authority,
                                       String digest,
                                       Map<String, RegionSelection> regions) {
            this.configured = configured;
            this.authority = safe(authority);
            this.digest = safe(digest);
            this.regions = regions;
        }

        static SymbolicInputSelection read(
                Path path, List<JsonObject> regionCatalog)
                throws IOException {
            if (path == null) {
                return discovered(regionCatalog);
            }
            requireFile(path, "symbolic input selection");
            Map<String, RegionSelection> selections = new LinkedHashMap<>();
            for (JsonObject row : readJsonl(path)) {
                String regionId = firstNonBlank(string(row, "regionId"));
                if (regionId.isEmpty()) {
                    throw new IOException("symbolic input selection row has "
                            + "no regionId: " + row);
                }
                RegionSelection selection = selections.computeIfAbsent(
                        regionId, ignored -> new RegionSelection());
                selection.addAll(selection.fields,
                        configurationArray(row, "fieldSignatures"),
                        "fieldSignatures");
                selection.addAll(selection.ports,
                        configurationArray(row, "portIds"), "portIds");
                selection.addAll(selection.cells,
                        configurationArray(row, "cells"), "cells");
                for (JsonObject declaration
                        : ConfiguredSourceSelectorContract.declarationsOf(
                        row)) {
                    selection.addSelectorDeclaration(declaration);
                }
                for (JsonElement element : configurationArray(row,
                        SymbolicSourceEvidence.TASK_FIELD)) {
                    if (!element.isJsonObject()) {
                        throw new IOException(SymbolicSourceEvidence.TASK_FIELD
                                + " entries must be objects");
                    }
                    selection.addSource(SourceField.from(
                            element.getAsJsonObject()));
                }
            }
            Set<String> catalogRegions = new LinkedHashSet<>();
            for (JsonObject region : regionCatalog == null
                    ? Collections.<JsonObject>emptyList() : regionCatalog) {
                String regionId = firstNonBlank(string(region, "regionId"));
                if (!regionId.isEmpty()) catalogRegions.add(regionId);
            }
            for (String configuredRegion : selections.keySet()) {
                if (!catalogRegions.contains(configuredRegion)) {
                    throw new IOException("symbolic input selection names "
                            + "an unknown static region: "
                            + configuredRegion);
                }
            }
            mergeDiscoveredSources(selections, regionCatalog);
            return new SymbolicInputSelection(true, CONFIGURED_AUTHORITY,
                    ArtifactIO.sha256(path), selections);
        }

        private static JsonArray configurationArray(
                JsonObject row, String field) throws IOException {
            JsonElement encoded = row == null ? null : row.get(field);
            if (encoded == null) return new JsonArray();
            if (!encoded.isJsonArray()) {
                throw new IOException("symbolic input selection " + field
                        + " must be an array");
            }
            return encoded.getAsJsonArray();
        }

        /**
         * An explicit source hook is itself the allowlist authority. Ordinary
         * region inputs stay concrete, and only hook fields that occur in the
         * selected output slice become symbolic roots.
         */
        private static SymbolicInputSelection discovered(
                List<JsonObject> regionCatalog) throws IOException {
            Map<String, RegionSelection> selections = new LinkedHashMap<>();
            mergeDiscoveredSources(selections, regionCatalog);
            JsonArray identity = new JsonArray();
            for (JsonObject region : regionCatalog == null
                    ? Collections.<JsonObject>emptyList() : regionCatalog) {
                String regionId = string(region, "regionId");
                for (JsonElement element : array(region,
                        StaticSymbolicSourceDeclaration.FIELD)) {
                    if (!element.isJsonObject() || regionId.isEmpty()) {
                        throw new IOException("static symbolic source has no "
                                + "declaring region");
                    }
                    JsonObject row = element.getAsJsonObject().deepCopy();
                    row.addProperty("regionId", regionId);
                    identity.add(row);
                }
            }
            if (selections.isEmpty()) {
                return new SymbolicInputSelection(false, "", "",
                        Collections.<String, RegionSelection>emptyMap());
            }
            return new SymbolicInputSelection(true, DISCOVERED_AUTHORITY,
                    CanonicalJson.sha256(identity), selections);
        }

        private static void mergeDiscoveredSources(
                Map<String, RegionSelection> selections,
                List<JsonObject> regionCatalog) throws IOException {
            Set<String> explicitOverrides = new LinkedHashSet<>();
            for (RegionSelection selection : selections.values()) {
                for (SourceField source : selection.sources) {
                    if (!source.inferOutputs) {
                        explicitOverrides.add(source.sourceIdentity());
                    }
                }
            }
            for (JsonObject region : regionCatalog == null
                    ? Collections.<JsonObject>emptyList() : regionCatalog) {
                String regionId = string(region, "regionId");
                for (JsonElement element : array(region,
                        StaticSymbolicSourceDeclaration.FIELD)) {
                    if (!element.isJsonObject() || regionId.isEmpty()) {
                        throw new IOException("static symbolic source has no "
                                + "declaring region");
                    }
                    SourceField source = SourceField.fromDiscovered(
                            element.getAsJsonObject());
                    // The explicit row names the authoritative region and
                    // target/output boundary.  A call-graph envelope that
                    // also reaches the same hook must not create another
                    // obligation or a second VM root.
                    if (explicitOverrides.contains(source.sourceIdentity())) {
                        continue;
                    }
                    selections.computeIfAbsent(regionId,
                            ignored -> new RegionSelection())
                            .addDiscoveredSource(source);
                }
            }
        }

        JsonArray select(String regionId, JsonArray actions) {
            if (!configured) return actions.deepCopy();
            JsonArray selected = new JsonArray();
            RegionSelection selection = regions.get(safe(regionId));
            for (JsonElement element : actions) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                JsonObject retained = action.deepCopy();
                // Every input remains declared because output captures and
                // concrete topology may use it as an anchor.  The allowlist
                // controls only whether that input mints a VM symbolic root.
                if ("SYMBOLIC".equals(string(action, "mode"))) {
                    if (selection != null
                            && selection.sourceOwns(action)) {
                        // The Java hook mints this exact root once. Letting an
                        // ordinary input selector mint it again would create
                        // two unrelated symbols for one source field.
                        retained.addProperty("mode", "CONCRETE");
                        retained.addProperty("symbolicDemand",
                                "CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED");
                    } else if (selection == null
                            || !selection.matches(action)) {
                        retained.addProperty("mode", "CONCRETE");
                        retained.addProperty("symbolicDemand",
                                "CONFIGURED_SYMBOLIC_INPUT_UNSELECTED");
                    }
                }
                selected.add(retained);
            }
            return selected;
        }

        /**
         * Keeps manual target roots needed by any guard of the same throw.
         *
         * <p>The ordinary materialization frontier is intentionally scoped to
         * the one branch this seed task first reopens.  A target path worklist
         * can expose deeper conjuncts without scheduling a new task, however,
         * so a manually declared source used by one of those conjuncts must
         * already be addressable.  Only hook-owned, locally materializable
         * actions are added; RPC/read-from inputs and undeclared heap leaves
         * retain the branch-local policy.</p>
         */
        JsonArray includeTargetSourceFrontier(
                String regionId, JsonArray branchActions,
                JsonArray guardedTargetActions) {
            JsonArray result = branchActions == null
                    ? new JsonArray() : branchActions.deepCopy();
            if (!configured || guardedTargetActions == null
                    || guardedTargetActions.size() == 0) {
                return result;
            }
            RegionSelection selection = regions.get(safe(regionId));
            if (selection == null || selection.sources.isEmpty()) {
                return result;
            }
            Set<String> represented = new LinkedHashSet<>();
            for (JsonElement element : result) {
                if (!element.isJsonObject()) continue;
                String symbol = firstNonBlank(string(
                        element.getAsJsonObject(), "symbol"),
                        string(element.getAsJsonObject(), "portId"));
                if (!symbol.isEmpty()) represented.add(symbol);
            }
            for (JsonElement element : guardedTargetActions) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                String symbol = firstNonBlank(string(action, "symbol"),
                        string(action, "portId"));
                if (symbol.isEmpty() || represented.contains(symbol)
                        || !"SYMBOLIC".equals(string(action, "mode"))
                        || !selection.sourceOwns(action)
                        || SourceField.relationBoundTargetInput(action)) {
                    continue;
                }
                result.add(action.deepCopy());
                represented.add(symbol);
            }
            return result;
        }

        /** Applies the same allowlist before target-first producer closure. */
        boolean selectedForDiscovery(
                String regionId, JsonObject action) {
            if (!configured) return true;
            RegionSelection selection = regions.get(safe(regionId));
            return selection != null && !selection.sourceOwns(action)
                    && selection.matches(action);
        }

        /** Source-derived outputs augment only an already ranked producer. */
        private Set<String> sourceOutputCellsForDiscovery(
                String regionId, OutputClosureContract closure) {
            if (!configured || closure == null) {
                return Collections.emptySet();
            }
            RegionSelection selection = regions.get(safe(regionId));
            if (selection == null || selection.sources.isEmpty()) {
                return Collections.emptySet();
            }
            Set<String> outputs = new LinkedHashSet<>();
            for (SourceField source : selection.sources) {
                outputs.addAll(source.matchingOutputs(closure));
            }
            return outputs;
        }

        void annotate(JsonObject task, JsonArray candidates,
                              JsonArray selected) {
            if (!configured) return;
            JsonObject policy = new JsonObject();
            policy.addProperty("authority", authority);
            policy.addProperty("configSha256", digest);
            policy.addProperty("candidateInputCount", candidates.size());
            policy.addProperty("selectedInputCount", selected.size());
            policy.addProperty("candidateSymbolicRootCount",
                    symbolicCount(candidates));
            policy.addProperty("selectedSymbolicRootCount",
                    symbolicCount(selected));
            task.add(TASK_FIELD, policy);
        }

        /**
         * Declares source roots only on output tasks whose exact closure
         * consumes the configured field and publishes the configured state.
         * A task in the same region but for an unrelated output phase must
         * not mint the source as a side effect.
         */
        void annotateSources(JsonObject task, String regionId,
                                     OutputClosureContract closure,
                                     JsonArray targetActions)
                throws IOException {
            if (!configured || task == null) return;
            RegionSelection selection = regions.get(safe(regionId));
            if (selection == null || selection.sources.isEmpty()) {
                task.remove(ConfiguredSourcePhaseContract.PLAN_FIELD);
                task.remove(ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD);
                return;
            }
            List<TaskSourcePhase> phases = taskSourcePhases(task);
            JsonArray selected = new JsonArray();
            Set<String> selectedSourceIdentities = new LinkedHashSet<>();
            Map<String, LinkedHashMap<String, TaskSourcePhase>>
                    publicationsBySource =
                    new LinkedHashMap<>();
            Set<String> retainedPhaseIds = new LinkedHashSet<>();
            for (SourceField source : selection.sources) {
                Set<String> outputs = closure == null
                        ? Collections.<String>emptySet()
                        : source.matchingOutputs(closure);
                Set<String> inputs = closure != null
                        ? Collections.<String>emptySet()
                        : source.matchingTargetInputs(targetActions);
                if (outputs.isEmpty() && inputs.isEmpty()) continue;
                selectedSourceIdentities.add(source.sourceIdentity());
                if (closure != null) {
                    Map<TaskSourcePhase, Set<String>> byPublication =
                            outputPublications(source, outputs, closure,
                                    phases, task);
                    for (Map.Entry<TaskSourcePhase, Set<String>> group
                            : byPublication.entrySet()) {
                        registerPublication(publicationsBySource, source,
                                group.getKey());
                        retainedPhaseIds.add(
                                group.getKey().occurrence.phaseId());
                        selected.add(source.toOutputJson(group.getValue(),
                                group.getKey().occurrence));
                    }
                } else if (ClosureGoalKind.TARGET_REACH_CLOSURE.name().equals(
                        string(task, ClosureGoalKind.TASK_FIELD))) {
                    TaskSourcePhase publish = latestPublication(source,
                            phases, phase -> phaseInsideSelectedBoundary(
                                    phase.occurrence, task, null));
                    requirePublication(source, task, publish,
                            "target boundary");
                    registerPublication(publicationsBySource, source,
                            publish);
                    retainedPhaseIds.add(publish.occurrence.phaseId());
                    selected.add(source.toTargetJson(inputs,
                            publish.occurrence));
                }
            }

            // A selector is required only by a source this exact task mints.
            // Its CONSUME phase must be in the same selected call boundary
            // and precede that dependent PUBLISH phase.
            for (JsonObject declaration : selection.selectorDeclarations) {
                Set<String> requiredBy = new LinkedHashSet<>(
                        ConfiguredSourceSelectorContract
                                .requiredBySourceIds(declaration));
                for (Map.Entry<String, LinkedHashMap<String,
                        TaskSourcePhase>> dependent
                        : publicationsBySource.entrySet()) {
                    if (!requiredBy.contains(dependent.getKey())) continue;
                    for (TaskSourcePhase publication
                            : dependent.getValue().values()) {
                        TaskSourcePhase consume = latestPhase(phases,
                                phase -> phase.occurrence.phase()
                                        == ConfiguredSourcePhaseContract
                                        .Phase.CONSUME
                                        && string(declaration,
                                        "sourceId").equals(
                                        phase.occurrence.sourceId())
                                        && phase.occurrence.runtimeEventSeq()
                                        < publication.occurrence
                                        .runtimeEventSeq()
                                        && phaseInsideSelectedCall(
                                        phase.occurrence, task, closure));
                        if (consume == null) {
                            throw new IOException("configured source selector "
                                    + string(declaration, "sourceId")
                                    + " required by " + dependent.getKey()
                                    + " phase "
                                    + publication.occurrence.phaseId()
                                    + " in task " + string(task, "taskId")
                                    + " has no exact preceding CONSUME phase");
                        }
                        retainedPhaseIds.add(
                                consume.occurrence.phaseId());
                    }
                }
            }
            JsonObject policy = object(task, TASK_FIELD);
            if (!task.has(TASK_FIELD)) {
                task.add(TASK_FIELD, policy);
            }
            policy.addProperty("declaredSymbolicSourceCount",
                    selection.sources.size());
            policy.addProperty("selectedSymbolicSourceCount",
                    selectedSourceIdentities.size());
            policy.addProperty("unusedSymbolicSourceCount",
                    selection.sources.size()
                            - selectedSourceIdentities.size());
            if (selected.size() > 0) {
                task.add(SymbolicSourceEvidence.TASK_FIELD, selected);
            }
            retainTaskSourcePhases(task, phases, retainedPhaseIds, closure);
        }

        private static Map<TaskSourcePhase, Set<String>> outputPublications(
                SourceField source, Set<String> outputCells,
                OutputClosureContract closure, List<TaskSourcePhase> phases,
                JsonObject task) throws IOException {
            Map<TaskSourcePhase, Set<String>> result = new LinkedHashMap<>();
            for (String cell : outputCells) {
                TaskSourcePhase selected = null;
                int members = 0;
                for (OutputClosureContract.Member member
                        : closure.members()) {
                    if (!cell.equals(member.cell())) continue;
                    members++;
                    TaskSourcePhase candidate = latestPublication(source,
                            phases, phase -> phaseBeforeOutput(
                                    phase.occurrence, member));
                    requirePublication(source, task, candidate,
                            "output " + member.portId());
                    if (selected != null && !selected.occurrence.phaseId()
                            .equals(candidate.occurrence.phaseId())) {
                        throw new IOException("configured source output cell "
                                + cell + " crosses two publication phases: "
                                + selected.occurrence.phaseId() + " and "
                                + candidate.occurrence.phaseId());
                    }
                    selected = candidate;
                }
                if (members == 0 || selected == null) {
                    throw new IOException("configured source output cell "
                            + cell + " is absent from selected closure in "
                            + string(task, "taskId"));
                }
                result.computeIfAbsent(selected,
                        ignored -> new LinkedHashSet<>()).add(cell);
            }
            return result;
        }

        private static boolean phaseBeforeOutput(
                ConfiguredSourcePhaseContract.Occurrence phase,
                OutputClosureContract.Member member) {
            long callId = longInteger(member.slice(),
                    "selectedRuntimeCallId", -1L);
            long boundary = Math.max(longInteger(member.slice(),
                            "selectedRuntimeEventSeq", -1L),
                    longInteger(member.slice(),
                            "definitionCompletionSeq", -1L));
            return callId > 0L && boundary > 0L
                    && phase.enclosingCallIds().contains(callId)
                    && phase.runtimeEventSeq() <= boundary;
        }

        private static TaskSourcePhase latestPublication(
                SourceField source, List<TaskSourcePhase> phases,
                java.util.function.Predicate<TaskSourcePhase> boundary) {
            return latestPhase(phases, phase -> phase.occurrence.phase()
                    == ConfiguredSourcePhaseContract.Phase.PUBLISH
                    && source.sourceId.equals(phase.occurrence.sourceId())
                    && source.fieldSignature.equals(
                    phase.occurrence.fieldSignature())
                    && boundary.test(phase));
        }

        private static TaskSourcePhase latestPhase(
                List<TaskSourcePhase> phases,
                java.util.function.Predicate<TaskSourcePhase> predicate) {
            TaskSourcePhase selected = null;
            for (TaskSourcePhase phase : phases) {
                if (predicate.test(phase)
                        && (selected == null
                        || phase.occurrence.runtimeEventSeq()
                        > selected.occurrence.runtimeEventSeq())) {
                    selected = phase;
                }
            }
            return selected;
        }

        private static void requirePublication(
                SourceField source, JsonObject task, TaskSourcePhase phase,
                String boundary) throws IOException {
            if (phase != null) return;
            throw new IOException("configured symbolic source "
                    + source.sourceId + " in task "
                    + string(task, "taskId") + "@"
                    + string(task, "occurrenceId")
                    + " has no exact PUBLISH phase before " + boundary);
        }

        private static void registerPublication(
                Map<String, LinkedHashMap<String, TaskSourcePhase>> versions,
                SourceField source, TaskSourcePhase phase) {
            versions.computeIfAbsent(source.sourceId,
                    ignored -> new LinkedHashMap<>()).putIfAbsent(
                    phase.occurrence.phaseId(), phase);
        }

        private static List<TaskSourcePhase> taskSourcePhases(
                JsonObject task) throws IOException {
            JsonArray encoded = array(task,
                    ConfiguredSourcePhaseContract.PLAN_FIELD);
            final List<ConfiguredSourcePhaseContract.Occurrence> decoded;
            try {
                decoded = ConfiguredSourcePhaseContract.occurrencesOf(encoded);
            } catch (IllegalArgumentException malformed) {
                throw new IOException("malformed configured source phases in "
                        + string(task, "taskId"), malformed);
            }
            if (decoded.size() != encoded.size()) {
                throw new IOException("configured source phase decode lost "
                        + "rows in " + string(task, "taskId"));
            }
            List<TaskSourcePhase> result = new ArrayList<>();
            for (int index = 0; index < decoded.size(); index++) {
                result.add(new TaskSourcePhase(decoded.get(index),
                        encoded.get(index).getAsJsonObject().deepCopy()));
            }
            return result;
        }

        private static boolean phaseInsideSelectedBoundary(
                ConfiguredSourcePhaseContract.Occurrence phase,
                JsonObject task, OutputClosureContract closure) {
            if (phase == null) return false;
            if (closure != null) {
                for (OutputClosureContract.Member member : closure.members()) {
                    JsonObject slice = member.slice();
                    long callId = longInteger(slice,
                            "selectedRuntimeCallId", -1L);
                    long boundary = Math.max(longInteger(slice,
                                    "selectedRuntimeEventSeq", -1L),
                            longInteger(slice, "definitionCompletionSeq",
                                    -1L));
                    if (callId > 0L && boundary > 0L
                            && phase.enclosingCallIds().contains(callId)
                            && phase.runtimeEventSeq() <= boundary) {
                        return true;
                    }
                }
                return false;
            }
            for (JsonElement element : array(task, "branches")) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (!bool(branch, "failureTarget", false)) continue;
                long callId = longInteger(branch, "selectedCallId", -1L);
                long boundary = longInteger(branch,
                        "selectedRuntimeEventSeq", -1L);
                if (callId > 0L && boundary > 0L
                        && phase.enclosingCallIds().contains(callId)
                        && phase.runtimeEventSeq() <= boundary) {
                    return true;
                }
            }
            return false;
        }

        private static boolean phaseInsideSelectedCall(
                ConfiguredSourcePhaseContract.Occurrence phase,
                JsonObject task, OutputClosureContract closure) {
            if (phase == null) return false;
            if (closure != null) {
                for (OutputClosureContract.Member member : closure.members()) {
                    long callId = longInteger(member.slice(),
                            "selectedRuntimeCallId", -1L);
                    if (callId > 0L
                            && phase.enclosingCallIds().contains(callId)) {
                        return true;
                    }
                }
                return false;
            }
            for (JsonElement element : array(task, "branches")) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (!bool(branch, "failureTarget", false)) continue;
                long callId = longInteger(branch, "selectedCallId", -1L);
                if (callId > 0L
                        && phase.enclosingCallIds().contains(callId)) {
                    return true;
                }
            }
            return false;
        }

        private static void retainTaskSourcePhases(
                JsonObject task, List<TaskSourcePhase> phases,
                Set<String> selectedPhaseIds,
                OutputClosureContract closure) {
            task.remove(ConfiguredSourcePhaseContract.PLAN_FIELD);
            task.remove(ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD);
            JsonArray catalog = new JsonArray();
            JsonArray selected = new JsonArray();
            for (TaskSourcePhase phase : phases) {
                if (!phaseInsideSelectedCall(
                        phase.occurrence, task, closure)) {
                    continue;
                }
                catalog.add(phase.encoded.deepCopy());
                if (selectedPhaseIds != null && selectedPhaseIds.contains(
                        phase.occurrence.phaseId())) {
                    selected.add(phase.occurrence.phaseId());
                }
            }
            if (selectedPhaseIds != null
                    && selected.size() != selectedPhaseIds.size()) {
                throw new IllegalArgumentException("selected configured "
                        + "source phase is outside the replay call");
            }
            if (catalog.size() > 0) {
                task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, catalog);
            }
            if (selected.size() > 0) {
                task.add(ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD,
                        selected);
            }
        }

        private static final class TaskSourcePhase {
            private final ConfiguredSourcePhaseContract.Occurrence occurrence;
            private final JsonObject encoded;

            private TaskSourcePhase(
                    ConfiguredSourcePhaseContract.Occurrence occurrence,
                    JsonObject encoded) {
                this.occurrence = occurrence;
                this.encoded = encoded;
            }
        }

        /** Every selected source must have exact boundary and phase evidence. */
        void bindSourceSelectors(List<JsonObject> tasks)
                throws IOException {
            if (!configured) return;
            List<SourceFlowTask> flow = new ArrayList<>();
            Map<String, List<SourceFlowTask>> byOccurrence =
                    new LinkedHashMap<>();
            for (JsonObject task : tasks) {
                SourceFlowTask indexed = new SourceFlowTask(task);
                flow.add(indexed);
                byOccurrence.computeIfAbsent(indexed.occurrenceId,
                        ignored -> new ArrayList<>()).add(indexed);
            }

            // Seed each new version at the output phase that its declaration
            // owns.  A task that also consumes the logical source therefore
            // still sees only the predecessor on its input side.
            for (SourceFlowTask task : flow) task.seedOwnSources();
            Map<String, String> edgeEndpoints = new LinkedHashMap<>();
            boolean changed;
            do {
                changed = false;
                Set<String> seenEdges = new LinkedHashSet<>();
                for (SourceFlowTask owner : flow) {
                    for (JsonElement element : array(owner.json,
                            "edgeBindings")) {
                        if (!element.isJsonObject()) continue;
                        JsonObject edge = element.getAsJsonObject();
                        String edgeId = string(edge, "edgeId");
                        String fromOccurrence = string(edge,
                                "fromOccurrenceId");
                        String toOccurrence = string(edge,
                                "toOccurrenceId");
                        String outputPort = string(edge, "fromOutputPort");
                        String inputPort = string(edge, "toInputPort");
                        String edgeKey = edgeId + "\n" + fromOccurrence
                                + "\n" + outputPort + "\n" + toOccurrence
                                + "\n" + inputPort;
                        if (edgeId.isEmpty() || fromOccurrence.isEmpty()
                                || toOccurrence.isEmpty()
                                || outputPort.isEmpty()
                                || inputPort.isEmpty()) {
                            continue;
                        }
                        String endpoints = fromOccurrence + "\n"
                                + outputPort + "\n" + toOccurrence + "\n"
                                + inputPort;
                        String priorEndpoints = edgeEndpoints.putIfAbsent(
                                edgeId, endpoints);
                        if (priorEndpoints != null
                                && !priorEndpoints.equals(endpoints)) {
                            throw new IOException("configured source flow edge "
                                    + edgeId + " has conflicting endpoints");
                        }
                        if (!seenEdges.add(edgeKey)) continue;
                        for (SourceFlowTask producer
                                : byOccurrence.getOrDefault(fromOccurrence,
                                Collections.<SourceFlowTask>emptyList())) {
                            if (!producer.publishes(outputPort, edgeId)) {
                                continue;
                            }
                            for (SourceFlowTask consumer
                                    : byOccurrence.getOrDefault(toOccurrence,
                                    Collections.<SourceFlowTask>emptyList())) {
                                for (SourceVersion version
                                        : producer.outputVersions(outputPort)) {
                                    changed |= consumer.addInputVersion(
                                            inputPort, version,
                                            inputArrival(edge), edgeId);
                                }
                            }
                        }
                    }
                }
                for (SourceFlowTask task : flow) {
                    changed |= task.propagateInputsToOutputs();
                }
            } while (changed);

            for (SourceFlowTask indexed : flow) {
                JsonObject task = indexed.json;
                RegionSelection selection = regions.get(
                        string(task, "regionId"));
                if (selection == null
                        || selection.selectorDeclarations.isEmpty()) {
                    continue;
                }
                JsonArray selected = new JsonArray();
                for (JsonObject declaration
                        : selection.selectorDeclarations) {
                    if (!indexed.requiresSelector(declaration)) {
                        continue;
                    }
                    String sourceId = string(declaration, "sourceId");
                    String field = string(declaration, "fieldSignature");
                    List<ConfiguredSourcePhaseContract.Occurrence> consumes =
                            indexed.consumePhases(sourceId);
                    if (consumes.isEmpty()) {
                        throw new IOException("configured source selector "
                                + sourceId + " required by "
                                + ConfiguredSourceSelectorContract
                                .requiredBySourceIds(declaration)
                                + " in consumer task " + indexed.taskId
                                + " has no exact CONSUME phase");
                    }
                    for (ConfiguredSourcePhaseContract.Occurrence consume
                            : consumes) {
                        List<SourceVersion> matching =
                                indexed.inputVersions(sourceId, field,
                                        consume);
                        if (matching.size() != 1) {
                            List<String> candidates = new ArrayList<>();
                            for (SourceVersion candidate : matching) {
                                candidates.add(candidate.taskId + "@"
                                        + candidate.occurrenceId + ":"
                                        + candidate.phaseId);
                            }
                            Collections.sort(candidates);
                            throw new IOException("configured source selector "
                                    + sourceId + " " + field + " consumePhase="
                                    + consume.phaseId() + " required by "
                                    + ConfiguredSourceSelectorContract
                                    .requiredBySourceIds(declaration)
                                    + " in consumer task " + indexed.taskId
                                    + "@" + indexed.occurrenceId + " region "
                                    + string(task, "regionId")
                                    + " requires one exact upstream source "
                                    + "version; found " + matching.size()
                                    + " candidates " + candidates);
                        }
                        SourceVersion producer = matching.get(0);
                        selected.add(
                                ConfiguredSourceSelectorContract.exactInt(
                                        consume.phaseId(), producer.phaseId,
                                        producer.occurrenceId, sourceId,
                                        field));
                    }
                }
                if (selected.size() > 0) {
                    task.add(ConfiguredSourceSelectorContract.TASK_FIELD,
                            selected);
                }
            }
        }

        /** Validates exact phase and boundary evidence for selected sources. */
        void validateSourceCoverage(List<JsonObject> tasks)
                throws IOException {
            if (!configured) return;
            Set<String> scheduledRegions = new LinkedHashSet<>();
            Map<String, Map<String, SourcePhaseSelection>> versions =
                    new LinkedHashMap<>();
            Set<String> coveredOutputs = new LinkedHashSet<>();
            Set<String> coveredTargetInputs = new LinkedHashSet<>();
            Set<String> expectedTargetInputs = new LinkedHashSet<>();
            for (JsonObject task : tasks) {
                String region = string(task, "regionId");
                scheduledRegions.add(region);
                ClosureGoalKind taskKind = ClosureGoalKind.fromTask(task);
                for (JsonElement element : array(task,
                        SymbolicSourceEvidence.TASK_FIELD)) {
                    if (!element.isJsonObject()) continue;
                    JsonObject declaration = element.getAsJsonObject();
                    String sourceId = string(declaration, "sourceId");
                    String phaseId = string(declaration, "sourcePhaseId");
                    if (sourceId.isEmpty() || phaseId.isEmpty()) {
                        throw new IOException("configured symbolic source "
                                + "selection lacks exact phase identity in "
                                + string(task, "taskId"));
                    }
                    Set<String> requiredOutputs =
                            SourceField.requiredOutputs(declaration);
                    Set<String> requiredTargetInputs =
                            SourceField.requiredTargetInputs(declaration);
                    if (requiredOutputs.isEmpty()
                            == requiredTargetInputs.isEmpty()) {
                        throw new IOException("configured symbolic source "
                                + sourceId + " has no exact boundary role in "
                                + string(task, "taskId"));
                    }
                    String expectedRole = requiredOutputs.isEmpty()
                            ? "TARGET_REACH" : "OUTPUT_RELATION";
                    SourcePhaseSelection selected = versions
                            .computeIfAbsent(region + "\n" + sourceId,
                                    ignored -> new LinkedHashMap<>())
                            .computeIfAbsent(phaseId,
                                    ignored -> new SourcePhaseSelection());
                    String sourceRole = string(declaration, "sourceRole");
                    if (!expectedRole.equals(sourceRole)
                            || "OUTPUT_RELATION".equals(expectedRole)
                            != taskKind.capturesOutputRelation()) {
                        throw new IOException("configured symbolic source "
                                + sourceId + " has a boundary/task role "
                                + "mismatch in "
                                + string(task, "taskId"));
                    }
                    selected.occurrences.add(string(task, "occurrenceId"));
                    selected.tasks.add(string(task, "taskId"));
                    selected.roles.add(sourceRole);
                    for (String output : SourceField.requiredOutputs(
                            declaration)) {
                        coveredOutputs.add(region + "\n" + sourceId + "\n"
                                + output);
                    }
                    for (String input : SourceField.requiredTargetInputs(
                            declaration)) {
                        coveredTargetInputs.add(region + "\n" + sourceId
                                + "\n" + input);
                    }
                }
                if (taskKind.capturesTargetReach()) {
                    JsonArray inputActions = array(task,
                            InputActionCatalog.FIELD);
                    if (inputActions.size() == 0) {
                        inputActions = array(task, "selectedActions");
                    }
                    RegionSelection selection = regions.get(region);
                    for (JsonElement element : inputActions) {
                        if (!element.isJsonObject() || selection == null) {
                            continue;
                        }
                        JsonObject action = element.getAsJsonObject();
                        if (!"CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED".equals(
                                string(action, "symbolicDemand"))
                                || SourceField.relationBoundTargetInput(
                                action)) {
                            continue;
                        }
                        String field = RegionSelection.actionField(action);
                        String input = firstNonBlank(string(action, "portId"),
                                string(action, "symbol"));
                        if (field.isEmpty() || input.isEmpty()) continue;
                        for (SourceField source : selection.sources) {
                            if (!field.equals(source.fieldSignature)
                                    || !source.inferOutputs
                                    && !source.requiredTargetInputPorts
                                    .contains(input)) {
                                continue;
                            }
                            expectedTargetInputs.add(region + "\n"
                                    + source.sourceId + "\n" + input);
                        }
                    }
                }
            }
            if (!coveredTargetInputs.containsAll(expectedTargetInputs)) {
                Set<String> missing = new LinkedHashSet<>(
                        expectedTargetInputs);
                missing.removeAll(coveredTargetInputs);
                throw new IOException("configured target-local source "
                        + "frontier lacks exact evidence: " + missing);
            }
            Set<String> validatedDiscovered = new LinkedHashSet<>();
            for (Map.Entry<String, RegionSelection> region
                    : regions.entrySet()) {
                if (!scheduledRegions.contains(region.getKey())) continue;
                for (SourceField source : region.getValue().sources) {
                    if (source.inferOutputs) {
                        String declaration = source.declarationIdentity();
                        if (!validatedDiscovered.add(declaration)) continue;
                        for (Map.Entry<String, RegionSelection> candidate
                                : regions.entrySet()) {
                            if (!scheduledRegions.contains(candidate.getKey())) {
                                continue;
                            }
                            for (SourceField peer : candidate.getValue().sources) {
                                if (!peer.inferOutputs || !declaration.equals(
                                        peer.declarationIdentity())) {
                                    continue;
                                }
                                String key = candidate.getKey() + "\n"
                                        + peer.sourceId;
                                Map<String, SourcePhaseSelection>
                                        selectedVersions = versions.get(key);
                                if (selectedVersions == null
                                        || selectedVersions.isEmpty()) {
                                    continue;
                                }
                                validateSourcePhaseSelections(
                                        "discovered symbolic source "
                                                + candidate.getKey() + ":"
                                                + peer.sourceId,
                                        selectedVersions);
                            }
                        }
                        // A Java symbolize hook declares an eligible source,
                        // not a requirement that every declared field affect
                        // every selected output.  Sources absent from the
                        // exact output slice remain concrete and are omitted
                        // from symbolicSourceFields.  Once selected, their
                        // phase/version evidence above is still fail-closed.
                        continue;
                    }
                    for (String output
                            : source.requiredOutputFieldSignatures) {
                        String coverageKey = region.getKey() + "\n"
                                + source.sourceId + "\n" + output;
                        if (!coveredOutputs.contains(coverageKey)) {
                            throw new IOException("configured symbolic source "
                                    + "output is not in the selected closure: "
                                    + region.getKey() + ":" + source.sourceId
                                    + ":" + output);
                        }
                    }
                    for (String input : source.requiredTargetInputPorts) {
                        String coverageKey = region.getKey() + "\n"
                                + source.sourceId + "\n" + input;
                        if (!coveredTargetInputs.contains(coverageKey)) {
                            throw new IOException("configured symbolic source "
                                    + "target input is not in the selected "
                                    + "target frontier: " + region.getKey()
                                    + ":" + source.sourceId + ":" + input);
                        }
                    }
                    validateSourcePhaseSelections(
                            "configured symbolic source "
                                    + region.getKey() + ":" + source.sourceId,
                            versions.get(region.getKey() + "\n"
                                    + source.sourceId));
                }
            }
        }

        private static void validateSourcePhaseSelections(String label,
                Map<String, SourcePhaseSelection> versions)
                throws IOException {
            if (versions == null || versions.isEmpty()) {
                throw new IOException(label
                        + " is not in the selected output closure");
            }
            for (Map.Entry<String, SourcePhaseSelection> version
                    : versions.entrySet()) {
                SourcePhaseSelection selected = version.getValue();
                if (version.getKey().isEmpty()
                        || selected.occurrences.size() != 1
                        || selected.occurrences.contains("")) {
                    throw new IOException(label + " phase "
                            + version.getKey() + " matches more than one "
                            + "occurrence: " + selected.occurrences);
                }
                if (selected.tasks.size() != 1
                        || selected.tasks.contains("")) {
                    throw new IOException(label + " phase "
                            + version.getKey() + " matches more than one "
                            + "output task: " + selected.tasks);
                }
            }
        }

        private static final class SourcePhaseSelection {
            private final Set<String> occurrences = new LinkedHashSet<>();
            private final Set<String> tasks = new LinkedHashSet<>();
            private final Set<String> roles = new LinkedHashSet<>();
        }

        private int symbolicCount(JsonArray actions) {
            int count = 0;
            for (JsonElement element : actions) {
                if (element.isJsonObject() && "SYMBOLIC".equals(string(
                        element.getAsJsonObject(), "mode"))) {
                    count++;
                }
            }
            return count;
        }

        private static final class RegionSelection {
            private final Set<String> fields = new LinkedHashSet<>();
            private final Set<String> ports = new LinkedHashSet<>();
            private final Set<String> cells = new LinkedHashSet<>();
            private final List<SourceField> sources = new ArrayList<>();
            private final List<JsonObject> selectorDeclarations =
                    new ArrayList<>();

            private void addSelectorDeclaration(JsonObject declaration)
                    throws IOException {
                String sourceId = string(declaration, "sourceId");
                for (JsonObject prior : selectorDeclarations) {
                    if (sourceId.equals(string(prior, "sourceId"))) {
                        throw new IOException(
                                ConfiguredSourceSelectorContract.CONFIG_FIELD
                                        + " repeats sourceId " + sourceId);
                    }
                }
                selectorDeclarations.add(declaration.deepCopy());
            }

            private void addSource(SourceField source) throws IOException {
                for (SourceField prior : sources) {
                    if (prior.sourceId.equals(source.sourceId)) {
                        if (!prior.fieldSignature.equals(
                                source.fieldSignature)) {
                            throw new IOException(
                                    SymbolicSourceEvidence.TASK_FIELD
                                            + " gives one sourceId two fields: "
                                            + source.sourceId);
                        }
                        if (!prior.requiredOutputFieldSignatures.isEmpty()
                                != !source.requiredOutputFieldSignatures
                                .isEmpty()
                                || !prior.requiredTargetInputPorts.isEmpty()
                                != !source.requiredTargetInputPorts
                                .isEmpty()) {
                            throw new IOException(
                                    SymbolicSourceEvidence.TASK_FIELD
                                            + " gives one source both output "
                                            + "and target roles: "
                                            + source.sourceId);
                        }
                        Set<String> repeated = new LinkedHashSet<>(
                                prior.requiredOutputFieldSignatures);
                        repeated.retainAll(
                                source.requiredOutputFieldSignatures);
                        Set<String> repeatedInputs = new LinkedHashSet<>(
                                prior.requiredTargetInputPorts);
                        repeatedInputs.retainAll(
                                source.requiredTargetInputPorts);
                        if (!repeated.isEmpty() || !repeatedInputs.isEmpty()) {
                            throw new IOException(
                                    SymbolicSourceEvidence.TASK_FIELD
                                            + " repeats one source boundary: "
                                            + source.sourceId + ":"
                                            + firstNonBlank(
                                            repeated.stream().findFirst()
                                                    .orElse(""),
                                            repeatedInputs.stream().findFirst()
                                                    .orElse("")));
                        }
                        prior.requiredOutputFieldSignatures.addAll(
                                source.requiredOutputFieldSignatures);
                        prior.requiredTargetInputPorts.addAll(
                                source.requiredTargetInputPorts);
                        return;
                    }
                }
                sources.add(source);
            }

            /** Explicit JSONL output restrictions win over inferred ones. */
            private void addDiscoveredSource(SourceField source)
                    throws IOException {
                for (SourceField prior : sources) {
                    if (!prior.sourceId.equals(source.sourceId)) continue;
                    if (!prior.fieldSignature.equals(source.fieldSignature)) {
                        throw new IOException(
                                SymbolicSourceEvidence.TASK_FIELD
                                        + " gives one sourceId two fields: "
                                        + source.sourceId);
                    }
                    return;
                }
                sources.add(source);
            }

            private void addAll(Set<String> output, JsonArray values,
                                String field) throws IOException {
                for (JsonElement element : values) {
                    if (!element.isJsonPrimitive()
                            || !element.getAsJsonPrimitive().isString()
                            || firstNonBlank(element.getAsString()).isEmpty()) {
                        throw new IOException("symbolic input selection "
                                + field + " entries must be non-empty "
                                + "strings");
                    }
                    output.add(firstNonBlank(element.getAsString()));
                }
            }

            private boolean matches(JsonObject action) {
                String field = actionField(action);
                String port = firstNonBlank(string(action, "portId"),
                        string(action, "symbol"));
                String cell = string(action, "cell");
                return fields.contains(field) || ports.contains(port)
                        || cells.contains(cell);
            }

            private boolean sourceOwns(JsonObject action) {
                String field = actionField(action);
                if (field.isEmpty()) return false;
                for (SourceField source : sources) {
                    if (source.fieldSignature.equals(field)) return true;
                }
                return false;
            }

            private static String actionField(JsonObject action) {
                return firstNonBlank(
                        string(action, "accessFieldSignature"),
                        string(action, "declaredFieldSignature"),
                        string(action, "leafFieldSignature"));
            }
        }

        /** One accepted-task candidate for a logical source version. */
        private static final class SourceVersion {
            private final String taskId;
            private final String occurrenceId;
            private final String phaseId;
            private final String sourceId;
            private final String fieldSignature;

            private SourceVersion(String taskId, String occurrenceId,
                                  String phaseId, String sourceId,
                                  String fieldSignature) {
                this.taskId = taskId;
                this.occurrenceId = occurrenceId;
                this.phaseId = phaseId;
                this.sourceId = sourceId;
                this.fieldSignature = fieldSignature;
            }

            private String identity() {
                return taskId + "\n" + occurrenceId + "\n" + phaseId
                        + "\n" + sourceId
                        + "\n" + fieldSignature;
            }

            private String logicalIdentity() {
                return sourceId + "\n" + fieldSignature;
            }
        }

        /** One version's exact arrival at one selected consumer input. */
        private static final class SourceArrival {
            private final SourceVersion version;
            private final long eventSeq;

            private SourceArrival(SourceVersion version, long eventSeq) {
                this.version = version;
                this.eventSeq = eventSeq;
            }
        }

        /** Port-sensitive source-version flow over the selected task graph. */
        private static final class SourceFlowTask {
            private final JsonObject json;
            private final String taskId;
            private final String occurrenceId;
            private final Map<String, FlowOutput> outputs =
                    new LinkedHashMap<>();
            private final Map<String, LinkedHashMap<String, SourceArrival>>
                    inputVersions = new LinkedHashMap<>();
            private final List<ConfiguredSourcePhaseContract.Occurrence>
                    sourcePhases;
            private final Set<String> selectedSourcePhaseIds;

            private SourceFlowTask(JsonObject task) throws IOException {
                this.json = task;
                this.taskId = string(task, "taskId");
                this.occurrenceId = string(task, "occurrenceId");
                if (taskId.isEmpty() || occurrenceId.isEmpty()) {
                    throw new IOException("configured source flow task has "
                            + "no exact task/occurrence identity");
                }
                try {
                    sourcePhases = ConfiguredSourcePhaseContract.occurrencesOf(
                            array(task,
                                    ConfiguredSourcePhaseContract.PLAN_FIELD));
                    selectedSourcePhaseIds = new LinkedHashSet<>(
                            ConfiguredSourcePhaseContract.selectedPhaseIdsOf(
                                    task, sourcePhases));
                } catch (IllegalArgumentException malformed) {
                    throw new IOException("configured source flow task has "
                            + "malformed phases in " + taskId, malformed);
                }
                for (JsonElement element : array(object(task,
                        OutputClosureContract.FIELD), "members")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject member = element.getAsJsonObject();
                    JsonObject output = object(member, "output");
                    JsonObject slice = object(member, "slice");
                    String port = string(output, "portId");
                    String cell = string(output, "cell");
                    if (port.isEmpty() || cell.isEmpty()
                            || outputs.put(port,
                            new FlowOutput(cell, slice)) != null) {
                        throw new IOException("configured source flow has "
                                + "a malformed output member in " + taskId);
                    }
                }
            }

            private void seedOwnSources() throws IOException {
                for (JsonElement element : array(json,
                        SymbolicSourceEvidence.TASK_FIELD)) {
                    if (!element.isJsonObject()) continue;
                    JsonObject source = element.getAsJsonObject();
                    String sourceId = string(source, "sourceId");
                    String phaseId = string(source, "sourcePhaseId");
                    String field = string(source, "fieldSignature");
                    Set<String> cells = SourceField.requiredOutputs(source);
                    if (sourceId.isEmpty() || phaseId.isEmpty()
                            || field.isEmpty()
                            || cells.isEmpty()) {
                        continue;
                    }
                    if (!selectedSourcePhaseIds.contains(phaseId)) {
                        throw new IOException("configured source " + sourceId
                                + " is not selected in phase catalog of "
                                + taskId);
                    }
                    SourceVersion version = new SourceVersion(taskId,
                            occurrenceId, phaseId, sourceId, field);
                    boolean seeded = false;
                    for (FlowOutput output : outputs.values()) {
                        if (cells.contains(output.cell)) {
                            output.seed(version);
                            seeded = true;
                        }
                    }
                    if (!seeded) {
                        throw new IOException("configured source " + sourceId
                                + " has no exact output phase in " + taskId);
                    }
                }
            }

            private boolean publishes(String outputPort, String edgeId) {
                FlowOutput output = outputs.get(outputPort);
                return output != null && output.edgeIds.contains(edgeId);
            }

            private List<SourceVersion> outputVersions(String outputPort) {
                FlowOutput output = outputs.get(outputPort);
                return output == null
                        ? Collections.<SourceVersion>emptyList()
                        : new ArrayList<>(output.versions.values());
            }

            private boolean addInputVersion(
                    String inputPort, SourceVersion version,
                    long arrivalEventSeq, String edgeId) {
                if (inputPort.isEmpty() || version == null
                        || arrivalEventSeq <= 0L || safe(edgeId).isEmpty()) {
                    return false;
                }
                LinkedHashMap<String, SourceArrival> arrivals = inputVersions
                        .computeIfAbsent(inputPort,
                                ignored -> new LinkedHashMap<>());
                SourceArrival prior = arrivals.get(version.identity());
                if (prior != null && prior.eventSeq >= arrivalEventSeq) {
                    return false;
                }
                arrivals.put(version.identity(), new SourceArrival(version,
                        arrivalEventSeq));
                return true;
            }

            private boolean propagateInputsToOutputs() {
                boolean changed = false;
                for (FlowOutput output : outputs.values()) {
                    for (String input : output.inputPorts) {
                        for (SourceArrival arrival : inputVersions
                                .getOrDefault(input,
                                        new LinkedHashMap<String,
                                                SourceArrival>()).values()) {
                            changed |= output.propagate(arrival.version);
                        }
                    }
                }
                return changed;
            }

            /** Whether this exact task declares a source that needs it. */
            private boolean requiresSelector(JsonObject declaration) {
                Set<String> requiredBy = new LinkedHashSet<>(
                        ConfiguredSourceSelectorContract
                                .requiredBySourceIds(declaration));
                for (JsonElement element : array(json,
                        SymbolicSourceEvidence.TASK_FIELD)) {
                    if (element.isJsonObject()
                            && requiredBy.contains(string(
                            element.getAsJsonObject(), "sourceId"))) {
                        return true;
                    }
                }
                return false;
            }

            private List<ConfiguredSourcePhaseContract.Occurrence>
                    consumePhases(String sourceId) {
                List<ConfiguredSourcePhaseContract.Occurrence> result =
                        new ArrayList<>();
                for (ConfiguredSourcePhaseContract.Occurrence phase
                        : sourcePhases) {
                    if (phase.phase()
                            == ConfiguredSourcePhaseContract.Phase.CONSUME
                            && selectedSourcePhaseIds.contains(
                            phase.phaseId())
                            && safe(sourceId).equals(phase.sourceId())) {
                        result.add(phase);
                    }
                }
                return result;
            }

            private List<SourceVersion> inputVersions(
                    String sourceId, String fieldSignature,
                    ConfiguredSourcePhaseContract.Occurrence consume) {
                Map<String, SourceArrival> exact = new LinkedHashMap<>();
                for (Map<String, SourceArrival> port
                        : inputVersions.values()) {
                    for (SourceArrival arrival : port.values()) {
                        SourceVersion version = arrival.version;
                        if (sourceId.equals(version.sourceId)
                                && fieldSignature.equals(
                                version.fieldSignature)
                                && !taskId.equals(version.taskId)
                                && arrival.eventSeq
                                < consume.runtimeEventSeq()) {
                            SourceArrival prior = exact.get(
                                    version.identity());
                            if (prior == null || arrival.eventSeq
                                    > prior.eventSeq) {
                                exact.put(version.identity(), arrival);
                            }
                        }
                    }
                }
                long latest = -1L;
                for (SourceArrival arrival : exact.values()) {
                    latest = Math.max(latest, arrival.eventSeq);
                }
                List<SourceVersion> result = new ArrayList<>();
                for (SourceArrival arrival : exact.values()) {
                    if (arrival.eventSeq == latest) {
                        result.add(arrival.version);
                    }
                }
                return result;
            }
        }

        /** Exact consumer-side event at which one selected edge arrived. */
        private static long inputArrival(JsonObject edge) {
            boolean protocol = "RUNTIME_PROTOCOL_FLOW".equals(
                    string(edge, "kind"));
            long primary = longInteger(edge, protocol
                    ? "receiverEventSeq" : "readerEventSeq", -1L);
            return primary > 0L ? primary : longInteger(edge, protocol
                    ? "readerEventSeq" : "receiverEventSeq", -1L);
        }

        private static final class FlowOutput {
            private final String cell;
            private final Set<String> inputPorts = new LinkedHashSet<>();
            private final Set<String> edgeIds = new LinkedHashSet<>();
            private final Set<String> ownLogicalVersions =
                    new LinkedHashSet<>();
            private final LinkedHashMap<String, SourceVersion> versions =
                    new LinkedHashMap<>();

            private FlowOutput(String cell, JsonObject slice) {
                this.cell = cell;
                addStrings(inputPorts, array(slice, "inputPorts"));
                addStrings(edgeIds, array(slice, "causalEdgeIds"));
            }

            private void seed(SourceVersion version) {
                ownLogicalVersions.add(version.logicalIdentity());
                versions.put(version.identity(), version);
            }

            private boolean propagate(SourceVersion version) {
                // A source hook in this task runs before its selected output
                // boundary.  Its new version shadows the predecessor only at
                // that boundary, while the predecessor remains visible on
                // the input side for this task's selector hook.
                return !ownLogicalVersions.contains(version.logicalIdentity())
                        && versions.putIfAbsent(version.identity(), version)
                        == null;
            }

            private static void addStrings(
                    Set<String> destination, JsonArray source) {
                for (JsonElement element : source) {
                    if (element.isJsonPrimitive()) {
                        String value = safe(element.getAsString());
                        if (!value.isEmpty()) destination.add(value);
                    }
                }
            }
        }

        /** One exact program source and the output state it must influence. */
        private static final class SourceField {
            private final String sourceId;
            private final String fieldSignature;
            private final Set<String> requiredOutputFieldSignatures =
                    new LinkedHashSet<>();
            private final Set<String> requiredTargetInputPorts =
                    new LinkedHashSet<>();
            private final boolean inferOutputs;
            private final String declarationMethod;
            private final int declarationUnitIndex;

            private SourceField(String sourceId, String fieldSignature,
                                Set<String> requiredOutputs,
                                Set<String> requiredTargetInputs,
                                boolean inferOutputs,
                                String declarationMethod,
                                int declarationUnitIndex) {
                this.sourceId = sourceId;
                this.fieldSignature = fieldSignature;
                this.requiredOutputFieldSignatures.addAll(requiredOutputs);
                this.requiredTargetInputPorts.addAll(requiredTargetInputs);
                this.inferOutputs = inferOutputs;
                this.declarationMethod = safe(declarationMethod);
                this.declarationUnitIndex = declarationUnitIndex;
            }

            private static SourceField from(JsonObject row)
                    throws IOException {
                String sourceId = firstNonBlank(string(row, "sourceId"));
                String field = firstNonBlank(string(row,
                        "fieldSignature"));
                Set<String> outputs = requiredOutputs(row);
                Set<String> targetInputs = requiredTargetInputs(row);
                if (sourceId.isEmpty() || field.isEmpty()
                        || outputs.isEmpty() == targetInputs.isEmpty()) {
                    throw new IOException(SymbolicSourceEvidence.TASK_FIELD
                            + " needs sourceId, fieldSignature and exactly "
                            + "one of output or target-input boundaries");
                }
                return new SourceField(sourceId, field, outputs,
                        targetInputs, false, "", -1);
            }

            private static SourceField fromDiscovered(JsonObject row)
                    throws IOException {
                String sourceId = firstNonBlank(string(row, "sourceId"));
                String field = firstNonBlank(string(row,
                        "fieldSignature"));
                if (JsonFields.exactInteger(row, "schemaVersion", -1)
                        != StaticSymbolicSourceDeclaration.SCHEMA_VERSION
                        || !StaticSymbolicSourceDeclaration.KIND.equals(
                        string(row, "kind"))
                        || !StaticSymbolicSourceDeclaration.AUTHORITY.equals(
                        string(row, "authority"))
                        || sourceId.isEmpty() || field.isEmpty()) {
                    throw new IOException("malformed static symbolic source "
                            + "declaration");
                }
                String method = string(row, "declarationMethod");
                int unit = JsonFields.exactInteger(row,
                        "declarationUnitIndex", -1);
                if (method.isEmpty() || unit < 0) {
                    throw new IOException("malformed static symbolic source "
                            + "declaration location");
                }
                return new SourceField(sourceId, field,
                        Collections.<String>emptySet(),
                        Collections.<String>emptySet(), true, method, unit);
            }

            private String sourceIdentity() {
                return sourceId + "\n" + fieldSignature;
            }

            private String declarationIdentity() {
                return sourceId + "\n" + fieldSignature + "\n"
                        + declarationMethod + "\n" + declarationUnitIndex;
            }

            private Set<String> matchingOutputs(
                    OutputClosureContract closure) {
                Set<String> matches = new LinkedHashSet<>();
                if (!inferOutputs
                        && requiredOutputFieldSignatures.isEmpty()) {
                    return matches;
                }
                for (OutputClosureContract.Member member
                        : closure.members()) {
                    if (!inferOutputs
                            && !requiredOutputFieldSignatures.contains(
                            member.cell())) {
                        continue;
                    }
                    for (JsonElement declaration : array(member.slice(),
                            "demandedHeapDeclarations")) {
                        if (declaration.isJsonPrimitive()
                                && fieldSignature.equals(
                                declaration.getAsString())) {
                            matches.add(member.cell());
                        }
                    }
                }
                return matches;
            }

            private Set<String> matchingTargetInputs(JsonArray actions) {
                Set<String> matches = new LinkedHashSet<>();
                if (!inferOutputs && requiredTargetInputPorts.isEmpty()) {
                    return matches;
                }
                for (JsonElement element : actions == null
                        ? new JsonArray() : actions) {
                    if (!element.isJsonObject()) continue;
                    JsonObject action = element.getAsJsonObject();
                    String input = firstNonBlank(string(action, "portId"),
                            string(action, "symbol"));
                    if (input.isEmpty()
                            || !"SYMBOLIC".equals(string(action, "mode"))
                            || !fieldSignature.equals(
                            RegionSelection.actionField(action))
                            || relationBoundTargetInput(action)
                            || !inferOutputs
                            && !requiredTargetInputPorts.contains(input)) {
                        continue;
                    }
                    matches.add(input);
                }
                return matches;
            }

            private static boolean relationBoundTargetInput(
                    JsonObject action) {
                return "EXACT_INCOMING_COMPOSITION".equals(
                        string(action, "symbolicDemand"))
                        || !string(action, "selectedIncomingEdgeId").isEmpty()
                        || !string(action,
                        "intraRegionReadFromAuthority").isEmpty();
            }

            private JsonObject baseJson(
                    String role,
                    ConfiguredSourcePhaseContract.Occurrence publish) {
                if (publish == null
                        || publish.phase()
                        != ConfiguredSourcePhaseContract.Phase.PUBLISH
                        || !sourceId.equals(publish.sourceId())
                        || !fieldSignature.equals(
                        publish.fieldSignature())) {
                    throw new IllegalArgumentException(
                            "configured source requires its exact PUBLISH "
                                    + "phase");
                }
                JsonObject row = new JsonObject();
                row.addProperty("authority",
                        SymbolicSourceEvidence.DECLARATION_AUTHORITY);
                row.addProperty("sourceId", sourceId);
                row.addProperty("sourcePhaseId", publish.phaseId());
                row.addProperty("sourceOccurrenceId",
                        publish.sourceOccurrenceId());
                row.addProperty("sourcePhaseSiteId", publish.siteId());
                row.addProperty("sourcePhaseOrdinal",
                        publish.baselineOrdinal());
                row.addProperty("fieldSignature", fieldSignature);
                row.addProperty("sourceRole", role);
                return row;
            }

            private JsonObject toOutputJson(
                    Set<String> outputs,
                    ConfiguredSourcePhaseContract.Occurrence publish) {
                JsonObject row = baseJson("OUTPUT_RELATION", publish);
                if (outputs.size() == 1) {
                    row.addProperty("requiredOutputFieldSignature",
                            outputs.iterator().next());
                } else {
                    JsonArray encoded = new JsonArray();
                    for (String output : outputs) encoded.add(output);
                    row.add("requiredOutputFieldSignatures", encoded);
                }
                return row;
            }

            private JsonObject toTargetJson(
                    Set<String> inputs,
                    ConfiguredSourcePhaseContract.Occurrence publish) {
                JsonObject row = baseJson("TARGET_REACH", publish);
                if (inputs.size() == 1) {
                    row.addProperty("requiredTargetInputPort",
                            inputs.iterator().next());
                } else {
                    JsonArray encoded = new JsonArray();
                    for (String input : inputs) encoded.add(input);
                    row.add("requiredTargetInputPorts", encoded);
                }
                return row;
            }

            private static Set<String> requiredOutputs(JsonObject row) {
                Set<String> result = new LinkedHashSet<>();
                String single = string(row,
                        "requiredOutputFieldSignature");
                if (!single.isEmpty()) result.add(single);
                for (JsonElement output : array(row,
                        "requiredOutputFieldSignatures")) {
                    if (output.isJsonPrimitive()
                            && !output.getAsString().isEmpty()) {
                        result.add(output.getAsString());
                    }
                }
                return result;
            }

            private static Set<String> requiredTargetInputs(JsonObject row) {
                Set<String> result = new LinkedHashSet<>();
                String single = string(row, "requiredTargetInputPort");
                if (!single.isEmpty()) result.add(single);
                for (JsonElement input : array(row,
                        "requiredTargetInputPorts")) {
                    if (input.isJsonPrimitive()
                            && !input.getAsString().isEmpty()) {
                        result.add(input.getAsString());
                    }
                }
                return result;
            }
        }
    }

    private static final class LoadedInputs {
        private final List<JsonObject> regionPlans;
        private final List<JsonObject> summaries;
        private final Map<String, Region> regionIndex;
        private final DefinitionIndex definitions;
        private final JsonObject regionPlanIdentity;
        private final SymbolicInputSelection symbolicInputs;

        private LoadedInputs(List<JsonObject> regionPlans,
                             List<JsonObject> summaries,
                             Map<String, Region> regionIndex,
                             DefinitionIndex definitions,
                             JsonObject regionPlanIdentity,
                             SymbolicInputSelection symbolicInputs) {
            this.regionPlans = regionPlans;
            this.summaries = summaries;
            this.regionIndex = regionIndex;
            this.definitions = definitions;
            this.regionPlanIdentity = regionPlanIdentity;
            this.symbolicInputs = symbolicInputs;
        }
    }

    public static final class Arguments {
        public final Path regionPlan;
        public final Path refinedGraph;
        public final Path summaries;
        public final Path outputDirectory;
        public final String regionId;
        public final String occurrenceId;
        public final String goalId;
        public final boolean targetFirst;
        public final int maxJobs;
        public final int maxLoopIterations;
        public final Path symbolicInputs;
        private final Set<String> targetEdgeIds;

        private Arguments(Path regionPlan, Path refinedGraph, Path summaries,
                          Path outputDirectory, String regionId,
                          String occurrenceId, String goalId,
                          boolean targetFirst, int maxJobs,
                          int maxLoopIterations,
                          Path symbolicInputs,
                          Set<String> targetEdgeIds) {
            this.regionPlan = regionPlan;
            this.refinedGraph = refinedGraph;
            this.summaries = summaries;
            this.outputDirectory = outputDirectory;
            this.regionId = safe(regionId);
            this.occurrenceId = safe(occurrenceId);
            this.goalId = safe(goalId);
            this.targetFirst = targetFirst;
            this.maxJobs = Math.max(1, maxJobs);
            this.maxLoopIterations = maxLoopIterations;
            this.symbolicInputs = symbolicInputs;
            this.targetEdgeIds = Collections.unmodifiableSet(
                    new LinkedHashSet<>(targetEdgeIds));
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
            Path regionPlan = requiredPath(values, "region-plan");
            Path output = Paths.get(firstNonBlank(values.get("output-dir"),
                    sibling(regionPlan, "concolic-schedule").toString()));
            Path refinedGraph = requiredPath(values, "refined-graph");
            Path summaries = optionalPath(values.get("summaries"));
            Path symbolicInputs = optionalPath(
                    values.get("symbolic-inputs"));
            boolean targetFirst = Boolean.parseBoolean(
                    values.getOrDefault("target-first", "false"));
            if (targetFirst
                    && (!firstNonBlank(values.get("region-id")).isEmpty()
                    || !firstNonBlank(values.get("occurrence-id"))
                    .isEmpty()
                    || !firstNonBlank(values.get("goal-id")).isEmpty())) {
                throw new IllegalArgumentException("--target-first cannot "
                        + "be combined with goal filters");
            }
            return new Arguments(regionPlan, refinedGraph,
                    summaries, output,
                    firstNonBlank(values.get("region-id")),
                    firstNonBlank(values.get("occurrence-id")),
                    firstNonBlank(values.get("goal-id")),
                    targetFirst,
                    parseInt(values.get("max-jobs"), 1),
                    positiveInt(values.get("max-loop-iterations"),
                            LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                            "max-loop-iterations"),
                    symbolicInputs,
                    Collections.<String>emptySet());
        }

        private static boolean knownOption(String key) {
            return "region-plan".equals(key)
                    || "refined-graph".equals(key)
                    || "summaries".equals(key)
                    || "output-dir".equals(key)
                    || "region-id".equals(key)
                    || "occurrence-id".equals(key)
                    || "goal-id".equals(key)
                    || "target-first".equals(key)
                    || "max-jobs".equals(key)
                    || "symbolic-inputs".equals(key)
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
            return new Arguments(regionPlan, refinedGraph,
                    summaries, outputDirectory,
                    selection.regionId, selection.occurrenceId,
                    selection.goalId, false, 1,
                    maxLoopIterations,
                    symbolicInputs,
                    selection.targetEdgeIds);
        }

    }
}
