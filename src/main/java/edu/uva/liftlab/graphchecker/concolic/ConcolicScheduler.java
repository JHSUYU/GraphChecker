package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.SymbolicEnvironment;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
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
    /**
     * An outbound relation whose endpoint is no port this pipeline declares.
     *
     * <p>A refusal and not a gap: both endpoints were already resolved
     * against the declaring region's own catalog, so an id that is neither
     * region-minted nor a declared cut port means the catalog and the id
     * minter disagree. Skipping it was silent - the binding was simply absent
     * from the task plan.</p>
     */
    static final String RELATION_PORT_UNRECOGNIZED =
            "OUTBOUND_RELATION_PORT_UNRECOGNIZED";


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
        List<JsonObject> edges = runtimePlan.edgeValidations();
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
        MergePlan mergePlan = buildMergePlan(regionIndex, edges);
        if (regionPlanIdentity != null) {
            requireArtifactIdentity(arguments.regionPlan,
                    regionPlanIdentity, "region plan changed while loading");
        }
        return new LoadedInputs(regionPlans, summaries, regionIndex,
                definitions, mergePlan, regionPlanIdentity, symbolicInputs);
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
                        loaded.mergePlan));
            }
            if (result.executionTasks.size() >= arguments.maxJobs) {
                continue;
            }
            JsonArray edgeBindings = loaded.mergePlan
                    .outboundValueEqualityBindings(candidate.goal);
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
            String taskId = candidate.seedTaskId();
            JsonArray selectedInputs = loaded.symbolicInputs.select(
                    candidate.goal.plan().regionId(),
                    candidate.inputActions);
            ExecutionTask scheduled = ExecutionTask.create(candidate.goal,
                    taskId, selectedInputs,
                    candidate.branches, edgeBindings,
                    loopBound, candidate.ready,
                    outputContract);
            JsonObject executionTask = scheduled.json();
            promoteSelectedReplayEntry(executionTask, outputContract);
            loaded.symbolicInputs.annotate(executionTask,
                    candidate.inputActions, selectedInputs);
            loaded.symbolicInputs.annotateSources(executionTask,
                    candidate.goal.plan().regionId(), outputContract);
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
            } else if (!selected.equals(entry)) {
                throw new IllegalArgumentException(
                        "selected outputs require incompatible replay "
                                + "continuations");
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
            putUnique(tasks, task, "taskId");
            for (JsonObject query : selected.queries) {
                putUnique(queries, query, "queryKey");
            }
        }
        Result result = new Result();
        result.executionTasks.addAll(sortedValues(tasks));
        result.queries.addAll(sortedValues(queries));
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
                        new JsonObject(), null, outputClosure));
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
                String queryInstance = targetQueryInstance(arguments, goal);
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
                        targetBindings, null));
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
            boolean selectedComponent = selectedEdgeIds.contains(
                    string(binding, "edgeId"))
                    && handoffComponentBinding(binding);
            if (queryInstance.equals(string(binding,
                    "toOccurrenceId"))
                    && (exactPorts.contains(string(binding, "toInputPort"))
                    || selectedComponent)
                    && (selectedEdgeIds.isEmpty()
                    || selectedEdgeIds.contains(string(binding, "edgeId")))
                    && (selectedComponent
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

    /**
     * The merge plan of one region catalog and one recorded edge set.
     *
     * <p>The seam {@link #loadInputs} and this package's tests share, so what
     * a test drives is the index a campaign really builds rather than a
     * smaller one written beside it.</p>
     */
    static MergePlan mergePlan(List<JsonObject> regions,
                               List<JsonObject> edges) {
        return buildMergePlan(regionIndex(regions), edges);
    }

    private static MergePlan buildMergePlan(Map<String, Region> regions,
                                            List<JsonObject> edges) {
        return new MergePlan();
    }

    private static JsonObject branchQuery(Candidate candidate,
                                          JsonObject summary,
                                          MergePlan mergePlan) {
        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 1);
        query.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        // The selected task already has a stable semantic identity.  Reuse it
        // rather than hashing the same region/occurrence/site tuple again.
        query.addProperty("queryKey",
                candidate.seedTaskId() + "/target-branch");
        query.addProperty("goalId", candidate.goal.goalId());
        query.addProperty("regionId", candidate.goal.plan().regionId());
        query.addProperty("sourceKey", candidate.goal.plan().sourceKey());
        query.addProperty("relationKey",
                candidate.goal.plan().relationKey());
        query.addProperty("occurrenceId",
                candidate.queryOccurrenceId);
        query.add("selectedTargetOccurrence",
                candidate.queryOccurrence.deepCopy());
        query.addProperty("targetSiteId", candidate.target.siteId);
        query.addProperty("fatalRequiredTakenOutcome",
                candidate.target.requiredOutcome);
        if (summary.has(LoopBoundPolicy.FIELD)
                && summary.get(LoopBoundPolicy.FIELD).isJsonObject()) {
            // The query is the target relation consumed by composition.
            // Preserve the exact task bound the importer validated; runtime
            // plan rows intentionally do not duplicate execution authority.
            query.add(LoopBoundPolicy.FIELD,
                    summary.get(LoopBoundPolicy.FIELD).deepCopy());
        }
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
                        candidate.queryOccurrenceId,
                        candidate.queryOccurrence,
                        candidate.targetEdgeBindings));
        // The target relation is carried by the query rather than decoded as
        // an output-producing RelationSummary.  Keep the VM evidence beside
        // that relation for the same reason: it belongs to this exact target
        // occurrence, and dropping it here leaves the composer with only the
        // pre-replay trace candidate.  In particular, a replay whose RPC
        // ordinal drifted still has an exact export/receive tuple and one
        // session event ledger; those are the runtime authority, while the
        // trace exchange id remains discovery metadata.
        JsonObject shared = object(summary,
                SharedStateEvidence.RECORDED_FIELD);
        if (shared.size() > 0) {
            query.add(SharedStateEvidence.RECORDED_FIELD,
                    shared.deepCopy());
        }
        VmHandoffEvidence.writeTo(query,
                VmHandoffEvidence.eventsOf(summary));
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

        private Candidate(Goal goal, JsonArray branches,
                          TargetBranch target,
                          boolean hasRequiredWitness,
                          JsonArray inputActions, boolean ready,
                          String queryOccurrenceId,
                          JsonObject queryOccurrence) {
            this(goal, branches, target, hasRequiredWitness, inputActions,
                    ready, queryOccurrenceId, queryOccurrence, null, null);
        }

        private Candidate(Goal goal, JsonArray branches,
                          TargetBranch target,
                          boolean hasRequiredWitness,
                          JsonArray inputActions, boolean ready,
                          String queryOccurrenceId,
                          JsonObject queryOccurrence,
                          JsonArray targetEdgeBindings,
                          OutputClosureContract selectedOutputContract) {
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
        private String seedTaskId() {
            StringBuilder identity = new StringBuilder(
                    "TASK.SEED.SEMANTIC.V3");
            identity.append('\n').append(goal.plan().sourceKey());
            identity.append('\n').append(goal.plan().occurrenceId());
            identity.append('\n').append(goal.plan().regionId());
            identity.append('\n').append(goal.kind().name());
            identity.append('\n').append(regionContentHash());
            identity.append('\n').append(portSetHash());
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

    static final class MergePlan {
        private MergePlan() {
        }

        /**
         * Copies runtime-confirmed protocol equalities onto the producer
         * activation that will own the imported output summary. This is a
         * summary edge, not a READ_FROM edge: serialization may change object
         * identity while preserving the complete endpoint value.
         */
        JsonArray outboundValueEqualityBindings(Goal goal) {
            JsonArray bindings = new JsonArray();
            for (JsonElement element : goal.edgeBindingsView()) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                bindings.add(binding.deepCopy());
            }
            return bindings;
        }

        JsonObject contextFor(String regionId,
                                      String occurrenceId,
                                      JsonObject selectedOccurrence,
                                      JsonArray selectedTargetBindings) {
            JsonObject context = new JsonObject();
            context.addProperty("occurrenceId", occurrenceId);
            return context;
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
                        array(row, "fieldSignatures"));
                selection.addAll(selection.ports,
                        array(row, "portIds"));
                selection.addAll(selection.cells,
                        array(row, "cells"));
                for (JsonElement element : array(row,
                        SymbolicSourceEvidence.TASK_FIELD)) {
                    if (!element.isJsonObject()) {
                        throw new IOException(SymbolicSourceEvidence.TASK_FIELD
                                + " entries must be objects");
                    }
                    selection.addSource(SourceField.from(
                            element.getAsJsonObject()));
                }
            }
            mergeDiscoveredSources(selections, regionCatalog);
            return new SymbolicInputSelection(true, CONFIGURED_AUTHORITY,
                    ArtifactIO.sha256(path), selections);
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
                                     OutputClosureContract closure)
                throws IOException {
            if (!configured || task == null || closure == null) return;
            RegionSelection selection = regions.get(safe(regionId));
            if (selection == null || selection.sources.isEmpty()) return;
            JsonArray selected = new JsonArray();
            for (SourceField source : selection.sources) {
                Set<String> outputs = source.matchingOutputs(closure);
                if (!outputs.isEmpty()) selected.add(source.toJson(outputs));
            }
            if (selected.size() > 0) {
                task.add(SymbolicSourceEvidence.TASK_FIELD, selected);
                JsonObject policy = object(task, TASK_FIELD);
                policy.addProperty("selectedSymbolicSourceCount",
                        selected.size());
            }
        }

        /** Every configured source in a scheduled region must be reachable. */
        void validateSourceCoverage(List<JsonObject> tasks)
                throws IOException {
            if (!configured) return;
            Set<String> scheduledRegions = new LinkedHashSet<>();
            Map<String, Set<String>> occurrences = new LinkedHashMap<>();
            Set<String> coveredOutputs = new LinkedHashSet<>();
            for (JsonObject task : tasks) {
                String region = string(task, "regionId");
                scheduledRegions.add(region);
                for (JsonElement element : array(task,
                        SymbolicSourceEvidence.TASK_FIELD)) {
                    if (!element.isJsonObject()) continue;
                    String sourceId = string(element.getAsJsonObject(),
                            "sourceId");
                    occurrences.computeIfAbsent(region + "\n" + sourceId,
                            ignored -> new LinkedHashSet<>()).add(
                            string(task, "occurrenceId"));
                    for (String output : SourceField.requiredOutputs(
                            element.getAsJsonObject())) {
                        coveredOutputs.add(region + "\n" + sourceId + "\n"
                                + output);
                    }
                }
            }
            for (Map.Entry<String, RegionSelection> region
                    : regions.entrySet()) {
                if (!scheduledRegions.contains(region.getKey())) continue;
                for (SourceField source : region.getValue().sources) {
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
                    Set<String> selected = occurrences.get(region.getKey()
                            + "\n" + source.sourceId);
                    if (selected == null || selected.isEmpty()) {
                        throw new IOException("configured symbolic source is "
                                + "not in the selected output closure: "
                                + region.getKey() + ":" + source.sourceId);
                    }
                    if (selected.size() != 1 || selected.contains("")) {
                        throw new IOException("configured symbolic source "
                        + "matches more than one occurrence: "
                                + region.getKey() + ":" + source.sourceId
                                + " -> " + selected);
                    }
                }
            }
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
                        if (prior.requiredOutputFieldSignatures.contains(
                                source.requiredOutputFieldSignature)) {
                            throw new IOException(
                                    SymbolicSourceEvidence.TASK_FIELD
                                            + " repeats one source output: "
                                            + source.sourceId + ":"
                                            + source.requiredOutputFieldSignature);
                        }
                        prior.requiredOutputFieldSignatures.addAll(
                                source.requiredOutputFieldSignatures);
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

            private void addAll(Set<String> output, JsonArray values) {
                for (JsonElement element : values) {
                    if (!element.isJsonPrimitive()) continue;
                    String value = firstNonBlank(element.getAsString());
                    if (!value.isEmpty()) output.add(value);
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

        /** One exact program source and the output state it must influence. */
        private static final class SourceField {
            private final String sourceId;
            private final String fieldSignature;
            private final String requiredOutputFieldSignature;
            private final Set<String> requiredOutputFieldSignatures =
                    new LinkedHashSet<>();
            private final boolean inferOutputs;

            private SourceField(String sourceId, String fieldSignature,
                                String requiredOutputFieldSignature,
                                boolean inferOutputs) {
                this.sourceId = sourceId;
                this.fieldSignature = fieldSignature;
                this.requiredOutputFieldSignature =
                        requiredOutputFieldSignature;
                this.inferOutputs = inferOutputs;
                if (!requiredOutputFieldSignature.isEmpty()) {
                    this.requiredOutputFieldSignatures.add(
                            requiredOutputFieldSignature);
                }
            }

            private static SourceField from(JsonObject row)
                    throws IOException {
                String sourceId = firstNonBlank(string(row, "sourceId"));
                String field = firstNonBlank(string(row,
                        "fieldSignature"));
                String output = firstNonBlank(string(row,
                        "requiredOutputFieldSignature"));
                if (sourceId.isEmpty() || field.isEmpty()
                        || output.isEmpty()) {
                    throw new IOException(SymbolicSourceEvidence.TASK_FIELD
                            + " needs sourceId, fieldSignature and "
                            + "requiredOutputFieldSignature");
                }
                return new SourceField(sourceId, field, output, false);
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
                return new SourceField(sourceId, field, "", true);
            }

            private Set<String> matchingOutputs(
                    OutputClosureContract closure) {
                Set<String> matches = new LinkedHashSet<>();
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

            private JsonObject toJson(Set<String> outputs) {
                JsonObject row = new JsonObject();
                row.addProperty("authority",
                        SymbolicSourceEvidence.DECLARATION_AUTHORITY);
                row.addProperty("sourceId", sourceId);
                row.addProperty("fieldSignature", fieldSignature);
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
        }
    }

    private static final class LoadedInputs {
        private final List<JsonObject> regionPlans;
        private final List<JsonObject> summaries;
        private final Map<String, Region> regionIndex;
        private final DefinitionIndex definitions;
        private final MergePlan mergePlan;
        private final JsonObject regionPlanIdentity;
        private final SymbolicInputSelection symbolicInputs;

        private LoadedInputs(List<JsonObject> regionPlans,
                             List<JsonObject> summaries,
                             Map<String, Region> regionIndex,
                             DefinitionIndex definitions,
                             MergePlan mergePlan,
                             JsonObject regionPlanIdentity,
                             SymbolicInputSelection symbolicInputs) {
            this.regionPlans = regionPlans;
            this.summaries = summaries;
            this.regionIndex = regionIndex;
            this.definitions = definitions;
            this.mergePlan = mergePlan;
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
