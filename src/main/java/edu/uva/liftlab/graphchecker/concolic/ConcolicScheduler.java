package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
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
import edu.uva.liftlab.graphchecker.contract.PathObservation;
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
import java.util.Arrays;
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

/** Builds graph-directed concolic jobs from static regions and concrete
 * runtime-selected region instance plans. */
public final class ConcolicScheduler {
    private static final Pattern LOCAL_CELL = Pattern.compile(
            "^(<.+>)::([^#]+)(?:#.*)?$");
    private ConcolicScheduler() {
    }

    public static void main(String[] args) throws Exception {
        Arguments arguments = Arguments.parse(args);
        Result result = scheduleTargetFirst(arguments);
        if (result.executionTasks.isEmpty()) {
            throw new IllegalStateException(noCandidateDiagnostic(
                    arguments,
                    RuntimePlanArtifact.read(arguments.regionPlan)
                            .regionPlans()));
        }
    }

    private static LoadedInputs loadInputs(Arguments arguments)
            throws IOException {
        requireFile(arguments.regionPlan, "region plan");
        requireFile(arguments.refinedGraph, "runtime-refined graph");
        Files.createDirectories(arguments.outputDirectory);

        JsonObject regionPlanIdentity = artifactIdentity(
                arguments.regionPlan);
        JsonObject refinedGraphIdentity = artifactIdentity(
                arguments.refinedGraph);
        JsonObject symbolicInputsIdentity = arguments.symbolicInputs == null
                ? null : artifactIdentity(arguments.symbolicInputs);
        RuntimePlanArtifact runtimePlan = RuntimePlanArtifact.read(
                arguments.regionPlan);
        List<JsonObject> regions = runtimePlan.regions();
        if (regions.isEmpty()) {
            throw new IOException("runtime plan has no region port catalog: "
                    + arguments.regionPlan);
        }
        List<RegionInstancePlan> regionPlans = runtimePlan.regionPlans();
        if (regionPlans.isEmpty()) {
            throw new IOException("runtime plan contains no region plans: "
                    + arguments.regionPlan);
        }
        List<JsonObject> summaries = arguments.summaries == null
                ? Collections.<JsonObject>emptyList()
                : ArtifactIO.readJsonl(arguments.summaries);
        List<JsonObject> refinedGraph = ArtifactIO.readJsonl(
                arguments.refinedGraph);
        requireRefinedGraph(refinedGraph);
        DefinitionIndex definitions = DefinitionIndex.from(refinedGraph);
        SymbolicInputSelection symbolicInputs =
                SymbolicInputSelection.read(arguments.symbolicInputs,
                        regions);
        JsonArray declaredFixedRoots =
                SymbolicMechanismCatalog.fixedRootDeclarations(regions);

        Map<String, Region> regionIndex = regionIndex(regions);
        if (regionPlanIdentity != null) {
            requireArtifactIdentity(arguments.regionPlan,
                    regionPlanIdentity, "region plan changed while loading");
        }
        requireArtifactIdentity(arguments.refinedGraph,
                refinedGraphIdentity,
                "runtime-refined graph changed while loading");
        if (arguments.symbolicInputs != null) {
            requireArtifactIdentity(arguments.symbolicInputs,
                    symbolicInputsIdentity,
                    "symbolic input selection changed while loading");
        }
        return new LoadedInputs(regionPlans, summaries, regionIndex,
                definitions, regionPlanIdentity, refinedGraphIdentity,
                symbolicInputsIdentity, declaredFixedRoots, symbolicInputs);
    }

    private static Result scheduleLoaded(
            Arguments arguments, LoadedInputs loaded,
            ProducerOutputProjection producerProjection,
            SymbolicMechanismCatalog.Selection mechanismSelection)
            throws IOException {
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
            JsonArray baselineInputs = loaded.symbolicInputs.select(
                    candidate.goal.plan().regionId(), taskInputActions);
            JsonArray mechanismBindings = mechanismBindings(candidate,
                    producerProjection);
            JsonArray writerAnchors = mechanismWriterAnchors(candidate,
                    taskInputActions, mechanismBindings,
                    loaded.regionIndex);
            result.mechanismObservations.addAll(
                    SymbolicMechanismCatalog.observations(
                            mechanismContext(candidate), taskInputActions,
                            baselineInputs, writerAnchors));
            JsonArray selectedInputs = mechanismSelection == null
                    ? baselineInputs
                    : mechanismSelection.select(taskInputActions,
                    baselineInputs, writerAnchors);
            String taskId = candidate.seedTaskId(selectedInputs);
            JsonObject taskQueryOccurrence = queryOccurrenceWithInputs(
                    candidate.queryOccurrence, selectedInputs);
            OutputClosureContract outputContract = candidate.outputContract();
            JsonObject captured = outputContract != null ? null
                    : exactTargetSummary(candidate, loaded.summaries);
            // A summary is evidence a previous replay already produced; making
            // its solver query consumes no replay-job slot.
            if (captured != null && outputContract == null) {
                result.queries.add(branchQuery(candidate, captured,
                        taskId, taskQueryOccurrence));
            }
            if (result.executionTasks.size() >= arguments.maxJobs) {
                continue;
            }
            JsonArray edgeBindings = objectRows(
                    candidate.goal.edgeBindings());
            if (candidate.targetEdgeBindings != null) {
                edgeBindings = candidate.targetEdgeBindings.deepCopy();
            }
            edgeBindings = mergeEdgeBindings(edgeBindings);
            if (producerProjection != null) {
                edgeBindings = selectedProducerEdgeBindings(edgeBindings,
                        producerProjection.edgeIds());
            }
            // Output alternatives are case obligations inside one coarse
            // occurrence task.
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
            // json() is the live row by decision (contract/PlanRow): the
            // scheduler annotates the task it has just created, and no typed
            // member it already decoded is derived from these carriers.
            JsonObject executionTask = scheduled.json();
            declareMapStateCarriers(executionTask, selectedInputs, candidate,
                    loaded.regionIndex.get(
                            candidate.goal.plan().regionId()));
            declareReadFromCarriers(executionTask, edgeBindings,
                    candidate.goal.plan().occurrenceId());
            if (candidate.goal.kind().capturesTargetReach()) {
                // The branch event this occurrence must decide.
                JsonObject target = new JsonObject();
                target.addProperty("siteId", candidate.target.siteId);
                target.addProperty("occurrence",
                        candidate.target.selectedOccurrence);
                executionTask.add("targetBranch", target);
            }

            result.executionTasks.add(scheduled);
        }
        if (producerProjection != null
                && result.executionTasks.size() != 1) {
            throw new IllegalStateException("producer projection must select "
                    + "exactly one execution task; found "
                    + result.executionTasks.size());
        }
        return result;
    }

    /** Compact audit coordinates only; none participates in root identity. */
    private static JsonObject mechanismContext(Candidate candidate) {
        JsonObject context = new JsonObject();
        context.addProperty("sourceKey", candidate.goal.plan().sourceKey());
        context.addProperty("occurrenceId",
                candidate.goal.plan().occurrenceId());
        context.addProperty("relationKey",
                candidate.goal.plan().relationKey());
        context.addProperty("regionId", candidate.goal.plan().regionId());
        context.addProperty("goalId", candidate.goal.goalId());
        context.addProperty("goalKind", candidate.goal.kind().name());
        context.addProperty("directed", candidate.directed);
        context.addProperty("ready", candidate.ready);
        if (!candidate.target.siteId.isEmpty()) {
            context.addProperty("targetSiteId", candidate.target.siteId);
            context.addProperty("targetSelectedOccurrence",
                    candidate.target.selectedOccurrence);
            context.addProperty("targetRequiredOutcome",
                    candidate.target.requiredOutcome);
            context.addProperty("targetDesiredOutcome",
                    candidate.target.desiredOutcome);
        }
        JsonArray methods = new JsonArray();
        java.util.TreeSet<String> ordered = new java.util.TreeSet<>(
                candidate.goal.runtimeDefinitionMethods());
        for (String method : ordered) methods.add(method);
        context.add("runtimeDefinitionMethods", methods);
        return context;
    }

    /**
     * Read-only view of the exact edges already selected for this candidate.
     * It deliberately does not merge or validate execution bindings: those
     * checks stay at the existing task-construction boundary below.
     */
    private static JsonArray mechanismBindings(
            Candidate candidate,
            ProducerOutputProjection producerProjection) {
        JsonArray source = candidate.targetEdgeBindings == null
                ? candidate.goal.edgeBindings()
                : candidate.targetEdgeBindings;
        JsonArray result = new JsonArray();
        for (JsonElement element : source) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            if (producerProjection == null
                    || producerProjection.edgeIds().contains(
                    string(edge, "edgeId"))) {
                result.add(edge.deepCopy());
            }
        }
        return result;
    }

    /**
     * Projects runtime edge ids and reader repetitions to stable writer sites.
     * One array entry corresponds to one input action.  Repeated reads of the
     * same writer therefore receive the same mechanism identity, while two
     * distinct static write/output sites remain separate.  The original edge
     * ledger and all bounded occurrences remain untouched in the task plan.
     */
    private static JsonArray mechanismWriterAnchors(
            Candidate candidate, JsonArray actions, JsonArray bindings,
            Map<String, Region> regions) {
        JsonArray result = new JsonArray();
        String receiver = PathObservation.plannedOccurrenceOf(
                candidate.queryOccurrenceId);
        for (JsonElement actionElement : actions) {
            JsonObject action = actionElement.getAsJsonObject();
            String port = firstNonBlank(string(action, "portId"),
                    string(action, "symbol"));
            Map<String, JsonObject> anchors = new TreeMap<>();
            for (JsonElement bindingElement : bindings) {
                if (!bindingElement.isJsonObject()) continue;
                JsonObject binding = bindingElement.getAsJsonObject();
                if (port.isEmpty()
                        || !port.equals(string(binding, "toInputPort"))) {
                    continue;
                }
                String toOccurrence = string(binding, "toOccurrenceId");
                if (!toOccurrence.isEmpty() && !receiver.equals(
                        PathObservation.plannedOccurrenceOf(toOccurrence))) {
                    continue;
                }
                JsonObject anchor = mechanismWriterAnchor(binding, regions);
                anchors.put(CanonicalJson.render(anchor), anchor);
            }
            if (anchors.isEmpty()
                    && "EXACT_INCOMING_COMPOSITION".equals(
                    string(action, "symbolicDemand"))) {
                JsonObject unresolved = new JsonObject();
                unresolved.addProperty("kind",
                        "UNRESOLVED_INCOMING_ACTION");
                unresolved.addProperty("regionId",
                        candidate.goal.plan().regionId());
                String incomingEdge = string(action,
                        "selectedIncomingEdgeId");
                if (!incomingEdge.isEmpty()) {
                    unresolved.addProperty("selectedIncomingEdgeId",
                            incomingEdge);
                }
                if (!port.isEmpty()) {
                    unresolved.addProperty("unresolvedPortId", port);
                }
                String site = firstNonBlank(
                        string(action, "staticAccessSiteId"),
                        canonicalMechanismCell(string(action, "cell")));
                if (!site.isEmpty()) unresolved.addProperty("siteId", site);
                JsonElement declarations = action.get(
                        "fieldPathDeclarations");
                if (declarations != null && !declarations.isJsonNull()) {
                    unresolved.add("fieldPathDeclarations",
                            declarations.deepCopy());
                }
                anchors.put(CanonicalJson.render(unresolved), unresolved);
            }
            JsonArray rows = new JsonArray();
            for (JsonObject anchor : anchors.values()) rows.add(anchor);
            result.add(rows);
        }
        return result;
    }

    private static JsonObject mechanismWriterAnchor(
            JsonObject binding, Map<String, Region> regions) {
        String edgeId = string(binding, "edgeId");
        boolean trusted = AutomaticRegionEdge
                .trustedRuntimeReadFromBinding(binding)
                || AutomaticRegionEdge.tracedExchangeCandidate(binding);
        String fromRegion = string(binding, "fromRegion");
        String fromPort = string(binding, "fromOutputPort");
        Region region = regions.get(fromRegion);
        JsonObject output = region == null ? null : region.outputRow(fromPort);
        if (!trusted || output == null || output.size() == 0) {
            return unresolvedWriterAnchor(edgeId);
        }

        JsonObject anchor = new JsonObject();
        anchor.addProperty("kind", "REGION_OUTPUT");
        anchor.addProperty("fromRegion", fromRegion);
        for (String field : new String[]{
                "sourceKind", "dependencyRole", "javaType",
                "accessFieldSignature", "declaredFieldSignature",
                "leafFieldSignature", "fieldSignature", "fieldPath",
                "fieldPaths", "fieldPathDeclarations", "definitionMethod",
                "definitionUnitIndex", "declaredCallee",
                "staticAccessSiteId", "siteId", "outputSiteId",
                "callSiteId", "handoffLeafPath", "manualCarrierClass",
                "manualCarrierDescriptor", "manualCarrierField",
                "captureKind", "outputCaptureKind"}) {
            JsonElement value = output.get(field);
            if (value != null && !value.isJsonNull()) {
                anchor.add(field, value.deepCopy());
            }
        }
        String cell = canonicalMechanismCell(string(output, "cell"));
        if (!cell.isEmpty()) anchor.addProperty("cell", cell);
        if (!anchor.has("fieldPathDeclarations")) {
            JsonElement path = binding.get("fieldPathDeclarations");
            if (path != null && !path.isJsonNull()) {
                anchor.add("fieldPathDeclarations", path.deepCopy());
            }
        }
        if (!anchor.has("declaredCallee")) {
            String callee = string(binding, "mutatorDeclaredCallee");
            if (!callee.isEmpty()) {
                anchor.addProperty("declaredCallee", callee);
            }
        }
        boolean hasDefinitionSite = anchor.has("definitionMethod")
                && anchor.has("definitionUnitIndex");
        boolean hasStaticSite = anchor.has("callSiteId")
                || anchor.has("staticAccessSiteId")
                || anchor.has("siteId")
                || anchor.has("outputSiteId")
                || hasDefinitionSite
                || anchor.has("declaredCallee");
        return hasStaticSite ? anchor : unresolvedWriterAnchor(edgeId);
    }

    private static JsonObject unresolvedWriterAnchor(String edgeId) {
        JsonObject anchor = new JsonObject();
        anchor.addProperty("kind", "UNRESOLVED_WRITER");
        // Fail closed: two unresolved relations must never collapse merely
        // because their reader-side field names happen to match.
        anchor.addProperty("edgeId", edgeId.isEmpty()
                ? "MISSING_EDGE_ID" : edgeId);
        return anchor;
    }

    private static String canonicalMechanismCell(String value) {
        return value == null ? ""
                : value.replaceAll("#call[0-9]+", "#call");
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

    /**
     * Declares on the receiving task every RPC exchange a replay recorded
     * whose sender is a sibling occurrence this same plan already schedules.
     *
     * <p>README Step 1 judges topology at the exchange event, as the (sender
     * occurrence, receiver occurrence, port) triple.  A receiver the plan
     * schedules more than once alternates between the senders the workload
     * pairs it with, while the plan declares only the pairing the baseline
     * trace saw; the pairing a replay actually took is then a member no plan
     * ever declares, {@link TopologyDelta} reports it on every iteration, and
     * the campaign has no fixed point to reach.  This is the feedback edge
     * that closes it.</p>
     *
     * <p>Nothing is minted.  The declared member is the producer task's own
     * frozen binding for that port, re-addressed to the receiver occurrence
     * the handoff attached at, and only when the receiver already declares
     * that port -- so the ports this task selects are exactly the ports it
     * already selected, and no communication handoff, closure member or
     * output contract changes.  An absorbed member is never a member of the
     * {@link OutputClosureContract}: that would hand the Composer a capture
     * from another occurrence, which is the merge across a cut the README
     * forbids.</p>
     *
     * <p>Every axis is fail-closed and every refusal is named: a sender task
     * this plan does not schedule, a sender or receiver occurrence the plan
     * does not name, a handoff with no recorded send strictly before its
     * receive, and a port the receiver never declared are all refused, and
     * the member stays diverging.</p>
     *
     * @return how many members were declared that no task declared before
     */
    static int absorbObservedExchanges(List<ExecutionTask> tasks,
                                       List<JsonObject> summaries,
                                       Map<String, Integer> refusals) {
        Map<String, ExecutionTask> byTaskId = new LinkedHashMap<>();
        for (ExecutionTask task : tasks) {
            byTaskId.put(task.taskId(), task);
        }
        Set<String> declaredNow = new LinkedHashSet<>();
        int absorbed = 0;
        for (JsonObject summary : summaries) {
            JsonArray handoffs = array(summary, VmHandoffEvidence.FIELD);
            if (handoffs.size() == 0) continue;
            ExecutionTask receiverTask = byTaskId.get(
                    string(summary, "taskId"));
            if (receiverTask == null) {
                refuse(refusals, "RECEIVER_TASK_NOT_IN_FROZEN_PLAN");
                continue;
            }
            // OCC-1: an activation is its planned occurrence plus an ordinal
            // minted at replay, and the ordinal is no member of the exchange.
            String receiver = PathObservation.plannedOccurrenceOf(
                    string(summary, "occurrenceId"));
            if (receiver.isEmpty()
                    || !receiver.equals(receiverTask.occurrenceId())) {
                refuse(refusals, "RECEIVER_OCCURRENCE_NOT_PLANNED");
                continue;
            }
            for (JsonElement element : handoffs) {
                if (!element.isJsonObject()) {
                    refuse(refusals, "HANDOFF_MALFORMED");
                    continue;
                }
                if (absorbObservedExchange(byTaskId, receiverTask, receiver,
                        element.getAsJsonObject(), declaredNow, refusals)) {
                    absorbed++;
                }
            }
        }
        return absorbed;
    }

    /** One recorded handoff: declared on the receiver, or refused by name. */
    private static boolean absorbObservedExchange(
            Map<String, ExecutionTask> byTaskId, ExecutionTask receiverTask,
            String receiver, JsonObject handoff, Set<String> declaredNow,
            Map<String, Integer> refusals) {
        String port = string(handoff, CommunicationCatalogContract.PORT_ID);
        if (port.isEmpty()) {
            refuse(refusals, "HANDOFF_WITHOUT_PORT");
            return false;
        }
        // Send strictly before receive, both endpoints recorded by the VM on
        // this one attach.  Not stated by the evidence, not admitted here.
        long export = longInteger(handoff,
                VmHandoffEvidence.EXPORT_EVENT_ID, -1L);
        long attach = longInteger(handoff,
                VmHandoffEvidence.ATTACH_EVENT_ID, -1L);
        if (export < 0 || attach < 0 || export >= attach) {
            refuse(refusals, "NO_RECORDED_SEND_BEFORE_RECEIVE");
            return false;
        }
        String producer = PathObservation.plannedOccurrenceOf(
                string(handoff, VmHandoffEvidence.PRODUCER_OCCURRENCE_ID));
        if (producer.isEmpty()) {
            refuse(refusals, "HANDOFF_WITHOUT_PRODUCER_OCCURRENCE");
            return false;
        }
        // The sender is a sibling this same frozen plan already schedules --
        // never an address invented from the observation.
        ExecutionTask producerTask = byTaskId.get(
                string(handoff, VmHandoffEvidence.PRODUCER_TASK_ID));
        if (producerTask == null) {
            refuse(refusals, "PRODUCER_TASK_NOT_IN_FROZEN_PLAN");
            return false;
        }
        if (!producer.equals(producerTask.occurrenceId())) {
            refuse(refusals, "PRODUCER_OCCURRENCE_NOT_PLANNED");
            return false;
        }
        JsonArray receiverEdges = array(receiverTask.json(), "edgeBindings");
        if (declaresExchange(receiverEdges, producer, receiver, port)) {
            return false;
        }
        // A port the frozen plan never gave this task is a new port, and this
        // rule never adds one: it re-addresses a pairing, it does not widen a
        // frontier.  This is also what keeps the task's already-retained
        // communication handoffs exactly what they were.
        if (!declaresPort(receiverEdges, port)) {
            refuse(refusals, "PORT_NOT_DECLARED_ON_RECEIVER");
            return false;
        }
        JsonObject template = declaredEdgeFrom(
                array(producerTask.json(), "edgeBindings"), producer, port);
        if (template == null) {
            refuse(refusals, "PRODUCER_DECLARES_NO_EDGE_FOR_PORT");
            return false;
        }
        // The absorbed row keeps the producer's edge id.  That id names the
        // one piece of traced evidence this binding was decoded from, and
        // evidenceIds names it too; minting a second id would claim a second
        // piece of evidence, which is exactly the synthesis this rule exists
        // to avoid.  What the id may never do is alias inside one task --
        // mergeEdgeBindings merges by edge id and would join two pairings
        // into one row -- so a receiver already holding it is refused.
        String edgeId = string(template, "edgeId");
        for (JsonElement element : receiverEdges) {
            if (element.isJsonObject() && edgeId.equals(
                    string(element.getAsJsonObject(), "edgeId"))) {
                refuse(refusals, "ABSORBED_EDGE_ID_ALREADY_DECLARED");
                return false;
            }
        }
        if (!declaredNow.add(receiverTask.taskId() + "\n" + producer + "\n"
                + port)) {
            return false;
        }
        JsonObject declared = template.deepCopy();
        declared.addProperty("toOccurrenceId", receiver);
        // Provenance: this member is declared because a replay recorded it,
        // and these four fields are the whole of what re-derives it.
        declared.addProperty(VmHandoffEvidence.ABSORBED_AUTHORITY_FIELD,
                VmHandoffEvidence.ABSORBED_AUTHORITY);
        declared.addProperty(VmHandoffEvidence.ABSORBED_FROM_TASK_ID,
                producerTask.taskId());
        declared.addProperty(VmHandoffEvidence.ABSORBED_EXPORT_EVENT_ID,
                export);
        declared.addProperty(VmHandoffEvidence.ABSORBED_ATTACH_EVENT_ID,
                attach);
        receiverEdges.add(declared);
        // PlanRow: json() is the live row, and the scheduler alone mutates a
        // task row it has just created.
        receiverTask.json().add("edgeBindings", receiverEdges);
        return true;
    }

    /** Whether these bindings already declare this exact exchange triple. */
    private static boolean declaresExchange(JsonArray edges, String from,
                                            String to, String port) {
        for (JsonElement element : edges) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            if (!from.equals(PathObservation.plannedOccurrenceOf(
                    string(edge, "fromOccurrenceId")))
                    || !to.equals(PathObservation.plannedOccurrenceOf(
                    string(edge, "toOccurrenceId")))) {
                continue;
            }
            if (port.equals(string(edge, "toInputPort"))
                    || port.equals(string(edge, "fromOutputPort"))) {
                return true;
            }
        }
        return false;
    }

    /** Whether this port is on the frontier these bindings already declare. */
    private static boolean declaresPort(JsonArray edges, String port) {
        for (JsonElement element : edges) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            if (port.equals(string(edge, "toInputPort"))
                    || port.equals(string(edge, "fromOutputPort"))) {
                return true;
            }
        }
        return false;
    }

    /** The sender's own frozen binding for this port, or {@code null}. */
    private static JsonObject declaredEdgeFrom(JsonArray edges, String from,
                                               String port) {
        for (JsonElement element : edges) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            if (!from.equals(PathObservation.plannedOccurrenceOf(
                    string(edge, "fromOccurrenceId")))) {
                continue;
            }
            if (port.equals(string(edge, "fromOutputPort"))
                    || port.equals(string(edge, "toInputPort"))) {
                return edge;
            }
        }
        return null;
    }

    private static void refuse(Map<String, Integer> refusals, String code) {
        Integer prior = refusals.get(code);
        refusals.put(code, prior == null ? 1 : prior + 1);
    }

    /** Never silent: what was absorbed, and every refusal by name. */
    private static void reportAbsorbedExchanges(
            int absorbed, Map<String, Integer> refusals) {
        StringBuilder line = new StringBuilder("[schedule] observed exchange "
                + "absorption: declared=" + absorbed);
        for (Map.Entry<String, Integer> refusal : refusals.entrySet()) {
            line.append(" refused[").append(refusal.getKey()).append("]=")
                    .append(refusal.getValue());
        }
        System.err.println(line.toString());
    }

    /** The one serialization of the rows the scheduler built. */
    private static void writeResult(Path output, Result result)
            throws IOException {
        List<JsonObject> rows = new ArrayList<>();
        for (ExecutionTask task : result.executionTasks) {
            rows.add(task.json());
        }
        ArtifactIO.replaceJsonl(output.resolve("execution_task_plan.jsonl"),
                rows);
        ArtifactIO.replaceJsonl(output.resolve("branch_queries.jsonl"),
                result.queries);
    }

    static Result scheduleTargetFirst(Arguments arguments)
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

        List<Result> scheduled = scheduleSelections(arguments, loaded,
                workflow, null);
        List<JsonObject> observations = new ArrayList<>();
        for (Result selected : scheduled) {
            observations.addAll(selected.mechanismObservations);
        }
        SymbolicMechanismCatalog mechanismCatalog =
                SymbolicMechanismCatalog.create(
                        mechanismCatalogInputs(arguments, loaded),
                        observations, loaded.declaredFixedRoots);
        Path mechanismCatalogPath = arguments.outputDirectory.resolve(
                SymbolicMechanismCatalog.FILE_NAME);
        ArtifactIO.replace(mechanismCatalogPath,
                CanonicalJson.render(mechanismCatalog.json()) + "\n");
        JsonObject mechanismCatalogIdentity = artifactIdentity(
                mechanismCatalogPath);

        JsonObject proposalIdentity = null;
        if (arguments.symbolicRootProposal != null) {
            requireFile(arguments.symbolicRootProposal,
                    "symbolic root proposal");
            proposalIdentity = artifactIdentity(
                    arguments.symbolicRootProposal);
            SymbolicMechanismCatalog.Selection mechanismSelection;
            try {
                SymbolicRootProposal proposal = SymbolicRootProposal.decode(
                        ArtifactIO.readObject(
                                arguments.symbolicRootProposal));
                mechanismSelection = mechanismCatalog.validate(proposal);
            } catch (RuntimeException rejected) {
                throw new IOException("symbolic root proposal rejected: "
                        + rejected.getMessage(), rejected);
            }
            requireArtifactIdentity(arguments.symbolicRootProposal,
                    proposalIdentity,
                    "symbolic root proposal changed while loading");
            // Proposal selection changes only materialization.  Target/producer
            // discovery above is intentionally unchanged.
            scheduled = scheduleSelections(arguments, loaded, workflow,
                    mechanismSelection);
        }

        Map<String, ExecutionTask> tasks = new LinkedHashMap<>();
        Map<String, JsonObject> queries = new LinkedHashMap<>();
        for (int index = 0; index < scheduled.size(); index++) {
            RuntimeWorkflowDiscovery.Selection selection =
                    workflow.selections().get(index);
            Result selected = scheduled.get(index);
            if (selected.executionTasks.size() != 1) {
                throw new IOException("target-first selection emitted "
                        + selected.executionTasks.size()
                        + " execution tasks; campaign="
                        + selection.campaignId);
            }
            ExecutionTask task = selected.executionTasks.get(0);
            ExecutionTask prior = tasks.putIfAbsent(task.taskId(), task);
            if (prior != null && !prior.json().equals(task.json())) {
                throw new IOException("conflicting scheduled taskId: "
                        + task.taskId());
            }
            for (JsonObject query : selected.queries) {
                indexTargetQuery(queries, query);
            }
        }
        Result result = new Result();
        result.executionTasks.addAll(sortedValues(tasks));
        result.queries.addAll(sortedValues(queries));
        // The last thing this plan learns, and the only thing it learns from
        // a replay.  It runs exactly here, once, because the member an
        // absorbed pairing re-addresses is another task's frozen binding:
        // scheduleLoaded above emits one task per selection and never sees a
        // sibling, and after writeResult the plan is committed by the digest
        // the schedule index publishes.
        Map<String, Integer> refusals = new TreeMap<>();
        reportAbsorbedExchanges(absorbObservedExchanges(
                result.executionTasks, loaded.summaries, refusals),
                refusals);
        writeResult(arguments.outputDirectory, result);
        Path taskPlan = arguments.outputDirectory.resolve(
                "execution_task_plan.jsonl");
        JsonObject taskPlanIdentity = artifactIdentity(taskPlan);
        JsonObject index = workflow.scheduleIndex(result.executionTasks,
                loaded.regionPlanIdentity, taskPlanIdentity);
        index.add("symbolicRootMechanismCatalog",
                mechanismCatalogIdentity.deepCopy());
        index.add("symbolicRootProposal", proposalIdentity == null
                ? JsonNull.INSTANCE : proposalIdentity.deepCopy());
        requireArtifactIdentity(arguments.regionPlan,
                loaded.regionPlanIdentity,
                "region plan changed while scheduling");
        requireArtifactIdentity(arguments.refinedGraph,
                loaded.refinedGraphIdentity,
                "runtime-refined graph changed while scheduling");
        if (arguments.symbolicInputs != null) {
            requireArtifactIdentity(arguments.symbolicInputs,
                    loaded.symbolicInputsIdentity,
                    "symbolic input selection changed while scheduling");
        }
        if (arguments.symbolicRootProposal != null) {
            requireArtifactIdentity(arguments.symbolicRootProposal,
                    proposalIdentity,
                    "symbolic root proposal changed while scheduling");
        }
        requireArtifactIdentity(mechanismCatalogPath,
                mechanismCatalogIdentity,
                "symbolic root mechanism catalog changed before index "
                        + "publication");
        requireArtifactIdentity(taskPlan, taskPlanIdentity,
                "execution task plan changed before index publication");
        // The integrity-checked index is the commit record.
        ArtifactIO.replace(arguments.outputDirectory.resolve(
                        "runtime_workflow_schedule_index.json"),
                CanonicalJson.render(index) + "\n");
        return result;
    }

    private static List<Result> scheduleSelections(
            Arguments arguments, LoadedInputs loaded,
            RuntimeWorkflowDiscovery.RankedWorkflow workflow,
            SymbolicMechanismCatalog.Selection mechanismSelection)
            throws IOException {
        List<Result> result = new ArrayList<>();
        for (RuntimeWorkflowDiscovery.Selection selection
                : workflow.selections()) {
            try {
                result.add(scheduleLoaded(arguments.forSelection(selection),
                        loaded, selection.producerProjection,
                        mechanismSelection));
            } catch (IllegalArgumentException failure) {
                String projection = selection.producerProjection == null
                        ? "TARGET" : CanonicalJson.render(
                        selection.producerProjection.json());
                throw new IOException("target-first selection is not "
                        + "executable: campaign=" + selection.campaignId
                        + " projection=" + projection, failure);
            }
        }
        return result;
    }

    private static JsonObject mechanismCatalogInputs(
            Arguments arguments, LoadedInputs loaded) {
        JsonObject inputs = new JsonObject();
        inputs.add("regionPlan", loaded.regionPlanIdentity.deepCopy());
        inputs.add("refinedGraph", loaded.refinedGraphIdentity.deepCopy());
        inputs.add("symbolicInputs",
                loaded.symbolicInputsIdentity == null
                        ? JsonNull.INSTANCE
                        : loaded.symbolicInputsIdentity.deepCopy());
        inputs.addProperty("maxLoopIterations",
                arguments.maxLoopIterations);
        inputs.addProperty("workflowAuthority",
                "RANKED_EXACT_RUNTIME_READ_FROM_CLOSURE_V1");
        return inputs;
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

    /** The exact target-query aggregation seam used by target-first. */
    static void indexTargetQuery(Map<String, JsonObject> queries,
                                 JsonObject query) throws IOException {
        String key = JsonFields.string(query, "queryKey");
        if (key.isEmpty()) {
            throw new IOException("scheduled row has no queryKey");
        }
        JsonObject prior = queries.putIfAbsent(key, query);
        if (prior != null && !prior.equals(query)) {
            throw new IOException("conflicting scheduled queryKey: " + key);
        }
    }

    private static <T> List<T> sortedValues(Map<String, T> values) {
        List<String> keys = new ArrayList<>(values.keySet());
        Collections.sort(keys);
        List<T> result = new ArrayList<>();
        for (String key : keys) result.add(values.get(key));
        return result;
    }

    /** Declares this task's selected associative containers as {@code
     * MAP_STATE} shared carriers.
     *
     * <p>README Step 2 asks a selected {@code Map} mutation to publish an
     * immutable whole-map state and a selected {@code Map.get} to bind to the
     * state it may have observed.</p> */
    private static void declareMapStateCarriers(JsonObject task,
                                                JsonArray selectedInputs,
                                                Candidate candidate,
                                                Region region) {
        Map<String, JsonObject> declared = new LinkedHashMap<>();
        // Planner carriers describe the occurrence catalog.
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

    /** Declares the shared locations this task's recorded read-from edges
     * name. */
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
            JsonObject carrier = sharedCarrier(
                    shape == JavaContainerTypes.Shape.ASSOCIATIVE
                            ? SharedStateEvidence.LOCATION_KIND_MAP_STATE
                            : "DECLARED_FIELD", leaf, descriptor, null);
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
        String javaType = string(port, "javaType");
        if (JavaContainerTypes.shape(javaType)
                != JavaContainerTypes.Shape.ASSOCIATIVE) {
            return;
        }
        // A receiver-rooted port is reachable at region entry.
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
        JsonObject carrier = sharedCarrier(
                SharedStateEvidence.LOCATION_KIND_MAP_STATE, field,
                descriptor, accessOwner ? null : path);
        declared.putIfAbsent(mapCarrierKey(carrier), carrier);
    }

    /** One shared-location declaration.  A {@code null} path means the owner
     *  is the object the instrumented access in this activation touched, and
     *  nothing else: the runtime binds that shape at the exact field access
     *  rather than searching the heap for a same-named receiver. */
    private static JsonObject sharedCarrier(
            String kind, FieldPathSpec.DeclaredField field,
            String descriptor, JsonArray fieldPath) {
        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind", kind);
        carrier.addProperty("declaringClass", field.owner());
        carrier.addProperty("fieldName", field.name());
        carrier.addProperty("descriptor", descriptor);
        if (fieldPath == null) {
            carrier.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
            carrier.add("fieldPath", new JsonArray());
        } else {
            carrier.add("fieldPath", fieldPath.deepCopy());
        }
        return carrier;
    }

    /** One causal edge can be represented by a refined runtime row and by a
     * compact closure row. */
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
        JsonArray result = new JsonArray();
        for (JsonObject row : rows.values()) result.add(row.deepCopy());
        return result;
    }

    private static List<Candidate> candidates(Arguments arguments,
                                              List<RegionInstancePlan>
                                                      regionPlans,
                                              Map<String, Region> regions,
                                              DefinitionIndex definitions,
                                              ProducerOutputProjection
                                                      producerProjection)
            throws IOException {
        List<Candidate> result = new ArrayList<>();
        for (RegionInstancePlan plan : regionPlans) {
            // Target-first scheduling selects one exact occurrence at a time.
            if (!arguments.occurrenceId.isEmpty()
                    && !arguments.occurrenceId.equals(plan.occurrenceId())) {
                continue;
            }
            if (!arguments.regionId.isEmpty()
                    && !arguments.regionId.equals(plan.regionId())) {
                continue;
            }
            Region region = regions.get(plan.regionId());
            if (region == null) {
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
                appendGoalCandidates(arguments, result, goal,
                        definitions, producerProjection);
            }
        }
        return result;
    }

    /** The per-loop {@code K_L} the region plan declares, as one contract.
     *
     * <p>A declared {@code K_L} that happens to equal the inherited bound
     * used to be dropped as redundant, but README {@code LOOP-1} accepts no
     * condition loop running under an inherited bound: dropping it would turn
     * four of HDFS-11741's own declarations back into silence and get the
     * loops they name refused as undeclared.</p> */
    static LoopBoundPolicy declaredLoopBounds(
            int inheritedBound, List<RegionInstancePlan> regionPlans) {
        Map<String, Integer> declared = new TreeMap<>();
        for (RegionInstancePlan plan : regionPlans) {
            for (JsonElement element : array(plan.json(),
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
        return LoopBoundPolicy.cfgBackedges(inheritedBound, declared);
    }

    private static void appendGoalCandidates(
            Arguments arguments, List<Candidate> result, Goal goal,
            DefinitionIndex definitions,
            ProducerOutputProjection producerProjection)
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
                    outputClosure = OutputClosureCodec
                            .projectSelectedVersions(outputClosure,
                            selectedOutgoingEdges(goal,
                                    producerProjection));
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
            // guarded throw.
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
                // slice is replayed prefix.
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

    /** Selected runtime edges grouped by the output member they consume. */
    private static Map<String, Set<String>> selectedOutgoingEdges(
            Goal goal, ProducerOutputProjection projection) {
        Map<String, Set<String>> result = new LinkedHashMap<>();
        for (JsonElement element : goal.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            String edgeId = string(edge, "edgeId");
            String output = string(edge, "fromOutputPort");
            if (!projection.edgeIds().contains(edgeId)
                    || !projection.outputPorts().contains(output)
                    || !goal.plan().occurrenceId().equals(
                    string(edge, "fromOccurrenceId"))) {
                continue;
            }
            result.computeIfAbsent(output,
                    ignored -> new LinkedHashSet<>()).add(edgeId);
        }
        return result;
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

    /** A target VM job has no reason to materialize a concrete owner merely
     * because the backward slice traversed through it. */
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
        for (JsonElement element : goal.edgeBindings()) {
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

    /** A selected response delivery remains part of the replay topology even
     * when the branch currently being reopened does not consume its value;
     * an exact component edge is target topology, not a local symbolic root.
     */
    private static boolean selectedWorkflowHandoffBinding(
            JsonObject binding) {
        if (!string(binding,
                CommunicationCatalogContract.PORT_COMPONENT_OF).isEmpty()
                && !string(binding,
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH).isEmpty()
                && !string(binding,
                CommunicationCatalogContract.PORT_ENCODING_AUTHORITY)
                .isEmpty()) {
            return true;
        }
        return "RUNTIME_PROTOCOL_FLOW".equals(string(binding, "kind"))
                && "RESPONSE".equalsIgnoreCase(
                string(binding, "direction"))
                && !string(binding, "fromOutputPort").isEmpty()
                && !string(binding, "toInputPort").isEmpty();
    }

    /** A target task solves one failure-directed branch. */
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

    /** Bounded control metadata needed to distinguish a terminal exception
     * guard from an observed frontier leading to a still-unobserved guard. */
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
        // The frame the root-entry hooks are injected into.
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
                    supportedBoundedContainerState(action, location);
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
                // selected for replay.
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
                // Output capture is demand-first.
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
                // decision can read the value.
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_UNGUARDED_PAYLOAD");
                continue;
            }
            if (scope != null && !scope.inputPorts().contains(
                    string(action, "symbol"))) {
                // The output closure is the authority for symbolic demand.
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_OUTSIDE_OUTPUT_CLOSURE_SCOPE");
                continue;
            }
            if (action.has("observed")
                    && !bool(action, "observed", false)) {
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
                    binding.addProperty("bindingMode", "METHOD_ARGUMENT");
                    binding.addProperty("method", argumentMethod);
                    binding.addProperty("index", argumentIndex);
                } else {
                    binding.addProperty("bindingMode", "ROOT_ENTRY");
                }
            } else if ("ARGUMENT_FIELD_PATH".equals(location)) {
                if (FieldPathSpec.hasNonEmptyPaths(action, "fieldPaths")) {
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
                    addInputAction(result, represented, localBinding,
                            InputActionCatalog.Mode.SYMBOLIC);
                }
                continue;
            } else if ("HEAP_OBJECT_FIELD".equals(location)) {
                binding.addProperty("bindingMode", "FIELD_ACCESS");
                List<String> path = FieldPathSpec.path(cell);
                // The one complete leaf declaration that is internally exact
                // for this direct getfield path.
                JsonObject declaredLeaf = FieldPathSpec.exactLeafDeclaration(
                        action, path,
                        "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1");
                if (path.size() > 2 && declaredLeaf == null) {
                    addConcreteInputAction(result, represented, binding,
                            "CONCRETE_UNDECLARED_HEAP_FIELD_PATH");
                    continue;
                }
                if (path.size() > 1
                        && action.has("valueObjectId")
                        && longInteger(action, "valueObjectId", 0L) == 0L) {
                    // The concrete discovery observed the first projected
                    // reference as null.
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

    /** Projects an exact Atomic mutation read-from carrier to the primitive
     * state actually consumed by the target branch. */
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
        for (JsonElement element : goal.edgeBindings()) {
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

    /** Input ports a demanded output capture is anchored on. */
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

    /** Operands of the decisions this task actually reopens. */
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

    /** R1: a leaf earns a solver dimension only by being able to move some
     * explored decision. */
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

    /** Admits only values for which the current VM/SMT contract has a compact
     * scalar representation. */
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

    /** Admits a container identity only as a bounded relational state port. */
    private static boolean supportedBoundedContainerState(
            JsonObject action, String location) {
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
        // The declared field path states the leaf exactly; the root signature
        // is the leaf only when the path is one hop.  Order says so.
        for (String signature : new String[]{
                pathLeafFieldSignature(action, cell),
                firstNonBlank(string(action, "accessFieldSignature"),
                        string(action, "leafFieldSignature")), cell}) {
            FieldPathSpec.DeclaredField declared =
                    FieldPathSpec.declaredField(signature);
            if (declared != null) return declared;
        }
        return null;
    }

    /** The declaration of the last hop of a receiver/heap field path. */
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
        if ("CONSTANT".equals(string(action, "sourceKind"))) {
            return true;
        }
        List<String> path = exactActionFieldPath(action,
                string(action, "cell"));
        return !path.isEmpty()
                && "$assertionsDisabled".equals(
                path.get(path.size() - 1));
    }

    /** Classifies compiler/runtime structure projections, not application
     * values. */
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
            // backing cardinality through a direct size() accessor.
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
        action.addProperty("mode", mode.name());
        represented.add(string(action, "symbol"));
        result.add(action);
    }

    /** The only way an input leaves {@link #materializationPlan} concrete. */
    static void addConcreteInputAction(
            JsonArray result, Set<String> represented,
            JsonObject binding, String reason) {
        binding.addProperty("symbolicDemand",
                reason == null || reason.trim().isEmpty()
                        ? "CONCRETE_UNNAMED_REFUSAL" : reason.trim());
        addInputAction(result, represented, binding,
                InputActionCatalog.Mode.CONCRETE);
    }

    /** Names why an action was concrete before any leaf support was examined:
     * either the producing stage already declared it concrete-only, or its
     * dependency role is not a value frontier at all. */
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
        // The query is the target relation consumed by composition.
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
            // This artifact is consumed by the target path-set builder, not by
            // the local path-flip solver.
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

    /** Target closure starts from the imported seed path, not from one
     * privileged Jimple branch. */
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

    /** Selects target-PC provenance only from the exact runtime region
     * instance and closure goal. */
    private static JsonObject exactTargetSummary(
            Candidate candidate, List<JsonObject> summaries) {
        String expectedInstance = candidate.goal.plan().occurrenceId();
        if (expectedInstance.isEmpty()) return null;
        // OCC-1: one target address publishes one summary per activation,
        // named <address>#a<ordinal>.  The candidate is keyed on the planned
        // address, so the seed is matched on the address and not on any one
        // activation of it.
        //
        // The seed's replay contract is a FLIP base: it names a branch the
        // replay took one way and requires the other way (the failure).  So
        // the seed is a non-failing sibling of the throw -- an activation
        // that did NOT reach the target, whose target branch flips to the
        // required failure outcome.  The throw activation itself is consumed
        // downstream by the reach-query builder as the direct failure
        // witness (directRequiredWitness), which is where the studied
        // exceptional exit actually enters the query; seeding the flip from
        // the throw would require the branch to flip to a polarity the throw
        // already took and the builder rejects it.
        JsonObject flipSeed = null;
        JsonObject anyComplete = null;
        for (JsonObject summary : summaries) {
            if (!candidate.goal.goalId().equals(string(summary, "goalId"))
                    || !candidate.goal.plan().regionId().equals(
                    string(summary, "regionId"))
                    || !expectedInstance.equals(
                    PathObservation.plannedOccurrenceOf(
                            string(summary, "occurrenceId")))
                    || !ClosureGoalKind.fromTask(summary)
                    .capturesTargetReach()
                    || !bool(summary, "relationallyComplete", false)
                    || string(summary, "summaryId").isEmpty()) {
                continue;
            }
            if (anyComplete == null) anyComplete = summary;
            if (flipSeed == null
                    && !bool(summary, PathObservation.TARGET_REACHED,
                    false)) {
                flipSeed = summary;
            }
        }
        // Prefer the non-failing flip base.  When every activation of the
        // address reached the target -- no sibling to flip from -- fall back
        // to a complete target summary so a query is still published; the
        // reach-query builder is the one authority that refuses a target
        // with no attested flip.
        return flipSeed != null ? flipSeed : anyComplete;
    }

    /** The one option scan of this entry point: {@code --key value} pairs,
     *  a bare {@code --flag} reading "true", and no unknown key. */
    static Map<String, String> parseArgs(String[] args, String... known) {
        Set<String> options = new LinkedHashSet<>(Arrays.asList(known));
        Map<String, String> values = new LinkedHashMap<>();
        for (int index = 0; args != null && index < args.length; index++) {
            String value = args[index];
            if (!value.startsWith("--")) {
                throw new IllegalArgumentException(
                        "Unexpected scheduler argument: " + value);
            }
            String key = value.substring(2);
            if (!options.contains(key)) {
                throw new IllegalArgumentException(
                        "Unknown scheduler option --" + key);
            }
            boolean hasNext = index + 1 < args.length
                    && !args[index + 1].startsWith("--");
            values.put(key, hasNext ? args[++index] : "true");
        }
        return values;
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

        /** Cells from which one of the given guard operands is still
         * reachable. */
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

        /** Exact producer guard demand never crosses a method boundary. */
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

        private JsonObject outputRow(String portId) {
            JsonObject row = outputRowsByPort.get(portId);
            return row == null ? null : row.deepCopy();
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

    /** Validates the target-first demand and uses it only to select a producer
     * occurrence. */
    private static boolean selectsProducerOccurrence(
            Goal goal, ProducerOutputProjection projection) {
        projection.requireMatches(goal);
        Set<String> foundEdges = new LinkedHashSet<>();
        Set<String> foundOutputs = new LinkedHashSet<>();
        Set<String> occurrences = new LinkedHashSet<>();
        for (JsonElement element : goal.edgeBindings()) {
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

        /** Stable task identity: source occurrence x relation content x exact
         * port set (x target predicate for reach goals). */
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

        /** Canonical ordinal-free port descriptors. Runtime port ids embed
         * trace call ids, so the identity uses each port's static semantic
         * shape instead: location/cell/site/declared field path for inputs,
         * and cell/kind/type plus static capture endpoints (with their
         * replay-stable bounded occurrence) for demanded outputs. */
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
                "location", "outputCell",
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

    /** Describes the existing selection/admission decision without adding one.
     */
    static String noCandidateDiagnostic(
            Arguments arguments, List<RegionInstancePlan> rows) {
        RegionInstancePlan selected = null;
        Goal selectedGoal = null;
        boolean regionFound = false;
        for (RegionInstancePlan plan : rows) {
            if (!arguments.regionId.isEmpty()
                    && !arguments.regionId.equals(plan.regionId())) continue;
            regionFound = true;
            if (!arguments.occurrenceId.isEmpty()
                    && !plan.occurrenceId().equals(
                    arguments.occurrenceId.trim())) continue;
            if (selected == null) {
                // Remembered only so an unmatched goal still reports which
                // fragments were searched.
                selected = plan;
            }
            Goal found = null;
            for (Goal goal : plan.goals()) {
                if (!arguments.goalId.isEmpty()
                        && !arguments.goalId.equals(goal.goalId())) continue;
                found = goal;
                break;
            }
            if (found == null) continue;
            selected = plan;
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
                : string(selected.json(), "targetMethod");
        JsonObject root = selected == null ? new JsonObject()
                : object(selected.json(), "rootSelector");
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
        public final List<ExecutionTask> executionTasks = new ArrayList<>();
        public final List<JsonObject> queries = new ArrayList<>();
        private final List<JsonObject> mechanismObservations =
                new ArrayList<>();
    }

    /**
     * Optional experiment-owned allowlist of symbolic roots.
     *
     * <p>Wave 3: the only surviving job is turning declared FIELD signatures
     * into SYMBOLIC materialization actions and everything else CONCRETE.
     * Which symbol reaches which read is decided at replay -- the VM's
     * propagated expression is the authority -- so no selector, selected
     * phase, producer version or output-version boundary is predicted here.
     * </p>
     */
    static final class SymbolicInputSelection {
        private final boolean configured;
        /** regionId -> the field signatures, port ids and cells it admits. */
        private final Map<String, Set<String>> admitted;
        /** regionId -> sourceId -> the one field that hook site mints. */
        private final Map<String, Map<String, String>> minted;

        private SymbolicInputSelection(
                boolean configured, Map<String, Set<String>> admitted,
                Map<String, Map<String, String>> minted) {
            this.configured = configured;
            this.admitted = admitted;
            this.minted = minted;
        }

        /** One pass over the static hook declarations and, when the campaign
         *  configured one, over the declared field/port/cell rows. */
        static SymbolicInputSelection read(
                Path path, List<JsonObject> regionCatalog)
                throws IOException {
            Map<String, Map<String, String>> minted = new LinkedHashMap<>();
            Set<String> catalogRegions = new LinkedHashSet<>();
            for (JsonObject region : regionCatalog == null
                    ? Collections.<JsonObject>emptyList() : regionCatalog) {
                String regionId = string(region, "regionId");
                if (!regionId.isEmpty()) catalogRegions.add(regionId);
                for (JsonElement element : array(region,
                        StaticSymbolicSourceDeclaration.FIELD)) {
                    if (!element.isJsonObject() || regionId.isEmpty()) {
                        throw new IOException("static symbolic source has no "
                                + "declaring region");
                    }
                    declareMintSite(minted.computeIfAbsent(regionId,
                            ignored -> new LinkedHashMap<>()),
                            element.getAsJsonObject());
                }
            }
            Map<String, Set<String>> admitted = new LinkedHashMap<>();
            if (path == null) {
                return new SymbolicInputSelection(!minted.isEmpty(),
                        admitted, minted);
            }
            requireFile(path, "symbolic input selection");
            for (JsonObject row : ArtifactIO.readJsonl(path)) {
                String regionId = firstNonBlank(string(row, "regionId"));
                if (regionId.isEmpty()) {
                    throw new IOException("symbolic input selection row has "
                            + "no regionId: " + row);
                }
                if (!catalogRegions.contains(regionId)) {
                    throw new IOException("symbolic input selection names "
                            + "an unknown static region: " + regionId);
                }
                Set<String> names = admitted.computeIfAbsent(regionId,
                        ignored -> new LinkedHashSet<>());
                for (String field : new String[]{
                        "fieldSignatures", "portIds", "cells"}) {
                    addDeclaredNames(names, row, field);
                }
            }
            return new SymbolicInputSelection(true, admitted, minted);
        }

        /** An explicit source hook is itself the allowlist authority. */
        private static void declareMintSite(
                Map<String, String> sites, JsonObject row) throws IOException {
            String sourceId = firstNonBlank(string(row, "sourceId"));
            String field = firstNonBlank(string(row, "fieldSignature"));
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
            if (string(row, "declarationMethod").isEmpty()
                    || JsonFields.exactInteger(row,
                    "declarationUnitIndex", -1) < 0) {
                throw new IOException("malformed static symbolic source "
                        + "declaration location");
            }
            String prior = sites.putIfAbsent(sourceId, field);
            if (prior != null && !prior.equals(field)) {
                throw new IOException("static symbolic source declaration "
                        + "gives one sourceId two fields: " + sourceId);
            }
        }

        private static void addDeclaredNames(
                Set<String> output, JsonObject row, String field)
                throws IOException {
            JsonElement encoded = row.get(field);
            if (encoded == null) return;
            if (!encoded.isJsonArray()) {
                throw new IOException("symbolic input selection " + field
                        + " must be an array");
            }
            for (JsonElement element : encoded.getAsJsonArray()) {
                if (!element.isJsonPrimitive()
                        || !element.getAsJsonPrimitive().isString()
                        || firstNonBlank(element.getAsString()).isEmpty()) {
                    throw new IOException("symbolic input selection " + field
                            + " entries must be non-empty strings");
                }
                output.add(firstNonBlank(element.getAsString()));
            }
        }

        JsonArray select(String regionId, JsonArray actions) {
            if (!configured) return actions.deepCopy();
            JsonArray selected = new JsonArray();
            for (JsonElement element : actions) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                JsonObject retained = action.deepCopy();
                // Every input remains declared because output captures and
                // concrete topology may use it as an anchor.
                if ("SYMBOLIC".equals(string(action, "mode"))) {
                    if (minted(regionId, action)) {
                        // The Java hook mints this exact root once.
                        retained.addProperty("mode", "CONCRETE");
                        retained.addProperty("symbolicDemand",
                                "CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED");
                    } else if (!admits(regionId, action)) {
                        retained.addProperty("mode", "CONCRETE");
                        retained.addProperty("symbolicDemand",
                                "CONFIGURED_SYMBOLIC_INPUT_UNSELECTED");
                    }
                }
                selected.add(retained);
            }
            return selected;
        }

        /** Keeps manual target roots needed by any guard of the same throw. */
        JsonArray includeTargetSourceFrontier(
                String regionId, JsonArray branchActions,
                JsonArray guardedTargetActions) {
            JsonArray result = branchActions == null
                    ? new JsonArray() : branchActions.deepCopy();
            if (!configured || guardedTargetActions == null
                    || guardedTargetActions.size() == 0
                    || !minted.containsKey(safe(regionId))) {
                return result;
            }
            Set<String> represented = new LinkedHashSet<>();
            for (JsonElement element : result) {
                if (!element.isJsonObject()) continue;
                String symbol = actionPort(element.getAsJsonObject());
                if (!symbol.isEmpty()) represented.add(symbol);
            }
            for (JsonElement element : guardedTargetActions) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                String symbol = actionPort(action);
                if (symbol.isEmpty() || represented.contains(symbol)
                        || !"SYMBOLIC".equals(string(action, "mode"))
                        || !minted(regionId, action)
                        // A relation-bound root is already carried by the
                        // edge the target task selected.
                        || "EXACT_INCOMING_COMPOSITION".equals(
                        string(action, "symbolicDemand"))
                        || !string(action, "selectedIncomingEdgeId").isEmpty()
                        || !string(action,
                        "intraRegionReadFromAuthority").isEmpty()) {
                    continue;
                }
                result.add(action.deepCopy());
                represented.add(symbol);
            }
            return result;
        }

        /** Applies the same allowlist before target-first producer closure. */
        boolean selectedForDiscovery(String regionId, JsonObject action) {
            if (!configured) return true;
            return !minted(regionId, action) && admits(regionId, action);
        }

        /** Source-derived outputs augment only an already ranked producer. */
        private Set<String> sourceOutputCellsForDiscovery(
                String regionId, OutputClosureContract closure) {
            Set<String> matches = new LinkedHashSet<>();
            if (!configured || closure == null) return matches;
            for (String fieldSignature : minted.getOrDefault(safe(regionId),
                    Collections.<String, String>emptyMap()).values()) {
                for (OutputClosureContract.Member member
                        : closure.members()) {
                    for (JsonElement declaration : array(member.slice(),
                            "demandedHeapDeclarations")) {
                        if (declaration.isJsonPrimitive()
                                && fieldSignature.equals(
                                declaration.getAsString())) {
                            matches.add(member.cell());
                        }
                    }
                }
            }
            return matches;
        }

        /** Whether a declaring hook site of this region mints the action's
         *  field: one field is one root, and the hook owns it. */
        private boolean minted(String regionId, JsonObject action) {
            String field = actionField(action);
            return !field.isEmpty() && minted.getOrDefault(safe(regionId),
                    Collections.<String, String>emptyMap())
                    .containsValue(field);
        }

        private boolean admits(String regionId, JsonObject action) {
            Set<String> names = admitted.get(safe(regionId));
            return names != null
                    && (names.contains(actionField(action))
                    || names.contains(actionPort(action))
                    || names.contains(string(action, "cell")));
        }

        private static String actionField(JsonObject action) {
            return firstNonBlank(string(action, "accessFieldSignature"),
                    string(action, "declaredFieldSignature"));
        }

        private static String actionPort(JsonObject action) {
            return firstNonBlank(string(action, "portId"),
                    string(action, "symbol"));
        }
    }

    private static final class LoadedInputs {
        private final List<RegionInstancePlan> regionPlans;
        private final List<JsonObject> summaries;
        private final Map<String, Region> regionIndex;
        private final DefinitionIndex definitions;
        private final JsonObject regionPlanIdentity;
        private final JsonObject refinedGraphIdentity;
        private final JsonObject symbolicInputsIdentity;
        private final JsonArray declaredFixedRoots;
        private final SymbolicInputSelection symbolicInputs;

        private LoadedInputs(List<RegionInstancePlan> regionPlans,
                             List<JsonObject> summaries,
                             Map<String, Region> regionIndex,
                             DefinitionIndex definitions,
                             JsonObject regionPlanIdentity,
                             JsonObject refinedGraphIdentity,
                             JsonObject symbolicInputsIdentity,
                             JsonArray declaredFixedRoots,
                             SymbolicInputSelection symbolicInputs) {
            this.regionPlans = regionPlans;
            this.summaries = summaries;
            this.regionIndex = regionIndex;
            this.definitions = definitions;
            this.regionPlanIdentity = regionPlanIdentity;
            this.refinedGraphIdentity = refinedGraphIdentity;
            this.symbolicInputsIdentity = symbolicInputsIdentity;
            this.declaredFixedRoots = declaredFixedRoots.deepCopy();
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
        public final int maxJobs;
        public final int maxLoopIterations;
        public final Path symbolicInputs;
        public final Path symbolicRootProposal;
        private final Set<String> targetEdgeIds;

        private Arguments(Path regionPlan, Path refinedGraph, Path summaries,
                          Path outputDirectory, String regionId,
                          String occurrenceId, String goalId,
                          int maxJobs, int maxLoopIterations,
                          Path symbolicInputs,
                          Path symbolicRootProposal,
                          Set<String> targetEdgeIds) {
            this.regionPlan = regionPlan;
            this.refinedGraph = refinedGraph;
            this.summaries = summaries;
            this.outputDirectory = outputDirectory;
            this.regionId = safe(regionId);
            this.occurrenceId = safe(occurrenceId);
            this.goalId = safe(goalId);
            this.maxJobs = Math.max(1, maxJobs);
            this.maxLoopIterations = maxLoopIterations;
            this.symbolicInputs = symbolicInputs;
            this.symbolicRootProposal = symbolicRootProposal;
            this.targetEdgeIds = Collections.unmodifiableSet(
                    new LinkedHashSet<>(targetEdgeIds));
        }

        public static Arguments parse(String[] args) {
            Map<String, String> values = parseArgs(args, "region-plan",
                    "refined-graph", "summaries", "output-dir", "max-jobs",
                    "symbolic-inputs", "symbolic-root-proposal",
                    "max-loop-iterations");
            Path regionPlan = requiredPath(values, "region-plan");
            Path output = Paths.get(firstNonBlank(values.get("output-dir"),
                    ArtifactIO.sibling(regionPlan,
                            "concolic-schedule").toString()));
            Path refinedGraph = requiredPath(values, "refined-graph");
            Path summaries = optionalPath(values.get("summaries"));
            Path symbolicInputs = optionalPath(
                    values.get("symbolic-inputs"));
            Path symbolicRootProposal = optionalPath(
                    values.get("symbolic-root-proposal"));
            // The scheduler has one mode: the whole target-first closure.
            return new Arguments(regionPlan, refinedGraph,
                    summaries, output, "", "", "",
                    parseInt(values.get("max-jobs"), 1),
                    positiveInt(values.get("max-loop-iterations"),
                            LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                            "max-loop-iterations"),
                    symbolicInputs,
                    symbolicRootProposal,
                    Collections.<String>emptySet());
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
                    selection.goalId, 1, maxLoopIterations,
                    symbolicInputs,
                    symbolicRootProposal,
                    selection.targetEdgeIds);
        }

    }
}
