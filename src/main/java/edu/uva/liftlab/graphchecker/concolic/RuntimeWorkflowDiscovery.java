package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.Goal;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;

import java.io.IOException;
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

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;

/**
 * Discovers the producer and target campaigns in one runtime region plan.
 *
 * <p>Producer position is graph-relative: a producer may supply another
 * producer or the target.  Field names and graph depth therefore never become
 * workflow identities.</p>
 */
public final class RuntimeWorkflowDiscovery {
    private static final Pattern CALL_ID = Pattern.compile(
            "(?:^|[#@])call([0-9]+)(?:$|[^0-9])");
    private static final Pattern GOAL_DIGEST = Pattern.compile(
            "(?i)([0-9a-f]{8,})$");

    private final List<RegionInstancePlan> plans = new ArrayList<>();
    private final List<Target> targets;
    private final Target target;

    private RuntimeWorkflowDiscovery(Path regionPlan, String targetInstance,
                                     String targetGoal) throws IOException {
        this(RuntimePlanArtifact.read(regionPlan).plans(), targetInstance,
                targetGoal);
    }

    private RuntimeWorkflowDiscovery(Iterable<JsonObject> regionPlan,
                                     String targetInstance,
                                     String targetGoal) throws IOException {
        Set<String> instances = new LinkedHashSet<>();
        for (JsonObject row : regionPlan) {
            RegionInstancePlan plan = RegionInstancePlan.decode(row);
            if (!instances.add(plan.occurrenceId())) {
                throw new IOException("duplicate occurrenceId: "
                        + plan.occurrenceId());
            }
            plans.add(plan);
        }
        if (plans.isEmpty()) {
            throw new IOException("runtime region plan is empty");
        }
        targets = discoverTargets();
        target = selectTarget(targetInstance, targetGoal);
    }

    /**
     * Materializes the ranked target-first workflow from an already decoded
     * region plan.  The scheduler uses this entry point so discovery and all
     * selected goals share one parse of the large runtime artifact.
     */
    static RankedWorkflow rankedWorkflow(List<JsonObject> regionPlan)
            throws IOException {
        RuntimeWorkflowDiscovery discovery =
                new RuntimeWorkflowDiscovery(regionPlan, "", "");
        Target selected = discovery.targets.get(0);
        if (!selected.goal.replayable()) {
            throw new IOException("ranked target goal is not replayable; "
                    + selected.context());
        }
        return new RankedWorkflow(selected,
                discovery.discoverDemands(selected));
    }

    public static void main(String[] argv) throws Exception {
        Map<String, String> args = parseArgs(argv);
        String command = required(args, "command");
        RuntimeWorkflowDiscovery discovery = new RuntimeWorkflowDiscovery(
                Paths.get(required(args, "region-plan")),
                optional(args, "target-instance"),
                optional(args, "target-goal"));
        switch (command) {
            case "discover":
                discovery.printDiscovery();
                return;
            case "producer-demands":
                for (Demand demand : discovery.discoverDemands()) {
                    System.out.println(demand.campaignId);
                }
                return;
            case "producer-binding": {
                Demand demand = discovery.demand(
                        required(args, "campaign"));
                System.out.println(demand.binding());
                return;
            }
            case "producer-projection": {
                Demand demand = discovery.demand(
                        required(args, "campaign"));
                System.out.println(CanonicalJson.render(
                        demand.projection().json()));
                return;
            }
            case "target-binding":
                System.out.println(discovery.requireTarget().binding());
                return;
            case "target-bindings":
                for (Target candidate : discovery.targets) {
                    System.out.println(candidate.binding());
                }
                return;
            case "scheduled-task":
                System.out.println(discovery.scheduledProducerTask(
                        required(args, "campaign"),
                        Paths.get(required(args, "task-plan"))));
                return;
            case "scheduled-target-task":
                System.out.println(discovery.scheduledTargetTask(
                        Paths.get(required(args, "task-plan"))));
                return;
            default:
                throw new IllegalArgumentException(
                        "unknown discovery command: " + command);
        }
    }

    /**
     * Selects one READY producer alternative for each exact downstream input
     * in the reverse runtime read-from closure rooted at the target.
     * A selected relation may discharge several distinct inputs at once.
     */
    private List<Demand> discoverDemands() throws IOException {
        return discoverDemands(requireTarget());
    }

    private List<Demand> discoverDemands(Target selectedTarget)
            throws IOException {
        DemandClosure closure = discoverDemandClosure(selectedTarget);
        if (closure.demands.isEmpty()) {
            throw new IOException("runtime read-from graph has no executable "
                    + "producer path to target; targetRegion="
                    + selectedTarget.regionId + "; targetInstance="
                    + selectedTarget.occurrenceId + "; outputGoals="
                    + outputGoalAdmissions());
        }
        return closure.demands;
    }

    private DemandClosure discoverDemandClosure(Target selectedTarget)
            throws IOException {
        Map<Endpoint, List<ProducerCandidate>> producersByDownstream =
                new LinkedHashMap<>();
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (!goal.kind().capturesOutputRelation()) {
                    continue;
                }
                List<JsonObject> edges = trustedEdges(plan, goal);
                if (!edges.isEmpty()) {
                    ProducerCandidate candidate =
                            new ProducerCandidate(plan, goal, edges);
                    for (Endpoint downstream
                            : candidate.downstreamEndpoints) {
                        producersByDownstream.computeIfAbsent(downstream,
                                ignored -> new ArrayList<>())
                                .add(candidate);
                    }
                }
            }
        }

        // This is the target's fatal input frontier, before producer inputs
        // extend the recursive closure.  Ranking is about freedom left on the
        // fault predicate itself, so retain this boundary separately from the
        // producer inputs subsequently added to frontier.
        Set<Endpoint> fatalInputs = new LinkedHashSet<>();
        for (JsonElement item : selectedTarget.goal.symbolize()) {
            if (!item.isJsonObject()) continue;
            JsonObject action = item.getAsJsonObject();
            String input = string(action, "symbol");
            if (input.isEmpty()) continue;
            Endpoint endpoint = new Endpoint(
                    selectedTarget.occurrenceId,
                    selectedTarget.exactInput(input));
            if (causalAction(action)
                    || exactTrustedProjectedProducer(endpoint,
                    producersByDownstream)) {
                fatalInputs.add(endpoint);
            }
        }
        Set<Endpoint> frontier = new LinkedHashSet<>(fatalInputs);
        Map<Endpoint, ProducerCandidate> producerByEndpoint =
                new LinkedHashMap<>();
        Map<ProducerCandidate, Demand> selected = new LinkedHashMap<>();
        while (true) {
            Set<Endpoint> unresolved = new LinkedHashSet<>(frontier);
            unresolved.removeAll(producerByEndpoint.keySet());
            List<ProducerChoice> choices = new ArrayList<>();
            Set<ProducerCandidate> eligible = new LinkedHashSet<>();
            for (Endpoint downstream : unresolved) {
                for (ProducerCandidate candidate
                        : producersByDownstream.getOrDefault(downstream,
                        java.util.Collections.emptyList())) {
                    if (candidate.ready()) eligible.add(candidate);
                }
            }
            for (ProducerCandidate candidate : eligible) {
                Demand demand = selected.get(candidate);
                try {
                    if (demand == null) demand = candidate.materialize();
                    ProducerChoice choice = new ProducerChoice(candidate,
                            demand, unresolved,
                            selected.containsKey(candidate));
                    if (!choice.coveredEndpoints.isEmpty()) {
                        choices.add(choice);
                    }
                } catch (IllegalArgumentException malformed) {
                    throw new IOException("invalid logical producer "
                            + "occurrence catalog; "
                            + context(candidate.plan, candidate.goal),
                            malformed);
                }
            }
            if (choices.isEmpty()) break;
            choices.sort(ProducerChoice.ORDER);
            ProducerChoice choice = choices.get(0);
            requireReady(choice.demand);
            selected.put(choice.candidate, choice.demand);
            for (Endpoint endpoint : choice.coveredEndpoints) {
                ProducerCandidate prior = producerByEndpoint.putIfAbsent(
                        endpoint, choice.candidate);
                if (prior != null && prior != choice.candidate) {
                    throw new IOException("exact downstream input selected "
                            + "more than one producer: "
                            + endpoint.binding());
                }
            }
            choice.demand.addRequiredInputs(choice.coveredEndpoints,
                    choice.candidate, frontier, producersByDownstream);
        }

        Set<Endpoint> discharged = producerByEndpoint.keySet();
        Set<String> blocked = new LinkedHashSet<>();
        for (Endpoint downstream : frontier) {
            if (discharged.contains(downstream)) continue;
            for (ProducerCandidate candidate
                    : producersByDownstream.getOrDefault(downstream,
                    java.util.Collections.emptyList())) {
                if (!candidate.ready()) {
                    blocked.add("endpoint=" + downstream.binding()
                            + "; " + context(candidate.plan,
                            candidate.goal));
                }
            }
        }
        if (!blocked.isEmpty()) {
            throw new IOException("runtime read-from graph has blocked exact "
                    + "producer closure; targetRegion="
                    + selectedTarget.regionId + "; targetInstance="
                    + selectedTarget.occurrenceId
                    + "; blockedProducers=" + blocked);
        }

        Map<Endpoint, JsonObject> selectedEdgeByEndpoint =
                new LinkedHashMap<>();
        for (Demand demand : selected.values()) {
            for (Map.Entry<Endpoint, JsonObject> edge
                    : demand.selectedEdges.entrySet()) {
                JsonObject prior = selectedEdgeByEndpoint.putIfAbsent(
                        edge.getKey(), edge.getValue());
                if (prior != null && !required(prior, "edgeId").equals(
                        required(edge.getValue(), "edgeId"))) {
                    throw new IOException("exact downstream input selected "
                            + "more than one output: "
                            + edge.getKey().binding());
                }
            }
        }
        for (Demand demand : selected.values()) {
            demand.finalizeProjection(selectedEdgeByEndpoint);
        }

        boolean exactDirectPresentation = false;
        for (JsonElement item : selectedTarget.goal.symbolize()) {
            if (!item.isJsonObject()) continue;
            JsonObject action = item.getAsJsonObject();
            if (!causalAction(action)
                    || !"PROTOCOL_INPUT".equals(
                    string(action, "sourceKind"))) {
                continue;
            }
            String input = string(action, "symbol");
            if (input.isEmpty()) continue;
            Endpoint endpoint = new Endpoint(
                    selectedTarget.occurrenceId,
                    selectedTarget.exactInput(input));
            JsonObject edge = selectedEdgeByEndpoint.get(endpoint);
            if (edge != null && AutomaticRegionEdge
                    .trustedRuntimeCompositionBinding(edge)) {
                exactDirectPresentation = true;
                break;
            }
        }

        List<Demand> result = new ArrayList<>(selected.values());
        result.sort(Comparator.comparing(Demand::sortKey));
        Set<String> campaignIds = new LinkedHashSet<>();
        for (Demand demand : result) {
            if (!campaignIds.add(demand.campaignId)) {
                throw new IOException("duplicate producer campaignId: "
                        + demand.campaignId);
            }
        }
        Set<String> exactBindings = new LinkedHashSet<>();
        Set<String> causalRegions = new LinkedHashSet<>();
        causalRegions.add(selectedTarget.regionId);
        for (Demand demand : result) {
            causalRegions.add(demand.regionId);
            demand.addExactBindings(exactBindings);
        }
        boolean propagatedBoundedStateTransition =
                directInterOccurrenceStatePresentation(fatalInputs,
                        selectedEdgeByEndpoint, result,
                        selectedTarget.occurrenceId);
        int stateBackedFatalInputs = stateBackedFatalInputs(fatalInputs,
                selectedEdgeByEndpoint, result,
                selectedTarget.occurrenceId);
        Set<String> observedSemanticGuards = new LinkedHashSet<>();
        for (Demand demand : result) {
            demand.addObservedSelectedSemanticGuards(
                    observedSemanticGuards);
        }
        int residualFatalInputs = 0;
        for (Endpoint input : fatalInputs) {
            if (!discharged.contains(input)) residualFatalInputs++;
        }
        return new DemandClosure(result, exactBindings, causalRegions,
                fatalInputs.size(), residualFatalInputs,
                exactDirectPresentation, propagatedBoundedStateTransition,
                stateBackedFatalInputs, observedSemanticGuards.size());
    }

    /**
     * Counts fatal operands whose selected exact producer ancestry contains
     * a complete bounded state transition before reaching the target.  This
     * keeps state evidence attached to the operand it actually explains: one
     * stateful side of a predicate must not make every other side look fully
     * backed merely because both occur in the same closure.
     */
    private static int stateBackedFatalInputs(
            Set<Endpoint> fatalInputs,
            Map<Endpoint, JsonObject> selectedEdgeByEndpoint,
            List<Demand> demands, String fatalTargetInstance)
            throws IOException {
        Map<String, Demand> demandByEdgeId = new LinkedHashMap<>();
        for (Demand demand : demands) {
            for (JsonObject edge : demand.selectedEdges.values()) {
                String edgeId = required(edge, "edgeId");
                Demand prior = demandByEdgeId.putIfAbsent(edgeId, demand);
                if (prior != null && prior != demand) {
                    throw new IOException("selected exact edge belongs to "
                            + "more than one producer: " + edgeId);
                }
            }
        }
        int backed = 0;
        for (Endpoint fatalInput : fatalInputs) {
            if (reachesBoundedStateTransition(fatalInput,
                    selectedEdgeByEndpoint, demandByEdgeId,
                    fatalTargetInstance, new LinkedHashSet<>())) {
                backed++;
            }
        }
        return backed;
    }

    /**
     * True when the producer that directly presents a fatal target input
     * consumes an exact heap value written by an earlier occurrence of that
     * same logical producer.  This is the cache create-to-reuse lineage the
     * target actually observes; unrelated state elsewhere in the closure is
     * not a target-selection signal.
     */
    private static boolean directInterOccurrenceStatePresentation(
            Set<Endpoint> fatalInputs,
            Map<Endpoint, JsonObject> selectedEdgeByEndpoint,
            List<Demand> demands, String fatalTargetInstance)
            throws IOException {
        Map<String, Demand> demandByEdgeId = new LinkedHashMap<>();
        for (Demand demand : demands) {
            for (JsonObject edge : demand.selectedEdges.values()) {
                demandByEdgeId.put(required(edge, "edgeId"), demand);
            }
        }
        for (Endpoint fatalInput : fatalInputs) {
            JsonObject targetEdge = selectedEdgeByEndpoint.get(fatalInput);
            if (targetEdge == null || !fatalTargetInstance.equals(
                    required(targetEdge, "toOccurrenceId"))) {
                continue;
            }
            Demand presentation = demandByEdgeId.get(
                    required(targetEdge, "edgeId"));
            if (presentation == null) continue;
            String presentationInstance = required(targetEdge,
                    "fromOccurrenceId");
            Occurrence presented = presentation.requireOccurrence(
                    presentationInstance);
            OutputClosureContract.Member presentedMember =
                    presentation.member(targetEdge, presented);
            for (JsonElement input : array(presentedMember.slice(),
                    "inputPorts")) {
                Endpoint endpoint = new Endpoint(presentationInstance,
                        presented.exactInput(input.getAsString()));
                if (!presentation.requiredInputEndpoints.contains(endpoint)) {
                    continue;
                }
                JsonObject stateEdge = selectedEdgeByEndpoint.get(endpoint);
                if (stateEdge == null) continue;
                Demand state = demandByEdgeId.get(required(stateEdge,
                        "edgeId"));
                if (state == null) continue;
                Occurrence producer = state.requireOccurrence(
                        required(stateEdge, "fromOccurrenceId"));
                OutputClosureContract.Member member = state.member(
                        stateEdge, producer);
                if (state.exactInterOccurrenceHeapStateHandoff(stateEdge,
                        member, member.slice(), producer,
                        new SelectedProducerOccurrence(
                                presentation.relationKey,
                                presented.occurrenceId))) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean reachesBoundedStateTransition(
            Endpoint downstream,
            Map<Endpoint, JsonObject> selectedEdgeByEndpoint,
            Map<String, Demand> demandByEdgeId,
            String fatalTargetInstance, Set<Endpoint> visiting)
            throws IOException {
        if (!visiting.add(downstream)) return false;
        JsonObject edge = selectedEdgeByEndpoint.get(downstream);
        if (edge == null) return false;
        Demand demand = demandByEdgeId.get(required(edge, "edgeId"));
        if (demand == null) {
            throw new IOException("selected exact edge has no producer "
                    + "demand: " + required(edge, "edgeId"));
        }
        String sourceInstance = required(edge, "fromOccurrenceId");
        Occurrence occurrence = demand.requireOccurrence(sourceInstance);
        OutputClosureContract.Member member = demand.member(edge,
                occurrence);
        JsonObject slice = member.slice();
        String consumerInstance = required(edge, "toOccurrenceId");
        boolean stateTransition = boundedStateTransition(slice);
        if (!stateTransition
                && demand.containsOccurrence(consumerInstance)) {
            Occurrence consumer = demand.requireOccurrence(
                    consumerInstance);
            stateTransition = demand.exactInterOccurrenceHeapStateHandoff(
                    edge, member, slice, occurrence,
                    new SelectedProducerOccurrence(demand.relationKey,
                            consumer.occurrenceId));
        }
        if (!fatalTargetInstance.equals(consumerInstance)
                && stateTransition) {
            return true;
        }
        for (JsonElement input : slice.getAsJsonArray("inputPorts")) {
            Endpoint upstream = new Endpoint(sourceInstance,
                    occurrence.exactInput(input.getAsString()));
            if (demand.requiredInputEndpoints.contains(upstream)
                    && reachesBoundedStateTransition(upstream,
                    selectedEdgeByEndpoint, demandByEdgeId,
                    fatalTargetInstance, visiting)) {
                return true;
            }
        }
        return false;
    }

    private static boolean boundedStateTransition(JsonObject slice) {
        return "DEFINITION_INVOCATION_NORMAL_EXIT".equals(
                string(slice, "outputBoundaryKind"))
                && "EARLIEST_READ_IN_EXACT_DEFINITION_INVOCATION_V1"
                .equals(string(slice, "containerPreStateAuthority"))
                && integer(slice, "foldedMutationCount", 0) > 0;
    }

    static boolean causalAction(JsonObject action) {
        if (action == null) {
            throw new IllegalArgumentException(
                    "causal input action is required");
        }
        String role = DependencyRole.normalize(
                action.get("dependencyRole"));
        if (DependencyRole.VALUE_FRONTIER.equals(role)) {
            return true;
        }
        // A configured RPC response object is a concrete VM carrier, but it
        // is also the exact conduit to the producer that returned it. Follow
        // only this lossless runtime contract; ordinary object owners remain
        // closure terminals and never reopen whole-object dependency search.
        return DependencyRole.CONCRETE_STRUCTURE_CARRIER.equals(role)
                && "PROTOCOL_INPUT".equals(string(action, "sourceKind"))
                && "RESPONSE".equals(firstNonBlank(
                string(action, "protocolDirection"),
                string(action, "direction")))
                && "TRUSTED_CONFIGURED_RPC_MAPPING_V1".equals(
                string(action, "authority"))
                && !string(action, "mappingId").isEmpty();
    }

    /**
     * A concrete carrier does not normally extend the value frontier.  One
     * exact descendant projected across a trusted runtime protocol edge does:
     * the edge proves both the field path and the producer occurrence, while
     * the carrier itself remains concrete.
     */
    private static boolean exactTrustedProjectedProducer(
            Endpoint endpoint,
            Map<Endpoint, List<ProducerCandidate>> producersByDownstream) {
        for (ProducerCandidate candidate
                : producersByDownstream.getOrDefault(endpoint,
                java.util.Collections.emptyList())) {
            for (JsonObject edge : candidate.edgesFor(endpoint)) {
                if (bool(edge, "rpcDescendantProjection", false)
                        && !string(edge, "projectionOfEdgeId").isEmpty()
                        && AutomaticRegionEdge
                        .trustedRuntimeCompositionBinding(edge)) {
                    return true;
                }
                // A reference-valued shared field is also an exact conduit
                // when the runtime edge identifies the object actually read.
                // The finalizer has already rejected historical writes whose
                // stored object differs, so following this carrier does not
                // reopen an unconstrained whole-object dependency search.
                if ("HEAP".equals(string(edge, "transportKind"))
                        && AutomaticRegionEdge.FIELD_ASSIGNMENT_READ_FROM
                        .equals(string(edge, "evidenceKind"))
                        && longInteger(edge, "valueObjectId", 0L) != 0L
                        && AutomaticRegionEdge
                        .trustedRuntimeReadFromBinding(edge)) {
                    return true;
                }
            }
        }
        return false;
    }

    private List<Target> discoverTargets() throws IOException {
        List<Target> matches = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (goal.kind() == ClosureGoalKind.TARGET_REACH_CLOSURE) {
                    matches.add(new Target(plan, goal,
                            new Occurrence(goal)));
                }
            }
        }
        if (matches.isEmpty()) {
            throw new IOException("expected at least one target reach closure; "
                    + "found 0");
        }
        for (Target candidate : matches) {
            try {
                candidate.rank = TargetRank.from(
                        discoverDemandClosure(candidate));
            } catch (IOException invalidClosure) {
                // Listing candidates remains useful when one alternative is
                // malformed.  Such an alternative sorts last and still
                // fails closed if it is explicitly selected for execution.
                candidate.rank = TargetRank.invalid();
            }
        }
        matches.sort(Target::compare);
        return matches;
    }

    private Target selectTarget(String targetInstance, String targetGoal)
            throws IOException {
        boolean selected = !targetInstance.isEmpty() || !targetGoal.isEmpty();
        List<Target> matches = new ArrayList<>();
        for (Target candidate : targets) {
            if ((!targetInstance.isEmpty()
                    && !targetInstance.equals(candidate.occurrenceId))
                    || (!targetGoal.isEmpty()
                    && !targetGoal.equals(candidate.goalId))) {
                continue;
            }
            matches.add(candidate);
        }
        if (!selected && matches.size() > 1) {
            return null;
        }
        if (matches.size() != 1) {
            throw new IOException("target selector must identify exactly one "
                    + "target reach closure; found " + matches.size()
                    + "; targetInstance=" + targetInstance
                    + "; targetGoal=" + targetGoal);
        }
        Target result = matches.get(0);
        if (!result.goal.replayable()) {
            throw new IOException("target goal is not replayable; "
                    + result.context());
        }
        return result;
    }

    private Target requireTarget() throws IOException {
        if (target == null) {
            throw new IOException("multiple target reach closures found ("
                    + targets.size() + "); select one with --target-instance "
                    + "and optionally --target-goal, or use target-bindings");
        }
        return target;
    }

    private static List<JsonObject> trustedEdges(RegionInstancePlan plan,
                                                 Goal goal) {
        List<JsonObject> result = new ArrayList<>();
        OutputClosureContract closure = goal.outputClosure();
        if (closure != null) {
            Set<String> selectedIds = new LinkedHashSet<>();
            for (JsonElement element : goal.edgeBindings()) {
                if (!element.isJsonObject()) continue;
                JsonObject edge = element.getAsJsonObject();
                String fromRegion = string(edge, "fromRegion");
                String fromOccurrence = string(edge,
                        "fromOccurrenceId");
                boolean sameRegion = plan.regionId().equals(fromRegion)
                        && fromOccurrence.equals(plan.occurrenceId());
                if (!sameRegion || string(edge, "fromOutputPort").isEmpty()
                        || !AutomaticRegionEdge
                        .trustedRuntimeCompositionBinding(edge)) {
                    continue;
                }
                String id = string(edge, "edgeId");
                if (selectedIds.add(id)) result.add(edge.deepCopy());
            }
            return result;
        }

        // A non-READY producer has no output-closure contract yet.  Its
        // binding ledger may still be used to fail closed when it is on the
        // exact frontier, but only edges emitted by this goal's execution
        // occurrence are producer candidates.  Incoming bindings describe
        // the relation's dependencies; indexing them as outputs makes the
        // relation appear to produce its own inputs.
        String producer = goal.plan().occurrenceId();
        for (JsonElement item : goal.edgeBindings()) {
            if (item.isJsonObject()) {
                JsonObject edge = item.getAsJsonObject();
                if (producer.equals(string(edge, "fromOccurrenceId"))
                        && AutomaticRegionEdge
                        .trustedRuntimeCompositionBinding(edge)) {
                    result.add(edge.deepCopy());
                }
            }
        }
        return result;
    }

    private static void requireReady(Demand demand) throws IOException {
        if (!"READY".equals(demand.goal.admissionState())) {
            throw new IOException("producer goal on target dependency path "
                    + "is not READY; " + demand.context());
        }
        if (demand.goal.outputClosure() == null) {
            throw new IOException("READY producer goal has no outputClosure; "
                    + demand.context());
        }
    }

    private List<String> outputGoalAdmissions() {
        List<String> result = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (goal.kind().capturesOutputRelation()) {
                    result.add(context(plan, goal));
                }
            }
        }
        return result;
    }

    private String scheduledProducerTask(String campaignId, Path taskPlan)
            throws IOException {
        Demand demand = demand(campaignId);
        return scheduledProducerTask(demand, readTasks(taskPlan)).taskId();
    }

    private static ExecutionTask scheduledProducerTask(
            Demand demand, List<ExecutionTask> tasks) throws IOException {
        Occurrence exactProducer = demand.exactProducerOccurrence();
        List<ExecutionTask> matches = new ArrayList<>();
        for (ExecutionTask task : tasks) {
            if (sameTaskIdentity(demand.plan, exactProducer, task)
                    && demand.goalId.equals(task.goalId())
                    && task.goalKind().capturesOutputRelation()
                    && task.outputClosure() != null
                    && task.executable()) {
                matches.add(task);
            }
        }
        ExecutionTask task = onlyTask(matches,
                "scheduled producer task; " + demand.context());
        requireSelectedProducerOccurrence(demand, task);
        return task;
    }

    private static ExecutionTask scheduledProducerTask(
            ProducerGroup group, List<ExecutionTask> tasks)
            throws IOException {
        List<ExecutionTask> matches = new ArrayList<>();
        Set<String> outputs = group.outputPorts();
        Set<String> edges = group.edgeIds();
        for (ExecutionTask task : tasks) {
            if (group.regionId.equals(task.regionId())
                    && group.sourceKey.equals(task.sourceKey())
                    && group.relationKey.equals(task.relationKey())
                    && group.relationContractHash.equals(
                    task.relationContractHash())
                    && group.occurrenceId.equals(task.occurrenceId())
                    && group.goalId().equals(task.goalId())
                    && task.goalKind().capturesOutputRelation()
                    && task.outputClosure() != null
                    && task.executable()) {
                matches.add(task);
            }
        }
        ExecutionTask task = onlyTask(matches,
                "scheduled atomic producer task; instance="
                        + group.occurrenceId + "; pathSeed="
                        + group.pathSeedKey);
        Set<String> actualOutputs = new LinkedHashSet<>();
        for (OutputClosureContract.Member member
                : task.outputClosure().members()) {
            actualOutputs.add(member.portId());
        }
        if (!actualOutputs.equals(outputs)
                || !task.outputClosure().executionScope().inputPorts()
                .equals(group.inputPorts())) {
            throw new IOException("scheduled atomic producer task closure "
                    + "does not exactly cover grouped ports; instance="
                    + group.occurrenceId);
        }
        for (Demand demand : group.demands) {
            requireSelectedProducerOccurrence(demand, task);
        }
        if (!taskEdgeIds(task).containsAll(edges)) {
            throw new IOException("scheduled atomic producer task omits "
                    + "selected state-flow edges; occurrence="
                    + group.occurrenceId);
        }
        return task;
    }

    private static Set<String> taskEdgeIds(ExecutionTask task)
            throws IOException {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : task.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            String edgeId = required(element.getAsJsonObject(), "edgeId");
            if (!result.add(edgeId)) {
                throw new IOException("execution task repeats state-flow edge "
                        + edgeId);
            }
        }
        return result;
    }

    private static boolean sameTaskIdentity(RegionInstancePlan plan,
                                            Occurrence occurrence,
                                            ExecutionTask task) {
        return plan.regionId().equals(task.regionId())
                && plan.sourceKey().equals(task.sourceKey())
                && plan.relationKey().equals(task.relationKey())
                && plan.relationContractHash().equals(
                task.relationContractHash())
                && occurrence.occurrenceId.equals(task.occurrenceId());
    }

    private static void requireSelectedProducerOccurrence(
            Demand demand, ExecutionTask task) throws IOException {
        Occurrence expected = demand.exactProducerOccurrence();
        if (!sameTaskIdentity(demand.plan, expected, task)) {
            throw new IOException("scheduled producer task occurrence does "
                    + "not match selected runtime evidence: "
                    + expected.occurrenceId);
        }

        Set<String> projectedInputs = demand.projectedInputPorts();
        if (!task.outputClosure().executionScope().inputPorts()
                .containsAll(projectedInputs)) {
            throw new IOException("scheduled producer task closure omits "
                    + "selected inputs: " + expected.occurrenceId);
        }
        Set<String> projectedOutputs = demand.projection().outputPorts();
        Set<String> projectedBindings = demand.projection().edgeIds();
        Set<String> actualOutputs = new LinkedHashSet<>();
        for (OutputClosureContract.Member member
                : task.outputClosure().members()) {
            actualOutputs.add(member.portId());
        }
        if (!actualOutputs.containsAll(projectedOutputs)
                || !taskEdgeIds(task).containsAll(projectedBindings)) {
            throw new IOException("scheduled producer task omits selected "
                    + "outputs or state-flow edges: "
                    + expected.occurrenceId);
        }
    }

    private String scheduledTargetTask(Path taskPlan) throws IOException {
        return scheduledTargetTask(requireTarget(), readTasks(taskPlan))
                .taskId();
    }

    private static ExecutionTask scheduledTargetTask(
            Target selectedTarget, List<ExecutionTask> tasks)
            throws IOException {
        List<ExecutionTask> matches = new ArrayList<>();
        for (ExecutionTask task : tasks) {
            if (selectedTarget.regionId.equals(task.regionId())
                    && selectedTarget.relationKey.equals(task.relationKey())
                    && selectedTarget.goalId.equals(task.goalId())
                    && task.goalKind().capturesTargetReach()
                    && task.executable()) {
                matches.add(task);
            }
        }
        ExecutionTask task = onlyTask(matches, "scheduled target task; "
                + selectedTarget.context());
        requireSelectedTargetOccurrence(selectedTarget, task);
        return task;
    }

    private static void requireSelectedTargetOccurrence(
            Target selectedTarget, ExecutionTask task) throws IOException {
        if (!sameTaskIdentity(selectedTarget.plan,
                selectedTarget.occurrence, task)) {
            throw new IOException("scheduled target task occurrence does "
                    + "not match selected runtime evidence: "
                    + selectedTarget.occurrenceId);
        }

        Set<String> canonicalInputs = new LinkedHashSet<>();
        for (JsonElement element : task.inputActions().all()) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            String port = firstNonBlank(string(action, "portId"),
                    string(action, "symbol"));
            if (!port.isEmpty()) canonicalInputs.add(port);
        }
        Set<String> touchingBindings = new LinkedHashSet<>();
        for (JsonElement element : task.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!selectedTarget.occurrenceId.equals(string(binding,
                    "fromOccurrenceId"))
                    && !selectedTarget.occurrenceId.equals(
                    string(binding, "toOccurrenceId"))) {
                continue;
            }
            String edgeId = string(binding, "edgeId");
            if (edgeId.isEmpty()) {
                throw new IOException("scheduled target occurrence binding "
                        + "has no edgeId: "
                        + selectedTarget.occurrenceId);
            }
            touchingBindings.add(edgeId);
        }
        if (!selectedTarget.occurrence.bindingIds.containsAll(
                touchingBindings)) {
            throw new IOException("scheduled target occurrence binding "
                    + "ledger is incomplete: "
                    + selectedTarget.occurrenceId);
        }
    }

    private static List<ExecutionTask> readTasks(Path taskPlan)
            throws IOException {
        List<ExecutionTask> result = new ArrayList<>();
        for (JsonObject row : ArtifactIO.readJsonl(taskPlan)) {
            result.add(ExecutionTask.decode(row));
        }
        return result;
    }

    private Demand demand(String campaignId) throws IOException {
        for (Demand demand : discoverDemands()) {
            if (demand.campaignId.equals(campaignId)) {
                return demand;
            }
        }
        throw new IOException("unknown producer campaign: " + campaignId);
    }

    private void printDiscovery() throws IOException {
        System.out.println("role\tcampaign\tregion\tinstance\tgoal");
        for (Demand demand : discoverDemands()) {
            System.out.println("PRODUCER\t" + demand.binding());
        }
        System.out.println("TARGET\t" + requireTarget().binding());
    }

    private static String campaignId(String regionId,
                                     String occurrenceId,
                                     String goalId) {
        String region = safeToken(regionId);
        Matcher call = CALL_ID.matcher(occurrenceId);
        String invocation = call.find()
                ? "call" + call.group(1)
                : "instance-"
                + ArtifactIO.sha256(occurrenceId).substring(0, 8);
        Matcher goalDigest = GOAL_DIGEST.matcher(goalId);
        String digest = goalDigest.find()
                ? goalDigest.group(1).substring(0, 8).toLowerCase()
                : ArtifactIO.sha256(goalId).substring(0, 8);
        return region + "-" + invocation + "-" + digest;
    }

    private static String safeToken(String value) {
        String token = value == null ? "" : value.trim()
                .replaceAll("[^A-Za-z0-9._-]+", "-")
                .replaceAll("^-+|-+$", "");
        return token.isEmpty() ? "region" : token;
    }

    private static String context(RegionInstancePlan plan, Goal goal) {
        return "region=" + plan.regionId()
                + "; instance=" + plan.occurrenceId()
                + "; goal=" + goal.goalId()
                + "; admission=" + goal.admissionState()
                + "; blockers=" + goal.admissionBlockers();
    }

    private static ExecutionTask onlyTask(List<ExecutionTask> values,
                                          String subject)
            throws IOException {
        if (values.size() != 1) {
            throw new IOException("expected one " + subject + "; found "
                    + values.size());
        }
        return values.get(0);
    }

    private static String required(JsonObject object, String field)
            throws IOException {
        String value = string(object, field);
        if (value.isEmpty()) {
            throw new IOException("trusted runtime edge is missing " + field);
        }
        return value;
    }

    private static String required(Map<String, String> args, String name) {
        String value = args.get(name);
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException("--" + name
                    + " is required");
        }
        return value.trim();
    }

    private static String optional(Map<String, String> args, String name) {
        String value = args.get(name);
        return value == null ? "" : value.trim();
    }

    private static Map<String, String> parseArgs(String[] argv) {
        Map<String, String> result = new LinkedHashMap<>();
        for (int index = 0; index < argv.length; index += 2) {
            if (!argv[index].startsWith("--") || index + 1 >= argv.length) {
                throw new IllegalArgumentException(
                        "arguments must be --name value pairs");
            }
            result.put(argv[index].substring(2), argv[index + 1]);
        }
        return result;
    }

    private static final class Demand {
        private final RegionInstancePlan plan;
        private final Goal goal;
        private final String campaignId;
        private final String regionId;
        private final String relationKey;
        private final String occurrenceId;
        private final String goalId;
        private final Occurrence occurrence;
        private final Map<Endpoint, JsonObject> selectedEdges =
                new LinkedHashMap<>();
        private final Set<Endpoint> requiredInputEndpoints =
                new LinkedHashSet<>();
        private ProducerOutputProjection projection;

        private Demand(RegionInstancePlan plan, Goal goal) {
            this.plan = plan;
            this.goal = goal;
            regionId = plan.regionId();
            relationKey = plan.relationKey();
            occurrenceId = goal.plan().occurrenceId();
            goalId = goal.goalId();
            campaignId = campaignId(regionId, occurrenceId, goalId);
            occurrence = new Occurrence(goal);
        }

        private void addRequiredInputs(Set<Endpoint> endpoints,
                                       ProducerCandidate candidate,
                                       Set<Endpoint> frontier,
                                       Map<Endpoint, List<ProducerCandidate>>
                                               producersByDownstream)
                throws IOException {
            if (goal.outputClosure() == null) return;
            for (Endpoint target : endpoints) {
                JsonObject edge = candidate.edgeFor(target, occurrence);
                JsonObject prior = selectedEdges.putIfAbsent(target, edge);
                if (prior != null && !required(prior, "edgeId").equals(
                        required(edge, "edgeId"))) {
                    throw new IOException("exact downstream input selected "
                            + "more than one output: " + target.binding());
                }
                String sourceInstance = required(edge,
                        "fromOccurrenceId");
                Occurrence selected = requireOccurrence(sourceInstance);
                OutputClosureContract.Member member = member(edge,
                        selected);
                for (JsonElement input : member.slice()
                        .getAsJsonArray("inputPorts")) {
                    String port = input.getAsString();
                    Endpoint endpoint = new Endpoint(sourceInstance,
                            selected.exactInput(port));
                    if (causalPort(goal, port)
                            || exactTrustedProjectedProducer(endpoint,
                            producersByDownstream)) {
                        requiredInputEndpoints.add(endpoint);
                        frontier.add(endpoint);
                    }
                }
            }
        }

        private void finalizeProjection(
                Map<Endpoint, JsonObject> selectedEdgeByEndpoint)
                throws IOException {
            Set<String> outputs = new LinkedHashSet<>();
            Set<String> edgeIds = new LinkedHashSet<>();
            for (JsonObject edge : selectedEdges.values()) {
                Occurrence occurrence = requireOccurrence(
                        required(edge, "fromOccurrenceId"));
                outputs.add(member(edge, occurrence).portId());
                edgeIds.add(required(edge, "edgeId"));
            }
            for (Endpoint input : requiredInputEndpoints) {
                JsonObject edge = selectedEdgeByEndpoint.get(input);
                if (edge != null) edgeIds.add(required(edge, "edgeId"));
            }
            projection = ProducerOutputProjection.create(campaignId,
                    regionId, relationKey, goalId,
                    firstNonBlank(goal.pathSeedKey(), goalId), outputs,
                    edgeIds);
        }

        private ProducerOutputProjection projection() throws IOException {
            if (projection == null) {
                throw new IOException("producer demand has no finalized "
                        + "exact-output projection; " + context());
            }
            return projection;
        }

        private OutputClosureContract.Member member(JsonObject edge,
                                                     Occurrence occurrence)
                throws IOException {
            String sourceInstance = required(edge, "fromOccurrenceId");
            String exactOutput = required(edge, "fromOutputPort");
            String output = occurrence.canonicalOutput(exactOutput);
            OutputClosureContract.Member member =
                    goal.outputClosure().member(output);
            if (member == null) {
                throw new IOException("exact producer output has no "
                        + "canonical closure member: "
                        + sourceInstance + ":" + exactOutput);
            }
            return member;
        }

        private Set<String> demandedCanonicalOutputs(
                Set<Endpoint> endpoints, ProducerCandidate candidate)
                throws IOException {
            Set<String> result = new LinkedHashSet<>();
            for (Endpoint endpoint : endpoints) {
                JsonObject edge = candidate.edgeFor(endpoint, occurrence);
                Occurrence selected = requireOccurrence(
                        required(edge, "fromOccurrenceId"));
                result.add(member(edge, selected).portId());
            }
            return result;
        }

        private Set<String> demandedInputs(Set<Endpoint> endpoints,
                                           ProducerCandidate candidate)
                throws IOException {
            Set<String> result = new LinkedHashSet<>();
            for (Endpoint endpoint : endpoints) {
                JsonObject edge = candidate.edgeFor(endpoint, occurrence);
                Occurrence selected = requireOccurrence(
                        required(edge, "fromOccurrenceId"));
                for (JsonElement input : member(edge, selected).slice()
                        .getAsJsonArray("inputPorts")) {
                    result.add(input.getAsString());
                }
            }
            return result;
        }

        private Set<String> projectedInputPorts() throws IOException {
            Set<String> result = new LinkedHashSet<>();
            for (JsonObject edge : selectedEdges.values()) {
                Occurrence occurrence = requireOccurrence(
                        required(edge, "fromOccurrenceId"));
                for (JsonElement input : member(edge, occurrence).slice()
                        .getAsJsonArray("inputPorts")) {
                    result.add(input.getAsString());
                }
            }
            return result;
        }

        private Occurrence exactProducerOccurrence() throws IOException {
            Set<String> instances = new LinkedHashSet<>();
            for (JsonObject edge : selectedEdges.values()) {
                instances.add(required(edge, "fromOccurrenceId"));
            }
            if (instances.size() != 1) {
                throw new IOException("producer demand must select exactly "
                        + "one exact producer occurrence; found "
                        + instances.size() + "; " + context());
            }
            return requireOccurrence(instances.iterator().next());
        }

        private void addExactBindings(Set<String> bindings)
                throws IOException {
            for (Map.Entry<Endpoint, JsonObject> selected
                    : selectedEdges.entrySet()) {
                Endpoint target = selected.getKey();
                JsonObject edge = selected.getValue();
                bindings.add(required(edge, "fromOccurrenceId") + "\n"
                        + required(edge, "fromOutputPort") + "\n"
                        + target.instance + "\n" + target.input);
            }
        }

        /**
         * Counts only guards exercised by the exact output members selected
         * for this target.  The logical goal can contain the union of several
         * occurrences, so a globally observed branch is not enough: its site
         * must also belong to the selected member slice.
         */
        private void addObservedSelectedSemanticGuards(Set<String> result)
                throws IOException {
            for (JsonObject edge : selectedEdges.values()) {
                Occurrence occurrence = requireOccurrence(
                        required(edge, "fromOccurrenceId"));
                JsonObject slice = member(edge, occurrence).slice();
                Set<String> selectedSites = new LinkedHashSet<>();
                for (String field : new String[]{"sites", "staticSites"}) {
                    for (JsonElement site : array(slice, field)) {
                        if (site.isJsonPrimitive()) {
                            selectedSites.add(site.getAsString().trim());
                        }
                    }
                }
                for (JsonElement element : goal.branches()) {
                    if (!element.isJsonObject()) continue;
                    JsonObject branch = element.getAsJsonObject();
                    String site = string(branch, "siteId");
                    if (!selectedSites.contains(site)
                            || !"EXPLORE".equals(string(branch, "policy"))
                            || !bool(branch, "observed", false)
                            || bool(branch, "failureTarget", false)
                            || bool(branch, "loopControlGuard", false)
                            || bool(branch, "loopControlOnly", false)) {
                        continue;
                    }
                    result.add(relationKey + "\n"
                            + firstNonBlank(goal.pathSeedKey(), goalId)
                            + "\n" + site);
                }
            }
        }

        /**
         * A concrete field write consumed by a later exact occurrence of the
         * same logical producer is also bounded state evolution.  It is not a
         * folded container mutation, so keep this evidence local to the
         * propagated-state rank instead of weakening boundedStateTransition,
         * which also backs individual fatal operands.
         */
        private boolean exactInterOccurrenceHeapStateHandoff(
                JsonObject edge, OutputClosureContract.Member member,
                JsonObject slice, Occurrence producer,
                SelectedProducerOccurrence consumer) {
            return relationKey.equals(consumer.relationKey)
                    && !producer.occurrenceId.equals(consumer.occurrenceId)
                    && "HEAP_STATE".equals(member.outputKind())
                    && "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT".equals(
                    string(slice, "outputBoundaryKind"))
                    && "HEAP".equals(string(edge, "transportKind"))
                    && "FIELD_ASSIGNMENT_READ_FROM_V1".equals(
                    string(edge, "evidenceKind"))
                    && AutomaticRegionEdge
                    .trustedRuntimeReadFromBinding(edge);
        }

        private static boolean causalPort(Goal goal, String port)
                throws IOException {
            JsonObject selected = null;
            for (JsonElement element : goal.symbolize()) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                if (port.equals(string(action, "symbol"))) {
                    if (selected != null) {
                        throw new IOException("output slice input has "
                                + "ambiguous dependency actions: " + port);
                    }
                    selected = action;
                }
            }
            if (selected == null) {
                throw new IOException("output slice input has no declared "
                        + "dependency action: " + port);
            }
            return causalAction(selected);
        }

        private String binding() {
            return campaignId + "\t" + regionId + "\t"
                    + occurrenceId + "\t" + goalId;
        }

        private String context() {
            return RuntimeWorkflowDiscovery.context(plan, goal);
        }

        private String sortKey() {
            return occurrenceId + "\n" + goalId;
        }

        private Occurrence requireOccurrence(String id) throws IOException {
            if (!occurrence.occurrenceId.equals(id)) {
                throw new IOException("relation does not contain occurrence "
                        + id);
            }
            return occurrence;
        }

        private boolean containsOccurrence(String id) {
            return occurrence.occurrenceId.equals(id);
        }

    }

    /**
     * Cheap exact-endpoint probe used before interpreting a logical
     * occurrence catalog.  A malformed producer outside the selected
     * target's backward frontier is diagnostic noise, while a matching one
     * is materialized and therefore still fails closed.
     */
    private static final class ProducerCandidate {
        private final RegionInstancePlan plan;
        private final Goal goal;
        private final Map<Endpoint, List<JsonObject>> edgesByDownstream =
                new LinkedHashMap<>();
        private final Set<Endpoint> downstreamEndpoints =
                new LinkedHashSet<>();

        private ProducerCandidate(RegionInstancePlan plan, Goal goal,
                                  List<JsonObject> edges) {
            this.plan = plan;
            this.goal = goal;
            for (JsonObject edge : edges) {
                String instance = string(edge, "toOccurrenceId");
                String input = string(edge, "toInputPort");
                if (!instance.isEmpty() && !input.isEmpty()) {
                    Endpoint endpoint = new Endpoint(instance, input);
                    downstreamEndpoints.add(endpoint);
                    edgesByDownstream.computeIfAbsent(endpoint,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
            for (List<JsonObject> alternatives
                    : edgesByDownstream.values()) {
                alternatives.sort(ProducerCandidate::compareEdges);
            }
        }

        private boolean ready() {
            return "READY".equals(goal.admissionState());
        }

        private Demand materialize() {
            if (goal.outputClosure() == null) {
                throw new IllegalArgumentException(
                        "READY producer goal has no outputClosure");
            }
            return new Demand(plan, goal);
        }

        private JsonObject edgeFor(Endpoint endpoint,
                                   Occurrence occurrence)
                throws IOException {
            List<JsonObject> edges = edgesByDownstream.get(endpoint);
            if (edges == null || edges.isEmpty()) {
                throw new IOException("producer candidate has no edge for "
                        + endpoint.binding());
            }
            for (JsonObject edge : edges) {
                if (occurrence.occurrenceId.equals(string(edge,
                        "fromOccurrenceId"))) {
                    return edge;
                }
            }
            throw new IOException("producer path seed has no exact "
                    + "occurrence for " + endpoint.binding());
        }

        private boolean covers(Endpoint endpoint,
                               Occurrence occurrence) {
            for (JsonObject edge : edgesByDownstream.getOrDefault(endpoint,
                    java.util.Collections.emptyList())) {
                if (occurrence.occurrenceId.equals(string(edge,
                        "fromOccurrenceId"))) {
                    return true;
                }
            }
            return false;
        }

        private List<JsonObject> edgesFor(Endpoint endpoint) {
            return edgesByDownstream.getOrDefault(endpoint,
                    java.util.Collections.emptyList());
        }

        private String semanticKey() {
            OutputClosureContract closure = goal.outputClosure();
            return plan.regionId() + "\n" + plan.relationKey() + "\n"
                    + firstNonBlank(goal.pathSeedKey(), goal.goalId()) + "\n"
                    + (closure == null ? "" : closure.demandKey()) + "\n"
                    + goal.goalId();
        }

        private static String edgeSortKey(JsonObject edge) {
            return string(edge, "fromOutputPort") + "\n"
                    + string(edge, "edgeId") + "\n"
                    + string(edge, "fromOccurrenceId");
        }

        private static int compareEdges(JsonObject left, JsonObject right) {
            int observedOrder = Long.compare(
                    longInteger(right, "writerEventSeq", -1L),
                    longInteger(left, "writerEventSeq", -1L));
            return observedOrder != 0 ? observedOrder
                    : edgeSortKey(left).compareTo(edgeSortKey(right));
        }
    }

    /** Deterministic greedy choice among alternative producer relations. */
    private static final class ProducerChoice {
        private static final Comparator<ProducerChoice> ORDER =
                Comparator.comparingInt(
                        (ProducerChoice value) -> value.coveredEndpoints.size())
                        .reversed()
                        .thenComparing(value -> !value.alreadySelected)
                        .thenComparingInt(value -> value.unrelatedEndpoints)
                        .thenComparingInt(value -> value.unrelatedOutputs)
                        .thenComparingInt(value -> value.unrelatedInputs)
                        .thenComparingInt(value -> value.demandedInputs)
                        .thenComparing(value -> value.candidate.semanticKey());

        private final ProducerCandidate candidate;
        private final Demand demand;
        private final Set<Endpoint> coveredEndpoints = new LinkedHashSet<>();
        private final boolean alreadySelected;
        private final int unrelatedEndpoints;
        private final int unrelatedOutputs;
        private final int unrelatedInputs;
        private final int demandedInputs;

        private ProducerChoice(ProducerCandidate candidate, Demand demand,
                               Set<Endpoint> unresolved,
                               boolean alreadySelected) throws IOException {
            this.candidate = candidate;
            this.demand = demand;
            this.alreadySelected = alreadySelected;
            for (Endpoint endpoint : candidate.downstreamEndpoints) {
                if (unresolved.contains(endpoint)
                        && candidate.covers(endpoint,
                        demand.occurrence)) {
                    coveredEndpoints.add(endpoint);
                }
            }
            Set<String> selectedOutputs = demand.demandedCanonicalOutputs(
                    coveredEndpoints, candidate);
            Set<String> selectedInputs = demand.demandedInputs(
                    coveredEndpoints, candidate);
            OutputClosureContract closure = demand.goal.outputClosure();
            unrelatedEndpoints = candidate.downstreamEndpoints.size()
                    - coveredEndpoints.size();
            unrelatedOutputs = closure.members().size()
                    - selectedOutputs.size();
            demandedInputs = selectedInputs.size();
            unrelatedInputs = closure.executionScope().inputPorts().size()
                    - demandedInputs;
        }
    }

    private static final class DemandClosure {
        private final List<Demand> demands;
        private final Set<String> exactBindings;
        private final Set<String> causalRegions;
        private final int fatalInputs;
        private final int residualFatalInputs;
        private final boolean exactDirectPresentation;
        private final boolean propagatedBoundedStateTransition;
        private final int stateBackedFatalInputs;
        private final int observedSelectedSemanticGuards;

        private DemandClosure(List<Demand> demands,
                              Set<String> exactBindings,
                              Set<String> causalRegions, int fatalInputs,
                              int residualFatalInputs,
                              boolean exactDirectPresentation,
                              boolean propagatedBoundedStateTransition,
                              int stateBackedFatalInputs,
                              int observedSelectedSemanticGuards) {
            this.demands = demands;
            this.exactBindings = exactBindings;
            this.causalRegions = causalRegions;
            this.fatalInputs = fatalInputs;
            this.residualFatalInputs = residualFatalInputs;
            this.exactDirectPresentation = exactDirectPresentation;
            this.propagatedBoundedStateTransition =
                    propagatedBoundedStateTransition;
            this.stateBackedFatalInputs = stateBackedFatalInputs;
            this.observedSelectedSemanticGuards =
                    observedSelectedSemanticGuards;
        }
    }

    /** One deterministic target-first closure over a decoded runtime plan. */
    static final class RankedWorkflow {
        private final Target target;
        private final List<Demand> producers;
        private final List<Selection> selections;
        private final List<ProducerGroup> producerGroups;

        private RankedWorkflow(Target target, List<Demand> producers)
                throws IOException {
            this.target = target;
            this.producers = new ArrayList<>(producers);
            List<Selection> materialized = new ArrayList<>();
            Map<String, ProducerGroup> grouped = new LinkedHashMap<>();
            Set<String> targetEdgeIds = new LinkedHashSet<>();
            for (Demand producer : producers) {
                Selection selection = Selection.producer(producer);
                materialized.add(selection);
                for (JsonObject edge : producer.selectedEdges.values()) {
                    if (target.occurrenceId.equals(string(edge,
                            "toOccurrenceId"))) {
                        targetEdgeIds.add(required(edge, "edgeId"));
                    }
                }
                String key = ProducerGroup.key(producer);
                ProducerGroup group = grouped.get(key);
                if (group == null) {
                    group = new ProducerGroup(producer);
                    grouped.put(key, group);
                }
                group.add(producer, selection);
            }
            materialized.add(0, Selection.target(target, targetEdgeIds));
            selections = java.util.Collections.unmodifiableList(materialized);
            producerGroups = java.util.Collections.unmodifiableList(
                    new ArrayList<>(grouped.values()));
        }

        List<Selection> selections() {
            return selections;
        }

        List<ProducerGroup> producerGroups() {
            return producerGroups;
        }

        int scheduledTaskCount() {
            return 1 + producerGroups.size();
        }

        /**
         * Deep-validates the scheduled tasks against discovery and emits the
         * compact index consumed by later candidate stages.
         */
        JsonObject scheduleIndex(List<JsonObject> encodedTasks,
                                 JsonObject regionPlanIdentity,
                                 JsonObject taskPlanIdentity)
                throws IOException {
            List<ExecutionTask> tasks = new ArrayList<>();
            for (JsonObject encoded : encodedTasks) {
                tasks.add(ExecutionTask.decode(encoded));
            }
            if (tasks.size() != scheduledTaskCount()) {
                throw new IOException("target-first schedule emitted "
                        + tasks.size() + " tasks for "
                        + scheduledTaskCount() + " atomic selections");
            }
            Set<String> selectedTaskIds = new LinkedHashSet<>();
            ExecutionTask targetTask = scheduledTargetTask(target, tasks);
            selectedTaskIds.add(targetTask.taskId());

            JsonObject index = new JsonObject();
            index.addProperty("schemaVersion", 1);
            index.addProperty("kind",
                    "RUNTIME_TARGET_FIRST_SCHEDULE_INDEX");
            index.addProperty("selectionAuthority",
                    "RANKED_EXACT_RUNTIME_READ_FROM_CLOSURE_V1");
            if (regionPlanIdentity == null || taskPlanIdentity == null) {
                throw new IOException("target-first schedule index requires "
                        + "committed artifact identities");
            }
            index.add("regionPlan", regionPlanIdentity.deepCopy());
            index.add("executionTaskPlan", taskPlanIdentity.deepCopy());
            index.add("target", target.indexEntry(targetTask.taskId()));

            com.google.gson.JsonArray encodedProducers =
                    new com.google.gson.JsonArray();
            for (ProducerGroup group : producerGroups) {
                ExecutionTask task = scheduledProducerTask(group, tasks);
                if (!selectedTaskIds.add(task.taskId())) {
                    throw new IOException("target-first schedule maps more "
                            + "than one producer group to task "
                            + task.taskId());
                }
                encodedProducers.add(group.indexEntry(task.taskId()));
            }
            if (selectedTaskIds.size() != tasks.size()) {
                throw new IOException("target-first schedule contains an "
                        + "unselected execution task");
            }
            index.add("producers", encodedProducers);
            return index;
        }

    }

    /** Producer demands that must execute in one exact invocation/path. */
    static final class ProducerGroup {
        final String regionId;
        final String sourceKey;
        final String relationKey;
        final String relationContractHash;
        final String occurrenceId;
        final String pathSeedKey;
        final List<Demand> demands = new ArrayList<>();
        final List<Selection> selections = new ArrayList<>();

        private ProducerGroup(Demand first) throws IOException {
            Occurrence exact = first.exactProducerOccurrence();
            regionId = first.regionId;
            sourceKey = first.plan.sourceKey();
            relationKey = first.plan.relationKey();
            relationContractHash = first.plan.relationContractHash();
            occurrenceId = exact.occurrenceId;
            pathSeedKey = firstNonBlank(first.goal.pathSeedKey(),
                    first.goalId);
        }

        private void add(Demand demand, Selection selection)
                throws IOException {
            Occurrence exact = demand.exactProducerOccurrence();
            if (!regionId.equals(demand.regionId)
                    || !sourceKey.equals(demand.plan.sourceKey())
                    || !relationKey.equals(demand.plan.relationKey())
                    || !relationContractHash.equals(
                    demand.plan.relationContractHash())
                    || !occurrenceId.equals(exact.occurrenceId)
                    || !pathSeedKey.equals(firstNonBlank(
                    demand.goal.pathSeedKey(), demand.goalId))) {
                throw new IOException("producer group crosses exact "
                        + "invocation or path boundary");
            }
            demands.add(demand);
            selections.add(selection);
        }

        private static String key(Demand demand) throws IOException {
            Occurrence exact = demand.exactProducerOccurrence();
            return demand.regionId + "\n" + demand.plan.sourceKey() + "\n"
                    + demand.plan.relationKey() + "\n"
                    + exact.occurrenceId + "\n" + firstNonBlank(
                    demand.goal.pathSeedKey(), demand.goalId);
        }

        Set<String> outputPorts() throws IOException {
            Set<String> result = new LinkedHashSet<>();
            for (Demand demand : demands) {
                result.addAll(demand.projection().outputPorts());
            }
            return result;
        }

        Set<String> edgeIds() throws IOException {
            Set<String> result = new LinkedHashSet<>();
            for (Demand demand : demands) {
                result.addAll(demand.projection().edgeIds());
            }
            return result;
        }

        Set<String> inputPorts() throws IOException {
            Set<String> result = new LinkedHashSet<>();
            for (Demand demand : demands) {
                result.addAll(demand.projectedInputPorts());
            }
            return result;
        }

        private String atomicDigest() throws IOException {
            if (demands.size() == 1) return "";
            java.util.TreeSet<String> members = new java.util.TreeSet<>();
            for (Demand demand : demands) {
                members.add(demand.goalId + "\n"
                        + CanonicalJson.render(demand.projection().json()));
            }
            return ArtifactIO.sha256("ATOMIC_PRODUCER_GROUP_V1\n"
                    + key(demands.get(0)) + "\n"
                    + String.join("\n--MEMBER--\n", members));
        }

        String campaignId() throws IOException {
            return demands.size() == 1 ? demands.get(0).campaignId
                    : regionId + "-atomic-" + atomicDigest();
        }

        String goalId() throws IOException {
            return demands.size() == 1 ? demands.get(0).goalId
                    : "GOAL.OUTPUT_RELATION.ATOMIC." + atomicDigest();
        }

        ProducerOutputProjection projection() throws IOException {
            if (demands.size() == 1) return demands.get(0).projection();
            return ProducerOutputProjection.create(campaignId(), regionId,
                    relationKey, goalId(), pathSeedKey, outputPorts(),
                    edgeIds());
        }

        JsonObject indexEntry(String taskId) throws IOException {
            JsonObject result = new JsonObject();
            result.addProperty("campaignId", campaignId());
            result.addProperty("regionId", regionId);
            result.addProperty("relationKey", relationKey);
            result.addProperty("occurrenceId", occurrenceId);
            result.addProperty("goalId", goalId());
            result.addProperty("taskId", taskId);
            return result;
        }
    }

    /** A scheduler filter plus the exact producer projection, if any. */
    static final class Selection {
        final String campaignId;
        final String regionId;
        final String occurrenceId;
        final String goalId;
        final ProducerOutputProjection producerProjection;
        final Set<String> targetEdgeIds;

        private Selection(String campaignId, String regionId,
                          String occurrenceId, String goalId,
                          ProducerOutputProjection producerProjection,
                          Set<String> targetEdgeIds) {
            this.campaignId = campaignId;
            this.regionId = regionId;
            this.occurrenceId = occurrenceId;
            this.goalId = goalId;
            this.producerProjection = producerProjection;
            this.targetEdgeIds = java.util.Collections.unmodifiableSet(
                    new LinkedHashSet<>(targetEdgeIds));
        }

        private static Selection target(Target target,
                                        Set<String> targetEdgeIds) {
            return new Selection(target.campaignId, target.regionId,
                    target.occurrenceId, target.goalId, null,
                    targetEdgeIds);
        }

        private static Selection producer(Demand producer)
                throws IOException {
            JsonObject canonicalProjection =
                    com.google.gson.JsonParser.parseString(
                            CanonicalJson.render(producer.projection()
                                    .json())).getAsJsonObject();
            return new Selection(producer.campaignId, producer.regionId,
                    producer.occurrenceId, producer.goalId,
                    ProducerOutputProjection.decode(canonicalProjection),
                    Collections.<String>emptySet());
        }
    }

    private static final class Endpoint {
        private final String instance;
        private final String input;

        private Endpoint(String instance, String input) {
            this.instance = instance == null ? "" : instance.trim();
            this.input = input == null ? "" : input.trim();
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof Endpoint)) return false;
            Endpoint value = (Endpoint) other;
            return instance.equals(value.instance) && input.equals(value.input);
        }

        @Override
        public int hashCode() {
            return 31 * instance.hashCode() + input.hashCode();
        }

        private String binding() {
            return instance + ":" + input;
        }
    }

    private static final class Target {
        private final RegionInstancePlan plan;
        private final Goal goal;
        private final String campaignId;
        private final String regionId;
        private final String relationKey;
        private final String occurrenceId;
        private final String goalId;
        private final Occurrence occurrence;
        private TargetRank rank = TargetRank.invalid();

        private Target(RegionInstancePlan plan, Goal goal,
                       Occurrence occurrence) {
            this.plan = plan;
            this.goal = goal;
            this.occurrence = occurrence;
            regionId = plan.regionId();
            relationKey = plan.relationKey();
            occurrenceId = occurrence.occurrenceId;
            goalId = goal.goalId();
            campaignId = campaignId(regionId, occurrenceId, goalId);
        }

        private String exactInput(String canonical) throws IOException {
            return occurrence.exactInput(canonical);
        }

        private String binding() {
            return campaignId + "\t" + regionId + "\t"
                    + occurrenceId + "\t" + goalId;
        }

        private JsonObject indexEntry(String taskId) {
            JsonObject result = new JsonObject();
            result.addProperty("campaignId", campaignId);
            result.addProperty("regionId", regionId);
            result.addProperty("relationKey", relationKey);
            result.addProperty("occurrenceId", occurrenceId);
            result.addProperty("goalId", goalId);
            result.addProperty("taskId", taskId);
            return result;
        }

        private String context() {
            return RuntimeWorkflowDiscovery.context(plan, goal);
        }

        private static int compare(Target left, Target right) {
            int compared = TargetRank.compare(left.rank, right.rank);
            if (compared != 0) return compared;
            compared = left.relationKey.compareTo(right.relationKey);
            if (compared != 0) return compared;
            compared = firstNonBlank(left.goal.pathSeedKey(), left.goalId)
                    .compareTo(firstNonBlank(right.goal.pathSeedKey(),
                            right.goalId));
            if (compared != 0) return compared;
            compared = left.goalId.compareTo(right.goalId);
            if (compared != 0) return compared;
            return left.occurrenceId.compareTo(right.occurrenceId);
        }
    }

    private static final class TargetRank {
        private final boolean valid;
        private final boolean exactDirectPresentation;
        private final boolean propagatedBoundedStateTransition;
        private final int stateBackedFatalInputs;
        private final int observedSelectedSemanticGuards;
        private final int residualFatalInputs;
        private final int fatalInputs;
        private final int producerGoals;
        private final int exactBindings;
        private final int causalRegions;

        private TargetRank(boolean valid, boolean exactDirectPresentation,
                           boolean propagatedBoundedStateTransition,
                           int stateBackedFatalInputs,
                           int observedSelectedSemanticGuards,
                           int residualFatalInputs,
                           int fatalInputs, int producerGoals,
                           int exactBindings, int causalRegions) {
            this.valid = valid;
            this.exactDirectPresentation = exactDirectPresentation;
            this.propagatedBoundedStateTransition =
                    propagatedBoundedStateTransition;
            this.stateBackedFatalInputs = stateBackedFatalInputs;
            this.observedSelectedSemanticGuards =
                    observedSelectedSemanticGuards;
            this.residualFatalInputs = residualFatalInputs;
            this.fatalInputs = fatalInputs;
            this.producerGoals = producerGoals;
            this.exactBindings = exactBindings;
            this.causalRegions = causalRegions;
        }

        private static TargetRank from(DemandClosure closure) {
            // producer-demands cannot execute a target-only campaign.  Keep
            // ranking consistent with that command instead of preferring an
            // otherwise well-formed zero-producer closure over a real one.
            if (closure.demands.isEmpty()) {
                return invalid();
            }
            return new TargetRank(true, closure.exactDirectPresentation,
                    closure.propagatedBoundedStateTransition,
                    closure.stateBackedFatalInputs,
                    closure.observedSelectedSemanticGuards,
                    closure.residualFatalInputs,
                    closure.fatalInputs, closure.demands.size(),
                    closure.exactBindings.size(),
                    closure.causalRegions.size());
        }

        private static TargetRank invalid() {
            return new TargetRank(false, false, false, 0, 0,
                    Integer.MAX_VALUE,
                    Integer.MAX_VALUE, Integer.MAX_VALUE,
                    Integer.MAX_VALUE, Integer.MAX_VALUE);
        }

        private static int compare(TargetRank left, TargetRank right) {
            int compared = Boolean.compare(right.valid, left.valid);
            if (compared != 0) return compared;
            // Prefer an occurrence where a failure-relevant protocol input
            // is presented by one exact, trusted cross-boundary edge.  A
            // same-process forwarding occurrence can have a much smaller
            // static slice while omitting the value that the remote peer
            // actually supplied.  This is trace/schema evidence, never an
            // application method-name heuristic.
            compared = Boolean.compare(right.exactDirectPresentation,
                    left.exactDirectPresentation);
            if (compared != 0) return compared;
            // A cheaper closure is not better when it leaves a fatal operand
            // free.  Rank the semantic boundary first; only equally closed
            // predicates are compared by replay/composition cost.
            compared = Integer.compare(left.residualFatalInputs,
                    right.residualFatalInputs);
            if (compared != 0) return compared;
            // Prefer the occurrence whose exact producer ancestry explains
            // more of the fatal predicate with bounded state evolution.  A
            // global "some state exists" bit is insufficient for a two-sided
            // predicate when only one operand is actually state-backed.
            compared = Integer.compare(right.stateBackedFatalInputs,
                    left.stateBackedFatalInputs);
            if (compared != 0) return compared;
            // Once the fatal frontier is equally closed, prefer a target
            // whose exact selected producer relation proves a bounded state
            // evolution.  This distinguishes coordination through evolving
            // cached state from a cheaper one-shot forwarding path without
            // relying on application identities.  It is deliberately a
            // boolean: replay/composition cost still decides among equally
            // stateful closures.
            compared = Boolean.compare(
                    right.propagatedBoundedStateTransition,
                    left.propagatedBoundedStateTransition);
            if (compared != 0) return compared;
            // Among equally closed/stateful targets, prefer the exact
            // occurrence that actually exercised more semantic decisions in
            // the selected producer members.  Loop controls, failure guards,
            // unobserved sites and replay-only assumptions do not contribute.
            compared = Integer.compare(
                    right.observedSelectedSemanticGuards,
                    left.observedSelectedSemanticGuards);
            if (compared != 0) return compared;
            compared = Integer.compare(left.fatalInputs,
                    right.fatalInputs);
            if (compared != 0) return compared;
            compared = Integer.compare(left.producerGoals,
                    right.producerGoals);
            if (compared != 0) return compared;
            compared = Integer.compare(left.causalRegions,
                    right.causalRegions);
            if (compared != 0) return compared;
            compared = Integer.compare(left.exactBindings,
                    right.exactBindings);
            if (compared != 0) return compared;
            return compared;
        }
    }

    private static final class SelectedProducerOccurrence {
        private final String relationKey;
        private final String occurrenceId;

        private SelectedProducerOccurrence(String relationKey,
                                           String occurrenceId) {
            this.relationKey = relationKey;
            this.occurrenceId = occurrenceId;
        }

    }

    private static final class Occurrence {
        private final String occurrenceId;
        private final String relationKey;
        private final Set<String> bindingIds;

        private Occurrence(Goal goal) {
            occurrenceId = goal.plan().occurrenceId();
            relationKey = goal.plan().relationKey();
            Set<String> ids = new LinkedHashSet<>();
            for (JsonElement element : goal.edgeBindings()) {
                if (element.isJsonObject()) {
                    String id = string(element.getAsJsonObject(), "edgeId");
                    if (!id.isEmpty()) ids.add(id);
                }
            }
            bindingIds = Collections.unmodifiableSet(ids);
        }

        private boolean sameIdentity(Occurrence other) {
            return other != null && occurrenceId.equals(other.occurrenceId);
        }

        private Map<String, String> exactInputs(Set<String> canonicalPorts) {
            Map<String, String> result = new LinkedHashMap<>();
            for (String port : canonicalPorts) {
                result.put(port, port);
            }
            return result;
        }

        private Map<String, String> canonicalOutputs(
                Set<String> canonicalPorts) {
            Map<String, String> result = new LinkedHashMap<>();
            for (String port : canonicalPorts) {
                result.put(port, port);
            }
            return result;
        }

        private Set<String> bindings(Set<String> selectedIds) {
            Set<String> result = new LinkedHashSet<>(bindingIds);
            result.retainAll(selectedIds);
            return result;
        }

        private String exactInput(String canonical) throws IOException {
            if (canonical == null || canonical.trim().isEmpty()) {
                throw new IOException("occurrence input is empty");
            }
            return canonical;
        }

        private String canonicalOutput(String exact) throws IOException {
            if (exact == null || exact.trim().isEmpty()) {
                throw new IOException("occurrence output is empty");
            }
            return exact;
        }
    }
}
