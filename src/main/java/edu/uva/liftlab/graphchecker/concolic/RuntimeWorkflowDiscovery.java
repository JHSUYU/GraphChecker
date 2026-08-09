package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.Goal;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
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
        Set<String> instances = new LinkedHashSet<>();
        for (JsonObject row : ArtifactIO.readJsonl(regionPlan)) {
            RegionInstancePlan plan = RegionInstancePlan.decode(row);
            if (!instances.add(plan.regionInstanceId())) {
                throw new IOException("duplicate regionInstanceId: "
                        + plan.regionInstanceId());
            }
            plans.add(plan);
        }
        if (plans.isEmpty()) {
            throw new IOException("runtime region plan is empty");
        }
        targets = discoverTargets();
        target = selectTarget(targetInstance, targetGoal);
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
                    + selectedTarget.regionInstanceId + "; outputGoals="
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
                    selectedTarget.regionInstanceId,
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
                    choices.add(new ProducerChoice(candidate, demand,
                            unresolved, selected.containsKey(candidate)));
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
                    + selectedTarget.regionInstanceId
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
                    selectedTarget.regionInstanceId,
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
        Set<String> selectedProducerOccurrences = new LinkedHashSet<>();
        for (Demand demand : result) {
            demand.addSelectedProducerOccurrences(
                    selectedProducerOccurrences);
        }
        boolean propagatedBoundedStateTransition = false;
        for (Demand demand : result) {
            causalRegions.add(demand.regionId);
            demand.addExactBindings(exactBindings);
            propagatedBoundedStateTransition |=
                    demand.selectsPropagatedBoundedStateTransition(
                            selectedProducerOccurrences,
                            selectedTarget.regionInstanceId);
        }
        int stateBackedFatalInputs = stateBackedFatalInputs(fatalInputs,
                selectedEdgeByEndpoint, result,
                selectedTarget.regionInstanceId);
        int residualFatalInputs = 0;
        for (Endpoint input : fatalInputs) {
            if (!discharged.contains(input)) residualFatalInputs++;
        }
        return new DemandClosure(result, exactBindings, causalRegions,
                fatalInputs.size(), residualFatalInputs,
                exactDirectPresentation, propagatedBoundedStateTransition,
                stateBackedFatalInputs);
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
        String sourceInstance = required(edge, "fromRegionInstance");
        Occurrence occurrence = demand.occurrences.require(sourceInstance);
        OutputClosureContract.Member member = demand.member(edge,
                occurrence);
        JsonObject slice = member.slice();
        if (!fatalTargetInstance.equals(required(edge,
                "toRegionInstance")) && boundedStateTransition(slice)) {
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
            }
        }
        return false;
    }

    private List<Target> discoverTargets() throws IOException {
        List<Target> matches = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (goal.kind() == ClosureGoalKind.TARGET_REACH_CLOSURE) {
                    try {
                        OccurrenceCatalog catalog =
                                OccurrenceCatalog.from(goal);
                        for (Occurrence occurrence
                                : catalog.occurrences.values()) {
                            matches.add(new Target(plan, goal, occurrence));
                        }
                    } catch (IllegalArgumentException malformed) {
                        throw new IOException("invalid logical target "
                                + "occurrence catalog; "
                                + context(plan, goal), malformed);
                    }
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
                    && !targetInstance.equals(candidate.regionInstanceId))
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
            // A logical summary's outputClosure is canonical and therefore
            // contains only its canonical occurrence edges.  edgeBindings is
            // the exact-occurrence ledger; index every trusted outgoing edge
            // from this logical region so a later loop/RPC occurrence can
            // satisfy an exact downstream port while still reusing one VM
            // relation.
            Set<String> selectedIds = new LinkedHashSet<>();
            for (JsonElement element : goal.edgeBindings()) {
                if (!element.isJsonObject()) continue;
                JsonObject edge = element.getAsJsonObject();
                String fromRegion = string(edge, "fromRegion");
                String fromInstance = string(edge,
                        "fromRegionInstance");
                boolean sameRegion = plan.regionId().equals(fromRegion)
                        || fromInstance.equals(plan.regionInstanceId())
                        || fromInstance.startsWith(plan.regionId() + "@");
                if (!sameRegion || string(edge, "fromOutputPort").isEmpty()
                        || !AutomaticRegionEdge
                        .trustedRuntimeCompositionBinding(edge)) {
                    continue;
                }
                String id = string(edge, "edgeId");
                if (selectedIds.add(id)) result.add(edge.deepCopy());
            }
            // Older/small artifacts may carry only the canonical contract.
            if (result.isEmpty()) {
                for (JsonObject edge : closure.causalEdges()) {
                    if (AutomaticRegionEdge
                            .trustedRuntimeCompositionBinding(edge)) {
                        result.add(edge.deepCopy());
                    }
                }
            }
            return result;
        }

        // A non-READY producer has no output-closure contract yet.  Its
        // binding ledger may still be used to fail closed when it is on the
        // exact frontier, but only edges emitted by this goal's execution
        // occurrence are producer candidates.  Incoming bindings describe
        // the relation's dependencies; indexing them as outputs makes the
        // relation appear to produce its own inputs.
        String producer = goal.executionRegionInstanceId();
        for (JsonElement item : goal.edgeBindings()) {
            if (item.isJsonObject()) {
                JsonObject edge = item.getAsJsonObject();
                if (producer.equals(string(edge, "fromRegionInstance"))
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
        List<ExecutionTask> matches = new ArrayList<>();
        for (ExecutionTask task : tasks) {
            if (demand.regionId.equals(task.regionId())
                    && demand.logicalRegionId.equals(firstNonBlank(
                    task.logicalRegionId(), task.regionInstanceId()))
                    && demand.goalId.equals(task.goalId())
                    && task.goalKind().capturesOutputRelation()
                    && task.outputClosure() != null
                    && task.executable()) {
                matches.add(task);
            }
        }
        ExecutionTask task = onlyTask(matches,
                "scheduled producer task; " + demand.context());
        JsonObject encodedProjection = task.producerProjection();
        if (encodedProjection.size() == 0
                || !CanonicalJson.render(demand.projection().json()).equals(
                CanonicalJson.render(encodedProjection))) {
            throw new IOException("scheduled producer task does not match "
                    + "selected exact-output projection; "
                    + demand.context());
        }
        return task;
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
                    && selectedTarget.logicalRegionId.equals(firstNonBlank(
                    task.logicalRegionId(), task.regionInstanceId()))
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

    /**
     * A logical target relation may be executed once using its canonical
     * semantic path seed and instantiated at several trace occurrences.  The
     * selected trace occurrence therefore must be present in the task's
     * compact occurrence catalog; it must not be confused with the VM task's
     * canonical execution identity (or with an invocation ordinal).
     */
    private static void requireSelectedTargetOccurrence(
            Target selectedTarget, ExecutionTask task) throws IOException {
        JsonObject encoded = task.occurrenceInstantiationCatalog();
        if (integer(encoded, "schemaVersion", -1) != 1
                || !"LOGICAL_SUMMARY_OCCURRENCE_CATALOG".equals(
                string(encoded, "kind"))
                || !selectedTarget.logicalRegionId.equals(
                string(encoded, "logicalRegionId"))
                || !task.summaryReuseKey().equals(
                string(encoded, "summaryReuseKey"))
                || !task.regionInstanceId().equals(string(encoded,
                "canonicalRegionInstanceId"))) {
            throw new IOException("scheduled target task has malformed "
                    + "logical occurrence catalog; "
                    + selectedTarget.context());
        }

        final OccurrenceCatalog actual;
        try {
            actual = OccurrenceCatalog.from(encoded);
        } catch (IllegalArgumentException malformed) {
            throw new IOException("scheduled target task has malformed "
                    + "logical occurrence catalog; "
                    + selectedTarget.context(), malformed);
        }
        Occurrence selected = actual.require(
                selectedTarget.regionInstanceId);
        if (!selected.sameIdentity(selectedTarget.occurrence)) {
            throw new IOException("scheduled target task occurrence does "
                    + "not match selected runtime evidence: "
                    + selectedTarget.regionInstanceId);
        }

        Set<String> canonicalInputs = new LinkedHashSet<>();
        for (JsonElement element : task.inputActions().all()) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            String port = firstNonBlank(string(action, "portId"),
                    string(action, "symbol"));
            if (!port.isEmpty()) canonicalInputs.add(port);
        }
        Map<String, String> expectedInputs = new LinkedHashMap<>();
        for (String canonical : canonicalInputs) {
            String exact = selectedTarget.occurrence
                    .exactInputByCanonical.get(canonical);
            if (exact != null) expectedInputs.put(canonical, exact);
        }
        if (!selected.exactInputByCanonical.equals(expectedInputs)
                || expectedInputs.size() != canonicalInputs.size()
                || !selected.canonicalOutputByExact.isEmpty()) {
            throw new IOException("scheduled target task occurrence port "
                    + "map does not cover the target inputs exactly: "
                    + selectedTarget.regionInstanceId);
        }

        Set<String> exactInputs = new LinkedHashSet<>(
                selected.exactInputByCanonical.values());
        Set<String> touchingBindings = new LinkedHashSet<>();
        Set<String> demandedBindings = new LinkedHashSet<>();
        for (JsonElement element : task.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!selectedTarget.regionInstanceId.equals(string(binding,
                    "fromRegionInstance"))
                    && !selectedTarget.regionInstanceId.equals(
                    string(binding, "toRegionInstance"))) {
                continue;
            }
            String edgeId = string(binding, "edgeId");
            if (edgeId.isEmpty()) {
                throw new IOException("scheduled target occurrence binding "
                        + "has no edgeId: "
                        + selectedTarget.regionInstanceId);
            }
            touchingBindings.add(edgeId);
            if (selectedTarget.regionInstanceId.equals(string(binding,
                    "toRegionInstance")) && exactInputs.contains(
                    string(binding, "toInputPort"))) {
                demandedBindings.add(edgeId);
            }
        }
        if (!touchingBindings.containsAll(selected.bindingIds)
                || !selected.bindingIds.containsAll(demandedBindings)
                || !selectedTarget.occurrence.bindingIds.containsAll(
                selected.bindingIds)) {
            throw new IOException("scheduled target occurrence binding "
                    + "ledger is incomplete: "
                    + selectedTarget.regionInstanceId);
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
                                     String regionInstanceId,
                                     String goalId) {
        String region = safeToken(regionId);
        Matcher call = CALL_ID.matcher(regionInstanceId);
        String invocation = call.find()
                ? "call" + call.group(1)
                : "instance-"
                + ArtifactIO.sha256(regionInstanceId).substring(0, 8);
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
                + "; instance=" + plan.regionInstanceId()
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
        private final String logicalRegionId;
        private final String regionInstanceId;
        private final String goalId;
        private final OccurrenceCatalog occurrences;
        private final Map<Endpoint, JsonObject> selectedEdges =
                new LinkedHashMap<>();
        private final Set<Endpoint> requiredInputEndpoints =
                new LinkedHashSet<>();
        private ProducerOutputProjection projection;

        private Demand(RegionInstancePlan plan, Goal goal) {
            this.plan = plan;
            this.goal = goal;
            regionId = plan.regionId();
            logicalRegionId = plan.logicalRegionId();
            regionInstanceId = goal.executionRegionInstanceId();
            goalId = goal.goalId();
            campaignId = campaignId(regionId, logicalRegionId, goalId);
            occurrences = OccurrenceCatalog.from(goal);
        }

        private void addRequiredInputs(Set<Endpoint> endpoints,
                                       ProducerCandidate candidate,
                                       Set<Endpoint> frontier,
                                       Map<Endpoint, List<ProducerCandidate>>
                                               producersByDownstream)
                throws IOException {
            if (goal.outputClosure() == null) return;
            for (Endpoint target : endpoints) {
                JsonObject edge = candidate.edgeFor(target);
                JsonObject prior = selectedEdges.putIfAbsent(target, edge);
                if (prior != null && !required(prior, "edgeId").equals(
                        required(edge, "edgeId"))) {
                    throw new IOException("exact downstream input selected "
                            + "more than one output: " + target.binding());
                }
                String sourceInstance = required(edge,
                        "fromRegionInstance");
                Occurrence occurrence = occurrences.require(sourceInstance);
                OutputClosureContract.Member member = member(edge,
                        occurrence);
                for (JsonElement input : member.slice()
                        .getAsJsonArray("inputPorts")) {
                    String port = input.getAsString();
                    Endpoint endpoint = new Endpoint(sourceInstance,
                            occurrence.exactInput(port));
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
                Occurrence occurrence = occurrences.require(
                        required(edge, "fromRegionInstance"));
                outputs.add(member(edge, occurrence).portId());
                edgeIds.add(required(edge, "edgeId"));
            }
            for (Endpoint input : requiredInputEndpoints) {
                JsonObject edge = selectedEdgeByEndpoint.get(input);
                if (edge != null) edgeIds.add(required(edge, "edgeId"));
            }
            projection = ProducerOutputProjection.create(campaignId,
                    regionId, logicalRegionId, goalId,
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
            String sourceInstance = required(edge, "fromRegionInstance");
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
                JsonObject edge = candidate.edgeFor(endpoint);
                Occurrence occurrence = occurrences.require(
                        required(edge, "fromRegionInstance"));
                result.add(member(edge, occurrence).portId());
            }
            return result;
        }

        private Set<String> demandedInputs(Set<Endpoint> endpoints,
                                           ProducerCandidate candidate)
                throws IOException {
            Set<String> result = new LinkedHashSet<>();
            for (Endpoint endpoint : endpoints) {
                JsonObject edge = candidate.edgeFor(endpoint);
                Occurrence occurrence = occurrences.require(
                        required(edge, "fromRegionInstance"));
                for (JsonElement input : member(edge, occurrence).slice()
                        .getAsJsonArray("inputPorts")) {
                    result.add(input.getAsString());
                }
            }
            return result;
        }

        private void addExactBindings(Set<String> bindings)
                throws IOException {
            for (Map.Entry<Endpoint, JsonObject> selected
                    : selectedEdges.entrySet()) {
                Endpoint target = selected.getKey();
                JsonObject edge = selected.getValue();
                bindings.add(required(edge, "fromRegionInstance") + "\n"
                        + required(edge, "fromOutputPort") + "\n"
                        + target.instance + "\n" + target.input);
            }
        }

        /**
         * True only when an exact selected output is one complete bounded
         * transition and its selected edge enters another selected producer
         * occurrence before the fatal target.  A target-local cache update
         * is common to every presentation of the same failure and therefore
         * must not make an otherwise one-shot input look stateful.
         */
        private boolean selectsPropagatedBoundedStateTransition(
                Set<String> selectedProducerOccurrences,
                String fatalTargetInstance) throws IOException {
            for (JsonObject edge : selectedEdges.values()) {
                String consumer = required(edge, "toRegionInstance");
                if (consumer.equals(fatalTargetInstance)
                        || !selectedProducerOccurrences.contains(consumer)) {
                    continue;
                }
                Occurrence occurrence = occurrences.require(
                        required(edge, "fromRegionInstance"));
                JsonObject slice = member(edge, occurrence).slice();
                if (boundedStateTransition(slice)) {
                    return true;
                }
            }
            return false;
        }

        private void addSelectedProducerOccurrences(Set<String> result)
                throws IOException {
            for (JsonObject edge : selectedEdges.values()) {
                String occurrence = required(edge, "fromRegionInstance");
                occurrences.require(occurrence);
                result.add(occurrence);
            }
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
                    + regionInstanceId + "\t" + goalId;
        }

        private String context() {
            return RuntimeWorkflowDiscovery.context(plan, goal);
        }

        private String sortKey() {
            return regionInstanceId + "\n" + goalId;
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
                String instance = string(edge, "toRegionInstance");
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
                alternatives.sort(Comparator.comparing(
                        ProducerCandidate::edgeSortKey));
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

        private JsonObject edgeFor(Endpoint endpoint) throws IOException {
            List<JsonObject> edges = edgesByDownstream.get(endpoint);
            if (edges == null || edges.isEmpty()) {
                throw new IOException("producer candidate has no edge for "
                        + endpoint.binding());
            }
            return edges.get(0);
        }

        private List<JsonObject> edgesFor(Endpoint endpoint) {
            return edgesByDownstream.getOrDefault(endpoint,
                    java.util.Collections.emptyList());
        }

        private String semanticKey() {
            OutputClosureContract closure = goal.outputClosure();
            return plan.regionId() + "\n" + plan.logicalRegionId() + "\n"
                    + firstNonBlank(goal.pathSeedKey(), goal.goalId()) + "\n"
                    + (closure == null ? "" : closure.demandKey()) + "\n"
                    + goal.goalId();
        }

        private static String edgeSortKey(JsonObject edge) {
            return string(edge, "fromOutputPort") + "\n"
                    + string(edge, "edgeId") + "\n"
                    + string(edge, "fromRegionInstance");
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
                if (unresolved.contains(endpoint)) {
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

        private DemandClosure(List<Demand> demands,
                              Set<String> exactBindings,
                              Set<String> causalRegions, int fatalInputs,
                              int residualFatalInputs,
                              boolean exactDirectPresentation,
                              boolean propagatedBoundedStateTransition,
                              int stateBackedFatalInputs) {
            this.demands = demands;
            this.exactBindings = exactBindings;
            this.causalRegions = causalRegions;
            this.fatalInputs = fatalInputs;
            this.residualFatalInputs = residualFatalInputs;
            this.exactDirectPresentation = exactDirectPresentation;
            this.propagatedBoundedStateTransition =
                    propagatedBoundedStateTransition;
            this.stateBackedFatalInputs = stateBackedFatalInputs;
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
        private final String logicalRegionId;
        private final String regionInstanceId;
        private final String goalId;
        private final Occurrence occurrence;
        private TargetRank rank = TargetRank.invalid();

        private Target(RegionInstancePlan plan, Goal goal,
                       Occurrence occurrence) {
            this.plan = plan;
            this.goal = goal;
            this.occurrence = occurrence;
            regionId = plan.regionId();
            logicalRegionId = plan.logicalRegionId();
            regionInstanceId = occurrence.regionInstanceId;
            goalId = goal.goalId();
            campaignId = campaignId(regionId, regionInstanceId, goalId);
        }

        private String exactInput(String canonical) throws IOException {
            return occurrence.exactInput(canonical);
        }

        private String binding() {
            return campaignId + "\t" + regionId + "\t"
                    + regionInstanceId + "\t" + goalId;
        }

        private String context() {
            return RuntimeWorkflowDiscovery.context(plan, goal);
        }

        private static int compare(Target left, Target right) {
            int compared = TargetRank.compare(left.rank, right.rank);
            if (compared != 0) return compared;
            compared = left.logicalRegionId.compareTo(right.logicalRegionId);
            if (compared != 0) return compared;
            compared = firstNonBlank(left.goal.pathSeedKey(), left.goalId)
                    .compareTo(firstNonBlank(right.goal.pathSeedKey(),
                            right.goalId));
            if (compared != 0) return compared;
            compared = left.goalId.compareTo(right.goalId);
            if (compared != 0) return compared;
            compared = Long.compare(left.occurrence.rootCallId,
                    right.occurrence.rootCallId);
            if (compared != 0) return compared;
            return left.regionInstanceId.compareTo(right.regionInstanceId);
        }
    }

    private static final class TargetRank {
        private final boolean valid;
        private final boolean exactDirectPresentation;
        private final boolean propagatedBoundedStateTransition;
        private final int stateBackedFatalInputs;
        private final int residualFatalInputs;
        private final int fatalInputs;
        private final int producerGoals;
        private final int exactBindings;
        private final int causalRegions;

        private TargetRank(boolean valid, boolean exactDirectPresentation,
                           boolean propagatedBoundedStateTransition,
                           int stateBackedFatalInputs,
                           int residualFatalInputs,
                           int fatalInputs, int producerGoals,
                           int exactBindings, int causalRegions) {
            this.valid = valid;
            this.exactDirectPresentation = exactDirectPresentation;
            this.propagatedBoundedStateTransition =
                    propagatedBoundedStateTransition;
            this.stateBackedFatalInputs = stateBackedFatalInputs;
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
                    closure.residualFatalInputs,
                    closure.fatalInputs, closure.demands.size(),
                    closure.exactBindings.size(),
                    closure.causalRegions.size());
        }

        private static TargetRank invalid() {
            return new TargetRank(false, false, false, 0, Integer.MAX_VALUE,
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

    private static final class OccurrenceCatalog {
        private final Map<String, Occurrence> occurrences =
                new LinkedHashMap<>();

        private static OccurrenceCatalog from(Goal goal) {
            return from(goal.occurrenceInstantiationCatalog());
        }

        private static OccurrenceCatalog from(JsonObject encoded) {
            OccurrenceCatalog result = new OccurrenceCatalog();
            for (JsonElement element : array(encoded, "occurrences")) {
                if (!element.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "occurrence catalog contains a non-object");
                }
                Occurrence occurrence = new Occurrence(
                        element.getAsJsonObject());
                if (result.occurrences.putIfAbsent(
                        occurrence.regionInstanceId, occurrence) != null) {
                    throw new IllegalArgumentException(
                            "duplicate occurrence "
                                    + occurrence.regionInstanceId);
                }
            }
            if (result.occurrences.isEmpty()) {
                throw new IllegalArgumentException(
                        "occurrence catalog is empty");
            }
            return result;
        }

        private Occurrence require(String instance) throws IOException {
            Occurrence result = occurrences.get(instance);
            if (result == null) {
                throw new IOException("logical summary has no exact "
                        + "occurrence " + instance);
            }
            return result;
        }
    }

    private static final class Occurrence {
        private final String regionInstanceId;
        private final long rootCallId;
        private final Map<String, String> exactInputByCanonical;
        private final Map<String, String> canonicalOutputByExact;
        private final Set<String> bindingIds;

        private Occurrence(JsonObject encoded) {
            regionInstanceId = string(encoded, "regionInstanceId");
            rootCallId = longInteger(encoded, "rootCallId", -1L);
            if (regionInstanceId.isEmpty() || (rootCallId >= 0L
                    && !regionInstanceId.endsWith("#call" + rootCallId))) {
                throw new IllegalArgumentException(
                        "occurrence requires consistent instance/root");
            }
            exactInputByCanonical = portMap(encoded, "inputPortMap",
                    false);
            canonicalOutputByExact = portMap(encoded, "outputPortMap",
                    true);
            bindingIds = stringSet(encoded, "bindingIds");
        }

        private boolean sameIdentity(Occurrence other) {
            return other != null && rootCallId == other.rootCallId
                    && regionInstanceId.equals(other.regionInstanceId);
        }

        private String exactInput(String canonical) throws IOException {
            String result = exactInputByCanonical.get(canonical);
            if (result == null) {
                throw new IOException("occurrence " + regionInstanceId
                        + " has no exact input for " + canonical);
            }
            return result;
        }

        private String canonicalOutput(String exact) throws IOException {
            String result = canonicalOutputByExact.get(exact);
            if (result == null) {
                throw new IOException("occurrence " + regionInstanceId
                        + " has no canonical output for " + exact);
            }
            return result;
        }

        private static Map<String, String> portMap(
                JsonObject occurrence, String field, boolean reverse) {
            Map<String, String> result = new LinkedHashMap<>();
            for (JsonElement element : array(occurrence, field)) {
                if (!element.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "malformed " + field);
                }
                JsonObject mapping = element.getAsJsonObject();
                String canonical = string(mapping, "canonicalPort");
                String exact = string(mapping, "exactPort");
                String key = reverse ? exact : canonical;
                String value = reverse ? canonical : exact;
                if (key.isEmpty() || value.isEmpty()
                        || result.putIfAbsent(key, value) != null) {
                    throw new IllegalArgumentException(
                            "ambiguous " + field);
                }
            }
            return result;
        }

        private static Set<String> stringSet(
                JsonObject occurrence, String field) {
            Set<String> result = new LinkedHashSet<>();
            for (JsonElement element : array(occurrence, field)) {
                if (!element.isJsonPrimitive()
                        || !element.getAsJsonPrimitive().isString()) {
                    throw new IllegalArgumentException(
                            "malformed " + field);
                }
                String value = element.getAsString().trim();
                if (value.isEmpty() || !result.add(value)) {
                    throw new IllegalArgumentException(
                            "ambiguous " + field);
                }
            }
            return result;
        }
    }
}
