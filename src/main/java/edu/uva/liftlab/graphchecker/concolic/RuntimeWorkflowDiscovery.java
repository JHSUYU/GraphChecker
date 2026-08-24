package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.Goal;

import java.io.IOException;
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
    private static final String SHARED_LOCATION_DEMAND =
            "SHARED_LOCATION_DEMAND_V1";
    private static final String DEMANDED_BY_REGIONS =
            "demandedByRegionIds";
    private static final Pattern CALL_ID = Pattern.compile(
            "(?:^|[#@])call([0-9]+)(?:$|[^0-9])");

    /**
     * An input of a demanded output slice that nothing can materialize.
     *
     * <p>Three answers make an input materializable, and this name is what is
     * left when none of them holds: the goal declares a dependency action for
     * it, a scheduled producer relation discharges it, or it is a declared
     * cut port whose value crossed the cut.  A fourth answer - "leave it
     * concrete" - is the one that must never be given silently: the fragment
     * would publish a relation over inputs it never bound, and every later
     * stage would read the recorded values of those inputs as if the relation
     * had constrained them.</p>
     *
     * <p>Named rather than skipped because the repair is never here.  The
     * port is stated by the closure member's own slice, so a goal that cannot
     * bind it is a fragment whose declared inputs and whose recorded
     * dependency evidence were attributed to different fragments upstream.</p>
     */
    static final String OUTPUT_SLICE_INPUT_UNMATERIALIZABLE =
            "RUNTIME_OUTPUT_SLICE_INPUT_UNMATERIALIZABLE";

    private final List<RegionInstancePlan> plans = new ArrayList<>();
    private final Map<String, RegionInstancePlan> plansByOccurrence =
            new LinkedHashMap<>();
    private final Map<String, List<RegionInstancePlan>>
            admittedPlansByConsumerRegion = new LinkedHashMap<>();
    private final Map<Endpoint, List<ProducerCandidate>>
            producersByDownstream = new LinkedHashMap<>();
    private final Map<String, List<ProducerCandidate>>
            producerCandidatesByOccurrence = new LinkedHashMap<>();
    private final List<Target> targets;

    @FunctionalInterface
    interface FailureInputSelection {
        boolean selected(String regionId, JsonObject action);
    }

    @FunctionalInterface
    interface SourceOutputSelection {
        Set<String> selected(String regionId,
                             OutputClosureContract closure);
    }

    private final FailureInputSelection failureInputSelection;

    private RuntimeWorkflowDiscovery(
            Iterable<JsonObject> regionPlan,
            FailureInputSelection failureInputSelection)
            throws IOException {
        if (failureInputSelection == null) {
            throw new IllegalArgumentException(
                    "failure input selection is required");
        }
        this.failureInputSelection = failureInputSelection;
        // A region is coarse: one selected execution-context entry and the
        // selected nested calls executed in it.  One plan row is therefore
        // one region occurrence, and that occurrence is the identity a row is
        // unique under.
        Set<String> occurrences = new LinkedHashSet<>();
        for (JsonObject row : regionPlan) {
            // The plan artifact this list was read from already refused every
            // incomplete executable row; this pass owns the uniqueness of the
            // occurrence, and re-refusing here would report a schema
            // complaint in place of the duplicate it exists to name.
            RegionInstancePlan plan = RegionInstancePlan.decode(row);
            if (!occurrences.add(plan.occurrenceKey())) {
                throw new IOException("duplicate region occurrence: "
                        + plan.occurrenceId());
            }
            // The relation key is deliberately not checked for uniqueness: a
            // worker whose activation ran three times contributes three rows
            // sharing one relation key.  That is the relation having
            // occurrences, not the planner contradicting itself.
            plans.add(plan);
            plansByOccurrence.put(plan.occurrenceKey(), plan);
        }
        if (plans.isEmpty()) {
            throw new IOException("runtime region plan is empty");
        }
        for (RegionInstancePlan plan : plans) {
            JsonObject row = plan.jsonView();
            if (!SHARED_LOCATION_DEMAND.equals(
                    string(row, "admissionBasis"))) {
                continue;
            }
            for (String consumer : strings(array(row,
                    DEMANDED_BY_REGIONS))) {
                admittedPlansByConsumerRegion.computeIfAbsent(consumer,
                        ignored -> new ArrayList<>()).add(plan);
            }
        }
        indexProducerCandidates();
        targets = discoverTargets();
    }

    /** Builds the immutable exact producer index once for all target ranks. */
    private void indexProducerCandidates() {
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (!goal.kind().capturesOutputRelation()) continue;
                List<JsonObject> edges = trustedEdges(plan, goal);
                if (edges.isEmpty()) continue;
                ProducerCandidate candidate =
                        new ProducerCandidate(plan, goal, edges);
                producerCandidatesByOccurrence.computeIfAbsent(
                        plan.occurrenceId(), ignored -> new ArrayList<>())
                        .add(candidate);
                for (Endpoint downstream : candidate.downstreamEndpoints) {
                    producersByDownstream.computeIfAbsent(downstream,
                            ignored -> new ArrayList<>()).add(candidate);
                }
            }
        }
    }

    /**
     * Materializes the ranked target-first workflow from an already decoded
     * region plan.  The scheduler uses this entry point so discovery and all
     * selected goals share one parse of the large runtime artifact.
     */
    static RankedWorkflow rankedWorkflow(
            List<JsonObject> regionPlan,
            FailureInputSelection failureInputSelection)
            throws IOException {
        return rankedWorkflow(regionPlan, failureInputSelection,
                (regionId, closure) -> Collections.emptySet());
    }

    static RankedWorkflow rankedWorkflow(
            List<JsonObject> regionPlan,
            FailureInputSelection failureInputSelection,
            SourceOutputSelection sourceOutputSelection)
            throws IOException {
        if (sourceOutputSelection == null) {
            throw new IllegalArgumentException(
                    "source output selection is required");
        }
        RuntimeWorkflowDiscovery discovery =
                new RuntimeWorkflowDiscovery(regionPlan,
                        failureInputSelection);
        Target selected = discovery.admissibleTargets().get(0);
        if (!selected.goal.replayable()) {
            throw new IOException("ranked target goal is not replayable; "
                    + selected.context());
        }
        List<Demand> producers = discovery.discoverDemands(selected,
                sourceOutputSelection);
        return new RankedWorkflow(selected, producers);
    }

    /**
     * Selects one READY producer alternative for each exact downstream input
     * in the reverse runtime read-from closure rooted at the target.
     * A selected relation may discharge several distinct inputs at once.
     */
    private List<Demand> discoverDemands(
            Target selectedTarget, SourceOutputSelection sourceSelection)
            throws IOException {
        DemandClosure closure = discoverDemandClosure(selectedTarget,
                sourceSelection);
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
        return discoverDemandClosure(selectedTarget,
                (regionId, closure) -> Collections.emptySet());
    }

    private DemandClosure discoverDemandClosure(
            Target selectedTarget, SourceOutputSelection sourceSelection)
            throws IOException {
        // This is the target's fatal input frontier, before producer inputs
        // extend the recursive closure.  Ranking is about freedom left on the
        // fault predicate itself, so retain this boundary separately from the
        // producer inputs subsequently added to frontier.
        Set<Endpoint> fatalInputs = new LinkedHashSet<>();
        for (JsonElement item : selectedTarget.goal.symbolizeView()) {
            if (!item.isJsonObject()) continue;
            JsonObject action = item.getAsJsonObject();
            String input = string(action, "symbol");
            if (input.isEmpty()) continue;
            Endpoint endpoint = Endpoint.of(selectedTarget.plan,
                    selectedTarget.occurrenceId,
                    selectedTarget.exactInput(input));
            if (failureInputSelection.selected(
                    selectedTarget.regionId, action)
                    && (causalAction(action)
                    || exactTrustedCausalProducer(endpoint,
                    producersByDownstream))) {
                fatalInputs.add(endpoint);
            }
        }
        // A communication cut is already an explicit input of this exact
        // target occurrence even when the local backward slice represents a
        // decoded request value through a container query rather than through
        // the handler parameter.  Keep the recorded incoming port on the
        // frontier so the first campaign executes the exporting occurrence and
        // can replace trace correlation with a VM symbolic handoff.
        Set<String> structuredProtocolParents = new LinkedHashSet<>();
        Map<Endpoint, Set<String>> targetProtocolEdges =
                new LinkedHashMap<>();
        for (JsonElement item : selectedTarget.goal.edgeBindingsView()) {
            if (!item.isJsonObject()) continue;
            JsonObject edge = item.getAsJsonObject();
            if (!selectedTarget.occurrenceId.equals(
                    string(edge, "toOccurrenceId"))) {
                continue;
            }
            String parent = string(edge,
                    CommunicationCatalogContract.PORT_COMPONENT_OF);
            if (!parent.isEmpty()) structuredProtocolParents.add(parent);
        }
        for (JsonElement item : selectedTarget.goal.edgeBindingsView()) {
            if (!item.isJsonObject()) continue;
            JsonObject edge = item.getAsJsonObject();
            if (!"RUNTIME_PROTOCOL_FLOW".equals(string(edge, "kind"))
                    || !selectedTarget.occurrenceId.equals(
                    string(edge, "toOccurrenceId"))
                    || !AutomaticRegionEdge
                    .schedulableProducerBinding(edge)) {
                continue;
            }
            String input = string(edge, "toInputPort");
            // A declared aggregate whose transported leaves are explicit is a
            // concrete carrier, not a second symbolic operand.  Requiring both
            // the aggregate and every leaf duplicates one interaction and is
            // exactly what left structured VM handoffs with a phantom p0
            // demand.  The leaves remain on the frontier and the VM handoff is
            // still the only value authority.
            if (!input.isEmpty()
                    && !structuredProtocolParents.contains(input)) {
                Endpoint endpoint = Endpoint.of(selectedTarget.plan,
                        selectedTarget.occurrenceId,
                        selectedTarget.exactInput(input));
                fatalInputs.add(endpoint);
                String edgeId = string(edge, "edgeId");
                if (!edgeId.isEmpty()) {
                    targetProtocolEdges.computeIfAbsent(endpoint,
                            ignored -> new LinkedHashSet<>()).add(edgeId);
                }
            }
        }
        CausalFrontier frontier = new CausalFrontier(fatalInputs);
        for (Map.Entry<Endpoint, Set<String>> exact
                : targetProtocolEdges.entrySet()) {
            frontier.constrain(exact.getKey(), exact.getValue());
        }
        Map<Endpoint, ProducerCandidate> producerByEndpoint =
                new LinkedHashMap<>();
        Map<ProducerCandidate, Demand> selected = new LinkedHashMap<>();
        Map<String, Demand> admitted = new LinkedHashMap<>();
        while (true) {
            int selectedBefore = selected.size();
            int admittedBefore = admitted.size();
            resolveProducerFrontier(frontier, producerByEndpoint, selected,
                    producersByDownstream);
            admitSharedStateStep(selectedTarget, selected, admitted,
                    frontier, producerByEndpoint, producersByDownstream);
            boolean sourceFrontierChanged = false;
            for (Demand demand : selected.values()) {
                sourceFrontierChanged |= demand.includeSourceOutputInputs(
                        sourceSelection, frontier, producersByDownstream);
            }
            if (selected.size() == selectedBefore
                    && admitted.size() == admittedBefore
                    && !sourceFrontierChanged) {
                break;
            }
        }

        Set<Endpoint> discharged = producerByEndpoint.keySet();
        Set<String> blocked = new LinkedHashSet<>();
        for (Endpoint downstream : frontier.endpoints()) {
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

        List<Demand> result = new ArrayList<>(selected.values());
        Map<Endpoint, JsonObject> selectedEdgeByEndpoint =
                new LinkedHashMap<>();
        for (Demand demand : result) {
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
        for (Demand demand : result) {
            demand.finalizeProjection(selectedEdgeByEndpoint);
        }

        boolean exactDirectPresentation = false;
        for (Endpoint endpoint : fatalInputs) {
            JsonObject edge = selectedEdgeByEndpoint.get(endpoint);
            // The first live campaign cannot already carry the VM handoff
            // attestation that campaign is meant to produce.  A uniquely
            // correlated runtime delivery is sufficient for target ranking
            // and producer scheduling; composition still rejects it until
            // the VM publishes the exact symbolic handoff evidence.
            if (edge != null
                    && "RUNTIME_PROTOCOL_FLOW".equals(
                    string(edge, "kind"))
                    && AutomaticRegionEdge
                    .schedulableProducerBinding(edge)) {
                exactDirectPresentation = true;
                break;
            }
        }

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
        int valueBackedFatalInputs = valueBackedFatalInputs(fatalInputs,
                selectedEdgeByEndpoint);
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
                valueBackedFatalInputs, stateBackedFatalInputs,
                observedSemanticGuards.size());
    }

    /**
     * Counts fatal operands whose selected producer edge carries a value,
     * rather than only the identity of a concrete transport/container.
     *
     * <p>Runtime object identity is sufficient to select a concrete
     * read-from arm, but it is not by itself a symbolic value lineage.  Target
     * ranking must therefore prefer an occurrence backed by a transported or
     * state value before using closure size as a tie-breaker.  Composition
     * remains the authority that requires the eventual VM handoff or recorded
     * state relation.</p>
     */
    private static int valueBackedFatalInputs(
            Set<Endpoint> fatalInputs,
            Map<Endpoint, JsonObject> selectedEdgeByEndpoint) {
        int backed = 0;
        for (Endpoint input : fatalInputs) {
            JsonObject edge = selectedEdgeByEndpoint.get(input);
            if (edge != null && DependencyRole.VALUE_FRONTIER.equals(
                    DependencyRole.normalize(edge.get("dependencyRole")))) {
                backed++;
            }
        }
        return backed;
    }

    /** Resolves the exact producer frontier until no READY edge can extend it. */
    private void resolveProducerFrontier(
            CausalFrontier frontier,
            Map<Endpoint, ProducerCandidate> producerByEndpoint,
            Map<ProducerCandidate, Demand> selected,
            Map<Endpoint, List<ProducerCandidate>> producersByDownstream)
            throws IOException {
        while (true) {
            Set<Endpoint> unresolved = new LinkedHashSet<>(
                    frontier.endpoints());
            unresolved.removeAll(producerByEndpoint.keySet());
            List<ProducerChoice> choices = new ArrayList<>();
            Set<ProducerCandidate> eligible = new LinkedHashSet<>();
            for (Endpoint downstream : unresolved) {
                for (ProducerCandidate candidate
                        : producersByDownstream.getOrDefault(downstream,
                        java.util.Collections.emptyList())) {
                    if (candidate.ready() && candidate.covers(downstream,
                            candidate.occurrence,
                            frontier.allowedEdges(downstream))) {
                        eligible.add(candidate);
                    }
                }
            }
            for (ProducerCandidate candidate : eligible) {
                Demand demand = selected.get(candidate);
                try {
                    if (demand == null) demand = candidate.materialize();
                    ProducerChoice choice = new ProducerChoice(candidate,
                            demand, unresolved, frontier,
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
    }

    /**
     * Adds one fixed-point layer of explicitly admitted state writers.
     *
     * <p>An admission is usable only when its declared consumer region is in
     * the current causal closure <em>and</em> one of its exact outgoing edges
     * reaches a selected consumer occurrence.  The former alone is too coarse:
     * one region template may have many executions, and the old region/field
     * name scan scheduled every writer feeding any of them.  The latter keeps
     * this as an occurrence graph walk.</p>
     *
     * <p>The selected writer's demanded output inputs are appended to the same
     * producer frontier used by the ordinary backward walk.  A response that
     * supplied the writer can therefore select its remote producer, which may
     * in turn expose another admitted writer on the next iteration.  This is
     * the causal fixed point; there is no separate downstream traversal and no
     * global field-name closure.</p>
     */
    private void admitSharedStateStep(
            Target selectedTarget,
            Map<ProducerCandidate, Demand> selected,
            Map<String, Demand> admitted,
            CausalFrontier frontier,
            Map<Endpoint, ProducerCandidate> producerByEndpoint,
            Map<Endpoint, List<ProducerCandidate>> producersByDownstream)
            throws IOException {
        Set<String> selectedRegions = new LinkedHashSet<>();
        Set<String> selectedOccurrences = new LinkedHashSet<>();
        selectedRegions.add(selectedTarget.regionId);
        selectedOccurrences.add(selectedTarget.occurrenceId);
        for (Demand demand : selected.values()) {
            selectedRegions.add(demand.regionId);
            selectedOccurrences.add(
                    demand.exactProducerOccurrence().occurrenceId);
        }
        for (Demand demand : admitted.values()) {
            selectedRegions.add(demand.regionId);
            selectedOccurrences.add(demand.occurrenceId);
        }

        Set<Endpoint> alreadyAdmitted = new LinkedHashSet<>();
        for (Demand demand : admitted.values()) {
            alreadyAdmitted.addAll(demand.selectedEdges.keySet());
        }
        Set<RegionInstancePlan> relevantPlans = new LinkedHashSet<>();
        for (String consumer : selectedRegions) {
            relevantPlans.addAll(admittedPlansByConsumerRegion.getOrDefault(
                    consumer, Collections.emptyList()));
        }
        List<Demand> candidates = new ArrayList<>();
        for (RegionInstancePlan plan : relevantPlans) {
            if (selectedOccurrences.contains(plan.occurrenceId())
                    || admitted.containsKey(plan.occurrenceId())) {
                continue;
            }
            JsonObject row = plan.jsonView();
            Set<String> demandedBy = strings(array(row,
                    DEMANDED_BY_REGIONS));
            demandedBy.retainAll(selectedRegions);
            if (!SHARED_LOCATION_DEMAND.equals(
                    string(row, "admissionBasis"))
                    || demandedBy.isEmpty()) {
                continue;
            }
            Demand materialized = null;
            for (Goal goal : plan.goals()) {
                if (!goal.kind().capturesOutputRelation()
                        || !"READY".equals(goal.admissionState())
                        || goal.outputClosure() == null) {
                    continue;
                }
                ProducerCandidate producer = producerCandidate(
                        plan.occurrenceId(), goal);
                if (producer == null) continue;
                Demand candidate = Demand.materialization(producer,
                        selectedOccurrences, frontier);
                if (candidate == null) continue;
                if (materialized != null) {
                    throw new IOException("admitted occurrence has more than "
                            + "one executable output goal: "
                            + plan.occurrenceId());
                }
                materialized = candidate;
            }
            // This admission may feed another occurrence of an already
            // selected template.  It is not part of this exact closure.
            if (materialized == null) continue;
            requireReady(materialized);
            candidates.add(materialized);
        }

        // Admission exposes alternatives for an exact consumer input; it
        // does not require every observed writer occurrence.  Apply the same
        // canonical latest-writer choice as the ordinary producer index.
        Map<Endpoint, Demand> winnerByEndpoint = new LinkedHashMap<>();
        for (Demand candidate : candidates) {
            for (Map.Entry<Endpoint, JsonObject> edgeEntry
                    : candidate.selectedEdges.entrySet()) {
                Endpoint endpoint = edgeEntry.getKey();
                if (producerByEndpoint.containsKey(endpoint)
                        || alreadyAdmitted.contains(endpoint)) {
                    continue;
                }
                Demand prior = winnerByEndpoint.get(endpoint);
                if (prior == null || ProducerCandidate.compareEdges(
                        edgeEntry.getValue(),
                        prior.selectedEdges.get(endpoint)) < 0) {
                    winnerByEndpoint.put(endpoint, candidate);
                }
            }
        }
        Map<Demand, Set<Endpoint>> wonByDemand = new LinkedHashMap<>();
        for (Map.Entry<Endpoint, Demand> winner
                : winnerByEndpoint.entrySet()) {
            wonByDemand.computeIfAbsent(winner.getValue(),
                    ignored -> new LinkedHashSet<>()).add(winner.getKey());
        }
        for (Map.Entry<Demand, Set<Endpoint>> winner
                : wonByDemand.entrySet()) {
            Demand materialized = winner.getKey();
            materialized.retainSelectedEndpoints(winner.getValue());
            ProducerCandidate producer = producerCandidate(
                    materialized.occurrenceId, materialized.goal);
            if (producer == null) {
                throw new IOException("admitted writer has no indexed "
                        + "producer candidate: "
                        + materialized.occurrenceId);
            }
            for (Endpoint endpoint : winner.getValue()) {
                ProducerCandidate prior = producerByEndpoint.putIfAbsent(
                        endpoint, producer);
                if (prior != null && prior != producer) {
                    throw new IOException("exact admitted input already has "
                            + "a different producer: "
                            + endpoint.binding());
                }
            }
            Demand priorDemand = selected.putIfAbsent(producer,
                    materialized);
            if (priorDemand != null && priorDemand != materialized) {
                throw new IOException("admitted writer occurrence already "
                        + "has a different selected demand: "
                        + materialized.occurrenceId);
            }
            materialized.addMaterializationInputs(frontier,
                    producersByDownstream);
            admitted.put(materialized.occurrenceId, materialized);
        }
    }

    /** Exact bounded output case for one occurrence and goal. */
    private ProducerCandidate producerCandidate(
            String occurrenceId, Goal goal) {
        for (ProducerCandidate candidate
                : producerCandidatesByOccurrence.getOrDefault(occurrenceId,
                Collections.emptyList())) {
            if (candidate.goal == goal) return candidate;
        }
        return null;
    }

    private static void addStrings(Set<String> target, JsonArray values) {
        for (JsonElement value : values) {
            if (value.isJsonPrimitive()) {
                String text = value.getAsString();
                if (!text.isEmpty()) target.add(text);
            }
        }
    }

    private static Set<String> strings(JsonArray values) {
        Set<String> result = new LinkedHashSet<>();
        addStrings(result, values);
        return result;
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
                Endpoint endpoint = Endpoint.of(presentation.plan,
                        presentationInstance,
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
            Endpoint upstream = Endpoint.of(demand.plan, sourceInstance,
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
        return false;
    }

    /**
     * A concrete carrier does not normally extend the value frontier.  A
     * reference-valued shared field does, because the runtime edge names the
     * object that was actually read.  A transported structure does too, for
     * the reason stated on {@link #transportedValueFrontier}.
     */
    private static boolean exactTrustedCausalProducer(
            Endpoint endpoint,
            Map<Endpoint, List<ProducerCandidate>> producersByDownstream) {
        for (ProducerCandidate candidate
                : producersByDownstream.getOrDefault(endpoint,
                java.util.Collections.emptyList())) {
            for (JsonObject edge : candidate.edgesFor(endpoint)) {
                if (exactSharedStateConduit(edge)) return true;
                if (transportedValueFrontier(edge)) return true;
            }
        }
        return false;
    }

    /**
     * A concrete local structure may carry transported value leaves, but an
     * exact heap object identity alone is not a symbolic producer demand.
     */
    private static boolean exactTransportedValueProducer(
            Endpoint endpoint,
            Map<Endpoint, List<ProducerCandidate>> producersByDownstream) {
        for (ProducerCandidate candidate
                : producersByDownstream.getOrDefault(endpoint,
                java.util.Collections.emptyList())) {
            for (JsonObject edge : candidate.edgesFor(endpoint)) {
                if (transportedValueFrontier(edge)) return true;
            }
        }
        return false;
    }

    /**
     * Whether one incoming shared-state edge is an exact conduit its
     * consuming endpoint may follow to the occurrence that wrote it.
     *
     * <p>A shared carrier is exact when the runtime edge identifies the
     * object actually read.  The finalizer has already rejected historical
     * writes whose stored object differs, so following one does not reopen
     * an unconstrained whole-object dependency search.</p>
     *
     * <p>Both recorded read-from kinds qualify, and the pair is the point.
     * A writer that assigns the field states {@code
     * FIELD_ASSIGNMENT_READ_FROM}; a writer that <em>mutates</em> a
     * container states {@code CONTAINER_MUTATION_READ_FROM}, because
     * {@code map.put(..)} never assigns the field it changes.  Admitting
     * only the first therefore refuses the writer of every container - the
     * rotation that fills a map is exactly as much its producer as an
     * assignment would be, and it is the only kind of producer a container
     * can have.</p>
     *
     * <p>This is a sibling clause and not a widening: the evidence kind
     * chooses which branch of {@link
     * AutomaticRegionEdge#trustedRuntimeReadFromBinding} decides, and that
     * predicate still decides.  Its container branch is the stricter of the
     * two - beyond the assignment branch's identity and channel order it
     * also demands the mutating callee, a mutation invocation, and the
     * recorded field-read, enter and completion order that proves the
     * writer's container is the reader's - so nothing the assignment arm
     * guards against is admitted by adding the second name.</p>
     */
    private static boolean exactSharedStateConduit(JsonObject edge) {
        String evidence = string(edge, "evidenceKind");
        return "HEAP".equals(string(edge, "transportKind"))
                && (AutomaticRegionEdge.FIELD_ASSIGNMENT_READ_FROM
                .equals(evidence)
                || AutomaticRegionEdge.CONTAINER_MUTATION_READ_FROM
                .equals(evidence))
                && longInteger(edge, "valueObjectId", 0L) != 0L
                && AutomaticRegionEdge.trustedRuntimeReadFromBinding(edge);
    }

    /**
     * Whether one incoming protocol edge makes its consuming endpoint extend
     * the value frontier even though the consuming action is a concrete
     * structure carrier.
     *
     * <p>The carrier is concrete <em>as a value</em> -- a transported object
     * reference is not a value and symbolizing it would state nothing -- but
     * it is the transport for the leaves the demand actually reads, and
     * transport-for-value is a producer relationship.  Frontier membership
     * therefore consults the role the edge states, not only the mode of the
     * consuming action.  Reading the mode alone is what left an exporting
     * occurrence unscheduled while ten recorded deliveries named it.</p>
     *
     * <p>The edge may rest on concrete trace correlation at planning time.
     * That correlation schedules the interacting occurrences; it never
     * becomes a value equality.  The replay's VM handoff ledger is the sole
     * value-propagation authority consumed by composition.</p>
     */
    private static boolean transportedValueFrontier(JsonObject edge) {
        if (!DependencyRole.VALUE_FRONTIER.equals(
                DependencyRole.normalize(edge.get("dependencyRole")))) {
            return false;
        }
        if (AutomaticRegionEdge.RUNTIME_PROTOCOL_EDGE_KIND.equals(
                string(edge, "kind"))) {
            return AutomaticRegionEdge.schedulableProducerBinding(edge);
        }
        // A concrete heap reference extends the frontier only when the
        // finalizer names why: this exact stored object carried a configured
        // VM component received by the writer occurrence.  The edge still
        // has to pass the ordinary exact receiver/order evidence gate.
        return AutomaticRegionEdge.RUNTIME_EDGE_KIND.equals(
                string(edge, "kind"))
                && AutomaticRegionEdge
                .TRANSPORTED_VALUE_FRONTIER_AUTHORITY.equals(string(edge,
                AutomaticRegionEdge.TRANSPORTED_VALUE_FRONTIER_FIELD))
                && exactSharedStateConduit(edge);
    }

    /**
     * Whether a branch row states the outcome that reaches the failure.
     *
     * <p>The field is absent when neither successor is decisive, so presence
     * is the evidence and the value is not read here.</p>
     */
    private static boolean statesReachingOutcome(JsonObject branch) {
        JsonElement value = branch == null
                ? null : branch.get("requiredOutcome");
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean();
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

    /**
     * The target closures that remain candidates for target-first ranking.
     *
     * <p>Every occurrence that observed a failure-directed guard plans its
     * own target-reach closure.  Only one of them is stated over the decision
     * the target predicate actually names: the occurrence holding a site the
     * static slice recorded a reaching outcome for.  Narrowing to those is a
     * containment fact the plan row already carries, not a ranking preference
     * - an occurrence that names no such site is exactly the one the planner
     * blocks with {@code 0_ELIGIBLE_FAILURE_TARGETS}.</p>
     *
     * <p>When nothing names a site the whole candidate list is kept, so a plan
     * this rule cannot speak about is refused with the same evidence as
     * before rather than silently narrowed to nothing.</p>
     */
    private List<Target> admissibleTargets() {
        List<Target> naming = new ArrayList<>();
        for (Target candidate : targets) {
            if (candidate.namesFailureSite()) naming.add(candidate);
        }
        return naming.isEmpty() ? targets : naming;
    }

    private List<JsonObject> trustedEdges(RegionInstancePlan plan,
                                          Goal goal) {
        List<JsonObject> result = new ArrayList<>();
        OutputClosureContract closure = goal.outputClosure();
        if (closure != null) {
            Set<String> selectedIds = new LinkedHashSet<>();
            for (JsonElement element : goal.edgeBindingsView()) {
                if (!element.isJsonObject()) continue;
                JsonObject edge = element.getAsJsonObject();
                String fromRegion = string(edge, "fromRegion");
                String fromOccurrence = string(edge,
                        "fromOccurrenceId");
                boolean sameRegion = plan.regionId().equals(fromRegion)
                        && fromOccurrence.equals(plan.occurrenceId());
                if (!sameRegion || string(edge, "fromOutputPort").isEmpty()
                        || !schedulable(edge)) {
                    continue;
                }
                String id = string(edge, "edgeId");
                if (selectedIds.add(id)) result.add(edge);
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
        for (JsonElement item : goal.edgeBindingsView()) {
            if (item.isJsonObject()) {
                JsonObject edge = item.getAsJsonObject();
                if (producer.equals(string(edge, "fromOccurrenceId"))
                        && schedulable(edge)) {
                    result.add(edge);
                }
            }
        }
        return result;
    }

    /**
     * Whether one concrete interaction edge may schedule its producer.
     *
     * <p>An attested relation is admitted as it always was.  A recorded
     * delivery is admitted too, and its admission is written down: it is
     * scope and order - the exchange, the attempt and the two occurrences
     * the two hooks named - and never a value equality, so the only thing it
     * may buy is the right to run the exporting occurrence.  It
     * has to buy that, because the attestation that would upgrade it is
     * produced by running the slice, and refusing to schedule the producer
     * makes that attestation unreachable forever.</p>
     *
     * <p>Composition does not consume this planning correlation as a value
     * relation; it consumes only replay-produced VM handoff evidence.</p>
     */
    private boolean schedulable(JsonObject edge) {
        return AutomaticRegionEdge.schedulableProducerBinding(edge);
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

    private static ExecutionTask scheduledProducerTask(
            ProducerGroup group, List<ExecutionTask> tasks)
            throws IOException {
        List<ExecutionTask> matches = new ArrayList<>();
        Set<String> outputs = group.outputPorts();
        Set<String> edges = group.edgeIds();
        for (ExecutionTask task : tasks) {
            Set<String> taskOutputs = new LinkedHashSet<>();
            if (task.outputClosure() != null) {
                for (OutputClosureContract.Member member
                        : task.outputClosure().members()) {
                    taskOutputs.add(member.portId());
                }
            }
            if (group.regionId.equals(task.regionId())
                    && group.sourceKey.equals(task.sourceKey())
                    && group.relationKey.equals(task.relationKey())
                    && group.occurrenceId.equals(task.occurrenceId())
                    && group.goalId().equals(task.goalId())
                    && task.goalKind().capturesOutputRelation()
                    && task.outputClosure() != null
                    && taskOutputs.equals(outputs)
                    && task.executable()) {
                matches.add(task);
            }
        }
        ExecutionTask task = onlyTask(matches,
                "scheduled producer task; instance="
                        + group.occurrenceId + "; goal="
                        + group.goalId());
        Set<String> actualOutputs = new LinkedHashSet<>();
        for (OutputClosureContract.Member member
                : task.outputClosure().members()) {
            actualOutputs.add(member.portId());
        }
        if (!actualOutputs.containsAll(outputs)
                || !task.outputClosure().executionScope().inputPorts()
                .containsAll(group.inputPorts())) {
            throw new IOException("scheduled producer task closure "
                    + "does not contain selected grouped ports; instance="
                    + group.occurrenceId);
        }
        if (!taskEdgeIds(task).containsAll(edges)) {
            throw new IOException("scheduled producer task omits "
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
                && occurrence.occurrenceId.equals(task.occurrenceId());
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

    private static String campaignId(String regionId,
                                     String occurrenceId) {
        String region = safeToken(regionId);
        Matcher call = CALL_ID.matcher(occurrenceId);
        String invocation = call.find()
                ? "call" + call.group(1)
                : "instance-"
                + ArtifactIO.sha256(occurrenceId).substring(0, 8);
        String digest = ArtifactIO.sha256(occurrenceId).substring(0, 8);
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

    private static final class Demand {
        private final RegionInstancePlan plan;
        private final Goal goal;
        private final String campaignId;
        private final String regionId;
        private final String relationKey;
        private final String occurrenceId;
        private final String goalId;
        private final Occurrence occurrence;
        private final boolean materialization;
        private final Map<Endpoint, JsonObject> selectedEdges =
                new LinkedHashMap<>();
        private final Set<Endpoint> requiredInputEndpoints =
                new LinkedHashSet<>();
        private final Map<Endpoint, String> requiredInputEdgeIds =
                new LinkedHashMap<>();
        /**
         * Outputs added solely because the source declaration requires them.
         * They are replay phases, not extra boundaries that an already
         * selected producer case must answer atomically.
         */
        private final Set<String> sourceAugmentedOutputs =
                new LinkedHashSet<>();
        private ProducerOutputProjection projection;

        private Demand(RegionInstancePlan plan, Goal goal) {
            this(plan, goal, false);
        }

        private Demand(RegionInstancePlan plan, Goal goal,
                       Occurrence occurrence) {
            this(plan, goal, false, occurrence);
        }

        private Demand(RegionInstancePlan plan, Goal goal,
                       boolean materialization) {
            this(plan, goal, materialization, new Occurrence(goal));
        }

        private Demand(RegionInstancePlan plan, Goal goal,
                       boolean materialization,
                       Occurrence occurrence) {
            this.plan = plan;
            this.goal = goal;
            this.materialization = materialization;
            regionId = plan.regionId();
            relationKey = plan.relationKey();
            occurrenceId = goal.plan().occurrenceId();
            goalId = goal.goalId();
            // One coarse occurrence can contribute several bounded output
            // cases.  They share the Java activation identity but replay as
            // distinct selected phases, so the campaign key includes the
            // exact goal instead of falsely requiring one producer case per
            // occurrence.
            campaignId = campaignId(regionId, occurrenceId) + "-goal-"
                    + ArtifactIO.sha256(goalId).substring(0, 8);
            this.occurrence = occurrence;
        }

        /** One exact occurrence retained only to expose a selected interaction. */
        private static Demand materialization(
                ProducerCandidate producer,
                Set<String> selectedConsumerOccurrences,
                CausalFrontier relevantInputs) throws IOException {
            RegionInstancePlan plan = producer.plan;
            Goal goal = producer.goal;
            Demand demand = new Demand(plan, goal, true,
                    producer.occurrence);
            for (Map.Entry<Endpoint, List<JsonObject>> candidate
                    : producer.edgesByDownstream.entrySet()) {
                Endpoint endpoint = candidate.getKey();
                if (!selectedConsumerOccurrences.contains(endpoint.instance)
                        || !relevantInputs.contains(endpoint)
                        || candidate.getValue().isEmpty()) {
                    continue;
                }
                // ProducerCandidate already sorted this exact endpoint by
                // latest writerEventSeq and stable edge identity.
                JsonObject edge = null;
                for (JsonObject alternative : candidate.getValue()) {
                    if (relevantInputs.allows(endpoint,
                            string(alternative, "edgeId"))) {
                        edge = alternative;
                        break;
                    }
                }
                if (edge == null) continue;
                String output = required(edge, "fromOutputPort");
                if (goal.outputClosure().member(output) == null) {
                    throw new IOException("materialized interaction edge has "
                            + "no output member: " + required(edge, "edgeId"));
                }
                JsonObject prior = demand.selectedEdges.get(endpoint);
                if (prior == null || ProducerCandidate.compareEdges(
                        edge, prior) < 0) {
                    // Repeated executions may publish several observed
                    // versions from one writer occurrence to the same exact
                    // consumer input.  The ordinary producer index already
                    // chooses the latest writerEventSeq deterministically;
                    // admission uses that same canonical choice instead of
                    // treating replay multiplicity as a contradiction.
                    demand.selectedEdges.put(endpoint, edge);
                }
            }
            return demand.selectedEdges.isEmpty() ? null : demand;
        }

        private void addRequiredInputs(Set<Endpoint> endpoints,
                                       ProducerCandidate candidate,
                                       CausalFrontier frontier,
                                       Map<Endpoint, List<ProducerCandidate>>
                                               producersByDownstream)
                throws IOException {
            if (goal.outputClosure() == null) return;
            for (Endpoint target : endpoints) {
                JsonObject edge = candidate.edgeFor(target, occurrence,
                        frontier.allowedEdges(target));
                JsonObject prior = selectedEdges.putIfAbsent(target, edge);
                if (prior != null && !required(prior, "edgeId").equals(
                        required(edge, "edgeId"))) {
                    throw new IOException("exact downstream input selected "
                            + "more than one output: " + target.binding());
                }
            }
            addSelectedMemberInputs(frontier, producersByDownstream);
        }

        /** Extends the common frontier from this demand's exact outputs. */
        private void addMaterializationInputs(
                CausalFrontier frontier,
                Map<Endpoint, List<ProducerCandidate>> producersByDownstream)
                throws IOException {
            addSelectedMemberInputs(frontier, producersByDownstream);
        }

        private void retainSelectedEndpoints(Set<Endpoint> retained) {
            selectedEdges.keySet().retainAll(retained);
        }

        private void addSelectedMemberInputs(
                CausalFrontier frontier,
                Map<Endpoint, List<ProducerCandidate>> producersByDownstream)
                throws IOException {
            for (JsonObject edge : selectedEdges.values()) {
                String sourceInstance = required(edge, "fromOccurrenceId");
                Occurrence selected = requireOccurrence(sourceInstance);
                OutputClosureContract.Member member = member(edge,
                        selected);
                addMemberInputs(sourceInstance, selected, member, frontier,
                        producersByDownstream);
            }
        }

        /**
         * Adds configured-source output members before the predecessor walk
         * closes.  Their exact inputs then participate in the same fixed
         * point as ordinary RPC/shared-state members, so a selector CONSUME
         * cannot be scheduled without its prior PUBLISH producer.
         */
        private boolean includeSourceOutputInputs(
                SourceOutputSelection selection,
                CausalFrontier frontier,
                Map<Endpoint, List<ProducerCandidate>> producersByDownstream)
                throws IOException {
            if (goal.outputClosure() == null) return false;
            Set<String> configuredCells = selection.selected(regionId,
                    goal.outputClosure());
            if (configuredCells == null || configuredCells.isEmpty()) {
                return false;
            }
            Set<String> alreadySelectedCells = new LinkedHashSet<>();
            for (JsonObject edge : selectedEdges.values()) {
                Occurrence exact = requireOccurrence(required(edge,
                        "fromOccurrenceId"));
                alreadySelectedCells.add(member(edge, exact).cell());
            }
            boolean changed = false;
            for (String cell : configuredCells) {
                if (alreadySelectedCells.contains(cell)) continue;
                List<OutputClosureContract.Member> matches =
                        new ArrayList<>();
                for (OutputClosureContract.Member member
                        : goal.outputClosure().members()) {
                    if (cell.equals(member.cell())) matches.add(member);
                }
                if (matches.size() != 1) {
                    throw new IOException("configured symbolic source output "
                            + "is not unique in selected producer closure: "
                            + cell + " -> " + matches.size());
                }
                OutputClosureContract.Member member = matches.get(0);
                if (!sourceAugmentedOutputs.add(member.portId())) continue;
                addMemberInputs(occurrenceId, occurrence, member, frontier,
                        producersByDownstream);
                changed = true;
            }
            return changed;
        }

        private void addMemberInputs(
                String sourceInstance, Occurrence selected,
                OutputClosureContract.Member member,
                CausalFrontier frontier,
                Map<Endpoint, List<ProducerCandidate>> producersByDownstream)
                throws IOException {
            Set<String> unmaterializable = new LinkedHashSet<>();
            for (JsonElement input : member.slice()
                    .getAsJsonArray("inputPorts")) {
                String port = input.getAsString();
                Endpoint endpoint = Endpoint.of(plan, sourceInstance,
                        selected.exactInput(port));
                JsonObject action = dependencyAction(goal, port);
                if (action != null) {
                    if (causalAction(action)
                            || exactTransportedValueProducer(endpoint,
                            producersByDownstream)) {
                        requiredInputEndpoints.add(endpoint);
                        frontier.addFromMember(endpoint, member,
                                producersByDownstream);
                    }
                    continue;
                }
                // A cut input can have no local action yet still have an
                // exact remote producer. Follow that evidence before the
                // declared-cut exemption.
                if (exactTrustedCausalProducer(endpoint,
                        producersByDownstream)) {
                    requiredInputEndpoints.add(endpoint);
                    frontier.addFromMember(endpoint, member,
                            producersByDownstream);
                    continue;
                }
                if (CommunicationCatalogContract.declaredPortId(port)) {
                    continue;
                }
                unmaterializable.add(port);
            }
            if (!unmaterializable.isEmpty()) {
                throw new IOException(
                        OUTPUT_SLICE_INPUT_UNMATERIALIZABLE + ": output="
                                + member.portId() + "; inputs="
                                + unmaterializable + "; " + context());
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
                if (edge != null) {
                    String edgeId = required(edge, "edgeId");
                    edgeIds.add(edgeId);
                    requiredInputEdgeIds.put(input, edgeId);
                }
            }
            // A coarse occurrence that reaches a declared communication cut
            // retains that cut as one of its own effects even when the edge
            // which selected the occurrence consumed a heap output.  The
            // declaration is bounded to this region and its member carries
            // the exact causal edges, so this adds neither another occurrence
            // nor a call-graph search.
            for (String output
                    : goal.outputClosure().producer().declaredOutputPorts()) {
                OutputClosureContract.Member member =
                        goal.outputClosure().member(output);
                if (member == null) {
                    // The template declares every possible cut site, while
                    // one concrete occurrence materializes only the sites its
                    // path reached.  Absence is therefore an unobserved
                    // interaction alternative, not a malformed occurrence.
                    continue;
                }
                outputs.add(output);
                addStrings(edgeIds,
                        array(member.slice(), "causalEdgeIds"));
            }
            for (String output : sourceAugmentedOutputs) {
                OutputClosureContract.Member member =
                        goal.outputClosure().member(output);
                if (member == null) {
                    throw new IOException("configured source output has no "
                            + "closure member: " + output);
                }
                outputs.add(output);
                addStrings(edgeIds, array(member.slice(), "causalEdgeIds"));
            }
            projection = ProducerOutputProjection.create(campaignId,
                    regionId, relationKey, goalId, outputs,
                    edgeIds);
        }

        private ProducerOutputProjection projection() throws IOException {
            if (projection == null) {
                throw new IOException("producer demand has no finalized "
                        + "exact-output projection; " + context());
            }
            return projection;
        }

        /**
         * Splits one selected coarse occurrence when its selected members
         * state different exact replay continuations.  A configured source
         * output added after target ranking is also its own phase: requiring
         * the pre-existing output and a different dynamic output selector in
         * one ActiveRegion made each individually observable boundary look
         * incomplete.  The source id remains stable across those phase tasks,
         * so this split does not mint a second symbolic source.
         */
        private List<ProducerOutputProjection> phaseProjections()
                throws IOException {
            ProducerOutputProjection selected = projection();
            Map<String, Set<String>> portsByEntry = new java.util.TreeMap<>();
            Map<String, Set<String>> inputsByEntry = new LinkedHashMap<>();
            for (String port : selected.outputPorts()) {
                OutputClosureContract.Member member =
                        goal.outputClosure().member(port);
                if (member == null) {
                    throw new IOException("selected producer output has no "
                            + "closure member: " + port);
                }
                String key = replayEntryKey(member);
                if (sourceAugmentedOutputs.contains(port)) {
                    key += "\nCONFIGURED_SOURCE_OUTPUT\n" + port;
                }
                portsByEntry.computeIfAbsent(key,
                        ignored -> new LinkedHashSet<>()).add(port);
                Set<String> inputs = inputsByEntry.computeIfAbsent(key,
                        ignored -> new LinkedHashSet<>());
                for (JsonElement input : array(member.slice(),
                        "inputPorts")) {
                    if (input.isJsonPrimitive()) {
                        inputs.add(input.getAsString());
                    }
                }
            }
            if (portsByEntry.size() == 1) {
                return Collections.singletonList(selected);
            }

            List<ProducerOutputProjection> result = new ArrayList<>();
            for (Map.Entry<String, Set<String>> phase
                    : portsByEntry.entrySet()) {
                Set<String> phaseEdges = new LinkedHashSet<>();
                for (String port : phase.getValue()) {
                    OutputClosureContract.Member member =
                            goal.outputClosure().member(port);
                    addStrings(phaseEdges,
                            array(member.slice(), "causalEdgeIds"));
                    for (JsonObject edge : selectedEdges.values()) {
                        if (port.equals(string(edge, "fromOutputPort"))) {
                            phaseEdges.add(required(edge, "edgeId"));
                        }
                    }
                }
                Set<String> phaseInputs = inputsByEntry.get(phase.getKey());
                for (Map.Entry<Endpoint, String> input
                        : requiredInputEdgeIds.entrySet()) {
                    if (occurrenceId.equals(input.getKey().instance)
                            && phaseInputs.contains(input.getKey().input)) {
                        phaseEdges.add(input.getValue());
                    }
                }
                phaseEdges.retainAll(selected.edgeIds());
                if (phaseEdges.isEmpty()) {
                    throw new IOException("selected producer replay phase "
                            + "has no exact causal edge; outputs="
                            + phase.getValue());
                }
                String phaseCampaign = campaignId + "-phase-"
                        + ArtifactIO.sha256(phase.getKey() + "\n"
                        + String.join("\n", phase.getValue()))
                        .substring(0, 8);
                result.add(ProducerOutputProjection.create(phaseCampaign,
                        regionId, relationKey, goalId,
                        phase.getValue(), phaseEdges));
            }
            return result;
        }

        private String replayEntryKey(
                OutputClosureContract.Member member) throws IOException {
            JsonElement encoded = member.slice().get(
                    ExecutionTask.REPLAY_ENTRY);
            if (encoded == null || encoded.isJsonNull()) {
                return "ROOT";
            }
            if (!encoded.isJsonObject()) {
                throw new IOException("selected producer replay entry is not "
                        + "an object: " + member.portId());
            }
            JsonObject entry = encoded.getAsJsonObject();
            if (string(entry, "method").isEmpty()
                    || string(entry, "receiverClass").isEmpty()) {
                throw new IOException("selected producer replay entry is "
                        + "incomplete: " + member.portId());
            }
            return CanonicalJson.render(entry);
        }

        private Set<String> projectedInputPorts(
                Set<String> selectedOutputs) throws IOException {
            OutputClosureContract closure = goal.outputClosure();
            if (closure == null) return Collections.emptySet();
            Set<String> result = new LinkedHashSet<>();
            for (String output : selectedOutputs) {
                OutputClosureContract.Member member = closure.member(output);
                if (member == null) {
                    throw new IOException("selected interaction output has "
                            + "no closure member: " + output);
                }
                for (JsonElement input : array(member.slice(),
                        "inputPorts")) {
                    if (input.isJsonPrimitive()) {
                        result.add(input.getAsString());
                    }
                }
            }
            return result;
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
                Set<Endpoint> endpoints, ProducerCandidate candidate,
                CausalFrontier frontier)
                throws IOException {
            Set<String> result = new LinkedHashSet<>();
            for (Endpoint endpoint : endpoints) {
                JsonObject edge = candidate.edgeFor(endpoint, occurrence,
                        frontier.allowedEdges(endpoint));
                Occurrence selected = requireOccurrence(
                        required(edge, "fromOccurrenceId"));
                result.add(member(edge, selected).portId());
            }
            return result;
        }

        private Set<String> demandedInputs(Set<Endpoint> endpoints,
                                           ProducerCandidate candidate,
                                           CausalFrontier frontier)
                throws IOException {
            Set<String> result = new LinkedHashSet<>();
            for (Endpoint endpoint : endpoints) {
                JsonObject edge = candidate.edgeFor(endpoint, occurrence,
                        frontier.allowedEdges(endpoint));
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
            if (materialization) {
                for (String output : projection().outputPorts()) {
                    OutputClosureContract.Member member =
                            goal.outputClosure().member(output);
                    if (member == null) {
                        throw new IOException("materialized output has no "
                                + "closure member: " + output);
                    }
                    for (JsonElement input : member.slice()
                            .getAsJsonArray("inputPorts")) {
                        result.add(input.getAsString());
                    }
                }
                return result;
            }
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
            if (materialization) return occurrence;
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
                for (JsonElement element : goal.branchesView()) {
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
                    result.add(relationKey + "\n" + goalId + "\n" + site);
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

        /**
         * The one action this goal declares for an output-slice input, or
         * {@code null} when it declares none.
         *
         * <p>Absence is not decided here.  A port with no action may still be
         * discharged by a scheduled producer or be a declared cut port whose
         * value crossed the cut, and only the caller sees both; what stays
         * fatal in every shape is <em>two</em> actions for one port, because
         * neither a cut nor a producer can explain a fragment binding one
         * input twice.</p>
         */
        private static JsonObject dependencyAction(Goal goal, String port)
                throws IOException {
            JsonObject selected = null;
            for (JsonElement element : goal.symbolizeView()) {
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
            return selected;
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
     * The exact consumer inputs still requiring producers, together with any
     * causal-edge identity already selected by the output member that exposed
     * each input.
     *
     * <p>The occurrence and port remain the endpoint identity.  Edge ids are
     * a restriction on the admissible producer for that endpoint, not another
     * endpoint dimension: several observed deliveries may reach one port, but
     * once a concrete output member records which delivery preceded its
     * value, scheduling must not silently replace it with an older delivery
     * that happens to share the same port.</p>
     */
    private static final class CausalFrontier {
        private final Set<Endpoint> endpoints = new LinkedHashSet<>();
        private final Map<Endpoint, Set<String>> allowedEdges =
                new LinkedHashMap<>();

        private CausalFrontier(Set<Endpoint> initial) {
            endpoints.addAll(initial);
        }

        private Set<Endpoint> endpoints() {
            return Collections.unmodifiableSet(endpoints);
        }

        private boolean contains(Endpoint endpoint) {
            return endpoints.contains(endpoint);
        }

        private Set<String> allowedEdges(Endpoint endpoint) {
            return allowedEdges.getOrDefault(endpoint,
                    Collections.emptySet());
        }

        private boolean allows(Endpoint endpoint, String edgeId) {
            Set<String> allowed = allowedEdges(endpoint);
            return allowed.isEmpty() || allowed.contains(edgeId);
        }

        private void constrain(Endpoint endpoint, Set<String> edgeIds)
                throws IOException {
            if (edgeIds == null || edgeIds.isEmpty()) return;
            endpoints.add(endpoint);
            Set<String> held = allowedEdges.get(endpoint);
            if (held == null) {
                allowedEdges.put(endpoint,
                        new LinkedHashSet<>(edgeIds));
                return;
            }
            Set<String> intersection = new LinkedHashSet<>(held);
            intersection.retainAll(edgeIds);
            if (intersection.isEmpty()) {
                throw new IOException("selected output members disagree on "
                        + "the causal producer for " + endpoint.binding()
                        + "; first=" + held + "; next=" + edgeIds);
            }
            allowedEdges.put(endpoint, intersection);
        }

        private void addFromMember(
                Endpoint endpoint, OutputClosureContract.Member member,
                Map<Endpoint, List<ProducerCandidate>> producersByDownstream)
                throws IOException {
            endpoints.add(endpoint);
            Set<String> memberEdges = new LinkedHashSet<>();
            addStrings(memberEdges,
                    array(member.slice(), "causalEdgeIds"));
            if (memberEdges.isEmpty()) return;

            Set<String> matching = new LinkedHashSet<>();
            for (ProducerCandidate candidate
                    : producersByDownstream.getOrDefault(endpoint,
                    Collections.emptyList())) {
                for (JsonObject edge : candidate.edgesFor(endpoint)) {
                    String edgeId = string(edge, "edgeId");
                    if (memberEdges.contains(edgeId)) matching.add(edgeId);
                }
            }
            if (!matching.isEmpty()) constrain(endpoint, matching);
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
        private final Occurrence occurrence;
        private final Map<Endpoint, List<JsonObject>> edgesByDownstream =
                new LinkedHashMap<>();
        private final Set<Endpoint> downstreamEndpoints =
                new LinkedHashSet<>();

        private ProducerCandidate(RegionInstancePlan plan, Goal goal,
                                  List<JsonObject> edges) {
            this.plan = plan;
            this.goal = goal;
            this.occurrence = new Occurrence(goal);
            for (JsonObject edge : edges) {
                String instance = string(edge, "toOccurrenceId");
                String input = string(edge, "toInputPort");
                if (!instance.isEmpty() && !input.isEmpty()) {
                    Endpoint endpoint = Endpoint.consumerOf(edge);
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
            return new Demand(plan, goal, occurrence);
        }

        private JsonObject edgeFor(Endpoint endpoint,
                                   Occurrence occurrence,
                                   Set<String> allowedEdgeIds)
                throws IOException {
            List<JsonObject> edges = edgesByDownstream.get(endpoint);
            if (edges == null || edges.isEmpty()) {
                throw new IOException("producer candidate has no edge for "
                        + endpoint.binding());
            }
            for (JsonObject edge : edges) {
                if (occurrence.occurrenceId.equals(string(edge,
                        "fromOccurrenceId"))
                        && (allowedEdgeIds.isEmpty()
                        || allowedEdgeIds.contains(string(edge,
                        "edgeId")))) {
                    return edge;
                }
            }
            throw new IOException("producer path seed has no exact "
                    + "occurrence for " + endpoint.binding());
        }

        private boolean covers(Endpoint endpoint,
                               Occurrence occurrence,
                               Set<String> allowedEdgeIds) {
            for (JsonObject edge : edgesByDownstream.getOrDefault(endpoint,
                    java.util.Collections.emptyList())) {
                if (occurrence.occurrenceId.equals(string(edge,
                        "fromOccurrenceId"))
                        && (allowedEdgeIds.isEmpty()
                        || allowedEdgeIds.contains(string(edge,
                        "edgeId")))) {
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
                               CausalFrontier frontier,
                               boolean alreadySelected) throws IOException {
            this.candidate = candidate;
            this.demand = demand;
            this.alreadySelected = alreadySelected;
            for (Endpoint endpoint : candidate.downstreamEndpoints) {
                if (unresolved.contains(endpoint)
                        && candidate.covers(endpoint,
                        demand.occurrence,
                        frontier.allowedEdges(endpoint))) {
                    coveredEndpoints.add(endpoint);
                }
            }
            Set<String> selectedOutputs = demand.demandedCanonicalOutputs(
                    coveredEndpoints, candidate, frontier);
            Set<String> selectedInputs = demand.demandedInputs(
                    coveredEndpoints, candidate, frontier);
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
        private final int valueBackedFatalInputs;
        private final int stateBackedFatalInputs;
        private final int observedSelectedSemanticGuards;

        private DemandClosure(List<Demand> demands,
                              Set<String> exactBindings,
                              Set<String> causalRegions, int fatalInputs,
                              int residualFatalInputs,
                              boolean exactDirectPresentation,
                              boolean propagatedBoundedStateTransition,
                              int valueBackedFatalInputs,
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
            this.valueBackedFatalInputs = valueBackedFatalInputs;
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
            List<ProducerGroup> grouped = new ArrayList<>();
            Set<String> targetEdgeIds = new LinkedHashSet<>();
            for (Demand producer : producers) {
                for (JsonObject edge : producer.selectedEdges.values()) {
                    if (target.occurrenceId.equals(string(edge,
                            "toOccurrenceId"))) {
                        targetEdgeIds.add(required(edge, "edgeId"));
                    }
                }
                for (ProducerOutputProjection phase
                        : producer.phaseProjections()) {
                    Selection selection = Selection.producer(
                            producer, phase);
                    materialized.add(selection);
                    grouped.add(new ProducerGroup(producer, selection));
                }
            }
            materialized.add(0, Selection.target(target, targetEdgeIds));
            selections = java.util.Collections.unmodifiableList(materialized);
            producerGroups = java.util.Collections.unmodifiableList(
                    grouped);
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

    /** One selected producer occurrence and all failure-relevant effects. */
    static final class ProducerGroup {
        final String regionId;
        final String sourceKey;
        final String relationKey;
        final String occurrenceId;
        final Demand demand;
        final Selection selection;

        private ProducerGroup(Demand first, Selection selection)
                throws IOException {
            Occurrence exact = first.exactProducerOccurrence();
            regionId = first.regionId;
            sourceKey = first.plan.sourceKey();
            relationKey = first.plan.relationKey();
            occurrenceId = exact.occurrenceId;
            demand = first;
            this.selection = selection;
        }

        Set<String> outputPorts() throws IOException {
            return new LinkedHashSet<>(
                    selection.producerProjection.outputPorts());
        }

        Set<String> edgeIds() throws IOException {
            return new LinkedHashSet<>(
                    selection.producerProjection.edgeIds());
        }

        Set<String> inputPorts() throws IOException {
            return demand.projectedInputPorts(outputPorts());
        }

        String campaignId() throws IOException {
            return selection.campaignId;
        }

        String goalId() throws IOException {
            return demand.goalId;
        }

        JsonObject indexEntry(String taskId) throws IOException {
            JsonObject result = new JsonObject();
            result.addProperty("campaignId", campaignId());
            result.addProperty("regionId", regionId);
            result.addProperty("relationKey", relationKey);
            result.addProperty("occurrenceId", occurrenceId);
            result.addProperty("goalId", goalId());
            result.addProperty("taskId", taskId);
            JsonArray outputs = new JsonArray();
            for (String output : outputPorts()) outputs.add(output);
            result.add("outputPorts", outputs);
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

        private static Selection producer(
                Demand producer, ProducerOutputProjection projection)
                throws IOException {
            JsonObject canonicalProjection =
                    com.google.gson.JsonParser.parseString(
                            CanonicalJson.render(projection
                                    .json())).getAsJsonObject();
            return new Selection(projection.campaignId(), producer.regionId,
                    producer.occurrenceId, producer.goalId,
                    ProducerOutputProjection.decode(canonicalProjection),
                    Collections.<String>emptySet());
        }

    }

    /**
     * One exact input of one selected region occurrence.
     *
     * <p>A port belongs to a region occurrence rather than to an activation:
     * two deliveries into two occurrences of one handler are two endpoints,
     * which is precisely the equal-payload case that must stay separated,
     * since nothing else about those two messages differs.</p>
     */
    private static final class Endpoint {
        private final String instance;
        private final String input;

        private Endpoint(String instance, String input) {
            this.instance = instance == null ? "" : instance.trim();
            this.input = input == null ? "" : input.trim();
        }

        /** The endpoint one plan row's own occurrence owns. */
        private static Endpoint of(RegionInstancePlan plan, String instance,
                                   String input) {
            return new Endpoint(instance, input);
        }

        /** The consuming endpoint one runtime edge names for itself. */
        private static Endpoint consumerOf(JsonObject edge) {
            return new Endpoint(string(edge, "toOccurrenceId"),
                    string(edge, "toInputPort"));
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof Endpoint)) return false;
            Endpoint value = (Endpoint) other;
            return instance.equals(value.instance)
                    && input.equals(value.input);
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
            campaignId = campaignId(regionId, occurrenceId);
        }

        private String exactInput(String canonical) throws IOException {
            return occurrence.exactInput(canonical);
        }

        /**
         * Whether the target predicate's decision site lies in this
         * occurrence.
         *
         * <p>A branch row qualifies when this occurrence observed it, it is not
         * a loop control, and the static slice recorded which of its outcomes
         * reaches the failure.  That last part is the containment evidence:
         * a reaching outcome only exists for a branch the failure site is
         * control-dependent on, so a fragment that carries one holds the site
         * the predicate is stated over and a fragment that carries none does
         * not.  Presence of {@code requiredOutcome} is what is read, never its
         * value - {@code false} is an ordinary reaching outcome.</p>
         */
        private boolean namesFailureSite() {
            for (JsonElement element : goal.branchesView()) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (bool(branch, "failureTarget", false)
                        && !bool(branch, "loopControlGuard", false)
                        && bool(branch, "observed", false)
                        && statesReachingOutcome(branch)
                        && !string(branch, "siteId").isEmpty()) {
                    return true;
                }
            }
            return false;
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
            compared = left.goalId.compareTo(right.goalId);
            if (compared != 0) return compared;
            return left.occurrenceId.compareTo(right.occurrenceId);
        }
    }

    private static final class TargetRank {
        private final boolean valid;
        private final boolean exactDirectPresentation;
        private final boolean propagatedBoundedStateTransition;
        private final int valueBackedFatalInputs;
        private final int stateBackedFatalInputs;
        private final int observedSelectedSemanticGuards;
        private final int residualFatalInputs;
        private final int fatalInputs;
        private final int producerGoals;
        private final int exactBindings;
        private final int causalRegions;

        private TargetRank(boolean valid, boolean exactDirectPresentation,
                           boolean propagatedBoundedStateTransition,
                           int valueBackedFatalInputs,
                           int stateBackedFatalInputs,
                           int observedSelectedSemanticGuards,
                           int residualFatalInputs,
                           int fatalInputs, int producerGoals,
                           int exactBindings, int causalRegions) {
            this.valid = valid;
            this.exactDirectPresentation = exactDirectPresentation;
            this.propagatedBoundedStateTransition =
                    propagatedBoundedStateTransition;
            this.valueBackedFatalInputs = valueBackedFatalInputs;
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
                    closure.valueBackedFatalInputs,
                    closure.stateBackedFatalInputs,
                    closure.observedSelectedSemanticGuards,
                    closure.residualFatalInputs,
                    closure.fatalInputs, closure.demands.size(),
                    closure.exactBindings.size(),
                    closure.causalRegions.size());
        }

        private static TargetRank invalid() {
            return new TargetRank(false, false, false, 0, 0, 0,
                    Integer.MAX_VALUE,
                    Integer.MAX_VALUE, Integer.MAX_VALUE,
                    Integer.MAX_VALUE, Integer.MAX_VALUE);
        }

        private static int compare(TargetRank left, TargetRank right) {
            int compared = Boolean.compare(right.valid, left.valid);
            if (compared != 0) return compared;
            // Prefer an occurrence where a failure-relevant protocol input
            // is presented by one exact schedulable cross-boundary edge.  A
            // same-process forwarding occurrence can have a much smaller
            // static slice while omitting the value that the remote peer
            // actually supplied.  An observed exchange may rank the seed
            // campaign before a VM handoff edge exists; the SMT admission gate
            // remains stricter.  This is trace/schema evidence, never an
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
            // Concrete receiver/container identity can identify a baseline
            // read-from arm but cannot stand in for symbolic value ancestry.
            // Prefer the target occurrence whose fatal operands are carried
            // by actual value-frontier relations before comparing replay
            // cost or the amount of surrounding state evidence.
            compared = Integer.compare(right.valueBackedFatalInputs,
                    left.valueBackedFatalInputs);
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
            for (JsonElement element : goal.edgeBindingsView()) {
                if (element.isJsonObject()) {
                    String id = string(element.getAsJsonObject(), "edgeId");
                    if (!id.isEmpty()) ids.add(id);
                }
            }
            bindingIds = Collections.unmodifiableSet(ids);
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
