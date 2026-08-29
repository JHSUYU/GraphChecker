package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
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
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;

/** Discovers the producer and target campaigns in one runtime region plan. */
public final class RuntimeWorkflowDiscovery {
    private static final String SHARED_LOCATION_DEMAND =
            "SHARED_LOCATION_DEMAND_V1";
    private static final String BOUNDED_VERSION_SCOPES =
            "boundedVersionScopes";
    private static final Pattern CALL_ID = Pattern.compile(
            "(?:^|[#@])call([0-9]+)(?:$|[^0-9])");

    /** An input of a demanded output slice that nothing can materialize. */
    static final String OUTPUT_SLICE_INPUT_UNMATERIALIZABLE =
            "RUNTIME_OUTPUT_SLICE_INPUT_UNMATERIALIZABLE";

    private final List<RegionInstancePlan> plans = new ArrayList<>();
    private final Map<String, List<RegionInstancePlan>>
            admittedPlansByConsumerRegion = new LinkedHashMap<>();
    private final Map<Endpoint, List<ProducerCandidate>>
            producersByDownstream = new LinkedHashMap<>();
    /** One coarse occurrence, one producer candidate (README REGION-1). */
    private final Map<String, ProducerCandidate>
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
            List<RegionInstancePlan> regionPlan,
            FailureInputSelection failureInputSelection)
            throws IOException {
        if (failureInputSelection == null) {
            throw new IllegalArgumentException(
                    "failure input selection is required");
        }
        this.failureInputSelection = failureInputSelection;
        // A region is coarse: one selected execution-context entry and the
        // selected nested calls executed in it.  The plan artifact decoded
        // these rows and owns their occurrence uniqueness; the relation key is
        // deliberately not unique, since a worker whose activation ran three
        // times contributes three rows sharing one.
        plans.addAll(regionPlan);
        if (plans.isEmpty()) {
            throw new IOException("runtime region plan is empty");
        }
        for (RegionInstancePlan plan : plans) {
            for (String consumer : sharedLocationConsumers(plan)) {
                admittedPlansByConsumerRegion.computeIfAbsent(consumer,
                        ignored -> new ArrayList<>()).add(plan);
            }
        }
        indexProducerCandidates();
        targets = discoverTargets();
    }

    /** The consumer regions one plan was admitted to serve, empty unless its
     * admission basis is the shared-location demand. */
    private static Set<String> sharedLocationConsumers(
            RegionInstancePlan plan) {
        return SHARED_LOCATION_DEMAND.equals(plan.admissionBasis())
                ? plan.demandedByRegionIds()
                : Collections.<String>emptySet();
    }

    /** Builds the immutable exact producer index once for all target ranks.
     *
     * <p>README REGION-1: one local occurrence is one coarse producer, so it
     * contributes exactly one candidate.</p> */
    private void indexProducerCandidates() throws IOException {
        for (RegionInstancePlan plan : plans) {
            for (Goal goal : plan.goals()) {
                if (!goal.kind().capturesOutputRelation()) continue;
                List<JsonObject> edges = trustedEdges(plan, goal);
                edges.removeIf(edge -> !causallyEligibleSourceEdge(
                        plan, goal, edge));
                if (edges.isEmpty()) continue;
                ProducerCandidate candidate =
                        new ProducerCandidate(plan, goal, edges);
                ProducerCandidate prior =
                        producerCandidatesByOccurrence.putIfAbsent(
                                plan.occurrenceId(), candidate);
                if (prior != null) {
                    throw new IOException("region occurrence has more than "
                            + "one output producer goal: "
                            + plan.occurrenceId());
                }
                for (Endpoint downstream : candidate.downstreamEndpoints) {
                    producersByDownstream.computeIfAbsent(downstream,
                            ignored -> new ArrayList<>()).add(candidate);
                }
            }
        }
    }

    /** Materializes the ranked target-first workflow from the region plan the
     * artifact decoded once. */
    static RankedWorkflow rankedWorkflow(
            List<RegionInstancePlan> regionPlan,
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
        // Source-owned output members extend a candidate's predecessor
        // frontier, so they are part of target ranking rather than a
        // projection detail added after a target has already won.  Ranking
        // with the empty selector first can choose a target which precedes
        // the configured source and can therefore only close through an
        // older presentation of the same protocol value.
        List<Target> candidates = new ArrayList<>(
                discovery.admissibleTargets());
        for (Target candidate : candidates) {
            try {
                candidate.rank = discovery.discoverDemandClosure(candidate,
                        sourceOutputSelection);
            } catch (IOException invalidClosure) {
                candidate.rank = TargetRank.invalid();
            }
        }
        candidates.sort(Target::compare);
        Target selected = candidates.get(0);
        if (!selected.goal.replayable()) {
            throw new IOException("ranked target goal is not replayable; "
                    + selected.context());
        }
        List<Demand> producers = discovery.discoverDemands(selected,
                sourceOutputSelection);
        return new RankedWorkflow(selected, producers);
    }

    /** Selects one READY producer alternative for each exact downstream input
     * in the reverse runtime read-from closure rooted at the target. */
    private List<Demand> discoverDemands(
            Target selectedTarget, SourceOutputSelection sourceSelection)
            throws IOException {
        TargetRank closure = discoverDemandClosure(selectedTarget,
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

    private TargetRank discoverDemandClosure(Target selectedTarget)
            throws IOException {
        return discoverDemandClosure(selectedTarget,
                (regionId, closure) -> Collections.emptySet());
    }

    private TargetRank discoverDemandClosure(
            Target selectedTarget, SourceOutputSelection sourceSelection)
            throws IOException {
        // This is the target's fatal input frontier, before producer inputs
        // extend the recursive closure.
        Set<Endpoint> fatalInputs = new LinkedHashSet<>();
        Map<Endpoint, Set<String>> targetAdmittedStateEdges =
                new LinkedHashMap<>();
        Set<String> failureMethods = selectedTarget.failureMethods();
        boolean hasDirectTargetState = hasDirectTargetStateFrontier(
                selectedTarget, failureMethods);
        for (JsonElement item : selectedTarget.goal.symbolize()) {
            if (!item.isJsonObject()) continue;
            JsonObject action = item.getAsJsonObject();
            String input = string(action, "symbol");
            if (input.isEmpty()) continue;
            Endpoint endpoint = new Endpoint(selectedTarget.occurrenceId,
                    selectedTarget.exactInput(input));
            boolean configuredRoot = failureInputSelection.selected(
                    selectedTarget.regionId, action);
            // A finalizer-admitted exact writer is propagated state, not a
            // new target-local symbolic root.  Seed that endpoint even when
            // the configured-root allowlist is intentionally empty.
            Set<String> admittedStateEdges =
                    exactAdmittedSharedStateProducerEdges(
                            selectedTarget.regionId, endpoint);
            boolean directTargetState = failureMethods.contains(
                    string(action, "rootMethod"));
            boolean admittedCausalState = !admittedStateEdges.isEmpty()
                    && (!hasDirectTargetState || directTargetState
                    || configuredRoot);
            if ((configuredRoot && (causalAction(action)
                    || exactCausalProducer(endpoint,
                    producersByDownstream, false)))
                    || admittedCausalState) {
                fatalInputs.add(endpoint);
                if (admittedCausalState) {
                    targetAdmittedStateEdges.put(endpoint,
                            admittedStateEdges);
                }
            }
        }
        // A communication cut is already an explicit input of this exact
        // target occurrence even when the local backward slice represents a
        // decoded request value through a container query rather than through
        // the handler parameter.
        Set<String> structuredProtocolParents = new LinkedHashSet<>();
        Map<Endpoint, Set<String>> targetProtocolEdges =
                new LinkedHashMap<>();
        for (JsonElement item : selectedTarget.goal.edgeBindings()) {
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
        for (JsonElement item : selectedTarget.goal.edgeBindings()) {
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
            // concrete carrier, not a second symbolic operand.
            if (!input.isEmpty()
                    && !structuredProtocolParents.contains(input)) {
                Endpoint endpoint = new Endpoint(selectedTarget.occurrenceId,
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
                : targetAdmittedStateEdges.entrySet()) {
            frontier.constrain(exact.getKey(), exact.getValue());
        }
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
        Set<String> causallyCarriedSourceIds = new LinkedHashSet<>();
        for (Demand demand : result) {
            demand.finalizeProjection(selectedEdgeByEndpoint);
            demand.addCausallyCarriedSourceIds(causallyCarriedSourceIds);
        }

        boolean exactDirectPresentation = false;
        for (Endpoint endpoint : fatalInputs) {
            JsonObject edge = selectedEdgeByEndpoint.get(endpoint);
            // The first live campaign cannot already carry the VM handoff
            // attestation that campaign is meant to produce.
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
        Map<String, Long> targetStateWriters = targetStateWriterVersions(
                fatalInputs, selectedEdgeByEndpoint,
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
        // Producer demands cannot execute a target-only campaign.
        return result.isEmpty() ? TargetRank.invalid()
                : new TargetRank(result, true, exactDirectPresentation,
                propagatedBoundedStateTransition, valueBackedFatalInputs,
                stateBackedFatalInputs, observedSemanticGuards.size(),
                causallyCarriedSourceIds.size(), targetStateWriters,
                residualFatalInputs,
                fatalInputs.size(), result.size(), exactBindings.size(),
                causalRegions.size());
    }

    /** Whether the fatal method itself reads an exact admitted state value.
     *
     * <p>If it does, container lookups in helper methods are the concrete
     * route to that object, not independent symbolic roots.  An explicitly
     * configured helper input remains selectable by the caller.</p> */
    private boolean hasDirectTargetStateFrontier(
            Target target, Set<String> failureMethods) throws IOException {
        if (failureMethods.isEmpty()) return false;
        for (JsonElement element : target.goal.symbolize()) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            if (!causalAction(action)
                    || !failureMethods.contains(string(action,
                    "rootMethod"))) {
                continue;
            }
            String input = string(action, "symbol");
            if (input.isEmpty()) continue;
            Endpoint endpoint = new Endpoint(target.occurrenceId,
                    target.exactInput(input));
            if (!exactAdmittedSharedStateProducerEdges(target.regionId,
                    endpoint).isEmpty()) {
                return true;
            }
        }
        return false;
    }

    /** Concrete state versions read directly by this target, by stable field.
     *
     * <p>When otherwise equivalent target calls straddle a real state
     * transition, a field-wise newer version is the changed causal topology
     * and repeated calls after it are stutter.  Missing or conflicting stable
     * field identities disable this preference rather than guessing.</p> */
    private static Map<String, Long> targetStateWriterVersions(
            Set<Endpoint> fatalInputs,
            Map<Endpoint, JsonObject> selectedEdgeByEndpoint,
            String targetOccurrence) {
        Map<String, Long> versions = new LinkedHashMap<>();
        for (Endpoint input : fatalInputs) {
            JsonObject edge = selectedEdgeByEndpoint.get(input);
            if (edge == null
                    || !targetOccurrence.equals(
                    string(edge, "toOccurrenceId"))
                    || !"HEAP".equals(string(edge, "transportKind"))) {
                continue;
            }
            String field = string(edge, "readFromField");
            long writer = longInteger(edge, "writerEventSeq", -1L);
            if (field.isEmpty() || writer < 0L) continue;
            Long prior = versions.putIfAbsent(field, writer);
            if (prior != null && prior.longValue() != writer) {
                return Collections.emptyMap();
            }
        }
        return Collections.unmodifiableMap(versions);
    }

    /** Counts fatal operands whose selected producer edge carries a value,
     * rather than only the identity of a concrete transport/container. */
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
            CausalAnchorIndex anchors = CausalAnchorIndex.of(unresolved,
                    producersByDownstream, selected, frontier);
            for (ProducerCandidate candidate : eligible) {
                Demand demand = selected.get(candidate);
                try {
                    if (demand == null) demand = candidate.materialize();
                    ProducerChoice choice = new ProducerChoice(candidate,
                            demand, unresolved, frontier,
                            selected.containsKey(candidate), anchors);
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

    /** Adds one fixed-point layer of explicitly admitted state writers. */
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
            Set<String> demandedBy = new LinkedHashSet<>(
                    sharedLocationConsumers(plan));
            demandedBy.retainAll(selectedRegions);
            if (demandedBy.isEmpty()) continue;
            // README REGION-1: the occurrence has one coarse producer, so this
            // admission materializes that one candidate.
            ProducerCandidate producer =
                    producerCandidatesByOccurrence.get(plan.occurrenceId());
            Demand materialized = null;
            if (producer != null && producer.ready()
                    && producer.goal.outputClosure() != null) {
                materialized = Demand.materialization(producer,
                        selectedOccurrences, frontier);
            }
            // This admission may feed another occurrence of an already
            // selected template.  It is not part of this exact closure.
            if (materialized == null) continue;
            requireReady(materialized);
            candidates.add(materialized);
        }

        // Admission exposes alternatives for an exact consumer input; it does
        // not require every observed writer occurrence.
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
            // Extends the common frontier from this demand's exact outputs.
            materialized.addSelectedMemberInputs(frontier,
                    producersByDownstream);
            admitted.put(materialized.occurrenceId, materialized);
        }
    }

    /** The one indexed producer of this occurrence, when it owns this goal. */
    private ProducerCandidate producerCandidate(
            String occurrenceId, Goal goal) {
        ProducerCandidate candidate =
                producerCandidatesByOccurrence.get(occurrenceId);
        return candidate != null && candidate.goal == goal
                ? candidate : null;
    }

    private static void addStrings(Set<String> target, JsonArray values) {
        for (JsonElement value : values) {
            if (value.isJsonPrimitive()) {
                String text = value.getAsString();
                if (!text.isEmpty()) target.add(text);
            }
        }
    }

    /** Counts fatal operands whose selected exact producer ancestry contains a
     * complete bounded state transition before reaching the target. */
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

    /** True when the producer that directly presents a fatal target input
     * consumes an exact heap value written by an earlier occurrence of that
     * same logical producer. */
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
                    presentation.member(targetEdge);
            for (JsonElement input : array(presentedMember.slice(),
                    "inputPorts")) {
                Endpoint endpoint = new Endpoint(
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
                        stateEdge);
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
        OutputClosureContract.Member member = demand.member(edge);
        JsonObject slice = member.slice();
        String consumerInstance = required(edge, "toOccurrenceId");
        boolean stateTransition = false;
        if (demand.containsOccurrence(consumerInstance)) {
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

    static boolean causalAction(JsonObject action) {
        if (action == null) {
            throw new IllegalArgumentException(
                    "causal input action is required");
        }
        return DependencyRole.VALUE_FRONTIER.equals(
                DependencyRole.normalize(action.get("dependencyRole")));
    }

    /** Whether an incoming producer edge makes this endpoint extend the
     * value frontier.
     *
     * <p>A concrete carrier does not normally extend it.  With {@code
     * transportedOnly} an exact heap object identity alone is refused: a
     * concrete local structure may carry transported value leaves, but the
     * identity by itself is not a symbolic producer demand.</p> */
    private static boolean exactCausalProducer(
            Endpoint endpoint,
            Map<Endpoint, List<ProducerCandidate>> producersByDownstream,
            boolean transportedOnly) {
        for (ProducerCandidate candidate
                : producersByDownstream.getOrDefault(endpoint,
                java.util.Collections.emptyList())) {
            for (JsonObject edge : candidate.edgesFor(endpoint)) {
                if (!transportedOnly && exactSharedStateConduit(edge)
                        || transportedValueFrontier(edge)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Exact edge ids the finalizer admitted for this target input.
     *
     * <p>The admission must name both this consumer region and the exact
     * shared location carried by a trusted runtime read-from edge.  This is
     * deliberately narrower than accepting every observed heap writer.</p> */
    private Set<String> exactAdmittedSharedStateProducerEdges(
            String consumerRegion, Endpoint endpoint) {
        Set<String> result = new LinkedHashSet<>();
        for (ProducerCandidate candidate
                : producersByDownstream.getOrDefault(endpoint,
                Collections.emptyList())) {
            if (!candidate.ready()
                    || !sharedLocationConsumers(candidate.plan)
                    .contains(consumerRegion)) {
                continue;
            }
            Set<String> admittedLocations =
                    candidate.plan.demandedSharedLocations();
            for (JsonObject edge : candidate.edgesFor(endpoint)) {
                String location = string(edge, "readFromField");
                if (!location.isEmpty()
                        && admittedLocations.contains(location)
                        && exactSharedStateConduit(edge)) {
                    String edgeId = string(edge, "edgeId");
                    if (!edgeId.isEmpty()) result.add(edgeId);
                }
            }
        }
        return result;
    }

    /** Whether one incoming shared-state edge is an exact conduit its
     * consuming endpoint may follow to the occurrence that wrote it.
     *
     * <p>A shared carrier is exact when the runtime edge identifies the
     * object actually read.</p> */
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

    /** Whether one incoming protocol edge makes its consuming endpoint extend
     * the value frontier even though the consuming action is a concrete
     * structure carrier. */
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
        // VM component received by the writer occurrence.
        return AutomaticRegionEdge.RUNTIME_EDGE_KIND.equals(
                string(edge, "kind"))
                && AutomaticRegionEdge
                .TRANSPORTED_VALUE_FRONTIER_AUTHORITY.equals(string(edge,
                AutomaticRegionEdge.TRANSPORTED_VALUE_FRONTIER_FIELD))
                && exactSharedStateConduit(edge);
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
                candidate.rank = discoverDemandClosure(candidate);
            } catch (IOException invalidClosure) {
                // Listing candidates remains useful when one alternative is
                // malformed.
                candidate.rank = TargetRank.invalid();
            }
        }
        matches.sort(Target::compare);
        return matches;
    }

    /** The target closures that remain candidates for target-first ranking. */
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
            for (JsonElement element : goal.edgeBindings()) {
                if (!element.isJsonObject()) continue;
                JsonObject edge = element.getAsJsonObject();
                String fromRegion = string(edge, "fromRegion");
                String fromOccurrence = string(edge,
                        "fromOccurrenceId");
                boolean sameRegion = plan.regionId().equals(fromRegion)
                        && fromOccurrence.equals(plan.occurrenceId());
                if (!sameRegion || string(edge, "fromOutputPort").isEmpty()
                        || !AutomaticRegionEdge.schedulableProducerBinding(edge)) {
                    continue;
                }
                String id = string(edge, "edgeId");
                if (selectedIds.add(id)) result.add(edge);
            }
            return result;
        }

        // A non-READY producer has no output-closure contract yet.
        String producer = goal.plan().occurrenceId();
        for (JsonElement item : goal.edgeBindings()) {
            if (item.isJsonObject()) {
                JsonObject edge = item.getAsJsonObject();
                if (producer.equals(string(edge, "fromOccurrenceId"))
                        && AutomaticRegionEdge.schedulableProducerBinding(
                        edge)) {
                    result.add(edge);
                }
            }
        }
        return result;
    }

    /**
     * Keeps only dynamic output versions that can carry every configured
     * source field their exact output slice demands.  This is deliberately
     * per edge/member: unrelated fields and outputs in the same coarse loop
     * occurrence keep their own independent read-from alternatives.
     */
    private static boolean causallyEligibleSourceEdge(
            RegionInstancePlan plan, Goal goal, JsonObject edge) {
        if (plan.configuredSourcePhases().isEmpty()
                || goal.outputClosure() == null) {
            return true;
        }
        OutputClosureContract.Member member = goal.outputClosure().member(
                string(edge, "fromOutputPort"));
        if (member == null) return true;
        return sourceIdsCarriedBy(plan, member.slice(),
                productionEvent(edge)) != null;
    }

    /**
     * Returns the source ids of the latest preceding phase for every
     * configured field this member demands.  {@code null} means that at least
     * one such field has no preceding phase and the dynamic output cannot
     * carry it.  A later phase of the same field starts a new version; it does
     * not retroactively invalidate an earlier output.
     */
    private static Set<String> sourceIdsCarriedBy(
            RegionInstancePlan plan, JsonObject selectedSlice,
            long produced) {
        Set<String> demandedFields = new LinkedHashSet<>();
        addStrings(demandedFields, array(selectedSlice,
                "demandedHeapDeclarations"));
        Set<String> carried = new LinkedHashSet<>();
        for (String field : demandedFields) {
            ConfiguredSourcePhaseContract.Occurrence latest = null;
            boolean configured = false;
            for (ConfiguredSourcePhaseContract.Occurrence phase
                    : plan.configuredSourcePhases()) {
                if (!field.equals(phase.fieldSignature())) continue;
                configured = true;
                if (phase.runtimeEventSeq() < produced
                        && (latest == null || phase.runtimeEventSeq()
                        > latest.runtimeEventSeq())) {
                    latest = phase;
                }
            }
            if (configured && latest == null) return null;
            if (latest != null) carried.add(latest.sourceId());
        }
        return carried;
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
        // The filter above already required the task's member ports to equal
        // the group's, so only the input side is still open.
        if (!task.outputClosure().executionScope().inputPorts()
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
            // An exchange pairing a replay recorded and the scheduler
            // absorbed is, by construction, one this occurrence's discovery
            // ledger does not hold: the ledger is what the baseline trace
            // saw, and the absorbed pairing is what it did not.  Its
            // authority is the VM's own send and receive events, named on
            // the row, so it is admitted here -- and nothing else is: a
            // binding without that stamp still has to be in the ledger, so a
            // scheduler that invents one is still caught.
            if (VmHandoffEvidence.absorbed(binding)) continue;
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
        /** Outputs added solely because the source declaration requires them.
         */
        private final Set<String> sourceAugmentedOutputs =
                new LinkedHashSet<>();
        private ProducerOutputProjection projection;

        private Demand(RegionInstancePlan plan, Goal goal,
                       Occurrence occurrence) {
            this(plan, goal, false, occurrence);
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
            // README REGION-1: one coarse occurrence is one campaign.
            campaignId = campaignId(regionId, occurrenceId);
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
                    // consumer input.
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

        private void retainSelectedEndpoints(Set<Endpoint> retained) {
            selectedEdges.keySet().retainAll(retained);
        }

        private void addSelectedMemberInputs(
                CausalFrontier frontier,
                Map<Endpoint, List<ProducerCandidate>> producersByDownstream)
                throws IOException {
            for (JsonObject edge : selectedEdges.values()) {
                String sourceInstance = required(edge, "fromOccurrenceId");
                OutputClosureContract.Member member = member(edge);
                addMemberInputs(sourceInstance,
                        requireOccurrence(sourceInstance), member,
                        selectedVersionSlice(member, edge),
                        frontier, producersByDownstream);
            }
        }

        /** Adds configured-source output members before the predecessor walk
         * closes. */
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
                alreadySelectedCells.add(member(edge).cell());
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
                addMemberInputs(occurrenceId, occurrence, member,
                        member.slice(), frontier, producersByDownstream);
                changed = true;
            }
            return changed;
        }

        private void addMemberInputs(
                String sourceInstance, Occurrence selected,
                OutputClosureContract.Member member,
                JsonObject selectedSlice,
                CausalFrontier frontier,
                Map<Endpoint, List<ProducerCandidate>> producersByDownstream)
                throws IOException {
            Set<String> unmaterializable = new LinkedHashSet<>();
            for (JsonElement input : array(selectedSlice, "inputPorts")) {
                String port = input.getAsString();
                Endpoint endpoint = new Endpoint(sourceInstance,
                        selected.exactInput(port));
                JsonObject action = dependencyAction(goal, port);
                if (action != null) {
                    if (causalAction(action)
                            || exactCausalProducer(endpoint,
                            producersByDownstream, true)) {
                        requiredInputEndpoints.add(endpoint);
                        frontier.addFromSlice(endpoint, selectedSlice,
                                producersByDownstream);
                    }
                    continue;
                }
                // A cut input can have no local action yet still have an exact
                // remote producer.
                if (exactCausalProducer(endpoint,
                        producersByDownstream, false)) {
                    requiredInputEndpoints.add(endpoint);
                    frontier.addFromSlice(endpoint, selectedSlice,
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
            Set<String> exactComponentParents = new LinkedHashSet<>();
            for (JsonObject edge : selectedEdges.values()) {
                OutputClosureContract.Member selectedMember = member(edge);
                outputs.add(selectedMember.portId());
                edgeIds.add(required(edge, "edgeId"));
                JsonObject selectedSlice = selectedVersionSlice(
                        selectedMember, edge);
                for (JsonElement element : array(selectedSlice,
                        "captureBindings")) {
                    if (!element.isJsonObject()) continue;
                    String parent = string(element.getAsJsonObject(),
                            CommunicationCatalogContract.PORT_COMPONENT_OF);
                    if (!parent.isEmpty()) exactComponentParents.add(parent);
                }
            }
            for (Endpoint input : requiredInputEndpoints) {
                JsonObject edge = selectedEdgeByEndpoint.get(input);
                if (edge != null) edgeIds.add(required(edge, "edgeId"));
            }
            // A coarse occurrence that reaches a declared communication cut
            // retains that cut as one of its own effects even when the edge
            // which selected the occurrence consumed a heap output.
            for (String output
                    : goal.outputClosure().producer().declaredOutputPorts()) {
                // A selected response/request leaf is the exact transported
                // value frontier.  Retaining its aggregate parent as a second
                // output would import every unrelated live-in of the whole
                // RPC handler (queues, registration state, metrics, ...).
                // Keep a declared cut when no exact component supersedes it.
                if (exactComponentParents.contains(output)) continue;
                OutputClosureContract.Member member =
                        goal.outputClosure().member(output);
                if (member == null) {
                    // The template declares every possible cut site, while one
                    // concrete occurrence materializes only the sites its path
                    // reached.
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

        /**
         * A configured source phase can explain only outputs produced after
         * that exact hook execution.  Coarse service-loop occurrences may
         * contain both an old write and a later source-bearing write; using
         * the former while scheduling the latter creates a disconnected
         * symbolic root even though both share one occurrence id.
         */
        private void addCausallyCarriedSourceIds(Set<String> carried)
                throws IOException {
            if (plan.configuredSourcePhases().isEmpty()) return;
            for (JsonObject edge : selectedEdges.values()) {
                OutputClosureContract.Member selectedMember = member(edge);
                long produced = productionEvent(edge);
                Set<String> selectedSources = sourceIdsCarriedBy(plan,
                        selectedVersionSlice(selectedMember, edge), produced);
                if (selectedSources == null) {
                    throw new IOException("configured source phase does not "
                            + "precede selected output: output="
                            + selectedMember.portId() + "; edge="
                            + required(edge, "edgeId")
                            + "; productionEvent=" + produced + "; "
                            + context());
                }
                carried.addAll(selectedSources);
            }
        }

        private ProducerOutputProjection projection() throws IOException {
            if (projection == null) {
                throw new IOException("producer demand has no finalized "
                        + "exact-output projection; " + context());
            }
            return projection;
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
                boolean exact = false;
                for (JsonObject edge : selectedEdges.values()) {
                    OutputClosureContract.Member edgeMember = member(edge);
                    if (!output.equals(edgeMember.portId())) continue;
                    addSliceInputs(result, selectedVersionSlice(edgeMember,
                            edge));
                    exact = true;
                }
                if (!exact) addSliceInputs(result, member);
            }
            return result;
        }

        /** Narrows predecessor discovery to the exact bounded writer version
         * consumed by one selected downstream edge. */
        private JsonObject selectedVersionSlice(
                OutputClosureContract.Member member, JsonObject edge)
                throws IOException {
            JsonObject union = member.slice();
            JsonArray versions = array(union, BOUNDED_VERSION_SCOPES);
            if (versions.size() == 0) return union;
            String selectedEdgeId = required(edge, "edgeId");
            long produced = productionEvent(edge);
            JsonObject selected = null;
            for (JsonElement element : versions) {
                if (!element.isJsonObject()) continue;
                JsonObject version = element.getAsJsonObject();
                Set<String> edges = new LinkedHashSet<>();
                addStrings(edges, array(version, "causalEdgeIds"));
                if (!edges.contains(selectedEdgeId)) {
                    continue;
                }
                if (selected != null) {
                    throw new IOException("output edge belongs to more than "
                            + "one bounded writer version: edge="
                            + selectedEdgeId + "; output=" + member.portId()
                            + "; " + context());
                }
                selected = version;
            }
            if (selected == null) {
                throw new IOException("selected output edge has no bounded "
                        + "writer version: edge=" + selectedEdgeId
                        + "; output=" + member.portId()
                        + "; productionEvent=" + produced + "; "
                        + context());
            }
            JsonObject exact = union.deepCopy();
            exact.add("inputPorts",
                    array(selected, "inputPorts").deepCopy());
            exact.add("causalEdgeIds",
                    array(selected, "causalEdgeIds").deepCopy());
            if (selected.has("demandedHeapDeclarations")) {
                exact.add("demandedHeapDeclarations", array(selected,
                        "demandedHeapDeclarations").deepCopy());
            }
            return exact;
        }

        private OutputClosureContract.Member member(JsonObject edge)
                throws IOException {
            String sourceInstance = required(edge, "fromOccurrenceId");
            String exactOutput = required(edge, "fromOutputPort");
            OutputClosureContract.Member member =
                    goal.outputClosure().member(requireOccurrence(
                            sourceInstance).canonicalOutput(exactOutput));
            if (member == null) {
                throw new IOException("exact producer output has no "
                        + "canonical closure member: "
                        + sourceInstance + ":" + exactOutput);
            }
            return member;
        }

        /** Adds every input port one closure member's slice lists. */
        private static void addSliceInputs(
                Set<String> result, OutputClosureContract.Member member) {
            addSliceInputs(result, member.slice());
        }

        private static void addSliceInputs(
                Set<String> result, JsonObject slice) {
            for (JsonElement input : array(slice, "inputPorts")) {
                if (input.isJsonPrimitive()) result.add(input.getAsString());
            }
        }

        /** The closure members the endpoints this candidate covers demand. */
        private List<OutputClosureContract.Member> demandedMembers(
                Set<Endpoint> endpoints, ProducerCandidate candidate,
                CausalFrontier frontier)
                throws IOException {
            List<OutputClosureContract.Member> result = new ArrayList<>();
            for (Endpoint endpoint : endpoints) {
                result.add(member(candidate.edgeFor(endpoint, occurrence,
                        frontier.allowedEdges(endpoint))));
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
                    addSliceInputs(result, member);
                }
                return result;
            }
            for (JsonObject edge : selectedEdges.values()) {
                OutputClosureContract.Member member = member(edge);
                addSliceInputs(result, selectedVersionSlice(member, edge));
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

        /** Counts only guards exercised by the exact output members selected
         * for this target. */
        private void addObservedSelectedSemanticGuards(Set<String> result)
                throws IOException {
            for (JsonObject edge : selectedEdges.values()) {
                JsonObject slice = member(edge).slice();
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
                    result.add(relationKey + "\n" + goalId + "\n" + site);
                }
            }
        }

        /** A concrete field write consumed by a later exact occurrence of the
         * same logical producer is also bounded state evolution. */
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

        /** The one action this goal declares for an output-slice input, or
         * {@code null} when it declares none. */
        private static JsonObject dependencyAction(Goal goal, String port)
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

    /** The exact consumer inputs still requiring producers, together with any
     * causal-edge identity already selected by the output member that exposed
     * each input.
     *
     * <p>Edge ids are a restriction on the admissible producer for that
     * endpoint, not another endpoint dimension: several observed deliveries
     * may reach one port, but once a concrete output member records which
     * delivery preceded its value, scheduling must not silently replace it
     * with an older delivery that happens to share the same port.</p> */
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

        private void addFromSlice(
                Endpoint endpoint, JsonObject selectedSlice,
                Map<Endpoint, List<ProducerCandidate>> producersByDownstream)
                throws IOException {
            endpoints.add(endpoint);
            Set<String> memberEdges = new LinkedHashSet<>();
            addStrings(memberEdges,
                    array(selectedSlice, "causalEdgeIds"));
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
     * When one recorded edge reached its consumer: a transported exchange is
     * received, a shared location is read.  {@code -1} when the trace
     * recorded neither, which is the only honest answer for an edge whose
     * arrival nobody observed.
     */
    private static long arrivalEvent(JsonObject edge) {
        long received = longInteger(edge, "receiverEventSeq", -1L);
        return received >= 0L ? received
                : longInteger(edge, "readerEventSeq", -1L);
    }

    /**
     * When one recorded edge left its producer: a transported exchange is
     * sent, a shared location is written.  {@code -1} when the trace
     * recorded neither.
     */
    private static long productionEvent(JsonObject edge) {
        long sent = longInteger(edge, "senderEventSeq", -1L);
        return sent >= 0L ? sent
                : longInteger(edge, "writerEventSeq", -1L);
    }

    /** Cheap exact-endpoint probe used before interpreting a logical
     * occurrence catalog. */
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

        /**
         * The latest recorded moment an exchange this occurrence produced
         * reached {@code endpoint}, or {@code -1} when the trace recorded
         * no arrival for it.  Only this occurrence's own edges answer: an
         * arrival another occurrence's edge recorded is that occurrence's.
         */
        private long arrivalAt(Endpoint endpoint,
                               Set<String> allowedEdgeIds) {
            long arrival = -1L;
            for (JsonObject edge : edgesFor(endpoint)) {
                if (!occurrence.occurrenceId.equals(
                        string(edge, "fromOccurrenceId"))) {
                    continue;
                }
                if (!allowedEdgeIds.isEmpty()
                        && !allowedEdgeIds.contains(
                        string(edge, "edgeId"))) {
                    continue;
                }
                arrival = Math.max(arrival, arrivalEvent(edge));
            }
            return arrival;
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

    /**
     * The read-from anchor of each demanded production: for one consumer
     * endpoint, and for each moment that consumer produced a value the
     * closure demands, the producer occurrence whose exchange arrived last
     * before that moment.
     *
     * <p>An occurrence is addressed by the exchange it carries, never by
     * where it happens to fall in an identity sort.  Every term here is the
     * plan's own recorded evidence: an edge the trace gave no arrival cannot
     * anchor anything, a consumer that produced nothing the closure demands
     * anchors nothing, and an arrival after the production it would have to
     * explain is refused rather than stretched.  An endpoint no recorded
     * arrival anchors is absent from this index and ranks exactly as it does
     * without one.</p>
     */
    private static final class CausalAnchorIndex {
        private static final CausalAnchorIndex EMPTY =
                new CausalAnchorIndex(
                        Collections.<Endpoint, Map<Long, String>>emptyMap());

        private final Map<Endpoint, Map<Long, String>> anchorsByEndpoint;

        private CausalAnchorIndex(
                Map<Endpoint, Map<Long, String>> anchorsByEndpoint) {
            this.anchorsByEndpoint = anchorsByEndpoint;
        }

        private static CausalAnchorIndex of(
                Set<Endpoint> unresolved,
                Map<Endpoint, List<ProducerCandidate>> producersByDownstream,
                Map<ProducerCandidate, Demand> selected,
                CausalFrontier frontier) {
            Map<String, Set<Long>> demandedProductions =
                    new LinkedHashMap<>();
            for (Demand demand : selected.values()) {
                for (JsonObject edge : demand.selectedEdges.values()) {
                    long produced = productionEvent(edge);
                    if (produced < 0L) continue;
                    Set<Long> productions = demandedProductions.get(
                            demand.occurrence.occurrenceId);
                    if (productions == null) {
                        productions = new java.util.TreeSet<>();
                        demandedProductions.put(
                                demand.occurrence.occurrenceId, productions);
                    }
                    productions.add(produced);
                }
            }
            if (demandedProductions.isEmpty()) return EMPTY;
            Map<Endpoint, Map<Long, String>> anchors = new LinkedHashMap<>();
            for (Endpoint endpoint : unresolved) {
                Set<Long> productions = demandedProductions.get(
                        endpoint.instance);
                if (productions == null) continue;
                Set<String> allowed = frontier.allowedEdges(endpoint);
                List<ProducerCandidate> candidates =
                        producersByDownstream.getOrDefault(endpoint,
                                Collections.<ProducerCandidate>emptyList());
                Map<Long, String> anchoredHere = new LinkedHashMap<>();
                for (Long production : productions) {
                    String anchor = "";
                    long latestArrival = -1L;
                    for (ProducerCandidate candidate : candidates) {
                        long arrival = candidate.arrivalAt(endpoint, allowed);
                        if (arrival < 0L
                                || arrival > production.longValue()) {
                            continue;
                        }
                        if (arrival > latestArrival) {
                            latestArrival = arrival;
                            anchor = candidate.occurrence.occurrenceId;
                        }
                    }
                    if (!anchor.isEmpty()) {
                        anchoredHere.put(production, anchor);
                    }
                }
                if (!anchoredHere.isEmpty()) {
                    anchors.put(endpoint, anchoredHere);
                }
            }
            return anchors.isEmpty() ? EMPTY
                    : new CausalAnchorIndex(anchors);
        }

        private Map<Long, String> anchorsAt(Endpoint endpoint) {
            return anchorsByEndpoint.getOrDefault(endpoint,
                    Collections.<Long, String>emptyMap());
        }

        /** How many demanded productions at {@code endpoint} read from
         * {@code occurrenceId}. */
        private int anchoredProductions(Endpoint endpoint,
                                        String occurrenceId) {
            int anchored = 0;
            for (String anchor : anchorsAt(endpoint).values()) {
                if (anchor.equals(occurrenceId)) anchored++;
            }
            return anchored;
        }

        /** The latest demanded production at {@code endpoint} that reads
         * from {@code occurrenceId}, or {@code 0} when none does. */
        private long latestAnchoredProduction(Endpoint endpoint,
                                              String occurrenceId) {
            long latest = 0L;
            for (Map.Entry<Long, String> anchor
                    : anchorsAt(endpoint).entrySet()) {
                if (anchor.getValue().equals(occurrenceId)) {
                    latest = Math.max(latest,
                            anchor.getKey().longValue());
                }
            }
            return latest;
        }
    }

    /** Deterministic greedy choice among alternative producer relations. */
    private static final class ProducerChoice {
        private static final Comparator<ProducerChoice> ORDER =
                Comparator.comparingInt(
                        (ProducerChoice value) -> value.coveredEndpoints.size())
                        .reversed()
                        // The consumer's recorded arrival/read-from is exact
                        // dynamic identity, so it outranks structural closure
                        // size and reuse.  Otherwise a smaller registration
                        // response can replace the later heartbeat version
                        // which actually preceded the demanded state write.
                        .thenComparingInt(
                                value -> -value.anchoredProductions)
                        .thenComparingLong(
                                value -> -value.latestAnchoredProduction)
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
        private final int anchoredProductions;
        private final long latestAnchoredProduction;

        private ProducerChoice(ProducerCandidate candidate, Demand demand,
                               Set<Endpoint> unresolved,
                               CausalFrontier frontier,
                               boolean alreadySelected,
                               CausalAnchorIndex anchors)
                throws IOException {
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
            Set<String> selectedOutputs = new LinkedHashSet<>();
            Set<String> selectedInputs = new LinkedHashSet<>();
            for (OutputClosureContract.Member member
                    : demand.demandedMembers(coveredEndpoints, candidate,
                    frontier)) {
                selectedOutputs.add(member.portId());
                Demand.addSliceInputs(selectedInputs, member);
            }
            OutputClosureContract closure = demand.goal.outputClosure();
            unrelatedEndpoints = candidate.downstreamEndpoints.size()
                    - coveredEndpoints.size();
            unrelatedOutputs = closure.members().size()
                    - selectedOutputs.size();
            demandedInputs = selectedInputs.size();
            unrelatedInputs = closure.executionScope().inputPorts().size()
                    - demandedInputs;
            int anchored = 0;
            long latestAnchored = 0L;
            for (Endpoint endpoint : coveredEndpoints) {
                anchored += anchors.anchoredProductions(endpoint,
                        demand.occurrence.occurrenceId);
                latestAnchored = Math.max(latestAnchored,
                        anchors.latestAnchoredProduction(endpoint,
                                demand.occurrence.occurrenceId));
            }
            anchoredProductions = anchored;
            latestAnchoredProduction = latestAnchored;
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
                // One coarse occurrence is one execution task: README
                // "occurrence plan" gives an occurrence one answer, and
                // which minted version reaches which read is decided at
                // replay.
                Selection selection = Selection.producer(producer,
                        producer.projection());
                materialized.add(selection);
                grouped.add(new ProducerGroup(producer, selection));
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

        /** Deep-validates the scheduled tasks against discovery and emits the
         * compact index consumed by later candidate stages. */
        JsonObject scheduleIndex(List<ExecutionTask> tasks,
                                 JsonObject regionPlanIdentity,
                                 JsonObject taskPlanIdentity)
                throws IOException {
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

    /** One exact input of one selected region occurrence. */
    private static final class Endpoint {
        private final String instance;
        private final String input;

        private Endpoint(String instance, String input) {
            this.instance = instance == null ? "" : instance.trim();
            this.input = input == null ? "" : input.trim();
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

        /** Whether the target predicate's decision site lies in this
         * occurrence. */
        private boolean namesFailureSite() {
            for (JsonElement element : goal.branches()) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (bool(branch, "failureTarget", false)
                        && !bool(branch, "loopControlGuard", false)
                        && bool(branch, "observed", false)
                        && TargetReachPathQueryBuilder
                        .requiredOutcome(branch) != null
                        && !string(branch, "siteId").isEmpty()) {
                    return true;
                }
            }
            return false;
        }

        private Set<String> failureMethods() {
            Set<String> methods = new LinkedHashSet<>();
            for (JsonElement element : goal.branches()) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (bool(branch, "failureTarget", false)
                        && !bool(branch, "loopControlGuard", false)
                        && TargetReachPathQueryBuilder
                        .requiredOutcome(branch) != null) {
                    String method = string(branch, "method");
                    if (!method.isEmpty()) methods.add(method);
                }
            }
            return methods;
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
            int compared = TargetRank.compareSemantic(left.rank, right.rank);
            if (compared != 0) return compared;
            if (left.relationKey.equals(right.relationKey)) {
                compared = TargetRank.compareStateWriters(
                        left.rank, right.rank);
                if (compared != 0) return compared;
                if (TargetRank.sameStateWriters(left.rank, right.rank)) {
                    compared = Long.compare(left.rootCallId(),
                            right.rootCallId());
                    if (compared != 0) return compared;
                }
            }
            compared = TargetRank.compareCost(left.rank, right.rank);
            if (compared != 0) return compared;
            compared = left.relationKey.compareTo(right.relationKey);
            if (compared != 0) return compared;
            compared = left.occurrenceId.compareTo(right.occurrenceId);
            if (compared != 0) return compared;
            return left.goalId.compareTo(right.goalId);
        }

        private long rootCallId() {
            return longInteger(object(plan.json(), "traceEvidence"),
                    "rootCallId", Long.MAX_VALUE);
        }
    }

    /** The rank of one candidate target, together with the producer demands
     * the closure that produced it selected. */
    private static final class TargetRank {
        private final List<Demand> demands;
        private final boolean valid;
        private final boolean exactDirectPresentation;
        private final boolean propagatedBoundedStateTransition;
        private final int valueBackedFatalInputs;
        private final int stateBackedFatalInputs;
        private final int observedSelectedSemanticGuards;
        private final int causallyCarriedSourceIds;
        private final Map<String, Long> targetStateWriterVersions;
        private final int residualFatalInputs;
        private final int fatalInputs;
        private final int producerGoals;
        private final int exactBindings;
        private final int causalRegions;

        private TargetRank(List<Demand> demands, boolean valid,
                           boolean exactDirectPresentation,
                           boolean propagatedBoundedStateTransition,
                           int valueBackedFatalInputs,
                           int stateBackedFatalInputs,
                           int observedSelectedSemanticGuards,
                           int causallyCarriedSourceIds,
                           Map<String, Long> targetStateWriterVersions,
                           int residualFatalInputs,
                           int fatalInputs, int producerGoals,
                           int exactBindings, int causalRegions) {
            this.demands = demands;
            this.valid = valid;
            this.producerGoals = producerGoals;
            this.exactDirectPresentation = exactDirectPresentation;
            this.propagatedBoundedStateTransition =
                    propagatedBoundedStateTransition;
            this.valueBackedFatalInputs = valueBackedFatalInputs;
            this.stateBackedFatalInputs = stateBackedFatalInputs;
            this.observedSelectedSemanticGuards =
                    observedSelectedSemanticGuards;
            this.causallyCarriedSourceIds = causallyCarriedSourceIds;
            this.targetStateWriterVersions =
                    Collections.unmodifiableMap(new LinkedHashMap<>(
                            targetStateWriterVersions));
            this.residualFatalInputs = residualFatalInputs;
            this.fatalInputs = fatalInputs;
            this.exactBindings = exactBindings;
            this.causalRegions = causalRegions;
        }

        private static TargetRank invalid() {
            return new TargetRank(Collections.<Demand>emptyList(), false,
                    false, false, 0, 0, 0, 0,
                    Collections.<String, Long>emptyMap(),
                    Integer.MAX_VALUE, Integer.MAX_VALUE,
                    Integer.MAX_VALUE,
                    Integer.MAX_VALUE, Integer.MAX_VALUE);
        }

        private static int compareSemantic(TargetRank left,
                                           TargetRank right) {
            int compared = Boolean.compare(right.valid, left.valid);
            if (compared != 0) return compared;
            // Explicit source hooks are roots, not optional decoration on an
            // otherwise cheaper closure.  Prefer the target whose exact
            // selected output versions causally carry more distinct roots.
            compared = Integer.compare(right.causallyCarriedSourceIds,
                    left.causallyCarriedSourceIds);
            if (compared != 0) return compared;
            // Prefer an occurrence where a failure-relevant protocol input is
            // presented by one exact schedulable cross-boundary edge.
            compared = Boolean.compare(right.exactDirectPresentation,
                    left.exactDirectPresentation);
            if (compared != 0) return compared;
            // A cheaper closure is not better when it leaves a fatal operand
            // free.
            compared = Integer.compare(left.residualFatalInputs,
                    right.residualFatalInputs);
            if (compared != 0) return compared;
            // Concrete receiver/container identity can identify a baseline
            // read-from arm but cannot stand in for symbolic value ancestry.
            compared = Integer.compare(right.valueBackedFatalInputs,
                    left.valueBackedFatalInputs);
            if (compared != 0) return compared;
            // Prefer the occurrence whose exact producer ancestry explains
            // more of the fatal predicate with bounded state evolution.
            compared = Integer.compare(right.stateBackedFatalInputs,
                    left.stateBackedFatalInputs);
            if (compared != 0) return compared;
            // Once the fatal frontier is equally closed, prefer a target whose
            // exact selected producer relation proves a bounded state
            // evolution.
            compared = Boolean.compare(
                    right.propagatedBoundedStateTransition,
                    left.propagatedBoundedStateTransition);
            if (compared != 0) return compared;
            // Among equally closed/stateful targets, prefer the exact
            // occurrence that actually exercised more semantic decisions in
            // the selected producer members.
            compared = Integer.compare(
                    right.observedSelectedSemanticGuards,
                    left.observedSelectedSemanticGuards);
            if (compared != 0) return compared;
            compared = Integer.compare(left.fatalInputs,
                    right.fatalInputs);
            return compared;
        }

        /** Returns a preference only when the same fields move monotonically.
         * Crossed versions are incomparable and retain the established rank. */
        private static int compareStateWriters(TargetRank left,
                                               TargetRank right) {
            if (left.targetStateWriterVersions.isEmpty()
                    || !left.targetStateWriterVersions.keySet().equals(
                    right.targetStateWriterVersions.keySet())) {
                return 0;
            }
            int direction = 0;
            for (String field : left.targetStateWriterVersions.keySet()) {
                int compared = Long.compare(
                        left.targetStateWriterVersions.get(field),
                        right.targetStateWriterVersions.get(field));
                if (compared == 0) continue;
                int next = compared > 0 ? -1 : 1;
                if (direction != 0 && direction != next) return 0;
                direction = next;
            }
            return direction;
        }

        private static boolean sameStateWriters(TargetRank left,
                                                TargetRank right) {
            return !left.targetStateWriterVersions.isEmpty()
                    && left.targetStateWriterVersions.equals(
                    right.targetStateWriterVersions);
        }

        private static int compareCost(TargetRank left, TargetRank right) {
            int compared = Integer.compare(left.producerGoals,
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
        private final Set<String> bindingIds;

        private Occurrence(Goal goal) {
            occurrenceId = goal.plan().occurrenceId();
            Set<String> ids = new LinkedHashSet<>();
            for (JsonElement element : goal.edgeBindings()) {
                if (element.isJsonObject()) {
                    String id = string(element.getAsJsonObject(), "edgeId");
                    if (!id.isEmpty()) ids.add(id);
                }
            }
            bindingIds = Collections.unmodifiableSet(ids);
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
