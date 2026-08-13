package edu.uva.liftlab.graphchecker.concolic;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.artifact;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sibling;

import edu.uva.liftlab.graphchecker.contract.BoundedOutputVersions;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
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
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.FloatingKind;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sha256;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Composes one selected fatal-region query with concolic summaries of its
 * upstream regions and runtime-validated equality/read-from edges.  The
 * resulting SMT is a structurally checked candidate formula used to obtain a
 * candidate model. Promoting it with an unforced natural target replay is
 * deliberately outside this component and remains the documented TODO.
 *
 * <p>This class is intentionally project independent. It consumes only common
 * region, summary, branch-contract, solver-context, and runtime-edge schemas;
 * no adapter can inject an arbitrary case formula. Missing upstream summaries
 * are reported as gaps and make the query unsatisfiable, so a syntactically
 * valid SMT query is never mistaken for a complete model.</p>
 */
public final class ConcolicSmtComposer {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().serializeNulls().setPrettyPrinting()
            .create();
    private ConcolicSmtComposer() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        Result result = compose(arguments);
        ArtifactIO.replace(arguments.output, result.smtLib);
        String manifest = GSON.toJson(result.manifest);
        ArtifactIO.replace(arguments.manifest, manifest
                + System.lineSeparator());
        System.out.println(manifest);
    }

    public static Result compose(Arguments arguments) throws IOException {
        require(arguments.fatalQueries, "fatal branch queries");
        require(arguments.runtimePlan, "runtime plan");
        RuntimePlanArtifact runtimePlan = RuntimePlanArtifact.read(
                arguments.runtimePlan);

        List<JsonObject> queryRows = ArtifactIO.readJsonl(
                arguments.fatalQueries);
        List<RelationSummary> summaries = new ArrayList<>();
        boolean observedUnderapproximation = false;
        for (Path summaryFile : arguments.summaries) {
            int row = 0;
            for (JsonObject encoded : ArtifactIO.readJsonl(summaryFile)) {
                try {
                    JsonObject coverage = object(encoded, "pathCoverage");
                    if (coverage.size() > 0) {
                        requireObservedCoverage(encoded, coverage,
                                arguments.compositionMode);
                        observedUnderapproximation = true;
                    }
                    RelationSummary summary =
                            RelationSummary.decode(encoded);
                    if (summary.regionId().isEmpty()
                            || summary.summaryId().isEmpty()) {
                        throw new IllegalArgumentException(
                                "summary identity is required");
                    }
                    summaries.addAll(OccurrenceInstantiator.expand(summary));
                } catch (IllegalArgumentException malformed) {
                    throw new IOException("Malformed relation summary "
                            + summaryFile + " row " + row, malformed);
                }
                row++;
            }
        }
        List<JsonObject> regions = runtimePlan.regions();
        if (regions.isEmpty()) {
            throw new IOException("runtime plan has no region port catalog: "
                    + arguments.runtimePlan);
        }
        JsonObject fatal = selectFatalQuery(queryRows, arguments);
        if (fatal.size() == 0) {
            throw new IOException("No ready fatal query matches region="
                    + arguments.fatalRegion + " instance="
                    + arguments.regionInstanceId);
        }
        requireCanonicalFatalQuerySchema(fatal);
        String fatalSite = string(fatal, "targetSiteId");

        // This composer consumes a seed query.  A solver-ready branch replay
        // contract is sufficient to build the candidate SMT, but it is not an
        // observation that the complete workload naturally reached the target.
        // Natural target replay promotion remains the explicit next-stage TODO.
        PortIndex ports = PortIndex.from(regions);
        JsonObject rawContext = object(fatal, "symbolicContext");
        // Runtime-confirmed first-hop demands are authoritative.  CLI bounds
        // describe supplied summaries; they must never erase a demanded edge
        // and turn its consumer input into an unconstrained existential.
        JsonObject resolutionContext = rawContext.deepCopy();
        boolean instanceScopedContext = resolutionContext.size() > 0
                && !string(resolutionContext, "regionInstanceId").isEmpty();

        ResolvedSummaryGraph resolved = resolveSummaryGraph(fatal,
                resolutionContext, summaries);
        FatalAbsenceMutationWitness failureWitness =
                FatalAbsenceMutationWitness.resolve(fatal, resolved, ports);
        // Runtime identity can expose several aliases for one concrete
        // writer/read event. Resolution deliberately admits only aliases
        // backed by an exact producer summary.  Re-scope the context to that
        // resolved graph before emission: one surviving alternative becomes
        // an ordinary versioned merge, while an entirely concrete alias
        // group disappears without creating symbolic ports.
        JsonObject context = boundedContext(resolutionContext,
                resolved);
        Emitter emitter = new Emitter(ports,
                new InvocationKey(string(fatal, "regionId"),
                        string(resolutionContext, "regionInstanceId")),
                failureWitness);
        emitter.begin(fatal);
        emitter.registerExactEqualityBoundExpressions(
                resolved.selectedEdges.values());
        if (!instanceScopedContext) {
            emitter.unsupported.add(
                    "MissingTargetInstanceSymbolicContext");
        }
        emitter.unsupported.addAll(resolved.gaps);

        List<String> fatalTerms = new ArrayList<>();
        List<String> fatalPrefixTerms = new ArrayList<>();
        String previousFatalScope = emitter.enterSymbolScope("fatal:"
                + firstNonBlank(string(fatal, "regionInstanceId"),
                string(fatal, "queryId"), fatalSite,
                string(fatal, "regionId"), "selected"));
        try {
            int pathOrdinal = 0;
            for (JsonElement element : array(fatal, "paths")) {
                JsonObject path = element.getAsJsonObject();
                int selectedPathOrdinal = pathOrdinal++;
                String label = "fatal target path " + selectedPathOrdinal;
                List<String> pathTerms = new ArrayList<>();
                List<String> prefixTerms = new ArrayList<>();
                JsonArray constraints = array(path, "constraints");
                for (int constraintIndex = 0;
                     constraintIndex < constraints.size();
                     constraintIndex++) {
                    boolean fatalCondition = constraintIndex
                            == constraints.size() - 1;
                    if (fatalCondition) {
                        emitter.beginFatalOperandCapture(
                                selectedPathOrdinal);
                    }
                    try {
                        String constraintTerm = emitter.constraint(
                                constraints.get(constraintIndex), label);
                        pathTerms.add(constraintTerm);
                        if (!fatalCondition) {
                            prefixTerms.add(constraintTerm);
                            emitter.recordFatalPrefixEquality(
                                    selectedPathOrdinal,
                                    constraints.get(constraintIndex));
                        }
                    } finally {
                        if (fatalCondition) {
                            emitter.endFatalOperandCapture();
                        }
                    }
                }
                String pathTerm = and(pathTerms);
                String prefixTerm = and(prefixTerms);
                fatalTerms.add(pathTerm);
                fatalPrefixTerms.add(prefixTerm);
                emitter.bindFatalPathPrefix(selectedPathOrdinal,
                        prefixTerm);
                emitter.bindFatalPath(selectedPathOrdinal, pathTerm);
            }
        } finally {
            emitter.restoreSymbolScope(previousFatalScope);
        }
        emitter.bindFatalPrefixAssertion(or(fatalPrefixTerms));
        emitter.bindFatalPathAssertion(or(fatalTerms));

        for (RelationSummary selection
                : resolved.selectedRegionSummaries.values()) {
            emitter.regionSummaryWithBoundedTimeline(selection);
        }

        emitter.merge(context);
        emitter.mergeEdgeBindings(resolved.selectedEdges.values());
        emitter.finishFatalAbsenceMutationWitness();
        emitter.emitExactCausalInputAliases(
                resolved.selectedRegionSummaries.values());
        emitter.finishBindings();
        boolean auditedEdgeEvidence = true;
        auditDroppedEdgeEvidence(emitter, ports,
                runtimePlan.edgeValidations());
        emitter.finish();
        String composedSmt = emitter.render();

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 2);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        manifest.addProperty("fatalSite", fatalSite);
        manifest.addProperty("compositionMode",
                arguments.compositionMode);
        manifest.addProperty("pathSetComplete",
                !observedUnderapproximation);
        manifest.add("resolvedEdgeBindings",
                GSON.toJsonTree(resolved.staticEdgeIds()));
        manifest.add("fatalAbsenceMutationWitness",
                failureWitness.manifest());
        manifest.add("suppliedInputs",
                GSON.toJsonTree(emitter.suppliedInputs));
        manifest.add("canonicalPortOccurrences",
                emitter.canonicalPortOccurrences());
        manifest.add("operandBindingLedger",
                emitter.operandBindingLedger());
        manifest.addProperty("droppedEdgeEvidenceAudit",
                auditedEdgeEvidence ? "AUDITED"
                        : "EDGE_VALIDATIONS_NOT_SUPPLIED");
        JsonArray gaps = new JsonArray();
        appendGaps(gaps, "COMPOSITION_GAP", emitter.unsupported);
        manifest.add("gaps", gaps);
        manifest.addProperty("state", gaps.size() == 0
                ? "CANDIDATE_READY" : "CANDIDATE_WITH_GAPS");
        manifest.addProperty("trustState", observedUnderapproximation
                ? "OBSERVED_PATH_UNDERAPPROX"
                : "CANDIDATE_ONLY");
        manifest.add("composedSmtArtifact", artifact(arguments.output,
                composedSmt.getBytes(StandardCharsets.UTF_8)));
        manifest.add("runtimePlanArtifact", artifact(arguments.runtimePlan));
        return new Result(composedSmt, manifest);
    }

    /**
     * Names evidence that was proven and then dropped.
     *
     * <p>An input the query presents without a producer is a freedom: the
     * model lets it take any value of its type, so a condition that turns on
     * it asserts almost nothing.  That freedom is honest only while no
     * producer for it was ever proven.  When the validated runtime edges
     * already carry an admissible write/read pair naming that exact consumer
     * port, the composition dropped a relation it was entitled to use, and
     * reporting no gap over it is a false report - worse than never having
     * found the evidence, because silence cannot be told from a genuine
     * absence.</p>
     *
     * <p>The admission gate is the shared one.  An edge counts only where
     * {@link AutomaticRegionEdge#composable} already admits it, so this audit
     * can never widen what the composer is allowed to believe: an edge whose
     * evidence the gate rejects could not have bound anything, and naming it
     * here would be a false alarm.  One gap per unbound consumer port keeps
     * the report proportional to the freedoms, not to the trace.</p>
     */
    private static void auditDroppedEdgeEvidence(Emitter emitter,
                                                 PortIndex ports,
                                                 List<JsonObject> edges) {
        Set<PortOccurrence> unbound = new LinkedHashSet<>();
        for (PortOccurrence occurrence : emitter.mentionedPorts) {
            if (ports.isInput(occurrence.portId)
                    && !emitter.suppliedInputOccurrences.contains(
                    occurrence)) {
                unbound.add(occurrence);
            }
        }
        if (unbound.isEmpty()) return;
        Set<PortOccurrence> reported = new LinkedHashSet<>();
        for (JsonObject edge : edges) {
            if (!AutomaticRegionEdge.composable(edge)) {
                continue;
            }
            String consumer = bindingTargetInput(edge);
            String instance = bindingTargetInstance(edge);
            String region = firstNonBlank(string(edge, "toRegion"),
                    regionOf(consumer));
            if (consumer.isEmpty() || instance.isEmpty()) continue;
            PortOccurrence occurrence = new PortOccurrence(
                    new InvocationKey(region, instance), consumer);
            if (!unbound.contains(occurrence)
                    || !reported.add(occurrence)) {
                continue;
            }
            emitter.unsupported.add(
                    "DROPPED_CONFIRMED_EDGE_EVIDENCE:"
                            + occurrence + ":"
                            + string(edge, "edgeId"));
        }
    }

    private static void requireObservedCoverage(JsonObject summary,
                                                JsonObject coverage,
                                                String compositionMode)
            throws IOException {
        if (!"EXISTENTIAL_OBSERVED_PATHS".equals(compositionMode)) {
            throw new IOException("Observed-path relation requires "
                    + "--composition-mode EXISTENTIAL_OBSERVED_PATHS");
        }
        JsonObject relation = object(summary, "regionRelation");
        if (integer(coverage, "schemaVersion", -1) != 1
                || !"OBSERVED_PATH_COVERAGE".equals(
                string(coverage, "kind"))
                || !"IMPORTED_VM_PATH_UNDERAPPROX_V1".equals(
                string(coverage, "authority"))
                || bool(coverage, "complete", true)
                || !("SELECTIVE_SYMBOLIC_BRANCH_SLICE".equals(
                string(relation, "guardProjection"))
                && "SELECTIVE_SYMBOLIC_INPUT_SLICE_V1".equals(
                string(coverage, "constraintProjectionAuthority"))
                || "FULL_PATH_COLLISION_FALLBACK".equals(
                string(relation, "guardProjection"))
                && "FULL_PATH_COLLISION_FALLBACK".equals(
                string(coverage, "constraintProjectionAuthority")))
                || integer(coverage, "observedCaseCount", -1)
                != array(relation, "cases").size()
                || integer(coverage, "observedPathCount", -1) < 1
                || integer(coverage, "observedCaseCount", -1)
                < integer(coverage, "observedPathCount", -1)
                || string(coverage, "observedPathSetHash").isEmpty()) {
            throw new IOException(
                    "Malformed observed-path under-approximation");
        }
    }

    private static void appendGaps(JsonArray target, String kind,
                                   Set<String> subjects) {
        for (String subject : subjects) {
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", kind);
            gap.addProperty("subject", subject);
            target.add(gap);
        }
    }

    private static void requireCanonicalFatalQuerySchema(JsonObject fatal)
            throws IOException {
        String kind = string(fatal, "kind");
        if (integer(fatal, "schemaVersion", -1) != 1
                || !"TARGET_REACH_PATH_SET_QUERY".equals(kind)) {
            throw new IOException("Unsupported canonical fatal query schema");
        }
        if (!"CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1".equals(
                string(fatal, "constraintAuthority"))
                || string(fatal, "targetSiteId").isEmpty()) {
            throw new IOException(
                    "Incomplete closed target reach path query");
        }
        for (JsonElement element : array(fatal, "paths")) {
            if (!element.isJsonObject()
                    || !element.getAsJsonObject().has("constraints")
                    || !element.getAsJsonObject().get("constraints")
                    .isJsonArray()) {
                throw new IOException(
                        "Malformed target reach path query member");
            }
        }
    }

    private static JsonObject selectFatalQuery(List<JsonObject> rows,
                                               Arguments arguments) {
        for (JsonObject row : rows) {
            if (!arguments.fatalRegion.isEmpty()
                    && !arguments.fatalRegion.equals(string(row,
                    "regionId"))) {
                continue;
            }
            if (!arguments.regionInstanceId.isEmpty()
                    && !arguments.regionInstanceId.equals(string(row,
                    "regionInstanceId"))) {
                continue;
            }
            if ("TARGET_REACH_PATH_SET_QUERY".equals(
                    string(row, "kind"))) {
                return row;
            }
        }
        return new JsonObject();
    }

    /**
     * Resolves the instance-scoped producer graph used by composition.
     *
     * <p>The fatal symbolic context is the only authority for the first hop.
     * Once an exact producer summary has been selected, its requested-output
     * slice declares the downstream input ports that may recursively admit an
     * upstream edge binding.  This keeps global plans and unrelated summary
     * bindings out of the automatic SMT relation.</p>
     */
    private static ResolvedSummaryGraph resolveSummaryGraph(
            JsonObject fatal, JsonObject context,
            List<RelationSummary> summaries) {
        SummaryIndex summaryIndex = SummaryIndex.build(summaries);
        ProducerDemandIndex knownDemands = new ProducerDemandIndex();
        List<JsonObject> equalities = relationRows(context,
                "equalityRelations");
        List<JsonObject> readFrom = relationRows(context,
                "versionedStateMerges");
        List<JsonObject> alternatives = alternativeRelations(context);
        while (true) {
            ResolvedSummaryGraph result = resolveSummaryGraphPass(
                    fatal, context, summaryIndex, knownDemands, equalities,
                    readFrom, alternatives);
            if (!knownDemands.addAll(result.demands)) return result;
        }
    }

    private static ResolvedSummaryGraph resolveSummaryGraphPass(
            JsonObject fatal, JsonObject context, SummaryIndex summaries,
            ProducerDemandIndex knownDemands,
            List<JsonObject> equalities, List<JsonObject> readFrom,
            List<JsonObject> alternatives) {
        String fatalRegion = string(fatal, "regionId");
        String fatalInstance = string(context, "regionInstanceId");
        ResolvedSummaryGraph result = new ResolvedSummaryGraph(fatalRegion,
                fatalInstance, knownDemands);

        registerContextDemands(result, equalities, readFrom, alternatives);
        seedContextRelations(result, summaries, equalities,
                "EQUALITY", true);
        seedContextRelations(result, summaries, readFrom,
                "READ_FROM", true);
        seedContextRelations(result, summaries, alternatives,
                "READ_FROM", false);

        while (!result.pending.isEmpty()) {
            ProducerKey consumer = result.pending.removeFirst();
            RelationSummary consumerSelection =
                    result.selectedRegionSummaries.get(
                            consumer.invocation());
            if (consumerSelection == null) continue;
            Set<String> demandedInputs =
                    consumerSelection.outputClosure().executionScope()
                            .inputPorts();
            if (demandedInputs.isEmpty()) continue;

            // Discover the whole upstream demand for this consumer before
            // selecting any producer summary.  Selecting while scanning one
            // edge at a time lets two singleton summaries stand in for one
            // atomic multi-output invocation.
            List<JsonObject> incoming = summaries.bindingsTargeting(
                    consumer.regionId, consumer.instanceId);
            List<JsonObject> admitted = new ArrayList<>();
            for (JsonObject binding : incoming) {
                if (!bindingTargets(binding, consumer.regionId,
                        consumer.instanceId, demandedInputs)
                        || !AutomaticRegionEdge
                        .trustedRuntimeCompositionBinding(binding)) {
                    continue;
                }
                admitted.add(binding);
                result.registerDemand(bindingSourceRegion(binding),
                        bindingSourceInstance(binding),
                        bindingSourceOutput(binding));
            }
            for (JsonObject binding : admitted) {
                resolveBindingProducer(result, binding, summaries,
                        consumer.regionId, consumer.instanceId);
            }
        }
        return result;
    }

    private static List<JsonObject> relationRows(JsonObject context,
                                                 String field) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : array(context, field)) {
            if (element.isJsonObject()) result.add(element.getAsJsonObject());
        }
        return result;
    }

    private static List<JsonObject> alternativeRelations(JsonObject context) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : array(context,
                "alternativeWriterGroups")) {
            if (!element.isJsonObject()) continue;
            JsonObject group = element.getAsJsonObject();
            for (JsonElement alternative : array(group, "alternatives")) {
                if (alternative.isJsonObject()) {
                    result.add(alternative.getAsJsonObject());
                }
            }
        }
        return result;
    }

    @SafeVarargs
    private static void registerContextDemands(
            ResolvedSummaryGraph graph, List<JsonObject>... groups) {
        for (List<JsonObject> relations : groups) {
            for (JsonObject relation : relations) {
                registerContextDemand(graph, relation);
            }
        }
    }

    private static void registerContextDemand(ResolvedSummaryGraph graph,
                                              JsonObject relation) {
        String output = string(relation, "fromEndpoint");
        String sourceRegion = regionOf(output);
        if (!graph.fatalRegion.equals(regionOf(string(relation,
                "toEndpoint"))) || sourceRegion.isEmpty()) return;
        for (JsonElement element : selectedBindings(relation)) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String targetInstance = bindingTargetInstance(binding);
            if (!targetInstance.isEmpty()
                    && !graph.fatalInstance.equals(targetInstance)) {
                continue;
            }
            String sourceInstance = bindingSourceInstance(binding);
            if (!sourceInstance.isEmpty()) {
                graph.registerDemand(sourceRegion, sourceInstance, output);
            }
        }
    }

    private static void seedContextRelations(
            ResolvedSummaryGraph graph, SummaryIndex summaries,
            List<JsonObject> relations,
            String expectedKind, boolean missingProducerIsGap) {
        for (JsonObject relation : relations) {
            seedContextRelation(graph, relation, summaries,
                    expectedKind, missingProducerIsGap);
        }
    }

    private static void seedContextRelation(ResolvedSummaryGraph graph,
                                            JsonObject relation,
                                            SummaryIndex summaries,
                                            String expectedRelationKind,
                                            boolean missingProducerIsGap) {
        String output = string(relation, "fromEndpoint");
        String input = string(relation, "toEndpoint");
        String sourceRegion = regionOf(output);
        if (!graph.fatalRegion.equals(regionOf(input))
                || sourceRegion.isEmpty()) {
            return;
        }
        JsonArray bindings = selectedBindings(relation);
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String targetInstance = bindingTargetInstance(binding);
            if (!targetInstance.isEmpty()
                    && !graph.fatalInstance.equals(targetInstance)) {
                continue;
            }
            String sourceInstance = bindingSourceInstance(binding);
            if (sourceInstance.isEmpty()) continue;
            ProducerKey key = selectExactProducer(graph, summaries,
                    sourceRegion, sourceInstance, output,
                    missingProducerIsGap);
            if (key != null) {
                graph.addDirectBindingIfPresent(key, graph.fatalRegion,
                        graph.fatalInstance, input, relation,
                        binding, expectedRelationKind);
            }
        }
    }

    private static void resolveBindingProducer(ResolvedSummaryGraph graph,
                                               JsonObject binding,
                                               SummaryIndex summaries,
                                               String targetRegion,
                                               String targetInstance) {
        if (!AutomaticRegionEdge.trustedRuntimeCompositionBinding(binding)) {
            graph.gaps.add("UntrustedRecursiveEdgeBinding:"
                    + string(binding, "edgeId"));
            return;
        }
        String sourceRegion = bindingSourceRegion(binding);
        String sourceInstance = bindingSourceInstance(binding);
        String output = bindingSourceOutput(binding);
        String input = bindingTargetInput(binding);
        if (sourceRegion.isEmpty() || output.isEmpty() || input.isEmpty()) {
            graph.gaps.add("MalformedRecursiveEdgeBinding:"
                    + string(binding, "edgeId"));
            return;
        }
        ProducerKey key = selectExactProducer(graph, summaries,
                sourceRegion, sourceInstance, output, true);
        if (key == null) return;
        RelationSummary selected = graph.selectedRegionSummaries.get(
                key.invocation());
        JsonObject exact = matchingBinding(selected, key, targetRegion,
                targetInstance, input, binding);
        if (exact.size() == 0) {
            graph.gaps.add("SelectedSummaryMissingExactEdgeBinding:"
                    + key + "->" + targetRegion + "@" + targetInstance
                    + ":" + input);
            return;
        }
        graph.addEdge(new ResolvedEdge(selected, exact));
    }

    private static ProducerKey selectExactProducer(
            ResolvedSummaryGraph graph, SummaryIndex summaries,
            String region, String requestedInstance,
            String output, boolean missingProducerIsGap) {
        Set<String> demandedOutputs = graph.demandedOutputs(region,
                requestedInstance, output);
        InvocationKey invocation = new InvocationKey(region,
                requestedInstance);
        RelationSummary regionSelection =
                graph.selectedRegionSummaries.get(invocation);
        boolean newlySelected = regionSelection == null;
        if (regionSelection != null
                && !regionSelection.outputClosure().outputPorts().containsAll(
                demandedOutputs)) {
            // The outer resolver reruns from a clean graph with the monotonic
            // demand index.  Never keep using a closure that omits a newly
            // discovered port.  A joint closure may safely cover a smaller
            // demand because all of its outputs share the same path cases.
            graph.gaps.add("ProducerDemandExpandedAfterSelection:"
                    + producerLabel(region, requestedInstance,
                    demandedOutputs) + ":selected="
                    + regionSelection.outputClosure().outputPorts());
            return null;
        }
        Map<String, RelationSummary> unique = new LinkedHashMap<>();
        Set<String> fingerprints = new LinkedHashSet<>();
        for (RelationSummary summary : summaries.covering(region,
                demandedOutputs)) {
            if (!requestedInstance.isEmpty()
                    && !requestedInstance.equals(
                    summary.regionInstanceId())) {
                continue;
            }
            unique.put(summary.summaryId(), summary);
            fingerprints.add(
                    summary.outputClosure().closureFingerprint());
        }
        if (unique.isEmpty()) {
            if (missingProducerIsGap) {
                graph.gaps.add("MissingExactProducerSummary:"
                        + producerLabel(region, requestedInstance,
                        demandedOutputs));
            }
            return null;
        }
        if (fingerprints.size() != 1) {
            graph.gaps.add("AmbiguousProducerClosureFingerprint:"
                    + producerLabel(region, requestedInstance,
                    demandedOutputs) + ":fingerprints=" + fingerprints);
            return null;
        }
        if (unique.size() > 1) {
            graph.gaps.add("AmbiguousExactProducerSummary:"
                    + producerLabel(region, requestedInstance,
                            demandedOutputs));
            return null;
        }
        RelationSummary selected = unique.values().iterator().next();
        String instance = firstNonBlank(requestedInstance,
                selected.regionInstanceId());
        ProducerKey key = new ProducerKey(region, instance, output);
        invocation = key.invocation();
        regionSelection = graph.selectedRegionSummaries.get(invocation);
        newlySelected = regionSelection == null;
        if (regionSelection != null && !regionSelection.same(selected)) {
            graph.gaps.add("ConflictingProducerSummarySelection:" + key);
            return null;
        }
        if (newlySelected) {
            graph.selectedRegionSummaries.put(invocation, selected);
            ProducerKey expansionKey = key;
            for (String demanded : demandedOutputs) {
                ProducerKey demandedKey = new ProducerKey(region, instance,
                        demanded);
                if (demanded.compareTo(expansionKey.outputPort) < 0) {
                    expansionKey = demandedKey;
                }
            }
            graph.relevantRegions.add(region);
            graph.pending.addLast(expansionKey);
        }
        return key;
    }

    private static String producerLabel(String region, String instance,
                                        Set<String> outputs) {
        return region + "[instance="
                + firstNonBlank(instance, "<unique-instance>")
                + ",outputs=" + outputs + "]";
    }

    private static JsonObject matchingBinding(RelationSummary summary,
                                              ProducerKey source,
                                              String targetRegion,
                                              String targetInstance,
                                              String targetInput,
                                              JsonObject preferred) {
        List<JsonObject> matches = matchingBindings(summary, source,
                targetRegion, targetInstance, targetInput, preferred, null,
                bindingRelationKind(preferred));
        return matches.size() == 1 ? matches.get(0) : new JsonObject();
    }

    private static List<JsonObject> matchingBindings(
            RelationSummary summary, ProducerKey source, String targetRegion,
            String targetInstance, String targetInput,
            JsonObject expectedRelation, JsonObject expectedBinding,
            String expectedKind) {
        Map<String, JsonObject> matches = new LinkedHashMap<>();
        for (JsonObject binding : summary.edgeBindings()) {
            if (!source.instanceId.equals(bindingSourceInstance(binding))
                    || !source.outputPort.equals(bindingSourceOutput(binding))
                    || !AutomaticRegionEdge
                    .trustedRuntimeCompositionBinding(binding)
                    || !sameCompositionRelation(binding, expectedRelation,
                    expectedKind)
                    || expectedBinding != null
                    && !sameCompositionRelation(binding, expectedBinding,
                    expectedKind)
                    || !bindingTargets(binding, targetRegion,
                    targetInstance, targetInput)) {
                continue;
            }
            String edgeId = string(binding, "edgeId");
            if (!edgeId.isEmpty()) matches.put(edgeId, binding);
        }
        return new ArrayList<>(matches.values());
    }

    private static JsonArray selectedBindings(JsonObject relation) {
        return array(relation, "selectedBindings");
    }

    /**
     * Keeps a context relation tied to the exact runtime edge that justified
     * it.  Matching ports and instances are not enough: an RPC equality and a
     * heap READ_FROM can legitimately name the same canonical cells while
     * carrying different identity semantics.
     */
    private static boolean sameCompositionRelation(JsonObject binding,
                                                   JsonObject expected,
                                                   String expectedKind) {
        String kind = firstNonBlank(expectedKind,
                bindingRelationKind(expected));
        if (kind.isEmpty() || !kind.equals(bindingRelationKind(binding))) {
            return false;
        }
        String edgeId = string(expected, "edgeId");
        if (!edgeId.isEmpty() && !edgeId.equals(string(binding, "edgeId"))) {
            return false;
        }
        String fromInstance = bindingSourceInstance(expected);
        String toInstance = bindingTargetInstance(expected);
        if (!fromInstance.isEmpty()
                && !fromInstance.equals(bindingSourceInstance(binding))
                || !toInstance.isEmpty()
                && !toInstance.equals(bindingTargetInstance(binding))) {
            return false;
        }
        if (expected.has("writerEventSeq")) {
            long expectedWriter = longInteger(expected, "writerEventSeq", -1);
            long actualWriter = longInteger(binding, "writerEventSeq", -1);
            if (expectedWriter != actualWriter) return false;
        }
        if (expected.has("readerEventSeq")) {
            long expectedReader = longInteger(expected, "readerEventSeq", -1);
            long actualReader = longInteger(binding, "readerEventSeq", -1);
            if (expectedReader != actualReader) return false;
        }
        return true;
    }

    private static String bindingRelationKind(JsonObject binding) {
        String kind = string(binding, "evidenceKind");
        if (AutomaticRegionEdge.CONFIGURED_PROTOCOL_EQUALITY.equals(kind)) {
            return "EQUALITY";
        }
        if (AutomaticRegionEdge.FIELD_ASSIGNMENT_READ_FROM.equals(kind)
                || AutomaticRegionEdge.CONTAINER_MUTATION_READ_FROM
                .equals(kind)) {
            return "READ_FROM";
        }
        return "";
    }

    private static boolean bindingTargets(JsonObject binding, String region,
                                          String instance, String input) {
        String bindingRegion = string(binding, "toRegion");
        String bindingInstance = bindingTargetInstance(binding);
        return region.equals(bindingRegion)
                && !instance.isEmpty() && instance.equals(bindingInstance)
                && (input.isEmpty() || input.equals(bindingTargetInput(binding)));
    }

    private static boolean bindingTargets(JsonObject binding, String region,
                                          String instance,
                                          Set<String> inputs) {
        return bindingTargets(binding, region, instance,
                bindingTargetInput(binding))
                && inputs.contains(bindingTargetInput(binding));
    }

    private static String bindingSourceRegion(JsonObject binding) {
        return string(binding, "fromRegion");
    }

    private static String bindingSourceInstance(JsonObject binding) {
        return string(binding, "fromRegionInstance");
    }

    private static String bindingTargetInstance(JsonObject binding) {
        return string(binding, "toRegionInstance");
    }

    private static String bindingSourceOutput(JsonObject binding) {
        return string(binding, "fromOutputPort");
    }

    private static String bindingTargetInput(JsonObject binding) {
        return string(binding, "toInputPort");
    }

    /**
     * Expands one logical VM relation into exact invocation-scoped views.
     * The relation is still imported and stored once; these copies are an
     * in-memory alpha-renaming adapter used only by composition.  In
     * particular, exact edge rows are selected by the compact binding-id
     * ledger instead of copying the planner's full occurrence plans into the
     * execution task or relation summary.
     */
    private static final class OccurrenceInstantiator {
        private static final String KIND =
                "LOGICAL_SUMMARY_OCCURRENCE_CATALOG";

        private static List<RelationSummary> expand(
                RelationSummary summary) {
            JsonObject catalog = summary.occurrenceInstantiationCatalog();
            if (catalog.size() == 0) {
                return Collections.singletonList(summary);
            }
            if (integer(catalog, "schemaVersion", -1) != 1
                    || !KIND.equals(string(catalog, "kind"))) {
                throw malformed(summary, "unsupported catalog schema");
            }
            String logicalRegion = string(catalog, "logicalRegionId");
            String reuseKey = string(catalog, "summaryReuseKey");
            if (logicalRegion.isEmpty() || reuseKey.isEmpty()
                    || !logicalRegion.equals(summary.logicalRegionId())
                    || !reuseKey.equals(summary.summaryReuseKey())) {
                throw malformed(summary, "logical region mismatch");
            }
            String canonicalInstance = string(catalog,
                    "canonicalRegionInstanceId");
            if (!summary.regionInstanceId().equals(canonicalInstance)) {
                throw malformed(summary,
                        "canonical invocation does not own the relation");
            }
            long canonicalRoot = longInteger(catalog,
                    "canonicalRootCallId", -1L);
            if (canonicalRoot >= 0L && canonicalRoot
                    != summary.outputClosure().producer().rootCallId()) {
                throw malformed(summary, "canonical root mismatch");
            }

            Set<String> canonicalInputs = new LinkedHashSet<>(
                    summary.outputClosure().executionScope().inputPorts());
            Set<String> canonicalOutputs = new LinkedHashSet<>(
                    summary.outputClosure().outputPorts());
            List<RelationSummary> result = new ArrayList<>();
            Set<String> instances = new LinkedHashSet<>();
            boolean foundCanonical = false;
            for (JsonElement element : array(catalog, "occurrences")) {
                if (!element.isJsonObject()) {
                    throw malformed(summary, "non-object occurrence");
                }
                JsonObject occurrence = element.getAsJsonObject();
                String instance = string(occurrence, "regionInstanceId");
                long rootCall = longInteger(occurrence, "rootCallId", -1L);
                if (instance.isEmpty() || rootCall < 0L
                        || !instances.add(instance)) {
                    throw malformed(summary,
                            "missing or duplicate exact invocation "
                                    + instance);
                }
                foundCanonical |= canonicalInstance.equals(instance);
                Map<String, String> inputs = portMap(summary, occurrence,
                        "inputPortMap", canonicalInputs);
                Map<String, String> outputs = portMap(summary, occurrence,
                        "outputPortMap", canonicalOutputs);
                Set<String> exactPorts = new LinkedHashSet<>(inputs.values());
                if (!exactPorts.addAll(outputs.values())) {
                    throw malformed(summary,
                            "exact input/output port collision at " + instance);
                }
                Map<String, String> ports = new LinkedHashMap<>();
                ports.putAll(inputs);
                ports.putAll(outputs);
                List<JsonObject> bindings = exactBindings(summary,
                        occurrence, instance);
                result.add(instantiate(summary, occurrence, ports,
                        bindings, rootCall));
            }
            if (result.isEmpty() || !foundCanonical) {
                throw malformed(summary,
                        "catalog has no canonical exact occurrence");
            }
            return result;
        }

        private static Map<String, String> portMap(
                RelationSummary summary, JsonObject occurrence,
                String field, Set<String> requiredCanonical) {
            Map<String, String> result = new LinkedHashMap<>();
            Set<String> exact = new LinkedHashSet<>();
            for (JsonElement element : array(occurrence, field)) {
                if (!element.isJsonObject()) {
                    throw malformed(summary, "malformed " + field);
                }
                JsonObject row = element.getAsJsonObject();
                String canonical = string(row, "canonicalPort");
                String actual = string(row, "exactPort");
                if (canonical.isEmpty() || actual.isEmpty()
                        || result.putIfAbsent(canonical, actual) != null
                        || !exact.add(actual)
                        || !summary.regionId().equals(regionOf(actual))) {
                    throw malformed(summary, "ambiguous " + field);
                }
            }
            if (!result.keySet().containsAll(requiredCanonical)) {
                throw malformed(summary, field
                        + " does not cover the relation ports");
            }
            return result;
        }

        private static List<JsonObject> exactBindings(
                RelationSummary summary, JsonObject occurrence,
                String instance) {
            Set<String> ids = new LinkedHashSet<>();
            for (JsonElement element : array(occurrence, "bindingIds")) {
                if (!element.isJsonPrimitive()
                        || !element.getAsJsonPrimitive().isString()
                        || firstNonBlank(element.getAsString()).isEmpty()
                        || !ids.add(element.getAsString().trim())) {
                    throw malformed(summary,
                            "ambiguous exact binding id at " + instance);
                }
            }
            Set<String> touchingIds = new LinkedHashSet<>();
            List<JsonObject> result = new ArrayList<>();
            for (JsonObject binding : summary.edgeBindings()) {
                if (!instance.equals(bindingSourceInstance(binding))
                        && !instance.equals(bindingTargetInstance(binding))) {
                    continue;
                }
                String edgeId = string(binding, "edgeId");
                if (edgeId.isEmpty()) {
                    throw malformed(summary,
                            "exact edge binding has no id at " + instance);
                }
                touchingIds.add(edgeId);
                if (ids.contains(edgeId)) result.add(binding.deepCopy());
            }
            if (!ids.equals(touchingIds)) {
                throw malformed(summary,
                        "binding-id ledger is incomplete at " + instance);
            }
            return result;
        }

        private static RelationSummary instantiate(
                RelationSummary summary, JsonObject occurrence,
                Map<String, String> ports, List<JsonObject> bindings,
                long rootCall) {
            JsonObject row = summary.toJson();
            String instance = string(occurrence, "regionInstanceId");
            row.addProperty("summaryId", summary.summaryId() + ".OCC."
                    + sha256(instance).substring(0, 16));
            row.addProperty("regionInstanceId", instance);
            row.addProperty("rootCallId", rootCall);

            JsonObject closure = remap(row.get(
                    OutputClosureContract.FIELD), ports).getAsJsonObject();
            JsonObject producer = object(closure, "producer");
            producer.addProperty("regionInstanceId", instance);
            producer.addProperty("rootCallId", rootCall);
            row.add(OutputClosureContract.FIELD, closure);
            if (row.has("regionRelation")) {
                row.add("regionRelation", remap(row.get("regionRelation"),
                        ports));
            }
            if (row.has("outputExpressions")) {
                row.add("outputExpressions", remap(
                        row.get("outputExpressions"), ports));
            }
            JsonArray exact = new JsonArray();
            for (JsonObject binding : bindings) exact.add(binding);
            row.add("edgeBindings", exact);
            return RelationSummary.decode(row);
        }

        private static JsonElement remap(JsonElement value,
                                         Map<String, String> ports) {
            return PortAlphaRenaming.remap(value, ports,
                    "occurrence port remap collides at ");
        }

        private static IllegalArgumentException malformed(
                RelationSummary summary, String issue) {
            return new IllegalArgumentException(
                    "malformed occurrence catalog for "
                            + summary.summaryId() + ": " + issue);
        }
    }

    private static final class SummaryIndex {
        private final Map<String, List<RelationSummary>> byClosure =
                new LinkedHashMap<>();
        private final Map<String, List<RelationSummary>> byRegion =
                new LinkedHashMap<>();
        private final Map<String, List<JsonObject>> bindingsByTarget =
                new LinkedHashMap<>();

        private static SummaryIndex build(List<RelationSummary> summaries) {
            SummaryIndex result = new SummaryIndex();
            for (RelationSummary decoded : summaries) {
                result.byRegion.computeIfAbsent(decoded.regionId(),
                        ignored -> new ArrayList<>()).add(decoded);
                result.byClosure.computeIfAbsent(closureKey(
                                decoded.regionId(),
                                decoded.outputClosure().outputPorts()),
                        ignored -> new ArrayList<>()).add(decoded);
                for (JsonObject binding : decoded.edgeBindings()) {
                    String targetRegion = string(binding, "toRegion");
                    String targetInstance =
                            bindingTargetInstance(binding);
                    if (targetRegion.isEmpty()
                            || targetInstance.isEmpty()) {
                        continue;
                    }
                    result.bindingsByTarget.computeIfAbsent(
                            targetRegion + "\n" + targetInstance,
                            ignored -> new ArrayList<>()).add(binding);
                }
            }
            return result;
        }

        private List<RelationSummary> covering(String region,
                                               Set<String> outputs) {
            List<RelationSummary> exact = byClosure.get(
                    closureKey(region, outputs));
            if (exact != null) return exact;
            int smallest = Integer.MAX_VALUE;
            List<RelationSummary> result = new ArrayList<>();
            for (RelationSummary summary : byRegion.getOrDefault(region,
                    Collections.emptyList())) {
                Set<String> available =
                        summary.outputClosure().outputPorts();
                if (!available.containsAll(outputs)) continue;
                if (available.size() < smallest) {
                    result.clear();
                    smallest = available.size();
                }
                if (available.size() == smallest) result.add(summary);
            }
            return result;
        }

        private List<JsonObject> bindingsTargeting(String region,
                                                   String instance) {
            return bindingsByTarget.getOrDefault(region + "\n" + instance,
                    Collections.emptyList());
        }

        private static String closureKey(String region,
                                         Set<String> outputs) {
            return firstNonBlank(region) + "\n"
                    + String.join("\u0000",
                    new TreeSet<>(outputs));
        }
    }

    private static final class ProducerDemandIndex {
        private final Map<String, Set<String>> outputsByInvocation =
                new LinkedHashMap<>();

        private ProducerDemandIndex() {
        }

        private ProducerDemandIndex(ProducerDemandIndex source) {
            addAll(source);
        }

        private void add(String region, String instance, String output) {
            String normalizedRegion = firstNonBlank(region);
            String normalizedOutput = firstNonBlank(output);
            if (normalizedRegion.isEmpty() || normalizedOutput.isEmpty()) {
                return;
            }
            String key = key(normalizedRegion, firstNonBlank(instance));
            outputsByInvocation.computeIfAbsent(key,
                    ignored -> new LinkedHashSet<>()).add(normalizedOutput);
        }

        private Set<String> outputs(String region, String instance) {
            Set<String> result = new TreeSet<>();
            Set<String> exact = outputsByInvocation.get(
                    key(region, instance));
            if (exact != null) result.addAll(exact);
            return result;
        }

        private boolean addAll(ProducerDemandIndex source) {
            boolean changed = false;
            if (source == null) return false;
            for (Map.Entry<String, Set<String>> entry
                    : source.outputsByInvocation.entrySet()) {
                changed |= outputsByInvocation.computeIfAbsent(
                        entry.getKey(), ignored -> new LinkedHashSet<>())
                        .addAll(entry.getValue());
            }
            return changed;
        }

        private static String key(String region, String instance) {
            return firstNonBlank(region) + "\u0000"
                    + firstNonBlank(instance);
        }
    }

    private static final class ProducerKey {
        private final String regionId;
        private final String instanceId;
        private final String outputPort;

        private ProducerKey(String regionId, String instanceId,
                            String outputPort) {
            this.regionId = firstNonBlank(regionId);
            this.instanceId = firstNonBlank(instanceId);
            this.outputPort = firstNonBlank(outputPort);
        }

        private InvocationKey invocation() {
            return new InvocationKey(regionId, instanceId);
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof ProducerKey)) return false;
            ProducerKey value = (ProducerKey) other;
            return regionId.equals(value.regionId)
                    && instanceId.equals(value.instanceId)
                    && outputPort.equals(value.outputPort);
        }

        @Override
        public int hashCode() {
            return Objects.hash(regionId, instanceId, outputPort);
        }

        @Override
        public String toString() {
            return regionId + "[instance=" + instanceId + ",output="
                    + outputPort + "]";
        }
    }

    private static final class InvocationKey {
        private final String regionId;
        private final String instanceId;

        private InvocationKey(String regionId, String instanceId) {
            this.regionId = firstNonBlank(regionId);
            this.instanceId = firstNonBlank(instanceId);
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof InvocationKey)) return false;
            InvocationKey value = (InvocationKey) other;
            return regionId.equals(value.regionId)
                    && instanceId.equals(value.instanceId);
        }

        @Override
        public int hashCode() {
            return Objects.hash(regionId, instanceId);
        }

        @Override
        public String toString() {
            return regionId + "@" + instanceId;
        }
    }

    private static final class PortOccurrence {
        private final InvocationKey invocation;
        private final String portId;

        private PortOccurrence(InvocationKey invocation, String portId) {
            this.invocation = invocation;
            this.portId = firstNonBlank(portId);
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof PortOccurrence)) return false;
            PortOccurrence value = (PortOccurrence) other;
            return invocation.equals(value.invocation)
                    && portId.equals(value.portId);
        }

        @Override
        public int hashCode() {
            return Objects.hash(invocation, portId);
        }

        @Override
        public String toString() {
            return invocation.instanceId + ":" + portId;
        }
    }

    private static final class ResolvedEdge {
        private final RelationSummary summary;
        private final JsonObject binding;

        private ResolvedEdge(RelationSummary summary, JsonObject binding) {
            this.summary = summary;
            this.binding = binding;
        }

    }

    /**
     * A failure-directed witness derived only from the selected fatal path,
     * its exact runtime state edge, and real VM output relations.  It is used
     * when a fatal associative lookup returns null and the supplying region
     * has a path that actually removes a member from that same state.
     */
    private static final class FatalAbsenceMutationWitness {
        private final List<Demand> demands;
        private final Map<PortOccurrence, List<RemovalCaseEffect>> effects =
                new LinkedHashMap<>();
        private final List<String> clauses = new ArrayList<>();

        private FatalAbsenceMutationWitness(List<Demand> demands) {
            this.demands = demands;
        }

        private static FatalAbsenceMutationWitness resolve(
                JsonObject fatal, ResolvedSummaryGraph graph,
                PortIndex ports) {
            List<AbsenceRead> reads = new ArrayList<>();
            int pathOrdinal = 0;
            for (JsonElement pathElement : array(fatal, "paths")) {
                if (!pathElement.isJsonObject()) {
                    pathOrdinal++;
                    continue;
                }
                for (JsonElement constraint : array(
                        pathElement.getAsJsonObject(), "constraints")) {
                    collectAbsenceReads(constraint, pathOrdinal, ports,
                            reads);
                }
                pathOrdinal++;
            }
            String fatalInstance = firstNonBlank(
                    string(fatal, "regionInstanceId"),
                    string(object(fatal, "symbolicContext"),
                            "regionInstanceId"));
            Map<String, Demand> selected = new LinkedHashMap<>();
            for (AbsenceRead read : reads) {
                PortOccurrence target = new PortOccurrence(
                        new InvocationKey(regionOf(read.inputPort),
                                fatalInstance), read.inputPort);
                for (ResolvedEdge edge : graph.selectedEdges.values()) {
                    JsonObject binding = edge.binding;
                    if (!target.equals(new PortOccurrence(
                            new InvocationKey(string(binding, "toRegion"),
                                    bindingTargetInstance(binding)),
                            bindingTargetInput(binding)))) {
                        continue;
                    }
                    String output = bindingSourceOutput(binding);
                    if (ports.sort(read.inputPort) != Sort.MAP
                            || ports.sort(output) != Sort.MAP
                            || !hasAssociativeRemovalOnSpine(
                            edge.summary.toJson(), output)) {
                        continue;
                    }
                    PortOccurrence source = new PortOccurrence(
                            new InvocationKey(bindingSourceRegion(binding),
                                    bindingSourceInstance(binding)), output);
                    Demand demand = new Demand(read.pathOrdinal, target,
                            source, new ResolvedBindingKey(binding),
                            read.keyExpression);
                    selected.putIfAbsent(demand.identity(), demand);
                }
            }
            return new FatalAbsenceMutationWitness(
                    new ArrayList<>(selected.values()));
        }

        private static void collectAbsenceReads(
                JsonElement expression, int pathOrdinal, PortIndex ports,
                List<AbsenceRead> result) {
            if (expression == null || !expression.isJsonObject()) return;
            JsonObject object = expression.getAsJsonObject();
            if ("BinaryExpression".equals(string(object, "_type"))
                    && "==".equals(string(object, "_op"))) {
                JsonElement left = object.get("_left");
                JsonElement right = object.get("_right");
                JsonObject read = associativeReadComparedWithNull(left,
                        right);
                if (read == null) {
                    read = associativeReadComparedWithNull(right, left);
                }
                if (read != null) {
                    String input = portInReceiver(read.get("receiver"),
                            ports);
                    JsonArray arguments = array(read, "arguments");
                    if (!input.isEmpty() && ports.isInput(input)
                            && arguments.size() == 1) {
                        result.add(new AbsenceRead(pathOrdinal, input,
                                arguments.get(0)));
                        return;
                    }
                }
            }
            for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
                collectAbsenceReads(entry.getValue(), pathOrdinal, ports,
                        result);
            }
        }

        private static JsonObject associativeReadComparedWithNull(
                JsonElement candidate, JsonElement other) {
            if (!recordedNull(other) || candidate == null
                    || !candidate.isJsonObject()) return null;
            JsonObject read = candidate.getAsJsonObject();
            return ContainerSmtCodec.EXPRESSION_TYPE.equals(
                    string(read, "_type"))
                    && "ASSOCIATIVE".equals(string(read, "shape"))
                    && "READ".equals(string(read, "operation"))
                    ? read : null;
        }

        private static boolean recordedNull(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) {
                return false;
            }
            JsonObject object = expression.getAsJsonObject();
            return "SymbolExpression".equals(string(object, "_type"))
                    && "N".equals(string(object, "_exp"));
        }

        private static String portInReceiver(JsonElement expression,
                                             PortIndex ports) {
            if (expression == null) return "";
            if (expression.isJsonArray()) {
                for (JsonElement item : expression.getAsJsonArray()) {
                    String found = portInReceiver(item, ports);
                    if (!found.isEmpty()) return found;
                }
                return "";
            }
            if (!expression.isJsonObject()) return "";
            JsonObject object = expression.getAsJsonObject();
            if ("SymbolExpression".equals(string(object, "_type"))) {
                return findPort(string(object, "_exp"), ports);
            }
            JsonElement receiver = object.get("receiver");
            return receiver == null ? ""
                    : portInReceiver(receiver, ports);
        }

        private static boolean hasAssociativeRemovalOnSpine(
                JsonObject summary, String output) {
            for (JsonElement caseElement : array(
                    object(summary, "regionRelation"), "cases")) {
                if (!caseElement.isJsonObject()) continue;
                JsonElement cursor = object(caseElement.getAsJsonObject(),
                        "outputExpressions").get(output);
                while (cursor != null && cursor.isJsonObject()) {
                    JsonObject relation = cursor.getAsJsonObject();
                    if (!ContainerSmtCodec.EXPRESSION_TYPE.equals(
                            string(relation, "_type"))
                            || !"ASSOCIATIVE".equals(
                            string(relation, "shape"))) {
                        break;
                    }
                    String operation = string(relation, "operation");
                    if ("REMOVE".equals(operation)
                            || "REMOVE_AT".equals(operation)) {
                        return true;
                    }
                    if (!"PUT".equals(operation)) break;
                    cursor = relation.get("receiver");
                }
            }
            return false;
        }

        private Set<String> outputsFor(InvocationKey invocation) {
            Set<String> result = new LinkedHashSet<>();
            for (Demand demand : demands) {
                if (demand.matchesInvocation(invocation)) {
                    result.add(demand.source.portId);
                }
            }
            return result;
        }

        private void addEffect(PortOccurrence source,
                               RemovalCaseEffect effect) {
            effects.computeIfAbsent(source,
                    ignored -> new ArrayList<>()).add(effect);
        }

        private void connect(Emitter.VersionedWriter writer,
                             PortOccurrence target, String writerGuard,
                             String targetState) {
            List<RemovalCaseEffect> candidates = effects.get(writer.source);
            if (candidates == null) return;
            for (Demand demand : demands) {
                if (!demand.target.equals(target)
                        || !demand.binding.equals(
                        new ResolvedBindingKey(writer.binding))
                        || demand.pathTerm.isEmpty()
                        || demand.keyTerm.isEmpty()) {
                    continue;
                }
                for (RemovalCaseEffect effect : candidates) {
                    clauses.add(and(Arrays.asList(demand.pathTerm,
                            writerGuard, effect.selector,
                            demand.keyPrecondition, effect.precondition,
                            "(= " + effect.removedKey + " "
                                    + demand.keyTerm + ")",
                            "(not (assoc_has " + targetState + " "
                                    + demand.keyTerm + "))")));
                }
            }
        }

        private JsonObject manifest() {
            JsonObject result = new JsonObject();
            result.addProperty("authority",
                    "EXACT_FATAL_ABSENCE_MUTATION_WITNESS_V1");
            result.addProperty("state", demands.isEmpty()
                    ? "NOT_APPLICABLE" : clauses.isEmpty()
                    ? "GAP" : "PINNED");
            result.addProperty("clauseCount", clauses.size());
            return result;
        }

        private static final class AbsenceRead {
            private final int pathOrdinal;
            private final String inputPort;
            private final JsonElement keyExpression;

            private AbsenceRead(int pathOrdinal, String inputPort,
                                JsonElement keyExpression) {
                this.pathOrdinal = pathOrdinal;
                this.inputPort = inputPort;
                this.keyExpression = keyExpression.deepCopy();
            }
        }

        private static final class Demand {
            private final int pathOrdinal;
            private final PortOccurrence target;
            private final PortOccurrence source;
            private final ResolvedBindingKey binding;
            private final JsonElement keyExpression;
            private String pathTerm = "";
            private String keyTerm = "";
            private String keyPrecondition = "true";

            private Demand(int pathOrdinal, PortOccurrence target,
                           PortOccurrence source,
                           ResolvedBindingKey binding,
                           JsonElement keyExpression) {
                this.pathOrdinal = pathOrdinal;
                this.target = target;
                this.source = source;
                this.binding = binding;
                this.keyExpression = keyExpression.deepCopy();
            }

            private boolean matchesInvocation(InvocationKey invocation) {
                return source.invocation.regionId.equals(invocation.regionId)
                        && (source.invocation.instanceId.equals(
                        invocation.instanceId)
                        || invocation.instanceId.startsWith(
                        source.invocation.instanceId + "#boundedStep"));
            }

            private String identity() {
                return pathOrdinal + "\n" + target + "\n" + source
                        + "\n" + binding.hashCode();
            }
        }

        private static final class RemovalCaseEffect {
            private final String selector;
            private final String removedKey;
            private final String precondition;

            private RemovalCaseEffect(String selector,
                                      String removedKey,
                                      String precondition) {
                this.selector = selector;
                this.removedKey = removedKey;
                this.precondition = precondition;
            }
        }
    }

    private static final class ResolvedBindingKey {
        private final String edgeId;
        private final String evidenceKind;
        private final String fromInstance;
        private final String fromOutput;
        private final String toInstance;
        private final String toInput;
        private final long writerEventSeq;
        private final long readerEventSeq;
        private final long callerSiteEventSeq;
        private final long sendEventSeq;
        private final long receiveEventSeq;

        private ResolvedBindingKey(JsonObject binding) {
            this.edgeId = string(binding, "edgeId");
            this.evidenceKind = string(binding, "evidenceKind");
            this.fromInstance = bindingSourceInstance(binding);
            this.fromOutput = bindingSourceOutput(binding);
            this.toInstance = bindingTargetInstance(binding);
            this.toInput = bindingTargetInput(binding);
            this.writerEventSeq = longInteger(binding,
                    "writerEventSeq", -1L);
            this.readerEventSeq = longInteger(binding,
                    "readerEventSeq", -1L);
            this.callerSiteEventSeq = longInteger(binding,
                    "callerSiteEventSeq", -1L);
            this.sendEventSeq = longInteger(binding,
                    "sendEventSeq", -1L);
            this.receiveEventSeq = longInteger(binding,
                    "receiveEventSeq", -1L);
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof ResolvedBindingKey)) return false;
            ResolvedBindingKey value = (ResolvedBindingKey) other;
            return edgeId.equals(value.edgeId)
                    && evidenceKind.equals(value.evidenceKind)
                    && fromInstance.equals(value.fromInstance)
                    && fromOutput.equals(value.fromOutput)
                    && toInstance.equals(value.toInstance)
                    && toInput.equals(value.toInput)
                    && writerEventSeq == value.writerEventSeq
                    && readerEventSeq == value.readerEventSeq
                    && callerSiteEventSeq == value.callerSiteEventSeq
                    && sendEventSeq == value.sendEventSeq
                    && receiveEventSeq == value.receiveEventSeq;
        }

        @Override
        public int hashCode() {
            return Objects.hash(edgeId, evidenceKind, fromInstance,
                    fromOutput, toInstance, toInput, writerEventSeq,
                    readerEventSeq, callerSiteEventSeq, sendEventSeq,
                    receiveEventSeq);
        }
    }

    private static final class ResolvedSummaryGraph {
        private final String fatalRegion;
        private final String fatalInstance;
        private final ProducerDemandIndex demands;
        private final Map<InvocationKey, RelationSummary>
                selectedRegionSummaries = new LinkedHashMap<>();
        private final Map<ResolvedBindingKey, ResolvedEdge> selectedEdges =
                new LinkedHashMap<>();
        private final Deque<ProducerKey> pending = new ArrayDeque<>();
        private final Set<String> relevantRegions = new LinkedHashSet<>();
        private final Set<String> gaps = new LinkedHashSet<>();

        private ResolvedSummaryGraph(String fatalRegion,
                                     String fatalInstance,
                                     ProducerDemandIndex knownDemands) {
            this.fatalRegion = firstNonBlank(fatalRegion);
            this.fatalInstance = firstNonBlank(fatalInstance);
            this.demands = new ProducerDemandIndex(knownDemands);
            this.relevantRegions.add(this.fatalRegion);
        }

        private void registerDemand(String region, String instance,
                                    String output) {
            demands.add(region, instance, output);
        }

        private Set<String> demandedOutputs(String region, String instance,
                                            String requiredOutput) {
            registerDemand(region, instance, requiredOutput);
            return demands.outputs(region, instance);
        }

        private void addEdge(ResolvedEdge edge) {
            String edgeId = string(edge.binding, "edgeId");
            if (!edgeId.isEmpty()) {
                selectedEdges.putIfAbsent(
                        new ResolvedBindingKey(edge.binding), edge);
            }
        }

        private void addDirectBindingIfPresent(ProducerKey source,
                                               String targetRegion,
                                               String targetInstance,
                                               String targetInput,
                                               JsonObject expectedRelation,
                                               JsonObject expectedBinding,
                                               String expectedRelationKind) {
            RelationSummary summary = selectedRegionSummaries.get(
                    source.invocation());
            if (summary == null
                    || !summary.outputClosure().outputPorts().contains(
                    source.outputPort)) {
                return;
            }
            List<JsonObject> matches = matchingBindings(summary, source,
                    targetRegion, targetInstance, targetInput,
                    expectedRelation, expectedBinding, expectedRelationKind);
            if (matches.size() == 1) {
                addEdge(new ResolvedEdge(summary, matches.get(0)));
            } else if (matches.size() > 1) {
                gaps.add("AmbiguousDirectEdgeBinding:" + source + "->"
                        + targetRegion + "@" + targetInstance + ":"
                        + targetInput);
            }
        }

        private Set<String> staticEdgeIds() {
            Set<String> result = new LinkedHashSet<>();
            for (ResolvedEdge edge : selectedEdges.values()) {
                String edgeId = string(edge.binding, "edgeId");
                if (!edgeId.isEmpty()) result.add(edgeId);
            }
            return result;
        }

        private boolean containsBinding(JsonObject relation,
                                        JsonObject binding) {
            String from = string(relation, "fromEndpoint");
            String to = string(relation, "toEndpoint");
            for (ResolvedEdge selected : selectedEdges.values()) {
                JsonObject candidate = selected.binding;
                String kind = bindingRelationKind(candidate);
                if (from.equals(bindingSourceOutput(candidate))
                        && to.equals(bindingTargetInput(candidate))
                        && bindingSourceInstance(binding).equals(
                        bindingSourceInstance(candidate))
                        && bindingTargetInstance(binding).equals(
                        bindingTargetInstance(candidate))
                        && sameCompositionRelation(candidate, relation, kind)
                        && sameCompositionRelation(candidate, binding, kind)) {
                    return true;
                }
            }
            return false;
        }

    }

    private static JsonObject boundedContext(JsonObject source,
                                             ResolvedSummaryGraph graph) {
        JsonObject result = source.deepCopy();
        for (String field : new String[]{"equalityRelations",
                "versionedStateMerges"}) {
            JsonArray selected = new JsonArray();
            for (JsonElement element : array(source, field)) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject relation = element.getAsJsonObject();
                JsonObject exact = selectedContextRelation(relation, graph);
                if (exact.size() > 0) selected.add(exact);
            }
            result.add(field, selected);
        }

        JsonArray direct = array(result, "versionedStateMerges");
        JsonArray selectedGroups = new JsonArray();
        for (JsonElement element : array(source,
                "alternativeWriterGroups")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject group = element.getAsJsonObject();
            JsonArray selected = new JsonArray();
            JsonArray alternatives = array(group, "alternatives");
            for (JsonElement alternative : alternatives) {
                if (!alternative.isJsonObject()) {
                    continue;
                }
                JsonObject relation = alternative.getAsJsonObject();
                JsonObject exact = selectedContextRelation(relation, graph);
                if (exact.size() > 0) selected.add(exact);
            }
            if (selected.size() == 1) {
                direct.add(selected.get(0));
            } else if (selected.size() > 1) {
                JsonObject copy = group.deepCopy();
                copy.add("alternatives", selected);
                selectedGroups.add(copy);
            }
        }
        result.add("versionedStateMerges", direct);
        result.add("alternativeWriterGroups", selectedGroups);
        return result;
    }

    private static JsonObject selectedContextRelation(
            JsonObject relation, ResolvedSummaryGraph graph) {
        JsonArray bindings = new JsonArray();
        for (JsonElement element : selectedBindings(relation)) {
            if (element.isJsonObject()
                    && graph.containsBinding(relation,
                    element.getAsJsonObject())) {
                bindings.add(element.deepCopy());
            }
        }
        if (bindings.size() == 0) return new JsonObject();
        JsonObject result = relation.deepCopy();
        result.add("selectedBindings", bindings);
        return result;
    }

    private static String regionOf(String endpoint) {
        if (endpoint == null) return "";
        int marker = endpoint.indexOf(".in.");
        if (marker < 0) marker = endpoint.indexOf(".out.");
        if (marker > 0) return endpoint.substring(0, marker);
        marker = endpoint.indexOf("::");
        return marker > 0 ? endpoint.substring(0, marker) : "";
    }

    private static String findPort(String rawSymbol, PortIndex ports) {
        for (String port : ports.longestFirst) {
            int index = rawSymbol.indexOf(port);
            while (index >= 0) {
                int end = index + port.length();
                boolean leftBoundary = index == 0
                        || rawSymbol.charAt(index - 1) == '_';
                boolean rightBoundary = end == rawSymbol.length()
                        || rawSymbol.charAt(end) == '_';
                if (leftBoundary && rightBoundary) return port;
                index = rawSymbol.indexOf(port, index + 1);
            }
        }
        return "";
    }

    private static String and(List<String> terms) {
        return booleanNary(terms, true);
    }

    private static String or(List<String> terms) {
        return booleanNary(terms, false);
    }

    private static String booleanNary(List<String> terms,
                                      boolean conjunction) {
        List<String> filtered = new ArrayList<>();
        for (String term : terms) {
            String value = term == null ? "" : term.trim();
            if (value.isEmpty()
                    || (conjunction ? "true" : "false").equals(value)) continue;
            if ((conjunction ? "false" : "true").equals(value)) return value;
            filtered.add(term);
        }
        if (filtered.isEmpty()) return conjunction ? "true" : "false";
        if (filtered.size() == 1) return filtered.get(0);
        StringBuilder result = new StringBuilder(conjunction
                ? "(and" : "(or");
        for (String term : filtered) result.append(' ').append(term);
        return result.append(')').toString();
    }

    /**
     * Scheduler-certified description of one repeatable container
     * transition.  It carries identity only; all state and leaf equations
     * still come from the imported VM relation.
     */
    private static final class BoundedTimelineStep {
        private static final String KIND =
                "SINGLE_WRITER_BOUNDED_CONTAINER_TIMELINE_STEP";
        private static final String AUTHORITY =
                "EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1";
        private final String preStatePort;
        private final String postStatePort;
        private final long containerObjectId;
        private final int bound;
        private final String blocker;

        private BoundedTimelineStep(String preStatePort,
                                    String postStatePort,
                                    long containerObjectId,
                                    int bound, String blocker) {
            this.preStatePort = preStatePort;
            this.postStatePort = postStatePort;
            this.containerObjectId = containerObjectId;
            this.bound = bound;
            this.blocker = blocker;
        }

        private static BoundedTimelineStep from(RelationSummary summary) {
            JsonObject selected = null;
            for (OutputClosureContract.Member member
                    : summary.outputClosure().members()) {
                JsonObject candidate = object(member.slice(),
                        "boundedContainerTimelineStep");
                if (candidate.size() == 0) continue;
                if (selected != null && !sameStep(selected, candidate)) {
                    return blocked("MULTIPLE_TIMELINE_WRITERS", summary);
                }
                selected = candidate;
            }
            if (selected == null) return null;
            if (integer(selected, "schemaVersion", -1) != 1
                    || !KIND.equals(string(selected, "kind"))
                    || !"ENGINE_STATE_CHAIN_BOUND_V1".equals(string(selected,
                    "boundAuthority"))
                    || !"ONE_DEFINITION_INVOCATION".equals(string(selected,
                    "transitionGranularity"))
                    || !"EXACT_PRE_STATE_TO_NORMAL_DEFINITION_EXIT_V1"
                    .equals(string(selected, "transitionAuthority"))
                    || !"SINGLE_WRITER_REQUIRED".equals(string(selected,
                    "writerPolicy"))) {
                return blocked("MALFORMED_TIMELINE_STEP", summary);
            }
            if (!"PROVED".equals(string(selected, "admission"))) {
                return blocked(firstNonBlank(string(selected, "blocker"),
                        "TIMELINE_STEP_NOT_PROVED"), summary);
            }
            String pre = string(selected, "preStatePort");
            String post = string(selected, "postStatePort");
            String token = string(selected, "memberToken");
            String lane = string(selected, "writerLaneId");
            long container = longInteger(selected, "containerObjectId", 0L);
            JsonArray projections = array(selected, "memberProjections");
            if (!AUTHORITY.equals(string(selected, "authority"))
                    || pre.isEmpty() || post.isEmpty() || token.isEmpty()
                    || lane.isEmpty() || container <= 0L
                    || !summary.outputClosure().executionScope()
                    .inputPorts().contains(pre)
                    || !summary.outputClosure().outputPorts().contains(post)
                    || !validProjectionPair(projections, token, lane,
                    container)) {
                return blocked("INCOMPLETE_TIMELINE_MEMBER_PROJECTION",
                        summary);
            }
            int bound = integer(selected, "stateChainBound", -1);
            if (bound != LoopBoundPolicy.MAX_STATE_TIMELINE_TRANSITIONS) {
                return blocked("INVALID_STATE_CHAIN_BOUND", summary);
            }
            return new BoundedTimelineStep(pre, post, container, bound, "");
        }

        private static boolean sameStep(JsonObject left,
                                        JsonObject right) {
            return left.equals(right);
        }

        private static boolean validProjectionPair(JsonArray projections,
                                                   String token,
                                                   String lane,
                                                   long container) {
            JsonObject pre = null;
            JsonObject post = null;
            for (JsonElement element : projections) {
                if (!element.isJsonObject()) return false;
                JsonObject projection = element.getAsJsonObject();
                if (!token.equals(string(projection, "memberToken"))
                        || !lane.equals(string(projection, "writerLaneId"))
                        || container != longInteger(projection,
                        "containerObjectId", 0L)
                        || !AUTHORITY.equals(string(projection,
                        "identityAuthority"))) {
                    return false;
                }
                if ("PRE_STATE".equals(string(projection, "stateRole"))) {
                    if (pre != null) return false;
                    pre = projection;
                } else if ("POST_STATE".equals(string(projection,
                        "stateRole"))) {
                    if (post != null) return false;
                    post = projection;
                } else {
                    return false;
                }
            }
            return pre != null && post != null
                    && projectionLeaves(pre).equals(projectionLeaves(post))
                    && projectionLeaves(pre).contains("PRESENT\nboolean\n");
        }

        private static Set<String> projectionLeaves(JsonObject projection) {
            Set<String> result = new LinkedHashSet<>();
            for (JsonElement element : array(projection, "leaves")) {
                if (!element.isJsonObject()) {
                    result.add("MALFORMED");
                    continue;
                }
                JsonObject leaf = element.getAsJsonObject();
                String kind = string(leaf, "kind");
                String javaType = string(leaf, "javaType");
                String field = string(leaf, "field");
                if (kind.isEmpty() || javaType.isEmpty()
                        || "VALUE_FIELD".equals(kind) && field.isEmpty()) {
                    result.add("MALFORMED");
                } else {
                    result.add(kind + "\n" + javaType + "\n" + field);
                }
            }
            return result;
        }

        private static BoundedTimelineStep blocked(
                String blocker, RelationSummary summary) {
            int bound = LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS;
            try {
                bound = LoopBoundPolicy.decode(summary.toJson())
                        .maxBackedgeTraversals();
            } catch (IllegalArgumentException ignored) {
                // The named blocker below closes the formula.
            }
            return new BoundedTimelineStep("", "", 0L, bound, blocker);
        }

        private String channelIdentity(RelationSummary summary) {
            // This identity is local to the exact selected occurrence.  The
            // member token names one put inside the state; it must never
            // split one container timeline into a channel per member.
            return summary.regionInstanceId() + "\n" + preStatePort
                    + "\n" + postStatePort;
        }
    }

    private static final class Emitter {
        private final PortIndex ports;
        private final FatalAbsenceMutationWitness failureWitness;
        private final List<String> preamble = new ArrayList<>();
        private final List<String> declarations = new ArrayList<>();
        private final List<String> assertions = new ArrayList<>();
        private final Set<String> declarationKeys = new LinkedHashSet<>();
        private final Set<String> assertionNames = new LinkedHashSet<>();
        private final Map<String, RawSymbol> rawSymbols =
                new LinkedHashMap<>();
        /**
         * Java references whose declared type is String need two solver
         * views.  The String-sorted term carries the characters while this
         * companion Bool carries reference nullness.  Keeping the companion
         * keyed by the same case-scoped raw identity prevents one guarded
         * path from constraining another path's engine-local symbol.
         */
        private final Map<PortOccurrence, Sort> portSortOverrides =
                new LinkedHashMap<>();
        private final Map<PortOccurrence, Sort> declaredPortSorts =
                new LinkedHashMap<>();
        private final Set<PortOccurrence> boundPorts = new LinkedHashSet<>();
        private final Set<PortOccurrence> mentionedPorts =
                new LinkedHashSet<>();
        private final Set<String> unsupported = new LinkedHashSet<>();
        private final Set<String> canonicalPortTermBindings =
                new LinkedHashSet<>();
        private final Set<String> javaIntRangeAssertions =
                new LinkedHashSet<>();
        private final Set<String> javaIntegralRangeAssertions =
                new LinkedHashSet<>();
        private final Map<PortOccurrence, EqualityBoundExpression>
                exactEqualityBoundExpressions = new LinkedHashMap<>();
        private final Set<PortOccurrence>
                ambiguousEqualityBoundExpressionPorts =
                new LinkedHashSet<>();
        private final Set<PortOccurrence> validatedIncomingEdgeInputs =
                new LinkedHashSet<>();
        private final Map<PortOccurrence, Sort>
                validatedIncomingEdgeInputSorts =
                new LinkedHashMap<>();
        private final Set<String> emittedExactCausalInputAliasKeys =
                new LinkedHashSet<>();
        private final List<PortOccurrence[]> portEqualities =
                new ArrayList<>();
        private final Set<String> emittedVersionedBindings =
                new LinkedHashSet<>();
        private final Map<PortOccurrence, TimelineOutputExpansion>
                boundedTimelineOutputs = new LinkedHashMap<>();
        private final Set<String> declaredOutputVersionChoices =
                new LinkedHashSet<>();
        private final Set<String> declaredReferenceIdentities =
                new LinkedHashSet<>();
        private final Set<String> suppliedInputs = new LinkedHashSet<>();
        private final Set<PortOccurrence> suppliedInputOccurrences =
                new LinkedHashSet<>();
        private final Map<String, JsonObject> canonicalPortOccurrences =
                new LinkedHashMap<>();
        /**
         * Solver terms read by the final branch condition of each fatal
         * path.  These are captured while lowering the real expression, so
         * the audit consumes the exact terms and sorts emitted to SMT rather
         * than reconstructing them from source names.
         */
        private final Map<String, FatalOperand> fatalOperands =
                new LinkedHashMap<>();
        /**
         * Exact, top-level equalities asserted by each selected fatal path
         * prefix.  They let the audit follow an engine-local temporary back
         * to a dynamic input port without guessing from names or values.
         */
        private final Map<Integer, List<FatalPrefixEquality>>
                fatalPrefixEqualities = new LinkedHashMap<>();
        /** Exact value-carrying named assertions, indexed by runtime edge. */
        private final List<ProducerVersionBinding> producerVersionBindings =
                new ArrayList<>();
        private boolean capturingFatalOperands;
        private int capturedFatalPathOrdinal = -1;
        private int nextFatalOperandOrdinal;
        private String fatalPrefixAssertionName = "";
        private String fatalPrefixAssertionTerm = "";
        private String fatalPathAssertionName = "";
        private String fatalPathAssertionTerm = "";
        private final Map<Integer, String> fatalPathPrefixes =
                new LinkedHashMap<>();
        private final Set<String> fatalDependentAssertionNames =
                new LinkedHashSet<>();
        /** Definedness facts collected while lowering one container term. */
        private Set<String> currentContainerRequirements;
        private String currentGuard = "";
        private String currentSymbolScope = "global";
        private InvocationKey currentInvocation;

        private Emitter(PortIndex ports, InvocationKey fatalInvocation,
                        FatalAbsenceMutationWitness failureWitness) {
            this.ports = ports;
            this.currentInvocation = fatalInvocation;
            this.failureWitness = failureWitness;
        }

        private InvocationKey enterInvocation(InvocationKey invocation) {
            InvocationKey previous = currentInvocation;
            currentInvocation = invocation;
            return previous;
        }

        private void restoreInvocation(InvocationKey invocation) {
            currentInvocation = invocation;
        }

        private PortOccurrence currentOccurrence(String port) {
            return new PortOccurrence(new InvocationKey(regionOf(port),
                    currentInvocation.instanceId), port);
        }

        private PortOccurrence occurrence(String instance, String port) {
            return new PortOccurrence(new InvocationKey(regionOf(port),
                    instance), port);
        }

        private String enterSymbolScope(String scope) {
            String previous = currentSymbolScope;
            currentSymbolScope = firstNonBlank(scope, "global");
            return previous;
        }

        private void restoreSymbolScope(String scope) {
            currentSymbolScope = firstNonBlank(scope, "global");
        }

        private void beginFatalOperandCapture(int pathOrdinal) {
            capturingFatalOperands = true;
            capturedFatalPathOrdinal = pathOrdinal;
        }

        private void endFatalOperandCapture() {
            capturingFatalOperands = false;
            capturedFatalPathOrdinal = -1;
        }

        private void begin(JsonObject fatal) {
            preamble.add("; GraphChecker composed concolic query");
            preamble.add("; fatal region: " + string(fatal, "regionId"));
            preamble.add("(set-logic ALL)");
            preamble.add("(declare-sort Ref 0)");
            preamble.add(ContainerSmtCodec.valueDatatypeDeclaration());
            preamble.add("(declare-const nullRef Ref)");
            preamble.addAll(ContainerSmtCodec.preamble());
            // SMT-LIB's str.from_int is defined only for non-negative
            // integers.  Java's decimal Integer.toString additionally emits
            // a leading '-' for negative values.  Keeping this definition in
            // the common emitter lets the codec proof below remain ordinary,
            // solver-visible string semantics instead of an unconstrained UF.
            preamble.add("(define-fun java_int_to_string ((i Int)) String"
                    + " (ite (< i 0)"
                    + " (str.++ \"-\" (str.from_int (- i)))"
                    + " (str.from_int i)))");
            // Java integral bytecodes wrap in two's-complement arithmetic.
            // Keeping the public scalar carrier as SMT Int is convenient for
            // ports and model materialization, but raw SMT +, -, and * would
            // otherwise silently use unbounded mathematical integers.
            preamble.add(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION);
            preamble.add(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION);
        }

        private void bindFatalPath(int pathOrdinal, String pathTerm) {
            for (FatalAbsenceMutationWitness.Demand demand
                    : failureWitness.demands) {
                if (demand.pathOrdinal != pathOrdinal) continue;
                Term nativeKey = term(demand.keyExpression, null);
                Term key = asValue(nativeKey,
                        expressionJavaType(demand.keyExpression));
                if (key.sort != Sort.VALUE) {
                    unsupported.add("FatalAbsenceKeySortGap:"
                            + demand.target);
                    continue;
                }
                demand.pathTerm = pathTerm;
                demand.keyTerm = key.text;
                demand.keyPrecondition = key.precondition;
            }
        }

        private void bindFatalPathAssertion(String pathTerm) {
            fatalPathAssertionTerm = pathTerm;
            fatalPathAssertionName = assertNamed("fatal_path", pathTerm);
            fatalDependentAssertionNames.add(fatalPathAssertionName);
        }

        private void bindFatalPathPrefix(int pathOrdinal,
                                         String prefixTerm) {
            fatalPathPrefixes.put(pathOrdinal,
                    firstNonBlank(prefixTerm, "true"));
        }

        private void bindFatalPrefixAssertion(String prefixTerm) {
            fatalPrefixAssertionTerm = prefixTerm;
            fatalPrefixAssertionName = assertNamed(
                    "fatal_path_prefix", prefixTerm);
        }

        private void captureFatalOperand(JsonObject expression, Term term) {
            if (!capturingFatalOperands || term == null) return;
            String raw = string(expression, "_exp");
            // These are fixed engine literals, not solver operands.
            if ("N".equals(raw) || "V".equals(raw)) return;
            String port = findPort(raw);
            PortOccurrence occurrence = port.isEmpty() ? null
                    : currentOccurrence(port);
            String javaType = string(expression, "_java_type");
            Term pin = term.sort == Sort.VALUE || term.sort == Sort.MAP
                    || term.sort == Sort.ARRAY_VALUE
                    ? term : asValue(term, javaType);
            String key = capturedFatalPathOrdinal + "\u0000" + term.text
                    + "\u0000" + term.sort.name();
            if (fatalOperands.containsKey(key)) return;
            String operandId = "fatal_operand_" + capturedFatalPathOrdinal
                    + "_" + nextFatalOperandOrdinal++;
            fatalOperands.put(key, new FatalOperand(operandId,
                    capturedFatalPathOrdinal,
                    term.text, term.sort, pin.text, pin.sort, occurrence));
        }

        private void recordFatalPrefixEquality(
                int pathOrdinal, JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return;
            JsonObject object = expression.getAsJsonObject();
            if ("MethodExpression".equals(string(object, "_type"))
                    && isJavaParseInt(string(object, "_name"))) {
                SplitPiece source = exactParseIntIntegerSource(object);
                PortOccurrence sourceOccurrence =
                        exactIntegerPieceOccurrence(source);
                if (sourceOccurrence == null) return;
                Term result = term(object.get("_res_exp"), Sort.INT);
                Term value = integerPieceTerm(source);
                if (result.sort != value.sort) return;
                fatalPrefixEqualities.computeIfAbsent(pathOrdinal,
                        ignored -> new ArrayList<>()).add(
                        new FatalPrefixEquality(result.text, result.sort,
                                null, value.text, value.sort,
                                sourceOccurrence));
                return;
            }
            if (!"BinaryExpression".equals(string(object, "_type"))
                    || !"==".equals(string(object, "_op"))) {
                return;
            }
            JsonElement leftExpression = object.get("_left");
            JsonElement rightExpression = object.get("_right");
            PortOccurrence leftOccurrence = directPortOccurrence(
                    leftExpression);
            PortOccurrence rightOccurrence = directPortOccurrence(
                    rightExpression);
            if (leftOccurrence == null && rightOccurrence == null) return;

            Term left = term(leftExpression, null);
            Term right = term(rightExpression, left.sort);
            if (left.sort != right.sort) return;
            fatalPrefixEqualities.computeIfAbsent(pathOrdinal,
                    ignored -> new ArrayList<>()).add(
                    new FatalPrefixEquality(left.text, left.sort,
                            leftOccurrence, right.text, right.sort,
                            rightOccurrence));
        }

        /**
         * Returns the exact integer witness recognized by the parse/split
         * codec.  This is the same structural proof used to lower parseInt;
         * it does not infer lineage from a concrete value or a symbol name.
         */
        private SplitPiece exactParseIntIntegerSource(JsonObject expression) {
            JsonArray params = array(expression, "_param_list");
            if (params.size() != 1 && params.size() != 2) return null;
            if (params.size() == 2) {
                Integer radix = exactIntLiteral(params.get(1));
                if (radix == null || radix != 10) return null;
            }
            SplitSegment segment = exactSplitSegment(params.get(0));
            return segment.complete() ? segment.singleIntegerPiece() : null;
        }

        private PortOccurrence exactIntegerPieceOccurrence(
                SplitPiece piece) {
            if (piece == null || piece.integerSource == null
                    || !piece.integerSource.isJsonObject()) {
                return null;
            }
            JsonObject source = piece.integerSource.getAsJsonObject();
            if (!"SymbolExpression".equals(string(source, "_type"))) {
                return null;
            }
            String port = findPort(string(source, "_exp"));
            if (port.isEmpty()) return null;
            InvocationKey invocation = piece.integerInvocation == null
                    ? currentInvocation : piece.integerInvocation;
            return occurrence(invocation.instanceId, port);
        }

        private PortOccurrence directPortOccurrence(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return null;
            JsonObject object = expression.getAsJsonObject();
            if (!"SymbolExpression".equals(string(object, "_type"))) {
                return null;
            }
            String port = findPort(string(object, "_exp"));
            return port.isEmpty() ? null : currentOccurrence(port);
        }

        private PortOccurrence exactFatalOperandOccurrence(
                FatalOperand operand) {
            if (operand.occurrence != null) return operand.occurrence;
            List<FatalPrefixEquality> equalities = fatalPrefixEqualities.get(
                    operand.pathOrdinal);
            if (equalities == null || equalities.isEmpty()) return null;

            Set<String> pending = new LinkedHashSet<>();
            Set<String> visited = new LinkedHashSet<>();
            Set<PortOccurrence> occurrences = new LinkedHashSet<>();
            pending.add(fatalEqualityTerm(operand.solverTerm,
                    operand.solverSort));
            while (!pending.isEmpty()) {
                String current = pending.iterator().next();
                pending.remove(current);
                if (!visited.add(current)) continue;
                for (FatalPrefixEquality equality : equalities) {
                    String left = fatalEqualityTerm(equality.leftTerm,
                            equality.leftSort);
                    String right = fatalEqualityTerm(equality.rightTerm,
                            equality.rightSort);
                    if (current.equals(left)) {
                        if (equality.leftOccurrence != null) {
                            occurrences.add(equality.leftOccurrence);
                        }
                        if (equality.rightOccurrence != null) {
                            occurrences.add(equality.rightOccurrence);
                        }
                        pending.add(right);
                    } else if (current.equals(right)) {
                        if (equality.leftOccurrence != null) {
                            occurrences.add(equality.leftOccurrence);
                        }
                        if (equality.rightOccurrence != null) {
                            occurrences.add(equality.rightOccurrence);
                        }
                        pending.add(left);
                    }
                }
            }
            return occurrences.size() == 1
                    ? occurrences.iterator().next() : null;
        }

        private String fatalEqualityTerm(String term, Sort sort) {
            return sort.name() + "\u0000" + term;
        }

        /**
         * Catalogs a producer's exact String output expression for a
         * consumer input only when the selected instance edge carries the
         * same trusted configured protocol mapping that will later be
         * asserted by {@link #mergeEdgeBindings(Collection)}. This is an
         * expression-level view of an ordinary merge edge, not a protocol
         * adapter: it lets sound Java codec reductions inspect the expression
         * on the other side of an already-proved equality.
         */
        private void registerExactEqualityBoundExpressions(
                Collection<ResolvedEdge> edges) {
            for (ResolvedEdge edge : edges) {
                JsonObject binding = edge.binding;
                String output = bindingSourceOutput(binding);
                String input = bindingTargetInput(binding);
                if (!AutomaticRegionEdge
                        .trustedRuntimeValueEqualityBinding(binding)
                        || !ports.contains(output)
                        || !ports.contains(input)) {
                    continue;
                }
                JsonElement value = caseInvariantOutputExpression(
                        edge.summary.toJson(), output);
                // The consumer must be reading a declared String, and the
                // producer's own expression must prove it built one.  That
                // expression is the evidence substituted into the codec
                // proof, and it is stronger than the producer port's
                // declaration - which a local-valued cell may not carry at
                // all.  A declaration that disagrees still stops here.
                if (value == null || !value.isJsonObject()
                        || !provablyStringValued(value)
                        || !declaredString(input)
                        || contradictsString(output)) {
                    continue;
                }
                EqualityBoundExpression candidate =
                        new EqualityBoundExpression(input, output,
                                bindingSourceInstance(binding),
                                bindingTargetInstance(binding), value);
                PortOccurrence target = occurrence(
                        bindingTargetInstance(binding), input);
                EqualityBoundExpression previous =
                        exactEqualityBoundExpressions.get(target);
                if (previous == null
                        && !ambiguousEqualityBoundExpressionPorts.contains(
                        target)) {
                    exactEqualityBoundExpressions.put(target, candidate);
                } else if (previous != null
                        && !previous.sameProofAndExpression(candidate)) {
                    exactEqualityBoundExpressions.remove(target);
                    ambiguousEqualityBoundExpressionPorts.add(target);
                    unsupported.add(
                            "AmbiguousExactEqualityBoundExpression:" + target);
                }
            }
        }

        /** Whether Java declares this port's value to be a String. */
        private boolean declaredString(String port) {
            return sortOfJava(declaredPortJavaType(port)) == Sort.STRING;
        }

        /** Whether a known declaration rules a String value out. */
        private boolean contradictsString(String port) {
            String declared = declaredPortJavaType(port);
            return !declared.isEmpty()
                    && sortOfJava(declared) != Sort.STRING;
        }

        /**
         * Reads one output's expression from a merged region relation.
         *
         * <p>{@link RelationSummary} publishes expressions per guarded case,
         * never at the summary root: a case owns both the path condition and
         * the bounded output version that produced its expression.  A reader
         * outside the case scope may therefore only use an expression every
         * case agrees on, because that is the one expression the producer
         * binds whichever case the solver selects.  Cases that disagree -
         * including the expanded bounded output versions - have no case-free
         * expression, and the reader keeps its own named gap instead.</p>
         */
        private JsonElement caseInvariantOutputExpression(JsonObject summary,
                                                          String port) {
            JsonElement direct = object(summary, "outputExpressions")
                    .get(port);
            if (direct != null) return direct;
            JsonArray cases = array(object(summary, "regionRelation"),
                    "cases");
            if (cases.size() == 0) return null;
            JsonElement selected = null;
            for (JsonElement element : cases) {
                if (!element.isJsonObject()) return null;
                JsonElement value = object(element.getAsJsonObject(),
                        "outputExpressions").get(port);
                if (value == null) return null;
                if (selected == null) {
                    selected = value;
                } else if (!CanonicalJson.render(selected).equals(
                        CanonicalJson.render(value))) {
                    return null;
                }
            }
            return selected;
        }

        private String constraint(JsonElement expression, String origin) {
            if (expression == null || !expression.isJsonObject()) {
                return unknownConstraint(origin, expression);
            }
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if (BoundedOutputVersions.isVersionSelection(object)) {
                return outputVersionSelection(object, origin);
            }
            if ("MethodExpression".equals(type)) {
                return methodConstraint(object);
            }
            Term term = term(expression, null);
            if (term.sort == Sort.BOOL) return condition(term);
            return unknownConstraint(origin + ": non-boolean " + type,
                    expression);
        }

        /**
         * Binds one relation case to one exported bounded output version.
         *
         * <p>The version choice is a solver variable per port occurrence,
         * bounded by the site-local export.  Each expanded case's guard says
         * {@code choice == ordinal}; with the ordinary exactly-one selector
         * partition this makes the solver pick exactly one exported version
         * per producer occurrence, and different alpha-renamed occurrences
         * choose independently.</p>
         */
        private String outputVersionSelection(JsonObject selection,
                                              String origin) {
            String port = string(selection, "outputPort");
            int ordinal = integer(selection, "versionOrdinal", -1);
            int bound = integer(selection, "versionBound", -1);
            if (port.isEmpty() || ordinal < 1 || bound < ordinal
                    || !ports.contains(port)) {
                return unknownConstraint(origin
                        + ": malformed output version selection", selection);
            }
            PortOccurrence occurrence = currentOccurrence(port);
            String choice = "output_version_choice__"
                    + smtName(String.valueOf(occurrence));
            if (declaredOutputVersionChoices.add(choice)) {
                declare(choice, Sort.INT);
                String previousGuard = currentGuard;
                currentGuard = "";
                try {
                    assertNamed(choice + "_bounds", "(and (<= 1 " + choice
                            + ") (<= " + choice + " " + bound + "))");
                } finally {
                    currentGuard = previousGuard;
                }
            }
            return "(= " + choice + " " + ordinal + ")";
        }

        /** A term may denote a Java expression that is defined only under a
         * reference guard (for example {@code s.length()} requires
         * {@code s != null}).  Keep that guard inside the expression so a
         * guarded-case selector owns it; emitting a top-level assertion while
         * constructing the selector would incorrectly constrain sibling
         * cases. */
        private String condition(Term term) {
            return and(Arrays.asList(term.precondition, term.text));
        }

        private Term dependent(Term result, Term... inputs) {
            List<String> values = new ArrayList<>();
            values.add(result.precondition);
            if (inputs != null) {
                for (Term input : inputs) {
                    if (input != null) values.add(input.precondition);
                }
            }
            return result.withPrecondition(and(values));
        }

        private String stringNonNull(Term term) {
            if (term.sort != Sort.STRING) return "false";
            return "false".equals(term.stringNullness) ? "true"
                    : "(not " + term.stringNullness + ")";
        }

        private String stringDereferencePrecondition(Term... strings) {
            List<String> values = new ArrayList<>();
            if (strings != null) {
                for (Term string : strings) {
                    if (string == null || string.sort != Sort.STRING) {
                        values.add("false");
                    } else {
                        values.add(string.precondition);
                        values.add(stringNonNull(string));
                    }
                }
            }
            return and(values);
        }

        /**
         * Lowers one recorded expression.
         *
         * <p>An operand slot the recording left out is not the Java null
         * reference: a recorded null is its own null symbol, and the two
         * appear side by side in the same relation.  Reading the omission
         * as null would state the one fact the record does not carry - and
         * it is the strongest fact available, because it decides every
         * later read of the value.  An absent operand is therefore a named
         * gap like any other unproven thing.</p>
         */
        private Term term(JsonElement expression, Sort expected) {
            if (expression == null || expression.isJsonNull()
                    || !expression.isJsonObject()) {
                unsupported.add("ABSENT_EXPRESSION");
                return unsupportedTerm(expected == null
                        ? Sort.REF : expected);
            }
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if ("SymbolExpression".equals(type)) {
                Term result = symbol(object, expected);
                captureFatalOperand(object, result);
                return result;
            }
            if ("ConstExpr".equals(type)
                    || "ConSymbolExp".equals(type)
                    || "ConStringSymbolExp".equals(type)) {
                return constant(object, expected);
            }
            if ("BinaryExpression".equals(type)) return binary(object);
            if ("OpStrExpression".equals(type)) {
                return stringOperation(object);
            }
            if ("PlaceholderExpression".equals(type)) {
                String function = string(object, "_place_holder_func");
                int count = integer(object, "_count", -1);
                if (!"currentTimeMills".equals(function) || count < 1) {
                    unsupported.add("PlaceholderExpression:"
                            + firstNonBlank(function, "unknown") + "#"
                            + count);
                    return unsupportedTerm(Sort.INT);
                }
                // The custom VM restarts placeholder ordinals for every
                // replay task.  Therefore #1 identifies an event only inside
                // the currently imported path case; treating it as a global
                // identity accidentally equates (for example) a NameNode
                // clock read with a later DataNode clock read.
                String identity = function + "#" + count;
                String scopedIdentity = currentSymbolScope + "\u0000"
                        + identity;
                String name = scopedName("environment", identity) + "__"
                        + CanonicalJson.sha256(scopedIdentity)
                        .substring(0, 10);
                declare(name, Sort.INT);
                assertJavaIntegralDomain(name, Sort.INT, "J", identity);
                Term result = new Term(name, Sort.INT,
                        IntegralWidth.JAVA_LONG);
                captureFatalOperand(object, result);
                return result;
            }
            if ("TypeCastExpression".equals(type)) {
                return typeCast(object);
            }
            if ("MethodExpression".equals(type)) {
                return methodTerm(object);
            }
            if (ContainerSmtCodec.handles(object)) {
                return containerTerm(object);
            }
            if (ContainerSmtCodec.handlesField(object)) {
                return containerFieldTerm(object);
            }
            unsupported.add(type.isEmpty() ? "MISSING_TYPE" : type);
            Sort sort = expected == null ? Sort.VALUE : expected;
            return unsupportedTerm(sort);
        }

        private Term containerTerm(JsonObject expression) {
            return lowerContainerTerm(expression, false);
        }

        private Term containerFieldTerm(JsonObject expression) {
            return lowerContainerTerm(expression, true);
        }

        private Term lowerContainerTerm(JsonObject expression,
                                        boolean field) {
            boolean owner = currentContainerRequirements == null;
            if (owner) currentContainerRequirements = new LinkedHashSet<>();
            try {
                Term result = fromContainerTerm(field
                        ? ContainerSmtCodec.field(expression, containerHost())
                        : ContainerSmtCodec.term(expression, containerHost()));
                if (!owner || result == null) return result;
                return result.withPrecondition(and(Arrays.asList(
                        result.precondition,
                        and(new ArrayList<>(currentContainerRequirements)))));
            } finally {
                if (owner) currentContainerRequirements = null;
            }
        }

        private ContainerSmtCodec.Host containerHost() {
            return new ContainerSmtCodec.Host() {
                @Override
                public ContainerSmtCodec.Term state(
                        JsonElement identity,
                        ContainerSmtCodec.Sort shape) {
                    if (identity != null && identity.isJsonObject()
                            && "SymbolExpression".equals(string(
                            identity.getAsJsonObject(), "_type"))) {
                        String port = findPort(string(
                                identity.getAsJsonObject(), "_exp"));
                        Sort required = shape
                                == ContainerSmtCodec.Sort.INDEXED
                                ? Sort.ARRAY_VALUE : Sort.MAP;
                        if (!port.isEmpty()) {
                            promotePort(port, required);
                        }
                        if (!port.isEmpty() && portSort(port) == required) {
                            ContainerSmtCodec.Term encoded = toContainerTerm(
                                    term(identity, required));
                            if (encoded != null && encoded.sort == shape) {
                                return encoded;
                            }
                        }
                        if (port.isEmpty()) {
                            // VM-local collection identities need not be
                            // canonical region ports.  Preserve them as
                            // typed, unconstrained container state instead
                            // of rejecting every size/read derived from the
                            // collection.
                            ContainerSmtCodec.Term encoded = toContainerTerm(
                                    term(identity, required));
                            if (encoded != null && encoded.sort == shape) {
                                return encoded;
                            }
                        }
                    }
                    Term reference = term(identity, Sort.REF);
                    if (reference == null || reference.sort != Sort.REF) {
                        unsupported("ContainerStateIdentity:" + shape);
                        return null;
                    }
                    return new ContainerSmtCodec.Term(
                            (shape == ContainerSmtCodec.Sort.INDEXED
                                    ? "(indexed_state_of "
                                    : "(assoc_state_of ")
                                    + reference.text + ")",
                            shape);
                }

                @Override
                public ContainerSmtCodec.Term operand(
                        JsonElement expression,
                        ContainerSmtCodec.Sort expected) {
                    if (ContainerSmtCodec.handles(expression)) {
                        return ContainerSmtCodec.term(
                                expression.getAsJsonObject(), this);
                    }
                    if (ContainerSmtCodec.handlesField(expression)) {
                        return ContainerSmtCodec.field(
                                expression.getAsJsonObject(), this);
                    }
                    Sort nativeExpected = expected == ContainerSmtCodec.Sort.INT
                            ? Sort.INT
                            : expected == ContainerSmtCodec.Sort.BOOL
                            ? Sort.BOOL
                            : expected == ContainerSmtCodec.Sort.REF
                            ? Sort.REF
                            : expected == ContainerSmtCodec.Sort.INDEXED
                            ? Sort.ARRAY_VALUE
                            : expected
                            == ContainerSmtCodec.Sort.ASSOCIATIVE
                            ? Sort.MAP : null;
                    return toContainerTerm(term(expression, nativeExpected));
                }

                @Override
                public ContainerSmtCodec.Term box(JsonElement expression) {
                    return toContainerTerm(asValue(term(expression, null),
                            expressionJavaType(expression)));
                }

                @Override
                public ContainerSmtCodec.Term unbox(
                        ContainerSmtCodec.Term value, String javaType) {
                    if (value == null
                            || value.sort != ContainerSmtCodec.Sort.VALUE) {
                        return value;
                    }
                    String kind = ContainerSmtCodec.valueKind(javaType);
                    if (!kind.isEmpty()) {
                        require("((_ is " + kind + ") "
                                + value.text + ")");
                    }
                    String integralValue =
                            ContainerSmtCodec.unboxIntegral(
                                    value.text, javaType);
                    if (!integralValue.isEmpty()) {
                        return new ContainerSmtCodec.Term(
                                integralValue, ContainerSmtCodec.Sort.INT,
                                JavaPrimitiveSmtSemantics.widthOfJavaType(
                                        javaType));
                    }
                    Sort sort = sortOfJava(javaType);
                    if (sort == Sort.BOOL) {
                        return new ContainerSmtCodec.Term(
                                "(valueBool " + value.text + ")",
                                ContainerSmtCodec.Sort.BOOL);
                    }
                    if (sort == Sort.REF) {
                        return new ContainerSmtCodec.Term(
                                "(valueRef " + value.text + ")",
                                ContainerSmtCodec.Sort.REF);
                    }
                    if (sort == Sort.FLOAT32) {
                        return new ContainerSmtCodec.Term(
                                "(valueFloat " + value.text + ")",
                                ContainerSmtCodec.Sort.FLOAT32);
                    }
                    if (sort == Sort.FLOAT64) {
                        return new ContainerSmtCodec.Term(
                                "(valueDouble " + value.text + ")",
                                ContainerSmtCodec.Sort.FLOAT64);
                    }
                    if (sort == Sort.STRING) {
                        return new ContainerSmtCodec.Term(
                                "(valueString " + value.text + ")",
                                ContainerSmtCodec.Sort.STRING);
                    }
                    return value;
                }

                @Override
                public void require(String predicate) {
                    if (currentContainerRequirements != null) {
                        currentContainerRequirements.add(predicate);
                    } else {
                        assertNamed("container_value_kind_"
                                + CanonicalJson.sha256(predicate)
                                .substring(0, 16), predicate);
                    }
                }

                @Override
                public ContainerSmtCodec.Term field(
                        ContainerSmtCodec.Term owner, String ownerClass,
                        int fieldOffset, String javaType) {
                    Sort result = sortOfJava(javaType);
                    if (owner == null
                            || owner.sort != ContainerSmtCodec.Sort.REF
                            || fieldOffset < 0 || result == Sort.VALUE
                            || result == Sort.MAP
                            || result == Sort.ARRAY_VALUE) {
                        unsupported("FieldAccessExpression:"
                                + ownerClass + "@" + fieldOffset + ":"
                                + javaType);
                        return null;
                    }
                    String identity = ownerClass + "\u0000" + fieldOffset
                            + "\u0000" + javaType;
                    String accessor = "container_field__"
                            + scopeToken(identity);
                    declareFunction(accessor, Collections.singletonList(
                            new Term("", Sort.REF)), result);
                    return toContainerTerm(new Term("(" + accessor + " "
                            + owner.text + ")", result,
                            integralWidthOfJava(javaType)));
                }

                @Override
                public void unsupported(String reason) {
                    Emitter.this.unsupported.add(
                            "MODEL_SEMANTICS_MISSING:" + reason);
                }
            };
        }

        private ContainerSmtCodec.Term toContainerTerm(Term value) {
            if (value == null) return null;
            ContainerSmtCodec.Sort sort = value.sort == Sort.BOOL
                    ? ContainerSmtCodec.Sort.BOOL
                    : value.sort == Sort.INT
                    ? ContainerSmtCodec.Sort.INT
                    : value.sort == Sort.REF
                    ? ContainerSmtCodec.Sort.REF
                    : value.sort == Sort.VALUE
                    ? ContainerSmtCodec.Sort.VALUE : null;
            if (value.sort == Sort.ARRAY_VALUE) {
                sort = ContainerSmtCodec.Sort.INDEXED;
            } else if (value.sort == Sort.MAP) {
                sort = ContainerSmtCodec.Sort.ASSOCIATIVE;
            } else if (value.sort == Sort.FLOAT32) {
                sort = ContainerSmtCodec.Sort.FLOAT32;
            } else if (value.sort == Sort.FLOAT64) {
                sort = ContainerSmtCodec.Sort.FLOAT64;
            } else if (value.sort == Sort.STRING) {
                sort = ContainerSmtCodec.Sort.STRING;
            }
            if (sort == null) {
                unsupported.add("ContainerOperandSort:" + value.sort);
                return null;
            }
            return new ContainerSmtCodec.Term(value.text, sort,
                    value.integralWidth);
        }

        private Term fromContainerTerm(ContainerSmtCodec.Term value) {
            if (value == null) return unsupportedTerm(Sort.VALUE);
            Sort sort = value.sort == ContainerSmtCodec.Sort.BOOL
                    ? Sort.BOOL
                    : value.sort == ContainerSmtCodec.Sort.INT
                    ? Sort.INT
                    : value.sort == ContainerSmtCodec.Sort.REF
                    ? Sort.REF
                    : value.sort == ContainerSmtCodec.Sort.FLOAT32
                    ? Sort.FLOAT32
                    : value.sort == ContainerSmtCodec.Sort.FLOAT64
                    ? Sort.FLOAT64
                    : value.sort == ContainerSmtCodec.Sort.STRING
                    ? Sort.STRING
                    : value.sort == ContainerSmtCodec.Sort.INDEXED
                    ? Sort.ARRAY_VALUE
                    : value.sort == ContainerSmtCodec.Sort.ASSOCIATIVE
                    ? Sort.MAP : Sort.VALUE;
            return new Term(value.text, sort, value.integralWidth);
        }

        private Term symbol(JsonObject expression, Sort expected) {
            String raw = string(expression, "_exp");
            if ("N".equals(raw)) {
                return new Term("nullRef", Sort.REF);
            }
            if ("V".equals(raw)) {
                return new Term("true", Sort.BOOL);
            }

            String port = findPort(raw);
            if (!port.isEmpty()) {
                mentionedPorts.add(currentOccurrence(port));
                if (expected == Sort.MAP) {
                    promotePort(port, Sort.MAP);
                    declarePort(port, Sort.MAP);
                    boundPorts.add(currentOccurrence(port));
                    return new Term(portName(port), Sort.MAP);
                }
                if (expected == Sort.ARRAY_VALUE) {
                    if (portSort(port) != Sort.ARRAY_VALUE) {
                        unsupported.add("ArraySymbolPortSortConflict:" + port
                                + ":" + portSort(port));
                    } else {
                        declarePort(port, Sort.ARRAY_VALUE);
                        boundPorts.add(currentOccurrence(port));
                        return new Term(portName(port), Sort.ARRAY_VALUE);
                    }
                }
                Port schema = ports.get(port);
                if (expected == Sort.REF && schema != null
                        && (portSort(port) == Sort.MAP
                        || portSort(port) == Sort.ARRAY_VALUE)) {
                    return canonicalPortTerm(port, Sort.REF,
                            string(expression, "_java_type"));
                }
                if (schema != null && portSort(port) == Sort.MAP) {
                    declarePort(port, Sort.MAP);
                    boundPorts.add(currentOccurrence(port));
                    return new Term(portName(port), Sort.MAP);
                }
                if (schema != null && portSort(port) == Sort.ARRAY_VALUE) {
                    declarePort(port, Sort.ARRAY_VALUE);
                    boundPorts.add(currentOccurrence(port));
                    return new Term(portName(port), Sort.ARRAY_VALUE);
                }
                if (schema != null
                        && JavaPrimitiveBoxing.wrapperType(
                        schema.javaType)) {
                    if (expected == Sort.REF) {
                        return canonicalBoxedPrimitiveReferenceTerm(port);
                    }
                    return canonicalPortTerm(port,
                            sortOfJava(schema.javaType), schema.javaType);
                }
            }

            String expressionJavaType = string(expression, "_java_type");
            Sort expressionSort = sortOfJava(expressionJavaType);
            Sort sort = expressionSort != Sort.VALUE ? expressionSort
                    : expected == null ? Sort.VALUE : expected;
            if (sort == Sort.VALUE || sort == Sort.MAP) {
                sort = sortOfJava(string(expression, "_java_type"));
                if (sort == Sort.VALUE || sort == Sort.MAP) sort = Sort.REF;
            }
            if (!port.isEmpty()) {
                return canonicalPortTerm(port, sort, expressionJavaType);
            }

            return scopedSymbol(raw, "sym", sort,
                    expressionJavaType, "scoped_symbol_" + smtName(raw),
                    "ScopedSymbol", "scoped:");
        }

        /**
         * A canonical port is a formal relation variable, not an engine-local
         * counter.  Give each scalar view of it one global typed witness and
         * connect that witness to the Value-typed schema port unconditionally.
         */
        private Term canonicalPortTerm(String port, Sort sort) {
            return canonicalPortTerm(port, sort, "");
        }

        private Term canonicalPortTerm(String port, Sort sort,
                                       String expressionJavaType) {
            Port schema = ports.get(port);
            String schemaJavaType = schema == null ? "" : schema.javaType;
            String integralJavaType = canonicalIntegralJavaType(
                    schemaJavaType, expressionJavaType);
            if (sort == Sort.REF
                    && sortOfJava(schemaJavaType) == Sort.STRING) {
                return canonicalNullableStringReferenceTerm(port,
                        schemaJavaType);
            }
            PortOccurrence occurrence = currentOccurrence(port);
            String bindingKey = occurrence + "\u0000" + sort.name();
            String name = "sym__port__" + smtName(occurrence.toString()) + "__"
                    + sort.name().toLowerCase(Locale.ROOT);
            IntegralWidth schemaWidth = integralWidthOfJava(schemaJavaType);
            IntegralWidth expressionWidth = integralWidthOfJava(
                    expressionJavaType);
            if (schemaWidth != IntegralWidth.NONE
                    && expressionWidth != IntegralWidth.NONE
                    && schemaWidth != expressionWidth) {
                unsupported.add("CanonicalPortIntegralWidthConflict:" + port
                        + ":" + schemaWidth + "!=" + expressionWidth);
            }
            FloatingKind schemaFloating = JavaPrimitiveSmtSemantics
                    .floatingKindOfJavaType(schemaJavaType);
            FloatingKind expressionFloating = JavaPrimitiveSmtSemantics
                    .floatingKindOfJavaType(expressionJavaType);
            FloatingKind requestedFloating = floatingKind(sort);
            if (schemaFloating != FloatingKind.NONE
                    && requestedFloating != schemaFloating) {
                unsupported.add("CanonicalPortFloatingSortConflict:" + port
                        + ":schema=" + schemaFloating + ":requested="
                        + requestedFloating);
            }
            if (expressionFloating != FloatingKind.NONE
                    && requestedFloating != expressionFloating) {
                unsupported.add("CanonicalPortExpressionFloatingSortConflict:"
                        + port + ":expression=" + expressionFloating
                        + ":requested=" + requestedFloating);
            }
            if (schemaFloating != FloatingKind.NONE
                    && expressionFloating != FloatingKind.NONE
                    && schemaFloating != expressionFloating) {
                unsupported.add("CanonicalPortFloatingTypeConflict:" + port
                        + ":" + schemaFloating + "!="
                        + expressionFloating);
            }
            declare(name, sort);
            Term term;
            if (sort == Sort.STRING) {
                String nullness = "sym__port__"
                        + smtName(occurrence.toString())
                        + "__string_is_null";
                declare(nullness, Sort.BOOL);
                term = Term.nullableString(name, nullness,
                        "canonical-port:" + port);
            } else {
                term = new Term(name, sort,
                        integralWidthOfJava(integralJavaType));
            }
            if (canonicalPortTermBindings.add(bindingKey)) {
                String previousGuard = currentGuard;
                currentGuard = "";
                try {
                    assertJavaIntegralDomain(name, sort, integralJavaType,
                            "canonical_port_"
                                    + smtName(occurrence.toString()));
                    if (emitPortBinding(port, term)) {
                        boundPorts.add(occurrence);
                        recordCanonicalPortOccurrence(occurrence, sort, name,
                                term.stringNullness);
                    }
                } finally {
                    currentGuard = previousGuard;
                }
            }
            return term;
        }

        private void recordCanonicalPortOccurrence(
                PortOccurrence occurrence, Sort sort, String solverTerm,
                String nullnessSolverTerm) {
            JsonObject row = new JsonObject();
            row.addProperty("portId", occurrence.portId);
            row.addProperty("regionInstanceId",
                    occurrence.invocation.instanceId);
            row.addProperty("sort", sort.name());
            row.addProperty("portTerm", portName(occurrence));
            row.addProperty("solverTerm", solverTerm);
            if (!firstNonBlank(nullnessSolverTerm).isEmpty()
                    && !"false".equals(nullnessSolverTerm)) {
                row.addProperty("nullnessSolverTerm", nullnessSolverTerm);
            }
            canonicalPortOccurrences.put(occurrence + "\u0000" + sort.name(),
                    row);
        }

        private JsonArray canonicalPortOccurrences() {
            List<Map.Entry<String, JsonObject>> rows = new ArrayList<>(
                    canonicalPortOccurrences.entrySet());
            rows.sort(Map.Entry.comparingByKey());
            JsonArray result = new JsonArray();
            for (Map.Entry<String, JsonObject> row : rows) {
                result.add(row.getValue().deepCopy());
            }
            return result;
        }

        /**
         * Emits the minimum solver-native evidence required by a generic
         * pin/ablation audit.  The ledger deliberately contains no source
         * method, application field, or expected value: it names only terms,
         * sorts, dynamic ports, runtime edge ids, and the exact assertions
         * already present in the generated SMT.
         */
        private JsonObject operandBindingLedger() {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 2);
            result.addProperty("kind", "FATAL_OPERAND_BINDING_LEDGER");
            JsonObject fatalAssertion = new JsonObject();
            fatalAssertion.addProperty("name", fatalPathAssertionName);
            fatalAssertion.addProperty("solverTerm",
                    fatalPathAssertionTerm);
            result.add("fatalPathAssertion", fatalAssertion);
            result.add("fatalDependentAssertionNames", GSON.toJsonTree(
                    fatalDependentAssertionNames));
            JsonObject retainedPrefix = new JsonObject();
            retainedPrefix.addProperty("name", fatalPrefixAssertionName);
            retainedPrefix.addProperty("solverTerm",
                    fatalPrefixAssertionTerm);
            result.add("retainedPathPrefixAssertion", retainedPrefix);

            JsonArray paths = new JsonArray();
            for (Map.Entry<Integer, String> entry
                    : fatalPathPrefixes.entrySet()) {
                int operandCount = 0;
                for (FatalOperand operand : fatalOperands.values()) {
                    if (operand.pathOrdinal == entry.getKey()) {
                        operandCount++;
                    }
                }
                JsonObject path = new JsonObject();
                path.addProperty("pathOrdinal", entry.getKey());
                path.addProperty("pathPrefixTerm", entry.getValue());
                path.addProperty("operandCount", operandCount);
                paths.add(path);
            }
            result.add("paths", paths);

            JsonArray operands = new JsonArray();
            for (FatalOperand operand : fatalOperands.values()) {
                JsonObject row = new JsonObject();
                row.addProperty("operandId", operand.operandId);
                row.addProperty("pathOrdinal", operand.pathOrdinal);
                PortOccurrence exactLineage =
                        exactFatalOperandOccurrence(operand);
                boolean exactOccurrence = exactLineage != null;
                Term exactLedgerTerm = exactOccurrence
                        ? exactFatalLedgerTerm(operand, exactLineage)
                        : null;
                row.addProperty("solverTerm", exactOccurrence
                        ? exactLedgerTerm.text : operand.solverTerm);
                row.addProperty("solverSort", exactOccurrence
                        ? exactLedgerTerm.sort.smt
                        : operand.solverSort.smt);
                row.addProperty("pinTerm", exactOccurrence
                        ? exactLedgerTerm.text : operand.pinTerm);
                row.addProperty("pinSort", exactOccurrence
                        ? exactLedgerTerm.sort.smt : operand.pinSort.smt);
                row.addProperty("pathPrefixTerm",
                        fatalPathPrefixes.getOrDefault(
                                operand.pathOrdinal, "true"));
                if (exactOccurrence) {
                    row.addProperty("portId", exactLineage.portId);
                    row.addProperty("regionInstanceId",
                            exactLineage.invocation.instanceId);
                    row.addProperty("producerLineageStatus",
                            "EXACT_TARGET_PORT_OCCURRENCE");
                    row.addProperty("producerLineageAuthority",
                            operand.occurrence != null
                                    ? "DIRECT_FATAL_PORT_REFERENCE_V1"
                                    : "EXACT_FATAL_PREFIX_EQUALITY_ALIAS_V1");
                } else {
                    row.addProperty("producerLineageStatus",
                            "UNAUDITABLE_NO_EXACT_PRODUCER_LINEAGE");
                }
                JsonArray versions = new JsonArray();
                Set<String> emitted = new LinkedHashSet<>();
                for (ProducerVersionBinding binding
                        : producerVersionBindings) {
                    // Producer-version evidence belongs only to the exact
                    // dynamic consumer port occurrence named by this fatal
                    // operand.  A same-sort producer elsewhere in the composed
                    // workflow is not lineage evidence for an engine-local
                    // temporary, even when both happen to take the same value.
                    if (!exactOccurrence
                            || !exactLineage.equals(binding.target)
                            || exactLedgerTerm.sort != binding.solverSort) {
                        continue;
                    }
                    String key = binding.edgeId + "\u0000"
                            + binding.assertionName + "\u0000"
                            + binding.solverTerm;
                    if (!emitted.add(key)) continue;
                    versions.add(binding.toJson());
                }
                row.add("producerVersions", versions);
                operands.add(row);
            }
            result.add("operands", operands);

            Map<String, Set<String>> assertionsByEdge =
                    new LinkedHashMap<>();
            for (ProducerVersionBinding binding : producerVersionBindings) {
                assertionsByEdge.computeIfAbsent(binding.edgeId,
                        ignored -> new LinkedHashSet<>()).add(
                        binding.assertionName);
            }
            JsonArray edges = new JsonArray();
            for (Map.Entry<String, Set<String>> entry
                    : assertionsByEdge.entrySet()) {
                JsonObject edge = new JsonObject();
                edge.addProperty("edgeId", entry.getKey());
                edge.add("assertionNames", GSON.toJsonTree(
                        entry.getValue()));
                edges.add(edge);
            }
            result.add("edgeAssertions", edges);
            return result;
        }

        /**
         * Uses the operand's native sort when the incoming edge carries it
         * directly.  State edges carry primitive fields through the ordinary
         * {@code Value} port, so in that one case the audit term is merely
         * the corresponding JVM box (for example {@code VInt(temp)}).  The
         * path prefix and the canonical port binding already assert the two
         * representations equal; no new program constraint is introduced.
         */
        private Term exactFatalLedgerTerm(FatalOperand operand,
                                          PortOccurrence occurrence) {
            boolean nativeSort = false;
            boolean valueSort = false;
            for (ProducerVersionBinding binding : producerVersionBindings) {
                if (!occurrence.equals(binding.target)) continue;
                nativeSort |= binding.solverSort == operand.solverSort;
                valueSort |= binding.solverSort == Sort.VALUE;
            }
            Term nativeTerm = new Term(operand.solverTerm,
                    operand.solverSort);
            if (nativeSort || !valueSort) return nativeTerm;
            Term boxed = asValue(nativeTerm);
            return boxed.sort == Sort.VALUE ? boxed : nativeTerm;
        }

        /**
         * Models an erased JVM reference view of a statically-known String
         * input without inventing a second Value binding for the same port.
         * The reference token is used only for identity/null comparisons;
         * its nullness is exactly the canonical nullable-String companion.
         */
        private Term canonicalNullableStringReferenceTerm(
                String port, String schemaJavaType) {
            Term stringTerm = canonicalPortTerm(port, Sort.STRING,
                    schemaJavaType);
            PortOccurrence occurrence = currentOccurrence(port);
            String name = "sym__port__" + smtName(occurrence.toString())
                    + "__ref";
            declare(name, Sort.REF);
            String bindingKey = occurrence
                    + "\u0000NULLABLE_STRING_REFERENCE_VIEW";
            if (canonicalPortTermBindings.add(bindingKey)) {
                String formula = "(= (= " + name + " nullRef) "
                        + stringTerm.stringNullness + ")";
                String previousGuard = currentGuard;
                currentGuard = "";
                try {
                    assertNamed("nullable_string_reference_view_" + port,
                            formula);
                } finally {
                    currentGuard = previousGuard;
                }
            }
            return new Term(name, Sort.REF);
        }

        /**
         * Keeps Java wrapper identity separate from the wrapper's logical
         * primitive value.  Field materialization and {@code ==}/{@code !=}
         * use this reference witness, while value/unboxing flow binds the
         * canonical Value port through {@link #canonicalPortTerm}.
         */
        private Term canonicalBoxedPrimitiveReferenceTerm(String port) {
            PortOccurrence occurrence = currentOccurrence(port);
            String name = "sym__port__"
                    + smtName(occurrence.toString()) + "__boxed_ref";
            declare(name, Sort.REF);
            return new Term(name, Sort.REF);
        }

        private Term scopedSymbol(String raw, String prefix, Sort requested,
                                  String javaType, String domainLabel,
                                  String conflictLabel, String sourcePrefix) {
            String key = currentSymbolScope + "\u0000" + raw;
            RawSymbol symbol = rawSymbols.get(key);
            if (symbol == null) {
                symbol = new RawSymbol(scopedName(prefix, raw), requested);
                rawSymbols.put(key, symbol);
                declare(symbol.name, symbol.sort);
                assertJavaIntegralDomain(symbol.name, symbol.sort, javaType,
                        domainLabel);
            } else if (symbol.sort != requested) {
                unsupported.add(conflictLabel + "SortConflict:" + raw
                        + ":" + symbol.sort + "->" + requested);
            }
            if (symbol.sort == Sort.STRING) {
                if (symbol.nullness.isEmpty()) {
                    symbol.nullness = scopedName("string_is_null", raw);
                    declare(symbol.nullness, Sort.BOOL);
                }
                return Term.nullableString(symbol.name, symbol.nullness,
                        sourcePrefix + key);
            }
            return new Term(symbol.name, symbol.sort,
                    integralWidthOfJava(javaType));
        }

        private Term constant(JsonObject expression, Sort expected) {
            String raw = string(expression, "_exp");
            String javaType = string(expression, "_java_type");
            String value = constantPayload(raw);
            Sort sort = sortOfJava(javaType);
            Term result;
            // The JVM has no boolean comparison instruction, so a boolean
            // test compiles to a comparison against the int literal 0:
            // `if (!it.hasNext())` reaches here as BOOL against an int 0.
            // Reading that as a sort conflict drops the guard and forces
            // its case false, so an integral 0/1 in a boolean position is
            // Java's own encoding of false/true, exactly as the path
            // solver already reads it.
            if (expected == Sort.BOOL
                    && (sort == Sort.BOOL || sort == Sort.INT)) {
                if (!"0".equals(value) && !"1".equals(value)) {
                    unsupported.add("InvalidJavaBooleanLiteral:"
                            + firstNonBlank(raw, "MISSING"));
                    result = unsupportedTerm(Sort.BOOL);
                } else {
                    result = new Term("1".equals(value)
                            ? "true" : "false", Sort.BOOL);
                }
            } else if (expected == Sort.REF && ("0".equals(value)
                    || "N".equals(raw))) {
                result = new Term("nullRef", Sort.REF);
            } else if (sort.floating()) {
                String literal = JavaPrimitiveSmtSemantics.floatingLiteral(
                        value, floatingKind(sort));
                result = literal == null
                        ? invalidNumericLiteral(raw, sort)
                        : new Term(literal, sort);
            } else if (sort == Sort.INT) {
                String literal = integerLiteral(value);
                result = literal == null
                        ? invalidNumericLiteral(raw, sort)
                        : new Term(literal, Sort.INT,
                        integralWidthOfJava(javaType));
            } else if (sort == Sort.STRING) {
                result = Term.nonNullString(quote(value), "true");
            } else {
                String name = "const__" + smtName(raw);
                declare(name, sort == Sort.VALUE ? Sort.REF : sort);
                result = new Term(name,
                        sort == Sort.VALUE ? Sort.REF : sort);
            }
            return result;
        }

        private Term invalidNumericLiteral(String raw, Sort sort) {
            unsupported.add("InvalidNumericLiteral:" + sort + ":"
                    + firstNonBlank(raw, "MISSING"));
            return unsupportedTerm(sort);
        }

        /**
         * Admits only conversions that are the identity in this encoder's
         * mathematical primitive model.  The source is lowered with its own
         * declared type first; a target sort is never allowed to redeclare it.
         */
        private Term typeCast(JsonObject expression) {
            JsonElement sourceExpression = expression.get("_exp");
            Term source = term(sourceExpression, null);
            String sourceType = castDescriptor(
                    firstNonBlank(string(expression, "sourceJavaType"),
                            expressionJavaType(sourceExpression)));
            String targetType = castTargetDescriptor(firstNonBlank(
                    string(expression, "targetJavaType"),
                    string(expression, "_java_type")), sourceType);
            Sort sourceSort = castSort(sourceType);
            Sort targetSort = castSort(targetType);
            boolean primitivePair = JavaPrimitiveSmtSemantics
                    .primitiveNumericDescriptor(sourceType)
                    && JavaPrimitiveSmtSemantics
                    .primitiveNumericDescriptor(targetType);
            if (primitivePair && source.sort == sourceSort) {
                String conversion = JavaPrimitiveSmtSemantics.primitiveCast(
                        source.text, sourceType, targetType);
                if (conversion != null) {
                    return dependent(new Term(conversion, targetSort,
                            integralWidthOfJava(targetType)), source);
                }
            } else if (primitivePair) {
                unsupported.add("JavaCastSourceSortConflict:"
                        + firstNonBlank(sourceType, "UNKNOWN") + ":"
                        + source.sort + "!=" + sourceSort);
                Sort diagnosticSort = targetSort == Sort.VALUE
                        ? Sort.REF : targetSort;
                return unsupportedTerm(diagnosticSort);
            }
            unsupported.add("MODEL_SEMANTICS_MISSING:TypeCastExpression:"
                    + firstNonBlank(sourceType, "UNKNOWN") + "->"
                    + firstNonBlank(targetType, "UNKNOWN"));
            Sort diagnosticSort = targetSort == Sort.VALUE
                    ? Sort.REF : targetSort;
            return unsupportedTerm(diagnosticSort);
        }

        private Term binary(JsonObject expression) {
            String operator = string(expression, "_op");
            JsonElement leftExpression = expression.get("_left");
            if (leftExpression == null || leftExpression.isJsonNull()) {
                Term operand = term(expression.get("_right"), null);
                if ("-".equals(operator) && numeric(operand.sort)) {
                    if (operand.sort.floating()) {
                        return dependent(new Term(JavaPrimitiveSmtSemantics
                                .floatingNegate(operand.text), operand.sort),
                                operand);
                    }
                    if (operand.integralWidth != IntegralWidth.NONE) {
                        return dependent(new Term(wrapIntegral("(- " + operand.text
                                + ")", operand.integralWidth), Sort.INT,
                                operand.integralWidth), operand);
                    }
                    unsupported.add("AmbiguousJavaIntegralUnaryWidth:"
                            + firstNonBlank(operator, "MISSING"));
                    return unsupportedTerm(Sort.INT);
                }
                unsupported.add("NonNumericOrUnknownUnary:"
                        + firstNonBlank(operator, "MISSING") + ":"
                        + operand.sort);
                return unsupportedTerm(operand.sort);
            }
            Sort identitySort = boxedPrimitiveReferenceEquality(expression)
                    ? Sort.REF : null;
            Term left = term(expression.get("_left"), identitySort);
            Term right = term(expression.get("_right"),
                    identitySort == null ? left.sort : identitySort);
            if (left.sort != right.sort && right.isZero()
                    && left.sort == Sort.REF) {
                right = new Term("nullRef", Sort.REF);
            } else if (left.sort != right.sort && left.isZero()
                    && right.sort == Sort.REF) {
                left = new Term("nullRef", Sort.REF);
            }
            if ("--".equals(operator)) {
                if (left.sort == Sort.INT && right.sort == Sort.INT
                        && left.integralWidth == IntegralWidth.JAVA_LONG
                        && right.integralWidth == IntegralWidth.JAVA_LONG) {
                    return dependent(new Term(JavaPrimitiveSmtSemantics
                            .integralCompareResult(left.text, right.text),
                            Sort.INT, IntegralWidth.JAVA_INT), left, right);
                }
                unsupported.add("MalformedJvmLcmpOperands:"
                        + left.sort + ":" + left.integralWidth + ":"
                        + right.sort + ":" + right.integralWidth);
                return new Term("0", Sort.INT,
                        IntegralWidth.JAVA_INT);
            }
            if ("--l".equals(operator) || "--g".equals(operator)) {
                if (left.sort == right.sort && left.sort.floating()) {
                    return dependent(new Term(JavaPrimitiveSmtSemantics
                            .floatingCompareResult(left.text, right.text,
                                    "--g".equals(operator)), Sort.INT,
                            IntegralWidth.JAVA_INT), left, right);
                }
                unsupported.add("MalformedJvmFloatingCompareOperands:"
                        + operator + ":" + left.sort + ":" + right.sort);
                return new Term("0", Sort.INT,
                        IntegralWidth.JAVA_INT);
            }
            if (left.sort != right.sort && numeric(left.sort)
                    && numeric(right.sort)
                    && (left.sort.floating() || right.sort.floating())) {
                Sort promoted = left.sort == Sort.FLOAT64
                        || right.sort == Sort.FLOAT64
                        ? Sort.FLOAT64 : Sort.FLOAT32;
                left = floatingPromotion(left, promoted, "left");
                right = floatingPromotion(right, promoted, "right");
            }
            if (("==".equals(operator) || "!=".equals(operator))
                    && (left.sort == Sort.STRING && isNull(right)
                    || right.sort == Sort.STRING && isNull(left))) {
                Term string = left.sort == Sort.STRING ? left : right;
                String equality = string.stringNullness;
                return dependent(new Term("!=".equals(operator)
                        ? "(not " + equality + ")" : equality,
                        Sort.BOOL), left, right);
            }
            if (left.sort != right.sort
                    && (("==".equals(operator) || "!=".equals(operator))
                    && (isNull(left) || isNull(right)))) {
                // Java primitives are never null.  This is the one mixed-sort
                // binary relation whose semantics can be closed without an
                // ill-sorted SMT application.
                return dependent(new Term("!=".equals(operator)
                        ? "true" : "false", Sort.BOOL), left, right);
            }
            if ("&&".equals(operator) || "||".equals(operator)) {
                if (left.sort != Sort.BOOL || right.sort != Sort.BOOL) {
                    unsupported.add("NonBooleanLogic:" + operator + ":"
                            + left.sort + ":" + right.sort);
                    return unsupportedTerm(Sort.BOOL);
                }
                boolean conjunction = "&&".equals(operator);
                String rightEvaluated = conjunction ? left.text
                        : "(not " + left.text + ")";
                String defined = and(Arrays.asList(left.precondition,
                        "(=> " + rightEvaluated + " "
                                + right.precondition + ")"));
                return new Term("(" + (conjunction ? "and" : "or")
                        + " " + left.text + " " + right.text + ")",
                        Sort.BOOL).withPrecondition(defined);
            }
            if (left.sort != right.sort) {
                unsupported.add("BinarySortConflict:" + operator + ":"
                        + left.sort + "!=" + right.sort);
                Sort resultSort = "==".equals(operator)
                        || "!=".equals(operator)
                        || !comparison(operator).isEmpty()
                        ? Sort.BOOL : left.sort;
                return unsupportedTerm(resultSort);
            }
            if ("==".equals(operator) || "!=".equals(operator)) {
                if (left.sort == Sort.STRING) {
                    if (ContainerSmtCodec.handlesFieldBinding(expression)) {
                        Term symbol = ContainerSmtCodec.handlesField(
                                expression.get("_left")) ? right : left;
                        String materialization = ContainerSmtCodec
                                .materializedStringEquality(left.text,
                                right.text, symbol.stringNullness);
                        return dependent(new Term(materialization,
                                Sort.BOOL), left, right);
                    }
                    if (!left.stringReferenceOrigin.isEmpty()
                            && left.stringReferenceOrigin.equals(
                            right.stringReferenceOrigin)) {
                        return dependent(new Term("!=".equals(operator)
                                ? "false" : "true", Sort.BOOL),
                                left, right);
                    }
                    unsupported.add("MODEL_SEMANTICS_MISSING:"
                            + "JAVA_STRING_REFERENCE_IDENTITY:"
                            + operator);
                    return dependent(unsupportedTerm(Sort.BOOL),
                            left, right);
                }
                if (left.sort.floating()) {
                    return dependent(new Term(JavaPrimitiveSmtSemantics
                            .floatingComparison(operator, left.text,
                                    right.text), Sort.BOOL), left, right);
                }
                String equality = "(= " + left.text + " " + right.text + ")";
                return dependent(new Term("!=".equals(operator)
                        ? "(not " + equality + ")" : equality, Sort.BOOL),
                        left, right);
            }
            String smt = comparison(operator);
            if (!smt.isEmpty()) {
                if (!numeric(left.sort) || !numeric(right.sort)) {
                    unsupported.add("NonNumericComparison:" + operator + ":"
                            + left.sort);
                    return unsupportedTerm(Sort.BOOL);
                }
                if (left.sort.floating()) {
                    return dependent(new Term(JavaPrimitiveSmtSemantics
                            .floatingComparison(operator, left.text,
                                    right.text), Sort.BOOL), left, right);
                }
                return dependent(new Term("(" + smt + " " + left.text + " "
                        + right.text + ")", Sort.BOOL), left, right);
            }
            if (arithmeticOperator(operator)) {
                if (!numeric(left.sort) || !numeric(right.sort)) {
                    unsupported.add("NonNumericArithmetic:" + operator + ":"
                            + left.sort);
                    return unsupportedTerm(left.sort);
                }
                Sort resultSort = left.sort;
                if ("%".equals(operator)) {
                    unsupported.add(resultSort.floating()
                            ? "JavaFloatingRemainderUnmodeled"
                            : "JavaIntegralRemainderUnmodeled");
                    return unsupportedTerm(resultSort);
                }
                if (resultSort.floating()) {
                    String floating = JavaPrimitiveSmtSemantics
                            .floatingArithmetic(operator, left.text,
                                    right.text);
                    if (floating != null) return dependent(new Term(floating,
                            resultSort), left, right);
                    unsupported.add("JavaFloatingOperatorUnmodeled:"
                            + operator);
                    return unsupportedTerm(resultSort);
                }
                if ("@".equals(operator) || "/".equals(operator)) {
                    unsupported.add("JavaIntegralDivisionUnmodeled");
                    return unsupportedTerm(Sort.INT);
                }
                smt = arithmetic(operator);
                String arithmeticExpression = "(" + smt + " "
                        + left.text + " " + right.text + ")";
                IntegralWidth resultWidth = promotedIntegralWidth(left,
                        right);
                if (resultWidth == IntegralWidth.NONE) {
                    unsupported.add("AmbiguousJavaIntegralBinaryWidth:"
                            + operator + ":" + left.integralWidth + ":"
                            + right.integralWidth);
                    return unsupportedTerm(Sort.INT);
                }
                return dependent(new Term(wrapIntegral(arithmeticExpression,
                        resultWidth), Sort.INT, resultWidth), left, right);
            }
            unsupported.add("BinaryOperator:" + operator);
            return unsupportedTerm(Sort.BOOL);
        }

        private boolean boxedPrimitiveReferenceEquality(
                JsonObject expression) {
            String operator = string(expression, "_op");
            if (!"==".equals(operator) && !"!=".equals(operator)) {
                return false;
            }
            return boxedPrimitiveReferenceOperand(expression.get("_left"))
                    || boxedPrimitiveReferenceOperand(
                    expression.get("_right"));
        }

        private boolean boxedPrimitiveReferenceOperand(
                JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) {
                return false;
            }
            JsonObject object = expression.getAsJsonObject();
            if (!"SymbolExpression".equals(string(object, "_type"))
                    || sortOfJava(string(object, "_java_type"))
                    != Sort.REF) {
                return false;
            }
            String port = findPort(string(object, "_exp"));
            Port schema = ports.get(port);
            return schema != null
                    && JavaPrimitiveBoxing.wrapperType(schema.javaType);
        }

        private Term floatingPromotion(Term term, Sort target,
                                       String origin) {
            FloatingKind targetKind = floatingKind(target);
            if (term.sort == target) return term;
            if (term.sort.floating()) {
                String converted = JavaPrimitiveSmtSemantics
                        .floatingConversion(term.text,
                                floatingKind(term.sort), targetKind);
                if (converted != null) return dependent(new Term(converted,
                        target), term);
            } else if (term.sort == Sort.INT
                    && term.integralWidth != IntegralWidth.NONE) {
                String converted = JavaPrimitiveSmtSemantics
                        .integralToFloating(term.text, targetKind);
                if (converted != null) return dependent(new Term(converted,
                        target), term);
            }
            unsupported.add("UnsupportedJavaNumericPromotion:" + origin
                    + ":" + term.sort + "->" + target);
            return unsupportedTerm(target);
        }

        /** Emits exact core Java String predicates/value operations plus the
         * decimal conversion used by the generic Java codec. Operations with
         * materially different Java/SMT semantics remain fail-closed. */
        private Term stringOperation(JsonObject expression) {
            String operation = string(expression, "_name");
            boolean negated = bool(expression, "_is_not", false);
            JsonArray params = array(expression, "_param_list");
            if ("isEmpty".equals(operation)) {
                List<Term> strings = exactStringParameters(params, 1);
                if (strings == null) {
                    return codecGap("OpStrExpression." + operation,
                            params.size() == 1 ? "NON_STRING_PARAMETER"
                                    : "ARITY", Sort.BOOL);
                }
                Term receiver = strings.get(0);
                return booleanStringResult("(= (str.len " + receiver.text
                        + ") 0)", negated,
                        stringDereferencePrecondition(receiver));
            }
            if ("length".equals(operation)) {
                if (negated) {
                    return codecGap("OpStrExpression.length",
                            "NEGATED_VALUE_OPERATION", Sort.INT);
                }
                List<Term> strings = exactStringParameters(params, 1);
                if (strings == null) {
                    return codecGap("OpStrExpression.length",
                            params.size() == 1 ? "NON_STRING_PARAMETER"
                                    : "ARITY", Sort.INT);
                }
                Term receiver = strings.get(0);
                Term length = new Term("(str.len " + receiver.text + ")",
                        Sort.INT, IntegralWidth.JAVA_INT).withPrecondition(
                        stringDereferencePrecondition(receiver));
                assertJavaIntegralDomain(length.text, length.sort, "I",
                        "java_string_length");
                return length;
            }
            if ("equals".equals(operation)) {
                if (params.size() != 2) {
                    return codecGap("OpStrExpression.equals", "ARITY",
                            Sort.BOOL);
                }
                Term receiver = term(params.get(0), null);
                Term argument = term(params.get(1), null);
                if (receiver.sort != Sort.STRING) {
                    return codecGap("OpStrExpression.equals",
                            "NON_STRING_PARAMETER", Sort.BOOL);
                }
                String predicate;
                if (isNull(argument)) {
                    predicate = "false";
                } else if (argument.sort == Sort.STRING) {
                    predicate = and(Arrays.asList(
                            stringNonNull(argument),
                            "(= " + receiver.text + " "
                                    + argument.text + ")"));
                } else {
                    return codecGap("OpStrExpression.equals",
                            "ARGUMENT_DYNAMIC_TYPE_UNMODELED", Sort.BOOL);
                }
                String defined = and(Arrays.asList(receiver.precondition,
                        stringNonNull(receiver), argument.precondition));
                return booleanStringResult(predicate, negated, defined);
            }
            if ("contains".equals(operation)
                    || "startsWith".equals(operation)
                    || "endsWith".equals(operation)) {
                List<Term> strings = exactStringParameters(params, 2);
                if (strings == null) {
                    return codecGap("OpStrExpression." + operation,
                            params.size() == 2 ? "NON_STRING_PARAMETER"
                                    : "ARITY", Sort.BOOL);
                }
                Term receiver = strings.get(0);
                Term argument = strings.get(1);
                String predicate;
                if ("contains".equals(operation)) {
                    predicate = "(str.contains " + receiver.text + " "
                            + argument.text + ")";
                } else if ("startsWith".equals(operation)) {
                    predicate = "(str.prefixof " + argument.text + " "
                            + receiver.text + ")";
                } else {
                    predicate = "(str.suffixof " + argument.text + " "
                            + receiver.text + ")";
                }
                return booleanStringResult(predicate, negated,
                        stringDereferencePrecondition(receiver, argument));
            }
            if (negated) {
                return codecGap("OpStrExpression." + operation,
                        "NEGATED_VALUE_OPERATION", Sort.STRING);
            }
            if ("concat".equals(operation)) {
                if (params.size() == 0) {
                    return codecGap("OpStrExpression.concat", "EMPTY",
                            Sort.STRING);
                }
                List<Term> strings = exactStringParameters(params,
                        params.size());
                if (strings == null) return codecGap(
                        "OpStrExpression.concat", "NON_STRING_PARAMETER",
                        Sort.STRING);
                String defined = stringDereferencePrecondition(
                        strings.toArray(new Term[strings.size()]));
                if (strings.size() == 1) {
                    return Term.nonNullString(strings.get(0).text, defined);
                }
                StringBuilder result = new StringBuilder("(str.++");
                for (Term value : strings) {
                    result.append(' ').append(value.text);
                }
                return Term.nonNullString(result.append(')').toString(),
                        defined);
            }
            if ("toString".equals(operation)) {
                if (params.size() != 1
                        || !isPrimitiveIntExpression(params.get(0))) {
                    return codecGap("OpStrExpression.toString",
                            "REQUIRES_ONE_PRIMITIVE_INT", Sort.STRING);
                }
                Term integer = term(params.get(0), Sort.INT);
                if (integer.sort != Sort.INT) {
                    return codecGap("OpStrExpression.toString",
                            "NON_INT_TERM", Sort.STRING);
                }
                assertJavaIntRange(integer);
                return javaIntString(integer);
            }
            return codecGap("OpStrExpression." + firstNonBlank(operation,
                    "unknown"), "UNSUPPORTED_OPERATION", Sort.STRING);
        }

        private List<Term> exactStringParameters(JsonArray params,
                                                 int expectedArity) {
            if (params.size() != expectedArity) return null;
            List<Term> result = new ArrayList<>();
            for (JsonElement parameter : params) {
                // Passing STRING as an expected sort would let a malformed
                // primitive SymbolExpression be declared as String. Derive
                // every operand's sort first, then accept only real strings.
                Term value = term(parameter, null);
                if (value.sort != Sort.STRING) return null;
                result.add(value);
            }
            return result;
        }

        private Term booleanStringResult(String predicate,
                                         boolean negated,
                                         String precondition) {
            return new Term(negated ? "(not " + predicate + ")"
                    : predicate, Sort.BOOL).withPrecondition(precondition);
        }

        /**
         * Recognizes the sound Java round trip
         *
         * <pre>
         * parseInt(splitElement(concat(toString(i), d, suffix),
         *                       d, [limit], 0)[, 10]) == i
         * </pre>
         *
         * and returns {@code i} itself.  Structural recognition is important:
         * a free parse/split UF would permit models that Java cannot execute.
         */
        private Term parseIntTerm(JsonObject expression) {
            JsonArray params = array(expression, "_param_list");
            if (params.size() != 1 && params.size() != 2) {
                return codecGap("java/lang/Integer.parseInt", "ARITY",
                        Sort.INT);
            }
            if (params.size() == 2) {
                Integer radix = exactIntLiteral(params.get(1));
                if (radix == null || radix != 10) {
                    return codecGap("java/lang/Integer.parseInt",
                            "RADIX_NOT_LITERAL_10", Sort.INT);
                }
            }
            SplitSegment match = exactSplitSegment(params.get(0));
            if (!match.complete()) {
                return codecGap("java/lang/Integer.parseInt",
                        "ROUNDTRIP_NOT_PROVED_" + match.gap, Sort.INT);
            }
            // parseInt inverts Integer.toString only when the element is
            // that rendering and nothing else; any surrounding text would
            // make Java throw rather than return this integer.
            SplitPiece source = match.singleIntegerPiece();
            if (source == null) {
                return codecGap("java/lang/Integer.parseInt",
                        "ROUNDTRIP_ELEMENT_NOT_ONE_INT_RENDERING", Sort.INT);
            }
            Term integer = integerPieceTerm(source);
            if (integer.sort != Sort.INT) {
                return codecGap("java/lang/Integer.parseInt",
                        "ROUNDTRIP_SOURCE_NOT_INT", Sort.INT);
            }
            assertJavaIntRange(integer);
            return integer;
        }

        private Term splitElementTerm(JsonObject expression) {
            SplitSegment match = exactSplitSegment(expression);
            if (!match.complete()) {
                return codecGap("java/lang/String.splitElement", match.gap,
                        Sort.STRING);
            }
            List<String> pieces = new ArrayList<>();
            List<String> preconditions = new ArrayList<>();
            for (SplitPiece piece : match.pieces) {
                if (piece.integerSource == null) {
                    pieces.add(quote(piece.text));
                    continue;
                }
                Term integer = integerPieceTerm(piece);
                if (integer.sort != Sort.INT) {
                    return codecGap("java/lang/String.splitElement",
                            "ROUNDTRIP_SOURCE_NOT_INT", Sort.STRING);
                }
                assertJavaIntRange(integer);
                Term rendered = javaIntString(integer);
                pieces.add(rendered.text);
                preconditions.add(rendered.precondition);
            }
            if (pieces.isEmpty()) {
                return Term.nonNullString(quote(""), "");
            }
            if (pieces.size() == 1) {
                return Term.nonNullString(pieces.get(0),
                        and(preconditions));
            }
            StringBuilder text = new StringBuilder("(str.++");
            for (String piece : pieces) text.append(' ').append(piece);
            return Term.nonNullString(text.append(')').toString(),
                    and(preconditions));
        }

        /**
         * Reads one element out of a concatenation split on a delimiter.
         *
         * <p>Java's split takes a regex, so only a delimiter that is one
         * ordinary literal character is admitted.  The concatenation is then
         * ordinary text that can be segmented statically: an exact literal
         * part contributes its own characters, and every delimiter inside it
         * ends an element.  A {@code toString(int)} part renders only digits
         * and a leading minus - exactly what {@code java_int_to_string}
         * states - so for a delimiter outside that set it provably contains
         * none.  Any other part might contain a delimiter and decides
         * nothing.</p>
         *
         * <p>The walk must reach the delimiter that closes the requested
         * element, because a later part could otherwise still extend it.  An
         * element that runs to the end of the concatenation is admitted only
         * when it is provably non-empty, since Java drops trailing empty
         * elements.</p>
         */
        private SplitSegment exactSplitSegment(JsonElement expression) {
            // A split result reaches its reader through the array the VM
            // filled in, so resolve the select-over-store first: the codec
            // lowers the same selection, and this proof inspects syntax.
            JsonElement selected =
                    ContainerSmtCodec.selectedIndexedElement(expression);
            if (selected == null || !selected.isJsonObject()) {
                return SplitSegment.gap("NOT_METHOD_EXPRESSION");
            }
            JsonObject split = selected.getAsJsonObject();
            if (!"MethodExpression".equals(string(split, "_type"))
                    || !isJavaSplitElement(string(split, "_name"))) {
                return SplitSegment.gap("NOT_STRING_SPLIT_ELEMENT");
            }
            JsonArray params = array(split, "_param_list");
            if (params.size() != 3 && params.size() != 4) {
                return SplitSegment.gap("SPLIT_ARITY");
            }

            Integer index = exactIntLiteral(params.get(params.size() - 1));
            if (index == null || index < 0) {
                return SplitSegment.gap("INDEX_NOT_EXACT_LITERAL");
            }
            String delimiter = exactStringLiteral(params.get(1));
            String delimiterGap = literalDelimiterGap(delimiter);
            if (!delimiterGap.isEmpty()) {
                return SplitSegment.gap(delimiterGap);
            }
            if (params.size() == 4) {
                Integer limit = exactIntLiteral(params.get(2));
                // A positive limit applies the pattern at most limit-1
                // times, so it has to allow the index splits that reach
                // this element plus the one that closes it.  Zero and
                // negative limits always split as far as the text goes.
                if (limit == null) {
                    return SplitSegment.gap("LIMIT_NOT_LITERAL");
                }
                if (limit > 0 && limit <= index + 1) {
                    return SplitSegment.gap("LIMIT_DOES_NOT_REACH_INDEX");
                }
            }

            ScopedExpression receiver = resolveExactEqualityBoundExpression(
                    params.get(0));
            List<JsonElement> parts = new ArrayList<>();
            if (!flattenConcat(receiver.expression, parts)) {
                return SplitSegment.gap("CONCAT_RECEIVER_REQUIRED");
            }
            return splitConcatElement(parts, receiver.invocation,
                    delimiter.charAt(0), index);
        }

        private SplitSegment splitConcatElement(List<JsonElement> parts,
                                                InvocationKey invocation,
                                                char delimiter, int index) {
            List<SplitPiece> element = new ArrayList<>();
            int segment = 0;
            for (JsonElement part : parts) {
                String literal = exactStringLiteral(part);
                if (literal != null) {
                    int start = 0;
                    while (true) {
                        int at = literal.indexOf(delimiter, start);
                        if (at < 0) break;
                        if (segment == index) {
                            addText(element,
                                    literal.substring(start, at));
                            return SplitSegment.of(element);
                        }
                        segment++;
                        start = at + 1;
                    }
                    if (segment == index) {
                        addText(element, literal.substring(start));
                    }
                    continue;
                }
                JsonElement rendered = javaIntRenderingSource(part);
                if (rendered == null) {
                    return SplitSegment.gap(
                            "PART_NOT_PROVABLY_DELIMITER_FREE");
                }
                if (Character.isDigit(delimiter) || delimiter == '-') {
                    return SplitSegment.gap(
                            "DELIMITER_OCCURS_IN_JAVA_INT_TEXT");
                }
                if (segment == index) {
                    if (!invocation.equals(currentInvocation)
                            && !invocationIndependentInteger(rendered)) {
                        return SplitSegment.gap(
                                "PRODUCER_INT_NOT_PORT_BACKED");
                    }
                    element.add(SplitPiece.integer(rendered, invocation));
                }
            }
            // Java keeps a final element only when it has characters.
            if (segment == index && !element.isEmpty()) {
                return SplitSegment.of(element);
            }
            return SplitSegment.gap(segment < index
                    ? "INDEX_BEYOND_CONCAT_ELEMENTS"
                    : "TRAILING_ELEMENT_MAY_BE_EMPTY");
        }

        /** An empty run between delimiters adds no characters. */
        private static void addText(List<SplitPiece> element, String text) {
            if (!text.isEmpty()) element.add(SplitPiece.text(text));
        }

        /**
         * Whether an int expression means the same thing in every
         * invocation.  A literal always does, and a port names one formal
         * relation variable whose witness {@link #integerPieceTerm} selects
         * by entering the stating invocation.  Anything else - a region
         * local symbol above all - is named only inside the invocation that
         * stated it, and lowering it elsewhere would invent a free value.
         */
        private boolean invocationIndependentInteger(
                JsonElement expression) {
            if (exactIntLiteral(expression) != null) return true;
            if (expression == null || !expression.isJsonObject()) {
                return false;
            }
            JsonObject object = expression.getAsJsonObject();
            return "SymbolExpression".equals(string(object, "_type"))
                    && !findPort(string(object, "_exp")).isEmpty();
        }

        /** Lowers a split piece's int in the invocation that states it. */
        private Term integerPieceTerm(SplitPiece piece) {
            if (piece.integerInvocation == null
                    || piece.integerInvocation.equals(currentInvocation)) {
                return term(piece.integerSource, Sort.INT);
            }
            InvocationKey previous =
                    enterInvocation(piece.integerInvocation);
            try {
                return term(piece.integerSource, Sort.INT);
            } finally {
                restoreInvocation(previous);
            }
        }

        /** The int a {@code String.valueOf(int)} style part renders. */
        private JsonElement javaIntRenderingSource(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return null;
            JsonObject object = expression.getAsJsonObject();
            JsonArray params = array(object, "_param_list");
            if (!"OpStrExpression".equals(string(object, "_type"))
                    || !"toString".equals(string(object, "_name"))
                    || bool(object, "_is_not", false)
                    || params.size() != 1
                    || !isPrimitiveIntExpression(params.get(0))) {
                return null;
            }
            return params.get(0);
        }

        /**
         * Chases only exact, uniquely selected String equality edges.  The
         * returned producer expression is still connected to the consumer
         * port by the ordinary merge assertion; this lookup merely exposes
         * its syntax to a structural codec proof.
         */
        private ScopedExpression resolveExactEqualityBoundExpression(
                JsonElement expression) {
            JsonElement current = expression;
            Set<PortOccurrence> visited = new LinkedHashSet<>();
            InvocationKey invocation = currentInvocation;
            while (current != null && current.isJsonObject()) {
                JsonObject object = current.getAsJsonObject();
                if (!"SymbolExpression".equals(string(object, "_type"))) {
                    break;
                }
                String port = findPort(string(object, "_exp"));
                PortOccurrence occurrence =
                        occurrence(invocation.instanceId, port);
                if (port.isEmpty() || !visited.add(occurrence)
                        || ambiguousEqualityBoundExpressionPorts.contains(
                        occurrence)) {
                    break;
                }
                EqualityBoundExpression binding =
                        exactEqualityBoundExpressions.get(occurrence);
                if (binding == null) break;
                current = binding.expression;
                invocation = new InvocationKey(
                        regionOf(binding.outputPort),
                        binding.sourceInstance);
            }
            return new ScopedExpression(current, invocation);
        }

        private boolean flattenConcat(JsonElement expression,
                                      List<JsonElement> result) {
            if (expression == null || !expression.isJsonObject()) {
                return false;
            }
            JsonObject object = expression.getAsJsonObject();
            if (!"OpStrExpression".equals(string(object, "_type"))
                    || !"concat".equals(string(object, "_name"))
                    || bool(object, "_is_not", false)) {
                return false;
            }
            JsonArray params = array(object, "_param_list");
            if (params.size() == 0) return false;
            for (JsonElement parameter : params) {
                if (parameter != null && parameter.isJsonObject()
                        && "OpStrExpression".equals(string(
                        parameter.getAsJsonObject(), "_type"))
                        && "concat".equals(string(
                        parameter.getAsJsonObject(), "_name"))) {
                    if (!flattenConcat(parameter, result)) return false;
                } else {
                    result.add(parameter);
                }
            }
            return true;
        }

        private boolean provablyStringValued(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return false;
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if ("ConStringSymbolExp".equals(type)) return true;
            if ("SymbolExpression".equals(type)
                    || "ConSymbolExp".equals(type)
                    || "ConstExpr".equals(type)) {
                return sortOfJava(string(object, "_java_type"))
                        == Sort.STRING;
            }
            if (!"OpStrExpression".equals(type)
                    || bool(object, "_is_not", false)) return false;
            String operation = string(object, "_name");
            if ("toString".equals(operation)) {
                JsonArray params = array(object, "_param_list");
                return params.size() == 1
                        && isPrimitiveIntExpression(params.get(0));
            }
            if (!"concat".equals(operation)) return false;
            JsonArray params = array(object, "_param_list");
            if (params.size() == 0) return false;
            for (JsonElement parameter : params) {
                if (!provablyStringValued(parameter)) return false;
            }
            return true;
        }

        private Term javaIntString(Term integer) {
            return Term.nonNullString("(java_int_to_string "
                    + integer.text + ")", integer.precondition);
        }

        private void assertJavaIntRange(Term integer) {
            String key = currentGuard + "\u0000" + integer.text;
            if (!javaIntRangeAssertions.add(key)) return;
            assertNamed("java_int_range_" + javaIntRangeAssertions.size(),
                    "(and (<= (- 2147483648) " + integer.text + ")"
                            + " (<= " + integer.text + " 2147483647))");
        }

        private void assertJavaIntegralDomain(String term, Sort sort,
                                              String javaType,
                                              String identity) {
            if (sort != Sort.INT) return;
            JavaPrimitiveSmtSemantics.IntegralDomain domain =
                    JavaPrimitiveSmtSemantics.domainOfJavaType(javaType);
            if (domain == null || term == null || term.isEmpty()) return;
            String key = currentGuard + "\u0000" + term + "\u0000"
                    + domain.lower + "\u0000" + domain.upper;
            if (!javaIntegralRangeAssertions.add(key)) return;
            assertNamed("java_integral_domain_"
                            + javaIntegralRangeAssertions.size() + "_"
                            + smtName(firstNonBlank(identity, "value")),
                    "(and (<= " + domain.lower + " " + term + ")"
                            + " (<= " + term + " " + domain.upper + "))");
        }

        private Term codecGap(String operation, String gap, Sort sort) {
            unsupported.add("MODEL_SEMANTICS_MISSING:" + operation + ":"
                    + gap);
            return unsupportedTerm(sort);
        }

        private boolean isPrimitiveIntExpression(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return false;
            JsonObject object = expression.getAsJsonObject();
            String javaType = string(object, "_java_type");
            return "I".equals(javaType) || "int".equals(javaType);
        }

        private Integer exactIntLiteral(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return null;
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if (!("ConstExpr".equals(type) || "ConSymbolExp".equals(type))) {
                return null;
            }
            String javaType = string(object, "_java_type");
            if (!("I".equals(javaType) || "int".equals(javaType))) {
                return null;
            }
            String value = constantPayload(string(object, "_exp"));
            if (!value.matches("-?[0-9]+")) return null;
            try {
                return Integer.valueOf(value);
            } catch (NumberFormatException ignored) {
                return null;
            }
        }

        private String exactStringLiteral(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return null;
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if (!("ConStringSymbolExp".equals(type)
                    || "ConstExpr".equals(type)
                    || "ConSymbolExp".equals(type))) return null;
            if (sortOfJava(string(object, "_java_type")) != Sort.STRING) {
                return null;
            }
            return constantPayload(string(object, "_exp"));
        }

        /**
         * Admits only a delimiter that is one ordinary literal character.
         *
         * <p>Java splits on a regex, so a metacharacter would match text
         * this segmentation never sees.  A delimiter made only of digits or
         * a minus is still admitted here and refused later, but only if an
         * integer rendering actually takes part.</p>
         */
        private String literalDelimiterGap(String value) {
            if (value == null || value.length() != 1) {
                return "REGEX_NOT_SAFE_SINGLE_LITERAL";
            }
            char delimiter = value.charAt(0);
            if (Character.isISOControl(delimiter)) {
                return "REGEX_NOT_SAFE_SINGLE_LITERAL";
            }
            if ("\\.^$|?*+()[]{}".indexOf(delimiter) >= 0) {
                return "REGEX_NOT_SAFE_SINGLE_LITERAL";
            }
            return "";
        }

        private String methodConstraint(JsonObject expression) {
            String name = string(expression, "_name");
            if (isJavaParseInt(name) || isJavaSplitElement(name)) {
                boolean split = isJavaSplitElement(name);
                Term value = methodTerm(expression);
                Term result = term(expression.get("_res_exp"),
                        split ? Sort.STRING : Sort.INT);
                if (!split) {
                    return and(Arrays.asList(result.precondition,
                            value.precondition, "(= " + result.text + " "
                                    + value.text + ")"));
                }
                Term boxedPrefix = asValue(value);
                Term boxedResult = asValue(result);
                return and(Arrays.asList(boxedPrefix.precondition,
                        boxedResult.precondition, "(= " + boxedResult.text
                                + " " + boxedPrefix.text + ")"));
            }
            unsupported.add("MODEL_SEMANTICS_MISSING:MethodExpression:"
                    + firstNonBlank(name, "unknown"));
            return "false";
        }

        private Term methodTerm(JsonObject expression) {
            String method = string(expression, "_name");
            if (isJavaParseInt(method)) {
                return parseIntTerm(expression);
            }
            if (isJavaSplitElement(method)) {
                return splitElementTerm(expression);
            }
            Term result = term(expression.get("_res_exp"), null);
            unsupported.add("MODEL_SEMANTICS_MISSING:MethodExpression:"
                    + firstNonBlank(method, "unknown"));
            return unsupportedTerm(result.sort);
        }

        private void regionSummaryWithBoundedTimeline(
                RelationSummary selected) {
            BoundedTimelineStep timeline = BoundedTimelineStep.from(selected);
            if (timeline == null) {
                regionSummary(selected);
                return;
            }
            if (!timeline.blocker.isEmpty()) {
                unsupported.add("BoundedContainerTimelineGap:"
                        + selected.regionId() + ":" + timeline.blocker);
                regionSummary(selected);
                return;
            }
            if (timeline.bound < 1
                    || ports.sort(timeline.preStatePort) != Sort.MAP
                    || ports.sort(timeline.postStatePort) != Sort.MAP) {
                unsupported.add("BoundedContainerTimelineGap:"
                        + selected.regionId() + ":INVALID_STATE_PORTS");
                regionSummary(selected);
                return;
            }

            InvocationKey canonical = new InvocationKey(
                    selected.regionId(), selected.regionInstanceId());
            Map<String, String> recurrence = timelineRecurrencePairs(
                    selected, timeline);
            Set<String> frozen = timelineFrozenInputs(selected,
                    recurrence.keySet());
            Set<String> derived = timelineDerivedInputs(selected, timeline);
            if (!recurrence.containsKey(timeline.preStatePort)
                    || !classifiedTimelineInputs(selected, recurrence,
                    frozen, derived)) {
                unsupported.add("BoundedContainerTimelineGap:"
                        + selected.regionId() + ":UNCLASSIFIED_INPUT");
                regionSummary(selected);
                return;
            }
            Map<String, List<TimelineCut>> outputCuts = new LinkedHashMap<>();
            for (String output : selected.outputClosure().outputPorts()) {
                outputCuts.put(output, new ArrayList<TimelineCut>());
            }
            Map<String, PortOccurrence> previousOutputsByInput =
                    new LinkedHashMap<>();
            for (int ordinal = 0; ordinal < timeline.bound; ordinal++) {
                InvocationKey invocation = ordinal == 0 ? canonical
                        : new InvocationKey(selected.regionId(),
                        selected.regionInstanceId() + "#boundedStep"
                                + ordinal);
                regionSummary(selected, invocation, "bounded-step-"
                        + ordinal);
                if (ordinal == 0) {
                    // Cut zero exists only for an explicit recurrence pair.
                    for (Map.Entry<String, String> pair
                            : recurrence.entrySet()) {
                        outputCuts.get(pair.getValue()).add(new TimelineCut(
                                new PortOccurrence(invocation,
                                        pair.getKey()), 0));
                    }
                } else {
                    for (Map.Entry<String, String> pair
                            : recurrence.entrySet()) {
                        PortOccurrence previous = previousOutputsByInput.get(
                                pair.getKey());
                        PortOccurrence input = new PortOccurrence(invocation,
                                pair.getKey());
                        if (previous == null) {
                            unsupported.add("BoundedContainerTimelineGap:"
                                    + selected.regionId()
                                    + ":MISSING_RECURRENCE_OUTPUT:"
                                    + pair.getKey());
                            continue;
                        }
                        assertPortEquality(previous, input,
                                "container_timeline_chain_"
                                        + scopeToken(timeline
                                        .channelIdentity(selected)) + "_"
                                        + smtName(pair.getKey()) + "_"
                                        + ordinal);
                    }
                }
                if (ordinal > 0) {
                    for (String external : frozen) {
                        assertPortEquality(new PortOccurrence(canonical,
                                        external),
                                new PortOccurrence(invocation, external),
                                "container_timeline_frozen_input_"
                                        + scopeToken(timeline
                                        .channelIdentity(selected)) + "_"
                                        + smtName(external) + "_" + ordinal);
                    }
                }
                int cut = ordinal + 1;
                for (String output : outputCuts.keySet()) {
                    outputCuts.get(output).add(new TimelineCut(
                            new PortOccurrence(invocation, output), cut));
                }
                for (Map.Entry<String, String> pair
                        : recurrence.entrySet()) {
                    previousOutputsByInput.put(pair.getKey(),
                            new PortOccurrence(invocation,
                                    pair.getValue()));
                }
            }
            String channel = timeline.channelIdentity(selected);
            for (Map.Entry<String, List<TimelineCut>> output
                    : outputCuts.entrySet()) {
                boundedTimelineOutputs.put(new PortOccurrence(canonical,
                                output.getKey()),
                        new TimelineOutputExpansion(channel,
                                output.getValue()));
            }
        }

        private Map<String, String> timelineRecurrencePairs(
                RelationSummary selected, BoundedTimelineStep timeline) {
            Map<String, String> result = new LinkedHashMap<>();
            result.put(timeline.preStatePort, timeline.postStatePort);
            Set<String> usedOutputs = new LinkedHashSet<>(result.values());
            for (String input : selected.outputClosure().executionScope()
                    .inputPorts()) {
                if (result.containsKey(input)) continue;
                String match = "";
                for (String output : selected.outputClosure().outputPorts()) {
                    if (usedOutputs.contains(output)
                            || !ports.sameStateCell(input, output)) {
                        continue;
                    }
                    if (!match.isEmpty()) {
                        match = "";
                        break;
                    }
                    match = output;
                }
                if (!match.isEmpty()) {
                    result.put(input, match);
                    usedOutputs.add(match);
                }
            }
            return result;
        }

        private Set<String> timelineFrozenInputs(RelationSummary selected,
                                                 Set<String> recurrent) {
            Set<String> result = new LinkedHashSet<>();
            for (String input : selected.outputClosure().executionScope()
                    .inputPorts()) {
                if (!recurrent.contains(input)
                        && ports.explicitReplayInvariant(input)) {
                    result.add(input);
                }
            }
            return result;
        }

        /**
         * Finds scalar inputs the VM defines from the current timeline state.
         * Every case that mentions such an input must contain its own exact
         * field materialization, and that field owner must be rooted only in
         * this timeline's pre-state port.  Alpha-renaming can then apply the
         * relation at each step without either freeing the scalar or freezing
         * an old member's value after the container changes.
         */
        private Set<String> timelineDerivedInputs(
                RelationSummary selected, BoundedTimelineStep timeline) {
            Set<String> derived = new LinkedHashSet<>();
            Set<String> unsafe = new LinkedHashSet<>();
            for (JsonElement element : array(object(selected.toJson(),
                    "regionRelation"), "cases")) {
                if (!element.isJsonObject()) continue;
                JsonObject pathCase = element.getAsJsonObject();
                Set<String> mentioned = new LinkedHashSet<>();
                collectTimelineInputPorts(pathCase, selected.regionId(),
                        mentioned);
                Set<String> defined = new LinkedHashSet<>();
                collectTimelineFieldDefinitions(pathCase,
                        selected.regionId(), timeline.preStatePort, defined);
                derived.addAll(defined);
                for (String input : mentioned) {
                    if (!defined.contains(input)) unsafe.add(input);
                }
            }
            derived.removeAll(unsafe);
            return derived;
        }

        private void collectTimelineFieldDefinitions(
                JsonElement expression, String region, String preStatePort,
                Set<String> result) {
            if (expression == null || expression.isJsonNull()) return;
            if (expression.isJsonArray()) {
                for (JsonElement item : expression.getAsJsonArray()) {
                    collectTimelineFieldDefinitions(item, region,
                            preStatePort, result);
                }
                return;
            }
            if (!expression.isJsonObject()) return;
            JsonObject object = expression.getAsJsonObject();
            if (ContainerSmtCodec.handlesFieldBinding(object)) {
                JsonElement left = object.get("_left");
                JsonElement right = object.get("_right");
                JsonElement field = ContainerSmtCodec.handlesField(left)
                        ? left : right;
                JsonElement symbol = field == left ? right : left;
                Set<String> ownerInputs = new LinkedHashSet<>();
                collectTimelineInputPorts(field, region, ownerInputs);
                String input = symbol != null && symbol.isJsonObject()
                        ? findPort(string(symbol.getAsJsonObject(), "_exp"))
                        : "";
                if (ports.isInput(input) && region.equals(regionOf(input))
                        && ownerInputs.size() == 1
                        && ownerInputs.contains(preStatePort)) {
                    result.add(input);
                }
                return;
            }
            for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
                collectTimelineFieldDefinitions(entry.getValue(), region,
                        preStatePort, result);
            }
        }

        /** Every relation-mentioned repeated input is either an exact
         * recurrence pair or an explicitly replay-invariant port.  Static
         * closure inputs that the VM relation does not mention create no SMT
         * term and therefore no new freedom on an alpha-renamed step. */
        private boolean classifiedTimelineInputs(RelationSummary selected,
                                                 Map<String, String> recurrence,
                                                 Set<String> frozen,
                                                 Set<String> derived) {
            for (String input : frozen) {
                if (!ports.isInput(input)
                        || !selected.regionId().equals(regionOf(input))) {
                    return false;
                }
            }
            for (String input : derived) {
                if (!ports.isInput(input)
                        || !selected.regionId().equals(regionOf(input))) {
                    return false;
                }
            }
            Set<String> mentioned = new LinkedHashSet<>();
            collectTimelineInputPorts(object(selected.toJson(),
                    "regionRelation"), selected.regionId(), mentioned);
            Set<String> classified = new LinkedHashSet<>(frozen);
            classified.addAll(recurrence.keySet());
            classified.addAll(derived);
            Set<String> scoped = selected.outputClosure().executionScope()
                    .inputPorts();
            return scoped.containsAll(mentioned)
                    && classified.containsAll(mentioned);
        }

        private void collectTimelineInputPorts(JsonElement expression,
                                               String region,
                                               Set<String> result) {
            if (expression == null || expression.isJsonNull()) return;
            if (expression.isJsonArray()) {
                for (JsonElement item : expression.getAsJsonArray()) {
                    collectTimelineInputPorts(item, region, result);
                }
                return;
            }
            if (!expression.isJsonObject()) return;
            JsonObject object = expression.getAsJsonObject();
            if ("SymbolExpression".equals(string(object, "_type"))) {
                String port = findPort(string(object, "_exp"));
                if (ports.isInput(port) && region.equals(regionOf(port))) {
                    result.add(port);
                }
            }
            for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
                collectTimelineInputPorts(entry.getValue(), region, result);
            }
        }

        private void regionSummary(RelationSummary selected) {
            regionSummary(selected, new InvocationKey(selected.regionId(),
                    selected.regionInstanceId()), "selected");
        }

        private void regionSummary(RelationSummary selected,
                                   InvocationKey invocation,
                                   String scopeSuffix) {
            JsonObject summary = selected.toJson();
            OutputClosureContract outputClosure =
                    selected.outputClosure();
            String region = outputClosure.producer().regionId();
            if (!bool(summary, "relationallyComplete", false)) {
                heapGap("IncompleteRegionSummary@" + region);
                return;
            }
            JsonObject relation = object(summary, "regionRelation");
            if (!"GUARDED_PATH_MERGE".equals(string(relation, "kind"))) {
                heapGap("UnsupportedRegionRelation@" + region);
                return;
            }
            String previousScope = enterSymbolScope("summary:"
                    + firstNonBlank(string(summary, "summaryId"),
                    region, "selected") + ":" + scopeSuffix + ":"
                    + invocation.instanceId);
            InvocationKey previousInvocation = enterInvocation(invocation);
            try {
                guardedRegionRelation(invocation, relation, outputClosure);
            } finally {
                restoreInvocation(previousInvocation);
                restoreSymbolScope(previousScope);
            }
        }

        private void guardedRegionRelation(InvocationKey invocation,
                                           JsonObject relation,
                                           OutputClosureContract outputClosure) {
            String region = invocation.regionId;
            JsonArray cases = array(relation, "cases");
            if (cases.size() == 0) {
                heapGap("GuardedPathCaseCountGap@" + region);
                return;
            }
            List<String> selectors = new ArrayList<>();
            Set<String> selectorSymbols = new LinkedHashSet<>();
            String previousGuard = currentGuard;
            for (int index = 0; index < cases.size(); index++) {
                // Guard construction belongs to the outer relation.  Leaving
                // case N's implication active here would bind case N+1 inputs
                // under the wrong path.
                currentGuard = previousGuard;
                if (!cases.get(index).isJsonObject()) {
                    heapGap("MalformedGuardedPathCase@" + region
                            + ":" + index);
                    continue;
                }
                JsonObject item = cases.get(index).getAsJsonObject();
                if (string(item, "sourceTaskId").isEmpty()) {
                    heapGap("MissingRegionCaseSourceTask@" + region
                            + ":" + index);
                    continue;
                }
                Set<String> casePorts = new LinkedHashSet<>(
                        object(item, "outputExpressions").keySet());
                casePorts.addAll(object(item,
                        "outputReferenceIdentities").keySet());
                if (outputClosure.outputPorts().size() > 1
                        && !casePorts.equals(outputClosure.outputPorts())) {
                    heapGap("JointOutputExpressionSetMismatch@" + region
                            + ":" + index);
                    continue;
                }
                JsonObject guardIr = object(item, "guard");
                if (!"PATH_CONDITION".equals(string(guardIr, "kind"))) {
                    heapGap("UnsupportedRegionGuard@" + region
                            + ":" + index);
                    continue;
                }
                String caseIdentity = "region:" + region + "/instance:"
                        + invocation.instanceId + "/case:"
                        + firstNonBlank(string(item, "caseId"),
                        String.valueOf(index));
                String previousScope = enterSymbolScope(caseIdentity);
                try {
                    List<String> conditionTerms = new ArrayList<>();
                    for (JsonElement expression : array(guardIr,
                            "conditions")) {
                        conditionTerms.add(constraint(expression,
                                "region " + region + " case " + index));
                    }
                    String guard = and(conditionTerms);
                    String selector = "case_selector__"
                            + scopeToken(caseIdentity);
                    if (!selectorSymbols.add(selector)) {
                        heapGap("DuplicateCaseSelector@" + region + ":"
                                + index);
                    }
                    selectors.add(selector);
                    declare(selector, Sort.BOOL);
                    assertNamed("case_selector_definition_" + region + "_"
                                    + index,
                            "(= " + selector + " " + guard + ")");
                    currentGuard = selector;
                    recordFatalAbsenceRemovalEffects(invocation, item,
                            selector);
                    bindOutputExpressions(region, item, outputClosure);
                } finally {
                    currentGuard = previousGuard;
                    restoreSymbolScope(previousScope);
                }
            }
            currentGuard = previousGuard;
            if (selectors.size() == cases.size() && !selectors.isEmpty()) {
                StringBuilder partition = new StringBuilder("(= (+");
                for (String selector : selectors) {
                    partition.append(" (ite ").append(selector)
                            .append(" 1 0)");
                }
                assertNamed("region_case_selector_partition_" + region,
                        partition.append(") 1)").toString());
            } else {
                heapGap("CaseSelectorPartitionGap@" + region);
            }
        }

        private void recordFatalAbsenceRemovalEffects(
                InvocationKey invocation, JsonObject pathCase,
                String selector) {
            for (String output : failureWitness.outputsFor(invocation)) {
                JsonElement expression = object(pathCase,
                        "outputExpressions").get(output);
                if (expression == null) continue;
                Set<String> previousRequirements =
                        currentContainerRequirements;
                Set<String> requirements = new LinkedHashSet<>();
                currentContainerRequirements = requirements;
                List<ContainerSmtCodec.AssociativeRemovalEffect> effects;
                try {
                    effects = ContainerSmtCodec
                            .associativeRemovalEffects(expression,
                                    containerHost());
                } finally {
                    currentContainerRequirements = previousRequirements;
                }
                PortOccurrence source = new PortOccurrence(invocation,
                        output);
                for (ContainerSmtCodec.AssociativeRemovalEffect effect
                        : effects) {
                    List<String> preconditions = new ArrayList<>(requirements);
                    preconditions.add(effect.precondition);
                    failureWitness.addEffect(source,
                            new FatalAbsenceMutationWitness.RemovalCaseEffect(
                                    selector, effect.removedKey.text,
                                    and(preconditions)));
                }
            }
        }

        private void bindOutputExpressions(String region,
                                           JsonObject summary,
                                           OutputClosureContract closure) {
            JsonObject outputs = object(summary, "outputExpressions");
            for (Map.Entry<String, JsonElement> entry
                    : outputs.entrySet()) {
                String port = entry.getKey();
                if (!ports.contains(port)
                        || !entry.getValue().isJsonObject()) {
                    heapGap("OutputExpressionEndpoint@" + region + ":"
                            + port);
                    continue;
                }
                requireExactRuntimePutReferenceValue(port,
                        entry.getValue(), closure);
                requireObservedSnapshotReferenceMembers(entry.getValue());
                Term value = term(entry.getValue(), portSort(port));
                if (value.sort == Sort.MAP
                        || value.sort == Sort.ARRAY_VALUE) {
                    promotePort(port, value.sort);
                }
                bindPort(port, value);
            }
            bindReferenceIdentityOutputs(region, summary, closure);
        }

        /**
         * Preserves the non-null identity of the reference value observed by
         * one exact runtime {@code Map.put} completion.
         *
         * <p>The selected output event is the join key between the imported
         * output closure and the static port's runtime-access ledger.  A
         * constraint is emitted only when that join selects exactly one
         * access in the same root invocation, the access carries the exact
         * associative-put provenance authority, and its recorded value object
         * id is non-zero.  Consequently no Java type, symbol spelling, or
         * application-specific name is used to infer nullness.</p>
         *
         * <p>That runtime event completes the outermost mutation represented
         * by the selected output expression.  Earlier {@code PUT}s on the
         * receiver spine are not constrained by this evidence.</p>
         */
        private void requireExactRuntimePutReferenceValue(
                String port, JsonElement expression,
                OutputClosureContract closure) {
            OutputClosureContract.Member member = closure.member(port);
            Port schema = ports.get(port);
            if (member == null || schema == null
                    || expression == null || !expression.isJsonObject()) {
                return;
            }
            long selectedEvent = longInteger(member.slice(),
                    "selectedRuntimeEventSeq", -1L);
            if (selectedEvent < 0L) return;

            JsonObject selectedAccess = null;
            int selectedAccessCount = 0;
            for (JsonElement element : array(schema.metadata,
                    "runtimeAccesses")) {
                if (!element.isJsonObject()) continue;
                JsonObject access = element.getAsJsonObject();
                if (longInteger(access, "eventSeq", -1L)
                        != selectedEvent
                        || longInteger(access, "rootCallId", -1L)
                        != closure.producer().rootCallId()) {
                    continue;
                }
                selectedAccess = access;
                selectedAccessCount++;
            }
            if (selectedAccessCount != 1
                    || !"EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1"
                    .equals(string(selectedAccess,
                            "containerMemberIdentityAuthority"))
                    || longInteger(selectedAccess,
                            "containerValueObjectId", 0L) <= 0L) {
                return;
            }

            JsonObject relation = expression.getAsJsonObject();
            JsonArray arguments = array(relation, "arguments");
            if (!ContainerSmtCodec.EXPRESSION_TYPE.equals(
                    string(relation, "_type"))
                    || !"ASSOCIATIVE".equals(string(relation, "shape"))
                    || !"PUT".equals(string(relation, "operation"))
                    || arguments.size() != 2) {
                return;
            }
            JsonElement valueExpression = arguments.get(1);
            Term value = term(valueExpression, null);
            if (value.sort != Sort.REF || isNull(value)) return;
            String identity = currentSymbolScope + "\u0000" + port
                    + "\u0000" + selectedEvent + "\u0000"
                    + longInteger(selectedAccess,
                    "containerValueObjectId", 0L) + "\u0000"
                    + CanonicalJson.render(valueExpression);
            assertNamed("exact_runtime_put_reference_non_null_"
                            + CanonicalJson.sha256(identity)
                            .substring(0, 16),
                    "(distinct " + value.text + " nullRef)");
        }

        /**
         * Passes a reference-only output on as the alias it recorded.
         *
         * <p>A reference the custom VM never symbolised was recorded by
         * identity: the producer says which object it handed on, and nothing
         * about any value inside it.  Naming that object is exactly what the
         * relation states, so the port is bound to one constant per recorded
         * identity - equal producers hand on equal objects, and a concrete
         * object is not null.  No value is claimed to live inside it.</p>
         *
         * <p>What such an alias cannot answer is a consumer reading a scalar
         * leaf below the reference: that leaf needs its own producer.  So
         * every other output this closure demands is checked one leaf at a
         * time, and only a leaf left without a producer is reported.  A leaf
         * that has its own versioned writer is already constrained and the
         * alias is all that was missing.</p>
         */
        private void bindReferenceIdentityOutputs(
                String region, JsonObject summary,
                OutputClosureContract closure) {
            JsonObject identities = object(summary,
                    "outputReferenceIdentities");
            if (identities.size() == 0) return;
            for (Map.Entry<String, JsonElement> entry
                    : identities.entrySet()) {
                String port = entry.getKey();
                if (!ports.contains(port)) continue;
                if (!bindConcreteReferenceIdentity(port, entry.getValue())) {
                    heapGap("ConcreteReferenceIdentityWithoutLeafProducer@"
                            + region + ":" + port);
                    continue;
                }
                for (String demanded : closure.outputPorts()) {
                    if (identities.has(demanded)
                            || !ports.contains(demanded)
                            || boundPorts.contains(
                            currentOccurrence(demanded))) {
                        continue;
                    }
                    heapGap("ConcreteReferenceIdentityWithoutLeafProducer@"
                            + region + ":" + demanded);
                }
            }
        }

        /**
         * Binds one port to the object a concrete reference identity names.
         *
         * <p>The constant is derived from the recorded identity, so two
         * producers that recorded the same object reach the same constant and
         * the alias travels.  Two different records stay merely unequated:
         * nothing asserts they denote different objects.</p>
         */
        private boolean bindConcreteReferenceIdentity(String port,
                                                      JsonElement identity) {
            if (identity == null || !identity.isJsonObject()) return false;
            JsonObject record = identity.getAsJsonObject();
            if (!ConcolicSummaryImporter
                    .CONCRETE_REFERENCE_IDENTITY_AUTHORITY.equals(
                    string(record, "authority"))) {
                return false;
            }
            String constant = "reference_identity__"
                    + scopeToken(CanonicalJson.render(record));
            if (declaredReferenceIdentities.add(constant)) {
                declare(constant, Sort.REF);
                String previousGuard = currentGuard;
                currentGuard = "";
                try {
                    assertNamed(constant + "_non_null",
                            "(distinct " + constant + " nullRef)");
                } finally {
                    currentGuard = previousGuard;
                }
            }
            bindPort(port, new Term(constant, Sort.REF));
            return boundPorts.contains(currentOccurrence(port));
        }

        /**
         * Normal-exit container outputs are rebuilt by the runtime from the
         * members that Java actually observed: {@code SNAPSHOT_BASE} followed
         * by {@code PUT}/{@code APPEND} (recordings taken before the base got
         * its own op name write {@code CLEAR} there).  A non-null member is
         * represented by a
         * VM reference symbol, while an observed null is the dedicated
         * {@code N} expression.  Preserve that distinction in the selected
         * path case; otherwise SMT may alias a concrete object identity with
         * {@code nullRef} and manufacture a missing map value.
         *
         * <p>This deliberately applies only to the snapshot suffix of a
         * captured output. Ordinary symbolic reference inputs, including
         * nullable map values, remain nullable.</p>
         */
        private void requireObservedSnapshotReferenceMembers(
                JsonElement expression) {
            List<JsonElement> members = new ArrayList<>();
            JsonElement cursor = expression;
            boolean exactSnapshot = false;
            while (cursor != null && cursor.isJsonObject()) {
                JsonObject relation = cursor.getAsJsonObject();
                if (!ContainerSmtCodec.EXPRESSION_TYPE.equals(
                        string(relation, "_type"))) {
                    break;
                }
                String operation = string(relation, "operation");
                if (ContainerSmtCodec.emptiesState(operation)) {
                    exactSnapshot = true;
                    break;
                }
                String shape = string(relation, "shape");
                JsonArray arguments = array(relation, "arguments");
                if ("ASSOCIATIVE".equals(shape)
                        && "PUT".equals(operation)
                        && arguments.size() == 2) {
                    members.add(arguments.get(0));
                    members.add(arguments.get(1));
                } else if ("INDEXED".equals(shape)
                        && "APPEND".equals(operation)
                        && arguments.size() == 1) {
                    members.add(arguments.get(0));
                } else {
                    break;
                }
                cursor = relation.get("receiver");
            }
            if (!exactSnapshot) return;

            for (JsonElement member : members) {
                Term value = term(member, null);
                if (value.sort != Sort.REF || isNull(value)) continue;
                String identity = currentSymbolScope + "\u0000"
                        + CanonicalJson.render(member);
                assertNamed("observed_snapshot_reference_non_null_"
                                + CanonicalJson.sha256(identity)
                                .substring(0, 16),
                        "(distinct " + value.text + " nullRef)");
            }
        }

        private void heapGap(String detail) {
            unsupported.add(detail);
        }

        private void merge(JsonObject context) {
            for (JsonElement element : array(context, "equalityClasses")) {
                if (!element.isJsonObject()) continue;
                JsonArray members = array(element.getAsJsonObject(), "members");
                List<String> selected = new ArrayList<>();
                for (JsonElement member : members) {
                    if (!member.isJsonPrimitive()) continue;
                    String endpoint = member.getAsString();
                    if (currentInvocation.regionId.equals(
                            regionOf(endpoint))) {
                        selected.add(endpoint);
                    }
                }
                if (selected.size() < 2) continue;
                String first = selected.get(0);
                for (int index = 1; index < selected.size(); index++) {
                    assertPortEquality(first, selected.get(index), "alias");
                }
            }
            Map<PortOccurrence, List<VersionedWriter>> contextWriters =
                    new LinkedHashMap<>();
            Map<PortOccurrence, List<String>> contextChannels =
                    new LinkedHashMap<>();
            for (JsonElement element : array(context,
                    "versionedStateMerges")) {
                if (!element.isJsonObject()) continue;
                JsonObject relation = element.getAsJsonObject();
                String from = string(relation, "fromEndpoint");
                String to = string(relation, "toEndpoint");
                JsonArray bindings = selectedBindings(relation);
                if (!allTrustedReadFromEvidence(bindings)) {
                    unsupported.add("UntrustedVersionedStateReadFrom:"
                            + string(relation, "edgeId"));
                    continue;
                }
                for (int index = 0; index < bindings.size(); index++) {
                    JsonObject binding = bindings.get(index).getAsJsonObject();
                    PortOccurrence target = occurrence(
                            bindingTargetInstance(binding), to);
                    contextWriters.computeIfAbsent(target,
                            ignored -> new ArrayList<>()).add(
                            new VersionedWriter(binding,
                            occurrence(bindingSourceInstance(binding), from),
                            firstNonBlank(string(relation, "guardSymbol"),
                                    "")));
                    contextChannels.computeIfAbsent(target,
                            ignored -> new ArrayList<>()).add(
                            firstNonBlank(string(relation, "edgeId"),
                                    "state_edge"));
                }
            }
            for (Map.Entry<PortOccurrence, List<VersionedWriter>> entry
                    : contextWriters.entrySet()) {
                List<String> channels = contextChannels.get(entry.getKey());
                String channel = entry.getValue().size() == 1
                        && channels != null && !channels.isEmpty()
                        ? channels.get(0)
                        : "versioned_state_channel__" + entry.getKey();
                emitVersionedReadChoice(channel, entry.getValue(),
                        entry.getKey());
            }
            for (JsonElement element : array(context,
                    "alternativeWriterGroups")) {
                if (!element.isJsonObject()) continue;
                JsonObject group = element.getAsJsonObject();
                JsonArray alternatives = array(group, "alternatives");
                String groupId = firstNonBlank(string(group, "groupId"),
                        "alternative");
                if (!"EXACTLY_ONE_GUARDED".equals(string(group,
                        "selectionSemantics")) || alternatives.size() < 2) {
                    unsupported.add("MalformedAlternativeWriterGroup:"
                            + groupId);
                    continue;
                }
                List<VersionedWriter> writers = new ArrayList<>();
                PortOccurrence target = null;
                for (int index = 0; index < alternatives.size(); index++) {
                    if (!alternatives.get(index).isJsonObject()) continue;
                    JsonObject relation = alternatives.get(index)
                            .getAsJsonObject();
                    String from = string(relation, "fromEndpoint");
                    String to = string(relation, "toEndpoint");
                    if (!allTrustedReadFromEvidence(
                            selectedBindings(relation))) {
                        unsupported.add("UntrustedAlternativeWriterReadFrom:"
                                + groupId + ":" + index);
                        continue;
                    }
                    JsonArray bindings = selectedBindings(relation);
                    for (JsonElement bindingElement : bindings) {
                        JsonObject binding = bindingElement.getAsJsonObject();
                        PortOccurrence candidateTarget = occurrence(
                                bindingTargetInstance(binding), to);
                        if (target != null && !target.equals(candidateTarget)) {
                            unsupported.add("AlternativeWriterTargetMismatch:"
                                    + groupId);
                            continue;
                        }
                        target = candidateTarget;
                        writers.add(new VersionedWriter(binding,
                                occurrence(bindingSourceInstance(binding),
                                        from),
                                string(relation, "guardSymbol")));
                    }
                }
                if (writers.size() < 2 || target == null) {
                    unsupported.add("IncompleteAlternativeWriterGroup:"
                            + groupId + ":" + writers.size());
                    continue;
                }
                emitVersionedReadChoice(groupId, writers, target);
            }
        }

        private boolean allTrustedReadFromEvidence(JsonArray bindings) {
            if (bindings == null || bindings.size() == 0) return false;
            for (JsonElement element : bindings) {
                if (!element.isJsonObject()
                        || !AutomaticRegionEdge.trustedReadFromEvidence(
                        element.getAsJsonObject())) {
                    return false;
                }
            }
            return true;
        }

        private String assertGuardedPortEquality(PortOccurrence left,
                                                 PortOccurrence right,
                                                 String guard,
                                                 String label) {
            if (!preparePortEquality(left, right)) return "";
            return assertNamed(label, "(=> " + guard + " (= "
                    + portName(left) + " " + portName(right) + "))");
        }

        /**
         * Models a bounded channel history independently of the observed
         * runtime schedule. The trace proves that each writer belongs to this
         * channel; solver positions choose which selected VM writer is the
         * latest writer preceding the read. An initial version is not implicit:
         * if one is relevant to a future closure, it must be supplied by an
         * explicit producer summary like every other writer.
         */
        private void emitVersionedReadChoice(String channelId,
                                             List<VersionedWriter> writers,
                                             PortOccurrence target) {
            if (writers.isEmpty()) return;
            writers = expandBoundedTimelineWriters(writers);
            String timelineChannel = "";
            boolean timeline = false;
            for (VersionedWriter writer : writers) {
                if (writer.timelineChannel.isEmpty()) {
                    if (timeline) {
                        unsupported.add("MixedTimelineAndObservedWriters:"
                                + channelId + ":" + target);
                        return;
                    }
                    continue;
                }
                if (!timelineChannel.isEmpty()
                        && !timelineChannel.equals(writer.timelineChannel)) {
                    unsupported.add("MultipleTimelineChannels:"
                            + channelId + ":" + target);
                    return;
                }
                timeline = true;
                timelineChannel = writer.timelineChannel;
            }
            if (timeline) {
                for (VersionedWriter writer : writers) {
                    if (writer.timelineChannel.isEmpty()) {
                        unsupported.add("MixedTimelineAndObservedWriters:"
                                + channelId + ":" + target);
                        return;
                    }
                }
            }
            String suffix = smtName(channelId + "__" + target);
            String sharedTimelineCut = "";
            if (timeline) {
                int firstCut = Integer.MAX_VALUE;
                int lastCut = Integer.MIN_VALUE;
                for (VersionedWriter writer : writers) {
                    firstCut = Math.min(firstCut, writer.timelineOrdinal);
                    lastCut = Math.max(lastCut, writer.timelineOrdinal);
                }
                sharedTimelineCut = "state_timeline_cut__" + scopeToken(
                        timelineChannel + "\n" + target.invocation);
                declare(sharedTimelineCut, Sort.INT);
                assertNamed("state_timeline_cut_bounds__" + suffix,
                        "(and (<= " + firstCut + " "
                                + sharedTimelineCut + ") (<= "
                                + sharedTimelineCut + " " + lastCut
                                + "))");
            }
            String readPosition = "state_read_position__" + suffix;
            int bound = writers.size() + 1;
            declareBoundedPosition(readPosition, bound);

            List<String> writePositions = new ArrayList<>();
            for (int index = 0; index < writers.size(); index++) {
                VersionedWriter writer = writers.get(index);
                String position = "state_write_position__" + suffix + "_"
                        + index;
                writer.position = position;
                writePositions.add(position);
                declareBoundedPosition(position, bound);
                // The observed writer may precede this reader, but its
                // alpha-renamed future steps are precisely the alternatives
                // the reader cut chooses among.  Requiring every synthetic
                // step to precede the read would force the final cut.
                if (writer.timelineChannel.isEmpty()
                        && bool(writer.binding, "programOrderRequired",
                        false)) {
                    assertNamed("state_program_order__" + suffix + "_"
                                    + index,
                            "(< " + position + " " + readPosition + ")");
                }
            }
            for (int left = 0; left < writers.size(); left++) {
                VersionedWriter first = writers.get(left);
                String firstLane = string(first.binding, "writerLaneId");
                long firstEvent = longInteger(first.binding,
                        "writerEventSeq", -1L);
                for (int right = left + 1; right < writers.size(); right++) {
                    VersionedWriter second = writers.get(right);
                    if (!first.timelineChannel.isEmpty()
                            && first.timelineChannel.equals(
                            second.timelineChannel)
                            && first.timelineOrdinal
                            != second.timelineOrdinal) {
                        String before = first.timelineOrdinal
                                < second.timelineOrdinal
                                ? first.position : second.position;
                        String after = first.timelineOrdinal
                                < second.timelineOrdinal
                                ? second.position : first.position;
                        assertNamed("state_timeline_order__" + suffix
                                        + "_" + left + "_" + right,
                                "(< " + before + " " + after + ")");
                        continue;
                    }
                    if (firstLane.isEmpty() || firstEvent < 0L) continue;
                    long secondEvent = longInteger(second.binding,
                            "writerEventSeq", -1L);
                    if (!firstLane.equals(string(second.binding,
                            "writerLaneId")) || secondEvent < 0L
                            || firstEvent == secondEvent) {
                        continue;
                    }
                    String before = firstEvent < secondEvent
                            ? first.position : second.position;
                    String after = firstEvent < secondEvent
                            ? second.position : first.position;
                    assertNamed("state_writer_program_order__" + suffix
                                    + "_" + left + "_" + right,
                            "(< " + before + " " + after + ")");
                }
            }
            StringBuilder distinct = new StringBuilder("(distinct ")
                    .append(readPosition);
            for (String write : writePositions) {
                distinct.append(' ').append(write);
            }
            distinct.append(')');
            assertNamed("state_event_positions_distinct__" + suffix,
                    distinct.toString());

            List<String> guards = new ArrayList<>();
            Set<String> usedGuards = new LinkedHashSet<>();
            for (int index = 0; index < writers.size(); index++) {
                VersionedWriter writer = writers.get(index);
                String guard = firstNonBlank(writer.requestedGuard,
                        "state_writer_before_reader__" + suffix + "_"
                                + index);
                guard = smtName(guard);
                if (!usedGuards.add(guard)) {
                    guard = guard + "_occurrence_" + index;
                    usedGuards.add(guard);
                }
                declare(guard, Sort.BOOL);
                List<String> latest = new ArrayList<>();
                latest.add("(< " + writer.position + " "
                        + readPosition + ")");
                for (int other = 0; other < writers.size(); other++) {
                    if (other == index) continue;
                    String otherPosition = writers.get(other).position;
                    latest.add("(or (< " + otherPosition + " "
                            + writer.position + ") (< " + readPosition
                            + " " + otherPosition + "))");
                }
                if (!sharedTimelineCut.isEmpty()) {
                    latest.add("(= " + sharedTimelineCut + " "
                            + writer.timelineOrdinal + ")");
                }
                assertNamed("state_writer_guard_definition__" + suffix
                        + "_" + index, "(= " + guard + " "
                        + and(latest) + ")");
                String valueAssertion = assertGuardedPortEquality(
                        writer.source, target, guard,
                        "state_writer_value__" + suffix + "_" + index);
                if (!valueAssertion.isEmpty()) {
                    guards.add(guard);
                    emittedVersionedBindings.add(
                            versionedBindingKey(writer.binding));
                    recordProducerVersionBinding(writer.binding,
                            writer.source, target, valueAssertion);
                    failureWitness.connect(writer, target, guard,
                            portName(target));
                }
            }

            if (guards.isEmpty()) {
                unsupported.add("MissingSelectedVersionedWriter:"
                        + channelId + ":" + target);
                return;
            }

            StringBuilder exactlyOne = new StringBuilder("(= (+");
            for (String guard : guards) {
                exactlyOne.append(" (ite ").append(guard).append(" 1 0)");
            }
            exactlyOne.append(") 1)");
            assertNamed("state_version_choice__" + suffix,
                    exactlyOne.toString());
            mentionedPorts.add(target);
            boundPorts.add(target);
            if (ports.isInput(target.portId)) {
                markSuppliedInput(target);
            }
        }

        private List<VersionedWriter> expandBoundedTimelineWriters(
                List<VersionedWriter> writers) {
            List<VersionedWriter> result = new ArrayList<>();
            for (VersionedWriter writer : writers) {
                TimelineOutputExpansion expansion =
                        boundedTimelineOutputs.get(
                        writer.source);
                if (expansion == null || expansion.cuts.isEmpty()) {
                    result.add(writer);
                    continue;
                }
                for (TimelineCut cut : expansion.cuts) {
                    String guard = writer.requestedGuard.isEmpty() ? ""
                            : writer.requestedGuard + "_bounded_step_"
                            + cut.ordinal;
                    result.add(new VersionedWriter(writer.binding,
                            cut.source, guard, expansion.channel,
                            cut.ordinal));
                }
            }
            return result;
        }

        private void declareBoundedPosition(String position, int bound) {
            declare(position, Sort.INT);
            assertNamed(position + "_bounds", "(and (<= 0 " + position
                    + ") (< " + position + " " + bound + "))");
        }

        private void mergeEdgeBindings(Collection<ResolvedEdge> edges) {
            int edgeIndex = 0;
            Map<PortOccurrence, List<VersionedWriter>> pendingVersioned =
                    new LinkedHashMap<>();
            for (ResolvedEdge edge : edges) {
                JsonObject binding = edge.binding;
                String region = bindingSourceRegion(binding);
                String targetRegion = string(binding, "toRegion");
                String output = bindingSourceOutput(binding);
                String input = bindingTargetInput(binding);
                PortOccurrence outputOccurrence = occurrence(
                        bindingSourceInstance(binding), output);
                PortOccurrence inputOccurrence = occurrence(
                        bindingTargetInstance(binding), input);
                String label = "edge_binding_" + region + "_to_"
                        + targetRegion + "_" + edgeIndex++;
                if (!ports.contains(output) || !ports.contains(input)) {
                    heapGap("EdgeBindingPortGap@" + region
                            + ":" + output + "->" + input);
                    continue;
                }
                boolean valueEquality = "EQUALITY".equals(
                        bindingRelationKind(binding));
                if (valueEquality) {
                    String equalityAssertion = assertPortEqualityNamed(
                            outputOccurrence,
                            inputOccurrence, label);
                    if (!equalityAssertion.isEmpty()) {
                        recordProducerVersionBinding(binding,
                                outputOccurrence, inputOccurrence,
                                equalityAssertion);
                        emitProtocolCausalOrder(binding, label);
                        validateIncomingEdgeInput(inputOccurrence, input);
                        failureWitness.connect(new VersionedWriter(binding,
                                        outputOccurrence, ""),
                                inputOccurrence, "true",
                                portName(inputOccurrence));
                    } else {
                        heapGap("EdgeBindingEqualityGap@" + region
                                + ":" + output + "->" + input);
                    }
                    continue;
                }
                if (emittedVersionedBindings.contains(
                        versionedBindingKey(binding))) {
                    validateIncomingEdgeInput(inputOccurrence, input);
                } else {
                    pendingVersioned.computeIfAbsent(inputOccurrence,
                            ignored -> new ArrayList<>()).add(
                            new VersionedWriter(binding, outputOccurrence,
                                    ""));
                }
            }
            for (Map.Entry<PortOccurrence, List<VersionedWriter>> entry
                    : pendingVersioned.entrySet()) {
                PortOccurrence target = entry.getKey();
                emitVersionedReadChoice("resolved_state_channel__" + target,
                        entry.getValue(), target);
                boolean complete = true;
                for (VersionedWriter writer : entry.getValue()) {
                    if (!emittedVersionedBindings.contains(
                            versionedBindingKey(writer.binding))) {
                        complete = false;
                        break;
                    }
                }
                if (complete) {
                    validateIncomingEdgeInput(target, target.portId);
                } else {
                    heapGap("EdgeBindingEqualityGap@" + target);
                }
            }
        }

        private void validateIncomingEdgeInput(PortOccurrence occurrence,
                                               String input) {
            validatedIncomingEdgeInputs.add(occurrence);
            Sort incomingSort = ports.get(input) == null ? null
                    : sortOfJava(ports.get(input).javaType);
            Sort previous = validatedIncomingEdgeInputSorts.get(occurrence);
            if (incomingSort != null
                    && (previous == null || previous == incomingSort)) {
                validatedIncomingEdgeInputSorts.put(occurrence,
                        incomingSort);
            } else if (incomingSort != null) {
                validatedIncomingEdgeInputSorts.remove(occurrence);
                unsupported.add("IncomingEdgeInputSortConflict:"
                        + input + ":" + previous + "!=" + incomingSort);
            }
        }

        private void emitProtocolCausalOrder(JsonObject binding,
                                             String label) {
            String suffix = smtName(label + "__"
                    + string(binding, "mappingId"));
            String caller = "rpc_caller_position__" + suffix;
            String send = "rpc_send_position__" + suffix;
            String receive = "rpc_receive_position__" + suffix;
            declareBoundedPosition(caller, 3);
            declareBoundedPosition(send, 3);
            declareBoundedPosition(receive, 3);
            assertNamed("rpc_caller_before_send__" + suffix,
                    "(< " + caller + " " + send + ")");
            assertNamed("rpc_send_before_receive__" + suffix,
                    "(< " + send + " " + receive + ")");
        }

        private String versionedBindingKey(JsonObject binding) {
            return string(binding, "edgeId") + "\n"
                    + bindingSourceInstance(binding) + "\n"
                    + bindingSourceOutput(binding) + "\n"
                    + bindingTargetInstance(binding) + "\n"
                    + bindingTargetInput(binding) + "\n"
                    + longInteger(binding, "writerEventSeq", -1L) + "\n"
                    + longInteger(binding, "readerEventSeq", -1L);
        }

        private void recordProducerVersionBinding(
                JsonObject binding, PortOccurrence source,
                PortOccurrence target, String assertionName) {
            String edgeId = string(binding, "edgeId");
            if (edgeId.isEmpty() || assertionName.isEmpty()) return;
            Term producer = producerSolverTerm(source);
            producerVersionBindings.add(new ProducerVersionBinding(
                    edgeId, target, producer.text,
                    producer.sort, assertionName));
        }

        /**
         * Projects a schema-level {@code Value} carrier back to the native
         * solver sort used by an exact fatal operand.  The edge assertion
         * equates the complete carriers, so applying the matching datatype
         * selector preserves that exact producer lineage without comparing
         * unrelated values of the same sort.
         */
        private Term producerSolverTerm(PortOccurrence source) {
            String carrier = portName(source);
            Sort carrierSort = portSort(source);
            Port schema = ports.get(source.portId);
            String javaType = schema == null ? "" : schema.javaType;
            Sort nativeSort = sortOfJava(javaType);
            if (carrierSort != Sort.VALUE || nativeSort == Sort.VALUE) {
                return new Term(carrier, carrierSort);
            }
            if (nativeSort == Sort.INT) {
                String integral = ContainerSmtCodec.unboxIntegral(
                        carrier, javaType);
                if (!integral.isEmpty()) {
                    return new Term(integral, Sort.INT,
                            integralWidthOfJava(javaType));
                }
            }
            if (nativeSort == Sort.BOOL) {
                return new Term("(valueBool " + carrier + ")", Sort.BOOL);
            }
            if (nativeSort == Sort.FLOAT32) {
                return new Term("(valueFloat " + carrier + ")",
                        Sort.FLOAT32);
            }
            if (nativeSort == Sort.FLOAT64) {
                return new Term("(valueDouble " + carrier + ")",
                        Sort.FLOAT64);
            }
            if (nativeSort == Sort.STRING) {
                return new Term("(valueString " + carrier + ")",
                        Sort.STRING);
            }
            if (nativeSort == Sort.REF) {
                return new Term("(valueRef " + carrier + ")", Sort.REF);
            }
            return new Term(carrier, carrierSort);
        }

        private static final class FatalOperand {
            private final String operandId;
            private final int pathOrdinal;
            private final String solverTerm;
            private final Sort solverSort;
            private final String pinTerm;
            private final Sort pinSort;
            private final PortOccurrence occurrence;

            private FatalOperand(String operandId, int pathOrdinal,
                                 String solverTerm, Sort solverSort,
                                 String pinTerm, Sort pinSort,
                                 PortOccurrence occurrence) {
                this.operandId = operandId;
                this.pathOrdinal = pathOrdinal;
                this.solverTerm = solverTerm;
                this.solverSort = solverSort;
                this.pinTerm = pinTerm;
                this.pinSort = pinSort;
                this.occurrence = occurrence;
            }
        }

        private static final class FatalPrefixEquality {
            private final String leftTerm;
            private final Sort leftSort;
            private final PortOccurrence leftOccurrence;
            private final String rightTerm;
            private final Sort rightSort;
            private final PortOccurrence rightOccurrence;

            private FatalPrefixEquality(
                    String leftTerm, Sort leftSort,
                    PortOccurrence leftOccurrence,
                    String rightTerm, Sort rightSort,
                    PortOccurrence rightOccurrence) {
                this.leftTerm = leftTerm;
                this.leftSort = leftSort;
                this.leftOccurrence = leftOccurrence;
                this.rightTerm = rightTerm;
                this.rightSort = rightSort;
                this.rightOccurrence = rightOccurrence;
            }
        }

        private static final class ProducerVersionBinding {
            private final String edgeId;
            private final PortOccurrence target;
            private final String solverTerm;
            private final Sort solverSort;
            private final String assertionName;

            private ProducerVersionBinding(
                    String edgeId, PortOccurrence target,
                    String solverTerm, Sort solverSort,
                    String assertionName) {
                this.edgeId = edgeId;
                this.target = target;
                this.solverTerm = solverTerm;
                this.solverSort = solverSort;
                this.assertionName = assertionName;
            }

            private JsonObject toJson() {
                JsonObject result = new JsonObject();
                result.addProperty("edgeId", edgeId);
                result.addProperty("solverTerm", solverTerm);
                result.addProperty("solverSort", solverSort.smt);
                result.addProperty("assertionName", assertionName);
                result.addProperty("targetPortId", target.portId);
                result.addProperty("targetRegionInstanceId",
                        target.invocation.instanceId);
                return result;
            }
        }

        private static final class VersionedWriter {
            private final JsonObject binding;
            private final PortOccurrence source;
            private final String requestedGuard;
            private final String timelineChannel;
            private final int timelineOrdinal;
            private String position;

            private VersionedWriter(JsonObject binding,
                                    PortOccurrence source,
                                    String requestedGuard) {
                this(binding, source, requestedGuard, "", -1);
            }

            private VersionedWriter(JsonObject binding,
                                    PortOccurrence source,
                                    String requestedGuard,
                                    String timelineChannel,
                                    int timelineOrdinal) {
                this.binding = binding;
                this.source = source;
                this.requestedGuard = requestedGuard;
                this.timelineChannel = timelineChannel;
                this.timelineOrdinal = timelineOrdinal;
            }
        }

        private static final class TimelineCut {
            private final PortOccurrence source;
            private final int ordinal;

            private TimelineCut(PortOccurrence source, int ordinal) {
                this.source = source;
                this.ordinal = ordinal;
            }
        }

        private static final class TimelineOutputExpansion {
            private final String channel;
            private final List<TimelineCut> cuts;

            private TimelineOutputExpansion(String channel,
                                            List<TimelineCut> cuts) {
                this.channel = channel;
                this.cuts = Collections.unmodifiableList(
                        new ArrayList<>(cuts));
            }
        }

        /**
         * Relates two scalar inputs of one selected summary only when (1) an
         * exact runtime edge has already bound the source input, (2) the
         * requested output expression directly consumes the target input,
         * and (3) the summary's static slice contains a directed path made
         * exclusively of equality-preserving transfers between exact input
         * cells.  This closes a common object-field-copy chain without
         * treating arbitrary data dependence as equality.
         */
        private void emitExactCausalInputAliases(
                Iterable<RelationSummary> selections) {
            for (RelationSummary selection : selections) {
                InvocationKey previous = enterInvocation(new InvocationKey(
                        selection.regionId(),
                        selection.regionInstanceId()));
                try {
                    JsonObject summary = selection.toJson();
                    for (String output
                            : selection.outputClosure().outputPorts()) {
                        JsonObject slice = selection.outputClosure()
                                .member(output).slice();
                        if (slice.size() == 0) continue;
                        JsonElement expression =
                                caseInvariantOutputExpression(summary, output);
                        if (expression == null) continue;
                        Set<String> consumedInputs = new LinkedHashSet<>();
                        collectExpressionInputPorts(expression,
                                selection.regionId(), consumedInputs);
                        emitExactCausalInputAliasesForMember(selection, slice,
                                selection.outputClosure().causalEdges(),
                                consumedInputs);
                    }
                } finally {
                    restoreInvocation(previous);
                }
            }
        }

        private void emitExactCausalInputAliasesForMember(
                RelationSummary selection, JsonObject slice,
                List<JsonObject> causalEdges,
                Set<String> consumedInputs) {
            if (consumedInputs.isEmpty()) return;
            JsonObject summary = selection.toJson();
            Map<String, List<String>> exactCells =
                    exactInputCells(slice, selection.regionId());
            Map<String, List<JsonObject>> adjacency =
                    exactCausalAdjacency(slice, causalEdges);
            if (exactCells.isEmpty() || adjacency.isEmpty()) return;

            List<PortOccurrence> sources = new ArrayList<>();
            for (PortOccurrence input : validatedIncomingEdgeInputs) {
                if (selection.regionInstanceId().equals(
                        input.invocation.instanceId)
                        && selection.regionId().equals(regionOf(input.portId))
                        && exactCells.containsKey(input.portId)) {
                    sources.add(input);
                }
            }
            Collections.sort(sources, Comparator.comparing(
                    PortOccurrence::toString));
            List<String> targets = new ArrayList<>(consumedInputs);
            Collections.sort(targets);
            for (PortOccurrence source : sources) {
                Port sourcePort = ports.get(source.portId);
                Sort sourceSort = validatedIncomingEdgeInputSorts.get(source);
                if (sourceSort == null && sourcePort != null) {
                    sourceSort = sortOfJava(sourcePort.javaType);
                }
                if (!exactCausalScalarSort(sourceSort)) continue;
                Set<String> reachable = exactCausalReachable(
                        exactCells.get(source.portId), adjacency);
                for (String target : targets) {
                    PortOccurrence targetOccurrence =
                            currentOccurrence(target);
                    if (source.equals(targetOccurrence)
                            || !exactCells.containsKey(target)) continue;
                    Port targetPort = ports.get(target);
                    if (targetPort == null || sourceSort != sortOfJava(
                            targetPort.javaType)) continue;
                    if (Collections.disjoint(reachable,
                            exactCells.get(target))) continue;
                    String key = firstNonBlank(string(summary,
                            "summaryId"), selection.regionId()) + "\n"
                            + source + "\n" + targetOccurrence;
                    if (!emittedExactCausalInputAliasKeys.add(key)) {
                        continue;
                    }

                    Term from = canonicalPortTerm(source.portId, sourceSort);
                    Term to = canonicalPortTerm(target, sourceSort);
                    String formula = "(= " + from.text + " "
                            + to.text + ")";
                    String label = "exact_causal_input_alias_"
                            + (emittedExactCausalInputAliasKeys.size() - 1);
                    assertNamed(label, formula);
                    recordSuppliedInput(source, targetOccurrence);
                }
            }
        }

        private void collectExpressionInputPorts(JsonElement expression,
                                                 String region,
                                                 Set<String> result) {
            if (expression == null || expression.isJsonNull()) return;
            if (expression.isJsonArray()) {
                for (JsonElement item : expression.getAsJsonArray()) {
                    collectExpressionInputPorts(item, region, result);
                }
                return;
            }
            if (!expression.isJsonObject()) return;
            JsonObject object = expression.getAsJsonObject();
            if ("SymbolExpression".equals(string(object, "_type"))) {
                String port = findPort(string(object, "_exp"));
                if (ports.isInput(port) && region.equals(regionOf(port))) {
                    result.add(port);
                }
                return;
            }
            for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
                if (!"_res_exp".equals(entry.getKey())) {
                    collectExpressionInputPorts(entry.getValue(), region,
                            result);
                }
            }
        }

        private Map<String, List<String>> exactInputCells(JsonObject slice,
                                                          String region) {
            Map<String, List<String>> result = new LinkedHashMap<>();
            for (JsonElement element : array(slice, "inputBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                String input = string(binding, "inputPort");
                String cell = string(binding, "dependencyCell");
                if (!"EXACT_CELL_IDENTITY".equals(string(binding,
                        "bindingAuthority"))
                        || !region.equals(regionOf(input))
                        || !ports.isInput(input) || cell.isEmpty()) {
                    continue;
                }
                List<String> cells = result.get(input);
                if (cells == null) {
                    cells = new ArrayList<>();
                    result.put(input, cells);
                }
                if (!cells.contains(cell)) cells.add(cell);
            }
            for (List<String> cells : result.values()) {
                Collections.sort(cells);
            }
            return result;
        }

        private Map<String, List<JsonObject>> exactCausalAdjacency(
                JsonObject slice, List<JsonObject> causalEdges) {
            Set<String> declared = new LinkedHashSet<>();
            for (JsonElement element : array(slice, "causalEdgeIds")) {
                if (element.isJsonPrimitive()
                        && element.getAsJsonPrimitive().isString()) {
                    declared.add(element.getAsString());
                }
            }
            Map<String, JsonObject> unique = new LinkedHashMap<>();
            Set<String> duplicates = new LinkedHashSet<>();
            for (JsonObject edge : causalEdges) {
                String id = string(edge, "edgeId");
                if (id.isEmpty()
                        || unique.putIfAbsent(id, edge) != null) {
                    duplicates.add(id);
                }
            }
            Map<String, List<JsonObject>> result = new LinkedHashMap<>();
            for (JsonObject edge : unique.values()) {
                String id = string(edge, "edgeId");
                String from = string(edge, "fromCell");
                String to = string(edge, "toCell");
                if (!declared.contains(id) || duplicates.contains(id)
                        || from.isEmpty() || to.isEmpty()
                        || !equalityPreservingCausalTransfer(
                        string(edge, "transferKind"))) {
                    continue;
                }
                List<JsonObject> outgoing = result.get(from);
                if (outgoing == null) {
                    outgoing = new ArrayList<>();
                    result.put(from, outgoing);
                }
                outgoing.add(edge);
            }
            for (List<JsonObject> outgoing : result.values()) {
                Collections.sort(outgoing, Comparator.comparing(
                        value -> string(value, "edgeId")));
            }
            return result;
        }

        private Set<String> exactCausalReachable(
                List<String> sources,
                Map<String, List<JsonObject>> adjacency) {
            Set<String> reachable = new LinkedHashSet<>();
            for (String source : sources) {
                Deque<String> pending = new ArrayDeque<>();
                Map<String, Integer> depths = new LinkedHashMap<>();
                pending.add(source);
                depths.put(source, 0);
                while (!pending.isEmpty()) {
                    String cell = pending.removeFirst();
                    int depth = depths.get(cell);
                    if (depth >= 64) continue;
                    List<JsonObject> outgoing = adjacency.get(cell);
                    if (outgoing == null) continue;
                    for (JsonObject edge : outgoing) {
                        String next = string(edge, "toCell");
                        if (depths.containsKey(next)) continue;
                        depths.put(next, depth + 1);
                        reachable.add(next);
                        pending.addLast(next);
                    }
                }
            }
            return reachable;
        }

        private boolean exactCausalScalarSort(Sort sort) {
            return sort == Sort.INT || sort.floating()
                    || sort == Sort.STRING || sort == Sort.BOOL;
        }

        private boolean equalityPreservingCausalTransfer(String kind) {
            return "VALUE_PASS".equals(kind)
                    || "FUNCTION_RETURN".equals(kind)
                    || "IDENTITY_BINDING".equals(kind)
                    || "HEAP_READ".equals(kind)
                    || "HEAP_WRITE".equals(kind)
                    || "PROTOCOL_TRANSFER".equals(kind);
        }

        private void finishBindings() {
            Map<PortOccurrence, Set<PortOccurrence>> equalPorts =
                    new LinkedHashMap<>();
            for (PortOccurrence[] equality : portEqualities) {
                equalPorts.computeIfAbsent(equality[0],
                        ignored -> new LinkedHashSet<>()).add(equality[1]);
                equalPorts.computeIfAbsent(equality[1],
                        ignored -> new LinkedHashSet<>()).add(equality[0]);
            }
            Deque<PortOccurrence> pending = new ArrayDeque<>(boundPorts);
            while (!pending.isEmpty()) {
                for (PortOccurrence port : equalPorts.getOrDefault(
                        pending.removeFirst(), Collections.emptySet())) {
                    if (boundPorts.add(port)) {
                        pending.addLast(port);
                    }
                }
            }
            for (PortOccurrence port : mentionedPorts) {
                if (!boundPorts.contains(port) && ports.isInput(port.portId)) {
                    unsupported.add("UnboundPort:" + port);
                }
            }
        }

        private boolean assertPortEquality(String left, String right,
                                           String label) {
            return assertPortEquality(currentOccurrence(left),
                    currentOccurrence(right), label);
        }

        private boolean assertPortEquality(PortOccurrence left,
                                           PortOccurrence right,
                                           String label) {
            return !assertPortEqualityNamed(left, right, label).isEmpty();
        }

        private String assertPortEqualityNamed(PortOccurrence left,
                                               PortOccurrence right,
                                               String label) {
            if (!preparePortEquality(left, right)) return "";
            String formula = "(= " + portName(left) + " "
                    + portName(right) + ")";
            String assertionName = assertNamed(label, formula);
            recordSuppliedInput(left, right);
            portEqualities.add(new PortOccurrence[]{left, right});
            return assertionName;
        }

        private boolean preparePortEquality(PortOccurrence left,
                                            PortOccurrence right) {
            if (left.portId.isEmpty() || right.portId.isEmpty()) return false;
            Sort leftSort = portSort(left);
            Sort rightSort = portSort(right);
            if (leftSort != rightSort
                    && refineNeutralPortSort(left, right, leftSort,
                    rightSort)) {
                leftSort = portSort(left);
                rightSort = portSort(right);
            }
            if (leftSort != rightSort) {
                unsupported.add("PortSortMismatch:" + left + ":" + leftSort
                        + "!=" + right + ":" + rightSort);
                return false;
            }
            if (!compatibleArrayPortTypes(left.portId, right.portId,
                    leftSort)) {
                return false;
            }
            declarePort(left, leftSort);
            declarePort(right, rightSort);
            mentionedPorts.add(left);
            mentionedPorts.add(right);
            return true;
        }

        /**
         * Sharpens a port still carrying the neutral {@code Value} sort to
         * the container sort its counterpart already proved.
         *
         * <p>{@link #promotePort} already treats {@code Value} as an
         * unrefined carrier a container-valued binding may sharpen, so a
         * producer whose bound expression is a container reaches an equality
         * with a consumer port nothing has refined yet.  That is the same
         * refinement, applied from the other side of the edge.</p>
         *
         * <p>Both ports must name the same declared Java type before the
         * neutral one is sharpened, and a port already declared to the solver
         * keeps the sort it was declared with.  An unknown or differing
         * declaration decides nothing and keeps the sort-mismatch gap.</p>
         */
        private boolean refineNeutralPortSort(PortOccurrence left,
                                              PortOccurrence right,
                                              Sort leftSort, Sort rightSort) {
            PortOccurrence neutral = leftSort == Sort.VALUE ? left
                    : rightSort == Sort.VALUE ? right : null;
            Sort container = leftSort == Sort.VALUE ? rightSort : leftSort;
            if (neutral == null || container != Sort.MAP
                    && container != Sort.ARRAY_VALUE
                    || declaredPortSorts.containsKey(neutral)) {
                return false;
            }
            String leftType = declaredPortJavaType(left.portId);
            if (leftType.isEmpty()
                    || !leftType.equals(declaredPortJavaType(right.portId))) {
                return false;
            }
            portSortOverrides.put(neutral, container);
            return true;
        }

        private String declaredPortJavaType(String port) {
            Port schema = ports.get(port);
            return schema == null ? "" : schema.declaredJavaType();
        }

        private boolean compatibleArrayPortTypes(String left, String right,
                                                 Sort sort) {
            if (sort != Sort.ARRAY_VALUE) return true;
            String leftType = javaTypeDescriptor(
                    declaredPortJavaType(left));
            String rightType = javaTypeDescriptor(
                    declaredPortJavaType(right));
            if (!leftType.isEmpty() && leftType.equals(rightType)) {
                return true;
            }
            unsupported.add("ArrayPortJavaTypeMismatch:" + left + ":"
                    + firstNonBlank(leftType, "<unknown>") + "!=" + right
                    + ":" + firstNonBlank(rightType, "<unknown>"));
            return false;
        }

        private void recordSuppliedInput(PortOccurrence left,
                                         PortOccurrence right) {
            Port leftPort = ports.get(left.portId);
            Port rightPort = ports.get(right.portId);
            if (leftPort != null && leftPort.input
                    && rightPort != null && !rightPort.input) {
                markSuppliedInput(left);
            }
            if (rightPort != null && rightPort.input
                    && leftPort != null && !leftPort.input) {
                markSuppliedInput(right);
            }
        }

        private void markSuppliedInput(PortOccurrence occurrence) {
            suppliedInputOccurrences.add(occurrence);
            // Schema-v2 compatibility for the reach-condition extractor.
            suppliedInputs.add(occurrence.portId);
        }

        private void recordSuppliedInput(String left, String right) {
            recordSuppliedInput(currentOccurrence(left),
                    currentOccurrence(right));
        }

        private Term asValue(Term term) {
            return asValue(term, "");
        }

        private Term asValue(Term term, String javaType) {
            if (term.sort == Sort.VALUE) return term;
            if (term.sort == Sort.INT) {
                String boxed = ContainerSmtCodec.boxIntegral(
                        term.text, javaType);
                return dependent(new Term(firstNonBlank(boxed,
                        "(VInt " + term.text + ")"), Sort.VALUE), term);
            }
            if (term.sort == Sort.FLOAT32) return dependent(new Term(
                    "(VFloat " + term.text + ")", Sort.VALUE), term);
            if (term.sort == Sort.FLOAT64) return dependent(new Term(
                    "(VDouble " + term.text + ")", Sort.VALUE), term);
            if (term.sort == Sort.BOOL) return dependent(new Term("(VBool "
                    + term.text + ")", Sort.VALUE), term);
            if (term.sort == Sort.STRING) {
                String boxed = "false".equals(term.stringNullness)
                        ? "(VString " + term.text + ")"
                        : "(ite " + term.stringNullness
                                + " (VRef nullRef) (VString "
                                + term.text + "))";
                return dependent(new Term(boxed, Sort.VALUE), term);
            }
            if (term.sort == Sort.REF) return dependent(new Term("(VRef "
                    + term.text + ")", Sort.VALUE), term);
            unsupported.add("CannotBox:" + term.sort);
            return unsupportedTerm(Sort.VALUE);
        }

        private void bindPort(String port, Term value) {
            PortOccurrence occurrence = currentOccurrence(port);
            if (currentGuard.isEmpty() && boundPorts.contains(occurrence)) {
                return;
            }
            if (emitPortBinding(port, value)) {
                boundPorts.add(occurrence);
            }
        }

        private boolean emitPortBinding(String port, Term value) {
            PortOccurrence occurrence = currentOccurrence(port);
            Port schema = ports.get(port);
            Sort portSort = schema == null ? Sort.VALUE : portSort(port);
            declarePort(occurrence, portSort);
            mentionedPorts.add(occurrence);
            if (portSort == Sort.MAP) {
                Term state = value.sort == Sort.MAP ? value
                        : value.sort == Sort.REF
                        ? new Term("(assoc_state_of " + value.text + ")",
                        Sort.MAP)
                        : null;
                if (state == null) {
                    unsupported.add("MapPortBinding:" + port + ":" + value.sort);
                    return false;
                }
                String formula = and(Arrays.asList(state.precondition,
                        "(= " + portName(occurrence) + " " + state.text
                                + ")"));
                assertNamed("bind_" + port, formula);
                return true;
            } else if (portSort == Sort.ARRAY_VALUE) {
                Term state = value.sort == Sort.ARRAY_VALUE ? value
                        : value.sort == Sort.REF
                        ? new Term("(indexed_state_of " + value.text + ")",
                        Sort.ARRAY_VALUE)
                        : null;
                if (state == null) {
                    unsupported.add("ArrayValuePortBinding:" + port + ":"
                            + value.sort);
                    return false;
                }
                String formula = and(Arrays.asList(state.precondition,
                        "(= " + portName(occurrence) + " " + state.text
                                + ")"));
                assertNamed("bind_" + port, formula);
                return true;
            } else {
                if (value.sort == Sort.ARRAY_VALUE) {
                    unsupported.add("UnsupportedArrayToScalarBinding:" + port
                            + ":" + value.sort);
                    return false;
                }
                Term boxed = asValue(value,
                        schema == null ? "" : schema.javaType);
                String formula = and(Arrays.asList(boxed.precondition,
                        "(= " + portName(occurrence) + " " + boxed.text
                                + ")"));
                assertNamed("bind_" + port, formula);
                return true;
            }
        }

        private void declarePort(String port, Sort requested) {
            declarePort(currentOccurrence(port), requested);
        }

        private void declarePort(PortOccurrence occurrence, Sort requested) {
            String port = occurrence.portId;
            Sort canonical = portSort(occurrence);
            Sort sort = requested == null ? canonical : requested;
            if (ports.contains(port) && sort != canonical) {
                unsupported.add("PortDeclarationSortConflict:" + port + ":"
                        + canonical + "->" + sort);
                sort = canonical;
            }
            Sort declared = declaredPortSorts.get(occurrence);
            if (declared != null && declared != sort) {
                unsupported.add("PortRedeclarationSortConflict:" + port
                        + ":" + declared + "->" + sort);
                return;
            }
            declaredPortSorts.put(occurrence, sort);
            addDeclaration("port:" + occurrence,
                    "(declare-const " + portName(occurrence) + " "
                            + sort.smt + ")");
        }

        private Sort portSort(String port) {
            return portSort(currentOccurrence(port));
        }

        private Sort portSort(PortOccurrence occurrence) {
            Sort declared = declaredPortSorts.get(occurrence);
            if (declared != null) return declared;
            Sort override = portSortOverrides.get(occurrence);
            return override == null ? ports.sort(occurrence.portId) : override;
        }

        private void promotePort(String port, Sort sort) {
            PortOccurrence occurrence = currentOccurrence(port);
            Sort current = portSort(port);
            boolean referenceToContainer = current == Sort.REF
                    && (sort == Sort.MAP || sort == Sort.ARRAY_VALUE);
            if (current != sort && current != Sort.VALUE
                    && !referenceToContainer) {
                unsupported.add("PortSortPromotionConflict:" + port + ":"
                        + current + "->" + sort);
                return;
            }
            portSortOverrides.put(occurrence, sort);
        }

        private String portName(String port) {
            return portName(currentOccurrence(port));
        }

        private String portName(PortOccurrence occurrence) {
            return "port__" + smtName(occurrence.portId)
                    + "__instance__"
                    + smtName(occurrence.invocation.instanceId);
        }

        private void declare(String name, Sort sort) {
            addDeclaration("const:" + name,
                    "(declare-const " + name + " " + sort.smt + ")");
        }

        private void declareFunction(String name, List<Term> arguments,
                                     Sort result) {
            StringBuilder declaration = new StringBuilder("(declare-fun ")
                    .append(name).append(" (");
            for (int index = 0; index < arguments.size(); index++) {
                if (index > 0) declaration.append(' ');
                declaration.append(arguments.get(index).sort.smt);
            }
            declaration.append(") ").append(result.smt).append(')');
            addDeclaration("fun:" + name + ":" + declaration,
                    declaration.toString());
        }

        private void addDeclaration(String key, String declaration) {
            if (declarationKeys.add(key)) declarations.add(declaration);
        }

        private String assertNamed(String name, String expression) {
            String unique = smtName(name);
            if (!assertionNames.add(unique)) {
                int suffix = 2;
                while (!assertionNames.add(unique + "_" + suffix)) {
                    suffix++;
                }
                unique = unique + "_" + suffix;
            }
            String asserted = currentGuard.isEmpty() ? expression
                    : "(=> " + currentGuard + " " + expression + ")";
            assertions.add("(assert (! " + asserted + " :named "
                    + unique + "))");
            return unique;
        }

        private boolean isNull(Term term) {
            return term.sort == Sort.REF && "nullRef".equals(term.text);
        }

        private String unknownConstraint(String origin, JsonElement expression) {
            String key = "UnsupportedConstraint:" + origin + ":"
                    + (expression == null ? "null" : GSON.toJson(expression));
            unsupported.add(key);
            return "false";
        }

        private String scopedName(String prefix, String raw) {
            return prefix + "__" + scopeToken(currentSymbolScope) + "__"
                    + smtName(raw);
        }

        /**
         * Unsupported expressions never gain solver freedom.  Their gap is
         * recorded by the caller, this closed value only keeps the diagnostic
         * SMT well-sorted, and {@link #finish()} makes every gapped query
         * non-executable.
         */
        private Term unsupportedTerm(Sort sort) {
            if (sort == Sort.BOOL) return new Term("false", sort);
            if (sort == Sort.INT) return new Term("0", sort);
            if (sort == Sort.FLOAT32 || sort == Sort.FLOAT64) {
                return new Term(JavaPrimitiveSmtSemantics.floatingLiteral(
                        "0.0", floatingKind(sort)), sort);
            }
            if (sort == Sort.STRING) {
                return Term.nonNullString("\"\"", "true");
            }
            if (sort == Sort.REF) return new Term("nullRef", sort);
            String nullValues = "((as const (Array Value Value))"
                    + " (VRef nullRef))";
            if (sort == Sort.MAP) {
                return new Term("(mkAssocState 0"
                        + " ((as const (Array Value Bool)) false)"
                        + " " + nullValues
                        + " ((as const (Array Int Value))"
                        + " (VRef nullRef))"
                        + " ((as const (Array Value Int)) (- 1)))", sort);
            }
            if (sort == Sort.VALUE) {
                return new Term("(VRef nullRef)", sort);
            }
            String elements = "((as const (Array Int Value))"
                    + " (VRef nullRef))";
            return new Term("(mkIndexedState 0 " + elements + ")", sort);
        }

        /** A readable prefix plus a reversible UTF-8 encoding avoids scope
         * collisions introduced by SMT identifier sanitization. */
        private String scopeToken(String scope) {
            String value = firstNonBlank(scope, "global");
            StringBuilder encoded = new StringBuilder();
            for (byte current : value.getBytes(StandardCharsets.UTF_8)) {
                encoded.append(String.format(Locale.ROOT, "%02x",
                        current & 0xff));
            }
            return smtName(value) + "__" + encoded;
        }

        private String findPort(String rawSymbol) {
            for (String port : ports.longestFirst) {
                int index = rawSymbol.indexOf(port);
                while (index >= 0) {
                    int end = index + port.length();
                    // Runtime field symbols wrap the exact activation token as
                    // ..._<port>_<owner>.  Do not accept arbitrary substrings
                    // such as REGION.X.in.2 inside REGION.X.in.25 or a derived
                    // field name such as REGION.X.in.2.selectedField.
                    boolean leftBoundary = index == 0
                            || rawSymbol.charAt(index - 1) == '_';
                    boolean rightBoundary = end == rawSymbol.length()
                            || rawSymbol.charAt(end) == '_';
                    if (leftBoundary && rightBoundary) return port;
                    index = rawSymbol.indexOf(port, index + 1);
                }
            }
            return "";
        }

        private void finish() {
            if (!unsupported.isEmpty()) {
                assertions.add("(assert false) ; fail closed: unsupported");
            }
            assertions.add("(check-sat)");
        }

        private void finishFatalAbsenceMutationWitness() {
            if (failureWitness.demands.isEmpty()) return;
            if (failureWitness.clauses.isEmpty()) {
                unsupported.add("FatalAbsenceMutationWitnessGap");
                return;
            }
            fatalDependentAssertionNames.add(assertNamed(
                    "fatal_absence_mutation_witness",
                    or(failureWitness.clauses)));
        }

        private String render() {
            StringBuilder result = new StringBuilder();
            appendLines(result, preamble);
            result.append(System.lineSeparator());
            appendLines(result, declarations);
            result.append(System.lineSeparator());
            appendLines(result, assertions);
            return result.toString();
        }

        private static void appendLines(StringBuilder builder,
                                        List<String> lines) {
            for (String line : lines) builder.append(line)
                    .append(System.lineSeparator());
        }
    }

    static String materializedPortJavaType(JsonObject port) {
        return MaterializationSpec.logicalJavaType(port);
    }

    private static final class PortIndex {
        private final Map<String, Port> ports = new LinkedHashMap<>();
        private final List<String> longestFirst = new ArrayList<>();

        private static PortIndex from(List<JsonObject> regions) {
            PortIndex result = new PortIndex();
            for (JsonObject region : regions) {
                for (JsonElement element : array(region, "symbolicInputs")) {
                    if (element.isJsonObject()) result.add(
                            element.getAsJsonObject(), true);
                }
                for (JsonElement element : array(region, "outputs")) {
                    if (element.isJsonObject()) result.add(
                            element.getAsJsonObject(), false);
                }
            }
            result.longestFirst.addAll(result.ports.keySet());
            Collections.sort(result.longestFirst,
                    new Comparator<String>() {
                        @Override
                        public int compare(String left, String right) {
                            return Integer.compare(right.length(), left.length());
                        }
                    });
            return result;
        }

        private void add(JsonObject json, boolean input) {
            String id = string(json, "portId");
            if (id.isEmpty()) return;
            String cell = string(json, "cell");
            String javaType = materializedPortJavaType(json);
            Sort sort = containerSort(javaType);
            if (sort == Sort.VALUE) {
                sort = containerCellSort(cell);
            }
            ports.put(id, new Port(javaType,
                    firstNonBlank(declaredFieldJavaType(json),
                            declaredCellJavaType(cell)), sort, input,
                    cell, json));
        }

        /**
         * The declared Java type of the field a port's access path ends at.
         *
         * <p>Runtime activation ports record the field path they walked but
         * not always a materialized type, so the last declaration on that
         * path is the type Java itself gives the value.</p>
         */
        private static String declaredFieldJavaType(JsonObject json) {
            JsonArray declarations = array(json, "fieldPathDeclarations");
            if (declarations.size() == 0) return "";
            JsonElement last = declarations.get(declarations.size() - 1);
            return last.isJsonPrimitive()
                    ? fieldSignatureJavaType(last.getAsString()) : "";
        }

        private Port get(String id) {
            return ports.get(id);
        }

        private boolean contains(String id) {
            return ports.containsKey(id);
        }

        private Sort sort(String id) {
            Port port = ports.get(id);
            return port == null ? Sort.VALUE : port.sort;
        }

        private boolean isInput(String id) {
            Port port = ports.get(id);
            return port != null && port.input;
        }

        private boolean sameStateCell(String input, String output) {
            Port left = ports.get(input);
            Port right = ports.get(output);
            return left != null && right != null && left.input && !right.input
                    && !left.cell.isEmpty() && left.cell.equals(right.cell)
                    && left.sort == right.sort;
        }

        private boolean explicitReplayInvariant(String id) {
            Port port = ports.get(id);
            return port != null && port.explicitReplayInvariant();
        }

    }

    private static final class Port {
        private final String javaType;
        private final String declaredFieldJavaType;
        private final Sort sort;
        private final boolean input;
        private final String cell;
        private final JsonObject metadata;

        private Port(String javaType, String declaredFieldJavaType,
                     Sort sort, boolean input, String cell,
                     JsonObject metadata) {
            this.javaType = javaType;
            this.declaredFieldJavaType = declaredFieldJavaType;
            this.sort = sort;
            this.input = input;
            this.cell = firstNonBlank(cell);
            this.metadata = metadata == null
                    ? new JsonObject() : metadata.deepCopy();
        }

        /** The type Java declares for this port's value, when it is known. */
        private String declaredJavaType() {
            return firstNonBlank(javaType, declaredFieldJavaType);
        }

        private boolean explicitReplayInvariant() {
            String role = string(metadata, "dependencyRole");
            String demand = string(metadata, "symbolicDemand");
            return "CONCRETE_STRUCTURE_CARRIER".equals(role)
                    || bool(metadata, "captureRootOnly", false)
                    || bool(metadata, "loopControlOnly", false)
                    || bool(metadata, "controlOnly", false)
                    || bool(metadata, "pathAssumptionOnly", false)
                    || demand.startsWith("CONCRETE_");
        }

    }

    private static final class RawSymbol {
        private final String name;
        private final Sort sort;
        private String nullness = "";

        private RawSymbol(String name, Sort sort) {
            this.name = name;
            this.sort = sort;
        }
    }

    private enum Sort {
        BOOL("Bool"), INT("Int"),
        FLOAT32("(_ FloatingPoint 8 24)"),
        FLOAT64("(_ FloatingPoint 11 53)"), STRING("String"),
        REF("Ref"), MAP("AssocState"), VALUE("Value"),
        ARRAY_VALUE("IndexedState");

        private final String smt;

        Sort(String smt) {
            this.smt = smt;
        }

        private boolean floating() {
            return this == FLOAT32 || this == FLOAT64;
        }
    }

    private static final class Term {
        private final String text;
        private final Sort sort;
        private final IntegralWidth integralWidth;
        /** Empty only for non-String terms.  "false" means a known non-null
         * String; any other value is the nullable reference companion Bool. */
        private final String stringNullness;
        /** Stable provenance used only for Java reference identity. */
        private final String stringReferenceOrigin;
        /** Java evaluation definedness (notably String dereference guards). */
        private final String precondition;

        private Term(String text, Sort sort) {
            this(text, sort, IntegralWidth.NONE);
        }

        private Term(String text, Sort sort,
                     IntegralWidth integralWidth) {
            this(text, sort, integralWidth,
                    sort == Sort.STRING ? "false" : "", "", "true");
        }

        private Term(String text, Sort sort,
                     IntegralWidth integralWidth,
                     String stringNullness,
                     String stringReferenceOrigin,
                     String precondition) {
            this.text = text;
            this.sort = sort;
            this.integralWidth = sort == Sort.INT && integralWidth != null
                    ? integralWidth : IntegralWidth.NONE;
            this.stringNullness = sort == Sort.STRING
                    ? firstNonBlank(stringNullness, "false") : "";
            this.stringReferenceOrigin = sort == Sort.STRING
                    ? firstNonBlank(stringReferenceOrigin) : "";
            this.precondition = firstNonBlank(precondition, "true");
        }

        private static Term nullableString(String text, String nullness,
                                           String referenceOrigin) {
            return new Term(text, Sort.STRING, IntegralWidth.NONE,
                    nullness, referenceOrigin, "true");
        }

        private static Term nonNullString(String text,
                                          String precondition) {
            return new Term(text, Sort.STRING, IntegralWidth.NONE,
                    "false", "", precondition);
        }

        private Term withPrecondition(String value) {
            return new Term(text, sort, integralWidth, stringNullness,
                    stringReferenceOrigin, value);
        }

        private boolean isZero() {
            return "0".equals(text) || "(- 0)".equals(text);
        }
    }

    /** One statically decided piece of a split element. */
    private static final class SplitPiece {
        private final String text;
        private final JsonElement integerSource;
        /**
         * The invocation whose relation states {@link #integerSource}.  A
         * producer expression names the producer's ports, so lowering it in
         * the reader's invocation would mint a second, unconstrained
         * occurrence of them instead of the witness the producer binds.
         */
        private final InvocationKey integerInvocation;

        private SplitPiece(String text, JsonElement integerSource,
                           InvocationKey integerInvocation) {
            this.text = text;
            this.integerSource = integerSource;
            this.integerInvocation = integerInvocation;
        }

        private static SplitPiece text(String text) {
            return new SplitPiece(text, null, null);
        }

        private static SplitPiece integer(JsonElement source,
                                          InvocationKey invocation) {
            return new SplitPiece("", source, invocation);
        }
    }

    /** One split element decided statically, or the reason it was not. */
    private static final class SplitSegment {
        private final List<SplitPiece> pieces;
        private final String gap;

        private SplitSegment(List<SplitPiece> pieces, String gap) {
            this.pieces = pieces;
            this.gap = firstNonBlank(gap);
        }

        private static SplitSegment of(List<SplitPiece> pieces) {
            return new SplitSegment(
                    Collections.unmodifiableList(
                            new ArrayList<>(pieces)), "");
        }

        private static SplitSegment gap(String gap) {
            return new SplitSegment(null, gap);
        }

        /** An element between two adjacent delimiters is decided and empty. */
        private boolean complete() {
            return pieces != null && gap.isEmpty();
        }

        /** The int this element renders when it renders nothing else. */
        private SplitPiece singleIntegerPiece() {
            return pieces != null && pieces.size() == 1
                    && pieces.get(0).integerSource != null
                    ? pieces.get(0) : null;
        }
    }

    /** An expression together with the invocation whose relation states it. */
    private static final class ScopedExpression {
        private final JsonElement expression;
        private final InvocationKey invocation;

        private ScopedExpression(JsonElement expression,
                                 InvocationKey invocation) {
            this.expression = expression;
            this.invocation = invocation;
        }
    }

    private static final class EqualityBoundExpression {
        private final String inputPort;
        private final String outputPort;
        private final String sourceInstance;
        private final String targetInstance;
        private final JsonElement expression;

        private EqualityBoundExpression(String inputPort, String outputPort,
                                        String sourceInstance,
                                        String targetInstance,
                                        JsonElement expression) {
            this.inputPort = firstNonBlank(inputPort);
            this.outputPort = firstNonBlank(outputPort);
            this.sourceInstance = firstNonBlank(sourceInstance);
            this.targetInstance = firstNonBlank(targetInstance);
            this.expression = expression.deepCopy();
        }

        private boolean sameProofAndExpression(
                EqualityBoundExpression other) {
            return other != null
                    && inputPort.equals(other.inputPort)
                    && outputPort.equals(other.outputPort)
                    && sourceInstance.equals(other.sourceInstance)
                    && targetInstance.equals(other.targetInstance)
                    && expression.equals(other.expression);
        }
    }

    public static final class Result {
        public final String smtLib;
        public final JsonObject manifest;

        private Result(String smtLib, JsonObject manifest) {
            this.smtLib = smtLib;
            this.manifest = manifest;
        }
    }

    public static final class Arguments {
        private Path fatalQueries;
        private final List<Path> summaries = new ArrayList<>();
        private Path output;
        private Path manifest;
        private Path runtimePlan;
        private String fatalRegion = "";
        private String regionInstanceId = "";
        private String compositionMode = "CLOSED_PATH_SET";

        public static Arguments parse(String[] argv) {
            Arguments result = new Arguments();
            for (int index = 0; index < argv.length; index++) {
                String argument = argv[index];
                if (!argument.startsWith("--") || index + 1 >= argv.length
                        || argv[index + 1].startsWith("--")) {
                    throw new IllegalArgumentException(
                            "Expected --option value at " + argument);
                }
                String value = argv[++index];
                String key = argument.substring(2);
                if ("fatal-query".equals(key)) {
                    result.fatalQueries = Paths.get(value);
                } else if ("summaries".equals(key)) {
                    result.summaries.add(Paths.get(value));
                } else if ("output".equals(key)) {
                    result.output = Paths.get(value);
                } else if ("manifest".equals(key)) {
                    result.manifest = Paths.get(value);
                } else if ("runtime-plan".equals(key)) {
                    result.runtimePlan = Paths.get(value);
                } else if ("fatal-region".equals(key)) {
                    result.fatalRegion = firstNonBlank(value);
                } else if ("region-instance-id".equals(key)) {
                    result.regionInstanceId = firstNonBlank(value);
                } else if ("composition-mode".equals(key)) {
                    result.compositionMode = firstNonBlank(value);
                } else {
                    throw new IllegalArgumentException(
                            "Unknown composer option: --" + key);
                }
            }
            if (result.fatalQueries == null || result.runtimePlan == null
                    || result.output == null) {
                throw new IllegalArgumentException(
                        "--fatal-query, --runtime-plan and --output are required");
            }
            if (result.manifest == null) {
                result.manifest = sibling(result.output,
                        "composed_smt_manifest.json");
            }
            if (!"CLOSED_PATH_SET".equals(result.compositionMode)
                    && !"EXISTENTIAL_OBSERVED_PATHS".equals(
                    result.compositionMode)) {
                throw new IllegalArgumentException(
                        "unsupported --composition-mode: "
                                + result.compositionMode);
            }
            return result;
        }
    }

    private static Sort sortOfJava(String type) {
        if (type == null) return Sort.VALUE;
        String normalized = type.replace('.', '/');
        Sort container = containerSort(normalized);
        if (container != Sort.VALUE) return container;
        String className = normalized.startsWith("L")
                && normalized.endsWith(";") && normalized.length() > 2
                ? normalized.substring(1, normalized.length() - 1)
                : normalized;
        if ("Z".equals(type) || "boolean".equals(type)) return Sort.BOOL;
        if ("B".equals(type) || "C".equals(type)
                || "S".equals(type) || "I".equals(type)
                || "J".equals(type)
                || "byte".equals(type) || "char".equals(type)
                || "short".equals(type) || "int".equals(type)
                || "long".equals(type)) return Sort.INT;
        if ("F".equals(type) || "float".equals(type)) return Sort.FLOAT32;
        if ("D".equals(type) || "double".equals(type)) return Sort.FLOAT64;
        if ("java/lang/Boolean".equals(className)) return Sort.BOOL;
        if ("java/lang/Byte".equals(className)
                || "java/lang/Character".equals(className)
                || "java/lang/Short".equals(className)
                || "java/lang/Integer".equals(className)
                || "java/lang/Long".equals(className)) return Sort.INT;
        if ("java/lang/Float".equals(className)) return Sort.FLOAT32;
        if ("java/lang/Double".equals(className)) return Sort.FLOAT64;
        if ("String".equals(className)
                || "java/lang/String".equals(className)) return Sort.STRING;
        if (type.isEmpty()) return Sort.VALUE;
        return Sort.REF;
    }

    private static Sort containerCellSort(String cell) {
        return containerSort(declaredCellJavaType(cell));
    }

    private static final Pattern CELL_PARAMETER = Pattern.compile(
            ">\\.param[0-9]+:([^#]+)(?:#.*)?$");
    private static final Pattern CELL_RETURN = Pattern.compile(
            "^<[^:]+:\\s+([^<>\\s]+)\\s+[^<>\\s(]+\\([^>]*\\)>"
                    + "\\.return(?:#.*)?$");

    /**
     * The Java type a port's cell declares, or an empty string.
     *
     * <p>A cell naming a parameter, a field, or a return value carries the
     * declaration Java itself made.  A cell naming a local carries none.</p>
     */
    private static String declaredCellJavaType(String cell) {
        String value = firstNonBlank(cell).trim();
        Matcher parameter = CELL_PARAMETER.matcher(value);
        if (parameter.find()) return parameter.group(1).trim();
        String field = fieldSignatureJavaType(value);
        if (!field.isEmpty()) return field;
        Matcher returned = CELL_RETURN.matcher(value);
        return returned.matches() ? returned.group(1) : "";
    }

    private static final Pattern FIELD_SIGNATURE = Pattern.compile(
            "^<[^:]+:\\s+([^()<>\\s]+)\\s+[^()<>\\s]+>(?:#.*)?$");

    /** The declared type in a Soot field signature, or an empty string. */
    private static String fieldSignatureJavaType(String signature) {
        Matcher field = FIELD_SIGNATURE.matcher(
                firstNonBlank(signature).trim());
        return field.matches() ? field.group(1) : "";
    }

    private static Sort containerSort(String type) {
        JavaContainerTypes.Shape shape = JavaContainerTypes.shape(type);
        return shape == JavaContainerTypes.Shape.ASSOCIATIVE
                ? Sort.MAP
                : shape == JavaContainerTypes.Shape.INDEXED
                ? Sort.ARRAY_VALUE : Sort.VALUE;
    }

    private static boolean isJavaParseInt(String name) {
        return "java/lang/Integer parseInt".equals(firstNonBlank(name));
    }

    private static boolean isJavaSplitElement(String name) {
        return "java/lang/String splitElement".equals(firstNonBlank(name));
    }

    private static String comparison(String operator) {
        if ("<".equals(operator) || ">".equals(operator)
                || "<=".equals(operator) || ">=".equals(operator)) {
            return operator;
        }
        return "";
    }

    private static String arithmetic(String operator) {
        if ("+".equals(operator) || "-".equals(operator)
                || "*".equals(operator)) return operator;
        return "";
    }

    private static boolean arithmeticOperator(String operator) {
        return "+".equals(operator) || "-".equals(operator)
                || "*".equals(operator) || "@".equals(operator)
                || "/".equals(operator) || "%".equals(operator);
    }

    private static boolean numeric(Sort sort) {
        return sort == Sort.INT || sort.floating();
    }

    private static IntegralWidth integralWidthOfJava(String javaType) {
        return JavaPrimitiveSmtSemantics.widthOfJavaType(javaType);
    }

    static String canonicalIntegralJavaType(String schemaJavaType,
                                            String expressionJavaType) {
        return integralWidthOfJava(schemaJavaType) == IntegralWidth.NONE
                ? expressionJavaType : schemaJavaType;
    }

    private static FloatingKind floatingKind(Sort sort) {
        if (sort == Sort.FLOAT32) return FloatingKind.JAVA_FLOAT;
        if (sort == Sort.FLOAT64) return FloatingKind.JAVA_DOUBLE;
        return FloatingKind.NONE;
    }

    /** Java binary numeric promotion for the two integral JVM widths. */
    private static IntegralWidth promotedIntegralWidth(Term left,
                                                        Term right) {
        if (left.sort != Sort.INT || right.sort != Sort.INT) {
            return IntegralWidth.NONE;
        }
        return JavaPrimitiveSmtSemantics.promote(left.integralWidth,
                right.integralWidth);
    }

    private static String wrapIntegral(String expression,
                                       IntegralWidth width) {
        return JavaPrimitiveSmtSemantics.wrap(expression, width);
    }

    private static Sort castSort(String descriptor) {
        if ("Z".equals(descriptor) || "B".equals(descriptor)
                || "C".equals(descriptor) || "S".equals(descriptor)
                || "I".equals(descriptor) || "J".equals(descriptor)) {
            return Sort.INT;
        }
        if ("F".equals(descriptor)) return Sort.FLOAT32;
        if ("D".equals(descriptor)) return Sort.FLOAT64;
        if (descriptor.startsWith("L") || descriptor.startsWith("[")) {
            return Sort.REF;
        }
        return Sort.VALUE;
    }

    private static String castDescriptor(String javaType) {
        return JavaPrimitiveSmtSemantics.primitiveDescriptor(javaType);
    }

    /** The VM uses bare L for primitive long conversions, while other IR
     * nodes also use it as a legacy reference tag.  The primitive source
     * disambiguates conversion bytecodes without mistyping a reference cast. */
    private static String castTargetDescriptor(String javaType,
                                               String sourceType) {
        return JavaPrimitiveSmtSemantics.primitiveTargetDescriptor(
                javaType, sourceType);
    }

    private static String expressionJavaType(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return "";
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        if ("TypeCastExpression".equals(type)) {
            return string(object, "_java_type");
        }
        if ("MethodExpression".equals(type)) {
            return string(object(object, "_res_exp"), "_java_type");
        }
        return string(object, "_java_type");
    }

    private static String constantPayload(String raw) {
        if (raw == null) return "0";
        int first = raw.indexOf('_');
        int second = first < 0 ? -1 : raw.indexOf('_', first + 1);
        return second < 0 ? raw : raw.substring(second + 1);
    }

    private static String integerLiteral(String value) {
        String raw = firstNonBlank(value).trim();
        if (raw.isEmpty() || raw.length() > 1024) return null;
        try {
            BigInteger parsed = new BigInteger(raw);
            return parsed.signum() < 0
                    ? "(- " + parsed.negate().toString() + ")"
                    : parsed.toString();
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    private static String quote(String value) {
        String exact = value == null ? "" : value;
        return "\"" + exact.replace("\"", "\"\"") + "\"";
    }

    private static String smtName(String value) {
        String normalized = firstNonBlank(value, "anonymous")
                .replaceAll("[^A-Za-z0-9_]", "_");
        if (normalized.isEmpty()) normalized = "anonymous";
        if (Character.isDigit(normalized.charAt(0))) normalized = "n_" + normalized;
        return normalized;
    }

    private static void require(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException(label + " not found: " + path);
        }
    }

}
