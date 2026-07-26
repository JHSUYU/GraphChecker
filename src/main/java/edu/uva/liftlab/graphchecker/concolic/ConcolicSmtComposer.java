package edu.uva.liftlab.graphchecker.concolic;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.artifact;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sibling;

import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;

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
        require(arguments.regions, "symbolic regions");

        List<JsonObject> queryRows = ArtifactIO.readJsonl(
                arguments.fatalQueries);
        List<RelationSummary> summaries = new ArrayList<>();
        for (Path summaryFile : arguments.summaries) {
            int row = 0;
            for (JsonObject encoded : ArtifactIO.readJsonl(summaryFile)) {
                try {
                    RelationSummary summary =
                            RelationSummary.decode(encoded);
                    if (summary.regionId().isEmpty()
                            || summary.summaryId().isEmpty()) {
                        throw new IllegalArgumentException(
                                "summary identity is required");
                    }
                    summaries.add(summary);
                } catch (IllegalArgumentException malformed) {
                    throw new IOException("Malformed relation summary "
                            + summaryFile + " row " + row, malformed);
                }
                row++;
            }
        }
        List<JsonObject> regions = ArtifactIO.readJsonl(arguments.regions);
        JsonObject fatal = selectFatalQuery(queryRows, arguments);
        if (fatal.size() == 0) {
            throw new IOException("No ready fatal query matches region="
                    + arguments.fatalRegion + " instance="
                    + arguments.regionInstanceId);
        }
        requireCanonicalFatalQuerySchema(fatal);
        boolean targetPathSet = "TARGET_REACH_PATH_SET_QUERY".equals(
                string(fatal, "kind"));
        BranchReplayContract fatalReplayContract = targetPathSet
                ? replayContract(fatal, "seedReplayContract")
                : replayContract(fatal, "replayContract");
        SolverPathContext fatalSolverPathContext = targetPathSet
                ? null : solverPathContext(fatal);
        JsonArray fatalConstraints = targetPathSet ? new JsonArray()
                : fatalConstraints(fatalReplayContract,
                fatalSolverPathContext);
        BranchWitness fatalSource = fatalReplayContract.source();
        String fatalSite = fatalSource.siteId();

        // This composer consumes a seed query.  A solver-ready branch replay
        // contract is sufficient to build the candidate SMT, but it is not an
        // observation that the complete workload naturally reached the target.
        // Natural target replay promotion remains the explicit next-stage TODO.
        PortIndex ports = PortIndex.from(regions);
        JsonObject rawContext = object(fatal, "symbolicContext");
        JsonObject resolutionContext = boundedContext(rawContext,
                arguments.boundedUpstreamRegions);
        boolean instanceScopedContext = resolutionContext.size() > 0
                && !string(resolutionContext, "regionInstanceId").isEmpty();

        ResolvedSummaryGraph resolved = resolveSummaryGraph(fatal,
                resolutionContext,
                summaries, arguments.boundedUpstreamRegions);
        Set<String> relevantRegions = resolved.relevantRegions;
        // Static projection can expose several aliases for one runtime
        // writer/read event.  Resolution deliberately admits only aliases
        // backed by an exact producer summary.  Re-scope the context to that
        // resolved graph before emission: one surviving alternative becomes
        // an ordinary versioned merge, while an entirely concrete alias
        // group disappears without creating symbolic ports.
        JsonObject context = boundedContext(resolutionContext,
                relevantRegions);
        Emitter emitter = new Emitter(ports);
        emitter.begin(fatal);
        emitter.registerExactEqualityBoundExpressions(
                resolved.selectedEdges.values());
        if (!instanceScopedContext) {
            emitter.unsupported.add(
                    "MissingTargetInstanceSymbolicContext");
        }
        emitter.unsupported.addAll(resolved.gaps);

        List<String> fatalTerms = new ArrayList<>();
        String previousFatalScope = emitter.enterSymbolScope("fatal:"
                + firstNonBlank(string(fatal, "regionInstanceId"),
                string(fatal, "queryId"), fatalSite,
                string(fatal, "regionId"), "selected"));
        try {
            emitter.registerVmIntrinsicPlaceholderBindings(fatal,
                    "fatal query");
            if (targetPathSet) {
                int pathOrdinal = 0;
                for (JsonElement element : array(fatal, "paths")) {
                    JsonObject path = element.getAsJsonObject();
                    String label = "fatal target path " + pathOrdinal++;
                    emitter.registerVmIntrinsicPlaceholderBindings(path,
                            label);
                    List<String> pathTerms = new ArrayList<>();
                    for (JsonElement constraint
                            : array(path, "constraints")) {
                        pathTerms.add(emitter.constraint(constraint, label));
                    }
                    fatalTerms.add(and(pathTerms));
                }
            } else {
                for (JsonElement constraint : fatalConstraints) {
                    fatalTerms.add(emitter.constraint(constraint,
                            "fatal query"));
                }
            }
        } finally {
            emitter.restoreSymbolScope(previousFatalScope);
        }
        emitter.assertNamed("fatal_path", targetPathSet
                ? or(fatalTerms) : and(fatalTerms));

        for (RelationSummary selection
                : resolved.selectedRegionSummaries.values()) {
            emitter.regionSummary(selection);
        }

        emitter.merge(context, relevantRegions);
        emitter.mergeEdgeBindings(resolved.selectedEdges.values(),
                relevantRegions);
        emitter.emitExactCausalInputAliases(
                resolved.selectedRegionSummaries.values());
        emitter.finishBindings();
        emitter.finish();
        String composedSmt = emitter.render();

        JsonArray summaryInputArtifacts = new JsonArray();
        for (Path input : arguments.summaries) {
            summaryInputArtifacts.add(artifact(input));
        }
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 2);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        manifest.addProperty("fatalSite", fatalSite);
        manifest.addProperty("fatalConstraintAuthority", targetPathSet
                ? "CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1"
                : "IMMUTABLE_BRANCH_REPLAY_CONTRACT_V1");
        manifest.add("resolvedEdgeBindings",
                GSON.toJsonTree(resolved.selectedEdges.keySet()));
        manifest.add("suppliedInputs",
                GSON.toJsonTree(emitter.suppliedInputs));
        JsonArray gaps = new JsonArray();
        appendGaps(gaps, "COMPOSITION_GAP", emitter.unsupported);
        manifest.add("gaps", gaps);
        manifest.addProperty("state", gaps.size() == 0
                ? "CANDIDATE_READY" : "CANDIDATE_WITH_GAPS");
        manifest.addProperty("trustState", "CANDIDATE_ONLY");
        manifest.add("composedSmtArtifact", artifact(arguments.output,
                composedSmt.getBytes(StandardCharsets.UTF_8)));
        manifest.add("staticRegionsArtifact", artifact(arguments.regions));
        manifest.add("fatalQueriesArtifact",
                artifact(arguments.fatalQueries));
        manifest.add("summaryInputArtifacts", summaryInputArtifacts);
        return new Result(composedSmt, manifest);
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
                || !"TARGET_BRANCH_SOLVER_QUERY".equals(kind)
                && !"TARGET_REACH_PATH_SET_QUERY".equals(kind)) {
            throw new IOException("Unsupported canonical fatal query schema");
        }
        if ("TARGET_REACH_PATH_SET_QUERY".equals(kind)) {
            if (!"CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1".equals(
                    string(fatal, "constraintAuthority"))) {
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
    }

    private static BranchReplayContract replayContract(
            JsonObject fatal, String field) throws IOException {
        JsonElement encoded = fatal.get(field);
        if (encoded == null || !encoded.isJsonObject()) {
            throw new IOException("Canonical fatal query requires " + field);
        }
        try {
            return BranchReplayContract.fromJson(encoded.getAsJsonObject());
        } catch (IllegalArgumentException malformed) {
            throw new IOException("Malformed " + field + ": "
                    + malformed.getMessage(), malformed);
        }
    }

    private static SolverPathContext solverPathContext(JsonObject fatal)
            throws IOException {
        JsonElement encoded = fatal.get("solverPathContext");
        if (encoded == null || !encoded.isJsonObject()) {
            throw new IOException(
                    "Canonical fatal query requires solverPathContext");
        }
        try {
            return SolverPathContext.fromJson(encoded.getAsJsonObject());
        } catch (IllegalArgumentException malformed) {
            throw new IOException("Malformed fatal solverPathContext: "
                    + malformed.getMessage(), malformed);
        }
    }

    private static JsonArray fatalConstraints(
            BranchReplayContract replayContract,
            SolverPathContext solverPathContext) {
        JsonArray result = solverPathContext.expressions();
        for (JsonElement predicate
                : replayContract.requiredPathPredicates()) {
            result.add(predicate);
        }
        return result;
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
                    string(row, "kind"))
                    || bool(row, "readyForSolver", false)) {
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
            List<RelationSummary> summaries,
            Set<String> sourceScopeRegions) {
        SummaryIndex summaryIndex = SummaryIndex.build(summaries);
        ProducerDemandIndex knownDemands = new ProducerDemandIndex();
        List<JsonObject> equalities = relationRows(context,
                "equalityRelations");
        List<JsonObject> readFrom = relationRows(context,
                "versionedStateMerges");
        List<JsonObject> alternatives = alternativeRelations(context);
        while (true) {
            ResolvedSummaryGraph result = resolveSummaryGraphPass(
                    fatal, context, summaryIndex,
                    sourceScopeRegions, knownDemands, equalities, readFrom,
                    alternatives);
            if (!knownDemands.addAll(result.demands)) return result;
        }
    }

    private static ResolvedSummaryGraph resolveSummaryGraphPass(
            JsonObject fatal, JsonObject context, SummaryIndex summaries,
            Set<String> sourceScopeRegions,
            ProducerDemandIndex knownDemands,
            List<JsonObject> equalities, List<JsonObject> readFrom,
            List<JsonObject> alternatives) {
        String fatalRegion = string(fatal, "regionId");
        String fatalInstance = string(context, "regionInstanceId");
        ResolvedSummaryGraph result = new ResolvedSummaryGraph(fatalRegion,
                fatalInstance, sourceScopeRegions, knownDemands);

        registerContextDemands(result, sourceScopeRegions,
                equalities, readFrom, alternatives);
        seedContextRelations(result, summaries, sourceScopeRegions,
                equalities, "EQUALITY", true);
        seedContextRelations(result, summaries, sourceScopeRegions,
                readFrom, "READ_FROM", true);
        seedContextRelations(result, summaries, sourceScopeRegions,
                alternatives, "READ_FROM", false);

        while (!result.pending.isEmpty()) {
            ProducerKey consumer = result.pending.removeFirst();
            RelationSummary consumerSelection =
                    result.selectedRegionSummaries.get(consumer.regionId);
            if (consumerSelection == null
                    || !consumer.instanceId.equals(
                    consumerSelection.regionInstanceId())) {
                continue;
            }
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
                        .trustedRuntimeCompositionBinding(binding)
                        || !allowedBoundedSource(
                        bindingSourceRegion(binding),
                        sourceScopeRegions)) {
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

        result.finishBounds();
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
            ResolvedSummaryGraph graph, Set<String> boundedRegions,
            List<JsonObject>... groups) {
        for (List<JsonObject> relations : groups) {
            for (JsonObject relation : relations) {
                registerContextDemand(graph, relation, boundedRegions);
            }
        }
    }

    private static void registerContextDemand(ResolvedSummaryGraph graph,
                                              JsonObject relation,
                                              Set<String> boundedRegions) {
        String output = string(relation, "fromEndpoint");
        String sourceRegion = regionOf(output);
        if (!graph.fatalRegion.equals(regionOf(string(relation,
                "toEndpoint"))) || sourceRegion.isEmpty()
                || !allowedBoundedSource(sourceRegion, boundedRegions)) return;
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
            Set<String> boundedRegions, List<JsonObject> relations,
            String expectedKind, boolean missingProducerIsGap) {
        for (JsonObject relation : relations) {
            seedContextRelation(graph, relation, summaries, boundedRegions,
                    expectedKind, missingProducerIsGap);
        }
    }

    private static void seedContextRelation(ResolvedSummaryGraph graph,
                                            JsonObject relation,
                                            SummaryIndex summaries,
                                            Set<String> boundedRegions,
                                            String expectedRelationKind,
                                            boolean missingProducerIsGap) {
        String output = string(relation, "fromEndpoint");
        String input = string(relation, "toEndpoint");
        String sourceRegion = regionOf(output);
        if (!graph.fatalRegion.equals(regionOf(input))
                || sourceRegion.isEmpty()
                || !allowedBoundedSource(sourceRegion, boundedRegions)) {
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
                key.regionId);
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
        RelationSummary regionSelection =
                graph.selectedRegionSummaries.get(region);
        boolean newlySelected = regionSelection == null;
        if (regionSelection != null && !requestedInstance.isEmpty()
                && !requestedInstance.equals(
                regionSelection.regionInstanceId())) {
            graph.gaps.add("ConflictingProducerRegionInstance:"
                    + producerLabel(region, requestedInstance,
                    demandedOutputs)
                    + ":selected="
                    + regionSelection.regionInstanceId());
            return null;
        }
        if (regionSelection != null
                && !regionSelection.outputClosure().outputPorts().equals(
                demandedOutputs)) {
            // The outer resolver reruns from a clean graph with the monotonic
            // demand index.  Never keep using the earlier singleton selection
            // during the pass in which a later consumer discovers a new port.
            graph.gaps.add("ProducerDemandExpandedAfterSelection:"
                    + producerLabel(region, requestedInstance,
                    demandedOutputs) + ":selected="
                    + regionSelection.outputClosure().outputPorts());
            return null;
        }
        Map<String, RelationSummary> unique = new LinkedHashMap<>();
        Set<String> fingerprints = new LinkedHashSet<>();
        for (RelationSummary summary : summaries.forClosure(region,
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
        if (regionSelection != null && !regionSelection.same(selected)) {
            graph.gaps.add("ConflictingProducerSummarySelection:" + key);
            return null;
        }
        if (newlySelected) {
            graph.selectedRegionSummaries.put(region, selected);
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
        String fingerprint = string(expected, "valueFingerprint");
        if (!fromInstance.isEmpty()
                && !fromInstance.equals(bindingSourceInstance(binding))
                || !toInstance.isEmpty()
                && !toInstance.equals(bindingTargetInstance(binding))
                || !fingerprint.isEmpty()
                && !fingerprint.equals(string(binding, "valueFingerprint"))) {
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
        if (AutomaticRegionEdge.COMPLETE_VALUE_EQUALITY.equals(kind)) {
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

    private static boolean allowedBoundedSource(String region,
                                                Set<String> boundedRegions) {
        return boundedRegions.isEmpty() || boundedRegions.contains(region);
    }

    private static final class SummaryIndex {
        private final Map<String, List<RelationSummary>> byClosure =
                new LinkedHashMap<>();
        private final Map<String, List<JsonObject>> bindingsByTarget =
                new LinkedHashMap<>();

        private static SummaryIndex build(List<RelationSummary> summaries) {
            SummaryIndex result = new SummaryIndex();
            for (RelationSummary decoded : summaries) {
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

        private List<RelationSummary> forClosure(String region,
                                                 Set<String> outputs) {
            return byClosure.getOrDefault(closureKey(region, outputs),
                    Collections.emptyList());
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

    private static final class ResolvedEdge {
        private final RelationSummary summary;
        private final JsonObject binding;

        private ResolvedEdge(RelationSummary summary, JsonObject binding) {
            this.summary = summary;
            this.binding = binding;
        }

    }

    private static final class ResolvedSummaryGraph {
        private final String fatalRegion;
        private final String fatalInstance;
        private final Set<String> boundedRegions;
        private final ProducerDemandIndex demands;
        private final Map<String, RelationSummary>
                selectedRegionSummaries = new LinkedHashMap<>();
        private final Map<String, ResolvedEdge> selectedEdges =
                new LinkedHashMap<>();
        private final Deque<ProducerKey> pending = new ArrayDeque<>();
        private final Set<String> relevantRegions = new LinkedHashSet<>();
        private final Set<String> gaps = new LinkedHashSet<>();

        private ResolvedSummaryGraph(String fatalRegion,
                                     String fatalInstance,
                                     Set<String> sourceScopeRegions,
                                     ProducerDemandIndex knownDemands) {
            this.fatalRegion = firstNonBlank(fatalRegion);
            this.fatalInstance = firstNonBlank(fatalInstance);
            this.boundedRegions = new LinkedHashSet<>(sourceScopeRegions);
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
            if (!edgeId.isEmpty()) selectedEdges.putIfAbsent(edgeId, edge);
        }

        private void addDirectBindingIfPresent(ProducerKey source,
                                               String targetRegion,
                                               String targetInstance,
                                               String targetInput,
                                               JsonObject expectedRelation,
                                               JsonObject expectedBinding,
                                               String expectedRelationKind) {
            RelationSummary summary = selectedRegionSummaries.get(
                    source.regionId);
            if (summary == null
                    || !source.instanceId.equals(
                    summary.regionInstanceId())
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

        private void finishBounds() {
            for (String region : boundedRegions) {
                if (!relevantRegions.contains(region)) {
                    gaps.add("UnreachableBoundedRegion:" + region);
                }
            }
        }

    }

    private static JsonObject boundedContext(JsonObject source,
                                             Set<String> boundedRegions) {
        JsonObject result = source.deepCopy();
        if (boundedRegions.isEmpty()) {
            return result;
        }
        for (String field : new String[]{"equalityRelations",
                "versionedStateMerges"}) {
            JsonArray selected = new JsonArray();
            for (JsonElement element : array(source, field)) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject relation = element.getAsJsonObject();
                if (boundedRegions.contains(regionOf(string(relation,
                        "fromEndpoint")))) {
                    selected.add(relation.deepCopy());
                }
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
                if (boundedRegions.contains(regionOf(string(relation,
                        "fromEndpoint")))) {
                    selected.add(relation.deepCopy());
                }
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

    private static String regionOf(String endpoint) {
        if (endpoint == null) return "";
        int marker = endpoint.indexOf(".in.");
        if (marker < 0) marker = endpoint.indexOf(".out.");
        if (marker > 0) return endpoint.substring(0, marker);
        marker = endpoint.indexOf("::");
        return marker > 0 ? endpoint.substring(0, marker) : "";
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

    private static final class Emitter {
        private final PortIndex ports;
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
        private final Map<String, Sort> portSortOverrides =
                new LinkedHashMap<>();
        private final Map<String, Sort> declaredPortSorts =
                new LinkedHashMap<>();
        private final Set<String> boundPorts = new LinkedHashSet<>();
        private final Set<String> mentionedPorts = new LinkedHashSet<>();
        private final Set<String> unsupported = new LinkedHashSet<>();
        private final Set<String> canonicalPortTermBindings =
                new LinkedHashSet<>();
        private final Set<String> javaIntRangeAssertions =
                new LinkedHashSet<>();
        private final Set<String> javaIntegralRangeAssertions =
                new LinkedHashSet<>();
        private final Map<String, EqualityBoundExpression>
                exactEqualityBoundExpressions = new LinkedHashMap<>();
        private final Set<String> ambiguousEqualityBoundExpressionPorts =
                new LinkedHashSet<>();
        private final Set<String> validatedIncomingEdgeInputs =
                new LinkedHashSet<>();
        private final Map<String, Sort> validatedIncomingEdgeInputSorts =
                new LinkedHashMap<>();
        private final Set<String> emittedExactCausalInputAliasKeys =
                new LinkedHashSet<>();
        private final Map<String, Map<String, String>>
                vmIntrinsicPlaceholderBindingsByScope =
                new LinkedHashMap<>();
        private final List<String[]> portEqualities = new ArrayList<>();
        private final Set<String> suppliedInputs = new LinkedHashSet<>();
        private String currentGuard = "";
        private String currentSymbolScope = "global";

        private Emitter(PortIndex ports) {
            this.ports = ports;
        }

        private String enterSymbolScope(String scope) {
            String previous = currentSymbolScope;
            currentSymbolScope = firstNonBlank(scope, "global");
            return previous;
        }

        private void restoreSymbolScope(String scope) {
            currentSymbolScope = firstNonBlank(scope, "global");
        }

        private void begin(JsonObject fatal) {
            preamble.add("; GraphChecker composed concolic query");
            preamble.add("; fatal region: " + string(fatal, "regionId"));
            preamble.add("(set-logic ALL)");
            preamble.add("(declare-sort Ref 0)");
            preamble.add("(declare-datatypes () ((Value"
                    + " (VInt (valueInt Int))"
                    + " (VFloat (valueFloat (_ FloatingPoint 8 24)))"
                    + " (VDouble (valueDouble (_ FloatingPoint 11 53)))"
                    + " (VBool (valueBool Bool))"
                    + " (VRef (valueRef Ref))"
                    + " (VString (valueString String)))))");
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

        /**
         * Catalogs a producer's exact String output expression for a
         * consumer input only when the selected instance edge carries the
         * same complete runtime value-equality proof that will later be
         * asserted by {@link #mergeEdgeBindings(Collection, Set)}. This is an
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
                        || !ports.contains(output) || !ports.contains(input)
                        || sortOfJava(ports.get(output).javaType)
                        != Sort.STRING
                        || sortOfJava(ports.get(input).javaType)
                        != Sort.STRING) {
                    continue;
                }
                JsonElement value = object(edge.summary.toJson(),
                        "outputExpressions").get(output);
                if (value == null || !value.isJsonObject()
                        || !provablyStringValued(value)) {
                    continue;
                }
                EqualityBoundExpression candidate =
                        new EqualityBoundExpression(input, output,
                                bindingSourceInstance(binding),
                                bindingTargetInstance(binding), value);
                EqualityBoundExpression previous =
                        exactEqualityBoundExpressions.get(input);
                if (previous == null
                        && !ambiguousEqualityBoundExpressionPorts.contains(
                        input)) {
                    exactEqualityBoundExpressions.put(input, candidate);
                } else if (previous != null
                        && !previous.sameProofAndExpression(candidate)) {
                    exactEqualityBoundExpressions.remove(input);
                    ambiguousEqualityBoundExpressionPorts.add(input);
                    unsupported.add(
                            "AmbiguousExactEqualityBoundExpression:" + input);
                }
            }
        }

        private String constraint(JsonElement expression, String origin) {
            if (expression == null || !expression.isJsonObject()) {
                return unknownConstraint(origin, expression);
            }
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if ("MethodExpression".equals(type)) {
                return methodConstraint(object, origin);
            }
            Term term = term(expression, null);
            if (term.sort == Sort.BOOL) return condition(term);
            return unknownConstraint(origin + ": non-boolean " + type,
                    expression);
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

        private Term term(JsonElement expression, Sort expected) {
            if (expression == null || expression.isJsonNull()
                    || !expression.isJsonObject()) {
                return new Term("nullRef", Sort.REF);
            }
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if ("SymbolExpression".equals(type)) {
                return symbol(object, expected);
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
                String function = firstNonBlank(string(object,
                        "_place_holder_func"), "unknown");
                int count = integer(object, "_count", 0);
                String identity = function + "#" + count;
                Map<String, String> scopeBindings =
                        vmIntrinsicPlaceholderBindingsByScope.get(
                                currentSymbolScope);
                String inputPort = scopeBindings == null ? null
                        : scopeBindings.get(identity);
                if (inputPort != null) {
                    return canonicalPortTerm(inputPort, Sort.INT);
                }
                unsupported.add("PlaceholderExpression:" + function
                        + "#" + count);
                return unsupportedTerm(Sort.INT);
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
            return fromContainerTerm(ContainerSmtCodec.term(
                    expression, containerHost()));
        }

        private Term containerFieldTerm(JsonObject expression) {
            return fromContainerTerm(ContainerSmtCodec.field(
                    expression, containerHost()));
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
                        if (!port.isEmpty() && portSort(port) == required) {
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
                    return toContainerTerm(asValue(term(expression, null)));
                }

                @Override
                public ContainerSmtCodec.Term unbox(
                        ContainerSmtCodec.Term value, String javaType) {
                    if (value == null
                            || value.sort != ContainerSmtCodec.Sort.VALUE) {
                        return value;
                    }
                    Sort sort = sortOfJava(javaType);
                    if (sort == Sort.INT) {
                        return new ContainerSmtCodec.Term(
                                "(valueInt " + value.text + ")",
                                ContainerSmtCodec.Sort.INT,
                                JavaPrimitiveSmtSemantics.widthOfJavaType(
                                        javaType));
                    }
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
                            + owner.text + ")", result));
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
                mentionedPorts.add(port);
                if (expected == Sort.MAP) {
                    promotePort(port, Sort.MAP);
                    declarePort(port, Sort.MAP);
                    boundPorts.add(port);
                    return new Term(portName(port), Sort.MAP);
                }
                if (expected == Sort.ARRAY_VALUE) {
                    if (portSort(port) != Sort.ARRAY_VALUE) {
                        unsupported.add("ArraySymbolPortSortConflict:" + port
                                + ":" + portSort(port));
                    } else {
                        declarePort(port, Sort.ARRAY_VALUE);
                        boundPorts.add(port);
                        return new Term(portName(port), Sort.ARRAY_VALUE);
                    }
                }
                Port schema = ports.get(port);
                if (schema != null && portSort(port) == Sort.MAP) {
                    declarePort(port, Sort.MAP);
                    boundPorts.add(port);
                    return new Term(portName(port), Sort.MAP);
                }
                if (schema != null && portSort(port) == Sort.ARRAY_VALUE) {
                    declarePort(port, Sort.ARRAY_VALUE);
                    boundPorts.add(port);
                    return new Term(portName(port), Sort.ARRAY_VALUE);
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
            String bindingKey = port + "\u0000" + sort.name();
            String name = "sym__port__" + smtName(port) + "__"
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
                String nullness = "sym__port__" + smtName(port)
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
                            "canonical_port_" + smtName(port));
                    if (emitPortBinding(port, term)) {
                        boundPorts.add(port);
                    }
                } finally {
                    currentGuard = previousGuard;
                }
            }
            return term;
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
            String name = "sym__port__" + smtName(port) + "__ref";
            declare(name, Sort.REF);
            String bindingKey = port
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
            if (expected == Sort.BOOL
                    && "Z".equals(javaTypeDescriptor(javaType))) {
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
            Term left = term(expression.get("_left"), null);
            Term right = term(expression.get("_right"), left.sort);
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
            SplitPrefix match = exactSplitPrefix(params.get(0));
            if (!match.complete()) {
                return codecGap("java/lang/Integer.parseInt",
                        "ROUNDTRIP_NOT_PROVED_" + match.gap, Sort.INT);
            }
            Term integer = term(match.integerExpression, Sort.INT);
            if (integer.sort != Sort.INT) {
                return codecGap("java/lang/Integer.parseInt",
                        "ROUNDTRIP_SOURCE_NOT_INT", Sort.INT);
            }
            assertJavaIntRange(integer);
            return integer;
        }

        private Term splitElementTerm(JsonObject expression) {
            SplitPrefix match = exactSplitPrefix(expression);
            if (!match.complete()) {
                return codecGap("java/lang/String.splitElement", match.gap,
                        Sort.STRING);
            }
            Term integer = term(match.integerExpression, Sort.INT);
            if (integer.sort != Sort.INT) {
                return codecGap("java/lang/String.splitElement",
                        "ROUNDTRIP_SOURCE_NOT_INT", Sort.STRING);
            }
            assertJavaIntRange(integer);
            return javaIntString(integer);
        }

        private SplitPrefix exactSplitPrefix(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) {
                return SplitPrefix.gap("NOT_METHOD_EXPRESSION");
            }
            JsonObject split = expression.getAsJsonObject();
            if (!"MethodExpression".equals(string(split, "_type"))
                    || !isJavaSplitElement(string(split, "_name"))) {
                return SplitPrefix.gap("NOT_STRING_SPLIT_ELEMENT");
            }
            JsonArray params = array(split, "_param_list");
            if (params.size() != 3 && params.size() != 4) {
                return SplitPrefix.gap("SPLIT_ARITY");
            }

            Integer index = exactIntLiteral(params.get(params.size() - 1));
            if (index == null || index != 0) {
                return SplitPrefix.gap("INDEX_NOT_LITERAL_0");
            }
            String delimiter = exactStringLiteral(params.get(1));
            String delimiterGap = decimalDelimiterGap(delimiter);
            if (!delimiterGap.isEmpty()) return SplitPrefix.gap(delimiterGap);
            if (params.size() == 4) {
                Integer limit = exactIntLiteral(params.get(2));
                // Java split(..., 1) returns the entire receiver and therefore
                // does not preserve the decimal prefix as element zero.  Zero,
                // negative limits, and positive limits greater than one do.
                if (limit == null || limit == 1) {
                    return SplitPrefix.gap(
                            "LIMIT_DOES_NOT_PRESERVE_PREFIX");
                }
            }

            JsonElement receiver = resolveExactEqualityBoundExpression(
                    params.get(0));
            List<JsonElement> flattened = new ArrayList<>();
            if (!flattenConcat(receiver, flattened)) {
                return SplitPrefix.gap("CONCAT_PREFIX_AND_SUFFIX_REQUIRED");
            }
            // String concatenation commonly starts from the compiler/JDK
            // builder identity "".  Removing only exact empty literals is a
            // semantics-preserving normalization; symbolic or non-empty
            // prefixes remain proof gaps.
            List<JsonElement> parts = new ArrayList<>();
            for (JsonElement part : flattened) {
                if (!"".equals(exactStringLiteral(part))) parts.add(part);
            }
            if (parts.size() < 3) {
                return SplitPrefix.gap("CONCAT_PREFIX_AND_SUFFIX_REQUIRED");
            }
            JsonElement first = parts.get(0);
            if (first == null || !first.isJsonObject()) {
                return SplitPrefix.gap("PREFIX_NOT_INT_TO_STRING");
            }
            JsonObject toString = first.getAsJsonObject();
            JsonArray toStringParams = array(toString, "_param_list");
            if (!"OpStrExpression".equals(string(toString, "_type"))
                    || !"toString".equals(string(toString, "_name"))
                    || bool(toString, "_is_not", false)
                    || toStringParams.size() != 1
                    || !isPrimitiveIntExpression(toStringParams.get(0))) {
                return SplitPrefix.gap("PREFIX_NOT_PRIMITIVE_INT_TO_STRING");
            }
            String concatenatedDelimiter = exactStringLiteral(parts.get(1));
            if (concatenatedDelimiter == null
                    || !delimiter.equals(concatenatedDelimiter)) {
                return SplitPrefix.gap("SPLIT_CONCAT_DELIMITER_MISMATCH");
            }
            for (int indexOfSuffix = 2; indexOfSuffix < parts.size();
                 indexOfSuffix++) {
                if (!provablyStringValued(parts.get(indexOfSuffix))) {
                    return SplitPrefix.gap("SUFFIX_NOT_STRING_VALUED");
                }
            }
            return SplitPrefix.complete(toStringParams.get(0));
        }

        /**
         * Chases only exact, uniquely selected String equality edges.  The
         * returned producer expression is still connected to the consumer
         * port by the ordinary merge assertion; this lookup merely exposes
         * its syntax to a structural codec proof.
         */
        private JsonElement resolveExactEqualityBoundExpression(
                JsonElement expression) {
            JsonElement current = expression;
            Set<String> visited = new LinkedHashSet<>();
            while (current != null && current.isJsonObject()) {
                JsonObject object = current.getAsJsonObject();
                if (!"SymbolExpression".equals(string(object, "_type"))) {
                    break;
                }
                String port = findPort(string(object, "_exp"));
                if (port.isEmpty() || !visited.add(port)
                        || ambiguousEqualityBoundExpressionPorts.contains(
                        port)) {
                    break;
                }
                EqualityBoundExpression binding =
                        exactEqualityBoundExpressions.get(port);
                if (binding == null) break;
                current = binding.expression;
            }
            return current;
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

        private String decimalDelimiterGap(String value) {
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
            if (Character.isDigit(delimiter) || delimiter == '-') {
                return "DELIMITER_OCCURS_IN_JAVA_INT_TEXT";
            }
            return "";
        }

        private String methodConstraint(JsonObject expression, String origin) {
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

        private void registerVmIntrinsicPlaceholderBindings(
                JsonObject container, String origin) {
            JsonArray rows = array(container,
                    "vmIntrinsicPlaceholderBindings");
            if (rows.size() == 0) return;
            Map<String, String> validated = new LinkedHashMap<>();
            Set<String> portsSeen = new LinkedHashSet<>();
            for (int ordinal = 0; ordinal < rows.size(); ordinal++) {
                JsonElement element = rows.get(ordinal);
                if (!element.isJsonObject()) {
                    unsupported.add("MalformedAdmittedVmPlaceholderBinding:"
                            + origin + ":" + ordinal);
                    continue;
                }
                JsonObject row = element.getAsJsonObject();
                String identity = string(row, "placeholderIdentity");
                String port = string(row, "inputPort");
                Port schema = ports.get(port);
                if (identity.isEmpty() || schema == null || !schema.input
                        || schema.sort != Sort.VALUE
                        || validated.containsKey(identity)
                        || !portsSeen.add(port)) {
                    unsupported.add("MalformedAdmittedVmPlaceholderBinding:"
                            + origin + ":" + ordinal);
                    continue;
                }
                validated.put(identity, port);
            }
            String scope = currentSymbolScope;
            if (vmIntrinsicPlaceholderBindingsByScope.containsKey(scope)) {
                unsupported.add("DuplicateVmPlaceholderBindingScope:"
                        + origin + ":" + scope);
                return;
            }
            vmIntrinsicPlaceholderBindingsByScope.put(scope, validated);
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

        private void regionSummary(RelationSummary selected) {
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
                    region, "selected"));
            try {
                registerVmIntrinsicPlaceholderBindings(summary,
                        "summary " + region);
                guardedRegionRelation(region, relation, outputClosure);
            } finally {
                restoreSymbolScope(previousScope);
            }
        }

        private void guardedRegionRelation(String region,
                                           JsonObject relation,
                                           OutputClosureContract outputClosure) {
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
                if (outputClosure.outputPorts().size() > 1
                        && !object(item, "outputExpressions").keySet().equals(
                        outputClosure.outputPorts())) {
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
                String caseIdentity = "region:" + region + "/case:"
                        + firstNonBlank(string(item, "caseId"),
                        String.valueOf(index));
                String previousScope = enterSymbolScope(caseIdentity);
                try {
                    registerVmIntrinsicPlaceholderBindings(item,
                            "region " + region + " case " + index);
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
                    bindOutputExpressions(region, item);
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

        private void bindOutputExpressions(String region,
                                           JsonObject summary) {
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
                bindPort(port, term(entry.getValue(), portSort(port)));
            }
        }

        private void heapGap(String detail) {
            unsupported.add(detail);
        }

        private void merge(JsonObject context,
                           Set<String> relevantRegions) {
            for (JsonElement element : array(context, "equalityClasses")) {
                if (!element.isJsonObject()) continue;
                JsonArray members = array(element.getAsJsonObject(), "members");
                List<String> selected = new ArrayList<>();
                for (JsonElement member : members) {
                    if (!member.isJsonPrimitive()) continue;
                    String endpoint = member.getAsString();
                    if (relevantRegions.contains(regionOf(endpoint))) {
                        selected.add(endpoint);
                    }
                }
                if (selected.size() < 2) continue;
                String first = selected.get(0);
                for (int index = 1; index < selected.size(); index++) {
                    assertPortEquality(first, selected.get(index), "alias");
                }
            }
            for (JsonElement element : array(context,
                    "versionedStateMerges")) {
                if (!element.isJsonObject()) continue;
                JsonObject relation = element.getAsJsonObject();
                String from = string(relation, "fromEndpoint");
                String to = string(relation, "toEndpoint");
                if (!relevantRegions.contains(regionOf(from))
                        || !relevantRegions.contains(regionOf(to))) {
                    continue;
                }
                JsonArray bindings = selectedBindings(relation);
                if (!allTrustedReadFromEvidence(bindings)) {
                    unsupported.add("UntrustedVersionedStateReadFrom:"
                            + string(relation, "edgeId"));
                    continue;
                }
                assertPortEquality(from, to, "read_from");
                for (int index = 0; index < bindings.size(); index++) {
                    JsonObject binding = bindings.get(index).getAsJsonObject();
                    String suffix = smtName(firstNonBlank(string(relation,
                            "edgeId"), "edge")) + "_" + index;
                    emitEventOrder("event_write_" + suffix,
                            "event_read_" + suffix, "order", "",
                            integer(binding, "writerEventSeq", 0),
                            integer(binding, "readerEventSeq", 0));
                }
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
                List<String> guards = new ArrayList<>();
                int emitted = 0;
                for (int index = 0; index < alternatives.size(); index++) {
                    if (!alternatives.get(index).isJsonObject()) continue;
                    JsonObject relation = alternatives.get(index)
                            .getAsJsonObject();
                    String from = string(relation, "fromEndpoint");
                    String to = string(relation, "toEndpoint");
                    if (!relevantRegions.contains(regionOf(from))
                            || !relevantRegions.contains(regionOf(to))) {
                        continue;
                    }
                    if (!allTrustedReadFromEvidence(
                            selectedBindings(relation))) {
                        unsupported.add("UntrustedAlternativeWriterReadFrom:"
                                + groupId + ":" + index);
                        continue;
                    }
                    String guard = firstNonBlank(string(relation,
                            "guardSymbol"), "writer_guard__"
                            + smtName(groupId + "_" + index));
                    guard = smtName(guard);
                    declare(guard, Sort.BOOL);
                    if (!assertGuardedPortEquality(from, to, guard,
                            "guarded_read_from_" + groupId + "_" + index)) {
                        continue;
                    }
                    guards.add(guard);
                    emitted++;
                    guardedRuntimeEvidence(relation, groupId, index, guard);
                }
                if (emitted < 2) {
                    unsupported.add("IncompleteAlternativeWriterGroup:"
                            + groupId + ":" + emitted);
                    continue;
                }
                StringBuilder exactlyOne = new StringBuilder("(= (+");
                for (String guard : guards) {
                    exactlyOne.append(" (ite ").append(guard)
                            .append(" 1 0)");
                }
                exactlyOne.append(") 1)");
                assertNamed("writer_choice_" + groupId,
                        exactlyOne.toString());
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

        private boolean assertGuardedPortEquality(String left, String right,
                                                  String guard,
                                                  String label) {
            if (!preparePortEquality(left, right)) return false;
            assertNamed(label, "(=> " + guard + " (= " + portName(left)
                    + " " + portName(right) + "))");
            portEqualities.add(new String[]{left, right});
            return true;
        }

        private void guardedRuntimeEvidence(JsonObject relation,
                                            String groupId, int alternative,
                                            String guard) {
            JsonArray bindings = selectedBindings(relation);
            if (bindings.size() == 0) {
                unsupported.add("MissingAlternativeWriterEvidence:"
                        + groupId + ":" + alternative);
                return;
            }
            for (int index = 0; index < bindings.size(); index++) {
                JsonObject binding = bindings.get(index).getAsJsonObject();
                String suffix = smtName(groupId) + "_" + alternative + "_"
                        + index;
                String write = "event_write_alt_" + suffix;
                String read = "event_read_alt_" + suffix;
                emitEventOrder(write, read, "order_alt_" + suffix, guard,
                        integer(binding, "writerEventSeq", 0),
                        integer(binding, "readerEventSeq", 0));
                int receiver = integer(binding, "receiverObjectId", 0);
                emitReceiverIdentity("receiver_write_alt_" + suffix,
                        "receiver_read_alt_" + suffix,
                        "identity_alt_" + suffix, guard, receiver);
            }
        }

        private void mergeEdgeBindings(
                Collection<ResolvedEdge> edges,
                Set<String> relevantRegions) {
            int edgeIndex = 0;
            for (ResolvedEdge edge : edges) {
                JsonObject binding = edge.binding;
                String region = bindingSourceRegion(binding);
                String targetRegion = string(binding, "toRegion");
                if (!relevantRegions.contains(region)
                        || !relevantRegions.contains(targetRegion)) {
                    continue;
                }
                String output = bindingSourceOutput(binding);
                String input = bindingTargetInput(binding);
                String label = "edge_binding_" + region + "_to_"
                        + targetRegion + "_" + edgeIndex++;
                if (!ports.contains(output) || !ports.contains(input)) {
                    heapGap("EdgeBindingPortGap@" + region
                            + ":" + output + "->" + input);
                    continue;
                }
                boolean valueEquality = "EQUALITY".equals(
                        bindingRelationKind(binding));
                long writeSeq = longInteger(binding, "writerEventSeq", -1);
                long readSeq = longInteger(binding, "readerEventSeq", -1);
                boolean equalityEmitted =
                        assertPortEquality(output, input, label);
                if (!equalityEmitted) {
                    heapGap("EdgeBindingEqualityGap@" + region
                            + ":" + output + "->" + input);
                    continue;
                }
                validatedIncomingEdgeInputs.add(input);
                Sort incomingSort = ports.get(input) == null ? null
                        : sortOfJava(ports.get(input).javaType);
                Sort previousIncomingSort =
                        validatedIncomingEdgeInputSorts.get(input);
                if (incomingSort != null
                        && (previousIncomingSort == null
                        || previousIncomingSort == incomingSort)) {
                    validatedIncomingEdgeInputSorts.put(input, incomingSort);
                } else if (incomingSort != null) {
                    validatedIncomingEdgeInputSorts.remove(input);
                    unsupported.add("IncomingEdgeInputSortConflict:"
                            + input + ":" + previousIncomingSort + "!="
                            + incomingSort);
                }
                emitEventOrder("event_write_" + smtName(label),
                        "event_read_" + smtName(label), "order_" + label, "",
                        writeSeq, readSeq);

                // A complete serialized value is sufficient for a transport
                // equality. The receiver-side object is normally a new
                // allocation, so object identity would be a false constraint.
                if (valueEquality) {
                    continue;
                }
                emitReceiverIdentity("receiver_write_" + smtName(label),
                        "receiver_read_" + smtName(label),
                        "identity_" + label, "",
                        integer(binding, "receiverObjectId", 0));
            }
        }

        private void emitEventOrder(String write, String read,
                                    String assertion, String guard,
                                    long writerSequence,
                                    long readerSequence) {
            declare(write, Sort.INT);
            declare(read, Sort.INT);
            assertNamed(write + "_seq", "(= " + write + " "
                    + writerSequence + ")");
            assertNamed(read + "_seq", "(= " + read + " "
                    + readerSequence + ")");
            String order = "(< " + write + " " + read + ")";
            assertNamed(assertion, guard.isEmpty() ? order
                    : "(=> " + guard + " " + order + ")");
        }

        private void emitReceiverIdentity(String writer, String reader,
                                          String assertion, String guard,
                                          int receiver) {
            declare(writer, Sort.INT);
            declare(reader, Sort.INT);
            assertNamed(writer + "_id", "(= " + writer + " "
                    + receiver + ")");
            assertNamed(reader + "_id", "(= " + reader + " "
                    + receiver + ")");
            String identity = "(= " + writer + " " + reader + ")";
            assertNamed(assertion, guard.isEmpty() ? identity
                    : "(=> " + guard + " " + identity + ")");
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
                JsonObject summary = selection.toJson();
                JsonObject outputs = object(summary, "outputExpressions");
                for (String output
                        : selection.outputClosure().outputPorts()) {
                    JsonObject slice =
                            selection.outputClosure().member(output).slice();
                    if (slice.size() == 0) continue;
                    JsonElement expression = outputs.get(output);
                    if (expression == null) continue;
                    Set<String> consumedInputs = new LinkedHashSet<>();
                    collectExpressionInputPorts(expression,
                            selection.regionId(), consumedInputs);
                    emitExactCausalInputAliasesForMember(selection, slice,
                            consumedInputs);
                }
            }
        }

        private void emitExactCausalInputAliasesForMember(
                RelationSummary selection, JsonObject slice,
                Set<String> consumedInputs) {
            if (consumedInputs.isEmpty()) return;
            JsonObject summary = selection.toJson();
            Map<String, List<String>> exactCells =
                    exactInputCells(slice, selection.regionId());
            Map<String, List<JsonObject>> adjacency =
                    exactCausalAdjacency(slice);
            if (exactCells.isEmpty() || adjacency.isEmpty()) return;

            List<String> sources = new ArrayList<>();
            for (String input : validatedIncomingEdgeInputs) {
                if (selection.regionId().equals(regionOf(input))
                        && exactCells.containsKey(input)) {
                    sources.add(input);
                }
            }
            Collections.sort(sources);
            List<String> targets = new ArrayList<>(consumedInputs);
            Collections.sort(targets);
            for (String source : sources) {
                Port sourcePort = ports.get(source);
                Sort sourceSort = validatedIncomingEdgeInputSorts.get(source);
                if (sourceSort == null && sourcePort != null) {
                    sourceSort = sortOfJava(sourcePort.javaType);
                }
                if (!exactCausalScalarSort(sourceSort)) continue;
                Set<String> reachable = exactCausalReachable(
                        exactCells.get(source), adjacency);
                for (String target : targets) {
                    if (source.equals(target)
                            || !exactCells.containsKey(target)) continue;
                    Port targetPort = ports.get(target);
                    if (targetPort == null || sourceSort != sortOfJava(
                            targetPort.javaType)) continue;
                    if (Collections.disjoint(reachable,
                            exactCells.get(target))) continue;
                    String key = firstNonBlank(string(summary,
                            "summaryId"), selection.regionId()) + "\n"
                            + source + "\n" + target;
                    if (!emittedExactCausalInputAliasKeys.add(key)) {
                        continue;
                    }

                    Term from = canonicalPortTerm(source, sourceSort);
                    Term to = canonicalPortTerm(target, sourceSort);
                    String formula = "(= " + from.text + " "
                            + to.text + ")";
                    String label = "exact_causal_input_alias_"
                            + (emittedExactCausalInputAliasKeys.size() - 1);
                    assertNamed(label, formula);
                    recordSuppliedInput(source, target);
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
                JsonObject slice) {
            Set<String> declared = new LinkedHashSet<>();
            for (JsonElement element : array(slice, "causalEdgeIds")) {
                if (element.isJsonPrimitive()
                        && element.getAsJsonPrimitive().isString()) {
                    declared.add(element.getAsString());
                }
            }
            Map<String, JsonObject> unique = new LinkedHashMap<>();
            Set<String> duplicates = new LinkedHashSet<>();
            for (JsonElement element : array(slice, "causalEdges")) {
                if (!element.isJsonObject()) continue;
                JsonObject edge = element.getAsJsonObject();
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
                    || "PROJECTION".equals(kind)
                    || "PROTOCOL_TRANSFER".equals(kind);
        }

        private void finishBindings() {
            Map<String, Set<String>> equalPorts = new LinkedHashMap<>();
            for (String[] equality : portEqualities) {
                equalPorts.computeIfAbsent(equality[0],
                        ignored -> new LinkedHashSet<>()).add(equality[1]);
                equalPorts.computeIfAbsent(equality[1],
                        ignored -> new LinkedHashSet<>()).add(equality[0]);
            }
            Deque<String> pending = new ArrayDeque<>(boundPorts);
            while (!pending.isEmpty()) {
                for (String port : equalPorts.getOrDefault(
                        pending.removeFirst(), Collections.emptySet())) {
                    if (boundPorts.add(port)) {
                        pending.addLast(port);
                    }
                }
            }
            for (String port : mentionedPorts) {
                if (!boundPorts.contains(port) && ports.isInput(port)) {
                    unsupported.add("UnboundPort:" + port);
                }
            }
        }

        private boolean assertPortEquality(String left, String right,
                                           String label) {
            if (!preparePortEquality(left, right)) return false;
            String formula = "(= " + portName(left) + " "
                    + portName(right) + ")";
            assertNamed(label, formula);
            recordSuppliedInput(left, right);
            portEqualities.add(new String[]{left, right});
            return true;
        }

        private boolean preparePortEquality(String left, String right) {
            if (left.isEmpty() || right.isEmpty()) return false;
            Sort leftSort = portSort(left);
            Sort rightSort = portSort(right);
            if (leftSort != rightSort) {
                unsupported.add("PortSortMismatch:" + left + ":" + leftSort
                        + "!=" + right + ":" + rightSort);
                return false;
            }
            if (!compatibleArrayPortTypes(left, right, leftSort)) {
                return false;
            }
            declarePort(left, leftSort);
            declarePort(right, rightSort);
            mentionedPorts.add(left);
            mentionedPorts.add(right);
            return true;
        }

        private boolean compatibleArrayPortTypes(String left, String right,
                                                 Sort sort) {
            if (sort != Sort.ARRAY_VALUE) return true;
            Port leftPort = ports.get(left);
            Port rightPort = ports.get(right);
            String leftType = leftPort == null ? ""
                    : javaTypeDescriptor(leftPort.javaType);
            String rightType = rightPort == null ? ""
                    : javaTypeDescriptor(rightPort.javaType);
            if (!leftType.isEmpty() && leftType.equals(rightType)) {
                return true;
            }
            unsupported.add("ArrayPortJavaTypeMismatch:" + left + ":"
                    + firstNonBlank(leftType, "<unknown>") + "!=" + right
                    + ":" + firstNonBlank(rightType, "<unknown>"));
            return false;
        }

        private void recordSuppliedInput(String left, String right) {
            Port leftPort = ports.get(left);
            Port rightPort = ports.get(right);
            if (leftPort != null && leftPort.input
                    && rightPort != null && !rightPort.input) {
                suppliedInputs.add(left);
            }
            if (rightPort != null && rightPort.input
                    && leftPort != null && !leftPort.input) {
                suppliedInputs.add(right);
            }
        }

        private Term asValue(Term term) {
            if (term.sort == Sort.VALUE) return term;
            if (term.sort == Sort.INT) return dependent(new Term("(VInt "
                    + term.text + ")", Sort.VALUE), term);
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
            if (currentGuard.isEmpty() && boundPorts.contains(port)) {
                return;
            }
            if (emitPortBinding(port, value)) {
                boundPorts.add(port);
            }
        }

        private boolean emitPortBinding(String port, Term value) {
            Port schema = ports.get(port);
            Sort portSort = schema == null ? Sort.VALUE : portSort(port);
            declarePort(port, portSort);
            mentionedPorts.add(port);
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
                        "(= " + portName(port) + " " + state.text + ")"));
                assertNamed("bind_" + port, formula);
                return true;
            } else if (portSort == Sort.ARRAY_VALUE) {
                if (value.sort != Sort.ARRAY_VALUE) {
                    unsupported.add("ArrayValuePortBinding:" + port + ":"
                            + value.sort);
                    return false;
                }
                String formula = and(Arrays.asList(value.precondition,
                        "(= " + portName(port) + " " + value.text + ")"));
                assertNamed("bind_" + port, formula);
                return true;
            } else {
                if (value.sort == Sort.ARRAY_VALUE) {
                    unsupported.add("UnsupportedArrayToScalarBinding:" + port
                            + ":" + value.sort);
                    return false;
                }
                Term boxed = asValue(value);
                String formula = and(Arrays.asList(boxed.precondition,
                        "(= " + portName(port) + " " + boxed.text + ")"));
                assertNamed("bind_" + port, formula);
                return true;
            }
        }

        private void declarePort(String port, Sort requested) {
            Sort canonical = portSort(port);
            Sort sort = requested == null ? canonical : requested;
            if (ports.contains(port) && sort != canonical) {
                unsupported.add("PortDeclarationSortConflict:" + port + ":"
                        + canonical + "->" + sort);
                sort = canonical;
            }
            Sort declared = declaredPortSorts.get(port);
            if (declared != null && declared != sort) {
                unsupported.add("PortRedeclarationSortConflict:" + port
                        + ":" + declared + "->" + sort);
                return;
            }
            declaredPortSorts.put(port, sort);
            addDeclaration("port:" + port,
                    "(declare-const " + portName(port) + " " + sort.smt + ")");
        }

        private Sort portSort(String port) {
            Sort declared = declaredPortSorts.get(port);
            if (declared != null) return declared;
            Sort override = portSortOverrides.get(port);
            return override == null ? ports.sort(port) : override;
        }

        private void promotePort(String port, Sort sort) {
            Sort current = portSort(port);
            if (current != sort && current != Sort.VALUE) {
                unsupported.add("PortSortPromotionConflict:" + port + ":"
                        + current + "->" + sort);
                return;
            }
            portSortOverrides.put(port, sort);
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

        private void assertNamed(String name, String expression) {
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
            Sort sort = isMapCell(cell) || isMapType(javaType)
                    ? Sort.MAP : isArrayType(javaType)
                    ? Sort.ARRAY_VALUE : Sort.VALUE;
            ports.put(id, new Port(javaType, sort, input));
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
    }

    private static final class Port {
        private final String javaType;
        private final Sort sort;
        private final boolean input;

        private Port(String javaType, Sort sort, boolean input) {
            this.javaType = javaType;
            this.sort = sort;
            this.input = input;
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

    private static final class SplitPrefix {
        private final JsonElement integerExpression;
        private final String gap;

        private SplitPrefix(JsonElement integerExpression, String gap) {
            this.integerExpression = integerExpression;
            this.gap = firstNonBlank(gap);
        }

        private static SplitPrefix complete(JsonElement integerExpression) {
            return new SplitPrefix(integerExpression, "");
        }

        private static SplitPrefix gap(String gap) {
            return new SplitPrefix(null, gap);
        }

        private boolean complete() {
            return integerExpression != null && gap.isEmpty();
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
        private Path regions;
        private Path output;
        private Path manifest;
        private String fatalRegion = "";
        private String regionInstanceId = "";
        private final Set<String> boundedUpstreamRegions =
                new LinkedHashSet<>();

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
                } else if ("regions".equals(key)) {
                    result.regions = Paths.get(value);
                } else if ("output".equals(key)) {
                    result.output = Paths.get(value);
                } else if ("manifest".equals(key)) {
                    result.manifest = Paths.get(value);
                } else if ("fatal-region".equals(key)) {
                    result.fatalRegion = firstNonBlank(value);
                } else if ("region-instance-id".equals(key)) {
                    result.regionInstanceId = firstNonBlank(value);
                } else if ("bounded-upstream-region".equals(key)) {
                    for (String region : value.split(",")) {
                        String normalized = firstNonBlank(region);
                        if (!normalized.isEmpty()) {
                            result.boundedUpstreamRegions.add(normalized);
                        }
                    }
                } else {
                    throw new IllegalArgumentException(
                            "Unknown composer option: --" + key);
                }
            }
            if (result.fatalQueries == null || result.regions == null
                    || result.output == null) {
                throw new IllegalArgumentException(
                        "--fatal-query, --regions and --output are required");
            }
            if (result.manifest == null) {
                result.manifest = sibling(result.output,
                        "composed_smt_manifest.json");
            }
            return result;
        }
    }

    private static Sort sortOfJava(String type) {
        if (type == null) return Sort.VALUE;
        String normalized = type.replace('.', '/');
        if (isArrayType(normalized)) return Sort.ARRAY_VALUE;
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

    private static boolean referenceDescriptor(String descriptor) {
        return descriptor != null && (descriptor.startsWith("L")
                || descriptor.startsWith("["));
    }

    private static boolean isArrayType(String type) {
        String value = firstNonBlank(type).trim();
        return value.startsWith("[") || value.endsWith("[]");
    }

    static boolean isMapCell(String cell) {
        String value = firstNonBlank(cell).trim();
        Matcher parameter = Pattern.compile(
                ">\\.param[0-9]+:([^#]+)(?:#.*)?$").matcher(value);
        if (parameter.find() && isMapType(parameter.group(1))) {
            return true;
        }
        Matcher field = Pattern.compile(
                "^<[^:]+:\\s+([^()<>\\s]+)\\s+[^()<>\\s]+>(?:#.*)?$")
                .matcher(value);
        if (field.matches() && isMapType(field.group(1))) {
            return true;
        }
        Matcher returned = Pattern.compile(
                "^<[^:]+:\\s+([^<>\\s]+)\\s+[^<>\\s(]+\\([^>]*\\)>\\.return(?:#.*)?$")
                .matcher(value);
        return returned.matches() && isMapType(returned.group(1));
    }

    private static boolean isMapType(String type) {
        return JavaContainerTypes.isMap(type);
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

    private static String portName(String port) {
        return "port__" + smtName(port);
    }

    private static void require(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException(label + " not found: " + path);
        }
    }

}
