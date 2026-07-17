package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayDeque;
import java.util.ArrayList;
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Composes one validated fatal-region query with concolic summaries of its
 * upstream region summaries and runtime-validated equality/read-from edges.
 *
 * <p>This class is intentionally project independent.  Project adapters may
 * discover regions and map ports, but cannot add semantic assertions; the
 * composer only consumes the common JSON schemas.  Missing upstream summaries are retained
 * as uninterpreted relations and reported in the manifest, so a syntactically
 * valid SMT query is never mistaken for a complete causal model.</p>
 */
public final class ConcolicSmtComposer {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();
    private static final String VALUE_REF_WITNESS_AUTHORITY =
            "ACTIVATION_LOCAL_OBJECT_TOKEN_REF_WITNESS_V1";
    private static final String VALUE_REF_WITNESS_KIND =
            "ACTIVATION_LOCAL_REF_SYMBOL_WITNESS";
    private static final String VALUE_REF_WITNESS_TOKEN_AUTHORITY =
            "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN_TO_"
                    + "SCOPED_REF_SYMBOL_V1";
    private static final String VALUE_REF_WITNESS_CERTIFICATION_AUTHORITY =
            "IMPORTER_EXACT_ACTIVATION_TOKEN_AND_DYNAMIC_FIELD_OWNER_JOIN_V1";
    private static final String VALUE_REF_WITNESS_SYMBOL_PREFIX =
            "CAUSYNTH_REF_WITNESS_V1_A";

    private ConcolicSmtComposer() {
    }

    static boolean completeContainerSelectorForTests(JsonObject binding) {
        return Emitter.completeContainerSelector(binding);
    }

    static boolean authenticatedValueRefWitnessForTests(
            JsonObject record, String expressionField,
            String authorityField, String objectTokenField) {
        return Emitter.authenticatedValueRefWitness(record, expressionField,
                authorityField, objectTokenField);
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        Result result = compose(arguments);
        write(arguments.output, result.smtLib);
        write(arguments.manifest, GSON.toJson(result.manifest)
                + System.lineSeparator());
        write(arguments.relationships, GSON.toJson(result.relationships)
                + System.lineSeparator());
        System.out.println(GSON.toJson(result.manifest));
    }

    public static Result compose(Arguments arguments) throws IOException {
        require(arguments.fatalQueries, "fatal branch queries");
        require(arguments.regions, "symbolic regions");
        require(arguments.mergePlan, "symbolic merge plan");

        List<JsonObject> queryRows = readJsonl(arguments.fatalQueries);
        List<JsonObject> summaries = new ArrayList<>();
        for (Path summaryFile : arguments.summaries) {
            summaries.addAll(readJsonl(summaryFile));
        }
        List<JsonObject> regions = readJsonl(arguments.regions);
        // Parse the global plan for schema/backward-compatibility validation,
        // but never recover target relations from it.  Only the scheduler's
        // instance-scoped context embedded in the selected fatal query has
        // enough provenance to enter automatic composition.
        readJson(arguments.mergePlan);
        JsonObject fatal = selectFatalQuery(queryRows, arguments);
        if (fatal.size() == 0) {
            throw new IOException("No ready fatal query matches region="
                    + arguments.fatalRegion + " activation="
                    + arguments.activationId);
        }
        boolean fatalReplayClaimed = bool(fatal,
                "targetReplayValidated", false)
                || bool(fatal, "replayAlreadyValidated", false)
                || !string(fatal, "validatedSummaryId").isEmpty()
                || object(fatal, "validatedTargetSummary").size() > 0;
        boolean fatalReplayRequired = bool(fatal, "readyForReplay", false)
                || array(fatal, "replayMaterializations").size() > 0
                || fatalReplayClaimed;
        FatalReplaySelection fatalReplaySelection;
        if (fatalReplayClaimed
                && "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_"
                .concat("TARGET_REPLAY").equals(string(fatal,
                        "replayValidationAuthority"))) {
            FreshFatalArtifactValidation validation =
                    validateFreshFatalArtifact(fatal, summaries);
            fatalReplaySelection = new FatalReplaySelection(
                    validation.valid, validation.reason,
                    validation.summary, validation.exactCandidateCount);
        } else {
            fatalReplaySelection = selectValidatedFatalReplay(summaries,
                    fatal, fatalReplayClaimed);
        }
        JsonObject fatalReplay = fatalReplaySelection.summary;
        boolean fatalReplayValidated = !fatalReplayRequired
                || fatalReplaySelection.valid;

        PortIndex ports = PortIndex.from(regions);
        JsonObject rawContext = object(fatal, "symbolicContext");
        ContextScope scoped = boundedContext(rawContext,
                arguments.boundedUpstreamRegions);
        JsonObject context = scoped.context;
        boolean instanceScopedContext = context.size() > 0
                && !string(context, "regionInstanceId").isEmpty();

        ResolvedSummaryGraph resolved = resolveSummaryGraph(fatal, context,
                summaries, arguments.boundedUpstreamRegions);
        Set<String> relevantRegions = resolved.relevantRegions;
        Emitter emitter = new Emitter(ports);
        emitter.begin(fatal);
        if (!instanceScopedContext) {
            emitter.unsupported.add(
                    "MissingTargetInstanceSymbolicContext");
        }
        if (!arguments.boundedUpstreamRegions.isEmpty()
                && scoped.includedRelations == 0) {
            emitter.unsupported.add(
                    "BoundedUpstreamRegionsHaveNoContextRelation:"
                            + arguments.boundedUpstreamRegions);
        }
        emitter.unsupported.addAll(resolved.gaps);

        JsonArray fatalConstraints = array(fatal, "constraints");
        List<String> fatalTerms = new ArrayList<>();
        String previousFatalScope = emitter.enterSymbolScope("fatal:"
                + firstNonBlank(string(fatal, "activationId"),
                string(fatal, "queryId"), string(fatal, "siteId"),
                string(fatal, "regionId"), "selected"));
        try {
            emitter.registerEngineArrayInputBindings(fatal, "fatal query");
            emitter.registerVmIntrinsicPlaceholderBindings(fatal,
                    "fatal query");
            for (JsonElement constraint : fatalConstraints) {
                fatalTerms.add(emitter.constraint(constraint,
                        "fatal query"));
            }
        } finally {
            emitter.restoreSymbolScope(previousFatalScope);
        }
        emitter.assertNamed("fatal_path", and(fatalTerms));

        Set<String> missingSummaries = new LinkedHashSet<>(
                resolved.missingSummaryRegions);
        List<String> includedSummaries = new ArrayList<>();
        String fatalRegion = string(fatal, "regionId");
        for (RegionSummarySelection selection
                : resolved.selectedRegionSummaries.values()) {
            JsonObject summary = selection.summary;
            includedSummaries.add(string(summary, "summaryId"));
            emitter.regionSummary(summary);
        }
        for (String regionId : missingSummaries) {
            emitter.uninterpretedRegion(regionId,
                    resolved.missingPorts(regionId, context));
        }

        MergeStats mergeStats = emitter.merge(context, relevantRegions);
        mergeStats.add(emitter.mergeEdgeBindings(resolved.selectedEdges,
                relevantRegions));
        emitter.finishBindings();
        emitter.finish();

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        manifest.addProperty("fatalRegion", fatalRegion);
        manifest.addProperty("fatalActivation",
                string(fatal, "activationId"));
        manifest.addProperty("fatalSite", string(fatal, "siteId"));
        manifest.addProperty("fatalConditionCount", fatalConstraints.size());
        manifest.addProperty("fatalReplayRequired", fatalReplayRequired);
        manifest.addProperty("fatalReplayClaimed", fatalReplayClaimed);
        manifest.addProperty("fatalReplayValidated", fatalReplayValidated);
        manifest.addProperty("fatalReplayGap",
                fatalReplayRequired && !fatalReplayValidated
                        ? fatalReplaySelection.reason : "");
        manifest.addProperty("fatalReplayExactCandidateCount",
                fatalReplaySelection.exactCandidateCount);
        manifest.addProperty("instanceScopedSymbolicContext",
                instanceScopedContext);
        manifest.addProperty("symbolicContextAuthority",
                instanceScopedContext
                        ? "SCHEDULER_SELECTED_RUNTIME_BINDINGS_FOR_FATAL_INSTANCE"
                        : "MISSING_NOT_RECOVERED_FROM_GLOBAL_MERGE_PLAN");
        manifest.addProperty("boundedComposition",
                !arguments.boundedUpstreamRegions.isEmpty());
        manifest.addProperty("compositionScope",
                arguments.boundedUpstreamRegions.isEmpty()
                        ? "FULL_INSTANCE_SCOPED_CONTEXT"
                        : "EXPLICIT_BOUNDED_UPSTREAM_REGIONS");
        manifest.add("boundedUpstreamRegions", GSON.toJsonTree(
                arguments.boundedUpstreamRegions));
        manifest.addProperty("excludedContextRelationCount",
                scoped.excludedRelations);
        manifest.addProperty("excludedAlternativeWriterCount",
                scoped.excludedAlternatives);
        manifest.addProperty("includedBoundedRelationCount",
                scoped.includedRelations);
        manifest.addProperty("validatedFatalReplaySummary",
                string(fatalReplay, "summaryId"));
        manifest.add("fatalReplayAdmission", object(fatalReplay,
                "executionAdmission").deepCopy());
        manifest.add("relevantRegions", GSON.toJsonTree(relevantRegions));
        manifest.add("resolvedProducerKeys",
                GSON.toJsonTree(resolved.producerKeyStrings()));
        manifest.add("reachedBoundedUpstreamRegions",
                GSON.toJsonTree(resolved.reachedBoundedRegions));
        manifest.add("unreachableBoundedUpstreamRegions",
                GSON.toJsonTree(resolved.unreachableBoundedRegions));
        manifest.addProperty("resolvedProducerCount",
                resolved.selectedRegionSummaries.size());
        manifest.addProperty("resolvedDemandedOutputCount",
                resolved.selectedSummaries.size());
        manifest.addProperty("resolvedEdgeBindingCount",
                resolved.selectedEdges.size());
        manifest.addProperty("resolvedRecursiveEdgeCount",
                resolved.recursiveEdgeCount());
        manifest.add("includedSummaries", GSON.toJsonTree(includedSummaries));
        manifest.add("missingSummaryRegions",
                GSON.toJsonTree(missingSummaries));
        manifest.add("incompleteSummaryRegions",
                GSON.toJsonTree(emitter.incompleteSummaries));
        manifest.add("unsupportedExpressions",
                GSON.toJsonTree(emitter.unsupported));
        manifest.add("unboundPorts", GSON.toJsonTree(emitter.unboundPorts));
        manifest.addProperty("equalityConstraintCount",
                mergeStats.equalities);
        manifest.addProperty("readFromConstraintCount",
                mergeStats.readFrom);
        manifest.addProperty("orderConstraintCount", mergeStats.orders);
        manifest.addProperty("objectIdentityConstraintCount",
                mergeStats.identities);
        manifest.addProperty("edgeBindingConstraintCount",
                mergeStats.edgeBindings);
        manifest.addProperty("alternativeWriterGroupCount",
                mergeStats.alternativeWriterGroups);
        manifest.addProperty("guardedAlternativeConstraintCount",
                mergeStats.guardedAlternatives);
        manifest.addProperty("guardedRegionRelationCount",
                emitter.guardedRegionRelationCount);
        manifest.addProperty("guardedPathCaseCount",
                emitter.guardedPathCaseCount);
        manifest.addProperty("heapObservationCount",
                emitter.heapObservationCount);
        manifest.addProperty("heapObservationFieldBindingCount",
                emitter.heapObservationFieldBindingCount);
        manifest.addProperty("finiteMapSnapshotCount",
                emitter.finiteMapSnapshotCount);
        manifest.add("runtimeBoundedMapSnapshots",
                emitter.runtimeBoundedMapSnapshots.deepCopy());
        manifest.add("caseProjectionCatalog",
                emitter.caseProjectionCatalog.deepCopy());
        manifest.addProperty("caseProjectionCatalogCount",
                emitter.caseProjectionCatalog.size());
        manifest.addProperty("caseProjectionCatalogComplete",
                emitter.caseProjectionCatalogComplete);
        manifest.addProperty("symbolicRelationshipCandidateCount",
                emitter.relationshipCandidates.size());
        manifest.addProperty("assertionCount", emitter.assertionCount);
        boolean complete = missingSummaries.isEmpty()
                && emitter.incompleteSummaries.isEmpty()
                && emitter.unsupported.isEmpty()
                && emitter.unboundPorts.isEmpty()
                && emitter.caseProjectionCatalogComplete
                && fatalReplayValidated
                && bool(fatal, "readyForSolver", false);
        manifest.addProperty("complete", complete);
        manifest.addProperty("status", complete
                ? "COMPLETE_BOUNDED_COMPOSITION"
                : "COMPOSITION_WITH_EXPLICIT_GAPS");
        manifest.addProperty("soundnessScope",
                "SELECTED_REGION_PATHS_AND_RUNTIME_VALIDATED_BINDINGS");
        manifest.addProperty("eligibleToReportAutomaticRelationship",
                complete && fatalReplayValidated);
        manifest.addProperty("domainSemanticAdapterUsed", false);
        manifest.addProperty("explicitContractsIncluded", false);
        manifest.addProperty("output",
                arguments.output.toAbsolutePath().toString());
        manifest.addProperty("relationshipCandidates",
                arguments.relationships.toAbsolutePath().toString());
        JsonObject relationships = new JsonObject();
        relationships.addProperty("schemaVersion", 1);
        relationships.addProperty("kind",
                "SYMBOLIC_RELATIONSHIP_CANDIDATES");
        relationships.addProperty("baseSmt",
                arguments.output.toAbsolutePath().toString());
        relationships.addProperty("fatalRegion", fatalRegion);
        relationships.addProperty("candidateCount",
                emitter.relationshipCandidates.size());
        relationships.add("relationships",
                GSON.toJsonTree(emitter.relationshipCandidates));
        relationships.addProperty("proofMethod",
                "CHECK_BASE_AND_NEGATED_RELATION_WITH_SMT_SOLVER");
        relationships.addProperty("fatalReplayValidated",
                fatalReplayValidated);
        relationships.addProperty("boundedComposition",
                !arguments.boundedUpstreamRegions.isEmpty());
        relationships.add("boundedUpstreamRegions", GSON.toJsonTree(
                arguments.boundedUpstreamRegions));
        relationships.addProperty("eligibleForAutomaticVerification",
                complete && fatalReplayValidated);
        return new Result(emitter.render(), manifest, relationships);
    }

    private static FatalReplaySelection selectValidatedFatalReplay(
            List<JsonObject> summaries, JsonObject fatal,
            boolean validatedClaim) {
        String activationId = string(fatal, "activationId");
        String regionId = string(fatal, "regionId");
        String regionInstanceId = firstNonBlank(string(fatal,
                "regionInstanceId"), string(object(fatal,
                "symbolicContext"), "regionInstanceId"));
        if (activationId.isEmpty() || regionId.isEmpty()
                || regionInstanceId.isEmpty()) {
            return FatalReplaySelection.failure(
                    "FATAL_REPLAY_IDENTITY_INCOMPLETE", 0);
        }
        String expectedSummaryId = string(fatal, "validatedSummaryId");
        JsonObject embedded = object(fatal, "validatedTargetSummary");
        if (validatedClaim && (!bool(fatal,
                "targetReplayValidated", false)
                || !bool(fatal, "replayAlreadyValidated", false)
                || expectedSummaryId.isEmpty() || embedded.size() == 0)) {
            return FatalReplaySelection.failure(
                    "FATAL_VALIDATED_REPLAY_CLAIM_INCOMPLETE", 0);
        }

        List<JsonObject> exact = new ArrayList<>();
        for (JsonObject summary : summaries) {
            if (!regionId.equals(string(summary, "regionId"))
                    || !activationId.equals(string(summary, "activationId"))
                    || !regionInstanceId.equals(string(summary,
                    "regionInstanceId"))
                    || validatedClaim && !expectedSummaryId.equals(
                    string(summary, "summaryId"))) continue;
            exact.add(summary);
        }
        if (exact.size() != 1) {
            return FatalReplaySelection.failure(exact.isEmpty()
                    ? "EXACT_FATAL_REPLAY_SUMMARY_MISSING"
                    : "EXACT_FATAL_REPLAY_SUMMARY_NOT_UNIQUE", exact.size());
        }
        JsonObject selected = exact.get(0);
        JsonObject admission = object(selected, "executionAdmission");
        if (string(selected, "summaryId").isEmpty()
                || !bool(selected, "valid", false)
                || !bool(selected, "targetReplayValidated", false)
                || bool(selected, "branchOverrideUsed", true)
                || !RegionCaptureGoal.from(selected).isTargetBranch()
                || !bool(admission, "required", false)
                || !bool(admission, "valid", false)
                || bool(admission, "branchOverrideAccepted", true)
                || !"SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_"
                .concat("OBSERVATION").equals(string(admission,
                        "authority"))) {
            return FatalReplaySelection.failure(
                    "EXACT_FATAL_REPLAY_ADMISSION_INVALID", 1);
        }
        if (!validatedClaim) {
            return FatalReplaySelection.success(selected, 1);
        }

        String replayAuthority = string(fatal,
                "replayValidationAuthority");
        boolean fresh = "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_"
                .concat("UNFORCED_TARGET_REPLAY").equals(replayAuthority);
        boolean same = "SAME_INSTANCE_IMPORTED_UNFORCED_TARGET_REPLAY"
                .equals(replayAuthority);
        JsonObject embeddedAdmission = object(embedded,
                "executionAdmission");
        if (!fresh && !same
                || !expectedSummaryId.equals(string(embedded, "summaryId"))
                || !activationId.equals(string(embedded, "activationId"))
                || !regionId.equals(string(embedded, "regionId"))
                || !regionInstanceId.equals(string(embedded,
                "regionInstanceId"))
                || !bool(embedded, "targetReplayValidated", false)
                || bool(embedded, "branchOverrideUsed", true)
                || !admission.equals(embeddedAdmission)) {
            return FatalReplaySelection.failure(
                    "FATAL_ROOT_VALIDATED_METADATA_MISMATCH", 1);
        }
        if (fresh) {
            JsonObject provenance = object(fatal,
                    "targetRebaseProvenance");
            if (!activationId.equals(string(provenance, "activationId"))
                    || !regionInstanceId.equals(string(provenance,
                    "regionInstanceId"))
                    || bool(provenance, "downstreamInjectionUsed", true)
                    || bool(provenance, "branchOverrideUsed", true)
                    || !replayAuthority.equals(string(provenance,
                    "authority"))) {
                return FatalReplaySelection.failure(
                        "FRESH_FATAL_REBASE_PROVENANCE_MISMATCH", 1);
            }
            String formulaIssue = freshFatalFormulaIssue(fatal, selected);
            if (!formulaIssue.isEmpty()) {
                return FatalReplaySelection.failure(formulaIssue, 1);
            }
        }
        return FatalReplaySelection.success(selected, 1);
    }

    /**
     * Shared campaign/composer admission for a completed fresh fatal root.
     * Callers must pass the exact summary ledger they intend to persist or
     * compose; the validation neither searches a different cache nor trusts
     * metadata embedded in the root by itself.
     */
    static FreshFatalArtifactValidation validateFreshFatalArtifact(
            JsonObject fatal, List<JsonObject> summaries) {
        if (fatal == null || !"FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_"
                .concat("UNFORCED_TARGET_REPLAY").equals(string(fatal,
                        "replayValidationAuthority"))) {
            return FreshFatalArtifactValidation.failure(
                    "FRESH_FATAL_REPLAY_AUTHORITY_MISSING", 0);
        }
        FatalReplaySelection selected = selectValidatedFatalReplay(
                summaries == null ? Collections.<JsonObject>emptyList()
                        : summaries, fatal, true);
        return selected.valid
                ? FreshFatalArtifactValidation.success(selected.summary,
                selected.exactCandidateCount)
                : FreshFatalArtifactValidation.failure(selected.reason,
                selected.exactCandidateCount);
    }

    /** Re-derives every fresh-fatal formula component from its exact summary. */
    private static String freshFatalFormulaIssue(JsonObject fatal,
                                                 JsonObject summary) {
        JsonObject storedFresh = object(summary,
                "freshObservedTargetQuery");
        if (storedFresh.size() == 0) {
            return "FRESH_FATAL_SUMMARY_QUERY_MISSING";
        }
        for (String field : new String[]{"activationId", "regionId",
                "regionInstanceId", "siteId", "occurrence",
                "desiredOutcome", "conditionIndex", "constraints",
                "freshObservedTargetCondition", "negatedTargetCondition",
                "engineArrayInputBindings", "symbolicContext",
                "formulaAuthority", "targetPolicy",
                "freshQueryRebuildProvenance"}) {
            JsonElement expected = fatal.get(field);
            JsonElement stored = storedFresh.get(field);
            if (expected == null || stored == null
                    || !expected.equals(stored)) {
                return "FRESH_FATAL_SUMMARY_QUERY_MISMATCH:" + field;
            }
        }
        if (!"FRESH_INSTANCE_IMPORTED_UNFORCED_TARGET_PREFIX_PLUS_"
                .concat("OBSERVED_TARGET").equals(string(fatal,
                        "formulaAuthority"))) {
            return "FRESH_FATAL_FORMULA_AUTHORITY_INVALID";
        }
        JsonObject rebuild = object(fatal,
                "freshQueryRebuildProvenance");
        if (!string(summary, "summaryId").equals(string(rebuild,
                "freshSummaryId"))
                || !string(fatal, "activationId").equals(string(rebuild,
                "activationId"))
                || !string(fatal, "regionInstanceId").equals(string(rebuild,
                "regionInstanceId"))
                || string(rebuild, "transitionExecutionId").isEmpty()
                || !"FRESH_SUMMARY_PATH_AND_CURRENT_RUNTIME_EDGE_LEDGER"
                .equals(string(rebuild, "authority"))) {
            return "FRESH_FATAL_FORMULA_PROVENANCE_MISMATCH";
        }
        String site = string(fatal, "siteId");
        int occurrence = integer(fatal, "occurrence", -1);
        boolean desired = bool(fatal, "desiredOutcome", false);
        JsonObject mapping = null;
        int mappingCount = 0;
        for (JsonElement element : array(summary, "branchMappings")) {
            if (!element.isJsonObject()) continue;
            JsonObject candidate = element.getAsJsonObject();
            if (site.equals(string(candidate, "siteId"))
                    && occurrence == integer(candidate, "occurrence", -1)) {
                mapping = candidate;
                mappingCount++;
            }
        }
        if (site.isEmpty() || occurrence < 1 || mappingCount != 1
                || mapping == null
                || bool(mapping, "overrideApplied", false)
                || desired != bool(mapping, "observedOutcome",
                bool(mapping, "outcome", !desired))) {
            return "FRESH_FATAL_BRANCH_MAPPING_INVALID";
        }
        JsonArray path = array(summary, "pathCondition");
        int conditionIndex = integer(mapping, "conditionIndex", -1);
        if (conditionIndex < 0 || conditionIndex >= path.size()
                || integer(fatal, "conditionIndex", -2) != conditionIndex
                || mapping.has("condition") && !mapping.get("condition")
                .equals(path.get(conditionIndex))) {
            return "FRESH_FATAL_CONDITION_MAPPING_INVALID";
        }
        JsonArray constraints = array(fatal, "constraints");
        if (constraints.size() != conditionIndex + 1) {
            return "FRESH_FATAL_PREFIX_LENGTH_MISMATCH";
        }
        for (int index = 0; index <= conditionIndex; index++) {
            if (!constraints.get(index).equals(path.get(index))) {
                return "FRESH_FATAL_PREFIX_CONSTRAINT_MISMATCH";
            }
        }
        JsonElement observed = path.get(conditionIndex);
        if (!observed.equals(fatal.get("freshObservedTargetCondition"))
                || !observed.equals(fatal.get("negatedTargetCondition"))
                || !"KEEP_FRESH_OBSERVED_DESIRED_TARGET_CONDITION".equals(
                string(fatal, "targetPolicy"))) {
            return "FRESH_FATAL_TARGET_CONDITION_MISMATCH";
        }
        if (!array(fatal, "engineArrayInputBindings").equals(array(summary,
                "engineArrayInputBindings"))) {
            return "FRESH_FATAL_ENGINE_ARRAY_BINDINGS_MISMATCH";
        }
        return freshFatalContextIssue(fatal, string(rebuild,
                "transitionExecutionId"));
    }

    private static String freshFatalContextIssue(JsonObject fatal,
                                                 String executionId) {
        String region = string(fatal, "regionId");
        String instance = string(fatal, "regionInstanceId");
        JsonObject context = object(fatal, "symbolicContext");
        if (!region.equals(string(context, "regionId"))
                || !instance.equals(string(context, "regionInstanceId"))
                || !executionId.equals(string(context,
                "transitionExecutionId"))
                || !"CURRENT_EDGE_LEDGER_EXACT_TARGET_ENDPOINT_INSTANCE"
                .equals(string(context, "selectionAuthority"))) {
            return "FRESH_FATAL_CONTEXT_SCOPE_MISMATCH";
        }
        int selected = 0;
        for (String collection : new String[]{"equalityRelations",
                "versionedStateMerges"}) {
            for (JsonElement element : array(context, collection)) {
                if (!element.isJsonObject()) {
                    return "FRESH_FATAL_CONTEXT_RELATION_MALFORMED";
                }
                int count = exactTargetBindingCount(
                        element.getAsJsonObject(), region, instance);
                if (count < 0) return "FRESH_FATAL_CONTEXT_ENDPOINT_MISMATCH";
                selected += count;
            }
        }
        for (JsonElement groupElement : array(context,
                "alternativeWriterGroups")) {
            if (!groupElement.isJsonObject()) {
                return "FRESH_FATAL_CONTEXT_ALTERNATIVE_GROUP_MALFORMED";
            }
            JsonObject group = groupElement.getAsJsonObject();
            if (array(group, "alternatives").size() < 2) {
                return "FRESH_FATAL_CONTEXT_ALTERNATIVE_GROUP_INCOMPLETE";
            }
            for (JsonElement alternative : array(group, "alternatives")) {
                if (!alternative.isJsonObject()) {
                    return "FRESH_FATAL_CONTEXT_ALTERNATIVE_MALFORMED";
                }
                int count = exactTargetBindingCount(
                        alternative.getAsJsonObject(), region, instance);
                if (count < 0) return "FRESH_FATAL_CONTEXT_ENDPOINT_MISMATCH";
                selected += count;
            }
        }
        return selected > 0 ? "" : "FRESH_FATAL_CONTEXT_HAS_NO_BINDING";
    }

    /** Returns -1 for an invalid relation, otherwise its exact binding count. */
    private static int exactTargetBindingCount(JsonObject relation,
                                               String targetRegion,
                                               String targetInstance) {
        String fromRegion = contextEndpointRegion(string(relation,
                "fromEndpoint"));
        String toRegion = contextEndpointRegion(string(relation,
                "toEndpoint"));
        boolean targetFrom = targetRegion.equals(fromRegion);
        boolean targetTo = targetRegion.equals(toRegion);
        if (targetFrom == targetTo) return -1;
        JsonArray bindings = array(relation, "selectedBindings");
        if (bindings.size() == 0) return -1;
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) return -1;
            JsonObject binding = element.getAsJsonObject();
            if (targetFrom && !targetInstance.equals(string(binding,
                    "fromRegionInstance"))
                    || targetTo && !targetInstance.equals(string(binding,
                    "toRegionInstance"))) return -1;
        }
        return bindings.size();
    }

    private static String contextEndpointRegion(String endpoint) {
        String value = endpoint == null ? "" : endpoint;
        // A fallback scheduler endpoint is REGION.X::REGION.X.out.N.  Use
        // the earliest schema delimiter; fixed precedence would invent the
        // non-existent region "REGION.X::REGION.X" for that shape.
        int marker = -1;
        for (String delimiter : new String[]{".in.", ".out.", "::"}) {
            int candidate = value.indexOf(delimiter);
            if (candidate > 0 && (marker < 0 || candidate < marker)) {
                marker = candidate;
            }
        }
        return marker <= 0 ? "" : value.substring(0, marker);
    }

    private static JsonObject selectFatalQuery(List<JsonObject> rows,
                                               Arguments arguments) {
        for (JsonObject row : rows) {
            if (!arguments.fatalRegion.isEmpty()
                    && !arguments.fatalRegion.equals(string(row,
                    "regionId"))) {
                continue;
            }
            if (!arguments.activationId.isEmpty()
                    && !arguments.activationId.equals(string(row,
                    "activationId"))) {
                continue;
            }
            if (bool(row, "readyForSolver", false)) {
                return row;
            }
        }
        return new JsonObject();
    }

    private static Map<String, JsonObject> selectSummaries(
            List<JsonObject> summaries, Set<String> regions,
            JsonObject fatal) {
        Map<String, JsonObject> result = new LinkedHashMap<>();
        for (JsonObject summary : summaries) {
            String region = string(summary, "regionId");
            if (!regions.contains(region) || !bool(summary, "valid", true)) {
                continue;
            }
            JsonObject previous = result.get(region);
            if (previous == null || summaryRank(summary, fatal)
                    > summaryRank(previous, fatal)) {
                result.put(region, summary);
            }
        }
        return result;
    }

    private static int summaryRank(JsonObject summary, JsonObject fatal) {
        int rank = 0;
        JsonObject relation = object(summary, "regionRelation");
        if ("GUARDED_PATH_MERGE".equals(string(relation, "kind"))) {
            rank += 100;
            if (bool(relation, "complete", false)) rank += 100;
        }
        if (bool(summary, "relationallyComplete", false)) rank += 20;
        if (string(summary, "activationId").equals(
                string(fatal, "activationId"))) rank += 5;
        if (summary.has("protocolModel")) rank -= 1000;
        return rank;
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
            JsonObject fatal, JsonObject context, List<JsonObject> summaries,
            Set<String> boundedRegions) {
        String fatalRegion = string(fatal, "regionId");
        String fatalInstance = firstNonBlank(string(context,
                "regionInstanceId"), string(fatal, "regionInstanceId"));
        ResolvedSummaryGraph result = new ResolvedSummaryGraph(fatalRegion,
                fatalInstance, boundedRegions);

        for (String field : new String[]{"equalityRelations",
                "versionedStateMerges"}) {
            for (JsonElement element : array(context, field)) {
                if (!element.isJsonObject()) continue;
                seedContextRelation(result, element.getAsJsonObject(),
                        summaries, fatal, boundedRegions);
            }
        }
        for (JsonElement element : array(context,
                "alternativeWriterGroups")) {
            if (!element.isJsonObject()) continue;
            JsonObject group = element.getAsJsonObject();
            String consumer = firstNonBlank(string(group,
                    "downstreamEndpoint"), string(group,
                    "consumerEndpoint"), alternativeConsumer(group));
            for (JsonElement alternative : array(group, "alternatives")) {
                if (!alternative.isJsonObject()) continue;
                JsonObject relation = alternative.getAsJsonObject().deepCopy();
                if (string(relation, "toEndpoint").isEmpty()) {
                    relation.addProperty("toEndpoint", consumer);
                }
                seedContextRelation(result, relation, summaries, fatal,
                        boundedRegions);
            }
        }

        // Preserve the existing direct edge-binding path.  Unlike a global
        // merge plan, an exact summary binding names both runtime instances
        // and is therefore safe to use as an additional first-hop seed.
        for (JsonObject summary : summaries) {
            if (!bool(summary, "valid", true)) continue;
            for (JsonElement element : edgeBindings(summary)) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if (!trustedRuntimeReadFrom(binding)) {
                    continue;
                }
                if (!bindingTargets(binding, fatalRegion, fatalInstance, "")) {
                    continue;
                }
                String sourceRegion = bindingSourceRegion(binding);
                if (!allowedBoundedSource(sourceRegion, boundedRegions)) {
                    continue;
                }
                resolveBindingProducer(result, binding, summaries, fatal,
                        fatalRegion, fatalInstance, false);
            }
        }

        while (!result.pending.isEmpty()) {
            ProducerKey consumer = result.pending.removeFirst();
            JsonObject consumerSummary = result.selectedSummaries.get(
                    consumer);
            if (consumerSummary == null) continue;
            if (!result.expanded.add(result.expansionIdentity(consumer,
                    consumerSummary))) continue;
            Set<String> demandedInputs = requestedInputPorts(consumerSummary);
            if (demandedInputs.isEmpty()) continue;

            for (JsonObject candidate : summaries) {
                if (!bool(candidate, "valid", true)) continue;
                for (JsonElement element : edgeBindings(candidate)) {
                    if (!element.isJsonObject()) continue;
                    JsonObject binding = element.getAsJsonObject();
                    if (!bindingTargets(binding, consumer.regionId,
                            consumer.instanceId, demandedInputs)) {
                        continue;
                    }
                    if (!trustedRuntimeReadFrom(binding)) {
                        continue;
                    }
                    String sourceRegion = bindingSourceRegion(binding);
                    if (!allowedBoundedSource(sourceRegion, boundedRegions)) {
                        continue;
                    }
                    resolveBindingProducer(result, binding, summaries, fatal,
                            consumer.regionId, consumer.instanceId, true);
                }
            }
        }

        result.finishBounds();
        result.rejectRepeatedRegionInstances();
        return result;
    }

    private static void seedContextRelation(ResolvedSummaryGraph graph,
                                            JsonObject relation,
                                            List<JsonObject> summaries,
                                            JsonObject fatal,
                                            Set<String> boundedRegions) {
        String output = string(relation, "fromEndpoint");
        String input = string(relation, "toEndpoint");
        String sourceRegion = regionOf(output);
        if (!graph.fatalRegion.equals(regionOf(input))
                || sourceRegion.isEmpty()
                || !allowedBoundedSource(sourceRegion, boundedRegions)) {
            return;
        }
        JsonArray bindings = selectedBindings(relation);
        boolean scopedBindingSeen = false;
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String targetInstance = bindingTargetInstance(binding);
            if (!targetInstance.isEmpty()
                    && !graph.fatalInstance.equals(targetInstance)) {
                continue;
            }
            scopedBindingSeen = true;
            String sourceInstance = bindingSourceInstance(binding);
            ProducerKey key = selectExactProducer(graph, summaries, fatal,
                    sourceRegion, sourceInstance, output);
            if (key != null) {
                graph.addDirectBindingIfPresent(key, graph.fatalRegion,
                        graph.fatalInstance, input);
            }
        }
        if (!scopedBindingSeen) {
            ProducerKey key = selectExactProducer(graph, summaries, fatal,
                    sourceRegion, "", output);
            if (key != null) {
                graph.addDirectBindingIfPresent(key, graph.fatalRegion,
                        graph.fatalInstance, input);
            }
        }
    }

    private static void resolveBindingProducer(ResolvedSummaryGraph graph,
                                               JsonObject binding,
                                               List<JsonObject> summaries,
                                               JsonObject fatal,
                                               String targetRegion,
                                               String targetInstance,
                                               boolean recursive) {
        if (!trustedRuntimeReadFrom(binding)) {
            graph.gaps.add((recursive
                    ? "UntrustedRecursiveEdgeBinding:"
                    : "UntrustedDirectEdgeBinding:")
                    + firstNonBlank(string(binding, "edgeId"),
                    GSON.toJson(binding)));
            return;
        }
        String sourceRegion = bindingSourceRegion(binding);
        String sourceInstance = bindingSourceInstance(binding);
        String output = bindingSourceOutput(binding);
        String input = bindingTargetInput(binding);
        if (sourceRegion.isEmpty() || output.isEmpty() || input.isEmpty()) {
            graph.gaps.add("MalformedRecursiveEdgeBinding:"
                    + firstNonBlank(string(binding, "edgeId"),
                    GSON.toJson(binding)));
            return;
        }
        ProducerKey key = selectExactProducer(graph, summaries, fatal,
                sourceRegion, sourceInstance, output);
        if (key == null) return;
        JsonObject selected = graph.selectedSummaries.get(key);
        JsonObject exact = matchingBinding(selected, key, targetRegion,
                targetInstance, input, binding);
        if (exact.size() == 0) {
            graph.gaps.add("SelectedSummaryMissingExactEdgeBinding:"
                    + key + "->" + targetRegion + "@" + targetInstance
                    + ":" + input);
            return;
        }
        graph.addEdge(new ResolvedEdge(key, selected, targetRegion,
                targetInstance, input, exact, recursive));
    }

    private static ProducerKey selectExactProducer(
            ResolvedSummaryGraph graph, List<JsonObject> summaries,
            JsonObject fatal, String region, String requestedInstance,
            String output) {
        RegionSummarySelection regionSelection =
                graph.selectedRegionSummaries.get(region);
        if (regionSelection != null && !requestedInstance.isEmpty()
                && !requestedInstance.equals(regionSelection.instanceId)) {
            graph.addMissingPort(region, output);
            graph.gaps.add("ConflictingProducerRegionInstance:"
                    + producerLabel(region, requestedInstance, output)
                    + ":selected=" + regionSelection.instanceId);
            return null;
        }
        Map<String, JsonObject> unique = new LinkedHashMap<>();
        for (JsonObject summary : summaries) {
            if (!region.equals(string(summary, "regionId"))
                    || !bool(summary, "valid", true)
                    || !summaryProvidesOutput(summary, output)) {
                continue;
            }
            Set<String> instances = summaryInstances(summary);
            if (!requestedInstance.isEmpty()) {
                String directInstance = string(summary,
                        "regionInstanceId");
                if (!directInstance.isEmpty()
                        ? !requestedInstance.equals(directInstance)
                        : instances.size() != 1
                        || !instances.contains(requestedInstance)) {
                    continue;
                }
            } else if (instances.size() != 1) {
                continue;
            }
            String identity = firstNonBlank(string(summary, "summaryId"),
                    string(summary, "cacheKey"), GSON.toJson(summary));
            unique.put(identity, summary);
        }
        if (unique.isEmpty()) {
            graph.missingSummaryRegions.add(region);
            graph.addMissingPort(region, output);
            graph.gaps.add("MissingExactProducerSummary:"
                    + producerLabel(region, requestedInstance, output));
            return null;
        }
        List<JsonObject> candidates = new ArrayList<>(unique.values());
        candidates.sort(Comparator
                .comparingInt((JsonObject value) -> summaryRank(value, fatal))
                .reversed()
                .thenComparing(value -> firstNonBlank(string(value,
                        "summaryId"), string(value, "cacheKey"))));
        JsonObject selected = candidates.get(0);
        int selectedRank = summaryRank(selected, fatal);
        if (candidates.size() > 1
                && summaryRank(candidates.get(1), fatal) == selectedRank) {
            graph.gaps.add("AmbiguousExactProducerSummary:"
                    + producerLabel(region, requestedInstance, output));
            return null;
        }
        Set<String> instances = summaryInstances(selected);
        String instance = firstNonBlank(requestedInstance,
                instances.size() == 1 ? instances.iterator().next() : "");
        if (instance.isEmpty()) {
            graph.gaps.add("MissingProducerInstanceIdentity:" + region
                    + ":" + output);
            return null;
        }
        ProducerKey key = new ProducerKey(region, instance, output);
        if (!graph.admitRegionSummary(key, selected)) return null;
        JsonObject previous = graph.selectedSummaries.get(key);
        if (previous != null && !sameSummary(previous, selected)) {
            graph.gaps.add("ConflictingProducerSummarySelection:" + key);
            return null;
        }
        if (previous == null) {
            graph.selectedSummaries.put(key, selected);
            graph.relevantRegions.add(region);
            if (graph.boundedRegions.contains(region)) {
                graph.reachedBoundedRegions.add(region);
            }
            graph.pending.addLast(key);
        }
        return key;
    }

    private static boolean sameSummary(JsonObject left, JsonObject right) {
        String leftId = firstNonBlank(string(left, "summaryId"),
                string(left, "cacheKey"));
        String rightId = firstNonBlank(string(right, "summaryId"),
                string(right, "cacheKey"));
        return !leftId.isEmpty() && leftId.equals(rightId)
                || GSON.toJson(left).equals(GSON.toJson(right));
    }

    private static String producerLabel(String region, String instance,
                                        String output) {
        return region + "[instance="
                + firstNonBlank(instance, "<unique-instance>")
                + ",output=" + output + "]";
    }

    private static boolean summaryProvidesOutput(JsonObject summary,
                                                 String output) {
        JsonObject requested = object(summary, "requestedOutput");
        if (output.equals(string(requested, "portId"))
                || output.equals(string(requested, "cell"))) return true;
        if (object(summary, "outputExpressions").has(output)) return true;
        for (JsonElement element : array(summary, "heapEffects")) {
            if (element.isJsonObject() && output.equals(string(
                    element.getAsJsonObject(), "outputPort"))) return true;
        }
        JsonObject relation = object(summary, "regionRelation");
        for (JsonElement caseElement : array(relation, "cases")) {
            if (!caseElement.isJsonObject()) continue;
            JsonObject item = caseElement.getAsJsonObject();
            if (object(item, "outputExpressions").has(output)) return true;
            for (JsonElement effectElement : array(item, "heapEffects")) {
                if (effectElement.isJsonObject() && output.equals(string(
                        effectElement.getAsJsonObject(), "outputPort"))) {
                    return true;
                }
            }
        }
        return false;
    }

    private static Set<String> summaryInstances(JsonObject summary) {
        Set<String> result = new LinkedHashSet<>();
        String direct = string(summary, "regionInstanceId");
        if (!direct.isEmpty()) result.add(direct);
        for (JsonElement element : array(summary,
                "sourceRegionInstanceIds")) {
            if (element.isJsonPrimitive()) {
                String value = element.getAsString();
                if (!value.isEmpty()) result.add(value);
            }
        }
        return result;
    }

    private static Set<String> requestedInputPorts(JsonObject summary) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : array(object(summary,
                "requestedOutputSlice"), "inputPorts")) {
            if (element.isJsonPrimitive()) result.add(element.getAsString());
        }
        result.remove("");
        return result;
    }

    private static JsonObject matchingBinding(JsonObject summary,
                                              ProducerKey source,
                                              String targetRegion,
                                              String targetInstance,
                                              String targetInput,
                                              JsonObject preferred) {
        Map<String, JsonObject> matches = new LinkedHashMap<>();
        for (JsonElement element : edgeBindings(summary)) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!source.instanceId.equals(bindingSourceInstance(binding))
                    || !source.outputPort.equals(bindingSourceOutput(binding))
                    || !trustedRuntimeReadFrom(binding)
                    || !bindingTargets(binding, targetRegion,
                    targetInstance, targetInput)) {
                continue;
            }
            matches.put(GSON.toJson(binding), binding);
        }
        if (matches.isEmpty()) return new JsonObject();
        String preferredJson = preferred == null ? "" : GSON.toJson(preferred);
        JsonObject exact = matches.get(preferredJson);
        if (exact != null) return exact;
        return matches.size() == 1
                ? matches.values().iterator().next() : new JsonObject();
    }

    private static JsonArray selectedBindings(JsonObject relation) {
        JsonArray selected = array(relation, "selectedBindings");
        return selected.size() > 0 ? selected
                : array(relation, "runtimeBindings");
    }

    private static boolean trustedRuntimeReadFrom(JsonObject binding) {
        return "RUNTIME_CONFIRMED_READ_FROM".equals(
                string(binding, "selectionAuthority"));
    }

    private static boolean bindingTargets(JsonObject binding, String region,
                                          String instance, String input) {
        String bindingRegion = firstNonBlank(string(binding, "toRegion"),
                regionOf(bindingTargetInput(binding)));
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
        return firstNonBlank(string(binding, "fromRegion"), regionOf(
                bindingSourceOutput(binding)));
    }

    private static String bindingSourceInstance(JsonObject binding) {
        return firstNonBlank(string(binding, "fromRegionInstance"),
                string(binding, "producerRegionInstance"));
    }

    private static String bindingTargetInstance(JsonObject binding) {
        return firstNonBlank(string(binding, "toRegionInstance"),
                string(binding, "consumerRegionInstance"));
    }

    private static String bindingSourceOutput(JsonObject binding) {
        return firstNonBlank(string(binding, "fromOutputPort"),
                string(binding, "producerOutputPort"));
    }

    private static String bindingTargetInput(JsonObject binding) {
        return firstNonBlank(string(binding, "toInputPort"),
                string(binding, "consumerInputPort"));
    }

    private static boolean allowedBoundedSource(String region,
                                                Set<String> boundedRegions) {
        return boundedRegions.isEmpty() || boundedRegions.contains(region);
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

    private static final class RegionSummarySelection {
        private final String regionId;
        private final String instanceId;
        private final JsonObject summary;
        private final Set<String> demandedOutputs = new LinkedHashSet<>();

        private RegionSummarySelection(ProducerKey key,
                                       JsonObject summary) {
            this.regionId = key.regionId;
            this.instanceId = key.instanceId;
            this.summary = summary;
            this.demandedOutputs.add(key.outputPort);
        }
    }

    private static final class FatalReplaySelection {
        private final boolean valid;
        private final String reason;
        private final JsonObject summary;
        private final int exactCandidateCount;

        private FatalReplaySelection(boolean valid, String reason,
                                     JsonObject summary,
                                     int exactCandidateCount) {
            this.valid = valid;
            this.reason = reason == null ? "" : reason;
            this.summary = summary == null
                    ? new JsonObject() : summary;
            this.exactCandidateCount = exactCandidateCount;
        }

        private static FatalReplaySelection success(JsonObject summary,
                                                    int candidateCount) {
            return new FatalReplaySelection(true, "", summary,
                    candidateCount);
        }

        private static FatalReplaySelection failure(String reason,
                                                    int candidateCount) {
            return new FatalReplaySelection(false, reason,
                    new JsonObject(), candidateCount);
        }
    }

    static final class FreshFatalArtifactValidation {
        final boolean valid;
        final String reason;
        final JsonObject summary;
        final int exactCandidateCount;

        private FreshFatalArtifactValidation(boolean valid, String reason,
                                             JsonObject summary,
                                             int exactCandidateCount) {
            this.valid = valid;
            this.reason = reason == null ? "" : reason;
            this.summary = summary == null
                    ? new JsonObject() : summary.deepCopy();
            this.exactCandidateCount = exactCandidateCount;
        }

        static FreshFatalArtifactValidation success(JsonObject summary,
                                                     int candidateCount) {
            return new FreshFatalArtifactValidation(true, "", summary,
                    candidateCount);
        }

        static FreshFatalArtifactValidation failure(String reason,
                                                     int candidateCount) {
            return new FreshFatalArtifactValidation(false, reason,
                    new JsonObject(), candidateCount);
        }

        JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("required", true);
            result.addProperty("valid", valid);
            result.addProperty("reason", reason);
            result.addProperty("summaryId", string(summary, "summaryId"));
            result.addProperty("exactCandidateCount", exactCandidateCount);
            result.addProperty("authority", valid
                    ? "EXACT_FRESH_FATAL_SUMMARY_FORMULA_AND_CONTEXT"
                    : "NONE");
            return result;
        }
    }

    private static final class ResolvedEdge {
        private final ProducerKey source;
        private final JsonObject summary;
        private final String targetRegion;
        private final String targetInstance;
        private final String targetInput;
        private final JsonObject binding;
        private final boolean recursive;

        private ResolvedEdge(ProducerKey source, JsonObject summary,
                             String targetRegion, String targetInstance,
                             String targetInput, JsonObject binding,
                             boolean recursive) {
            this.source = source;
            this.summary = summary;
            this.targetRegion = firstNonBlank(targetRegion);
            this.targetInstance = firstNonBlank(targetInstance);
            this.targetInput = firstNonBlank(targetInput);
            this.binding = binding.deepCopy();
            this.recursive = recursive;
        }

        private String identity() {
            return source + "->" + targetRegion + "@" + targetInstance
                    + ":" + targetInput + "\n" + GSON.toJson(binding);
        }
    }

    private static final class ResolvedSummaryGraph {
        private final String fatalRegion;
        private final String fatalInstance;
        private final Set<String> boundedRegions;
        private final Map<ProducerKey, JsonObject> selectedSummaries =
                new LinkedHashMap<>();
        private final Map<String, RegionSummarySelection>
                selectedRegionSummaries = new LinkedHashMap<>();
        private final List<ResolvedEdge> selectedEdges = new ArrayList<>();
        private final Set<String> selectedEdgeIds = new LinkedHashSet<>();
        private final Deque<ProducerKey> pending = new ArrayDeque<>();
        private final Set<String> expanded = new LinkedHashSet<>();
        private final Set<String> relevantRegions = new LinkedHashSet<>();
        private final Set<String> reachedBoundedRegions =
                new LinkedHashSet<>();
        private final Set<String> unreachableBoundedRegions =
                new LinkedHashSet<>();
        private final Set<String> missingSummaryRegions =
                new LinkedHashSet<>();
        private final Map<String, Set<String>> missingPortsByRegion =
                new LinkedHashMap<>();
        private final Set<String> gaps = new LinkedHashSet<>();

        private ResolvedSummaryGraph(String fatalRegion,
                                     String fatalInstance,
                                     Set<String> boundedRegions) {
            this.fatalRegion = firstNonBlank(fatalRegion);
            this.fatalInstance = firstNonBlank(fatalInstance);
            this.boundedRegions = new LinkedHashSet<>(boundedRegions);
            this.relevantRegions.add(this.fatalRegion);
        }

        private void addEdge(ResolvedEdge edge) {
            if (selectedEdgeIds.add(edge.identity())) {
                selectedEdges.add(edge);
            }
        }

        private boolean admitRegionSummary(ProducerKey key,
                                           JsonObject summary) {
            RegionSummarySelection selected = selectedRegionSummaries.get(
                    key.regionId);
            if (selected == null) {
                selectedRegionSummaries.put(key.regionId,
                        new RegionSummarySelection(key, summary));
                return true;
            }
            if (!selected.instanceId.equals(key.instanceId)) {
                addMissingPort(key.regionId, key.outputPort);
                gaps.add("ConflictingProducerRegionInstance:" + key
                        + ":selected=" + selected.instanceId);
                return false;
            }
            if (!sameSummary(selected.summary, summary)) {
                addMissingPort(key.regionId, key.outputPort);
                gaps.add("ConflictingProducerSummarySelection:" + key);
                return false;
            }
            selected.demandedOutputs.add(key.outputPort);
            return true;
        }

        private String expansionIdentity(ProducerKey key,
                                         JsonObject summary) {
            return key.regionId + "@" + key.instanceId + ":"
                    + firstNonBlank(string(summary, "summaryId"),
                    string(summary, "cacheKey"), GSON.toJson(summary));
        }

        private void addDirectBindingIfPresent(ProducerKey source,
                                               String targetRegion,
                                               String targetInstance,
                                               String targetInput) {
            JsonObject summary = selectedSummaries.get(source);
            if (summary == null) return;
            List<JsonObject> matches = new ArrayList<>();
            Set<String> seen = new LinkedHashSet<>();
            for (JsonElement element : edgeBindings(summary)) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if (!source.instanceId.equals(bindingSourceInstance(binding))
                        || !source.outputPort.equals(
                        bindingSourceOutput(binding))
                        || !trustedRuntimeReadFrom(binding)
                        || !bindingTargets(binding, targetRegion,
                        targetInstance, targetInput)) {
                    continue;
                }
                if (seen.add(GSON.toJson(binding))) matches.add(binding);
            }
            if (matches.size() == 1) {
                addEdge(new ResolvedEdge(source, summary, targetRegion,
                        targetInstance, targetInput, matches.get(0), false));
            } else if (matches.size() > 1) {
                gaps.add("AmbiguousDirectEdgeBinding:" + source + "->"
                        + targetRegion + "@" + targetInstance + ":"
                        + targetInput);
            }
        }

        private void addMissingPort(String region, String port) {
            Set<String> ports = missingPortsByRegion.get(region);
            if (ports == null) {
                ports = new LinkedHashSet<>();
                missingPortsByRegion.put(region, ports);
            }
            if (!port.isEmpty()) ports.add(port);
        }

        private Set<String> missingPorts(String region,
                                         JsonObject context) {
            Set<String> result = new LinkedHashSet<>(
                    relevantPorts(region, context));
            Set<String> recursive = missingPortsByRegion.get(region);
            if (recursive != null) result.addAll(recursive);
            return result;
        }

        private void finishBounds() {
            for (String region : boundedRegions) {
                if (!reachedBoundedRegions.contains(region)) {
                    unreachableBoundedRegions.add(region);
                    gaps.add("UnreachableBoundedRegion:" + region);
                }
            }
        }

        private void rejectRepeatedRegionInstances() {
            for (Map.Entry<ProducerKey, JsonObject> entry
                    : selectedSummaries.entrySet()) {
                RegionSummarySelection selected = selectedRegionSummaries.get(
                        entry.getKey().regionId);
                if (selected == null
                        || !selected.instanceId.equals(
                        entry.getKey().instanceId)
                        || !sameSummary(selected.summary,
                        entry.getValue())) {
                    gaps.add("ConflictingProducerRegionPortNamespace:"
                            + entry.getKey());
                }
            }
        }

        private List<String> producerKeyStrings() {
            List<String> result = new ArrayList<>();
            for (ProducerKey key : selectedSummaries.keySet()) {
                result.add(key.toString());
            }
            return result;
        }

        private int recursiveEdgeCount() {
            int result = 0;
            for (ResolvedEdge edge : selectedEdges) {
                if (edge.recursive) result++;
            }
            return result;
        }
    }

    private static ContextScope boundedContext(JsonObject source,
                                               Set<String> boundedRegions) {
        JsonObject result = source.deepCopy();
        if (boundedRegions.isEmpty()) {
            return new ContextScope(result, 0, 0, 0);
        }
        int excludedRelations = 0;
        int excludedAlternatives = 0;
        int includedRelations = 0;
        for (String field : new String[]{"equalityRelations",
                "versionedStateMerges"}) {
            JsonArray selected = new JsonArray();
            for (JsonElement element : array(source, field)) {
                if (!element.isJsonObject()) {
                    excludedRelations++;
                    continue;
                }
                JsonObject relation = element.getAsJsonObject();
                if (boundedRegions.contains(regionOf(string(relation,
                        "fromEndpoint")))) {
                    selected.add(relation.deepCopy());
                    includedRelations++;
                } else {
                    excludedRelations++;
                }
            }
            result.add(field, selected);
        }

        JsonArray direct = array(result, "versionedStateMerges");
        JsonArray selectedGroups = new JsonArray();
        for (JsonElement element : array(source,
                "alternativeWriterGroups")) {
            if (!element.isJsonObject()) {
                excludedRelations++;
                continue;
            }
            JsonObject group = element.getAsJsonObject();
            JsonArray selected = new JsonArray();
            JsonArray alternatives = array(group, "alternatives");
            for (JsonElement alternative : alternatives) {
                if (!alternative.isJsonObject()) {
                    excludedAlternatives++;
                    continue;
                }
                JsonObject relation = alternative.getAsJsonObject();
                if (boundedRegions.contains(regionOf(string(relation,
                        "fromEndpoint")))) {
                    selected.add(relation.deepCopy());
                } else {
                    excludedAlternatives++;
                }
            }
            if (selected.size() == 1) {
                JsonObject relation = selected.get(0).getAsJsonObject();
                if (string(relation, "toEndpoint").isEmpty()) {
                    relation.addProperty("toEndpoint", firstNonBlank(
                            string(group, "downstreamEndpoint"),
                            string(group, "consumerEndpoint")));
                }
                direct.add(relation);
                includedRelations++;
            } else if (selected.size() > 1) {
                JsonObject copy = group.deepCopy();
                copy.add("alternatives", selected);
                selectedGroups.add(copy);
                includedRelations += selected.size();
            } else {
                excludedRelations++;
            }
        }
        result.add("versionedStateMerges", direct);
        result.add("alternativeWriterGroups", selectedGroups);
        return new ContextScope(result, excludedRelations,
                excludedAlternatives, includedRelations);
    }

    private static final class ContextScope {
        private final JsonObject context;
        private final int excludedRelations;
        private final int excludedAlternatives;
        private final int includedRelations;

        private ContextScope(JsonObject context, int excludedRelations,
                             int excludedAlternatives,
                             int includedRelations) {
            this.context = context;
            this.excludedRelations = excludedRelations;
            this.excludedAlternatives = excludedAlternatives;
            this.includedRelations = includedRelations;
        }
    }

    private static Set<String> relevantRegions(JsonObject fatal,
                                               JsonObject context,
                                               List<JsonObject> summaries,
                                               Set<String> boundedRegions) {
        Set<String> result = new LinkedHashSet<>();
        String fatalRegion = string(fatal, "regionId");
        result.add(fatalRegion);
        boolean changed = true;
        while (changed) {
            changed = false;
            for (String field : new String[]{"equalityRelations",
                    "versionedStateMerges"}) {
                for (JsonElement element : array(context, field)) {
                    if (!element.isJsonObject()) continue;
                    JsonObject relation = element.getAsJsonObject();
                    String downstream = regionOf(string(relation,
                            "toEndpoint"));
                    String upstream = regionOf(string(relation,
                            "fromEndpoint"));
                    if (result.contains(downstream) && !upstream.isEmpty()) {
                        changed |= result.add(upstream);
                    }
                }
            }
            for (JsonElement element : array(context,
                    "alternativeWriterGroups")) {
                if (!element.isJsonObject()) continue;
                JsonObject group = element.getAsJsonObject();
                String downstream = regionOf(firstNonBlank(
                        string(group, "downstreamEndpoint"),
                        string(group, "consumerEndpoint"),
                        alternativeConsumer(group)));
                if (!result.contains(downstream)) continue;
                for (JsonElement alternative : array(group,
                        "alternatives")) {
                    if (!alternative.isJsonObject()) continue;
                    String upstream = regionOf(string(
                            alternative.getAsJsonObject(), "fromEndpoint"));
                    if (!upstream.isEmpty()) changed |= result.add(upstream);
                }
            }
        }
        String fatalInstance = string(context, "regionInstanceId");
        for (JsonObject summary : summaries) {
            if (!bool(summary, "valid", true)) {
                continue;
            }
            if (!boundedRegions.isEmpty()
                    && !boundedRegions.contains(string(summary,
                    "regionId"))) {
                continue;
            }
            for (JsonElement element : edgeBindings(summary)) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject binding = element.getAsJsonObject();
                if (edgeBindingTargets(binding, fatalRegion,
                        fatalInstance)
                        && edgeBindingSourceMatches(binding, summary)) {
                    result.add(string(summary, "regionId"));
                }
            }
        }
        result.remove("");
        return result;
    }

    private static boolean edgeBindingTargets(JsonObject binding,
                                              String fatalRegion,
                                              String fatalInstance) {
        String downstreamRegion = firstNonBlank(string(binding, "toRegion"),
                regionOf(firstNonBlank(string(binding, "toInputPort"),
                        string(binding, "consumerInputPort"))));
        if (!fatalRegion.equals(downstreamRegion)) {
            return false;
        }
        String downstreamInstance = firstNonBlank(string(binding,
                "toRegionInstance"), string(binding,
                "consumerRegionInstance"));
        return !fatalInstance.isEmpty() && !downstreamInstance.isEmpty()
                && fatalInstance.equals(downstreamInstance);
    }

    private static boolean edgeBindingSourceMatches(JsonObject binding,
                                                    JsonObject summary) {
        String sourceInstance = firstNonBlank(string(binding,
                "fromRegionInstance"), string(binding,
                "producerRegionInstance"));
        if (sourceInstance.isEmpty()) return false;
        String direct = string(summary, "regionInstanceId");
        if (!direct.isEmpty()) return sourceInstance.equals(direct);
        for (JsonElement element : array(summary,
                "sourceRegionInstanceIds")) {
            if (element.isJsonPrimitive()
                    && sourceInstance.equals(element.getAsString())) {
                return true;
            }
        }
        return false;
    }

    private static Set<String> endpointMembers(JsonObject context) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : array(context, "equalityClasses")) {
            if (!element.isJsonObject()) continue;
            for (JsonElement member : array(element.getAsJsonObject(),
                    "members")) {
                if (member.isJsonPrimitive()) result.add(member.getAsString());
            }
        }
        for (String field : new String[]{"equalityRelations",
                "versionedStateMerges"}) {
            for (JsonElement element : array(context, field)) {
                if (!element.isJsonObject()) continue;
                JsonObject relation = element.getAsJsonObject();
                result.add(string(relation, "fromEndpoint"));
                result.add(string(relation, "toEndpoint"));
            }
        }
        for (JsonElement element : array(context,
                "alternativeWriterGroups")) {
            if (!element.isJsonObject()) continue;
            JsonObject group = element.getAsJsonObject();
            result.add(firstNonBlank(string(group, "downstreamEndpoint"),
                    string(group, "consumerEndpoint")));
            for (JsonElement alternative : array(group, "alternatives")) {
                if (!alternative.isJsonObject()) continue;
                JsonObject relation = alternative.getAsJsonObject();
                result.add(string(relation, "fromEndpoint"));
                result.add(string(relation, "toEndpoint"));
            }
        }
        result.remove("");
        return result;
    }

    private static Set<String> relevantPorts(String region,
                                             JsonObject context) {
        Set<String> result = new LinkedHashSet<>();
        for (String member : endpointMembers(context)) {
            if (region.equals(regionOf(member))) result.add(member);
        }
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

    private static String alternativeConsumer(JsonObject group) {
        JsonArray alternatives = array(group, "alternatives");
        return alternatives.size() > 0 && alternatives.get(0).isJsonObject()
                ? string(alternatives.get(0).getAsJsonObject(), "toEndpoint")
                : "";
    }

    private static String and(List<String> terms) {
        List<String> filtered = new ArrayList<>();
        for (String term : terms) {
            if (term != null && !term.trim().isEmpty()) filtered.add(term);
        }
        if (filtered.isEmpty()) return "true";
        if (filtered.size() == 1) return filtered.get(0);
        StringBuilder result = new StringBuilder("(and");
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
        private final Map<String, Sort> rawSorts = new LinkedHashMap<>();
        private final Map<String, String> rawNames = new LinkedHashMap<>();
        private final Map<String, Sort> portSortOverrides =
                new LinkedHashMap<>();
        private final Map<String, Sort> declaredPortSorts =
                new LinkedHashMap<>();
        private final Map<String, String> symbolToPort = new LinkedHashMap<>();
        private final Set<String> boundPorts = new LinkedHashSet<>();
        private final Set<String> mentionedPorts = new LinkedHashSet<>();
        private final Set<String> unsupported = new LinkedHashSet<>();
        private final Set<String> incompleteSummaries = new LinkedHashSet<>();
        private final Set<String> unboundPorts = new LinkedHashSet<>();
        private final Set<String> canonicalPortTermBindings =
                new LinkedHashSet<>();
        private final Set<String> javaIntRangeAssertions =
                new LinkedHashSet<>();
        private final Map<String, EngineArrayInputBridge>
                engineArrayInputBridges = new LinkedHashMap<>();
        private final Map<String, String> canonicalFieldAccessors =
                new LinkedHashMap<>();
        private final Map<String, Sort> canonicalFieldAccessorSorts =
                new LinkedHashMap<>();
        private final Map<String, Map<String, String>>
                vmIntrinsicPlaceholderBindingsByScope =
                new LinkedHashMap<>();
        private final List<String[]> portEqualities = new ArrayList<>();
        private final List<JsonObject> relationshipCandidates =
                new ArrayList<>();
        private final Set<String> relationshipIds = new LinkedHashSet<>();
        private final JsonArray caseProjectionCatalog = new JsonArray();
        private boolean caseProjectionCatalogComplete = true;
        private int unknownCounter;
        private int assertionCount;
        private int guardedRegionRelationCount;
        private int guardedPathCaseCount;
        private int heapObservationCount;
        private int heapObservationFieldBindingCount;
        private int finiteMapSnapshotCount;
        private final JsonArray runtimeBoundedMapSnapshots = new JsonArray();
        private String currentGuard = "";
        private String currentSymbolScope = "global";
        private CaseProjectionCapture currentCaseProjection;

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
                    + " (VReal (valueReal Real))"
                    + " (VBool (valueBool Bool))"
                    + " (VRef (valueRef Ref))"
                    + " (VString (valueString String))"
                    + " (VMapBoolean (valueMapBoolean Bool))"
                    + " (VMapByte (valueMapByte Int))"
                    + " (VMapChar (valueMapChar Int))"
                    + " (VMapShort (valueMapShort Int))"
                    + " (VMapInteger (valueMapInteger Int))"
                    + " (VMapLong (valueMapLong Int))"
                    + " (VMapString (valueMapString String)))))");
            preamble.add("(declare-datatypes () ((FiniteArrayValue"
                    + " (mkFiniteArrayValue"
                    + " (finite_array_length Int)"
                    + " (finite_array_elements (Array Int Value))))))");
            preamble.add("(define-fun finite_array_select"
                    + " ((a FiniteArrayValue) (i Int)) Value"
                    + " (select (finite_array_elements a) i))");
            preamble.add("(declare-datatypes () ((MapState"
                    + " (mkMapState"
                    + " (map_members (Array Value Bool))"
                    + " (map_values (Array Value Value))))))");
            preamble.add("(declare-const nullRef Ref)");
            preamble.add("(define-fun map_has ((s MapState) (k Value)) Bool"
                    + " (select (map_members s) k))");
            preamble.add("(define-fun map_select ((s MapState) (k Value)) Value"
                    + " (select (map_values s) k))");
            preamble.add("(define-fun map_put ((s MapState) (k Value)"
                    + " (v Value)) MapState (mkMapState"
                    + " (store (map_members s) k true)"
                    + " (store (map_values s) k v)))");
            preamble.add("(define-fun map_remove ((s MapState) (k Value))"
                    + " MapState (mkMapState"
                    + " (store (map_members s) k false)"
                    + " (map_values s)))");
            preamble.add("(declare-fun map_state_of (Ref) MapState)");
            preamble.add("(declare-const emptyMapState MapState)");
            preamble.add("(assert (= (map_members emptyMapState)"
                    + " ((as const (Array Value Bool)) false)))");
            preamble.add("(assert (= (map_values emptyMapState)"
                    + " ((as const (Array Value Value)) (VRef nullRef))))");
            preamble.add("(define-fun map_clear ((s MapState)) MapState"
                    + " emptyMapState)");
            preamble.add("(define-fun map_put_all ((dst MapState)"
                    + " (src MapState)) MapState (mkMapState"
                    + " (lambda ((q Value)) (or"
                    + " (select (map_members dst) q)"
                    + " (select (map_members src) q)))"
                    + " (lambda ((q Value)) (ite"
                    + " (select (map_members src) q)"
                    + " (select (map_values src) q)"
                    + " (select (map_values dst) q)))))");
            // SMT-LIB's str.from_int is defined only for non-negative
            // integers.  Java's decimal Integer.toString additionally emits
            // a leading '-' for negative values.  Keeping this definition in
            // the common emitter lets the codec proof below remain ordinary,
            // solver-visible string semantics instead of an unconstrained UF.
            preamble.add("(define-fun java_int_to_string ((i Int)) String"
                    + " (ite (< i 0)"
                    + " (str.++ \"-\" (str.from_int (- i)))"
                    + " (str.from_int i)))");
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
            if ("_array_expr".equals(type)) {
                return arrayConstraint(object, origin);
            }
            Term term = term(expression, null);
            if (term.sort == Sort.BOOL) return term.text;
            return unknownConstraint(origin + ": non-boolean " + type,
                    expression);
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
                    Term result = canonicalPortTerm(inputPort, Sort.INT);
                    recordCaseSymbol(identity, result,
                            "VM_INTRINSIC_PLACEHOLDER_CANONICAL_PORT",
                            inputPort);
                    return result;
                }
                unsupported.add("PlaceholderExpression:" + function
                        + "#" + count);
                String name = scopedName("placeholder",
                        function + "_" + count);
                declare(name, Sort.INT);
                return new Term(name, Sort.INT);
            }
            if ("TypeCastExpression".equals(type)) {
                return term(object.get("_exp"), sortOfJava(
                        string(object, "_java_type")));
            }
            if ("MethodExpression".equals(type)) {
                return methodTerm(object);
            }
            unsupported.add(type.isEmpty() ? "MISSING_TYPE" : type);
            String name = scopedFreshName("unknown_term");
            Sort sort = expected == null ? Sort.VALUE : expected;
            declare(name, sort);
            return new Term(name, sort);
        }

        private Term symbol(JsonObject expression, Sort expected) {
            String raw = string(expression, "_exp");
            if ("N".equals(raw)) {
                Term result = new Term("nullRef", Sort.REF);
                recordCaseSymbol(raw, result, "SPECIAL_CONSTANT", "");
                return result;
            }
            if ("V".equals(raw)) {
                Term result = new Term("true", Sort.BOOL);
                recordCaseSymbol(raw, result, "SPECIAL_CONSTANT", "");
                return result;
            }

            String port = findPort(raw);
            if (!port.isEmpty()) {
                symbolToPort.put(raw, port);
                mentionedPorts.add(port);
                if (expected == Sort.MAP) {
                    promotePort(port, Sort.MAP);
                    declarePort(port, Sort.MAP);
                    boundPorts.add(port);
                    Term result = new Term(portName(port), Sort.MAP);
                    recordCaseSymbol(raw, result, "CANONICAL_MAP_PORT", port);
                    return result;
                }
                if (expected == Sort.ARRAY_VALUE) {
                    if (portSort(port) != Sort.ARRAY_VALUE) {
                        unsupported.add("ArraySymbolPortSortConflict:" + port
                                + ":" + portSort(port));
                    } else {
                        declarePort(port, Sort.ARRAY_VALUE);
                        boundPorts.add(port);
                        Term result = new Term(portName(port),
                                Sort.ARRAY_VALUE);
                        recordCaseSymbol(raw, result,
                                "CANONICAL_ARRAY_VALUE_PORT", port);
                        return result;
                    }
                }
                Port schema = ports.get(port);
                if (schema != null && portSort(port) == Sort.MAP) {
                    declarePort(port, Sort.MAP);
                    boundPorts.add(port);
                    Term result = new Term(portName(port), Sort.MAP);
                    recordCaseSymbol(raw, result, "CANONICAL_MAP_PORT", port);
                    return result;
                }
                if (schema != null && portSort(port) == Sort.ARRAY_VALUE) {
                    declarePort(port, Sort.ARRAY_VALUE);
                    boundPorts.add(port);
                    Term result = new Term(portName(port),
                            Sort.ARRAY_VALUE);
                    recordCaseSymbol(raw, result,
                            "CANONICAL_ARRAY_VALUE_PORT", port);
                    return result;
                }
            }

            Sort sort = expected == null
                    ? sortOfJava(string(expression, "_java_type")) : expected;
            if (sort == Sort.VALUE || sort == Sort.MAP) {
                sort = sortOfJava(string(expression, "_java_type"));
                if (sort == Sort.VALUE || sort == Sort.MAP) sort = Sort.REF;
            }
            if (!port.isEmpty()) {
                Term result = canonicalPortTerm(port, sort);
                recordCaseSymbol(raw, result, "CANONICAL_PORT_TERM", port);
                return result;
            }

            String scopedRaw = currentSymbolScope + "\u0000" + raw;
            String name = rawNames.get(scopedRaw);
            if (name == null) {
                name = scopedName("sym", raw);
                rawNames.put(scopedRaw, name);
                rawSorts.put(scopedRaw, sort);
                declare(name, sort);
            } else {
                Sort declaredSort = rawSorts.get(scopedRaw);
                if (declaredSort == null) {
                    unsupported.add("MissingScopedSymbolSort:" + raw);
                    declaredSort = Sort.VALUE;
                } else if (declaredSort != sort) {
                    unsupported.add("ScopedSymbolSortConflict:" + raw
                            + ":" + declaredSort + "->" + sort);
                }
                // A symbol has one SMT declaration per summary scope.  Keep
                // returning that declaration's actual sort after a conflict;
                // pretending it has the requested sort can manufacture an
                // ill-sorted equality and obscure the admission failure.
                sort = declaredSort;
            }
            Term result = new Term(name, sort);
            recordCaseSymbol(raw, result, "SCOPED_ENGINE_SYMBOL", "");
            return result;
        }

        /**
         * A canonical port is a formal relation variable, not an engine-local
         * counter.  Give each scalar view of it one global typed witness and
         * connect that witness to the Value-typed schema port unconditionally.
         */
        private Term canonicalPortTerm(String port, Sort sort) {
            String bindingKey = port + "\u0000" + sort.name();
            String name = "sym__port__" + smtName(port) + "__"
                    + sort.name().toLowerCase(Locale.ROOT);
            Term term = new Term(name, sort);
            declare(name, sort);
            if (canonicalPortTermBindings.add(bindingKey)) {
                String previousGuard = currentGuard;
                currentGuard = "";
                try {
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
         * Materializes an occurrence-specific VM symbol without the normal
         * substring-to-port lookup.  Dynamic field names intentionally retain
         * their static base port as a prefix; resolving that prefix as a scalar
         * port would collapse every map entry back into one expiry value.
         */
        private Term exactDynamicFieldTerm(JsonObject expression,
                                           String dynamicFieldSymbol,
                                           Sort sort) {
            String raw = string(expression, "_exp");
            if (!rawSymbolReferences(expression, dynamicFieldSymbol)) {
                unsupported.add("DynamicFieldExpressionMismatch:"
                        + dynamicFieldSymbol);
            }
            String scopedRaw = currentSymbolScope + "\u0000" + raw;
            String name = rawNames.get(scopedRaw);
            if (name == null) {
                name = scopedName("dynamic_field", raw);
                rawNames.put(scopedRaw, name);
                rawSorts.put(scopedRaw, sort);
                declare(name, sort);
            } else {
                Sort declaredSort = rawSorts.get(scopedRaw);
                if (declaredSort == null) {
                    unsupported.add("MissingDynamicFieldSort:" + raw);
                    declaredSort = Sort.VALUE;
                } else if (declaredSort != sort) {
                    unsupported.add("DynamicFieldSortConflict:" + raw
                            + ":" + declaredSort + "->" + sort);
                }
                sort = declaredSort;
            }
            Term result = new Term(name, sort);
            recordCaseSymbol(raw, result, "SCOPED_DYNAMIC_FIELD", "");
            return result;
        }

        /** Declares a schema-v3 field symbol authorized by the runtime's
         * exact symbolizeField evidence.  No VM expression is synthesized:
         * this term may be absent from the path condition by design. */
        private Term authorizedRuntimeDynamicFieldTerm(
                JsonObject binding, Sort sort) {
            String raw = string(binding, "dynamicFieldSymbol");
            if (raw.isEmpty()
                    || !"EXACT_SYMBOLIZE_FIELD_OBSERVATION_AND_"
                    .concat("SYMBOLIZED_INPUT").equals(string(binding,
                            "runtimeSymbolizationAuthority"))
                    || !"UNIQUE_ENTRYSET_KEYED_SNAPSHOT_AND_OUTPUT_"
                    .concat("IDENTITY_VALIDATION").equals(string(binding,
                            "projectionEvidenceAuthority"))) {
                unsupported.add("UnauthorizedRuntimeDynamicField:" + raw);
            }
            String scopedRaw = currentSymbolScope + "\u0000" + raw;
            String name = rawNames.get(scopedRaw);
            if (name == null) {
                name = scopedName("runtime_dynamic_field", raw);
                rawNames.put(scopedRaw, name);
                rawSorts.put(scopedRaw, sort);
                declare(name, sort);
            } else {
                Sort declaredSort = rawSorts.get(scopedRaw);
                if (declaredSort == null || declaredSort != sort) {
                    unsupported.add("RuntimeDynamicFieldSortConflict:" + raw);
                    sort = declaredSort == null ? Sort.VALUE : declaredSort;
                }
            }
            Term result = new Term(name, sort);
            recordCaseSymbol(raw, result,
                    "AUTHORIZED_RUNTIME_DYNAMIC_FIELD", "");
            return result;
        }

        private void recordCaseSymbol(String raw, Term term, String kind,
                                      String canonicalPort) {
            if (currentCaseProjection != null && raw != null
                    && !raw.isEmpty() && term != null) {
                currentCaseProjection.record(raw, term, kind, canonicalPort);
            }
        }

        private static boolean rawSymbolReferences(JsonElement expression,
                                                   String dynamicSymbol) {
            if (expression == null || !expression.isJsonObject()
                    || dynamicSymbol == null || dynamicSymbol.isEmpty()) {
                return false;
            }
            JsonObject object = expression.getAsJsonObject();
            if (!("SymbolExpression".equals(string(object, "_type"))
                    || "ConSymbolExp".equals(string(object, "_type")))) {
                return false;
            }
            String raw = string(object, "_exp");
            int start = raw.indexOf(dynamicSymbol);
            while (start >= 0) {
                int end = start + dynamicSymbol.length();
                boolean left = start == 0 || !Character.isLetterOrDigit(
                        raw.charAt(start - 1));
                boolean right = end == raw.length()
                        || !Character.isLetterOrDigit(raw.charAt(end));
                if (left && right) return true;
                start = raw.indexOf(dynamicSymbol, start + 1);
            }
            return false;
        }

        private Term constant(JsonObject expression, Sort expected) {
            String raw = string(expression, "_exp");
            String javaType = string(expression, "_java_type");
            String value = constantPayload(raw);
            Sort sort = sortOfJava(javaType);
            Term result;
            if (expected == Sort.REF && ("0".equals(value)
                    || "N".equals(raw))) {
                result = new Term("nullRef", Sort.REF);
            } else if (sort == Sort.REAL) {
                result = new Term(realLiteral(value), Sort.REAL);
            } else if (sort == Sort.INT) {
                result = new Term(integerLiteral(value), Sort.INT);
            } else if (sort == Sort.STRING) {
                result = new Term(quote(value), Sort.STRING);
            } else {
                String name = "const__" + smtName(raw);
                declare(name, sort == Sort.VALUE ? Sort.REF : sort);
                result = new Term(name,
                        sort == Sort.VALUE ? Sort.REF : sort);
            }
            recordCaseSymbol(raw, result, "ENGINE_LITERAL", "");
            return result;
        }

        private Term binary(JsonObject expression) {
            String operator = string(expression, "_op");
            Term left = term(expression.get("_left"), null);
            Term right = term(expression.get("_right"), left.sort);
            if (left.sort != right.sort && right.isZero()
                    && left.sort == Sort.REF) {
                right = new Term("nullRef", Sort.REF);
            } else if (left.sort != right.sort && left.isZero()
                    && right.sort == Sort.REF) {
                left = new Term("nullRef", Sort.REF);
            }
            if (left.sort != right.sort
                    && (("==".equals(operator) || "!=".equals(operator))
                    && (isNull(left) || isNull(right)))) {
                // Java primitives are never null.  This is the one mixed-sort
                // binary relation whose semantics can be closed without an
                // ill-sorted SMT application.
                return new Term("!=".equals(operator)
                        ? "true" : "false", Sort.BOOL);
            }
            if (left.sort != right.sort) {
                unsupported.add("BinarySortConflict:" + operator + ":"
                        + left.sort + "!=" + right.sort);
                Sort resultSort = "==".equals(operator)
                        || "!=".equals(operator)
                        || !comparison(operator).isEmpty()
                        ? Sort.BOOL : left.sort;
                String unknown = scopedFreshName("binary_sort_conflict");
                declare(unknown, resultSort);
                return new Term(unknown, resultSort);
            }
            if ("==".equals(operator) || "!=".equals(operator)) {
                String equality = "(= " + left.text + " " + right.text + ")";
                return new Term("!=".equals(operator)
                        ? "(not " + equality + ")" : equality, Sort.BOOL);
            }
            String smt = comparison(operator);
            if (!smt.isEmpty()) {
                return new Term("(" + smt + " " + left.text + " "
                        + right.text + ")", Sort.BOOL);
            }
            smt = arithmetic(operator);
            if (!smt.isEmpty()) {
                return new Term("(" + smt + " " + left.text + " "
                        + right.text + ")", left.sort);
            }
            unsupported.add("BinaryOperator:" + operator);
            String name = scopedFreshName("unknown_binary");
            declare(name, Sort.BOOL);
            return new Term(name, Sort.BOOL);
        }

        /**
         * Emits only the two string value operations needed by the generic
         * Java decimal codec.  In particular, Integer.toString is not modeled
         * as an uninterpreted function: {@code java_int_to_string} is defined
         * in the preamble using SMT string primitives and each source is
         * constrained to the Java int domain.
         */
        private Term stringOperation(JsonObject expression) {
            String operation = string(expression, "_name");
            if (bool(expression, "_is_not", false)) {
                return codecGap("OpStrExpression." + operation,
                        "NEGATED_VALUE_OPERATION", Sort.STRING);
            }
            JsonArray params = array(expression, "_param_list");
            if ("concat".equals(operation)) {
                if (params.size() == 0) {
                    return codecGap("OpStrExpression.concat", "EMPTY",
                            Sort.STRING);
                }
                List<Term> strings = new ArrayList<>();
                for (JsonElement parameter : params) {
                    Term value = term(parameter, null);
                    if (value.sort != Sort.STRING) {
                        return codecGap("OpStrExpression.concat",
                                "NON_STRING_PARAMETER", Sort.STRING);
                    }
                    strings.add(value);
                }
                if (strings.size() == 1) return strings.get(0);
                StringBuilder result = new StringBuilder("(str.++");
                for (Term value : strings) {
                    result.append(' ').append(value.text);
                }
                return new Term(result.append(')').toString(), Sort.STRING);
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

            List<JsonElement> parts = new ArrayList<>();
            if (!flattenConcat(params.get(0), parts) || parts.size() < 3) {
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
            return new Term("(java_int_to_string " + integer.text + ")",
                    Sort.STRING);
        }

        private void assertJavaIntRange(Term integer) {
            String key = currentGuard + "\u0000" + integer.text;
            if (!javaIntRangeAssertions.add(key)) return;
            assertNamed("java_int_range_" + javaIntRangeAssertions.size(),
                    "(and (<= (- 2147483648) " + integer.text + ")"
                            + " (<= " + integer.text + " 2147483647))");
        }

        private Term codecGap(String operation, String gap, Sort sort) {
            unsupported.add("MODEL_SEMANTICS_MISSING:" + operation + ":"
                    + gap);
            String name = scopedFreshName("unknown_codec_"
                    + smtName(operation));
            declare(name, sort);
            return new Term(name, sort);
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
            if (isJavaParseInt(name)) {
                Term decoded = parseIntTerm(expression);
                Term result = term(expression.get("_res_exp"), Sort.INT);
                return "(= " + result.text + " " + decoded.text + ")";
            }
            if (isJavaSplitElement(name)) {
                Term prefix = splitElementTerm(expression);
                Term result = term(expression.get("_res_exp"), Sort.STRING);
                return "(= " + result.text + " " + prefix.text + ")";
            }
            if (isMapGet(name)) {
                JsonArray params = array(expression, "_param_list");
                if (params.size() < 2) {
                    return unknownConstraint(origin + ": malformed Map.get",
                            expression);
                }
                Term receiver = mapState(params.get(0));
                Term key = mapKeyTerm(params.get(1), origin + "_map_get");
                if (key == null) {
                    return unknownConstraint(origin
                            + ": unsupported Java Map.get key", expression);
                }
                Term result = term(expression.get("_res_exp"), Sort.REF);
                Term boxedResult = asValue(result);
                return "(= " + boxedResult.text + " (ite (map_has "
                        + receiver.text + " " + key.text + ") (map_select "
                        + receiver.text + " " + key.text
                        + ") (VRef nullRef)))";
            }
            JsonArray params = array(expression, "_param_list");
            List<Term> arguments = new ArrayList<>();
            for (JsonElement parameter : params) {
                arguments.add(term(parameter, null));
            }
            Term result = term(expression.get("_res_exp"), null);
            String function = "uf__" + smtName(name);
            declareFunction(function, arguments, result.sort);
            StringBuilder call = new StringBuilder("(").append(function);
            for (Term argument : arguments) {
                call.append(' ').append(argument.text);
            }
            call.append(')');
            return "(= " + result.text + " " + call + ")";
        }

        private String arrayConstraint(JsonObject expression, String origin) {
            String rawArray = string(expression, "_arr_str");
            if (expression.has("_is_load")
                    && !bool(expression, "_is_load", false)) {
                unsupported.add("EngineArrayStoreUnsupported:"
                        + firstNonBlank(rawArray, "<unnamed>") + ":"
                        + origin);
                return unknownConstraint(origin
                        + ": engine array store unsupported", expression);
            }
            if (!bool(expression, "_is_load", false)
                    || !hasExpression(expression, "_index_exp")
                    || !hasExpression(expression, "_value_exp")) {
                return unknownConstraint(origin + ": malformed array event",
                        expression);
            }
            if (rawArray.isEmpty()) {
                return unknownConstraint(origin + ": unnamed array event",
                        expression);
            }
            EngineArrayInputBridge bridge = engineArrayInputBridges.get(
                    currentSymbolScope + "\u0000" + rawArray);
            if (bridge == null) {
                unsupported.add("EngineArrayInputBridgeMissing:" + rawArray
                        + ":" + currentSymbolScope);
                return unknownConstraint(origin
                        + ": engine array input bridge missing", expression);
            }
            String array = bridge.arrayTerm;
            recordCaseSymbol(rawArray, new Term(array, Sort.ARRAY),
                    "CANONICAL_ARRAY_INPUT_ELEMENTS", bridge.inputPort);
            Term index = term(expression.get("_index_exp"), Sort.INT);
            Term value = asValue(term(expression.get("_value_exp"), null));
            return "(and (<= 0 " + index.text + ") (< " + index.text
                    + " (finite_array_length " + portName(bridge.inputPort)
                    + ")) (= " + value.text + " (select " + array + " "
                    + index.text + ")))";
        }

        private void registerEngineArrayInputBindings(
                JsonObject container, String origin) {
            JsonElement declared = container.get(
                    "engineArrayInputBindings");
            if (declared == null || declared.isJsonNull()) return;
            if (!declared.isJsonArray()) {
                unsupported.add("MalformedEngineArrayInputBindings:"
                        + origin);
                return;
            }
            String expectedActivation = firstNonBlank(string(container,
                    "activationId"), string(container,
                    "sourceActivationId"));
            Map<String, String> portToId = new LinkedHashMap<>();
            Map<String, String> idToPort = new LinkedHashMap<>();
            Map<String, Long> idToToken = new LinkedHashMap<>();
            Set<String> rowIds = new LinkedHashSet<>();
            JsonArray rows = declared.getAsJsonArray();
            for (int ordinal = 0; ordinal < rows.size(); ordinal++) {
                if (!rows.get(ordinal).isJsonObject()) {
                    unsupported.add("MalformedEngineArrayInputBinding:"
                            + origin + ":" + ordinal);
                    continue;
                }
                JsonObject row = rows.get(ordinal).getAsJsonObject();
                List<String> issues = new ArrayList<>();
                String port = string(row, "inputPort");
                String cell = string(row, "inputCell");
                String javaType = string(row, "inputJavaType");
                String descriptor = string(row,
                        "inputJavaTypeDescriptor");
                String arrayId = string(row, "engineArrayId");
                long token = longInteger(row, "arrayObjectToken", 0L);
                String sourceActivation = string(row,
                        "sourceActivationId");
                if (integer(row, "schemaVersion", -1) != 1) {
                    issues.add("SCHEMA_VERSION_UNSUPPORTED");
                }
                if (!"ENGINE_ARRAY_TO_INPUT_PORT".equals(
                        string(row, "kind"))) {
                    issues.add("KIND_INVALID");
                }
                if (port.isEmpty() || cell.isEmpty() || javaType.isEmpty()
                        || descriptor.isEmpty() || arrayId.isEmpty()) {
                    issues.add("REQUIRED_IDENTITY_FIELD_MISSING");
                }
                if (!descriptor.equals(javaTypeDescriptor(descriptor))
                        || !descriptor.startsWith("[")
                        || !descriptor.equals(javaTypeDescriptor(javaType))) {
                    issues.add("INPUT_ARRAY_DESCRIPTOR_INVALID");
                }
                if (!port.equals(string(row, "symbolizationPrefix"))
                        || !"DIRECT_ARRAY_VALUE_WITH_CANONICAL_INPUT_PREFIX"
                        .equals(string(row, "symbolizationMode"))) {
                    issues.add("ARRAY_SYMBOLIZATION_PREFIX_OR_MODE_INVALID");
                }
                Port schema = ports.get(port);
                if (schema == null || !schema.input
                        || schema.sort != Sort.ARRAY_VALUE
                        || !cell.equals(schema.cell)
                        || !descriptor.equals(javaTypeDescriptor(
                        schema.javaType))) {
                    issues.add("CANONICAL_INPUT_PORT_SCHEMA_MISMATCH");
                }
                if (!expectedActivation.isEmpty()
                        && !expectedActivation.equals(sourceActivation)) {
                    issues.add("SOURCE_ACTIVATION_MISMATCH");
                }
                if (sourceActivation.isEmpty()
                        || !sourceActivation.equals(string(row,
                        "objectTokenScope"))
                        || token <= 0L
                        || longInteger(row,
                        "symbolizationArrayObjectToken", 0L) != token
                        || row.get("sameArrayObjectTokenVerified") == null
                        || !row.get("sameArrayObjectTokenVerified")
                        .isJsonPrimitive()
                        || !row.get("sameArrayObjectTokenVerified")
                        .getAsJsonPrimitive().isBoolean()
                        || !row.get("sameArrayObjectTokenVerified")
                        .getAsBoolean()
                        || !"SAME_JAVA_REFERENCE_PASSED_TO_SYMBOLIZE_AND_"
                        .concat("EXPRESSION_CAPTURE").equals(string(row,
                                "symbolizationIdentityAuthority"))
                        || !"ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN"
                        .equals(string(row, "objectTokenAuthority"))) {
                    issues.add("ARRAY_OBJECT_IDENTITY_INVALID");
                }
                if (!"VM_ACTIVE_SYM_ARRAY_ID_V1".equals(string(row,
                        "engineArrayIdAuthority"))) {
                    issues.add("ENGINE_ARRAY_ID_AUTHORITY_INVALID");
                }
                JsonElement complete = row.get("complete");
                if (!"SAME_LIVE_ARRAY_AFTER_EXACT_INPUT_ACTION_"
                        .concat("SYMBOLIZATION").equals(string(row,
                                "captureAuthority"))
                        || complete == null || !complete.isJsonPrimitive()
                        || !complete.getAsJsonPrimitive().isBoolean()
                        || !complete.getAsBoolean()) {
                    issues.add("CAPTURE_AUTHORITY_OR_COMPLETENESS_INVALID");
                }
                validateEngineArrayValueExpression(row, descriptor,
                        arrayId, issues);

                if (!rowIds.add(arrayId)) {
                    issues.add("ENGINE_ARRAY_ID_DUPLICATE");
                }
                String oldId = portToId.put(port, arrayId);
                if (oldId != null && !oldId.equals(arrayId)) {
                    issues.add("INPUT_PORT_TO_ARRAY_ID_NOT_FUNCTIONAL");
                }
                String oldPort = idToPort.put(arrayId, port);
                if (oldPort != null && !oldPort.equals(port)) {
                    issues.add("ARRAY_ID_TO_INPUT_PORT_NOT_FUNCTIONAL");
                }
                Long oldToken = idToToken.put(arrayId, token);
                if (oldToken != null && oldToken.longValue() != token) {
                    issues.add("ARRAY_ID_TO_OBJECT_TOKEN_NOT_FUNCTIONAL");
                }
                String bridgeKey = currentSymbolScope + "\u0000" + arrayId;
                if (engineArrayInputBridges.containsKey(bridgeKey)) {
                    issues.add("SCOPED_ARRAY_ID_DUPLICATE");
                }
                if (!issues.isEmpty()) {
                    for (String issue : issues) {
                        unsupported.add("EngineArrayInputBinding:" + origin
                                + ":" + ordinal + ":" + issue);
                    }
                    continue;
                }

                declarePort(port, Sort.ARRAY_VALUE);
                mentionedPorts.add(port);
                boundPorts.add(port);
                String arrayTerm = scopedName("array", arrayId);
                declare(arrayTerm, Sort.ARRAY);
                EngineArrayInputBridge bridge =
                        new EngineArrayInputBridge(arrayId, arrayTerm, port,
                                token, integer(object(row,
                                "arrayValueExpression"),
                                "_concrete_length", -1));
                engineArrayInputBridges.put(bridgeKey, bridge);
                recordCaseSymbol(arrayId, new Term(arrayTerm, Sort.ARRAY),
                        "CANONICAL_ARRAY_INPUT_ELEMENTS", port);
                String previousGuard = currentGuard;
                try {
                    // The VM bridge is execution identity, not one branch's
                    // semantic consequence.  It therefore remains active
                    // independently of a guarded merge selector.
                    currentGuard = "";
                    assertNamed("engine_array_input_bridge_"
                                    + scopeToken(currentSymbolScope) + "_"
                                    + arrayId,
                            "(= " + arrayTerm
                                    + " (finite_array_elements "
                                    + portName(port) + "))");
                    assertNamed("engine_array_input_length_"
                                    + scopeToken(currentSymbolScope) + "_"
                                    + arrayId,
                            "(= (finite_array_length " + portName(port)
                                    + ") " + bridge.concreteLength + ")");
                } finally {
                    currentGuard = previousGuard;
                }
            }
        }

        private void registerVmIntrinsicPlaceholderBindings(
                JsonObject container, String origin) {
            JsonElement declared = container.get(
                    "vmIntrinsicPlaceholderBindings");
            JsonElement admissionElement = container.get(
                    "vmIntrinsicPlaceholderBindingAdmission");
            if ((declared == null || declared.isJsonNull())
                    && (admissionElement == null
                    || admissionElement.isJsonNull())) {
                return;
            }
            if (declared != null && declared.isJsonArray()
                    && declared.getAsJsonArray().size() == 0
                    && (admissionElement == null
                    || admissionElement.isJsonNull())) {
                return;
            }
            List<String> issues = new ArrayList<>();
            if (declared == null || !declared.isJsonArray()) {
                issues.add("BINDING_CATALOG_MISSING_OR_MALFORMED");
            }
            if (admissionElement == null
                    || !admissionElement.isJsonObject()) {
                issues.add("BINDING_ADMISSION_MISSING_OR_MALFORMED");
            }
            if (!issues.isEmpty()) {
                addVmIntrinsicPlaceholderIssues(origin, issues);
                return;
            }

            JsonArray rows = declared.getAsJsonArray();
            JsonObject admission = admissionElement.getAsJsonObject();
            if (integer(admission, "schemaVersion", -1) != 1
                    || !"VM_INTRINSIC_PLACEHOLDER_BINDING_ADMISSION".equals(
                    string(admission, "kind"))
                    || !bool(admission, "complete", false)
                    || integer(admission, "bindingCount", -1) != rows.size()
                    || admission.get("bindings") == null
                    || !admission.get("bindings").isJsonArray()
                    || !rows.equals(admission.getAsJsonArray("bindings"))
                    || admission.get("failures") == null
                    || !admission.get("failures").isJsonArray()
                    || admission.getAsJsonArray("failures").size() != 0
                    || !"OWNER_EXACT_UNIQUE_USED_CUSTOM_JDK_PLACEHOLDER_V1"
                    .equals(string(admission, "authority"))) {
                issues.add("BINDING_ADMISSION_CERTIFICATE_INVALID");
            }

            JsonElement inputAdmissionElement = container.get(
                    "inputMaterializationAdmission");
            JsonElement requirementsElement = container.get(
                    "unforcedEnvironmentValidationRequirements");
            JsonObject inputAdmission = inputAdmissionElement != null
                    && inputAdmissionElement.isJsonObject()
                    ? inputAdmissionElement.getAsJsonObject() : null;
            JsonArray requirements = requirementsElement != null
                    && requirementsElement.isJsonArray()
                    ? requirementsElement.getAsJsonArray() : null;
            if (rows.size() > 0 && (inputAdmission == null
                    || requirements == null)) {
                issues.add("OWNER_INPUT_ADMISSION_MISSING_OR_MALFORMED");
            }
            if (inputAdmission != null
                    && (!bool(inputAdmission, "complete", false)
                    || !"STATIC_GLOBAL_SLICE_DEMAND_REFINED_BY_EXACT_"
                    .concat("TRANSFORMER_RUNTIME_PATH_PROOFS").equals(
                            string(inputAdmission, "authority"))
                    || !"EXACT_SCHEDULER_BINDING_PLUS_CUSTOM_JDK_STRUCTURED_"
                    .concat("PLACEHOLDER_EVIDENCE").equals(string(
                            inputAdmission,
                            "vmIntrinsicPlaceholderAuthority"))
                    || inputAdmission.get("failures") == null
                    || !inputAdmission.get("failures").isJsonArray()
                    || array(inputAdmission, "failures").size() != 0
                    || requirements == null
                    || !requirements.equals(array(inputAdmission,
                    "unforcedEnvironmentValidationRequirements")))) {
                issues.add("OWNER_INPUT_ADMISSION_CERTIFICATE_INVALID");
            }

            Map<String, String> validated = new LinkedHashMap<>();
            Set<String> portsSeen = new LinkedHashSet<>();
            for (int ordinal = 0; ordinal < rows.size(); ordinal++) {
                JsonElement element = rows.get(ordinal);
                if (!element.isJsonObject()) {
                    issues.add("NON_OBJECT_BINDING:" + ordinal);
                    continue;
                }
                JsonObject row = element.getAsJsonObject();
                String identity = string(row, "placeholderIdentity");
                String function = string(row, "placeholderFunction");
                int count = integer(row, "placeholderCount", -1);
                String port = string(row, "inputPort");
                String cell = string(row, "cell");
                Port schema = ports.get(port);
                boolean uniqueIdentity = !validated.containsKey(identity);
                boolean uniquePort = !portsSeen.contains(port);
                boolean valid = integer(row, "schemaVersion", -1) == 1
                        && "VM_INTRINSIC_PLACEHOLDER_PORT_BINDING".equals(
                        string(row, "kind"))
                        && count > 0
                        && identity.equals(function + "#" + count)
                        && "currentTimeMills".equals(function)
                        && "<java.lang.System: long currentTimeMillis()>"
                        .concat(".return").equals(cell)
                        && "J".equals(string(row, "javaTypeDescriptor"))
                        && "ENVIRONMENT".equals(string(row, "sourceKind"))
                        && "VM_INTRINSIC_PLACEHOLDER".equals(string(row,
                        "bindingMode"))
                        && "CUSTOM_JDK_SYMBOLIC_ND_FUNC".equals(string(row,
                        "captureAuthority"))
                        && "CUSTOM_JDK_STRUCTURED_PLACEHOLDER_EXPRESSION"
                        .equals(string(row, "evidenceAuthority"))
                        && row.has("modelControllable")
                        && !bool(row, "modelControllable", true)
                        && "UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION".equals(
                        string(row, "replayPolicy"))
                        && "UNIQUE_USED_PLACEHOLDER_IDENTITY_TO_EXACT_"
                        .concat("SLICE_INPUT").equals(string(row,
                                "ownerAuthority"))
                        && bool(row, "required", false)
                        && schema != null && schema.input
                        && schema.sort == Sort.VALUE
                        && cell.equals(schema.cell)
                        && "J".equals(javaTypeDescriptor(schema.javaType))
                        && uniqueIdentity && uniquePort
                        && inputAdmissionOwnsVmPlaceholder(inputAdmission,
                        requirements, port, identity, function, cell);
                if (!valid) {
                    issues.add("BINDING_INVALID:" + ordinal + ":"
                            + firstNonBlank(identity, port, "unnamed"));
                } else {
                    validated.put(identity, port);
                    portsSeen.add(port);
                }
            }
            if (validated.size() != rows.size()) {
                issues.add("VALIDATED_BINDING_COUNT_MISMATCH");
            }
            Set<String> admittedPorts = inputAdmission == null ? null
                    : strictStringSet(array(inputAdmission,
                    "admittedVmIntrinsicPlaceholderInputs"));
            if (rows.size() > 0 && (requirements == null
                    || requirements.size() != rows.size()
                    || admittedPorts == null
                    || !admittedPorts.equals(portsSeen))) {
                issues.add("OWNER_REQUIREMENT_OR_PORT_CATALOG_MISMATCH");
            }
            String scope = currentSymbolScope;
            if (vmIntrinsicPlaceholderBindingsByScope.containsKey(scope)) {
                issues.add("SCOPED_BINDING_CATALOG_DUPLICATE");
            }
            if (!issues.isEmpty()) {
                addVmIntrinsicPlaceholderIssues(origin, issues);
                return;
            }
            vmIntrinsicPlaceholderBindingsByScope.put(scope, validated);
        }

        private boolean inputAdmissionOwnsVmPlaceholder(
                JsonObject admission, JsonArray requirements, String port,
                String identity, String function, String cell) {
            if (admission == null || requirements == null
                    || !containsString(array(admission,
                    "globalSliceInputs"), port)
                    || !containsString(array(admission,
                    "requiredSliceInputs"), port)
                    || !containsString(array(admission,
                    "admittedVmIntrinsicPlaceholderInputs"), port)) {
                return false;
            }
            int matches = 0;
            for (JsonElement element : requirements) {
                if (!element.isJsonObject()) return false;
                JsonObject requirement = element.getAsJsonObject();
                if (!port.equals(string(requirement, "inputPort"))) {
                    continue;
                }
                matches++;
                if (!"UNFORCED_ENVIRONMENT_VALIDATION_REQUIREMENT".equals(
                        string(requirement, "kind"))
                        || !bool(requirement, "required", false)
                        || !cell.equals(string(requirement, "cell"))
                        || !"ENVIRONMENT".equals(string(requirement,
                        "sourceKind"))
                        || !"VM_INTRINSIC_PLACEHOLDER".equals(string(
                        requirement, "bindingMode"))
                        || !function.equals(string(requirement,
                        "placeholderFunction"))
                        || !"CUSTOM_JDK_SYMBOLIC_ND_FUNC".equals(string(
                        requirement, "captureAuthority"))
                        || !requirement.has("modelControllable")
                        || bool(requirement, "modelControllable", true)
                        || !"UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION"
                        .equals(string(requirement, "replayPolicy"))
                        || !"CUSTOM_JDK_STRUCTURED_PLACEHOLDER_EXPRESSION"
                        .equals(string(requirement, "evidenceAuthority"))
                        || !containsString(array(requirement,
                        "placeholderEvidenceIdentities"), identity)) {
                    return false;
                }
            }
            return matches == 1;
        }

        private Set<String> strictStringSet(JsonArray values) {
            Set<String> result = new LinkedHashSet<>();
            for (JsonElement value : values) {
                if (!value.isJsonPrimitive()
                        || !value.getAsJsonPrimitive().isString()
                        || !result.add(value.getAsString())) {
                    return null;
                }
            }
            return result;
        }

        private void addVmIntrinsicPlaceholderIssues(
                String origin, List<String> issues) {
            for (String issue : issues) {
                unsupported.add("VmIntrinsicPlaceholderBinding:" + origin
                        + ":" + issue);
            }
        }

        private void validateEngineArrayValueExpression(
                JsonObject row, String descriptor, String arrayId,
                List<String> issues) {
            JsonElement value = row.get("arrayValueExpression");
            if (value == null || !value.isJsonObject()) {
                issues.add("ARRAY_VALUE_EXPRESSION_MISSING");
                return;
            }
            JsonObject expression = value.getAsJsonObject();
            if (!"ArrayValueExpression".equals(string(expression, "_type"))
                    || integer(expression, "_schema_version", -1) != 1
                    || !"VM_EXACT_FINITE_ARRAY_VALUE_V1".equals(
                    string(expression, "_authority"))) {
                issues.add("ARRAY_VALUE_SCHEMA_OR_AUTHORITY_INVALID");
            }
            String expressionDescriptor = string(expression, "_java_type");
            String component = string(expression,
                    "_component_java_type");
            if (!descriptor.equals(expressionDescriptor)
                    || !descriptor.equals(javaTypeDescriptor(
                    expressionDescriptor))) {
                issues.add("ARRAY_VALUE_JAVA_TYPE_MISMATCH");
            }
            if (!descriptor.startsWith("[")
                    || !descriptor.substring(1).equals(component)
                    || !component.equals(javaTypeDescriptor(component))) {
                issues.add("ARRAY_VALUE_COMPONENT_TYPE_MISMATCH");
            }
            if (!arrayId.equals(string(expression, "_engine_array_id"))
                    || !"VM_ACTIVE_SYM_ARRAY_ID_V1".equals(string(
                    expression, "_engine_array_id_authority"))
                    || !string(row, "engineArrayIdAuthority").equals(
                    string(expression, "_engine_array_id_authority"))) {
                issues.add("ARRAY_VALUE_ENGINE_ID_MISMATCH");
            }
            int length = integer(expression, "_concrete_length", -1);
            JsonElement lengthExpression = expression.get("_length_exp");
            JsonElement complete = expression.get("_elements_complete");
            if (length < 0 || !validFiniteArrayLength(lengthExpression,
                    length)
                    || lengthExpression == null
                    || !lengthExpression.isJsonObject()
                    || !"ConstExpr".equals(string(
                    lengthExpression.getAsJsonObject(), "_type"))
                    || complete == null || !complete.isJsonPrimitive()
                    || !complete.getAsJsonPrimitive().isBoolean()
                    || !complete.getAsBoolean()) {
                issues.add("ARRAY_VALUE_LENGTH_OR_COMPLETENESS_INVALID");
            }
            JsonElement rawElements = expression.get("_elements");
            if (rawElements == null || !rawElements.isJsonArray()) {
                issues.add("ARRAY_VALUE_ELEMENTS_MISSING");
                return;
            }
            JsonArray elements = rawElements.getAsJsonArray();
            if (length < 0 || elements.size() != length) {
                issues.add("ARRAY_VALUE_ELEMENT_COUNT_MISMATCH");
            }
            Set<Integer> indices = new LinkedHashSet<>();
            for (int ordinal = 0; ordinal < elements.size(); ordinal++) {
                if (!elements.get(ordinal).isJsonObject()) {
                    issues.add("ARRAY_VALUE_ELEMENT_MALFORMED:" + ordinal);
                    continue;
                }
                JsonObject element = elements.get(ordinal).getAsJsonObject();
                int index = integer(element, "index", -1);
                JsonElement elementExpression = element.get("expression");
                if (index != ordinal || index < 0 || index >= length
                        || !indices.add(index)) {
                    issues.add("ARRAY_VALUE_ELEMENT_INDEX_INVALID:"
                            + ordinal);
                }
                if (elementExpression == null
                        || !elementExpression.isJsonObject()
                        || !validFiniteArrayElementProvenance(string(element,
                        "provenance"),
                        elementExpression.getAsJsonObject(), component)
                        || !finiteArrayElementTypeCompatible(
                        elementExpression.getAsJsonObject(), component)
                        || component.startsWith("[")) {
                    issues.add("ARRAY_VALUE_ELEMENT_INVALID:" + ordinal);
                }
            }
        }

        private Term methodTerm(JsonObject expression) {
            String method = string(expression, "_name");
            if (isJavaParseInt(method)) {
                return parseIntTerm(expression);
            }
            if (isJavaSplitElement(method)) {
                return splitElementTerm(expression);
            }
            JsonArray params = array(expression, "_param_list");
            List<Term> arguments = new ArrayList<>();
            for (JsonElement parameter : params) {
                arguments.add(term(parameter, null));
            }
            Term result = term(expression.get("_res_exp"), null);
            String function = "uf__" + smtName(method);
            declareFunction(function, arguments, result.sort);
            StringBuilder call = new StringBuilder("(").append(function);
            for (Term argument : arguments) {
                call.append(' ').append(argument.text);
            }
            call.append(')');
            if (result.sort == Sort.BOOL && "V".equals(string(
                    object(expression, "_res_exp"), "_exp"))) {
                return new Term(call.toString(), Sort.BOOL);
            }
            return new Term(call.toString(), result.sort);
        }

        private void regionSummary(JsonObject summary) {
            String region = string(summary, "regionId");
            String previousScope = enterSymbolScope("summary:"
                    + firstNonBlank(string(summary, "summaryId"),
                    string(summary, "cacheKey"),
                    string(summary, "activationId"), region, "selected"));
            try {
                registerEngineArrayInputBindings(summary,
                        "summary " + region);
                registerVmIntrinsicPlaceholderBindings(summary,
                        "summary " + region);
                JsonObject relation = object(summary, "regionRelation");
                if ("GUARDED_PATH_MERGE".equals(string(relation, "kind"))) {
                    guardedRegionRelation(region, relation,
                            object(summary, "requestedOutputSlice"));
                    rejectNonRegionSemantics(region, summary);
                    return;
                }
                List<String> path = new ArrayList<>();
                for (JsonElement expression : array(summary,
                        "pathCondition")) {
                    path.add(constraint(expression, "summary " + region));
                }
                if (!path.isEmpty()) assertNamed("summary_path_" + region,
                        and(path));

                JsonArray heapInitializers = array(summary,
                        "heapStateInitializers");
                JsonArray heapEffects = array(summary, "heapEffects");
                validateHeapEffectSummary(region, summary, heapInitializers,
                        heapEffects);
                finiteMapSnapshots(region, summary);
                heapObservations(region, summary);
                for (JsonElement element : heapInitializers) {
                    if (!element.isJsonObject()) continue;
                    heapInitializer(region, element.getAsJsonObject());
                }
                for (JsonElement element : heapEffects) {
                    if (!element.isJsonObject()) continue;
                    heapEffect(region, element.getAsJsonObject());
                }
                bindOutputExpressions(region, summary);
                bindContainerElementFields(region, summary,
                        object(summary, "requestedOutputSlice"));
                rejectNonRegionSemantics(region, summary);
            } finally {
                restoreSymbolScope(previousScope);
            }
        }

        private void guardedRegionRelation(String region,
                                           JsonObject relation,
                                           JsonObject requestedOutputSlice) {
            JsonArray cases = array(relation, "cases");
            if (!bool(relation, "complete", false)) {
                heapGap(region, "IncompleteGuardedPathMerge@" + region);
            }
            if (integer(relation, "caseCount", -1) != cases.size()
                    || cases.size() == 0) {
                heapGap(region, "GuardedPathCaseCountGap@" + region);
                return;
            }
            List<String> selectors = new ArrayList<>();
            Set<String> selectorSymbols = new LinkedHashSet<>();
            Set<String> rawGuardShapes = new LinkedHashSet<>();
            String previousGuard = currentGuard;
            for (int index = 0; index < cases.size(); index++) {
                // Guard construction belongs to the outer relation.  Leaving
                // case N's implication active here would bind case N+1 inputs
                // under the wrong path.
                currentGuard = previousGuard;
                if (!cases.get(index).isJsonObject()) {
                    heapGap(region, "MalformedGuardedPathCase@" + region
                            + ":" + index);
                    continue;
                }
                JsonObject item = cases.get(index).getAsJsonObject();
                JsonObject guardIr = object(item, "guard");
                if (!"PATH_CONDITION".equals(string(guardIr, "kind"))) {
                    heapGap(region, "UnsupportedRegionGuard@" + region
                            + ":" + index);
                    continue;
                }
                String caseIdentity = firstNonBlank(
                        string(item, "symbolScope"),
                        "region:" + region + "/case:"
                                + firstNonBlank(string(item, "caseId"),
                                string(item, "pathKey"),
                                String.valueOf(index)));
                CaseProjectionCapture capture = new CaseProjectionCapture(
                        region, item, caseIdentity,
                        validateCaseDynamicBindings(item));
                String rawGuardShape = GSON.toJson(array(guardIr,
                        "conditions"));
                if (!rawGuardShapes.add(rawGuardShape)) {
                    capture.gap("OVERLAPPING_IDENTICAL_CASE_GUARD");
                }
                String previousScope = enterSymbolScope(caseIdentity);
                CaseProjectionCapture previousCapture = currentCaseProjection;
                currentCaseProjection = capture;
                try {
                    registerEngineArrayInputBindings(item,
                            "region " + region + " case " + index);
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
                    capture.selector(selector, guard);
                    if (!selectorSymbols.add(selector)) {
                        capture.gap("DUPLICATE_CASE_SELECTOR_SYMBOL");
                    }
                    selectors.add(selector);
                    declare(selector, Sort.BOOL);
                    assertNamed("case_selector_definition_" + region + "_"
                                    + index,
                            "(= " + selector + " " + guard + ")");
                    currentGuard = selector;
                    JsonArray initializers = array(item,
                            "heapStateInitializers");
                    JsonArray effects = array(item, "heapEffects");
                    validateHeapEffectSummary(region, item, initializers,
                            effects);
                    finiteMapSnapshots(region, item);
                    heapObservations(region, item);
                    for (JsonElement initializer : initializers) {
                        if (initializer.isJsonObject()) heapInitializer(region,
                                initializer.getAsJsonObject());
                    }
                    for (JsonElement effect : effects) {
                        if (effect.isJsonObject()) heapEffect(region,
                                effect.getAsJsonObject());
                    }
                    bindOutputExpressions(region, item);
                    bindContainerElementFields(region, item,
                            requestedOutputSlice);
                    bindMapProjectionElementFields(region, item);
                    guardedPathCaseCount++;
                } finally {
                    currentGuard = previousGuard;
                    currentCaseProjection = previousCapture;
                    restoreSymbolScope(previousScope);
                    capture.finish();
                    caseProjectionCatalog.add(capture.toJson());
                    if (!capture.complete()) {
                        caseProjectionCatalogComplete = false;
                        for (String gap : capture.gaps) {
                            heapGap(region, "CaseProjectionCatalogGap@"
                                    + region + ":"
                                    + firstNonBlank(string(item, "caseId"),
                                    String.valueOf(index)) + ":" + gap);
                        }
                    }
                }
            }
            currentGuard = previousGuard;
            if (bool(relation, "complete", false)
                    && selectors.size() == cases.size()
                    && !selectors.isEmpty()) {
                String coverage;
                if (selectors.size() == 1) coverage = selectors.get(0);
                else {
                    StringBuilder value = new StringBuilder("(or");
                    for (String selector : selectors) value.append(' ')
                            .append(selector);
                    coverage = value.append(')').toString();
                }
                assertNamed("region_case_selector_coverage_" + region,
                        coverage);
                for (int left = 0; left < selectors.size(); left++) {
                    for (int right = left + 1; right < selectors.size();
                            right++) {
                        assertNamed("region_case_selector_exclusive_" + region
                                        + "_" + left + "_" + right,
                                "(not (and " + selectors.get(left) + " "
                                        + selectors.get(right) + "))");
                    }
                }
            } else if (bool(relation, "complete", false)) {
                caseProjectionCatalogComplete = false;
                heapGap(region, "CaseSelectorPartitionGap@" + region);
            }
            guardedRegionRelationCount++;
        }

        /**
         * The imported runtime catalog carries replay identity while the heap
         * observation carries the exact VM expression used by the path guard.
         * Composition is projectable only when those two views form a bijection;
         * accepting either one alone would permit a solver term with no exact
         * concrete entry-field target.
         */
        private CaseDynamicValidation validateCaseDynamicBindings(
                JsonObject item) {
            CaseDynamicValidation result = new CaseDynamicValidation();
            JsonElement declared = item.get("dynamicFieldBindings");
            JsonElement observationsElement = item.get("heapObservations");
            if (declared == null || !declared.isJsonArray()) {
                result.gap("MISSING_CASE_DYNAMIC_FIELD_BINDING_CATALOG");
                return result;
            }

            Map<String, JsonObject> metadataById = new LinkedHashMap<>();
            Set<String> dynamicSymbols = new LinkedHashSet<>();
            Set<String> siteOccurrences = new LinkedHashSet<>();
            Set<String> matched = new LinkedHashSet<>();
            JsonArray bindings = declared.getAsJsonArray();
            for (int index = 0; index < bindings.size(); index++) {
                JsonElement element = bindings.get(index);
                if (!element.isJsonObject()) {
                    result.gap("NON_OBJECT_DYNAMIC_BINDING:" + index);
                    continue;
                }
                JsonObject binding = element.getAsJsonObject();
                String id = string(binding, "dynamicBindingId");
                String base = string(binding, "baseInputSymbol");
                String dynamic = string(binding, "dynamicFieldSymbol");
                String site = string(binding, "materializationSiteId");
                int occurrence = integer(binding,
                        "materializationOccurrence", -1);
                String kind = string(binding, "kind");
                boolean map = "DYNAMIC_MAP_ENTRY_FIELD_BINDING".equals(kind);
                boolean container =
                        "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(kind);
                boolean mapProjection =
                        "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING"
                        .equals(kind);
                boolean selectorValid = map
                        && integer(binding, "schemaVersion", -1) == 1
                        && !string(binding,
                        "entryReadObservationId").isEmpty()
                        && binding.get("keyExpression") != null
                        && binding.get("keyExpression").isJsonObject()
                        && !string(binding,
                        "keyExpressionAuthority").isEmpty()
                        && "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        .concat("FIELD_SITE_OCCURRENCE").equals(string(
                                binding, "authority"))
                        || container
                        && integer(binding, "schemaVersion", -1) == 2
                        && completeContainerSelector(binding)
                        && "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_"
                        .concat("IDENTITY_AND_STABLE_FIELD_SITE_OCCURRENCE")
                        .equals(string(binding, "authority"));
                selectorValid |= mapProjection
                        && integer(binding, "schemaVersion", -1) == 3
                        && completeMapProjectionSelector(binding)
                        && "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_"
                        .concat("WITH_EXACT_OUTPUT_IDENTITY")
                        .equals(string(binding, "authority"))
                        && "EXACT_SYMBOLIZE_FIELD_OBSERVATION_AND_"
                        .concat("SYMBOLIZED_INPUT").equals(string(binding,
                                "runtimeSymbolizationAuthority"))
                        && "UNIQUE_ENTRYSET_KEYED_SNAPSHOT_AND_OUTPUT_"
                        .concat("IDENTITY_VALIDATION").equals(string(binding,
                                "projectionEvidenceAuthority"));
                boolean valid = selectorValid
                        && bool(binding, "complete", false)
                        && !id.isEmpty()
                        && id.equals("DYNAMIC_FIELD:" + dynamic)
                        && !base.isEmpty() && !dynamic.isEmpty()
                        && !site.isEmpty() && occurrence > 0
                        && !string(binding, "fieldSignature").isEmpty()
                        && array(binding, "fieldPath").size() > 0;
                if (!valid) {
                    result.gap("INCOMPLETE_DYNAMIC_BINDING:"
                            + firstNonBlank(id, String.valueOf(index)));
                    continue;
                }
                String siteOccurrence = base + "\u0000" + site + "\u0000"
                        + occurrence;
                if (metadataById.containsKey(id)
                        || !dynamicSymbols.add(dynamic)
                        || !siteOccurrences.add(siteOccurrence)) {
                    result.gap("DUPLICATE_DYNAMIC_BINDING:" + id);
                    continue;
                }
                JsonObject metadata = projectionDynamicMetadata(binding);
                metadataById.put(id, metadata);
                result.dynamicBindings.add(metadata);
                if (container) {
                    List<JsonObject> expressions = new ArrayList<>();
                    collectExactDynamicExpressions(object(item, "guard").get(
                            "conditions"), dynamic, expressions,
                            new LinkedHashSet<String>());
                    if (expressions.size() != 1) {
                        result.gap(expressions.isEmpty()
                                ? "CONTAINER_DYNAMIC_BINDING_WITHOUT_EXACT_"
                                + "GUARD_EXPRESSION:" + id
                                : "AMBIGUOUS_CONTAINER_DYNAMIC_GUARD_"
                                + "EXPRESSION:" + id);
                    } else {
                        JsonObject expression = expressions.get(0);
                        metadata.add("fieldExpression",
                                expression.deepCopy());
                        metadata.addProperty(
                                "fieldExpressionRawEngineSymbol",
                                string(expression, "_exp"));
                        metadata.addProperty("fieldJavaType",
                                string(expression, "_java_type"));
                        metadata.addProperty("observationBindingAuthority",
                                "EXACT_CASE_GUARD_DYNAMIC_SYMBOL");
                        metadata.addProperty("observationMatched", true);
                        matched.add(id);
                    }
                } else if (mapProjection) {
                    String javaType = string(binding, "fieldJavaType");
                    if (javaType.isEmpty()
                            || !declaredExactFieldDescriptor(string(binding,
                            "fieldSignature")).equals(javaTypeDescriptor(
                            javaType))) {
                        result.gap("MAP_PROJECTION_DYNAMIC_FIELD_TYPE_"
                                + "MISMATCH:" + id);
                    } else {
                        metadata.addProperty(
                                "fieldExpressionRawEngineSymbol", dynamic);
                        metadata.addProperty("fieldJavaType", javaType);
                        metadata.addProperty(
                                "observationBindingAuthority",
                                "EXACT_RUNTIME_SYMBOLIZE_FIELD_WITHOUT_"
                                        + "PC_EXPRESSION");
                        metadata.addProperty("dynamicTermSourceAuthority",
                                "EXACT_RUNTIME_SYMBOLIZE_FIELD_WITHOUT_"
                                        + "PC_EXPRESSION");
                        metadata.addProperty("observationMatched", true);
                        matched.add(id);
                    }
                }
            }

            JsonArray observations = observationsElement != null
                    && observationsElement.isJsonArray()
                    ? observationsElement.getAsJsonArray() : new JsonArray();
            for (int observationIndex = 0;
                    observationIndex < observations.size(); observationIndex++) {
                JsonElement observationElement = observations.get(
                        observationIndex);
                if (!observationElement.isJsonObject()) {
                    result.gap("NON_OBJECT_HEAP_OBSERVATION:"
                            + observationIndex);
                    continue;
                }
                JsonObject observation = observationElement.getAsJsonObject();
                String observationId = string(observation, "observationId");
                for (int bindingIndex = 0; bindingIndex < array(observation,
                        "entryFieldBindings").size(); bindingIndex++) {
                    JsonElement bindingElement = array(observation,
                            "entryFieldBindings").get(bindingIndex);
                    if (!bindingElement.isJsonObject()) {
                        result.gap("NON_OBJECT_ENTRY_FIELD_BINDING:"
                                + observationId + ":" + bindingIndex);
                        continue;
                    }
                    JsonObject observed = bindingElement.getAsJsonObject();
                    boolean dynamic = "DYNAMIC_MAP_ENTRY_FIELD_BINDING".equals(
                            string(observed, "kind"))
                            || observed.has("dynamicBindingId")
                            || observed.has("dynamicFieldSymbol")
                            || observed.has("baseInputSymbol")
                            || observed.has("fieldExpression");
                    if (!dynamic) {
                        continue;
                    }
                    String id = string(observed, "dynamicBindingId");
                    JsonObject metadata = metadataById.get(id);
                    JsonObject runtime = metadata == null ? null
                            : object(metadata, "runtimeBinding");
                    if (runtime != null
                            && "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING"
                            .equals(string(runtime, "kind"))) {
                        continue;
                    }
                    if (runtime != null
                            && "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_"
                            .concat("FIELD_BINDING").equals(string(runtime,
                                    "kind"))) {
                        continue;
                    }
                    boolean valid = metadata != null
                            && integer(observed, "schemaVersion", -1) == 1
                            && "DYNAMIC_MAP_ENTRY_FIELD_BINDING".equals(
                            string(observed, "kind"))
                            && observationId.equals(string(observed,
                            "entryReadObservationId"))
                            && "FIELD_FAMILY_TEMPLATE_ONLY".equals(string(
                            observed, "baseInputRole"))
                            && "RUNTIME_DYNAMIC_FIELD_INSTANCE_EXACT_"
                            .concat("EXPRESSION_AND_ENTRY_VALUE_TOKEN_JOIN")
                            .equals(string(observed, "authority"))
                            && sameDynamicMember(runtime, observed,
                            "dynamicBindingId")
                            && sameDynamicMember(runtime, observed,
                            "baseInputSymbol")
                            && sameDynamicMember(runtime, observed,
                            "dynamicFieldSymbol")
                            && sameDynamicMember(runtime, observed,
                            "materializationSiteId")
                            && integer(runtime, "materializationOccurrence", -1)
                            == integer(observed,
                            "materializationOccurrence", -2)
                            && sameDynamicMember(runtime, observed,
                            "fieldSignature")
                            && array(runtime, "fieldPath").equals(array(
                            observed, "fieldPath"))
                            && sameDynamicMember(runtime, observed,
                            "entryReadObservationId")
                            && sameDynamicMember(runtime, observed,
                            "keyExpressionAuthority")
                            && runtime.get("keyExpression") != null
                            && runtime.get("keyExpression").equals(
                            observed.get("keyExpression"))
                            && observed.get("fieldExpression") != null
                            && observed.get("fieldExpression").isJsonObject()
                            && rawSymbolReferences(observed.get(
                            "fieldExpression"), string(observed,
                            "dynamicFieldSymbol"));
                    if (!valid) {
                        result.gap("DYNAMIC_BINDING_OBSERVATION_MISMATCH:"
                                + firstNonBlank(id, observationId + ":"
                                + bindingIndex));
                        continue;
                    }
                    if (!matched.add(id)) {
                        result.gap("DYNAMIC_BINDING_USED_MORE_THAN_ONCE:" + id);
                        continue;
                    }
                    metadata.add("fieldExpression", observed.get(
                            "fieldExpression").deepCopy());
                    metadata.addProperty("fieldExpressionRawEngineSymbol",
                            string(observed.getAsJsonObject("fieldExpression"),
                                    "_exp"));
                    metadata.addProperty("fieldJavaType", string(observed,
                            "fieldJavaType"));
                    metadata.addProperty("heapObservationId", observationId);
                    metadata.addProperty("observationBindingAuthority",
                            string(observed, "authority"));
                    metadata.addProperty("observationMatched", true);
                }
            }
            for (String id : metadataById.keySet()) {
                if (!matched.contains(id)) {
                    result.gap("DYNAMIC_BINDING_WITHOUT_HEAP_OBSERVATION:"
                            + id);
                }
            }
            return result;
        }

        private static JsonObject projectionDynamicMetadata(
                JsonObject binding) {
            JsonObject result = new JsonObject();
            result.add("runtimeBinding", binding.deepCopy());
            for (String field : new String[]{"schemaVersion", "kind",
                    "dynamicBindingId", "baseInputSymbol",
                    "dynamicFieldSymbol", "materializationSiteId",
                    "materializationOccurrence", "fieldSignature",
                    "fieldPath", "leafOwnerObjectToken",
                    "objectTokenAuthority", "objectTokenScope",
                    "entryReadObservationId", "keyExpression",
                    "keyExpressionAuthority", "containerSelector",
                    "containerBindingId", "containerInputPort",
                    "containerInputCell", "selectorAuthority",
                    "elementIndex", "elementOccurrence",
                    "declaredFieldOwnerClass", "declaredFieldType",
                    "mapProjectionSelector", "entrySnapshotElementCount",
                    "outputElementCount",
                    "entrySnapshotElementObjectTokens",
                    "entrySnapshotMapKeyExpressions",
                    "entryKeyExpressionAuthority",
                    "entrySetViewOrderAuthority",
                    "runtimeSymbolizationAuthority",
                    "projectionEvidenceAuthority", "fieldJavaType",
                    "outputValidationMode",
                    "authority", "complete"}) {
                JsonElement value = binding.get(field);
                if (value != null) result.add(field, value.deepCopy());
            }
            result.addProperty("observationMatched", false);
            return result;
        }

        private static boolean completeContainerSelector(
                JsonObject binding) {
            JsonObject selector = object(binding, "containerSelector");
            long leafOwner = longInteger(binding,
                    "leafOwnerObjectToken", 0L);
            long containerObject = longInteger(selector,
                    "containerObjectToken", 0L);
            long elementObject = longInteger(selector,
                    "elementObjectToken", 0L);
            String scope = string(binding, "objectTokenScope");
            String resolvedFrom = string(selector,
                    "resolvedFromSelectorAuthority");
            return "ARRAY_INDEX".equals(string(selector, "kind"))
                    && bool(selector, "complete", false)
                    && !string(selector, "bindingId").isEmpty()
                    && !string(selector, "containerInputPort").isEmpty()
                    && !string(selector, "containerInputCell").isEmpty()
                    && !string(selector, "containerInputPort").equals(
                    string(binding, "baseInputSymbol"))
                    && "EXACT_ARRAY_INDEX".equals(string(selector,
                    "selectorAuthority"))
                    && integer(selector, "elementIndex", -1) >= 0
                    && integer(selector, "elementOccurrence", -1) > 0
                    && integer(selector, "elementOccurrence", -1)
                    == integer(binding, "materializationOccurrence", -2)
                    && !string(selector,
                    "declaredFieldOwnerClass").isEmpty()
                    && !string(selector, "declaredFieldType").isEmpty()
                    && leafOwner > 0L && containerObject > 0L
                    && elementObject > 0L && leafOwner == elementObject
                    && !scope.isEmpty()
                    && scope.equals(string(selector, "objectTokenScope"))
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN"
                    .equals(string(binding, "objectTokenAuthority"))
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN"
                    .equals(string(selector, "objectTokenAuthority"))
                    && ("EXACT_ARRAY_INDEX".equals(resolvedFrom)
                    || "DISCOVER_UNIQUE_IDENTITY_INDEX".equals(
                    resolvedFrom))
                    && "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                    .concat("ACTIVATION_LOCAL_ELEMENT_IDENTITY").equals(
                    string(selector, "authority"));
        }

        private static boolean completeMapProjectionSelector(
                JsonObject binding) {
            JsonObject selector = object(binding,
                    "mapProjectionSelector");
            long leaf = longInteger(binding, "leafOwnerObjectToken", 0L);
            long map = longInteger(selector, "mapObjectToken", 0L);
            long element = longInteger(selector,
                    "elementObjectToken", 0L);
            long output = longInteger(selector,
                    "outputArrayObjectToken", 0L);
            String scope = string(binding, "objectTokenScope");
            int index = integer(selector, "outputIndex", -1);
            int occurrence = integer(selector,
                    "elementOccurrence", -1);
            int entryCount = integer(binding,
                    "entrySnapshotElementCount", -1);
            int outputCount = integer(binding, "outputElementCount", -1);
            JsonArray tokens = array(binding,
                    "entrySnapshotElementObjectTokens");
            JsonArray keys = array(binding,
                    "entrySnapshotMapKeyExpressions");
            String outputMode = string(binding, "outputValidationMode");
            String outputAuthority = string(selector,
                    "outputVerificationAuthority");
            boolean outputAuthorityValid =
                    "ROOT_RETURN_PROJECTED_FIELD".equals(outputMode)
                    && "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD"
                    .equals(outputAuthority)
                    || "EXACT_REQUESTED_OUTPUT_CAPTURE".equals(outputMode)
                    && ("ACTIVE_TOKEN_EXACT_ORIGINAL_CALL_ARGUMENT".equals(
                    outputAuthority)
                    || "ACTIVE_TOKEN_EXACT_POST_INSTANCE_FIELD_ASSIGNMENT"
                    .equals(outputAuthority));
            return "MAP_OUTPUT_ARRAY_INDEX".equals(string(selector,
                    "kind"))
                    && bool(selector, "complete", false)
                    && !string(selector, "bindingId").isEmpty()
                    && !string(selector, "mapInputPort").isEmpty()
                    && !string(selector, "mapInputCell").isEmpty()
                    && !string(selector, "outputPort").isEmpty()
                    && !string(selector, "outputCell").isEmpty()
                    && "MAP_VALUES_VIEW".equals(string(selector,
                    "mapProjectionOperation"))
                    && index >= 0 && occurrence == index + 1
                    && occurrence == integer(binding,
                    "materializationOccurrence", -2)
                    && !string(selector,
                    "declaredFieldOwnerClass").isEmpty()
                    && !string(selector,
                    "declaredFieldType").isEmpty()
                    && string(binding, "fieldSignature").equals(string(
                    selector, "declaredFieldSignature"))
                    && leaf > 0L && map > 0L && element == leaf
                    && output > 0L
                    && map != element && map != output && element != output
                    && entryCount > 0 && outputCount == entryCount
                    && tokens.size() == entryCount
                    && keys.size() == entryCount && index < entryCount
                    && jsonLong(tokens.get(index), -1L) == element
                    && selector.get("expectedMapKey") != null
                    && selector.get("expectedMapKey").equals(keys.get(index))
                    && "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_"
                    .concat("SNAPSHOT").equals(string(binding,
                            "entryKeyExpressionAuthority"))
                    && "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                    .concat("POSITIONAL_REFERENCE_EQUALITY").equals(string(
                            binding, "entrySetViewOrderAuthority"))
                    && !scope.isEmpty()
                    && scope.equals(string(selector, "objectTokenScope"))
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                    string(binding, "objectTokenAuthority"))
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                    string(selector, "objectTokenAuthority"))
                    && "NONE".equals(string(selector,
                    "crossExecutionOrdinalAuthority"))
                    && exactImmutableMapKeyExpression(selector.get(
                    "expectedMapKey"))
                    && "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_"
                    .concat("SNAPSHOT").equals(string(selector,
                            "expectedMapKeyAuthority"))
                    && "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                    .concat("POSITIONAL_REFERENCE_EQUALITY").equals(string(
                            selector, "sourceOutputIndexAuthority"))
                    && "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_AND_"
                    .concat("EXACT_OUTPUT_IDENTITY").equals(string(selector,
                            "replaySelectionAuthority"))
                    && bool(selector, "outputIdentityVerified", false)
                    && supportedMapProjectionImplementation(selector)
                    && bool(selector,
                    "entryConcreteFieldValueCaptured", false)
                    && bool(selector,
                    "noInterveningFieldWriteVerified", false)
                    && bool(selector, "outputFieldValueVerified", false)
                    && "SAME_EXECUTION_BOUNDED_OBSERVED_SCHEDULE_EXACT_"
                    .concat("DECLARED_FIELD_ENTRY_VALUE_PLUS_NO_")
                    .concat("INTERVENING_RUNTIME_FIELD_WRITE_AND_EXACT_")
                    .concat("OUTPUT_RECHECK").equals(string(selector,
                            "fieldValueFlowAuthority"))
                    && outputAuthorityValid
                    && "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                    .concat("EXACT_OUTPUT_IDENTITY")
                    .equals(string(selector, "authority"));
        }

        private static boolean supportedMapProjectionImplementation(
                JsonObject row) {
            String implementation = string(row, "mapImplementationClass");
            return ("java.util.HashMap".equals(implementation)
                    || "java.util.LinkedHashMap".equals(implementation))
                    && "EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_"
                    .concat("LINKEDHASHMAP_JAVA_EQUALS_HASHCODE_")
                    .concat("EXTENSIONAL_V1").equals(string(row,
                            "mapImplementationAuthority"));
        }

        private static long jsonLong(JsonElement value, long fallback) {
            try {
                return value == null || value.isJsonNull()
                        ? fallback : value.getAsLong();
            } catch (RuntimeException malformed) {
                return fallback;
            }
        }

        private static boolean exactImmutableMapKeyExpression(
                JsonElement element) {
            if (element == null || !element.isJsonObject()) return false;
            JsonObject expression = element.getAsJsonObject();
            if (!"ConstExpr".equals(string(expression, "_type"))) {
                return false;
            }
            String raw = string(expression, "_exp");
            if (!raw.startsWith("Y_") || raw.length() < 4
                    || raw.charAt(3) != '_') return false;
            char kind = raw.charAt(2);
            String type = string(expression, "_java_type")
                    .replace('.', '/');
            boolean typeMatches = kind == 'Z'
                    && "java/lang/Boolean".equals(type)
                    || kind == 'B' && "java/lang/Byte".equals(type)
                    || kind == 'C' && "java/lang/Character".equals(type)
                    || kind == 'S' && "java/lang/Short".equals(type)
                    || kind == 'I' && "java/lang/Integer".equals(type)
                    || kind == 'J' && "java/lang/Long".equals(type)
                    || kind == 'L' && "java/lang/String".equals(type);
            if (!typeMatches) return false;
            String value = raw.substring(4);
            try {
                if (kind == 'Z') return "0".equals(value)
                        || "1".equals(value);
                if (kind == 'B' || kind == 'C' || kind == 'S'
                        || kind == 'I' || kind == 'J') {
                    java.math.BigInteger integer =
                            new java.math.BigInteger(value);
                    if (!integer.toString().equals(value)) return false;
                    if (kind == 'B') return integer.compareTo(
                            java.math.BigInteger.valueOf(Byte.MIN_VALUE)) >= 0
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Byte.MAX_VALUE)) <= 0;
                    if (kind == 'C') return integer.signum() >= 0
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Character.MAX_VALUE)) <= 0;
                    if (kind == 'S') return integer.compareTo(
                            java.math.BigInteger.valueOf(Short.MIN_VALUE)) >= 0
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Short.MAX_VALUE)) <= 0;
                    if (kind == 'I') return integer.compareTo(
                            java.math.BigInteger.valueOf(Integer.MIN_VALUE)) >= 0
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Integer.MAX_VALUE)) <= 0;
                    return integer.compareTo(java.math.BigInteger.valueOf(
                            Long.MIN_VALUE)) >= 0
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Long.MAX_VALUE)) <= 0;
                }
                return kind == 'L';
            } catch (RuntimeException malformed) {
                return false;
            }
        }

        private static String stableImmutableMapKeySelector(
                JsonElement element) {
            if (!exactImmutableMapKeyExpression(element)) return "";
            String raw = string(element.getAsJsonObject(), "_exp");
            String value = raw.substring(4);
            return raw.charAt(2) + ":" + value.length() + ":" + value;
        }

        private static void collectExactDynamicExpressions(
                JsonElement value, String dynamic,
                List<JsonObject> result, Set<String> seen) {
            if (value == null || value.isJsonNull()) return;
            if (value.isJsonArray()) {
                for (JsonElement child : value.getAsJsonArray()) {
                    collectExactDynamicExpressions(child, dynamic, result,
                            seen);
                }
                return;
            }
            if (!value.isJsonObject()) return;
            JsonObject object = value.getAsJsonObject();
            if (rawSymbolReferences(object, dynamic)) {
                String canonical = GSON.toJson(object);
                if (seen.add(canonical)) result.add(object);
            }
            for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
                if (!"_code_position".equals(entry.getKey())) {
                    collectExactDynamicExpressions(entry.getValue(), dynamic,
                            result, seen);
                }
            }
        }

        private static boolean sameDynamicMember(JsonObject left,
                                                 JsonObject right,
                                                 String field) {
            if (left == null || right == null) return false;
            JsonElement leftValue = left.get(field);
            JsonElement rightValue = right.get(field);
            return leftValue != null && rightValue != null
                    && leftValue.equals(rightValue);
        }

        private void rejectNonRegionSemantics(String region,
                                              JsonObject summary) {
            if (summary.has("protocolModel")) {
                heapGap(region,
                        "LEGACY_DOMAIN_SEMANTIC_ADAPTER_REJECTED@" + region);
            }
            if (array(summary, "explicitContracts").size() > 0) {
                heapGap(region,
                        "EXPLICIT_CONTRACT_EXCLUDED_FROM_AUTOMATIC_DERIVATION@"
                                + region);
            }
        }

        private void addRelationshipCandidate(String id, String kind,
                                              String formula,
                                              boolean required,
                                              JsonObject roles,
                                              String... provenance) {
            String stableId = smtName(id);
            if (!relationshipIds.add(stableId)) return;
            JsonObject candidate = new JsonObject();
            candidate.addProperty("relationshipId", stableId);
            candidate.addProperty("kind", kind);
            candidate.addProperty("formula", formula);
            candidate.addProperty("required", required);
            candidate.addProperty("status", "UNVERIFIED_CANDIDATE");
            candidate.add("roles", roles.deepCopy());
            JsonArray sources = new JsonArray();
            for (String value : provenance) sources.add(value);
            candidate.add("provenance", sources);
            relationshipCandidates.add(candidate);
        }

        private void validateHeapEffectSummary(String region,
                                               JsonObject summary,
                                               JsonArray initializers,
                                               JsonArray effects) {
            if (summary.has("relationallyComplete")
                    && !bool(summary, "relationallyComplete", false)) {
                heapGap(region, "IncompleteRelationalSummary@" + region);
            }
            boolean modelDeclared = summary.has("heapEffectModel")
                    && summary.get("heapEffectModel").isJsonObject();
            JsonObject model = object(summary, "heapEffectModel");
            if (effects.size() > 0 && !modelDeclared) {
                heapGap(region, "MissingHeapEffectModel@" + region);
            }
            if (modelDeclared) {
                if (!bool(model, "complete", false)) {
                    heapGap(region, "IncompleteHeapEffectModel@" + region);
                }
                int declaredEffects = integer(model, "effectCount", -1);
                if (declaredEffects != effects.size()) {
                    heapGap(region, "HeapEffectCountMismatch@" + region
                            + ":" + declaredEffects + "!=" + effects.size());
                }
                int declaredInitializers = integer(model,
                        "initializerCount", 0);
                if (declaredInitializers != initializers.size()) {
                    heapGap(region, "HeapInitializerCountMismatch@" + region
                            + ":" + declaredInitializers + "!="
                            + initializers.size());
                }
                int initializedInputs = integer(model,
                        "initializedInputCount", 0);
                if (initializedInputs != initializers.size()) {
                    heapGap(region, "HeapInitializedInputCountMismatch@"
                            + region + ":" + initializedInputs + "!="
                            + initializers.size());
                }
            }

            Map<String, JsonObject> initializersByFamily =
                    validateHeapInitializers(region, initializers);
            Map<String, HeapStateCursor> cursors = new LinkedHashMap<>();
            Set<String> effectIds = new LinkedHashSet<>();
            for (int index = 0; index < effects.size(); index++) {
                JsonElement element = effects.get(index);
                if (!element.isJsonObject()) {
                    heapGap(region, "MalformedHeapEffect@" + region
                            + ":" + index);
                    continue;
                }
                JsonObject effect = element.getAsJsonObject();
                String effectId = firstNonBlank(string(effect, "effectId"),
                        "effect-" + index);
                if (!effect.has("effectId") || !effectIds.add(effectId)) {
                    heapGap(region, "HeapEffectIdentityGap@" + region
                            + ":" + effectId);
                }
                String family = string(effect, "stateFamily");
                String preState = string(effect, "preState");
                String postState = string(effect, "postState");
                String inputPort = string(effect, "inputPort");
                String outputPort = string(effect, "outputPort");
                int before = integer(effect, "stateOrdinalBefore",
                        Integer.MIN_VALUE);
                int after = integer(effect, "stateOrdinalAfter",
                        Integer.MIN_VALUE);
                if (family.isEmpty() || preState.isEmpty()
                        || postState.isEmpty() || inputPort.isEmpty()
                        || outputPort.isEmpty()
                        || before == Integer.MIN_VALUE
                        || after == Integer.MIN_VALUE) {
                    heapGap(region, "HeapStateMetadataMissing@" + region
                            + ":" + effectId);
                    continue;
                }
                if (after != before + 1) {
                    heapGap(region, "HeapStateOrdinalGap@" + region
                            + ":" + effectId + ":" + before + "->" + after);
                }
                HeapStateCursor cursor = cursors.get(family);
                if (cursor == null) {
                    if (before != 0) {
                        heapGap(region, "HeapStateInitialOrdinalGap@" + region
                                + ":" + effectId + ":" + before);
                    }
                    JsonObject initializer = initializersByFamily.get(family);
                    boolean freshInput = "STATIC_FRESH_EMPTY_MAP".equals(
                            string(effect, "inputBinding"));
                    if (freshInput && initializer == null) {
                        heapGap(region, "MissingFreshMapInitializer@" + region
                                + ":" + effectId);
                    } else if (!freshInput && initializer != null) {
                        heapGap(region, "UnusedFreshMapInitializerBinding@"
                                + region + ":" + effectId);
                    } else if (freshInput
                            && (!inputPort.equals(string(initializer,
                            "statePort"))
                            || !preState.equals(string(initializer,
                            "stateId")))) {
                        heapGap(region, "FreshMapInitializerStateMismatch@"
                                + region + ":" + effectId);
                    }
                } else {
                    if (before != cursor.after
                            || !preState.equals(cursor.postState)) {
                        heapGap(region, "HeapStateChainGap@" + region
                                + ":" + effectId);
                    }
                    if (!inputPort.equals(cursor.outputPort)) {
                        heapGap(region, "HeapPortChainGap@" + region
                                + ":" + effectId);
                    }
                }
                cursors.put(family, new HeapStateCursor(after, postState,
                        outputPort));
            }
            for (Map.Entry<String, JsonObject> entry
                    : initializersByFamily.entrySet()) {
                HeapStateCursor cursor = cursors.get(entry.getKey());
                if (cursor == null) {
                    heapGap(region, "UnusedFreshMapInitializer@" + region
                            + ":" + entry.getKey());
                    continue;
                }
                String requestedOutput = string(entry.getValue(),
                        "requestedOutputPort");
                if (requestedOutput.isEmpty()
                        || !requestedOutput.equals(cursor.outputPort)) {
                    heapGap(region, "FreshMapInitializerOutputMismatch@"
                            + region + ":" + entry.getKey());
                }
            }
            if (modelDeclared) {
                int declaredFamilies = integer(model,
                        "mapStateFamilyCount", -1);
                if (declaredFamilies != cursors.size()) {
                    heapGap(region, "HeapStateFamilyCountMismatch@" + region
                            + ":" + declaredFamilies + "!=" + cursors.size());
                }
            }
        }

        private Map<String, JsonObject> validateHeapInitializers(
                String region, JsonArray initializers) {
            Map<String, JsonObject> result = new LinkedHashMap<>();
            Set<String> initializerIds = new LinkedHashSet<>();
            Set<String> statePorts = new LinkedHashSet<>();
            for (int index = 0; index < initializers.size(); index++) {
                JsonElement element = initializers.get(index);
                if (!element.isJsonObject()) {
                    heapGap(region, "MalformedHeapInitializer@" + region
                            + ":" + index);
                    continue;
                }
                JsonObject initializer = element.getAsJsonObject();
                String id = string(initializer, "initializerId");
                String kind = string(initializer, "kind");
                String statePort = string(initializer, "statePort");
                String family = string(initializer, "stateFamily");
                String stateId = string(initializer, "stateId");
                String staticId = string(initializer,
                        "staticInitializerId");
                String allocationEdge = string(initializer,
                        "allocationEdgeId");
                boolean valid = validMapEmptyInitializer(initializer);
                if (!valid) {
                    heapGap(region, "MalformedMapEmptyInitializer@" + region
                            + ":" + index);
                    continue;
                }
                if (!initializerIds.add(id)
                        || !statePorts.add(statePort)
                        || result.containsKey(family)) {
                    heapGap(region, "HeapInitializerIdentityGap@" + region
                            + ":" + id);
                    continue;
                }
                result.put(family, initializer);
            }
            return result;
        }

        private void finiteMapSnapshots(String region, JsonObject summary) {
            JsonElement declared = summary.get("finiteMapSnapshots");
            if (declared == null) return;
            if (!declared.isJsonArray()) {
                heapGap(region, "MalformedFiniteMapSnapshots@" + region);
                return;
            }
            JsonArray snapshots = declared.getAsJsonArray();
            Map<String, JsonObject> observations = new LinkedHashMap<>();
            Set<String> duplicateObservationIds = new LinkedHashSet<>();
            for (JsonElement element : array(summary, "heapObservations")) {
                if (!element.isJsonObject()) continue;
                JsonObject observation = element.getAsJsonObject();
                String id = string(observation, "observationId");
                if (id.isEmpty()) continue;
                if (observations.put(id, observation) != null) {
                    duplicateObservationIds.add(id);
                }
            }
            Set<String> snapshotIds = new LinkedHashSet<>();
            Set<String> statePorts = new LinkedHashSet<>();
            for (int index = 0; index < snapshots.size(); index++) {
                JsonElement element = snapshots.get(index);
                if (!element.isJsonObject()) {
                    heapGap(region, "MalformedFiniteMapSnapshot@" + region
                            + ":" + index);
                    continue;
                }
                JsonObject snapshot = element.getAsJsonObject();
                String id = string(snapshot, "snapshotId");
                String rawStatePort = string(snapshot, "statePort");
                int cardinality = integer(snapshot, "cardinality", -1);
                long token = jsonLong(snapshot.get(
                        "backingMapObjectToken"), -1L);
                String scope = string(snapshot, "objectTokenScope");
                String implementation = string(snapshot,
                        "implementationClass");
                JsonArray entries = array(snapshot, "entries");
                JsonArray proofIds = array(snapshot, "proofObservationIds");
                boolean valid = integer(snapshot, "schemaVersion", -1) == 1
                        && "EXACT_RUNTIME_FINITE_MAP_SNAPSHOT".equals(
                        string(snapshot, "kind"))
                        && !id.isEmpty() && snapshotIds.add(id)
                        && !rawStatePort.isEmpty()
                        && statePorts.add(rawStatePort)
                        && cardinality >= 0 && cardinality <= 32
                        && entries.size() == cardinality
                        && proofIds.size() == cardinality
                        && token > 0 && !scope.isEmpty()
                        && ("java.util.HashMap".equals(implementation)
                        || "java.util.LinkedHashMap".equals(implementation))
                        && bool(snapshot, "mapKeysFullyCaptured", false)
                        && bool(snapshot, "entryReadBijectionComplete", false)
                        && bool(snapshot, "complete", false)
                        && "INITIAL_EXACT_MAP_SIZE_AND_KEYS_PLUS_COMPLETE_"
                        .concat("ENTRY_READ_BIJECTION_V1").equals(
                        string(snapshot, "authority"));

                Set<String> entryObservationIds = new LinkedHashSet<>();
                Set<String> declaredProofIds = new LinkedHashSet<>();
                for (JsonElement proofId : proofIds) {
                    if (!proofId.isJsonPrimitive()
                            || !declaredProofIds.add(
                            proofId.getAsString())) {
                        valid = false;
                    }
                }
                List<Term> keys = new ArrayList<>();
                List<Term> values = new ArrayList<>();
                for (int entryIndex = 0; entryIndex < entries.size();
                     entryIndex++) {
                    JsonElement entryElement = entries.get(entryIndex);
                    if (!entryElement.isJsonObject()) {
                        valid = false;
                        continue;
                    }
                    JsonObject entry = entryElement.getAsJsonObject();
                    String observationId = string(entry, "observationId");
                    JsonObject observation = observations.get(observationId);
                    if (observationId.isEmpty()
                            || !entryObservationIds.add(observationId)
                            || duplicateObservationIds.contains(observationId)
                            || observation == null
                            || !"MAP_ENTRY_READ".equals(string(observation,
                            "kind"))
                            || !bool(observation, "complete", false)
                            || !rawStatePort.equals(string(observation,
                            "statePort"))
                            || token != jsonLong(observation.get(
                            "backingMapObjectToken"), -1L)
                            || !scope.equals(string(observation,
                            "objectTokenScope"))
                            || !"EXACT_ACTIVATION_MAP_INPUT_EXPRESSION".equals(
                            string(observation, "stateBindingAuthority"))
                            || !"JAVA_MAP_ENTRY_FROM_BOUND_ENTRY_SET_NEXT".equals(
                            string(observation, "entryBindingAuthority"))
                            || !"SAME_MAP_ENTRY_GET_KEY_AT_NEXT".equals(
                            string(observation, "keyBindingAuthority"))
                            || !"SAME_MAP_ENTRY_GET_VALUE_AT_NEXT".equals(
                            string(observation, "valueBindingAuthority"))
                            || !entry.has("keyExpression")
                            || !entry.has("valueExpression")
                            || !entry.get("keyExpression").equals(
                            observation.get("keyExpression"))
                            || !entry.get("valueExpression").equals(
                            observation.get("valueExpression"))
                            || !authenticatedValueRefWitness(observation,
                            "valueExpression", "valueExpressionAuthority",
                            "valueObjectToken")) {
                        valid = false;
                        continue;
                    }
                    Term key = mapKeyTerm(entry.get("keyExpression"),
                            "finite_snapshot_" + region + "_" + id + "_"
                                    + entryIndex);
                    Term value = term(entry.get("valueExpression"), Sort.REF);
                    if (key == null || key.sort != Sort.VALUE
                            || value.sort != Sort.REF) {
                        valid = false;
                        continue;
                    }
                    keys.add(key);
                    values.add(asValue(value));
                }
                if (!entryObservationIds.equals(declaredProofIds)
                        || keys.size() != cardinality
                        || values.size() != cardinality) {
                    valid = false;
                }
                if (!valid) {
                    heapGap(region, "InvalidFiniteMapSnapshot@" + region
                            + ":" + firstNonBlank(id,
                            String.valueOf(index)));
                    continue;
                }

                String statePort = scopedHeapPort(rawStatePort);
                if (ports.contains(rawStatePort)
                        && ports.sort(rawStatePort) != Sort.MAP) {
                    heapGap(region, "FiniteMapSnapshotStateSortGap@"
                            + region + ":" + id);
                    continue;
                }
                declarePort(statePort, Sort.MAP);
                mentionedPorts.add(statePort);
                boundPorts.add(statePort);
                if (keys.size() > 1) {
                    StringBuilder distinct = new StringBuilder("(distinct");
                    for (Term key : keys) distinct.append(' ')
                            .append(key.text);
                    assertNamed("finite_map_snapshot_distinct_" + id,
                            distinct.append(')').toString());
                }
                String exactState = "emptyMapState";
                for (int entryIndex = 0; entryIndex < keys.size();
                     entryIndex++) {
                    exactState = "(map_put " + exactState + " "
                            + keys.get(entryIndex).text + " "
                            + values.get(entryIndex).text + ")";
                }
                assertNamed("finite_map_snapshot_exact_" + id,
                        "(= " + portName(statePort) + " " + exactState
                                + ")");
                JsonObject catalog = new JsonObject();
                catalog.addProperty("snapshotId", id);
                catalog.addProperty("regionId", region);
                catalog.addProperty("statePort", rawStatePort);
                catalog.addProperty("runtimeBoundedMapCardinality",
                        cardinality);
                catalog.addProperty("objectTokenScope", scope);
                catalog.addProperty("authority", string(snapshot,
                        "authority"));
                catalog.addProperty("guarded", !currentGuard.isEmpty());
                runtimeBoundedMapSnapshots.add(catalog);
                finiteMapSnapshotCount++;
            }
        }

        private void heapObservations(String region, JsonObject summary) {
            JsonElement declared = summary.get("heapObservations");
            if (declared == null) return;
            if (!declared.isJsonArray()) {
                heapGap(region, "MalformedHeapObservations@" + region);
                return;
            }
            JsonArray observations = declared.getAsJsonArray();
            Map<String, Integer> idCounts = new LinkedHashMap<>();
            for (JsonElement element : observations) {
                if (!element.isJsonObject()) continue;
                String id = string(element.getAsJsonObject(), "observationId");
                if (id.isEmpty()) continue;
                Integer count = idCounts.get(id);
                idCounts.put(id, count == null ? 1 : count + 1);
            }

            Set<String> declaredStatePorts = new LinkedHashSet<>();
            for (JsonElement element : array(summary, "heapEffects")) {
                if (!element.isJsonObject()) continue;
                JsonObject effect = element.getAsJsonObject();
                declaredStatePorts.add(string(effect, "inputPort"));
                declaredStatePorts.add(string(effect, "outputPort"));
            }
            for (JsonElement element : array(summary,
                    "heapStateInitializers")) {
                if (element.isJsonObject()) declaredStatePorts.add(string(
                        element.getAsJsonObject(), "statePort"));
            }

            for (int index = 0; index < observations.size(); index++) {
                JsonElement element = observations.get(index);
                if (!element.isJsonObject()) {
                    heapGap(region, "MalformedHeapObservation@" + region
                            + ":" + index);
                    continue;
                }
                JsonObject observation = element.getAsJsonObject();
                String id = string(observation, "observationId");
                String statePort = string(observation, "statePort");
                JsonElement bindingsElement = observation.get(
                        "entryFieldBindings");
                JsonArray bindings = bindingsElement != null
                        && bindingsElement.isJsonArray()
                        ? bindingsElement.getAsJsonArray() : new JsonArray();
                boolean valid = "MAP_ENTRY_READ".equals(string(observation,
                        "kind"))
                        && bool(observation, "complete", false)
                        && !id.isEmpty() && idCounts.get(id) != null
                        && idCounts.get(id) == 1
                        && !statePort.isEmpty()
                        && hasExpression(observation, "keyExpression")
                        && hasExpression(observation, "valueExpression")
                        && authenticatedValueRefWitness(observation,
                        "valueExpression", "valueExpressionAuthority",
                        "valueObjectToken")
                        && !string(observation,
                        "entryBindingAuthority").isEmpty()
                        && bool(observation,
                        "entryValueFieldBindingComplete", false)
                        && bindingsElement != null
                        && bindingsElement.isJsonArray()
                        && bindings.size() > 0;
                boolean canonicalState = ports.contains(statePort);
                if (canonicalState && ports.sort(statePort) != Sort.MAP) {
                    valid = false;
                }
                if (!canonicalState && !declaredStatePorts.contains(
                        statePort)) {
                    valid = false;
                }

                Set<String> fieldSymbols = new LinkedHashSet<>();
                Set<String> fieldSignatures = new LinkedHashSet<>();
                Set<String> dynamicBindingIds = new LinkedHashSet<>();
                Map<String, Sort> pendingAccessorSorts =
                        new LinkedHashMap<>();
                boolean baseOnlyBinding = false;
                for (JsonElement bindingElement : bindings) {
                    if (!bindingElement.isJsonObject()) {
                        valid = false;
                        continue;
                    }
                    JsonObject binding = bindingElement.getAsJsonObject();
                    String fieldSymbol = string(binding, "fieldSymbol");
                    String baseInputSymbol = string(binding,
                            "baseInputSymbol");
                    String dynamicFieldSymbol = string(binding,
                            "dynamicFieldSymbol");
                    String fieldSignature = string(binding, "fieldSignature");
                    String fieldJavaType = string(binding, "fieldJavaType");
                    boolean dynamicBinding = !baseInputSymbol.isEmpty()
                            || !dynamicFieldSymbol.isEmpty()
                            || binding.has("fieldExpression");
                    Sort resultSort;
                    if (dynamicBinding) {
                        JsonElement fieldExpression = binding.get(
                                "fieldExpression");
                        String dynamicBindingId = string(binding,
                                "dynamicBindingId");
                        boolean hasExactExpression = fieldExpression != null
                                && fieldExpression.isJsonObject()
                                && ("SymbolExpression".equals(string(
                                fieldExpression.getAsJsonObject(), "_type"))
                                || "ConSymbolExp".equals(string(
                                fieldExpression.getAsJsonObject(), "_type")));
                        if (!baseInputSymbol.isEmpty()
                                && !hasExactExpression) {
                            baseOnlyBinding = true;
                        }
                        resultSort = sortOfJava(fieldJavaType);
                        if (integer(binding, "schemaVersion", -1) != 1
                                || !"DYNAMIC_MAP_ENTRY_FIELD_BINDING".equals(
                                string(binding, "kind"))
                                || dynamicBindingId.isEmpty()
                                || !dynamicBindingId.equals("DYNAMIC_FIELD:"
                                + dynamicFieldSymbol)
                                || baseInputSymbol.isEmpty()
                                || !ports.contains(baseInputSymbol)
                                || !ports.isInput(baseInputSymbol)
                                || dynamicFieldSymbol.isEmpty()
                                || !dynamicFieldSymbol.startsWith(
                                baseInputSymbol + ".field.")
                                || !dynamicFieldSymbol.endsWith(".occ."
                                + integer(binding,
                                "materializationOccurrence", -1))
                                || !hasExactExpression
                                || !rawSymbolReferences(fieldExpression,
                                dynamicFieldSymbol)
                                || fieldSignature.isEmpty()
                                || fieldJavaType.isEmpty()
                                || array(binding, "fieldPath").size() == 0
                                || string(binding,
                                "materializationSiteId").isEmpty()
                                || integer(binding,
                                "materializationOccurrence", -1) < 1
                                || !id.equals(string(binding,
                                "entryReadObservationId"))
                                || !"FIELD_FAMILY_TEMPLATE_ONLY".equals(
                                string(binding, "baseInputRole"))
                                || !"RUNTIME_DYNAMIC_FIELD_INSTANCE_EXACT_"
                                .concat("EXPRESSION_AND_ENTRY_VALUE_TOKEN_JOIN")
                                .equals(string(binding, "authority"))
                                || resultSort == Sort.VALUE
                                || resultSort == Sort.MAP
                                || !declaredExactFieldDescriptor(
                                fieldSignature).equals(javaTypeDescriptor(
                                fieldJavaType))
                                || !javaTypeDescriptor(fieldJavaType).equals(
                                javaTypeDescriptor(string(
                                fieldExpression.getAsJsonObject(),
                                "_java_type")))
                                || sortOfJava(string(
                                fieldExpression.getAsJsonObject(),
                                "_java_type")) != resultSort
                                || !dynamicBindingIds.add(dynamicBindingId)
                                || !fieldSymbols.add(dynamicFieldSymbol)
                                || !fieldSignatures.add(fieldSignature)) {
                            valid = false;
                            continue;
                        }
                    } else {
                        if (fieldSymbol.isEmpty() || fieldSignature.isEmpty()
                                || fieldJavaType.isEmpty()
                                || !declaredExactFieldDescriptor(
                                fieldSignature).equals(javaTypeDescriptor(
                                fieldJavaType))
                                || !ports.contains(fieldSymbol)
                                || !fieldSymbols.add(fieldSymbol)
                                || !fieldSignatures.add(fieldSignature)) {
                            valid = false;
                            continue;
                        }
                        resultSort = sortOfJava(fieldJavaType);
                    }
                    String accessorIdentity = exactFieldAccessorIdentity(
                            fieldSignature, array(binding, "fieldPath"),
                            resultSort);
                    Sort existing = canonicalFieldAccessorSorts.get(
                            accessorIdentity);
                    Sort pending = pendingAccessorSorts.get(
                            accessorIdentity);
                    if (accessorIdentity.isEmpty()
                            || existing != null && existing != resultSort
                            || pending != null && pending != resultSort) {
                        valid = false;
                    } else {
                        pendingAccessorSorts.put(accessorIdentity, resultSort);
                    }
                }
                if (!valid) {
                    heapGap(region, (baseOnlyBinding
                            ? "BaseOnlyEntryFieldBindingRequiresDynamicExpression@"
                            : "IncompleteOrAmbiguousMapEntryRead@")
                            + region + ":" + firstNonBlank(id,
                            String.valueOf(index)));
                    continue;
                }

                Term key = mapKeyTerm(observation.get("keyExpression"),
                        "heap_observation_" + region + "_" + id);
                if (key == null) {
                    heapGap(region, "MapEntryReadKeyTypeUnsupported@"
                            + region + ":" + id);
                    continue;
                }
                Term valueRef = term(observation.get("valueExpression"),
                        Sort.REF);
                if (valueRef.sort != Sort.REF) {
                    heapGap(region, "MapEntryReadValueIsNotReference@" + region
                            + ":" + id);
                    continue;
                }
                String effectiveStatePort = scopedHeapPort(statePort);
                declarePort(effectiveStatePort, Sort.MAP);
                mentionedPorts.add(effectiveStatePort);
                boundPorts.add(effectiveStatePort);
                assertNamed("heap_observation_key_present_" + id,
                        "(map_has " + portName(effectiveStatePort) + " "
                                + key.text + ")");
                assertNamed("heap_observation_value_" + id,
                        "(= (map_select " + portName(effectiveStatePort) + " "
                                + key.text + ") "
                                + asValue(valueRef).text + ")");
                assertNamed("heap_observation_value_non_null_" + id,
                        "(not (= " + valueRef.text + " nullRef))");

                int bindingIndex = 0;
                for (JsonElement bindingElement : bindings) {
                    JsonObject binding = bindingElement.getAsJsonObject();
                    String fieldSymbol = string(binding, "fieldSymbol");
                    String fieldSignature = string(binding, "fieldSignature");
                    String dynamicFieldSymbol = string(binding,
                            "dynamicFieldSymbol");
                    boolean dynamicBinding = !dynamicFieldSymbol.isEmpty();
                    Sort resultSort = dynamicBinding
                            ? sortOfJava(string(binding, "fieldJavaType"))
                            : sortOfJava(string(binding, "fieldJavaType"));
                    String accessor = canonicalExactFieldAccessor(
                            fieldSignature, array(binding, "fieldPath"),
                            resultSort, "heap observation " + id);
                    if (accessor.isEmpty()) {
                        heapGap(region,
                                "CanonicalExactFieldAccessorGap@" + region
                                        + ":" + id + ":" + fieldSignature);
                        continue;
                    }
                    String fieldValue;
                    if (dynamicBinding) {
                        fieldValue = exactDynamicFieldTerm(
                                binding.getAsJsonObject("fieldExpression"),
                                dynamicFieldSymbol, resultSort).text;
                    } else {
                        Term fieldPort = canonicalPortTerm(fieldSymbol,
                                resultSort);
                        if (fieldPort.sort != resultSort) {
                            heapGap(region,
                                    "HeapObservationFieldPortSortGap@"
                                            + region + ":" + id + ":"
                                            + fieldSymbol);
                            continue;
                        }
                        fieldValue = fieldPort.text;
                    }
                    assertNamed("heap_observation_field_" + id + "_"
                                    + bindingIndex++,
                            "(= (" + accessor + " " + valueRef.text + ") "
                                    + fieldValue + ")");
                    heapObservationFieldBindingCount++;
                }
                heapObservationCount++;
            }
        }

        private void heapInitializer(String region, JsonObject initializer) {
            if (!validMapEmptyInitializer(initializer)) {
                return;
            }
            String rawStatePort = string(initializer, "statePort");
            if (rawStatePort.isEmpty()) {
                return;
            }
            String statePort = scopedHeapPort(rawStatePort);
            declarePort(statePort, Sort.MAP);
            mentionedPorts.add(statePort);
            assertNamed("heap_initializer_" + region + "_"
                            + string(initializer, "initializerId"),
                    "(= " + portName(statePort) + " emptyMapState)");
            boundPorts.add(statePort);
        }

        private boolean validMapEmptyInitializer(JsonObject initializer) {
            String allocationEdge = string(initializer,
                    "allocationEdgeId");
            String family = string(initializer, "stateFamily");
            return "MAP_EMPTY".equals(string(initializer, "kind"))
                    && !string(initializer, "initializerId").isEmpty()
                    && !string(initializer, "statePort").isEmpty()
                    && !family.isEmpty()
                    && (family + ".0").equals(string(initializer, "stateId"))
                    && !string(initializer, "requestedOutputPort").isEmpty()
                    && !string(initializer, "staticInitializerId").isEmpty()
                    && !string(initializer, "allocatedType").isEmpty()
                    && !allocationEdge.isEmpty()
                    && containsString(array(initializer, "proofEdgeIds"),
                    allocationEdge)
                    && bool(initializer, "proofComplete", false)
                    && integer(initializer,
                    "constructorArgumentCount", -1) == 0
                    && "STATIC_UNIQUE_DEFAULT_ALLOCATION_TO_REQUESTED_"
                    .concat("OUTPUT_PLUS_RUNTIME_UNIQUE_MAP_RECEIVER")
                    .equals(string(initializer, "bindingAuthority"))
                    && "JAVA_PLATFORM_DEFAULT_MAP_CONSTRUCTOR_SEMANTICS"
                    .equals(string(initializer, "emptyStateAuthority"));
        }

        private void bindOutputExpressions(String region,
                                           JsonObject summary) {
            JsonObject outputs = object(summary, "outputExpressions");
            for (Map.Entry<String, JsonElement> entry : outputs.entrySet()) {
                String port = entry.getKey();
                if (!ports.contains(port) || !entry.getValue().isJsonObject()) {
                    continue;
                }
                JsonObject expression = entry.getValue().getAsJsonObject();
                String kind = string(expression, "kind");
                if ("EXIT_OBSERVATION".equals(kind)
                        || "HEAP_STATE_VERSION".equals(kind)) {
                    continue;
                }
                boolean arrayExpression = "ArrayValueExpression".equals(
                        string(expression, "_type"));
                if (arrayExpression) {
                    Term value = finiteArrayValue(region, port, expression);
                    if (value != null) bindPort(port, value);
                    continue;
                }
                if (portSort(port) == Sort.ARRAY_VALUE) {
                    heapGap(region, "ArrayValueExpressionRequired@" + region
                            + ":" + port);
                    continue;
                }
                Term value = term(entry.getValue(), null);
                bindPort(port, value);
            }
        }

        /**
         * Consumes the frozen VM finite-array snapshot contract.  Array-valued
         * ports use a dedicated relation sort: treating the snapshot as the
         * scalar {@code Value} carrier would erase both its length and the
         * selected element identities before a recursive read-from edge is
         * emitted.
         */
        private Term finiteArrayValue(String region, String port,
                                      JsonObject expression) {
            List<String> issues = new ArrayList<>();
            if (portSort(port) != Sort.ARRAY_VALUE) {
                issues.add("ARRAY_TO_NON_ARRAY_PORT:" + port + ":"
                        + portSort(port));
            }
            if (integer(expression, "_schema_version", -1) != 1) {
                issues.add("SCHEMA_VERSION_UNSUPPORTED");
            }
            if (!"VM_EXACT_FINITE_ARRAY_VALUE_V1".equals(string(expression,
                    "_authority"))) {
                issues.add("AUTHORITY_INVALID");
            }

            String descriptor = javaTypeDescriptor(string(expression,
                    "_java_type"));
            String component = javaTypeDescriptor(string(expression,
                    "_component_java_type"));
            if (!descriptor.startsWith("[")) {
                issues.add("JAVA_TYPE_NOT_ARRAY");
            } else if (!descriptor.substring(1).equals(component)) {
                issues.add("COMPONENT_TYPE_MISMATCH");
            }
            Port schema = ports.get(port);
            String portDescriptor = schema == null ? ""
                    : javaTypeDescriptor(schema.javaType);
            if (!portDescriptor.isEmpty()
                    && !portDescriptor.equals(descriptor)) {
                issues.add("PORT_JAVA_TYPE_MISMATCH:" + portDescriptor
                        + "!=" + descriptor);
            }

            int length = integer(expression, "_concrete_length", -1);
            JsonElement lengthExpression = expression.get("_length_exp");
            if (length < 0) issues.add("LENGTH_INVALID");
            if (!validFiniteArrayLength(lengthExpression, length)) {
                issues.add("LENGTH_EXPRESSION_INVALID");
            }
            if (!bool(expression, "_elements_complete", false)) {
                issues.add("ELEMENTS_INCOMPLETE");
            }
            JsonElement rawElements = expression.get("_elements");
            JsonArray elements = rawElements != null
                    && rawElements.isJsonArray()
                    ? rawElements.getAsJsonArray() : null;
            if (elements == null) {
                issues.add("ELEMENTS_MISSING");
            } else if (length < 0 || elements.size() != length) {
                issues.add("ELEMENT_COUNT_MISMATCH");
            }

            Set<Integer> indices = new LinkedHashSet<>();
            if (elements != null) {
                for (int ordinal = 0; ordinal < elements.size(); ordinal++) {
                    JsonElement rawElement = elements.get(ordinal);
                    if (!rawElement.isJsonObject()) {
                        issues.add("ELEMENT_MALFORMED:" + ordinal);
                        continue;
                    }
                    JsonObject element = rawElement.getAsJsonObject();
                    int index = integer(element, "index", -1);
                    if (index != ordinal || index < 0 || index >= length
                            || !indices.add(index)) {
                        issues.add("ELEMENT_INDEX_INVALID:" + ordinal);
                    }
                    JsonElement value = element.get("expression");
                    if (value == null || !value.isJsonObject()) {
                        issues.add("ELEMENT_EXPRESSION_MISSING:" + ordinal);
                        continue;
                    }
                    String provenance = string(element, "provenance");
                    if (!validFiniteArrayElementProvenance(provenance,
                            value.getAsJsonObject(), component)) {
                        issues.add("ELEMENT_PROVENANCE_UNSUPPORTED:"
                                + ordinal);
                    }
                    if (!finiteArrayElementTypeCompatible(
                            value.getAsJsonObject(), component)) {
                        issues.add("ELEMENT_TYPE_MISMATCH:" + ordinal);
                    }
                    if (component.startsWith("[")) {
                        issues.add("NESTED_ARRAY_ELEMENT_UNSUPPORTED:"
                                + ordinal);
                    }
                }
            }
            if (!issues.isEmpty()) {
                for (String issue : issues) {
                    heapGap(region, "ArrayValueExpression@" + region + ":"
                            + port + ":" + issue);
                }
                return null;
            }

            Term lengthTerm = term(lengthExpression, Sort.INT);
            if (lengthTerm.sort != Sort.INT) {
                heapGap(region, "ArrayValueExpression@" + region + ":"
                        + port + ":LENGTH_TERM_NOT_INT");
                return null;
            }
            assertNamed("finite_array_length_" + port,
                    "(= " + lengthTerm.text + " " + length + ")");

            String elementArray = "((as const (Array Int Value))"
                    + " (VRef nullRef))";
            // Array component descriptors carry JVM storage semantics.  Every
            // L*/[ component is a reference even when the class happens to be
            // String or a boxed primitive; applying scalar value semantics
            // here would destroy the object identity needed by element-field
            // selectors.
            Sort componentSort = referenceDescriptor(component)
                    ? Sort.REF : sortOfJava(component);
            for (int index = 0; index < elements.size(); index++) {
                JsonObject element = elements.get(index).getAsJsonObject();
                Term value = term(element.get("expression"), componentSort);
                if (value.sort != componentSort
                        || value.sort == Sort.ARRAY_VALUE
                        || value.sort == Sort.ARRAY
                        || value.sort == Sort.MAP
                        || value.sort == Sort.VALUE) {
                    heapGap(region, "ArrayValueExpression@" + region + ":"
                            + port + ":ELEMENT_TERM_SORT_MISMATCH:" + index
                            + ":" + value.sort + "!=" + componentSort);
                    return null;
                }
                elementArray = "(store " + elementArray + " " + index
                        + " " + asValue(value).text + ")";
            }
            return new Term("(mkFiniteArrayValue " + lengthTerm.text + " "
                    + elementArray + ")", Sort.ARRAY_VALUE);
        }

        private boolean validFiniteArrayLength(JsonElement value,
                                               int concreteLength) {
            if (concreteLength < 0 || value == null
                    || !value.isJsonObject()) return false;
            JsonObject expression = value.getAsJsonObject();
            String type = string(expression, "_type");
            if (!("SymbolExpression".equals(type)
                    || "ConSymbolExp".equals(type)
                    || "ConstExpr".equals(type))
                    || !"I".equals(javaTypeDescriptor(string(expression,
                    "_java_type")))) {
                return false;
            }
            if (!"ConstExpr".equals(type)) return true;
            String literal = constantPayload(string(expression, "_exp"));
            try {
                return Integer.parseInt(literal) == concreteLength;
            } catch (NumberFormatException malformed) {
                return false;
            }
        }

        private boolean validFiniteArrayElementProvenance(
                String provenance, JsonObject expression,
                String componentDescriptor) {
            if ("CONCRETE_NULL".equals(provenance)) {
                return referenceDescriptor(componentDescriptor)
                        && "SymbolExpression".equals(string(expression,
                        "_type"))
                        && "N".equals(string(expression, "_exp"));
            }
            if ("CONCRETE_PRIMITIVE".equals(provenance)) {
                return primitiveDescriptor(componentDescriptor)
                        && "ConstExpr".equals(string(expression, "_type"));
            }
            return "ARRAY_SHADOW".equals(provenance)
                    || "SYMBOLIC_ELEMENT".equals(provenance);
        }

        private boolean finiteArrayElementTypeCompatible(
                JsonObject expression, String componentDescriptor) {
            if ("N".equals(string(expression, "_exp"))) {
                return referenceDescriptor(componentDescriptor);
            }
            return componentDescriptor.equals(javaTypeDescriptor(
                    string(expression, "_java_type")));
        }

        /**
         * Closes an exact runtime array selector back to the corresponding
         * symbolic field input.  The backing array remains a finite array
         * value throughout recursive composition; only the selected element
         * is unboxed as a reference for the declared field projection.
         */
        private void bindContainerElementFields(
                String region, JsonObject summary,
                JsonObject requestedOutputSlice) {
            JsonElement declared = requestedOutputSlice.get(
                    "containerElementFieldBindings");
            if (declared == null) return;
            if (!declared.isJsonArray()) {
                heapGap(region, "MalformedContainerElementFieldBindings@"
                        + region);
                return;
            }
            Set<String> requestedInputs = new LinkedHashSet<>();
            for (JsonElement element : array(requestedOutputSlice,
                    "inputPorts")) {
                if (element.isJsonPrimitive()) {
                    requestedInputs.add(element.getAsString());
                }
            }
            Set<String> bindingIds = new LinkedHashSet<>();
            Set<String> basePorts = new LinkedHashSet<>();
            JsonArray bindings = declared.getAsJsonArray();
            for (int ordinal = 0; ordinal < bindings.size(); ordinal++) {
                JsonElement rawBinding = bindings.get(ordinal);
                if (!rawBinding.isJsonObject()) {
                    heapGap(region, "MalformedContainerElementFieldBinding@"
                            + region + ":" + ordinal);
                    continue;
                }
                JsonObject binding = rawBinding.getAsJsonObject();
                String bindingId = firstNonBlank(string(binding,
                        "bindingId"), String.valueOf(ordinal));
                String issue = validateContainerElementFieldBinding(
                        binding, requestedInputs, bindingIds, basePorts);
                if (!issue.isEmpty()) {
                    heapGap(region, "ContainerElementFieldBinding@" + region
                            + ":" + bindingId + ":" + issue);
                    continue;
                }

                ContainerFieldSelector selector = containerFieldSelector(
                        summary, binding);
                if (!selector.complete()) {
                    heapGap(region, "ContainerElementFieldBinding@" + region
                            + ":" + bindingId + ":" + selector.gap);
                    continue;
                }

                String basePort = string(binding, "baseInputSymbol");
                String containerPort = string(binding,
                        "containerInputPort");
                String declaredType = string(binding, "declaredFieldType");
                Sort fieldSort = containerFieldSort(basePort, declaredType);
                Term base = containerFieldPortTerm(basePort, fieldSort);
                if (base == null) {
                    heapGap(region, "ContainerElementFieldBinding@" + region
                            + ":" + bindingId + ":FIELD_PORT_SORT_CONFLICT");
                    continue;
                }

                declarePort(containerPort, Sort.ARRAY_VALUE);
                mentionedPorts.add(containerPort);
                boundPorts.add(containerPort);
                String container = portName(containerPort);
                String selected = "(finite_array_select " + container + " "
                        + selector.index + ")";
                assertNamed("container_index_bounds_" + bindingId,
                        "(and (<= 0 " + selector.index + ") (< "
                                + selector.index + " (finite_array_length "
                                + container + ")))" );
                assertNamed("container_element_is_ref_" + bindingId,
                        "((_ is VRef) " + selected + ")");
                String owner = "(valueRef " + selected + ")";
                assertNamed("container_element_non_null_" + bindingId,
                        "(not (= " + owner + " nullRef))");

                String accessor = canonicalExactFieldAccessor(
                        string(binding, "declaredFieldSignature"),
                        array(binding, "fieldPath"), fieldSort,
                        "container element field " + bindingId);
                if (accessor.isEmpty()) {
                    heapGap(region, "ContainerElementFieldBinding@" + region
                            + ":" + bindingId
                            + ":CANONICAL_FIELD_ACCESSOR_INVALID");
                    continue;
                }
                String projected = "(" + accessor + " " + owner + ")";
                String equality = "(= " + projected + " " + base.text
                        + ")";
                assertNamed("container_element_field_" + bindingId,
                        equality);
                addAutomaticRelationship("container_element_field_"
                                + bindingId,
                        "CONTAINER_ELEMENT_FIELD_BINDING", equality,
                        basePort, projected);

                if (selector.fieldExpression != null) {
                    Term dynamic = exactDynamicFieldTerm(
                            selector.fieldExpression,
                            selector.dynamicFieldSymbol, fieldSort);
                    if (dynamic.sort != fieldSort) {
                        heapGap(region, "ContainerElementFieldBinding@"
                                + region + ":" + bindingId
                                + ":DYNAMIC_FIELD_SORT_CONFLICT");
                        continue;
                    }
                    assertNamed("container_dynamic_field_" + bindingId,
                            "(= " + dynamic.text + " " + base.text + ")");
                }
            }
        }

        /** Emits the finite, same-execution Map-view projection certified by
         * schema-v3 runtime bindings.  Every assertion is emitted while the
         * selected guarded case is active. */
        private void bindMapProjectionElementFields(
                String region, JsonObject item) {
            List<JsonObject> projected = new ArrayList<>();
            for (JsonElement element : array(item,
                    "dynamicFieldBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if ("DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING"
                        .equals(string(binding, "kind"))) {
                    projected.add(binding);
                }
            }
            if (projected.isEmpty()) return;

            Map<String, List<JsonObject>> groups = new LinkedHashMap<>();
            for (JsonObject binding : projected) {
                if (!completeMapProjectionSelector(binding)) {
                    mapProjectionGap(region, "INCOMPLETE_SELECTOR:"
                            + string(binding, "dynamicBindingId"));
                    continue;
                }
                JsonObject selector = object(binding,
                        "mapProjectionSelector");
                String group = string(selector, "mapInputPort") + "\u0000"
                        + string(selector, "mapInputCell") + "\u0000"
                        + string(selector, "outputPort") + "\u0000"
                        + string(selector, "outputCell") + "\u0000"
                        + string(selector, "mapProjectionOperation");
                List<JsonObject> rows = groups.get(group);
                if (rows == null) {
                    rows = new ArrayList<>();
                    groups.put(group, rows);
                }
                rows.add(binding);
            }

            int groupOrdinal = 0;
            for (List<JsonObject> rows : groups.values()) {
                if (rows.isEmpty()) continue;
                JsonObject first = rows.get(0);
                JsonObject firstSelector = object(first,
                        "mapProjectionSelector");
                String mapPort = string(firstSelector, "mapInputPort");
                String mapCell = string(firstSelector, "mapInputCell");
                String outputPort = string(firstSelector, "outputPort");
                String outputCell = string(firstSelector, "outputCell");
                String operation = string(firstSelector,
                        "mapProjectionOperation");
                int count = integer(first,
                        "entrySnapshotElementCount", -1);
                Port mapSchema = ports.get(mapPort);
                Port outputSchema = ports.get(outputPort);
                if (count <= 0
                        || integer(first, "outputElementCount", -1) != count
                        || mapSchema == null || mapSchema.sort != Sort.MAP
                        || !mapCell.equals(mapSchema.cell)
                        || outputSchema == null
                        || outputSchema.sort != Sort.ARRAY_VALUE
                        || !outputCell.equals(outputSchema.cell)) {
                    mapProjectionGap(region,
                            "ENDPOINT_SORT_OR_LENGTH_MISMATCH:"
                                    + mapPort + "->" + outputPort);
                    continue;
                }

                Map<String, Map<Integer, JsonObject>> byDeclaration =
                        new LinkedHashMap<>();
                long[] elementTokens = new long[count];
                JsonElement[] keyExpressions = new JsonElement[count];
                long mapToken = longInteger(firstSelector,
                        "mapObjectToken", 0L);
                long outputToken = longInteger(firstSelector,
                        "outputArrayObjectToken", 0L);
                String scope = string(firstSelector, "objectTokenScope");
                String mapImplementation = string(firstSelector,
                        "mapImplementationClass");
                String mapImplementationAuthority = string(firstSelector,
                        "mapImplementationAuthority");
                boolean valid = mapToken > 0L && outputToken > 0L
                        && !scope.isEmpty()
                        && supportedMapProjectionImplementation(
                        firstSelector);
                for (JsonObject binding : rows) {
                    JsonObject selector = object(binding,
                            "mapProjectionSelector");
                    JsonArray bindingKeys = array(binding,
                            "entrySnapshotMapKeyExpressions");
                    int index = integer(selector, "outputIndex", -1);
                    String declaration = string(selector, "bindingId");
                    valid &= count == integer(binding,
                            "entrySnapshotElementCount", -2)
                            && count == integer(binding,
                            "outputElementCount", -2)
                            && mapPort.equals(string(selector,
                            "mapInputPort"))
                            && mapCell.equals(string(selector,
                            "mapInputCell"))
                            && outputPort.equals(string(selector,
                            "outputPort"))
                            && outputCell.equals(string(selector,
                            "outputCell"))
                            && operation.equals(string(selector,
                            "mapProjectionOperation"))
                            && mapToken == longInteger(selector,
                            "mapObjectToken", -1L)
                            && outputToken == longInteger(selector,
                            "outputArrayObjectToken", -1L)
                            && scope.equals(string(selector,
                            "objectTokenScope"))
                            && mapImplementation.equals(string(selector,
                            "mapImplementationClass"))
                            && mapImplementationAuthority.equals(string(
                            selector, "mapImplementationAuthority"))
                            && bindingKeys.size() == count
                            && "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_"
                            .concat("ENTRYSET_SNAPSHOT").equals(string(
                                    binding, "entryKeyExpressionAuthority"))
                            && "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_"
                            .concat("EXECUTION_POSITIONAL_REFERENCE_EQUALITY")
                            .equals(string(binding,
                                    "entrySetViewOrderAuthority"))
                            && index >= 0 && index < count;
                    Map<Integer, JsonObject> indexed = byDeclaration.get(
                            declaration);
                    if (indexed == null) {
                        indexed = new LinkedHashMap<>();
                        byDeclaration.put(declaration, indexed);
                    }
                    if (indexed.put(index, binding) != null) valid = false;
                    long elementToken = longInteger(selector,
                            "elementObjectToken", 0L);
                    if (index >= 0 && index < count) {
                        if (elementTokens[index] != 0L
                                && elementTokens[index] != elementToken) {
                            valid = false;
                        }
                        elementTokens[index] = elementToken;
                        JsonElement key = selector.get("expectedMapKey");
                        if (key == null || !key.equals(bindingKeys.get(index))
                                || keyExpressions[index] != null
                                && !keyExpressions[index].equals(key)) {
                            valid = false;
                        } else {
                            keyExpressions[index] = key.deepCopy();
                        }
                    }
                }
                Set<Long> distinctTokens = new LinkedHashSet<>();
                for (long token : elementTokens) {
                    valid &= token > 0L && distinctTokens.add(token);
                }
                Set<String> distinctKeys = new LinkedHashSet<>();
                for (JsonElement key : keyExpressions) {
                    String stableKey = stableImmutableMapKeySelector(key);
                    valid &= !stableKey.isEmpty()
                            && distinctKeys.add(stableKey);
                }
                for (Map<Integer, JsonObject> indexed
                        : byDeclaration.values()) {
                    valid &= indexed.size() == count;
                    for (int index = 0; index < count; index++) {
                        valid &= indexed.containsKey(index);
                    }
                }
                if (!valid || byDeclaration.isEmpty()) {
                    mapProjectionGap(region,
                            "INDEX_ORDER_LENGTH_OR_IDENTITY_MISMATCH:"
                                    + mapPort + "->" + outputPort);
                    continue;
                }

                declarePort(mapPort, Sort.MAP);
                declarePort(outputPort, Sort.ARRAY_VALUE);
                mentionedPorts.add(mapPort);
                mentionedPorts.add(outputPort);
                boundPorts.add(mapPort);
                boundPorts.add(outputPort);
                String map = portName(mapPort);
                String output = portName(outputPort);
                String label = "map_projection_" + region + "_"
                        + groupOrdinal++;
                assertNamed(label + "_entry_snapshot_length",
                        "(= (finite_array_length " + output + ") "
                                + count + ")");
                assertNamed(label + "_output_identity_length",
                        "(= (finite_array_length " + output + ") "
                                + integer(first, "outputElementCount", -1)
                                + ")");

                List<String> keys = new ArrayList<>();
                List<String> selectedValues = new ArrayList<>();
                List<String> selectedRefs = new ArrayList<>();
                for (int index = 0; index < count; index++) {
                    Term keyTerm = mapKeyTerm(keyExpressions[index],
                            label + "_key_" + index);
                    if (keyTerm == null) {
                        mapProjectionGap(region,
                                "EXPECTED_MAP_KEY_TERM_SORT_UNSUPPORTED:"
                                        + index);
                        valid = false;
                        break;
                    }
                    String key = keyTerm.text;
                    keys.add(key);
                    String selected = "(finite_array_select " + output
                            + " " + index + ")";
                    String ref = "(valueRef " + selected + ")";
                    selectedValues.add(selected);
                    selectedRefs.add(ref);
                    assertNamed(label + "_selected_ref_" + index,
                            "((_ is VRef) " + selected + ")");
                    assertNamed(label + "_selected_non_null_" + index,
                            "(not (= " + ref + " nullRef))");
                    assertNamed(label + "_key_present_" + index,
                            "(map_has " + map + " " + key + ")");
                    if ("MAP_VALUES_VIEW".equals(operation)) {
                        assertNamed(label + "_value_at_key_" + index,
                                "(= (map_select " + map + " " + key
                                        + ") " + selected + ")");
                    } else {
                        mapProjectionGap(region,
                                "UNSUPPORTED_MAP_PROJECTION_OPERATION:"
                                        + operation);
                        valid = false;
                        break;
                    }
                }
                if (!valid || keys.size() != count) continue;
                if (count > 1) {
                    assertNamed(label + "_keys_distinct",
                            distinct(keys));
                    assertNamed(label + "_selected_values_distinct",
                            distinct(selectedValues));
                    assertNamed(label + "_selected_refs_distinct",
                            distinct(selectedRefs));
                }
                StringBuilder finiteDomain = new StringBuilder(
                        "(forall ((q Value)) (= (map_has ")
                        .append(map).append(" q) (or");
                for (String key : keys) {
                    finiteDomain.append(" (= q ").append(key).append(')');
                }
                finiteDomain.append(")))");
                assertNamed(label + "_finite_map_domain",
                        finiteDomain.toString());

                for (JsonObject binding : rows) {
                    JsonObject selector = object(binding,
                            "mapProjectionSelector");
                    int index = integer(selector, "outputIndex", -1);
                    Sort fieldSort = sortOfJava(string(binding,
                            "fieldJavaType"));
                    String signature = string(binding, "fieldSignature");
                    if (fieldSort == Sort.VALUE || fieldSort == Sort.MAP
                            || fieldSort == Sort.ARRAY_VALUE
                            || !declaredExactFieldDescriptor(signature)
                            .equals(javaTypeDescriptor(string(binding,
                                    "fieldJavaType")))) {
                        mapProjectionGap(region,
                                "DYNAMIC_FIELD_TYPE_MISMATCH:"
                                        + string(binding,
                                        "dynamicBindingId"));
                        continue;
                    }
                    String accessor = canonicalExactFieldAccessor(signature,
                            array(binding, "fieldPath"), fieldSort,
                            "map projection " + string(binding,
                                    "dynamicBindingId"));
                    Term dynamic = authorizedRuntimeDynamicFieldTerm(
                            binding, fieldSort);
                    if (accessor.isEmpty() || dynamic.sort != fieldSort) {
                        mapProjectionGap(region,
                                "CANONICAL_FIELD_OR_TERM_GAP:"
                                        + string(binding,
                                        "dynamicBindingId"));
                        continue;
                    }
                    String equality = "(= (" + accessor + " "
                            + selectedRefs.get(index) + ") "
                            + dynamic.text + ")";
                    assertNamed(label + "_field_" + string(selector,
                            "bindingId") + "_" + index, equality);
                    addAutomaticRelationship(label + "_field_"
                                    + string(selector, "bindingId") + "_"
                                    + index,
                            "MAP_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING",
                            equality, mapPort, dynamic.text);
                }
            }
        }

        private void mapProjectionGap(String region, String detail) {
            heapGap(region, "MapProjectionElementField@" + region + ":"
                    + detail);
            if (currentCaseProjection != null) {
                currentCaseProjection.gap("MAP_PROJECTION:" + detail);
            }
        }

        private static String distinct(List<String> terms) {
            StringBuilder result = new StringBuilder("(distinct");
            for (String term : terms) result.append(' ').append(term);
            return result.append(')').toString();
        }

        /**
         * Returns the one global accessor for an exact declared Java field.
         * Runtime map-entry observations and finite-array element projections
         * intentionally meet here: using emitter-specific UF families would
         * sever object-field identity across recursively composed regions.
         */
        private String canonicalExactFieldAccessor(
                String signature, JsonArray fieldPath, Sort resultSort,
                String origin) {
            String identity = normalizedExactFieldIdentity(signature,
                    fieldPath);
            Sort declaredSort = declaredExactFieldSort(signature);
            if (identity.isEmpty() || declaredSort == null
                    || declaredSort != resultSort) {
                unsupported.add("CanonicalExactFieldAccessorIdentity:"
                        + origin + ":" + firstNonBlank(signature,
                        "<missing>") + ":" + resultSort);
                return "";
            }
            Sort previousSort = canonicalFieldAccessorSorts.get(identity);
            if (previousSort != null && previousSort != resultSort) {
                unsupported.add("CanonicalExactFieldAccessorSortConflict:"
                        + origin + ":" + identity + ":" + previousSort
                        + "!=" + resultSort);
                return "";
            }
            canonicalFieldAccessorSorts.put(identity, resultSort);
            String key = identity + "\u0000" + resultSort.name();
            String accessor = canonicalFieldAccessors.get(key);
            if (accessor == null) {
                accessor = "exact_field__" + scopeToken(key);
                canonicalFieldAccessors.put(key, accessor);
                declareFunction(accessor, Collections.singletonList(
                        new Term("", Sort.REF)), resultSort);
            }
            return accessor;
        }

        private String exactFieldAccessorIdentity(
                String signature, JsonArray fieldPath, Sort resultSort) {
            String identity = normalizedExactFieldIdentity(signature,
                    fieldPath);
            Sort declaredSort = declaredExactFieldSort(signature);
            return !identity.isEmpty() && declaredSort == resultSort
                    ? identity : "";
        }

        private String normalizedExactFieldIdentity(
                String signature, JsonArray fieldPath) {
            Matcher field = Pattern.compile(
                    "^<([^:]+):\\s+([^\\s]+)\\s+([^\\s()>]+)>$")
                    .matcher(firstNonBlank(signature));
            if (!field.matches() || fieldPath == null
                    || fieldPath.size() == 0) {
                return "";
            }
            JsonArray normalizedPath = new JsonArray();
            for (JsonElement element : fieldPath) {
                if (!element.isJsonPrimitive()
                        || !element.getAsJsonPrimitive().isString()
                        || element.getAsString().isEmpty()) {
                    return "";
                }
                normalizedPath.add(element.getAsString());
            }
            if (!field.group(3).equals(normalizedPath.get(
                    normalizedPath.size() - 1).getAsString())) {
                return "";
            }
            String owner = field.group(1).replace('.', '/');
            String descriptor = javaTypeDescriptor(field.group(2));
            if (owner.isEmpty() || descriptor.isEmpty()) return "";
            return owner + "\u0000" + descriptor + "\u0000"
                    + field.group(3) + "\u0000"
                    + GSON.toJson(normalizedPath);
        }

        private Sort declaredExactFieldSort(String signature) {
            Matcher field = Pattern.compile(
                    "^<([^:]+):\\s+([^\\s]+)\\s+([^\\s()>]+)>$")
                    .matcher(firstNonBlank(signature));
            if (!field.matches()) return null;
            String type = field.group(2);
            return isMapType(type) ? Sort.MAP : sortOfJava(type);
        }

        private String declaredExactFieldDescriptor(String signature) {
            Matcher field = Pattern.compile(
                    "^<([^:]+):\\s+([^\\s]+)\\s+([^\\s()>]+)>$")
                    .matcher(firstNonBlank(signature));
            return field.matches() ? javaTypeDescriptor(field.group(2)) : "";
        }

        private String validateContainerElementFieldBinding(
                JsonObject binding, Set<String> requestedInputs,
                Set<String> bindingIds, Set<String> basePorts) {
            String id = string(binding, "bindingId");
            String base = string(binding, "baseInputSymbol");
            String container = string(binding, "containerInputPort");
            if (integer(binding, "schemaVersion", -1) != 1
                    || !"ARRAY_ELEMENT_FIELD".equals(string(binding,
                    "kind")) || !bool(binding, "complete", false)) {
                return "INCOMPLETE_OR_UNSUPPORTED_SCHEMA";
            }
            if (id.isEmpty() || !bindingIds.add(id)) {
                return "MISSING_OR_DUPLICATE_BINDING_ID";
            }
            if (base.isEmpty() || container.isEmpty()
                    || base.equals(container) || !basePorts.add(base)) {
                return "AMBIGUOUS_INPUT_PORTS";
            }
            if (!ports.contains(base) || !ports.isInput(base)
                    || !ports.contains(container) || !ports.isInput(container)
                    || !requestedInputs.contains(base)
                    || !requestedInputs.contains(container)) {
                return "INPUT_PORT_NOT_IN_EXACT_REQUESTED_SLICE";
            }
            Port containerSchema = ports.get(container);
            if (containerSchema == null
                    || portSort(container) != Sort.ARRAY_VALUE
                    || !string(binding, "containerInputCell").equals(
                    containerSchema.cell)) {
                return "CONTAINER_PORT_TYPE_OR_CELL_MISMATCH";
            }
            String containerDescriptor = javaTypeDescriptor(
                    containerSchema.javaType);
            if (!containerDescriptor.startsWith("[")
                    || !referenceDescriptor(containerDescriptor.substring(1))) {
                return "CONTAINER_ELEMENT_IS_NOT_REFERENCE_TYPED";
            }

            String selector = string(binding, "selectorAuthority");
            int index = integer(binding, "elementIndex", -2);
            int occurrence = integer(binding, "elementOccurrence", -2);
            boolean exact = "EXACT_ARRAY_INDEX".equals(selector)
                    && index >= 0 && occurrence > 0;
            boolean discovery = "DISCOVER_UNIQUE_IDENTITY_INDEX".equals(
                    selector) && index == -1 && occurrence == -1;
            if (!exact && !discovery) {
                return "SELECTOR_INCOMPLETE";
            }

            JsonArray path = array(binding, "fieldPath");
            String signature = string(binding, "declaredFieldSignature");
            Matcher field = Pattern.compile(
                    "^<([^:]+):\\s+([^\\s]+)\\s+([^\\s()>]+)>$")
                    .matcher(signature);
            if (!field.matches() || path.size() == 0
                    || !path.get(path.size() - 1).isJsonPrimitive()
                    || !field.group(1).replace('/', '.').equals(
                    string(binding, "declaredFieldOwnerClass")
                            .replace('/', '.'))
                    || !javaTypeDescriptor(field.group(2)).equals(
                    javaTypeDescriptor(string(binding,
                            "declaredFieldType")))
                    || !field.group(3).equals(string(binding,
                    "declaredFieldName"))
                    || !field.group(3).equals(path.get(path.size() - 1)
                    .getAsString())) {
                return "DECLARED_FIELD_IDENTITY_MISMATCH";
            }
            Port baseSchema = ports.get(base);
            String baseDescriptor = baseSchema == null ? ""
                    : javaTypeDescriptor(baseSchema.javaType);
            if (!baseDescriptor.isEmpty() && !baseDescriptor.equals(
                    javaTypeDescriptor(field.group(2)))) {
                return "BASE_PORT_FIELD_TYPE_MISMATCH";
            }
            JsonArray proof = array(binding, "proofCausalEdgeIds");
            Set<String> proofIds = new LinkedHashSet<>();
            for (JsonElement element : proof) {
                if (element.isJsonPrimitive()
                        && !element.getAsString().isEmpty()) {
                    proofIds.add(element.getAsString());
                }
            }
            if (proof.size() != 4 || proofIds.size() != 4
                    || string(binding, "method").isEmpty()
                    || string(binding, "fieldMaterializationSiteId").isEmpty()
                    || string(binding, "arrayLoadSiteId").isEmpty()
                    || !"STATIC_EXACT_CONTAINER_ARRAY_ACCESSOR_DECLARED_"
                    .concat("FIELD_FOUR_EDGE_JOIN_V1").equals(
                            string(binding, "proofAuthority"))) {
                return "STATIC_FOUR_EDGE_PROOF_INCOMPLETE";
            }
            return "";
        }

        private ContainerFieldSelector containerFieldSelector(
                JsonObject summary, JsonObject declaration) {
            String id = string(declaration, "bindingId");
            String base = string(declaration, "baseInputSymbol");
            String container = string(declaration, "containerInputPort");
            List<JsonObject> matches = new ArrayList<>();
            for (JsonElement element : array(summary,
                    "dynamicFieldBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                JsonObject selector = object(binding, "containerSelector");
                String runtimeId = firstNonBlank(string(binding,
                        "containerBindingId"), string(selector, "bindingId"));
                if ("DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(
                        string(binding, "kind"))
                        && id.equals(runtimeId)
                        && base.equals(string(binding, "baseInputSymbol"))
                        && container.equals(string(selector,
                        "containerInputPort"))) {
                    matches.add(binding);
                }
            }
            String declaredAuthority = string(declaration,
                    "selectorAuthority");
            if (matches.isEmpty()) {
                return "EXACT_ARRAY_INDEX".equals(declaredAuthority)
                        ? ContainerFieldSelector.complete(integer(declaration,
                        "elementIndex", -1), "", null)
                        : ContainerFieldSelector.gap(
                        "RUNTIME_SELECTOR_RESOLUTION_MISSING");
            }
            if (matches.size() != 1) {
                return ContainerFieldSelector.gap(
                        "RUNTIME_SELECTOR_RESOLUTION_AMBIGUOUS");
            }
            JsonObject runtime = matches.get(0);
            JsonObject selector = object(runtime, "containerSelector");
            String resolvedFrom = string(selector,
                    "resolvedFromSelectorAuthority");
            int runtimeOccurrence = integer(selector,
                    "elementOccurrence", -1);
            String activationId = string(summary, "activationId");
            if (integer(runtime, "schemaVersion", -1) != 2
                    || !bool(runtime, "complete", false)
                    || !completeContainerSelector(runtime)
                    || activationId.isEmpty()
                    || !activationId.equals(string(runtime,
                    "objectTokenScope"))
                    || !activationId.equals(string(selector,
                    "objectTokenScope"))
                    || !"ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_"
                    .concat("IDENTITY_AND_STABLE_FIELD_SITE_OCCURRENCE")
                    .equals(string(runtime, "authority"))
                    || !string(declaration, "declaredFieldSignature").equals(
                    string(runtime, "fieldSignature"))
                    || !array(declaration, "fieldPath").equals(
                    array(runtime, "fieldPath"))
                    || !string(declaration,
                    "fieldMaterializationSiteId").equals(string(runtime,
                    "materializationSiteId"))
                    || !string(declaration, "containerInputCell").equals(
                    string(selector, "containerInputCell"))
                    || !string(declaration,
                    "declaredFieldOwnerClass").replace('/', '.').equals(
                    string(selector,
                    "declaredFieldOwnerClass").replace('/', '.'))
                    || !javaTypeDescriptor(string(declaration,
                    "declaredFieldType")).equals(javaTypeDescriptor(
                    string(selector, "declaredFieldType")))
                    || (!resolvedFrom.isEmpty()
                    && !declaredAuthority.equals(resolvedFrom))) {
                return ContainerFieldSelector.gap(
                        "RUNTIME_SELECTOR_IDENTITY_MISMATCH");
            }
            int index = integer(selector, "elementIndex", -1);
            if ("EXACT_ARRAY_INDEX".equals(declaredAuthority)
                    && (index != integer(declaration, "elementIndex", -2)
                    || runtimeOccurrence != integer(declaration,
                    "elementOccurrence", -2))) {
                return ContainerFieldSelector.gap(
                        "STATIC_RUNTIME_INDEX_MISMATCH");
            }
            String dynamic = string(runtime, "dynamicFieldSymbol");
            List<JsonObject> expressions = new ArrayList<>();
            Set<String> seen = new LinkedHashSet<>();
            JsonElement explicit = runtime.get("fieldExpression");
            if (explicit != null && explicit.isJsonObject()
                    && rawSymbolReferences(explicit, dynamic)) {
                expressions.add(explicit.getAsJsonObject());
                seen.add(GSON.toJson(explicit));
            }
            JsonElement conditions = summary.has("guard")
                    ? object(summary, "guard").get("conditions")
                    : summary.get("pathCondition");
            collectExactDynamicExpressions(conditions, dynamic, expressions,
                    seen);
            if (dynamic.isEmpty() || expressions.size() != 1) {
                return ContainerFieldSelector.gap(expressions.isEmpty()
                        ? "DYNAMIC_FIELD_EXPRESSION_MISSING"
                        : "DYNAMIC_FIELD_EXPRESSION_AMBIGUOUS");
            }
            String declaredDescriptor = javaTypeDescriptor(string(
                    declaration, "declaredFieldType"));
            String expressionDescriptor = javaTypeDescriptor(string(
                    expressions.get(0), "_java_type"));
            if (!declaredDescriptor.equals(expressionDescriptor)) {
                return ContainerFieldSelector.gap(
                        "DYNAMIC_FIELD_EXPRESSION_TYPE_MISMATCH");
            }
            return ContainerFieldSelector.complete(index, dynamic,
                    expressions.get(0));
        }

        private Sort containerFieldSort(String basePort,
                                        String declaredType) {
            Sort carrier = portSort(basePort);
            if (carrier == Sort.MAP) {
                return isMapType(declaredType) ? Sort.MAP : Sort.VALUE;
            }
            return sortOfJava(declaredType);
        }

        private Term containerFieldPortTerm(String port, Sort fieldSort) {
            Sort carrier = portSort(port);
            if (carrier == Sort.VALUE && fieldSort != Sort.VALUE
                    && fieldSort != Sort.MAP
                    && fieldSort != Sort.ARRAY_VALUE
                    && fieldSort != Sort.ARRAY) {
                return canonicalPortTerm(port, fieldSort);
            }
            if (carrier == fieldSort
                    && (carrier == Sort.MAP
                    || carrier == Sort.ARRAY_VALUE)) {
                declarePort(port, carrier);
                mentionedPorts.add(port);
                boundPorts.add(port);
                return new Term(portName(port), carrier);
            }
            return null;
        }

        /**
         * A Runtime token witness is evidence, not custom-JDK symbolic state.
         * Only the importer can authorize it after joining the same activation
         * token to the dynamic field's leaf owner.  The ordinary symbol path
         * then adds the selected summary/path-case scope on top of the
         * activation already encoded in the raw witness name.
         */
        private static boolean authenticatedValueRefWitness(
                JsonObject record, String expressionField,
                String authorityField, String objectTokenField) {
            JsonElement expressionElement = record.get(expressionField);
            if (expressionElement == null || !expressionElement.isJsonObject()) {
                return false;
            }
            JsonObject expression = expressionElement.getAsJsonObject();
            String raw = string(expression, "_exp");
            String authority = string(record, authorityField);
            if (!VALUE_REF_WITNESS_AUTHORITY.equals(authority)) {
                // Do not permit a witness-shaped symbol to bypass the gate by
                // deleting or relabeling its explicit Runtime authority.
                return !raw.startsWith(VALUE_REF_WITNESS_SYMBOL_PREFIX);
            }
            long token = jsonLong(record.get(objectTokenField), 0L);
            long witnessToken = jsonLong(record.get(
                    "valueExpressionWitnessObjectToken"), 0L);
            long certifiedToken = jsonLong(record.get(
                    "valueExpressionWitnessCertifiedObjectToken"), 0L);
            String scope = string(record,
                    "valueExpressionWitnessObjectTokenScope");
            return token > 0L && witnessToken == token
                    && certifiedToken == token
                    && integer(record,
                    "valueExpressionWitnessSchemaVersion", -1) == 1
                    && VALUE_REF_WITNESS_KIND.equals(string(record,
                    "valueExpressionWitnessKind"))
                    && VALUE_REF_WITNESS_TOKEN_AUTHORITY.equals(string(record,
                    "valueExpressionWitnessAuthority"))
                    && bool(record, "valueExpressionWitnessCertified", false)
                    && VALUE_REF_WITNESS_CERTIFICATION_AUTHORITY.equals(string(
                    record, "valueExpressionWitnessCertificationAuthority"))
                    && !scope.isEmpty()
                    && scope.equals(string(record, "objectTokenScope"))
                    && scope.equals(string(record,
                    "valueExpressionWitnessCertifiedObjectTokenScope"))
                    && "SymbolExpression".equals(string(expression, "_type"))
                    && "L".equals(string(expression, "_java_type"))
                    && valueRefWitnessSymbol(scope, token).equals(raw);
        }

        private static String valueRefWitnessSymbol(String activationId,
                                                    long objectToken) {
            byte[] bytes = firstNonBlank(activationId, "")
                    .getBytes(StandardCharsets.UTF_8);
            StringBuilder hex = new StringBuilder(bytes.length * 2);
            for (byte value : bytes) {
                int unsigned = value & 0xff;
                hex.append(Character.forDigit(unsigned >>> 4, 16));
                hex.append(Character.forDigit(unsigned & 0x0f, 16));
            }
            return VALUE_REF_WITNESS_SYMBOL_PREFIX + hex.length() + "_" + hex
                    + "_T" + objectToken;
        }

        private void heapEffect(String region, JsonObject effect) {
            String kind = string(effect, "kind");
            String rawInput = string(effect, "inputPort");
            String rawOutput = string(effect, "outputPort");
            if (rawInput.isEmpty() || rawOutput.isEmpty()) {
                heapGap(region,
                        "HeapEffectWithoutPorts:" + kind + "@" + region);
                return;
            }
            String input = scopedHeapPort(rawInput);
            String output = scopedHeapPort(rawOutput);
            declarePort(input, Sort.MAP);
            declarePort(output, Sort.MAP);
            mentionedPorts.add(input);
            mentionedPorts.add(output);
            // The semantic effect consumes the pre-state port directly; no
            // separate engine-symbol binding is required for that free input.
            boundPorts.add(input);
            String rhs;
            if ("MAP_PUT".equals(kind)) {
                if (!hasExpression(effect, "keyExpression")
                        || !hasExpression(effect, "valueExpression")
                        || !authenticatedValueRefWitness(effect,
                        "valueExpression", "valueExpressionAuthority",
                        "valueObjectToken")) {
                    heapGap(region, "MalformedHeapEffect:" + kind + "@"
                            + region);
                    return;
                }
                Term key = mapKeyTerm(effect.get("keyExpression"),
                        "heap_effect_" + region + "_" + kind);
                if (key == null) {
                    heapGap(region, "HeapEffectKeyTypeUnsupported:" + kind
                            + "@" + region);
                    return;
                }
                Term value = asValue(term(effect.get("valueExpression"), null));
                rhs = "(map_put " + portName(input) + " " + key.text
                        + " " + value.text + ")";
            } else if ("MAP_REMOVE".equals(kind)) {
                if (!hasExpression(effect, "keyExpression")) {
                    heapGap(region, "MalformedHeapEffect:" + kind + "@"
                            + region);
                    return;
                }
                Term key = mapKeyTerm(effect.get("keyExpression"),
                        "heap_effect_" + region + "_" + kind);
                if (key == null) {
                    heapGap(region, "HeapEffectKeyTypeUnsupported:" + kind
                            + "@" + region);
                    return;
                }
                if (bool(effect, "requiresKeyPresent", false)
                        && hasExpression(effect, "removedValueExpression")
                        && !string(effect, "entryBindingAuthority").isEmpty()
                        && !string(effect, "valueBindingAuthority").isEmpty()) {
                    if (!authenticatedValueRefWitness(effect,
                            "removedValueExpression",
                            "removedValueExpressionAuthority",
                            "entryValueObjectToken")) {
                        heapGap(region,
                                "UnauthenticatedRemovedValueRefWitness@"
                                        + region + ":" + firstNonBlank(
                                        string(effect, "effectId"), kind));
                    } else {
                        Term removedValue = asValue(term(
                                effect.get("removedValueExpression"), null));
                        String suffix = firstNonBlank(string(effect,
                                "effectId"), region + "_" + assertionCount);
                        assertNamed("heap_remove_key_present_" + suffix,
                                "(map_has " + portName(input) + " "
                                        + key.text + ")");
                        assertNamed("heap_remove_value_binding_" + suffix,
                                "(= (map_select " + portName(input) + " "
                                        + key.text + ") "
                                        + removedValue.text + ")");
                    }
                }
                rhs = "(map_remove " + portName(input) + " "
                        + key.text + ")";
            } else if ("MAP_CLEAR".equals(kind)) {
                rhs = "(map_clear " + portName(input) + ")";
            } else if ("MAP_IDENTITY".equals(kind)) {
                rhs = portName(input);
            } else if ("MAP_PUT_ALL".equals(kind)) {
                if (!hasExpression(effect, "sourceExpression")) {
                    heapGap(region, "MalformedHeapEffect:" + kind + "@"
                            + region);
                    return;
                }
                Term source = mapState(effect.get("sourceExpression"));
                rhs = "(map_put_all " + portName(input) + " "
                        + source.text + ")";
            } else {
                heapGap(region, "HeapEffect:" + kind);
                return;
            }
            assertNamed("heap_effect_" + region + "_" + assertionCount,
                    "(= " + portName(output) + " " + rhs + ")");
            boundPorts.add(output);
        }

        private boolean hasExpression(JsonObject effect, String field) {
            JsonElement expression = effect.get(field);
            return expression != null && expression.isJsonObject();
        }

        private boolean containsString(JsonArray values, String expected) {
            for (JsonElement value : values) {
                if (value.isJsonPrimitive()
                        && expected.equals(value.getAsString())) {
                    return true;
                }
            }
            return false;
        }

        private void heapGap(String region, String detail) {
            incompleteSummaries.add(region);
            unsupported.add(detail);
        }

        private MergeStats merge(JsonObject context,
                                 Set<String> relevantRegions) {
            MergeStats stats = new MergeStats();
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
                    if (assertPortEquality(first,
                            selected.get(index),
                            "alias_" + stats.equalities)) {
                        stats.equalities++;
                    }
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
                if (assertPortEquality(from, to,
                        "read_from_" + stats.readFrom)) {
                    stats.readFrom++;
                }
                JsonArray bindings = selectedBindings(relation);
                for (int index = 0; index < bindings.size(); index++) {
                    JsonObject binding = bindings.get(index).getAsJsonObject();
                    if (!bool(binding, "orderConfirmed", false)) continue;
                    String write = "event_write_" + smtName(firstNonBlank(
                            string(relation, "edgeId"), "edge")) + "_" + index;
                    String read = "event_read_" + smtName(firstNonBlank(
                            string(relation, "edgeId"), "edge")) + "_" + index;
                    declare(write, Sort.INT);
                    declare(read, Sort.INT);
                    if (binding.has("writeSeq")) assertNamed(write + "_seq",
                            "(= " + write + " "
                                    + integer(binding, "writeSeq", 0) + ")");
                    if (binding.has("readSeq")) assertNamed(read + "_seq",
                            "(= " + read + " "
                                    + integer(binding, "readSeq", 0) + ")");
                    assertNamed("order_" + stats.orders,
                            "(< " + write + " " + read + ")");
                    stats.orders++;
                }
            }
            for (JsonElement element : array(context,
                    "alternativeWriterGroups")) {
                if (!element.isJsonObject()) continue;
                JsonObject group = element.getAsJsonObject();
                JsonArray alternatives = array(group, "alternatives");
                String groupId = firstNonBlank(string(group, "groupId"),
                        "alternative-" + stats.alternativeWriterGroups);
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
                    String to = firstNonBlank(string(relation, "toEndpoint"),
                            firstNonBlank(string(group,
                                    "downstreamEndpoint"), string(group,
                                    "consumerEndpoint")));
                    if (!relevantRegions.contains(regionOf(from))
                            || !relevantRegions.contains(regionOf(to))) {
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
                    stats.readFrom++;
                    stats.guardedAlternatives++;
                    guardedRuntimeEvidence(relation, groupId, index, guard,
                            stats);
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
                stats.alternativeWriterGroups++;
            }
            return stats;
        }

        private boolean assertGuardedPortEquality(String left, String right,
                                                  String guard,
                                                  String label) {
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
            assertNamed(label, "(=> " + guard + " (= " + portName(left)
                    + " " + portName(right) + "))");
            portEqualities.add(new String[]{left, right});
            return true;
        }

        private void guardedRuntimeEvidence(JsonObject relation,
                                            String groupId, int alternative,
                                            String guard, MergeStats stats) {
            JsonArray bindings = selectedBindings(relation);
            boolean requiresOrder = bool(relation, "requiresOrder", true);
            boolean requiresIdentity = bool(relation,
                    "requiresObjectIdentity", true);
            if (bindings.size() == 0 && (requiresOrder || requiresIdentity)) {
                unsupported.add("MissingAlternativeWriterEvidence:"
                        + groupId + ":" + alternative);
                return;
            }
            for (int index = 0; index < bindings.size(); index++) {
                if (!bindings.get(index).isJsonObject()) continue;
                JsonObject binding = bindings.get(index).getAsJsonObject();
                String suffix = smtName(groupId) + "_" + alternative + "_"
                        + index;
                if (requiresOrder) {
                    if (!bool(binding, "orderConfirmed", false)
                            || !binding.has("writeSeq")
                            || !binding.has("readSeq")) {
                        unsupported.add("AlternativeWriterOrderGap:"
                                + groupId + ":" + alternative + ":" + index);
                    } else {
                        String write = "event_write_alt_" + suffix;
                        String read = "event_read_alt_" + suffix;
                        declare(write, Sort.INT);
                        declare(read, Sort.INT);
                        assertNamed(write + "_seq", "(= " + write + " "
                                + integer(binding, "writeSeq", 0) + ")");
                        assertNamed(read + "_seq", "(= " + read + " "
                                + integer(binding, "readSeq", 0) + ")");
                        assertNamed("order_alt_" + suffix, "(=> " + guard
                                + " (< " + write + " " + read + "))");
                        stats.orders++;
                    }
                }
                if (requiresIdentity) {
                    int receiver = integer(binding, "receiverObjectId", 0);
                    if (receiver == 0
                            || (binding.has("objectIdentityConfirmed")
                            && !bool(binding, "objectIdentityConfirmed",
                            false))) {
                        unsupported.add("AlternativeWriterIdentityGap:"
                                + groupId + ":" + alternative + ":" + index);
                    } else {
                        String writer = "receiver_write_alt_" + suffix;
                        String reader = "receiver_read_alt_" + suffix;
                        declare(writer, Sort.INT);
                        declare(reader, Sort.INT);
                        assertNamed(writer + "_id", "(= " + writer + " "
                                + receiver + ")");
                        assertNamed(reader + "_id", "(= " + reader + " "
                                + receiver + ")");
                        assertNamed("identity_alt_" + suffix, "(=> " + guard
                                + " (= " + writer + " " + reader + "))");
                        stats.identities++;
                    }
                }
            }
        }

        private MergeStats mergeEdgeBindings(
                List<ResolvedEdge> edges, Set<String> relevantRegions) {
            MergeStats stats = new MergeStats();
            int edgeIndex = 0;
            for (ResolvedEdge edge : edges) {
                String region = edge.source.regionId;
                if (!relevantRegions.contains(region)
                        || !relevantRegions.contains(edge.targetRegion)) {
                    continue;
                }
                JsonObject binding = edge.binding;
                JsonObject summary = edge.summary;
                String output = bindingSourceOutput(binding);
                String input = bindingTargetInput(binding);
                String label = "edge_binding_" + region + "_to_"
                        + edge.targetRegion + "_" + edgeIndex++;
                if (!edgeBindingSourceMatches(binding, summary)
                        || !edge.source.instanceId.equals(
                        bindingSourceInstance(binding))) {
                    heapGap(region, "EdgeBindingSourceInstanceGap@"
                            + region + ":" + output + "->" + input);
                    continue;
                }
                if (!edge.targetInstance.equals(bindingTargetInstance(binding))) {
                    heapGap(region, "EdgeBindingTargetInstanceGap@"
                            + region + ":" + output + "->" + input);
                    continue;
                }
                if (!region.equals(regionOf(output))
                        || !edge.targetRegion.equals(regionOf(input))
                        || !edge.source.outputPort.equals(output)
                        || !edge.targetInput.equals(input)
                        || !ports.contains(output) || !ports.contains(input)) {
                    heapGap(region, "EdgeBindingPortGap@" + region
                            + ":" + output + "->" + input);
                    continue;
                }
                if (!trustedRuntimeReadFrom(binding)) {
                    heapGap(region, "EdgeBindingAuthorityGap@" + region
                            + ":" + output + "->" + input);
                    continue;
                }
                if (!bool(binding, "orderConfirmed", false)) {
                    heapGap(region, "EdgeBindingOrderGap@" + region
                            + ":" + output + "->" + input);
                    continue;
                }
                if (!bool(binding, "objectIdentityConfirmed", false)) {
                    heapGap(region, "EdgeBindingIdentityGap@" + region
                            + ":" + output + "->" + input);
                    continue;
                }
                int writeSeq = firstInteger(binding, "writerEventSeq",
                        "writeSeq", Integer.MIN_VALUE);
                int readSeq = firstInteger(binding, "readerEventSeq",
                        "readSeq", Integer.MIN_VALUE);
                int receiver = integer(binding, "receiverObjectId", 0);
                if (writeSeq == Integer.MIN_VALUE
                        || readSeq == Integer.MIN_VALUE
                        || writeSeq >= readSeq) {
                    heapGap(region, "EdgeBindingSequenceGap@" + region
                            + ":" + output + "->" + input);
                    continue;
                }
                if (receiver == 0) {
                    heapGap(region, "EdgeBindingIdentityGap@" + region
                            + ":zero-receiver");
                    continue;
                }
                if (!assertPortEquality(output, input, label)) {
                    heapGap(region, "EdgeBindingEqualityGap@" + region
                            + ":" + output + "->" + input);
                    continue;
                }
                stats.readFrom++;
                stats.edgeBindings++;

                String write = "event_write_" + smtName(label);
                String read = "event_read_" + smtName(label);
                declare(write, Sort.INT);
                declare(read, Sort.INT);
                assertNamed(write + "_seq", "(= " + write + " "
                        + writeSeq + ")");
                assertNamed(read + "_seq", "(= " + read + " "
                        + readSeq + ")");
                assertNamed("order_" + label,
                        "(< " + write + " " + read + ")");
                stats.orders++;

                String writerReceiver = "receiver_write_"
                        + smtName(label);
                String readerReceiver = "receiver_read_"
                        + smtName(label);
                declare(writerReceiver, Sort.INT);
                declare(readerReceiver, Sort.INT);
                assertNamed(writerReceiver + "_id", "(= "
                        + writerReceiver + " " + receiver + ")");
                assertNamed(readerReceiver + "_id", "(= "
                        + readerReceiver + " " + receiver + ")");
                assertNamed("identity_" + label, "(= "
                        + writerReceiver + " " + readerReceiver + ")");
                stats.identities++;
            }
            return stats;
        }

        private void finishBindings() {
            boolean changed = true;
            while (changed) {
                changed = false;
                for (String[] equality : portEqualities) {
                    if (boundPorts.contains(equality[0])) {
                        changed |= boundPorts.add(equality[1]);
                    }
                    if (boundPorts.contains(equality[1])) {
                        changed |= boundPorts.add(equality[0]);
                    }
                }
            }
            for (String port : mentionedPorts) {
                if (!boundPorts.contains(port) && ports.isInput(port)) {
                    unboundPorts.add(port);
                }
            }
        }

        private JsonArray selectedBindings(JsonObject relation) {
            JsonArray selected = array(relation, "selectedBindings");
            return selected.size() > 0 ? selected
                    : array(relation, "runtimeBindings");
        }

        private boolean assertPortEquality(String left, String right,
                                           String label) {
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
            String formula = "(= " + portName(left) + " "
                    + portName(right) + ")";
            assertNamed(label, formula);
            addAutomaticRelationship(label, "VALIDATED_PORT_EQUALITY",
                    formula, left, right);
            portEqualities.add(new String[]{left, right});
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

        private void addAutomaticRelationship(String id, String kind,
                                              String formula, String left,
                                              String right) {
            String asserted = currentGuard.isEmpty() ? formula
                    : "(=> " + currentGuard + " " + formula + ")";
            JsonObject roles = new JsonObject();
            roles.addProperty("left", left);
            roles.addProperty("right", right);
            roles.addProperty("guarded", !currentGuard.isEmpty());
            String candidateId = currentGuard.isEmpty() ? id : id
                    + "_guard_" + Integer.toHexString(
                    currentGuard.hashCode());
            addRelationshipCandidate(candidateId, kind, asserted, false, roles,
                    "AUTOMATIC_REGION_SUMMARY_OR_VALIDATED_EDGE",
                    "NO_DOMAIN_SEMANTIC_ADAPTER");
        }

        private void uninterpretedRegion(String region, Set<String> endpoints) {
            List<String> arguments = new ArrayList<>();
            List<Sort> sorts = new ArrayList<>();
            for (String endpoint : endpoints) {
                Sort sort = portSort(endpoint);
                declarePort(endpoint, sort);
                mentionedPorts.add(endpoint);
                arguments.add(portName(endpoint));
                sorts.add(sort);
            }
            String predicate = "summary_missing__" + smtName(region);
            StringBuilder declaration = new StringBuilder("(declare-fun ")
                    .append(predicate).append(" (");
            for (int index = 0; index < sorts.size(); index++) {
                if (index > 0) declaration.append(' ');
                declaration.append(sorts.get(index).smt);
            }
            declaration.append(") Bool)");
            addDeclaration("fun:" + predicate, declaration.toString());
            StringBuilder call = new StringBuilder("(").append(predicate);
            for (String argument : arguments) call.append(' ').append(argument);
            call.append(')');
            assertNamed("missing_summary_" + region, call.toString());
        }

        private Term mapState(JsonElement expression) {
            Term receiver = term(expression, Sort.MAP);
            if (receiver.sort == Sort.MAP) return receiver;
            if (receiver.sort == Sort.REF) {
                return new Term("(map_state_of " + receiver.text + ")",
                        Sort.MAP);
            }
            unsupported.add("MapReceiverSort:" + receiver.sort);
            String name = scopedFreshName("unknown_map");
            declare(name, Sort.MAP);
            return new Term(name, Sort.MAP);
        }

        /**
         * Encodes a Java Map key without erasing wrapper identity.  Java's
         * equals contract makes Integer(1) and Long(1) different keys even
         * though both have the same mathematical payload, so ordinary VInt
         * boxing is unsound at every Map boundary.
         */
        private Term mapKeyTerm(JsonElement expression, String origin) {
            if (expression == null || !expression.isJsonObject()) {
                unsupported.add("MAP_KEY_EXPRESSION_MISSING:" + origin);
                return null;
            }
            JsonObject object = expression.getAsJsonObject();
            // Preserve the engine expression's own admission diagnostics
            // (notably PlaceholderExpression) in addition to the Java Map
            // key-type diagnostic below.
            Term raw = term(expression, null);
            String kind = mapKeyKind(string(object, "_java_type"));
            if (kind.isEmpty()) {
                unsupported.add("MAP_KEY_TYPE_UNSUPPORTED:" + origin + ":"
                        + string(object, "_java_type"));
                return null;
            }
            if (!validMapKeyLiteral(object, kind)) {
                unsupported.add("MAP_KEY_LITERAL_INVALID:" + origin + ":"
                        + string(object, "_java_type") + ":"
                        + string(object, "_exp"));
                return null;
            }
            if ("STRING".equals(kind)) {
                if (raw.sort != Sort.STRING) {
                    unsupported.add("MAP_KEY_TERM_SORT_MISMATCH:" + origin
                            + ":STRING:" + raw.sort);
                    return null;
                }
                return new Term("(VMapString " + raw.text + ")",
                        Sort.VALUE);
            }
            if (raw.sort != Sort.INT) {
                unsupported.add("MAP_KEY_TERM_SORT_MISMATCH:" + origin + ":"
                        + kind + ":" + raw.sort);
                return null;
            }
            String lower = "";
            String upper = "";
            String constructor;
            if ("BOOLEAN".equals(kind)) {
                lower = "0";
                upper = "1";
                constructor = "VMapBoolean";
            } else if ("BYTE".equals(kind)) {
                lower = "-128";
                upper = "127";
                constructor = "VMapByte";
            } else if ("CHAR".equals(kind)) {
                lower = "0";
                upper = "65535";
                constructor = "VMapChar";
            } else if ("SHORT".equals(kind)) {
                lower = "-32768";
                upper = "32767";
                constructor = "VMapShort";
            } else if ("INTEGER".equals(kind)) {
                lower = "-2147483648";
                upper = "2147483647";
                constructor = "VMapInteger";
            } else if ("LONG".equals(kind)) {
                lower = "-9223372036854775808";
                upper = "9223372036854775807";
                constructor = "VMapLong";
            } else {
                unsupported.add("MAP_KEY_KIND_UNSUPPORTED:" + origin + ":"
                        + kind);
                return null;
            }
            assertNamed("map_key_domain_" + origin + "_" + assertionCount,
                    "(and (<= " + lower + " " + raw.text + ") (<= "
                            + raw.text + " " + upper + "))");
            if ("BOOLEAN".equals(kind)) {
                return new Term("(VMapBoolean (= " + raw.text + " 1))",
                        Sort.VALUE);
            }
            return new Term("(" + constructor + " " + raw.text + ")",
                    Sort.VALUE);
        }

        private static String mapKeyKind(String javaType) {
            String type = firstNonBlank(javaType).trim().replace('.', '/');
            if (type.startsWith("L") && type.endsWith(";")
                    && type.length() > 2) {
                type = type.substring(1, type.length() - 1);
            }
            if ("Z".equals(type) || "boolean".equals(type)
                    || "java/lang/Boolean".equals(type)) return "BOOLEAN";
            if ("B".equals(type) || "byte".equals(type)
                    || "java/lang/Byte".equals(type)) return "BYTE";
            if ("C".equals(type) || "char".equals(type)
                    || "java/lang/Character".equals(type)) return "CHAR";
            if ("S".equals(type) || "short".equals(type)
                    || "java/lang/Short".equals(type)) return "SHORT";
            if ("I".equals(type) || "int".equals(type)
                    || "java/lang/Integer".equals(type)) return "INTEGER";
            if ("J".equals(type) || "long".equals(type)
                    || "java/lang/Long".equals(type)) return "LONG";
            if ("String".equals(type)
                    || "java/lang/String".equals(type)) return "STRING";
            return "";
        }

        private static boolean validMapKeyLiteral(JsonObject expression,
                                                  String kind) {
            String expressionType = string(expression, "_type");
            if (!("ConstExpr".equals(expressionType)
                    || "ConSymbolExp".equals(expressionType)
                    || "ConStringSymbolExp".equals(expressionType))) {
                return true;
            }
            String raw = string(expression, "_exp");
            if (!raw.startsWith("Y_") || raw.length() < 4) return false;
            char expected = "BOOLEAN".equals(kind) ? 'Z'
                    : "BYTE".equals(kind) ? 'B'
                    : "CHAR".equals(kind) ? 'C'
                    : "SHORT".equals(kind) ? 'S'
                    : "INTEGER".equals(kind) ? 'I'
                    : "LONG".equals(kind) ? 'J'
                    : "STRING".equals(kind) ? 'L' : 0;
            if (expected == 0 || raw.charAt(2) != expected) return false;
            if ("STRING".equals(kind)) return true;
            if (raw.charAt(3) != '_') return false;
            String payload = raw.substring(4);
            try {
                java.math.BigInteger value = new java.math.BigInteger(
                        payload);
                if (!value.toString().equals(payload)) return false;
                java.math.BigInteger lower;
                java.math.BigInteger upper;
                if ("BOOLEAN".equals(kind)) {
                    lower = java.math.BigInteger.ZERO;
                    upper = java.math.BigInteger.ONE;
                } else if ("BYTE".equals(kind)) {
                    lower = java.math.BigInteger.valueOf(Byte.MIN_VALUE);
                    upper = java.math.BigInteger.valueOf(Byte.MAX_VALUE);
                } else if ("CHAR".equals(kind)) {
                    lower = java.math.BigInteger.ZERO;
                    upper = java.math.BigInteger.valueOf(Character.MAX_VALUE);
                } else if ("SHORT".equals(kind)) {
                    lower = java.math.BigInteger.valueOf(Short.MIN_VALUE);
                    upper = java.math.BigInteger.valueOf(Short.MAX_VALUE);
                } else if ("INTEGER".equals(kind)) {
                    lower = java.math.BigInteger.valueOf(Integer.MIN_VALUE);
                    upper = java.math.BigInteger.valueOf(Integer.MAX_VALUE);
                } else {
                    lower = java.math.BigInteger.valueOf(Long.MIN_VALUE);
                    upper = java.math.BigInteger.valueOf(Long.MAX_VALUE);
                }
                return value.compareTo(lower) >= 0
                        && value.compareTo(upper) <= 0;
            } catch (RuntimeException malformed) {
                return false;
            }
        }

        private Term asValue(Term term) {
            if (term.sort == Sort.VALUE) return term;
            if (term.sort == Sort.INT) return new Term("(VInt " + term.text + ")",
                    Sort.VALUE);
            if (term.sort == Sort.REAL) return new Term("(VReal " + term.text + ")",
                    Sort.VALUE);
            if (term.sort == Sort.BOOL) return new Term("(VBool " + term.text + ")",
                    Sort.VALUE);
            if (term.sort == Sort.STRING) return new Term("(VString " + term.text
                    + ")", Sort.VALUE);
            if (term.sort == Sort.REF) return new Term("(VRef " + term.text + ")",
                    Sort.VALUE);
            unsupported.add("CannotBox:" + term.sort);
            String name = scopedFreshName("unknown_value");
            declare(name, Sort.VALUE);
            return new Term(name, Sort.VALUE);
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
                        ? new Term("(map_state_of " + value.text + ")", Sort.MAP)
                        : null;
                if (state == null) {
                    unsupported.add("MapPortBinding:" + port + ":" + value.sort);
                    return false;
                }
                String formula = "(= " + portName(port) + " "
                        + state.text + ")";
                assertNamed("bind_" + port, formula);
                addAutomaticRelationship("region_output_" + port,
                        "GUARDED_REGION_OUTPUT", formula, port,
                        state.text);
                return true;
            } else if (portSort == Sort.ARRAY_VALUE) {
                if (value.sort != Sort.ARRAY_VALUE) {
                    unsupported.add("ArrayValuePortBinding:" + port + ":"
                            + value.sort);
                    return false;
                }
                String formula = "(= " + portName(port) + " "
                        + value.text + ")";
                assertNamed("bind_" + port, formula);
                addAutomaticRelationship("region_output_" + port,
                        "GUARDED_REGION_OUTPUT", formula, port,
                        value.text);
                return true;
            } else {
                if (value.sort == Sort.ARRAY_VALUE
                        || value.sort == Sort.ARRAY) {
                    unsupported.add("UnsupportedArrayToScalarBinding:" + port
                            + ":" + value.sort);
                    return false;
                }
                Term boxed = asValue(value);
                String formula = "(= " + portName(port) + " "
                        + boxed.text + ")";
                assertNamed("bind_" + port, formula);
                addAutomaticRelationship("region_output_" + port,
                        "GUARDED_REGION_OUTPUT", formula, port,
                        boxed.text);
                return true;
            }
        }

        private String scopedHeapPort(String rawPort) {
            if (ports.contains(rawPort)) return rawPort;
            return "local_heap__" + scopeToken(currentSymbolScope) + "__"
                    + rawPort;
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
            assertionCount++;
        }

        private boolean isNull(Term term) {
            return term.sort == Sort.REF && "nullRef".equals(term.text);
        }

        private String unknownConstraint(String origin, JsonElement expression) {
            String key = "UnsupportedConstraint:" + origin + ":"
                    + (expression == null ? "null" : GSON.toJson(expression));
            unsupported.add(key);
            String name = scopedFreshName("unknown_constraint");
            declare(name, Sort.BOOL);
            return name;
        }

        private String scopedName(String prefix, String raw) {
            return prefix + "__" + scopeToken(currentSymbolScope) + "__"
                    + smtName(raw);
        }

        private String scopedFreshName(String prefix) {
            return prefix + "__" + scopeToken(currentSymbolScope) + "__"
                    + unknownCounter++;
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
            String id = firstNonBlank(string(json, "portId"),
                    string(json, "symbol"));
            if (id.isEmpty()) return;
            String cell = string(json, "cell");
            String javaType = firstNonBlank(string(json, "javaType"),
                    string(json, "declaredType"), cellJavaType(cell));
            Sort sort = isMapCell(cell) || isMapType(javaType)
                    ? Sort.MAP : isArrayType(javaType)
                    ? Sort.ARRAY_VALUE : Sort.VALUE;
            ports.put(id, new Port(id, cell, javaType, sort, input));
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
        private final String id;
        private final String cell;
        private final String javaType;
        private final Sort sort;
        private final boolean input;

        private Port(String id, String cell, String javaType, Sort sort,
                     boolean input) {
            this.id = id;
            this.cell = cell;
            this.javaType = javaType;
            this.sort = sort;
            this.input = input;
        }
    }

    private static final class EngineArrayInputBridge {
        private final String engineArrayId;
        private final String arrayTerm;
        private final String inputPort;
        private final long objectToken;
        private final int concreteLength;

        private EngineArrayInputBridge(String engineArrayId,
                                       String arrayTerm,
                                       String inputPort,
                                       long objectToken,
                                       int concreteLength) {
            this.engineArrayId = engineArrayId;
            this.arrayTerm = arrayTerm;
            this.inputPort = inputPort;
            this.objectToken = objectToken;
            this.concreteLength = concreteLength;
        }
    }

    private enum Sort {
        BOOL("Bool"), INT("Int"), REAL("Real"), STRING("String"),
        REF("Ref"), MAP("MapState"), VALUE("Value"),
        ARRAY_VALUE("FiniteArrayValue"),
        ARRAY("(Array Int Value)");

        private final String smt;

        Sort(String smt) {
            this.smt = smt;
        }
    }

    private static final class Term {
        private final String text;
        private final Sort sort;

        private Term(String text, Sort sort) {
            this.text = text;
            this.sort = sort;
        }

        private boolean isZero() {
            return "0".equals(text) || "(- 0)".equals(text);
        }
    }

    private static final class ContainerFieldSelector {
        private final int index;
        private final String dynamicFieldSymbol;
        private final JsonObject fieldExpression;
        private final String gap;

        private ContainerFieldSelector(int index, String dynamicFieldSymbol,
                                       JsonObject fieldExpression,
                                       String gap) {
            this.index = index;
            this.dynamicFieldSymbol = firstNonBlank(dynamicFieldSymbol);
            this.fieldExpression = fieldExpression;
            this.gap = firstNonBlank(gap);
        }

        private static ContainerFieldSelector complete(
                int index, String dynamicFieldSymbol,
                JsonObject fieldExpression) {
            return index < 0
                    ? gap("RUNTIME_SELECTOR_INDEX_INVALID")
                    : new ContainerFieldSelector(index, dynamicFieldSymbol,
                    fieldExpression, "");
        }

        private static ContainerFieldSelector gap(String gap) {
            return new ContainerFieldSelector(-1, "", null, gap);
        }

        private boolean complete() {
            return gap.isEmpty() && index >= 0;
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

    private static final class CaseDynamicValidation {
        private final JsonArray dynamicBindings = new JsonArray();
        private final Set<String> gaps = new LinkedHashSet<>();

        private void gap(String value) {
            if (value != null && !value.isEmpty()) gaps.add(value);
        }
    }

    /** Captures the exact terms emitted while one guarded case is active. */
    private static final class CaseProjectionCapture {
        private final String regionId;
        private final String caseId;
        private final String pathKey;
        private final String symbolScope;
        private final String sourceSummaryId;
        private final String sourceActivationId;
        private final JsonArray dynamicBindings;
        private final Map<String, SymbolProjection> symbols =
                new LinkedHashMap<>();
        private final Set<String> gaps = new LinkedHashSet<>();
        private String selectorSolverSymbol = "";
        private String selectorGuardFormula = "";

        private CaseProjectionCapture(String regionId, JsonObject item,
                                      String symbolScope,
                                      CaseDynamicValidation validation) {
            this.regionId = regionId;
            this.caseId = firstNonBlank(string(item, "caseId"), symbolScope);
            this.pathKey = string(item, "pathKey");
            this.symbolScope = symbolScope;
            this.sourceSummaryId = string(item, "sourceSummaryId");
            this.sourceActivationId = string(item, "sourceActivationId");
            this.dynamicBindings = validation.dynamicBindings.deepCopy();
            this.gaps.addAll(validation.gaps);
            if (this.pathKey.isEmpty()) gap("MISSING_CASE_PATH_KEY");
            if (this.sourceSummaryId.isEmpty()) {
                gap("MISSING_CASE_SOURCE_SUMMARY_ID");
            }
            if (this.sourceActivationId.isEmpty()) {
                gap("MISSING_CASE_SOURCE_ACTIVATION_ID");
            }
        }

        private void selector(String solverSymbol, String guardFormula) {
            this.selectorSolverSymbol = firstNonBlank(solverSymbol);
            this.selectorGuardFormula = firstNonBlank(guardFormula);
            if (this.selectorSolverSymbol.isEmpty()) {
                gap("MISSING_CASE_SELECTOR_SYMBOL");
            }
            if (this.selectorGuardFormula.isEmpty()) {
                gap("MISSING_CASE_GUARD_FORMULA");
            }
        }

        private void record(String raw, Term term, String kind,
                            String canonicalPort) {
            SymbolProjection projection = symbols.get(raw);
            if (projection == null) {
                projection = new SymbolProjection(raw, term.text, term.sort,
                        kind, canonicalPort);
                symbols.put(raw, projection);
            } else {
                if (!projection.solverTerm.equals(term.text)
                        || projection.sort != term.sort) {
                    gap("RAW_SYMBOL_TERM_CONFLICT:" + raw);
                }
                projection.upgradeKind(kind);
                if (!canonicalPort.isEmpty()) {
                    if (!projection.canonicalPort.isEmpty()
                            && !projection.canonicalPort.equals(
                            canonicalPort)) {
                        gap("RAW_SYMBOL_PORT_CONFLICT:" + raw);
                    } else {
                        projection.canonicalPort = canonicalPort;
                    }
                }
            }
            for (JsonElement element : dynamicBindings) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                String dynamic = string(binding, "dynamicFieldSymbol");
                if (rawReferences(raw, dynamic)) {
                    projection.dynamicBindingIds.add(string(binding,
                            "dynamicBindingId"));
                }
            }
        }

        private void finish() {
            if (selectorSolverSymbol.isEmpty()) {
                gap("MISSING_CASE_SELECTOR_SYMBOL");
            }
            for (JsonElement element : dynamicBindings) {
                if (!element.isJsonObject()) {
                    gap("NON_OBJECT_PROJECTION_DYNAMIC_BINDING");
                    continue;
                }
                JsonObject binding = element.getAsJsonObject();
                String id = string(binding, "dynamicBindingId");
                String raw = string(binding,
                        "fieldExpressionRawEngineSymbol");
                SymbolProjection projection = symbols.get(raw);
                if (raw.isEmpty() || projection == null) {
                    gap("UNMAPPED_DYNAMIC_FIELD_EXPRESSION:" + id);
                    continue;
                }
                if (!projection.dynamicBindingIds.contains(id)) {
                    gap("DYNAMIC_TERM_SELECTOR_MISMATCH:" + id);
                    continue;
                }
                binding.addProperty("solverTerm", projection.solverTerm);
                binding.addProperty("sort", projection.sort.name());
                binding.addProperty("solverSort", projection.sort.smt);
                binding.addProperty("termBindingAuthority",
                        "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING"
                        .equals(string(binding, "kind"))
                        ? "EXACT_RUNTIME_SYMBOLIZE_FIELD_WITHOUT_PC_"
                        + "EXPRESSION" : "EMITTER_ACTUAL_DYNAMIC_FIELD_TERM");
            }
        }

        private boolean complete() {
            return gaps.isEmpty();
        }

        private void gap(String value) {
            if (value != null && !value.isEmpty()) gaps.add(value);
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 1);
            result.addProperty("kind", "GUARDED_CASE_PROJECTION_CATALOG");
            result.addProperty("regionId", regionId);
            result.addProperty("caseId", caseId);
            result.addProperty("pathKey", pathKey);
            result.addProperty("symbolScope", symbolScope);
            result.addProperty("sourceSummaryId", sourceSummaryId);
            result.addProperty("sourceActivationId", sourceActivationId);
            result.addProperty("selectorSolverSymbol",
                    selectorSolverSymbol);
            result.addProperty("selectorGuardFormula", selectorGuardFormula);
            result.addProperty("selectorAuthority",
                    "DECLARED_BOOL_EQ_EXACT_CASE_GUARD");

            JsonArray mappings = new JsonArray();
            List<String> rawSymbols = new ArrayList<>(symbols.keySet());
            Collections.sort(rawSymbols);
            for (String raw : rawSymbols) {
                mappings.add(symbols.get(raw).toJson());
            }
            result.add("rawEngineSymbolMappings", mappings);
            result.addProperty("rawEngineSymbolMappingCount",
                    mappings.size());
            result.addProperty("rawEngineSymbolMappingAuthority",
                    "EMITTER_ACTUAL_TERM_CAPTURE_IN_CASE_SCOPE");
            result.add("dynamicFieldBindings", dynamicBindings.deepCopy());
            result.addProperty("dynamicFieldBindingCount",
                    dynamicBindings.size());
            boolean container = false;
            boolean mapProjection = false;
            for (JsonElement element : dynamicBindings) {
                if (element.isJsonObject()
                        && "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(
                        string(element.getAsJsonObject(), "kind"))) {
                    container = true;
                }
                if (element.isJsonObject()
                        && "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_"
                        .concat("BINDING").equals(string(
                                element.getAsJsonObject(), "kind"))) {
                    mapProjection = true;
                }
            }
            result.addProperty("mapProjectionBindingPresent",
                    mapProjection);
            result.addProperty("dynamicBindingJoinAuthority", mapProjection
                    ? "CASE_RUNTIME_MAP_ENTRY_SNAPSHOT_OUTPUT_IDENTITY_"
                    + "AND_EXACT_SYMBOLIZE_FIELD_EVIDENCE"
                    : container
                    ? "CASE_RUNTIME_EXACT_ARRAY_SELECTOR_WITH_EXACT_GUARD_"
                    + "EXPRESSION" : "CASE_RUNTIME_BINDING_BIJECTION_WITH_"
                    + "HEAP_OBSERVATION");
            result.add("validationGaps", GSON.toJsonTree(gaps));
            result.addProperty("complete", complete());
            return result;
        }

        private static boolean rawReferences(String raw, String symbol) {
            if (raw == null || symbol == null || symbol.isEmpty()) return false;
            int start = raw.indexOf(symbol);
            while (start >= 0) {
                int end = start + symbol.length();
                boolean left = start == 0 || !Character.isLetterOrDigit(
                        raw.charAt(start - 1));
                boolean right = end == raw.length()
                        || !Character.isLetterOrDigit(raw.charAt(end));
                if (left && right) return true;
                start = raw.indexOf(symbol, start + 1);
            }
            return false;
        }
    }

    private static final class SymbolProjection {
        private final String rawEngineSymbol;
        private final String solverTerm;
        private final Sort sort;
        private String termKind;
        private String canonicalPort;
        private final Set<String> dynamicBindingIds = new LinkedHashSet<>();

        private SymbolProjection(String rawEngineSymbol, String solverTerm,
                                 Sort sort, String termKind,
                                 String canonicalPort) {
            this.rawEngineSymbol = rawEngineSymbol;
            this.solverTerm = solverTerm;
            this.sort = sort;
            this.termKind = firstNonBlank(termKind,
                    "SCOPED_ENGINE_SYMBOL");
            this.canonicalPort = firstNonBlank(canonicalPort);
        }

        private void upgradeKind(String candidate) {
            if ("SCOPED_DYNAMIC_FIELD".equals(candidate)) {
                termKind = candidate;
            } else if (termKind.isEmpty()) {
                termKind = candidate;
            }
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("rawEngineSymbol", rawEngineSymbol);
            result.addProperty("solverTerm", solverTerm);
            result.addProperty("sort", sort.name());
            result.addProperty("solverSort", sort.smt);
            result.addProperty("termKind", termKind);
            if (!canonicalPort.isEmpty()) {
                result.addProperty("canonicalPort", canonicalPort);
            }
            result.add("dynamicBindingIds",
                    GSON.toJsonTree(dynamicBindingIds));
            result.addProperty("authority", "EMITTER_ACTUAL_TERM");
            return result;
        }
    }

    private static final class HeapStateCursor {
        private final int after;
        private final String postState;
        private final String outputPort;

        private HeapStateCursor(int after, String postState,
                                String outputPort) {
            this.after = after;
            this.postState = postState;
            this.outputPort = outputPort;
        }
    }

    private static final class MergeStats {
        private int equalities;
        private int readFrom;
        private int orders;
        private int identities;
        private int edgeBindings;
        private int alternativeWriterGroups;
        private int guardedAlternatives;

        private void add(MergeStats other) {
            equalities += other.equalities;
            readFrom += other.readFrom;
            orders += other.orders;
            identities += other.identities;
            edgeBindings += other.edgeBindings;
            alternativeWriterGroups += other.alternativeWriterGroups;
            guardedAlternatives += other.guardedAlternatives;
        }
    }

    public static final class Result {
        public final String smtLib;
        public final JsonObject manifest;
        public final JsonObject relationships;

        private Result(String smtLib, JsonObject manifest,
                       JsonObject relationships) {
            this.smtLib = smtLib;
            this.manifest = manifest;
            this.relationships = relationships;
        }
    }

    public static final class Arguments {
        private Path fatalQueries;
        private final List<Path> summaries = new ArrayList<>();
        private Path regions;
        private Path mergePlan;
        private Path output;
        private Path manifest;
        private Path relationships;
        private String fatalRegion = "";
        private String activationId = "";
        private final Set<String> boundedUpstreamRegions =
                new LinkedHashSet<>();

        public static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            List<String> summaryValues = new ArrayList<>();
            List<String> boundedRegionValues = new ArrayList<>();
            for (int index = 0; index < argv.length; index++) {
                String argument = argv[index];
                if (!argument.startsWith("--")) {
                    throw new IllegalArgumentException(
                            "Unexpected argument: " + argument);
                }
                String key = argument.substring(2);
                if (index + 1 >= argv.length
                        || argv[index + 1].startsWith("--")) {
                    throw new IllegalArgumentException(
                            "Missing value for --" + key);
                }
                String value = argv[++index];
                if ("summaries".equals(key)) {
                    summaryValues.add(value);
                } else if ("bounded-upstream-region".equals(key)) {
                    boundedRegionValues.add(value);
                } else {
                    values.put(key, value);
                }
            }
            Arguments result = new Arguments();
            result.fatalQueries = path(values, "fatal-query", true);
            for (String value : summaryValues) {
                if (value != null && !value.trim().isEmpty()) {
                    result.summaries.add(Paths.get(value));
                }
            }
            result.regions = path(values, "regions", true);
            result.mergePlan = path(values, "merge-plan", true);
            result.output = path(values, "output", true);
            result.manifest = values.containsKey("manifest")
                    ? Paths.get(values.get("manifest"))
                    : sibling(result.output, "composed_smt_manifest.json");
            result.relationships = values.containsKey("relationships")
                    ? Paths.get(values.get("relationships"))
                    : sibling(result.output,
                    "symbolic_relationship_candidates.json");
            result.fatalRegion = firstNonBlank(values.get("fatal-region"));
            result.activationId = firstNonBlank(values.get("activation-id"));
            for (String value : boundedRegionValues) {
                for (String region : value.split(",")) {
                    String normalized = firstNonBlank(region);
                    if (!normalized.isEmpty()) {
                        result.boundedUpstreamRegions.add(normalized);
                    }
                }
            }
            return result;
        }

        private static Path path(Map<String, String> values, String key,
                                 boolean required) {
            String value = values.get(key);
            if ((value == null || value.trim().isEmpty()) && required) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return value == null || value.trim().isEmpty()
                    ? null : Paths.get(value);
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
        if ("Z".equals(type) || "B".equals(type) || "C".equals(type)
                || "S".equals(type) || "I".equals(type)
                || "J".equals(type) || "boolean".equals(type)
                || "byte".equals(type) || "char".equals(type)
                || "short".equals(type) || "int".equals(type)
                || "long".equals(type)) return Sort.INT;
        if ("F".equals(type) || "D".equals(type)
                || "float".equals(type) || "double".equals(type)) {
            return Sort.REAL;
        }
        if ("java/lang/Boolean".equals(className)
                || "java/lang/Byte".equals(className)
                || "java/lang/Character".equals(className)
                || "java/lang/Short".equals(className)
                || "java/lang/Integer".equals(className)
                || "java/lang/Long".equals(className)) return Sort.INT;
        if ("java/lang/Float".equals(className)
                || "java/lang/Double".equals(className)) return Sort.REAL;
        if ("String".equals(className)
                || "java/lang/String".equals(className)) return Sort.STRING;
        if (type.isEmpty()) return Sort.VALUE;
        return Sort.REF;
    }

    /** Normalizes source names and VM names to one JVM descriptor. */
    private static String javaTypeDescriptor(String type) {
        String value = firstNonBlank(type).trim().replace('.', '/');
        if (value.isEmpty()) return "";
        if (value.startsWith("[")) return value;
        int dimensions = 0;
        while (value.endsWith("[]")) {
            dimensions++;
            value = value.substring(0, value.length() - 2);
        }
        String descriptor;
        if (value.length() == 1 && "ZBCSIJFDV".contains(value)) {
            descriptor = value;
        } else if ("boolean".equals(value)) descriptor = "Z";
        else if ("byte".equals(value)) descriptor = "B";
        else if ("char".equals(value)) descriptor = "C";
        else if ("short".equals(value)) descriptor = "S";
        else if ("int".equals(value)) descriptor = "I";
        else if ("long".equals(value)) descriptor = "J";
        else if ("float".equals(value)) descriptor = "F";
        else if ("double".equals(value)) descriptor = "D";
        else if ("void".equals(value)) descriptor = "V";
        else if (value.startsWith("L") && value.endsWith(";")) {
            descriptor = value;
        } else {
            descriptor = "L" + value + ";";
        }
        StringBuilder result = new StringBuilder(dimensions
                + descriptor.length());
        for (int index = 0; index < dimensions; index++) result.append('[');
        return result.append(descriptor).toString();
    }

    private static boolean primitiveDescriptor(String descriptor) {
        return descriptor != null && descriptor.length() == 1
                && "ZBCSIJFD".contains(descriptor);
    }

    private static boolean referenceDescriptor(String descriptor) {
        return descriptor != null && (descriptor.startsWith("L")
                || descriptor.startsWith("["));
    }

    private static String cellJavaType(String cell) {
        String value = firstNonBlank(cell).trim();
        Matcher parameter = Pattern.compile(
                ">\\.param[0-9]+:([^#]+)(?:#.*)?$").matcher(value);
        if (parameter.find()) return parameter.group(1).trim();
        Matcher field = Pattern.compile(
                "^<[^:]+:\\s+([^()<>\\s]+)\\s+[^()<>\\s]+>(?:#.*)?$")
                .matcher(value);
        if (field.matches()) return field.group(1).trim();
        Matcher returned = Pattern.compile(
                "^<[^:]+:\\s+([^<>\\s]+)\\s+[^<>\\s(]+\\([^>]*\\)>"
                        + "\\.return(?:#.*)?$").matcher(value);
        return returned.matches() ? returned.group(1).trim() : "";
    }

    static boolean isArrayCell(String cell) {
        return isArrayType(cellJavaType(cell));
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
        String normalized = firstNonBlank(type)
                .replace('/', '.').toLowerCase(Locale.ROOT);
        return normalized.matches("java\\.util\\.(?:map|sortedmap|navigablemap|"
                + "hashmap|linkedhashmap|treemap|weakhashmap|identityhashmap|"
                + "concurrent\\.concurrentmap|concurrent\\.concurrenthashmap)");
    }

    private static boolean isMapGet(String name) {
        return firstNonBlank(name).endsWith(" get");
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
        if ("@".equals(operator)) return "div";
        if ("%".equals(operator)) return "mod";
        return "";
    }

    private static String constantPayload(String raw) {
        if (raw == null) return "0";
        int first = raw.indexOf('_');
        int second = first < 0 ? -1 : raw.indexOf('_', first + 1);
        return second < 0 ? raw : raw.substring(second + 1);
    }

    private static String integerLiteral(String value) {
        String normalized = firstNonBlank(value, "0");
        if (normalized.startsWith("-")) {
            return "(- " + normalized.substring(1) + ")";
        }
        return normalized.matches("[0-9]+") ? normalized : "0";
    }

    private static String realLiteral(String value) {
        String normalized = firstNonBlank(value, "0.0")
                .replace('e', 'E');
        if (!normalized.matches("-?[0-9]+(?:\\.[0-9]+)?(?:E[+-]?[0-9]+)?")) {
            return "0.0";
        }
        if (normalized.startsWith("-")) {
            return "(- " + normalized.substring(1) + ")";
        }
        return normalized;
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

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            return Collections.emptyList();
        }
        List<JsonObject> result = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                JsonElement parsed = JsonParser.parseString(line);
                if (parsed.isJsonObject()) result.add(parsed.getAsJsonObject());
            }
        }
        return result;
    }

    private static JsonObject readJson(Path path) throws IOException {
        require(path, "JSON input");
        JsonElement parsed = JsonParser.parseString(new String(
                Files.readAllBytes(path), StandardCharsets.UTF_8));
        if (!parsed.isJsonObject()) {
            throw new IOException("Expected JSON object: " + path);
        }
        return parsed.getAsJsonObject();
    }

    private static void write(Path path, String value) throws IOException {
        Path parent = path.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        Files.write(path, value.getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING);
    }

    private static Path sibling(Path path, String name) {
        Path parent = path.toAbsolutePath().getParent();
        return parent == null ? Paths.get(name) : parent.resolve(name);
    }

    private static JsonArray array(JsonObject object, String field) {
        JsonElement element = object == null ? null : object.get(field);
        return element != null && element.isJsonArray()
                ? element.getAsJsonArray() : new JsonArray();
    }

    /** Reads the neutral schema first and accepts the old name only here. */
    private static JsonArray edgeBindings(JsonObject object) {
        JsonArray current = array(object, "edgeBindings");
        if (object != null && object.has("edgeBindings")) return current;
        return array(object, "producerBindings");
    }

    private static JsonObject object(JsonObject object, String field) {
        JsonElement element = object == null ? null : object.get(field);
        return element != null && element.isJsonObject()
                ? element.getAsJsonObject() : new JsonObject();
    }

    private static String string(JsonObject object, String field) {
        JsonElement element = object == null ? null : object.get(field);
        try {
            return element == null || element.isJsonNull()
                    ? "" : element.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static int integer(JsonObject object, String field, int fallback) {
        JsonElement element = object == null ? null : object.get(field);
        try {
            return element == null || element.isJsonNull()
                    ? fallback : element.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longInteger(JsonObject object, String field,
                                    long fallback) {
        JsonElement element = object == null ? null : object.get(field);
        try {
            return element == null || element.isJsonNull()
                    ? fallback : element.getAsLong();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int firstInteger(JsonObject object, String first,
                                    String second, int fallback) {
        int value = integer(object, first, Integer.MIN_VALUE);
        return value != Integer.MIN_VALUE
                ? value : integer(object, second, fallback);
    }

    private static boolean bool(JsonObject object, String field,
                                boolean fallback) {
        JsonElement element = object == null ? null : object.get(field);
        try {
            return element == null || element.isJsonNull()
                    ? fallback : element.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String firstNonBlank(String... values) {
        if (values != null) {
            for (String value : values) {
                if (value != null && !value.trim().isEmpty()) {
                    return value.trim();
                }
            }
        }
        return "";
    }
}
