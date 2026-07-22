package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.SymbolicEnvironment;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
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

/**
 * Validates raw VM region results, normalizes them into composable summaries,
 * and maintains a content-addressed summary cache.
 */
public final class ConcolicSummaryImporter {
    private static final Gson GSON = new GsonBuilder().disableHtmlEscaping().create();
    public static final String PATH_CONDITION_ISOLATION_POLICY =
            "GRAPH_CHECKER_RUNTIME_HOOKS_PAUSED_V1";
    private static final Pattern REGION_INPUT_PORT = Pattern.compile(
            "(REGION(?:\\.[A-Za-z0-9-]+)+\\.in\\.[0-9]+)");
    private static final Pattern FAILURE_EXCEPTION = Pattern.compile(
            "#exception:([^#]+)");
    private static final Pattern ENGINE_ARRAY_ID = Pattern.compile(
            "^A([ZBCSIJFDL])_([0-9]+)$");
    private static final String VALUE_REF_WITNESS_AUTHORITY =
            "ACTIVATION_LOCAL_OBJECT_TOKEN_REF_WITNESS_V1";
    private static final String MAP_REF_WITNESS_AUTHORITY =
            "ACTIVATION_LOCAL_MAP_OBJECT_TOKEN_REF_WITNESS_V1";
    private static final String VALUE_REF_WITNESS_KIND =
            "ACTIVATION_LOCAL_REF_SYMBOL_WITNESS";
    private static final String MAP_REF_WITNESS_KIND =
            "ACTIVATION_LOCAL_MAP_REF_SYMBOL_WITNESS";
    private static final String VALUE_REF_WITNESS_TOKEN_AUTHORITY =
            "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN_TO_"
                    + "SCOPED_REF_SYMBOL_V1";
    private static final String VALUE_REF_WITNESS_SYMBOL_PREFIX =
            "CAUSYNTH_REF_WITNESS_V1_A";
    private static final String VALUE_REF_WITNESS_CERTIFICATION_AUTHORITY =
            "IMPORTER_EXACT_ACTIVATION_TOKEN_AND_DYNAMIC_FIELD_OWNER_JOIN_V1";
    private static final String CONTAINER_SITE_BRIDGE_AUTHORITY =
            "STATIC_CONTAINER_SELECTOR_AND_ACTIVATION_LOCAL_EXACT_ELEMENT_"
                    + "IDENTITY_TO_DECLARED_FIELD_HOOK_V1";
    private static final String CONTAINER_PUT_CONSUMER_AUTHORITY =
            "RAW_SEMANTIC_REQUESTED_OUTPUT_MAP_PUT_KEY_EXACT_DYNAMIC_"
                    + "SYMBOL_V1";
    private static final String CONTAINER_SNAPSHOT_BRANCH_CONSUMER_AUTHORITY =
            "REQUESTED_OUTPUT_SLICE_EXACT_BRANCH_DYNAMIC_SYMBOL_V1";
    private static final String NON_MUTATING_MAP_ENTRY_READ_STATE_AUTHORITY =
            "NON_MUTATING_MAP_ENTRY_READ_EXACT_DYNAMIC_FIELD_BASE_V1";
    private static final String NON_MUTATING_DYNAMIC_FIELD_EXPRESSION_AUTHORITY =
            "EXACT_VM_BRANCH_MAPPING_DYNAMIC_SYMBOL_AND_REQUESTED_SLICE_BASE_V1";
    private static final String CERTIFIED_CONCRETE_GUARD_AUTHORITY =
            "EXACT_NULL_MODEL_CONCRETE_GUARD_REPLAY_V1";
    private static final String CONCRETE_GUARD_CERTIFICATE_AUTHORITY =
            "RUNTIME_EXACT_APPLIED_NULL_MODEL_ASSIGNMENT_AND_"
                    + "VM_BRANCH_EVENT_V1";
    private static final String CONCRETE_GUARD_PROOF_KIND =
            "REFERENCE_NULL_CONCRETE_GUARD_REPLAY_PROOF";
    private static final String CONCRETE_GUARD_PROOF_AUTHORITY =
            "SOLVER_EXACT_REFERENCE_NULL_GUARD_AND_MODEL_ASSIGNMENT_V1";
    private static final Pattern MATERIALIZATION_HOOK_SITE =
            Pattern.compile("^<.+>#u[0-9]+$");
    private static final Pattern JIMPLE_CMP_ASSIGNMENT = Pattern.compile(
            "^\\s*(\\S+)\\s*=\\s*(\\S+)\\s+(cmp)\\s+(\\S+)\\s*$");
    private static final Pattern JIMPLE_CMP_BRANCH = Pattern.compile(
            "^\\s*if\\s+(\\S+)\\s*(==|!=|<=|>=|<|>)\\s*0\\s+goto\\s+.+$");
    private static final Pattern JIMPLE_TRANSPARENT_CAST = Pattern.compile(
            "^\\s*\\S+\\s*=\\s*\\([^)]*\\)\\s*(\\S+)\\s*$");
    private static final String ITERATOR_REMOVE_SIGNATURE =
            "<java.util.Iterator: void remove()>";

    private ConcolicSummaryImporter() {
    }

    static boolean validValueRefWitnessForTests(JsonObject record,
                                                String activationId) {
        return validValueRefWitness(record, activationId);
    }

    static boolean validMapRefWitnessForTests(JsonObject record,
                                              String activationId) {
        return validMapRefWitness(record, activationId);
    }

    public static void main(String[] args) throws Exception {
        Map<String, String> options = parseArgs(args);
        Path results = required(options, "results");
        Path activations = required(options, "activation-plan");
        Path regions = required(options, "regions");
        Path output = Paths.get(firstNonBlank(options.get("output"),
                sibling(results, "concolic_region_summaries.jsonl").toString()));
        Path diagnostics = Paths.get(firstNonBlank(options.get("diagnostics"),
                sibling(results, "concolic_import_diagnostics.jsonl").toString()));
        Path cache = Paths.get(firstNonBlank(options.get("cache-dir"),
                sibling(results, "concolic-summary-cache").toString()));
        ImportResult imported = importSummaries(results, activations, regions,
                output, diagnostics, cache);
        String boundedIteratorOutput = options.get(
                "bounded-map-iterator-output");
        if (boundedIteratorOutput != null
                && !boundedIteratorOutput.trim().isEmpty()) {
            Path staticGraph = required(options, "static-graph");
            BoundedIteratorResult bounded =
                    synthesizeBoundedOneEntryMapIteratorSummaries(
                            output, activations, regions, staticGraph,
                            Paths.get(boundedIteratorOutput));
            imported.summary.add("boundedMapIteratorApproximation",
                    bounded.toJson());
        }
        System.out.println(GSON.toJson(imported.summary));
        if (imported.validSummaryCount == 0 && imported.rawResultCount > 0) {
            System.exit(2);
        }
    }

    public static ImportResult importSummaries(
            Path resultsFile, Path activationFile, Path regionFile,
            Path outputFile, Path diagnosticFile, Path cacheDirectory)
            throws IOException {
        Map<String, JsonObject> activations = index(readJsonl(activationFile),
                "activationId");
        Map<String, JsonObject> regions = index(readJsonl(regionFile), "regionId");
        List<JsonObject> rawResults = readJsonl(resultsFile);
        List<JsonObject> summaries = new ArrayList<>();
        List<JsonObject> diagnostics = new ArrayList<>();
        Set<String> emittedCacheKeys = new LinkedHashSet<>();
        int skippedEvents = 0;

        for (JsonObject raw : rawResults) {
            String event = string(raw, "event");
            if (!"CONCOLIC_REGION_RESULT".equals(event)) {
                skippedEvents++;
                diagnostics.add(diagnostic(raw, "SKIPPED_RUNTIME_EVENT",
                        firstNonBlank(string(raw, "reason"), event)));
                continue;
            }
            String activationId = string(raw, "activationId");
            JsonObject activation = activations.get(activationId);
            if (activation == null) {
                diagnostics.add(diagnostic(raw, "UNKNOWN_ACTIVATION",
                        activationId));
                continue;
            }
            String regionId = string(raw, "regionId");
            JsonObject region = regions.get(regionId);
            if (region == null) {
                diagnostics.add(diagnostic(raw, "UNKNOWN_REGION", regionId));
                continue;
            }
            if (!regionId.equals(string(activation, "regionId"))) {
                diagnostics.add(diagnostic(raw, "ACTIVATION_REGION_MISMATCH",
                        regionId + " != " + string(activation, "regionId")));
                continue;
            }
            JsonObject engine = object(raw, "engineSummary");
            JsonArray enginePathCondition = array(engine, "pathCondition");
            if (engine.size() == 0 || !bool(engine, "active", false)) {
                diagnostics.add(diagnostic(raw, "INVALID_ENGINE_SUMMARY",
                        "summary missing or captured outside active region"));
                continue;
            }
            String engineRegion = string(engine, "regionId");
            String engineActivation = string(engine, "activationId");
            if (!engineRegion.isEmpty() && !regionId.equals(engineRegion)
                    || !engineActivation.isEmpty()
                    && !activationId.equals(engineActivation)) {
                diagnostics.add(diagnostic(raw, "ENGINE_IDENTITY_MISMATCH",
                        engineRegion + "/" + engineActivation));
                continue;
            }
            String pathConditionIsolationPolicy = string(raw,
                    "pathConditionIsolationPolicy");
            RuntimePathContamination runtimePathContamination =
                    runtimePathContamination(new JsonArray());
            if (PATH_CONDITION_ISOLATION_POLICY.equals(
                    pathConditionIsolationPolicy)) {
                runtimePathContamination =
                        runtimePathContamination(enginePathCondition);
            }
            PathAdmissionPolicy admission = pathAdmissionPolicy(region,
                    activation);
            RegionCaptureGoal captureGoal = RegionCaptureGoal.from(
                    activation);
            boolean outputClosure = captureGoal.isOutputClosure();
            JsonArray rawBranchMappings = array(raw, "branchMappings");
            List<String> branchWitnessIssues = branchWitnessIssues(
                    rawBranchMappings);
            if (!branchWitnessIssues.isEmpty()) {
                for (String issue : branchWitnessIssues) {
                    diagnostics.add(diagnostic(raw,
                            "REJECTED_BINARY_BRANCH_WITNESS", issue));
                }
                continue;
            }
            CertifiedConcreteGuardCatalog certifiedConcreteGuards =
                    certifiedConcreteGuards(raw, activation,
                            enginePathCondition, rawBranchMappings,
                            admission);
            if (!certifiedConcreteGuards.issues.isEmpty()) {
                for (String issue : certifiedConcreteGuards.issues) {
                    diagnostics.add(diagnostic(raw,
                            "REJECTED_CERTIFIED_CONCRETE_GUARD", issue));
                }
                // A self-declared certificate is solver provenance.  Once
                // present, any malformed, unmatched, or duplicate member
                // invalidates the complete runtime result rather than merely
                // dropping the synthetic predicate and preserving a weaker
                // relational summary.
                continue;
            }
            DynamicSemanticPcFallbackCatalog dynamicPcFallbacks =
                    dynamicSemanticPcFallbacks(raw, activation,
                            enginePathCondition, rawBranchMappings,
                            admission);
            Set<Integer> mappedConditions = mappedConditionIndices(
                    rawBranchMappings);
            Map<Integer, JsonElement> semanticBranchConditions =
                    semanticBranchConditions(rawBranchMappings,
                            enginePathCondition);
            PathNormalization normalization = normalizePathCondition(
                    enginePathCondition, admission, mappedConditions,
                    semanticBranchConditions,
                    !mappedConditions.isEmpty()
                            || !certifiedConcreteGuards.guards.isEmpty(),
                    activation,
                    dynamicPcFallbacks, certifiedConcreteGuards);
            JsonArray pathCondition = normalization.conditions;
            RuntimePathContamination residualRuntimePath =
                    runtimePathContamination(pathCondition);
            if (!residualRuntimePath.valid()) {
                diagnostics.add(diagnostic(raw,
                        "RUNTIME_BOOKKEEPING_PATH_CONDITION",
                        GSON.toJson(residualRuntimePath.toJson())));
                continue;
            }
            EngineArrayInputBindingExtraction engineArrayBindings =
                    engineArrayInputBindings(raw, activation, region,
                            enginePathCondition, pathCondition);
            HeapEffectExtraction heapEffects = extractHeapEffects(
                    raw, enginePathCondition, normalization,
                    raw.get("runtimeHeapEffects"),
                    raw.get("runtimeHeapObservations"),
                    raw.get("fieldObservations"),
                    raw.get("dynamicFieldBindings"), rawBranchMappings,
                    activation, regionId, dynamicPcFallbacks,
                    engineArrayBindings.bindings);
            OutputExpressionExtraction outputExtraction =
                    outputExpressions(raw, activation, captureGoal,
                            normalization);
            InputAdmission inputAdmission = inputAdmission(raw, activation,
                    outputClosure, heapEffects.staticCoverage,
                    pathCondition, outputExtraction);
            VmIntrinsicPlaceholderBindingExtraction placeholderBindings =
                    vmIntrinsicPlaceholderBindings(pathCondition,
                            inputAdmission);
            ReplayAdmission replayAdmission = replayAdmission(raw,
                    activation, region, captureGoal);
            if (!replayAdmission.valid) {
                diagnostics.add(diagnostic(raw, "TARGET_REPLAY_REJECTED",
                        replayAdmission.failures.toString()));
                continue;
            }

            String cacheKey = sha256(GSON.toJson(region) + "\n"
                    + GSON.toJson(activation) + "\n"
                    + GSON.toJson(pathCondition) + "\n"
                    + GSON.toJson(heapEffects.effects) + "\n"
                    + GSON.toJson(heapEffects.observations) + "\n"
                    + "EXACT_RUNTIME_FINITE_MAP_SNAPSHOT_POLICY_V1\n"
                    + GSON.toJson(heapEffects.finiteMapSnapshots) + "\n"
                    + "OWNER_EXACT_VM_INTRINSIC_PLACEHOLDER_BINDING_V1\n"
                    + GSON.toJson(placeholderBindings.toJson()) + "\n"
                    + GSON.toJson(heapEffects.runtimeJoin.toJson()) + "\n"
                    + GSON.toJson(heapEffects.staticCoverage.toJson()) + "\n"
                    + GSON.toJson(rawBranchMappings) + "\n"
                    + (raw.has("runtimeHeapEffects")
                    ? GSON.toJson(raw.get("runtimeHeapEffects"))
                    : "<legacy-runtime-heap-effects>") + "\n"
                    + (raw.has("runtimeHeapObservations")
                    ? GSON.toJson(raw.get("runtimeHeapObservations"))
                    : "<legacy-runtime-heap-observations>") + "\n"
                    + (raw.has("fieldObservations")
                    ? GSON.toJson(raw.get("fieldObservations"))
                    : "<no-field-observations>") + "\n"
                    + (raw.has("finalFieldObservations")
                    ? GSON.toJson(raw.get("finalFieldObservations"))
                    : "<no-final-field-observations>") + "\n"
                    + (raw.has("runtimeApproximations")
                    ? GSON.toJson(raw.get("runtimeApproximations"))
                    : "<no-runtime-approximations>") + "\n"
                    + (raw.has("dynamicFieldBindings")
                    ? GSON.toJson(raw.get("dynamicFieldBindings"))
                    : "<legacy-dynamic-field-bindings>") + "\n"
                    + (raw.has("engineArrayInputBindings")
                    ? GSON.toJson(raw.get("engineArrayInputBindings"))
                    : "<no-engine-array-input-bindings>") + "\n"
                    + GSON.toJson(engineArrayBindings.bindings) + "\n"
                    + (raw.has("outputCaptures")
                    ? GSON.toJson(raw.get("outputCaptures"))
                    : "<no-output-captures>") + "\n"
                    + string(raw, "exitKind") + "\n"
                    + string(raw, "exceptionType")
                    + (pathConditionIsolationPolicy.isEmpty() ? ""
                    : "\n" + pathConditionIsolationPolicy));
            if (!emittedCacheKeys.add(cacheKey)) {
                diagnostics.add(diagnostic(raw, "DUPLICATE_SUMMARY", cacheKey));
                continue;
            }

            JsonObject summary = new JsonObject();
            summary.addProperty("summaryId", "SUMMARY." + regionId + "."
                    + cacheKey.substring(0, 12));
            summary.addProperty("cacheKey", cacheKey);
            summary.addProperty("activationId", activationId);
            summary.addProperty("regionId", regionId);
            summary.addProperty("regionInstanceId", string(activation,
                    "regionInstanceId"));
            summary.addProperty("rootCallId", integer(activation,
                    "rootCallId", -1));
            summary.add("captureGoal", captureGoal.toJson());
            summary.addProperty("rootMethod", firstNonBlank(
                    string(activation, "rootMethod"), string(region, "rootMethod")));
            summary.addProperty("dynamicReceiverType",
                    string(activation, "receiverType"));
            summary.add("pathSignature", pathSignature(pathCondition));
            summary.add("symbolicInputs", symbolicInputs(activation));
            summary.add("requestedOutput", copy(
                    activation.get("requestedOutput"), new JsonObject()));
            summary.add("requestedOutputSlice", copy(
                    activation.get("requestedOutputSlice"), new JsonObject()));
            summary.add("requestedOutputCapture", copy(
                    activation.get("requestedOutputCapture"),
                    new JsonArray()));
            summary.addProperty("requestedOutputCaptureRequired", bool(
                    activation, "requestedOutputCaptureRequired", false));
            summary.addProperty("requestedOutputCaptureComplete", bool(
                    activation, "requestedOutputCaptureComplete",
                    !bool(activation, "requestedOutputCaptureRequired",
                            false)));
            summary.addProperty("requestedOutputCaptureRefinementRequired",
                    bool(activation,
                            "requestedOutputCaptureRefinementRequired",
                            false));
            summary.addProperty("requestedOutputCaptureTemplateReady", bool(
                    activation, "requestedOutputCaptureTemplateReady",
                    false));
            summary.addProperty("requestedOutputCaptureTemplateAuthority",
                    string(activation,
                            "requestedOutputCaptureTemplateAuthority"));
            summary.addProperty("requestedOutputCaptureRefinementPolicy",
                    string(activation,
                            "requestedOutputCaptureRefinementPolicy"));
            boolean requestedOutputSliceComplete = !outputClosure || bool(
                    activation, "requestedOutputSliceComplete", false);
            boolean boundedPartialOutputSliceAdmitted = outputClosure
                    && bool(activation,
                    "boundedPartialOutputSliceAdmitted", false);
            boolean requestedOutputSliceOperationallyAdmitted =
                    !outputClosure || requestedOutputSliceComplete
                            || boundedPartialOutputSliceAdmitted;
            summary.addProperty("requestedOutputSliceComplete",
                    requestedOutputSliceComplete);
            summary.addProperty("boundedPartialOutputSliceAdmitted",
                    boundedPartialOutputSliceAdmitted);
            summary.addProperty(
                    "requestedOutputSliceOperationallyAdmitted",
                    requestedOutputSliceOperationallyAdmitted);
            summary.addProperty("requestedOutputSlicePolicy", string(
                    activation, "requestedOutputSlicePolicy"));
            summary.add("edgeBindings", copy(firstElement(activation,
                    "edgeBindings", "producerBindings"), new JsonArray()));
            summary.add("pathCondition", pathCondition.deepCopy());
            summary.add("branchMappings", normalizeBranchMappings(
                    rawBranchMappings, normalization));
            JsonObject normalizationSummary = new JsonObject();
            normalizationSummary.addProperty("policy",
                    admission.policy);
            normalizationSummary.addProperty("allowedMethodCount",
                    admission.methodKeys.size());
            normalizationSummary.addProperty("declaredBoundaryCount",
                    admission.boundaries.size());
            normalizationSummary.addProperty("engineConditionCount",
                    enginePathCondition.size());
            normalizationSummary.addProperty("rawConditionCount",
                    enginePathCondition.size());
            normalizationSummary.addProperty("semanticConditionCount",
                    normalization.semanticConditionCount);
            normalizationSummary.addProperty("normalizedConditionCount",
                    pathCondition.size());
            normalizationSummary.addProperty("filteredConditionCount",
                    normalization.filteredConditionCount);
            normalizationSummary.addProperty("consecutiveDuplicatesRemoved",
                    normalization.duplicateConditionCount);
            normalizationSummary.addProperty(
                    "semanticBranchConditionSubstitutionCount",
                    normalization.semanticBranchConditionSubstitutionCount);
            normalizationSummary.addProperty(
                    "certifiedConcreteGuardConditionCount",
                    normalization.syntheticConditionCount);
            normalizationSummary.add("conditionIndexMap",
                    normalization.indexMap());
            normalizationSummary.add("filteredConditions",
                    normalization.filteredConditions());
            summary.add("pathConditionNormalization", normalizationSummary);
            JsonObject outputs = outputExtraction.expressions;
            heapEffects.bindOutputExpressions(outputs);
            summary.add("outputExpressions", outputs);
            summary.add("outputExpressionAdmission",
                    outputExtraction.toJson());
            summary.add("heapStateInitializers",
                    heapEffects.initializers.deepCopy());
            summary.add("heapEffects", heapEffects.effects.deepCopy());
            summary.add("heapObservations",
                    heapEffects.observations.deepCopy());
            summary.add("ignoredRuntimeHeapEvidence",
                    heapEffects.ignoredEvidence.deepCopy());
            summary.add("finiteMapSnapshots",
                    heapEffects.finiteMapSnapshots.deepCopy());
            summary.add("dynamicFieldBindings",
                    heapEffects.dynamicFieldBindings.deepCopy());
            summary.add("engineArrayInputBindings",
                    engineArrayBindings.bindings.deepCopy());
            summary.add("heapEffectModel", heapEffects.model());
            summary.addProperty("relationallyComplete",
                    heapEffects.complete()
                            && requestedOutputSliceOperationallyAdmitted
                            && inputAdmission.complete
                            && placeholderBindings.complete
                            && engineArrayBindings.complete
                            && outputExtraction.complete);
            summary.add("inputMaterializationAdmission",
                    inputAdmission.toJson());
            summary.add("unforcedEnvironmentValidationRequirements",
                    inputAdmission.unforcedEnvironmentValidationRequirements
                            .deepCopy());
            summary.add("vmIntrinsicPlaceholderBindings",
                    placeholderBindings.bindings.deepCopy());
            summary.add("vmIntrinsicPlaceholderBindingAdmission",
                    placeholderBindings.toJson());
            summary.addProperty("normalExit", "NORMAL".equals(string(raw, "exitKind")));
            summary.addProperty("exceptionType", string(raw, "exceptionType"));
            summary.addProperty("engine", firstNonBlank(string(engine, "engine"),
                    "openjdk8-zero-concolic"));
            if (!pathConditionIsolationPolicy.isEmpty()) {
                summary.addProperty("pathConditionIsolationPolicy",
                        pathConditionIsolationPolicy);
            }
            summary.addProperty("confidence", "RUNTIME_CONCOLIC");
            summary.addProperty("valid", true);
            summary.add("executionAdmission", replayAdmission.toJson());
            summary.addProperty("targetReplayValidated",
                    replayAdmission.required && replayAdmission.valid);
            if (replayAdmission.required && replayAdmission.valid) {
                summary.add("directedTargetQuery", object(activation,
                        "directedTargetQuery").deepCopy());
            }
            summary.addProperty("branchOverrideUsed",
                    bool(raw, "branchOverrideUsed", false));
            summary.add("replayMaterializationsApplied", copy(raw.get(
                    "replayMaterializationsApplied"), new JsonArray()));
            summary.add("modelAssignmentsApplied", copy(raw.get(
                    "modelAssignmentsApplied"), new JsonArray()));
            summary.add("exceptionChain", copy(raw.get("exceptionChain"),
                    new JsonArray()));
            summary.add("unresolvedInputs", copy(raw.get("unresolvedInputs"),
                    new JsonArray()));
            summaries.add(summary);
            writeCacheEntry(cacheDirectory, cacheKey, summary);
            for (HeapEffectIssue issue : heapEffects.issues) {
                diagnostics.add(diagnostic(raw, issue.code, issue.detail()));
            }
            for (EngineArrayInputBindingIssue issue
                    : engineArrayBindings.issues) {
                diagnostics.add(diagnostic(raw, issue.code, issue.detail));
            }
            if (!inputAdmission.complete) {
                diagnostics.add(diagnostic(raw,
                        "INCOMPLETE_OUTPUT_INPUT_MATERIALIZATION",
                        inputAdmission.failures.toString()));
            }
            if (!placeholderBindings.complete) {
                diagnostics.add(diagnostic(raw,
                        "INCOMPLETE_VM_INTRINSIC_PLACEHOLDER_BINDING",
                        placeholderBindings.failures.toString()));
            }
            if (normalization.filteredConditionCount > 0) {
                diagnostics.add(diagnostic(raw,
                        "FILTERED_NON_SEMANTIC_PATH_CONDITIONS",
                        String.valueOf(normalization.filteredConditionCount)));
            }
            if (!runtimePathContamination.valid()) {
                diagnostics.add(diagnostic(raw,
                        "FILTERED_RUNTIME_BOOKKEEPING_PATH_CONDITIONS",
                        GSON.toJson(runtimePathContamination.toJson())));
            }
        }

        writeJsonlAtomic(outputFile, summaries);
        writeJsonlAtomic(diagnosticFile, diagnostics);
        ImportResult result = new ImportResult(rawResults.size(), summaries.size(),
                diagnostics.size(), skippedEvents);
        result.summary.addProperty("rawResultCount", result.rawResultCount);
        result.summary.addProperty("validSummaryCount", result.validSummaryCount);
        result.summary.addProperty("diagnosticCount", result.diagnosticCount);
        result.summary.addProperty("skippedEventCount", result.skippedEventCount);
        result.summary.addProperty("output", outputFile.toAbsolutePath().toString());
        result.summary.addProperty("cacheDirectory",
                cacheDirectory.toAbsolutePath().toString());
        return result;
    }

    /**
     * Produces an optional, standalone bounded summary for a Java
     * {@link java.util.Iterator#remove()} path that the concrete workload
     * could not enter because the exact input Map snapshot was empty.
     *
     * <p>This is deliberately a separate artifact rather than an extra row in
     * the ordinary import output.  A caller must choose the approximation in
     * place of the concrete summary; otherwise two transformers for the same
     * region output would be asserted simultaneously.  Admission is based on
     * the frozen requested-output slice only: one exact Map pre/output port,
     * one exact Iterator.remove mutation, one Jimple long {@code cmp} guard
     * whose operands resolve to a declared entry field and an environment
     * input, one same-owner integral projected field for the entry key, and
     * one complete zero-cardinality runtime snapshot.  No application class,
     * region id, activation id, or field name is special-cased.</p>
     */
    public static BoundedIteratorResult
    synthesizeBoundedOneEntryMapIteratorSummaries(
            Path summariesFile, Path activationFile, Path regionFile,
            Path outputFile) throws IOException {
        return synthesizeBoundedOneEntryMapIteratorSummaries(summariesFile,
                activationFile, regionFile, null, outputFile);
    }

    public static BoundedIteratorResult
    synthesizeBoundedOneEntryMapIteratorSummaries(
            Path summariesFile, Path activationFile, Path regionFile,
            Path staticGraphFile, Path outputFile) throws IOException {
        Map<String, JsonObject> activations = index(readJsonl(activationFile),
                "activationId");
        Map<String, JsonObject> regions = index(readJsonl(regionFile),
                "regionId");
        Map<String, JsonObject> staticEdges = indexStaticEdges(readJsonl(
                staticGraphFile));
        List<JsonObject> generated = new ArrayList<>();
        JsonArray diagnostics = new JsonArray();
        Set<String> cacheKeys = new LinkedHashSet<>();
        int candidates = 0;
        for (JsonObject summary : readJsonl(summariesFile)) {
            JsonObject activation = activations.get(string(summary,
                    "activationId"));
            JsonObject region = regions.get(string(summary, "regionId"));
            BoundedIteratorEvidence evidence = boundedIteratorEvidence(
                    summary, activation, region, staticEdges);
            if (evidence.applicable) {
                candidates++;
            }
            if (!evidence.complete) {
                if (evidence.applicable) {
                    diagnostics.add(evidence.diagnostic(summary));
                }
                continue;
            }
            JsonObject bounded = boundedIteratorSummary(summary, activation,
                    region, evidence);
            String key = string(bounded, "cacheKey");
            if (cacheKeys.add(key)) {
                generated.add(bounded);
            }
        }
        writeJsonlAtomic(outputFile, generated);
        return new BoundedIteratorResult(candidates, generated.size(),
                diagnostics, outputFile);
    }

    private static BoundedIteratorEvidence boundedIteratorEvidence(
            JsonObject summary, JsonObject activation, JsonObject region,
            Map<String, JsonObject> staticEdges) {
        if (activation == null || region == null
                || !bool(summary, "valid", true)
                || !RegionCaptureGoal.from(summary).isOutputClosure()) {
            return BoundedIteratorEvidence.notApplicable();
        }
        JsonObject requested = object(activation, "requestedOutput");
        JsonObject slice = object(activation, "requestedOutputSlice");
        String outputPort = firstNonBlank(string(requested, "portId"),
                string(requested, "symbol"));
        String outputCell = string(requested, "cell");
        if (!"HEAP_STATE".equals(string(requested, "kind"))
                || outputPort.isEmpty() || outputCell.isEmpty()
                || !bool(activation, "boundedPartialOutputSliceAdmitted",
                false)
                || !bool(slice, "structuralComplete", false)
                || bool(slice, "truncated", true)
                || !bool(slice,
                "requestedStateTransformerContractApplicable", false)
                || !bool(slice,
                "requestedStateTransformerContractComplete", false)) {
            return BoundedIteratorEvidence.notApplicable();
        }
        for (JsonElement effect : array(summary, "heapEffects")) {
            if (effect.isJsonObject() && "MAP_REMOVE".equals(string(
                    effect.getAsJsonObject(), "kind"))) {
                return BoundedIteratorEvidence.notApplicable();
            }
        }

        Map<String, JsonObject> ports = new LinkedHashMap<>();
        Map<String, List<String>> portsByCell = new LinkedHashMap<>();
        for (JsonElement element : array(region, "symbolicInputs")) {
            if (!element.isJsonObject()) continue;
            JsonObject port = element.getAsJsonObject();
            String id = firstNonBlank(string(port, "portId"),
                    string(port, "symbol"));
            String cell = string(port, "cell");
            if (id.isEmpty() || cell.isEmpty()) continue;
            ports.put(id, port);
            List<String> ids = portsByCell.get(cell);
            if (ids == null) {
                ids = new ArrayList<>();
                portsByCell.put(cell, ids);
            }
            ids.add(id);
        }
        Set<String> sliceInputs = primitiveStrings(array(slice,
                "inputPorts"));
        List<String> mapInputs = portsByCell.get(outputCell);
        String mapInput = uniqueAdmittedPort(mapInputs, sliceInputs);
        if (mapInput.isEmpty()) {
            return BoundedIteratorEvidence.gap(
                    "MAP_PRESTATE_PORT_NOT_UNIQUE", outputPort);
        }

        List<JsonObject> causalEdges = hydratedCausalEdges(slice,
                staticEdges);
        List<JsonObject> mutations = new ArrayList<>();
        for (JsonObject edge : causalEdges) {
            if ("field_mutation".equals(string(edge, "kind"))
                    && outputCell.equals(string(edge, "toCell"))
                    && ITERATOR_REMOVE_SIGNATURE.equals(string(edge,
                    "invoke"))) {
                mutations.add(edge);
            }
        }
        if (mutations.size() != 1) {
            return BoundedIteratorEvidence.gap(
                    "ITERATOR_REMOVE_MUTATION_COUNT=" + mutations.size(),
                    outputPort);
        }
        JsonObject mutation = mutations.get(0);
        String mutationSite = string(mutation, "siteId");
        if (!exactTransformerObligation(slice, mutationSite, outputCell)) {
            return BoundedIteratorEvidence.gap(
                    "ITERATOR_REMOVE_TRANSFORMER_OBLIGATION_NOT_EXACT",
                    mutationSite);
        }

        CmpGuardResolution comparison = CmpGuardResolution.none();
        int comparisonCandidates = 0;
        for (JsonObject edge : causalEdges) {
            if (!"heap_mutation_path_guard".equals(string(edge, "kind"))
                    || !mutationSite.equals(string(edge,
                    "guardedMutationSiteId"))) {
                continue;
            }
            CmpGuardResolution candidate = resolveCmpGuard(edge,
                    causalEdges, portsByCell, ports);
            if (candidate.complete) {
                comparison = candidate;
                comparisonCandidates++;
            }
        }
        if (comparisonCandidates != 1) {
            return BoundedIteratorEvidence.gap(
                    "EXPIRY_CMP_GUARD_COUNT=" + comparisonCandidates,
                    mutationSite);
        }

        JsonObject leftPort = ports.get(comparison.leftPort);
        JsonObject rightPort = ports.get(comparison.rightPort);
        boolean leftEnvironment = "ENVIRONMENT".equals(string(leftPort,
                "sourceKind"));
        boolean rightEnvironment = "ENVIRONMENT".equals(string(rightPort,
                "sourceKind"));
        String fieldPort;
        String environmentPort;
        String operator;
        if (!leftEnvironment && rightEnvironment) {
            fieldPort = comparison.leftPort;
            environmentPort = comparison.rightPort;
            operator = comparison.operator;
        } else if (leftEnvironment && !rightEnvironment) {
            fieldPort = comparison.rightPort;
            environmentPort = comparison.leftPort;
            operator = swapRelationalOperator(comparison.operator);
        } else {
            return BoundedIteratorEvidence.gap(
                    "CMP_REQUIRES_ONE_ENVIRONMENT_OPERAND", mutationSite);
        }
        JsonObject field = ports.get(fieldPort);
        String fieldSignature = string(field, "cell");
        String fieldOwner = declaredFieldOwner(fieldSignature);
        String fieldType = declaredFieldType(fieldSignature);
        if (!"<".equals(operator)
                || !"SHARED_HEAP".equals(string(field, "sourceKind"))
                || fieldOwner.isEmpty() || fieldType.isEmpty()
                || !isIntegralFieldType(fieldType)
                || !sliceInputs.contains(fieldPort)
                || !sliceInputs.contains(environmentPort)) {
            return BoundedIteratorEvidence.gap(
                    "STRICT_FIELD_BEFORE_ENVIRONMENT_GUARD_NOT_PROVEN",
                    comparison.guardSite);
        }

        List<String> keyPorts = new ArrayList<>();
        for (Map.Entry<String, JsonObject> entry : ports.entrySet()) {
            String id = entry.getKey();
            JsonObject port = entry.getValue();
            String signature = string(port, "cell");
            if (!id.equals(fieldPort) && sliceInputs.contains(id)
                    && "SHARED_HEAP".equals(string(port, "sourceKind"))
                    && fieldOwner.equals(declaredFieldOwner(signature))
                    && isIntegralFieldType(declaredFieldType(signature))) {
                keyPorts.add(id);
            }
        }
        if (keyPorts.size() != 1) {
            return BoundedIteratorEvidence.gap(
                    "SAME_OWNER_INTEGRAL_ENTRY_KEY_PORT_COUNT="
                            + keyPorts.size(), fieldOwner);
        }

        List<JsonObject> emptySnapshots = new ArrayList<>();
        for (JsonElement element : array(summary, "finiteMapSnapshots")) {
            if (!element.isJsonObject()) continue;
            JsonObject snapshot = element.getAsJsonObject();
            if (mapInput.equals(string(snapshot, "statePort"))
                    && integer(snapshot, "cardinality", -1) == 0
                    && bool(snapshot, "complete", false)
                    && bool(snapshot, "mapKeysFullyCaptured", false)) {
                emptySnapshots.add(snapshot);
            }
        }
        if (emptySnapshots.size() != 1) {
            return BoundedIteratorEvidence.gap(
                    "EXACT_EMPTY_MAP_SNAPSHOT_COUNT="
                            + emptySnapshots.size(), mapInput);
        }

        JsonArray proofEdges = new JsonArray();
        proofEdges.add(string(mutation, "id"));
        proofEdges.add(comparison.guardEdgeId);
        for (String id : comparison.definitionEdgeIds) proofEdges.add(id);
        return BoundedIteratorEvidence.complete(outputPort, outputCell,
                mapInput, keyPorts.get(0), fieldPort, environmentPort,
                fieldSignature, declaredFieldName(fieldSignature),
                fieldType, fieldOwner, mutationSite, comparison.guardSite,
                string(emptySnapshots.get(0), "snapshotId"), proofEdges);
    }

    private static JsonObject boundedIteratorSummary(
            JsonObject source, JsonObject activation, JsonObject region,
            BoundedIteratorEvidence evidence) {
        String evidenceJson = GSON.toJson(evidence.toJson());
        String cacheKey = sha256(GSON.toJson(source) + "\n"
                + GSON.toJson(activation) + "\n" + GSON.toJson(region)
                + "\nBOUNDED_ONE_ENTRY_MAP_ITERATOR_REMOVE_V1\n"
                + evidenceJson);
        String regionId = string(source, "regionId");
        String scope = cacheKey.substring(0, 12);
        String family = "MAP_STATE." + regionId + ".BOUNDED." + scope;
        String effectId = "HEAP_EFFECT." + regionId + ".BOUNDED."
                + scope;
        String observationId = "MAP_ENTRY_READ.BOUNDED." + scope;

        JsonObject keyExpression = boundedPortExpression(evidence.keyPort,
                declaredFieldType(string(port(region, evidence.keyPort),
                        "cell")), "entry_key");
        JsonObject expiryExpression = boundedPortExpression(
                evidence.fieldPort, evidence.fieldType, "entry_field");
        JsonObject timeExpression = boundedPortExpression(
                evidence.environmentPort, evidence.fieldType,
                "environment");
        JsonObject valueExpression = new JsonObject();
        valueExpression.addProperty("_type", "SymbolExpression");
        valueExpression.addProperty("_java_type",
                evidence.fieldOwner.replace('.', '/'));
        valueExpression.addProperty("_exp",
                "bounded_map_entry_value_" + scope);

        JsonObject guard = new JsonObject();
        guard.addProperty("_type", "BinaryExpression");
        guard.add("_left", expiryExpression.deepCopy());
        guard.addProperty("_op", "<");
        guard.add("_right", timeExpression.deepCopy());
        guard.addProperty("_causynth_authority",
                "STATIC_EXACT_JIMPLE_CMP_AND_REQUIRED_BRANCH_OUTCOME_V1");

        JsonObject observation = new JsonObject();
        observation.addProperty("schemaVersion", 1);
        observation.addProperty("kind", "MAP_ENTRY_READ");
        observation.addProperty("complete", true);
        observation.addProperty("observationId", observationId);
        observation.addProperty("statePort", evidence.mapInputPort);
        observation.add("keyExpression", keyExpression.deepCopy());
        observation.add("valueExpression", valueExpression.deepCopy());
        observation.addProperty("entryBindingAuthority",
                "STATIC_BOUNDED_ONE_ENTRY_ITERATOR_VALUE_BINDING_V1");
        observation.addProperty("entryValueFieldBindingComplete", true);
        JsonObject fieldBinding = new JsonObject();
        fieldBinding.addProperty("fieldSymbol", evidence.fieldPort);
        fieldBinding.addProperty("fieldSignature", evidence.fieldSignature);
        fieldBinding.addProperty("fieldJavaType", evidence.fieldType);
        JsonArray fieldPath = new JsonArray();
        fieldPath.add(evidence.fieldName);
        fieldBinding.add("fieldPath", fieldPath);
        fieldBinding.addProperty("authority",
                "STATIC_EXACT_DECLARED_FIELD_TO_CMP_OPERAND_PORT_V1");
        JsonArray fieldBindings = new JsonArray();
        fieldBindings.add(fieldBinding);
        observation.add("entryFieldBindings", fieldBindings);

        JsonObject effect = new JsonObject();
        effect.addProperty("effectId", effectId);
        effect.addProperty("kind", "MAP_REMOVE");
        effect.addProperty("stateFamily", family);
        effect.addProperty("preState", family + ".0");
        effect.addProperty("postState", family + ".1");
        effect.addProperty("stateOrdinalBefore", 0);
        effect.addProperty("stateOrdinalAfter", 1);
        effect.addProperty("inputPort", evidence.mapInputPort);
        effect.addProperty("outputPort", evidence.outputPort);
        effect.addProperty("inputBinding", "BOUNDED_PRESTATE_PORT");
        effect.addProperty("outputBinding", "ACTIVATION_HEAP_OUTPUT");
        effect.add("keyExpression", keyExpression.deepCopy());
        effect.addProperty("requiresKeyPresent", true);
        effect.addProperty("entryReadObservationId", observationId);
        effect.addProperty("siteId", evidence.mutationSite);
        effect.addProperty("occurrence", 1);
        effect.addProperty("provenanceAuthority",
                "STATIC_EXACT_ITERATOR_REMOVE_PLUS_BOUNDED_ONE_ENTRY_"
                        + "PRESTATE_V1");
        effect.addProperty("approximation", true);

        JsonObject outputExpression = new JsonObject();
        outputExpression.addProperty("kind", "HEAP_STATE_VERSION");
        outputExpression.addProperty("stateId", family + ".1");
        outputExpression.addProperty("stateFamily", family);
        outputExpression.addProperty("effectId", effectId);
        outputExpression.addProperty("sourcePort", evidence.outputPort);
        JsonObject outputs = new JsonObject();
        outputs.add(evidence.outputPort, outputExpression);

        JsonObject model = new JsonObject();
        model.addProperty("policy",
                "STATIC_BOUNDED_ONE_ENTRY_MAP_ITERATOR_SSA_V1");
        model.addProperty("candidateMutationCount", 1);
        model.addProperty("effectCount", 1);
        model.addProperty("observationCount", 1);
        model.addProperty("finiteMapSnapshotCount", 0);
        model.addProperty("identityEffectCount", 0);
        model.addProperty("mapStateFamilyCount", 1);
        model.addProperty("unsupportedMutationCount", 0);
        model.addProperty("malformedMutationCount", 0);
        model.addProperty("syntheticInputCount", 0);
        model.addProperty("initializedInputCount", 0);
        model.addProperty("initializerCount", 0);
        model.addProperty("unboundFinalOutputCount", 0);
        model.addProperty("intermediateStateCount", 0);
        model.addProperty("complete", true);

        JsonObject bounded = new JsonObject();
        bounded.addProperty("schemaVersion", 1);
        bounded.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        bounded.addProperty("summaryId", "SUMMARY." + regionId
                + ".BOUNDED_ITERATOR." + scope);
        bounded.addProperty("cacheKey", cacheKey);
        bounded.addProperty("activationId", string(source, "activationId"));
        bounded.addProperty("regionId", regionId);
        bounded.addProperty("regionInstanceId", string(source,
                "regionInstanceId"));
        bounded.addProperty("rootCallId", integer(source, "rootCallId", -1));
        bounded.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        bounded.addProperty("rootMethod", string(source, "rootMethod"));
        bounded.addProperty("dynamicReceiverType", string(source,
                "dynamicReceiverType"));
        JsonArray pathSignature = new JsonArray();
        pathSignature.add("bounded-one-entry:" + scope);
        bounded.add("pathSignature", pathSignature);
        JsonArray symbolicInputs = new JsonArray();
        symbolicInputs.add(evidence.mapInputPort);
        symbolicInputs.add(evidence.keyPort);
        symbolicInputs.add(evidence.fieldPort);
        symbolicInputs.add(evidence.environmentPort);
        bounded.add("symbolicInputs", symbolicInputs);
        bounded.add("requestedOutput", object(source,
                "requestedOutput").deepCopy());
        JsonObject boundedSlice = new JsonObject();
        boundedSlice.addProperty("outputPort", evidence.outputPort);
        boundedSlice.addProperty("outputCell", evidence.outputCell);
        boundedSlice.add("inputPorts", symbolicInputs.deepCopy());
        boundedSlice.add("staticInputPorts", symbolicInputs.deepCopy());
        boundedSlice.add("containerElementFieldBindings", new JsonArray());
        boundedSlice.addProperty("complete", false);
        boundedSlice.addProperty("structuralComplete", false);
        boundedSlice.addProperty("boundedApproximation", true);
        boundedSlice.addProperty("boundedRelationallyComplete", true);
        boundedSlice.addProperty("scope",
                "ONE_RELEVANT_PRESTATE_MAP_ENTRY_AND_ONE_ITERATION");
        boundedSlice.addProperty("authority",
                "STATIC_EXACT_BOUNDED_ITERATOR_EVIDENCE_PORTS_V1");
        bounded.add("requestedOutputSlice", boundedSlice);
        bounded.add("requestedOutputCapture", new JsonArray());
        bounded.addProperty("requestedOutputCaptureRequired", false);
        bounded.addProperty("requestedOutputCaptureComplete", true);
        bounded.addProperty("requestedOutputSliceComplete", false);
        bounded.addProperty("boundedPartialOutputSliceAdmitted", true);
        bounded.addProperty("requestedOutputSliceOperationallyAdmitted",
                true);
        bounded.addProperty("requestedOutputSlicePolicy",
                "STATIC_BOUNDED_ONE_ENTRY_ITERATOR_RELEVANT_PATH_V1");
        bounded.add("edgeBindings", array(source, "edgeBindings").deepCopy());
        JsonArray pathCondition = new JsonArray();
        pathCondition.add(guard);
        bounded.add("pathCondition", pathCondition);
        bounded.add("branchMappings", new JsonArray());
        bounded.add("outputExpressions", outputs);
        bounded.add("heapStateInitializers", new JsonArray());
        JsonArray effects = new JsonArray();
        effects.add(effect);
        bounded.add("heapEffects", effects);
        JsonArray observations = new JsonArray();
        observations.add(observation);
        bounded.add("heapObservations", observations);
        bounded.add("ignoredRuntimeHeapEvidence", new JsonArray());
        bounded.add("finiteMapSnapshots", new JsonArray());
        bounded.add("dynamicFieldBindings", new JsonArray());
        bounded.add("engineArrayInputBindings", new JsonArray());
        bounded.add("heapEffectModel", model);
        // This closes the selected one-entry iterator transition, not every
        // entry or every path through the source region.  Keep the global
        // completeness bit honest so an unbounded consumer cannot mistake
        // this approximation for a complete relational summary.
        bounded.addProperty("relationallyComplete", false);
        bounded.addProperty("boundedRelationallyComplete", true);
        // The synthesized guard already refers to the canonical ENVIRONMENT
        // input port.  It neither consumes nor claims a customized-JDK
        // placeholder/materialization certificate copied from the concrete
        // source path.
        bounded.add("vmIntrinsicPlaceholderBindings", new JsonArray());
        bounded.addProperty("normalExit", true);
        bounded.addProperty("exceptionType", "");
        bounded.addProperty("engine", "static-bounded-summary-synthesis");
        bounded.addProperty("confidence", "STATIC_BOUNDED_APPROXIMATION");
        bounded.addProperty("valid", true);
        JsonObject executionAdmission = new JsonObject();
        executionAdmission.addProperty("kind",
                "BOUNDED_ONE_ENTRY_MAP_ITERATOR_APPROXIMATION");
        executionAdmission.addProperty("valid", true);
        executionAdmission.addProperty("authority",
                "EXACT_STATIC_TRANSFORMER_AND_RUNTIME_EMPTY_PRESTATE_V1");
        bounded.add("executionAdmission", executionAdmission);
        bounded.addProperty("targetReplayValidated", false);
        bounded.addProperty("branchOverrideUsed", false);
        bounded.add("replayMaterializationsApplied", new JsonArray());
        bounded.add("modelAssignmentsApplied", new JsonArray());
        bounded.add("exceptionChain", new JsonArray());
        bounded.add("unresolvedInputs", new JsonArray());
        bounded.add("boundedApproximation", evidence.toJson());
        return bounded;
    }

    private static CmpGuardResolution resolveCmpGuard(
            JsonObject guard, List<JsonObject> edges,
            Map<String, List<String>> portsByCell,
            Map<String, JsonObject> ports) {
        String method = string(guard, "method");
        String current = string(guard, "fromCell");
        Matcher branch = JIMPLE_CMP_BRANCH.matcher(string(guard, "unit"));
        if (method.isEmpty() || current.isEmpty() || !branch.matches()
                || !branch.group(1).equals(localName(current))) {
            return CmpGuardResolution.none();
        }
        List<String> proof = new ArrayList<>();
        for (int depth = 0; depth < 8; depth++) {
            List<JsonObject> casts = new ArrayList<>();
            for (JsonObject edge : edges) {
                if (!method.equals(string(edge, "method"))
                        || !current.equals(string(edge, "toCell"))) {
                    continue;
                }
                Matcher cast = JIMPLE_TRANSPARENT_CAST.matcher(string(edge,
                        "unit"));
                if (cast.matches() && cast.group(1).equals(localName(
                        string(edge, "fromCell")))) {
                    casts.add(edge);
                }
            }
            if (casts.size() != 1) break;
            JsonObject cast = casts.get(0);
            current = string(cast, "fromCell");
            proof.add(string(cast, "id"));
        }

        List<JsonObject> compareEdges = new ArrayList<>();
        String compareUnit = "";
        Matcher compare = null;
        for (JsonObject edge : edges) {
            if (!method.equals(string(edge, "method"))
                    || !current.equals(string(edge, "toCell"))) {
                continue;
            }
            Matcher candidate = JIMPLE_CMP_ASSIGNMENT.matcher(string(edge,
                    "unit"));
            if (!candidate.matches()
                    || !candidate.group(1).equals(localName(current))) {
                continue;
            }
            if (compareUnit.isEmpty()) {
                compareUnit = string(edge, "unit");
                compare = candidate;
            } else if (!compareUnit.equals(string(edge, "unit"))) {
                return CmpGuardResolution.none();
            }
            compareEdges.add(edge);
        }
        if (compare == null || compareEdges.size() < 2) {
            return CmpGuardResolution.none();
        }
        String leftCell = uniqueOperandCell(compareEdges, compare.group(2));
        String rightCell = uniqueOperandCell(compareEdges, compare.group(4));
        if (leftCell.isEmpty() || rightCell.isEmpty()) {
            return CmpGuardResolution.none();
        }
        String leftPort = resolveUniqueInputPort(leftCell, method, edges,
                portsByCell);
        String rightPort = resolveUniqueInputPort(rightCell, method, edges,
                portsByCell);
        String operator = requiredCmpRelation(branch.group(2),
                bool(guard, "requiredOutcome", false));
        if (leftPort.isEmpty() || rightPort.isEmpty() || operator.isEmpty()
                || !ports.containsKey(leftPort)
                || !ports.containsKey(rightPort)) {
            return CmpGuardResolution.none();
        }
        for (JsonObject edge : compareEdges) {
            String id = string(edge, "id");
            if (!id.isEmpty() && !proof.contains(id)) proof.add(id);
        }
        return new CmpGuardResolution(true, leftPort, rightPort, operator,
                string(guard, "siteId"), string(guard, "id"), proof);
    }

    private static String resolveUniqueInputPort(
            String start, String method, List<JsonObject> edges,
            Map<String, List<String>> portsByCell) {
        List<String> queue = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        Set<String> result = new LinkedHashSet<>();
        queue.add(start);
        for (int index = 0; index < queue.size() && index < 128; index++) {
            String cell = queue.get(index);
            if (!seen.add(cell)) continue;
            List<String> exact = portsByCell.get(cell);
            if (exact != null) result.addAll(exact);
            if (!result.isEmpty() && index > 16) continue;
            for (JsonObject edge : edges) {
                if (!cell.equals(string(edge, "toCell"))
                        || !method.equals(string(edge, "method"))
                        || "GUARD".equals(string(edge, "transferKind"))
                        || "HEAP_WRITE".equals(string(edge,
                        "transferKind"))) {
                    continue;
                }
                String from = string(edge, "fromCell");
                if (!from.isEmpty() && !seen.contains(from)) queue.add(from);
            }
        }
        return result.size() == 1 ? result.iterator().next() : "";
    }

    private static String uniqueOperandCell(List<JsonObject> edges,
                                            String operand) {
        Set<String> cells = new LinkedHashSet<>();
        for (JsonObject edge : edges) {
            String from = string(edge, "fromCell");
            if (operand.equals(localName(from))) cells.add(from);
        }
        return cells.size() == 1 ? cells.iterator().next() : "";
    }

    private static String localName(String cell) {
        int separator = cell == null ? -1 : cell.lastIndexOf("::");
        return separator < 0 ? firstNonBlank(cell, "")
                : cell.substring(separator + 2);
    }

    private static String requiredCmpRelation(String branchOperator,
                                              boolean requiredOutcome) {
        if (requiredOutcome) return branchOperator;
        if ("==".equals(branchOperator)) return "!=";
        if ("!=".equals(branchOperator)) return "==";
        if ("<".equals(branchOperator)) return ">=";
        if ("<=".equals(branchOperator)) return ">";
        if (">".equals(branchOperator)) return "<=";
        if (">=".equals(branchOperator)) return "<";
        return "";
    }

    private static String swapRelationalOperator(String operator) {
        if ("<".equals(operator)) return ">";
        if ("<=".equals(operator)) return ">=";
        if (">".equals(operator)) return "<";
        if (">=".equals(operator)) return "<=";
        return operator;
    }

    private static boolean exactTransformerObligation(
            JsonObject slice, String mutationSite, String outputCell) {
        int matches = 0;
        for (JsonElement element : array(slice,
                "requestedStateTransformerObligations")) {
            if (!element.isJsonObject()) continue;
            JsonObject obligation = element.getAsJsonObject();
            if (mutationSite.equals(string(obligation, "siteId"))
                    && outputCell.equals(string(obligation, "targetCell"))
                    && "HEAP_WRITE".equals(string(obligation,
                    "transferKind"))
                    && !string(obligation, "authority").isEmpty()
                    && array(obligation, "causalEdgeIds").size() > 0) {
                matches++;
            }
        }
        return matches == 1;
    }

    private static String uniqueAdmittedPort(List<String> candidates,
                                             Set<String> admitted) {
        Set<String> matches = new LinkedHashSet<>();
        if (candidates != null) {
            for (String candidate : candidates) {
                if (admitted.contains(candidate)) matches.add(candidate);
            }
        }
        return matches.size() == 1 ? matches.iterator().next() : "";
    }

    private static List<JsonObject> jsonObjects(JsonArray values) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement value : values) {
            if (value.isJsonObject()) result.add(value.getAsJsonObject());
        }
        return result;
    }

    private static Map<String, JsonObject> indexStaticEdges(
            List<JsonObject> edges) {
        Map<String, JsonObject> result = new LinkedHashMap<>();
        for (JsonObject edge : edges) {
            String id = firstNonBlank(string(edge, "edgeId"),
                    string(edge, "id"));
            if (!id.isEmpty()) result.put(id, edge);
        }
        return result;
    }

    private static List<JsonObject> hydratedCausalEdges(
            JsonObject slice, Map<String, JsonObject> staticEdges) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : array(slice, "causalEdges")) {
            if (!element.isJsonObject()) continue;
            JsonObject compact = element.getAsJsonObject();
            String id = firstNonBlank(string(compact, "edgeId"),
                    string(compact, "id"));
            JsonObject full = staticEdges.get(id);
            JsonObject hydrated = full == null
                    ? compact.deepCopy() : full.deepCopy();
            for (Map.Entry<String, JsonElement> entry : compact.entrySet()) {
                hydrated.add(entry.getKey(), entry.getValue().deepCopy());
            }
            if (!id.isEmpty()) {
                hydrated.addProperty("id", id);
                hydrated.addProperty("edgeId", id);
            }
            result.add(hydrated);
        }
        return result;
    }

    private static boolean isIntegralFieldType(String type) {
        String value = firstNonBlank(type, "").trim();
        return "byte".equals(value) || "short".equals(value)
                || "int".equals(value) || "long".equals(value)
                || "java.lang.Byte".equals(value)
                || "java.lang.Short".equals(value)
                || "java.lang.Integer".equals(value)
                || "java.lang.Long".equals(value);
    }

    private static JsonObject port(JsonObject region, String portId) {
        for (JsonElement element : array(region, "symbolicInputs")) {
            if (!element.isJsonObject()) continue;
            JsonObject port = element.getAsJsonObject();
            if (portId.equals(firstNonBlank(string(port, "portId"),
                    string(port, "symbol")))) return port;
        }
        return new JsonObject();
    }

    private static JsonObject boundedPortExpression(String port,
                                                    String javaType,
                                                    String role) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        String descriptor = javaTypeDescriptor(javaType);
        result.addProperty("_java_type", descriptor.isEmpty()
                ? javaType : descriptor);
        result.addProperty("_exp", "M_" + firstNonBlank(descriptor, "I")
                + "_field_" + port + "_bounded_" + role);
        result.addProperty("_causynth_port", port);
        result.addProperty("_causynth_authority",
                "STATIC_BOUNDED_CANONICAL_INPUT_PORT_V1");
        return result;
    }

    private static JsonArray symbolicInputs(JsonObject activation) {
        JsonArray result = new JsonArray();
        for (JsonElement element : runtimeMaterializationActions(
                activation)) {
            if (!element.isJsonObject()) {
                continue;
            }
            String symbol = string(element.getAsJsonObject(), "symbol");
            if (!symbol.isEmpty()) {
                result.add(symbol);
            }
        }
        return result;
    }

    /**
     * Mirrors {@code ConcolicRegionRuntime.Activation}: a non-empty refined
     * materialization plan replaces (rather than augments) the raw static
     * symbolize list.  Older activation artifacts have no refined list and
     * retain the legacy symbolize behavior.
     */
    private static JsonArray runtimeMaterializationActions(
            JsonObject activation) {
        JsonArray refined = array(activation, "materializations");
        return refined.size() > 0 ? refined : array(activation, "symbolize");
    }

    /**
     * Joins a VM execution-local symbolic array id to exactly one canonical
     * region input.  The bridge is admitted only when the activation action,
     * concrete object identity, finite VM array snapshot, and every array load
     * in the normalized path agree.  This prevents a free SMT array from
     * silently replacing the input that was actually symbolized by the VM.
     */
    private static EngineArrayInputBindingExtraction
    engineArrayInputBindings(JsonObject raw, JsonObject activation,
                             JsonObject region,
                             JsonArray enginePathCondition,
                             JsonArray normalizedPathCondition) {
        List<EngineArrayInputBindingIssue> issues = new ArrayList<>();
        ArrayEventCatalog rawEvents = arrayEvents(enginePathCondition);
        ArrayEventCatalog normalizedEvents = arrayEvents(
                normalizedPathCondition);
        for (String issue : rawEvents.issues) {
            issues.add(new EngineArrayInputBindingIssue(
                    "ENGINE_ARRAY_EVENT_INVALID", issue));
        }
        for (String issue : normalizedEvents.issues) {
            if (!rawEvents.issues.contains(issue)) {
                issues.add(new EngineArrayInputBindingIssue(
                        "ENGINE_ARRAY_EVENT_INVALID", issue));
            }
        }

        Set<String> requiredArrayIds = normalizedEvents.loadIds;
        JsonElement declared = raw.get("engineArrayInputBindings");
        if (declared == null || declared.isJsonNull()) {
            for (String id : requiredArrayIds) {
                issues.add(new EngineArrayInputBindingIssue(
                        "MISSING_ENGINE_ARRAY_INPUT_BINDING", id));
            }
            return new EngineArrayInputBindingExtraction(new JsonArray(),
                    issues.isEmpty(), issues);
        }
        if (!declared.isJsonArray()) {
            issues.add(new EngineArrayInputBindingIssue(
                    "MALFORMED_ENGINE_ARRAY_INPUT_BINDINGS",
                    "expected JSON array"));
            return new EngineArrayInputBindingExtraction(new JsonArray(),
                    false, issues);
        }

        Map<String, List<JsonObject>> actionsByPort = new LinkedHashMap<>();
        for (JsonElement element : runtimeMaterializationActions(activation)) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            String port = string(action, "symbol");
            if (port.isEmpty()) continue;
            List<JsonObject> actions = actionsByPort.get(port);
            if (actions == null) {
                actions = new ArrayList<>();
                actionsByPort.put(port, actions);
            }
            actions.add(action);
        }
        Map<String, List<JsonObject>> regionInputs = new LinkedHashMap<>();
        for (JsonElement element : array(region, "symbolicInputs")) {
            if (!element.isJsonObject()) continue;
            JsonObject input = element.getAsJsonObject();
            String port = firstNonBlank(string(input, "portId"),
                    string(input, "symbol"));
            if (port.isEmpty()) continue;
            List<JsonObject> values = regionInputs.get(port);
            if (values == null) {
                values = new ArrayList<>();
                regionInputs.put(port, values);
            }
            values.add(input);
        }
        Map<String, Integer> observedInputCounts = new LinkedHashMap<>();
        for (JsonElement element : array(raw, "symbolizedInputs")) {
            if (!element.isJsonPrimitive()
                    || !element.getAsJsonPrimitive().isString()) {
                issues.add(new EngineArrayInputBindingIssue(
                        "MALFORMED_SYMBOLIZED_INPUT_FOR_ENGINE_ARRAY",
                        GSON.toJson(element)));
                continue;
            }
            String port = element.getAsString();
            Integer count = observedInputCounts.get(port);
            observedInputCounts.put(port, count == null ? 1 : count + 1);
        }

        List<JsonObject> admitted = new ArrayList<>();
        Set<String> rowIds = new LinkedHashSet<>();
        Map<String, String> portToId = new LinkedHashMap<>();
        Map<String, String> idToPort = new LinkedHashMap<>();
        Map<String, Long> idToToken = new LinkedHashMap<>();
        JsonArray records = declared.getAsJsonArray();
        for (int ordinal = 0; ordinal < records.size(); ordinal++) {
            JsonElement element = records.get(ordinal);
            if (!element.isJsonObject()) {
                issues.add(new EngineArrayInputBindingIssue(
                        "MALFORMED_ENGINE_ARRAY_INPUT_BINDING",
                        "engineArrayInputBindings[" + ordinal
                                + "] is not an object"));
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            List<String> rowIssues = new ArrayList<>();
            String port = string(row, "inputPort");
            String cell = string(row, "inputCell");
            String inputJavaType = string(row, "inputJavaType");
            String descriptorField = string(row,
                    "inputJavaTypeDescriptor");
            String descriptor = javaTypeDescriptor(descriptorField);
            String engineArrayId = string(row, "engineArrayId");
            long objectToken = longInteger(row, "arrayObjectToken", 0L);
            long symbolizationObjectToken = longInteger(row,
                    "symbolizationArrayObjectToken", 0L);
            String activationId = string(activation, "activationId");

            if (integer(row, "schemaVersion", -1) != 1) {
                rowIssues.add("SCHEMA_VERSION_UNSUPPORTED");
            }
            if (!"ENGINE_ARRAY_TO_INPUT_PORT".equals(string(row, "kind"))) {
                rowIssues.add("KIND_INVALID");
            }
            if (activationId.isEmpty() || !activationId.equals(string(row,
                    "sourceActivationId"))) {
                rowIssues.add("SOURCE_ACTIVATION_MISMATCH");
            }
            if (port.isEmpty() || cell.isEmpty() || inputJavaType.isEmpty()
                    || descriptorField.isEmpty() || engineArrayId.isEmpty()) {
                rowIssues.add("REQUIRED_IDENTITY_FIELD_MISSING");
            }
            if (descriptor.isEmpty() || !descriptor.startsWith("[")
                    || !descriptor.equals(descriptorField)
                    || !descriptor.equals(javaTypeDescriptor(
                    inputJavaType))) {
                rowIssues.add("INPUT_ARRAY_TYPE_DESCRIPTOR_INVALID");
            }
            if (!"VM_ACTIVE_SYM_ARRAY_ID_V1".equals(string(row,
                    "engineArrayIdAuthority"))) {
                rowIssues.add("ENGINE_ARRAY_ID_AUTHORITY_INVALID");
            }
            if (!engineArrayIdMatchesComponent(engineArrayId,
                    descriptor)) {
                rowIssues.add("ENGINE_ARRAY_ID_COMPONENT_TYPE_INVALID");
            }
            if (!port.equals(string(row, "symbolizationPrefix"))
                    || !"DIRECT_ARRAY_VALUE_WITH_CANONICAL_INPUT_PREFIX"
                    .equals(string(row, "symbolizationMode"))) {
                rowIssues.add("ARRAY_SYMBOLIZATION_PREFIX_OR_MODE_INVALID");
            }
            if (objectToken <= 0L
                    || symbolizationObjectToken != objectToken
                    || !hasBoolean(row, "sameArrayObjectTokenVerified")
                    || !row.get("sameArrayObjectTokenVerified")
                    .getAsBoolean()
                    || !"SAME_JAVA_REFERENCE_PASSED_TO_SYMBOLIZE_AND_"
                    .concat("EXPRESSION_CAPTURE").equals(string(row,
                            "symbolizationIdentityAuthority"))
                    || !"ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN"
                    .equals(string(row, "objectTokenAuthority"))
                    || !activationId.equals(string(row,
                    "objectTokenScope"))) {
                rowIssues.add("ARRAY_OBJECT_IDENTITY_INVALID");
            }
            if (!"SAME_LIVE_ARRAY_AFTER_EXACT_INPUT_ACTION_SYMBOLIZATION"
                    .equals(string(row, "captureAuthority"))
                    || !hasBoolean(row, "complete")
                    || !row.get("complete").getAsBoolean()) {
                rowIssues.add("CAPTURE_AUTHORITY_OR_COMPLETENESS_INVALID");
            }
            List<JsonObject> actions = actionsByPort.get(port);
            if (actions == null || actions.size() != 1) {
                rowIssues.add("INPUT_ACTION_NOT_UNIQUE");
            } else {
                JsonObject action = actions.get(0);
                String actionDescriptor = javaTypeDescriptor(
                        inputActionJavaType(action));
                if (!cell.equals(string(action, "cell"))) {
                    rowIssues.add("INPUT_ACTION_CELL_MISMATCH");
                }
                if (!descriptor.equals(actionDescriptor)) {
                    rowIssues.add("INPUT_ACTION_TYPE_MISMATCH");
                }
            }
            if (!Integer.valueOf(1).equals(observedInputCounts.get(port))) {
                rowIssues.add("EXACT_INPUT_SYMBOLIZATION_NOT_OBSERVED_ONCE");
            }
            if (!regionInputs.isEmpty()) {
                List<JsonObject> schemas = regionInputs.get(port);
                if (schemas == null || schemas.size() != 1) {
                    rowIssues.add("REGION_INPUT_SCHEMA_NOT_UNIQUE");
                } else {
                    JsonObject schema = schemas.get(0);
                    String schemaCell = string(schema, "cell");
                    String schemaType = firstNonBlank(string(schema,
                            "javaType"), string(schema, "declaredType"),
                            inputCellJavaType(schemaCell));
                    if (!cell.equals(schemaCell)
                            || !descriptor.equals(javaTypeDescriptor(
                            schemaType))) {
                        rowIssues.add("REGION_INPUT_SCHEMA_MISMATCH");
                    }
                }
            }
            validateEngineArrayValueExpression(row, descriptor,
                    engineArrayId, rowIssues);

            if (!rowIds.add(engineArrayId)) {
                rowIssues.add("ENGINE_ARRAY_ID_DUPLICATE");
            }
            String previousId = portToId.put(port, engineArrayId);
            if (previousId != null && !previousId.equals(engineArrayId)) {
                rowIssues.add("INPUT_PORT_TO_ENGINE_ARRAY_ID_NOT_FUNCTIONAL");
            }
            String previousPort = idToPort.put(engineArrayId, port);
            if (previousPort != null && !previousPort.equals(port)) {
                rowIssues.add("ENGINE_ARRAY_ID_TO_INPUT_PORT_NOT_FUNCTIONAL");
            }
            Long previousToken = idToToken.put(engineArrayId, objectToken);
            if (previousToken != null && previousToken.longValue()
                    != objectToken) {
                rowIssues.add("ENGINE_ARRAY_ID_TO_TOKEN_NOT_FUNCTIONAL");
            }
            if (rowIssues.isEmpty()) {
                JsonObject normalized = new JsonObject();
                normalized.addProperty("schemaVersion", 1);
                normalized.addProperty("kind",
                        "ENGINE_ARRAY_TO_INPUT_PORT");
                normalized.addProperty("sourceActivationId", activationId);
                normalized.addProperty("inputPort", port);
                normalized.addProperty("inputCell", cell);
                normalized.addProperty("inputJavaType", inputJavaType);
                normalized.addProperty("inputJavaTypeDescriptor", descriptor);
                normalized.addProperty("symbolizationPrefix", port);
                normalized.addProperty("symbolizationMode",
                        "DIRECT_ARRAY_VALUE_WITH_CANONICAL_INPUT_PREFIX");
                normalized.addProperty("engineArrayId", engineArrayId);
                normalized.addProperty("engineArrayIdAuthority",
                        "VM_ACTIVE_SYM_ARRAY_ID_V1");
                normalized.addProperty("arrayObjectToken", objectToken);
                normalized.addProperty("symbolizationArrayObjectToken",
                        objectToken);
                normalized.addProperty("symbolizationIdentityAuthority",
                        "SAME_JAVA_REFERENCE_PASSED_TO_SYMBOLIZE_AND_"
                                + "EXPRESSION_CAPTURE");
                normalized.addProperty("sameArrayObjectTokenVerified", true);
                normalized.addProperty("objectTokenAuthority",
                        "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
                normalized.addProperty("objectTokenScope", activationId);
                normalized.addProperty("captureAuthority",
                        "SAME_LIVE_ARRAY_AFTER_EXACT_INPUT_ACTION_"
                                + "SYMBOLIZATION");
                normalized.add("arrayValueExpression", object(row,
                        "arrayValueExpression").deepCopy());
                normalized.addProperty("complete", true);
                admitted.add(normalized);
            } else {
                issues.add(new EngineArrayInputBindingIssue(
                        "INVALID_ENGINE_ARRAY_INPUT_BINDING",
                        "engineArrayInputBindings[" + ordinal + "] "
                                + rowIssues));
            }
        }

        Set<String> admittedIds = new LinkedHashSet<>();
        for (JsonObject row : admitted) {
            admittedIds.add(string(row, "engineArrayId"));
        }
        for (String id : requiredArrayIds) {
            if (!admittedIds.contains(id)) {
                issues.add(new EngineArrayInputBindingIssue(
                        "MISSING_ENGINE_ARRAY_INPUT_BINDING", id));
            }
        }
        Collections.sort(admitted, new Comparator<JsonObject>() {
            @Override
            public int compare(JsonObject left, JsonObject right) {
                int port = string(left, "inputPort").compareTo(
                        string(right, "inputPort"));
                return port != 0 ? port : string(left, "engineArrayId")
                        .compareTo(string(right, "engineArrayId"));
            }
        });
        JsonArray normalized = new JsonArray();
        for (JsonObject row : admitted) normalized.add(row);
        return new EngineArrayInputBindingExtraction(normalized,
                issues.isEmpty(), issues);
    }

    private static void validateEngineArrayValueExpression(
            JsonObject row, String descriptor, String engineArrayId,
            List<String> issues) {
        JsonElement rawExpression = row.get("arrayValueExpression");
        if (rawExpression == null || !rawExpression.isJsonObject()) {
            issues.add("ARRAY_VALUE_EXPRESSION_MISSING");
            return;
        }
        JsonObject expression = rawExpression.getAsJsonObject();
        if (!"ArrayValueExpression".equals(string(expression, "_type"))
                || integer(expression, "_schema_version", -1) != 1
                || !"VM_EXACT_FINITE_ARRAY_VALUE_V1".equals(
                string(expression, "_authority"))) {
            issues.add("ARRAY_VALUE_SCHEMA_OR_AUTHORITY_INVALID");
        }
        String expressionDescriptor = string(expression, "_java_type");
        if (!descriptor.equals(expressionDescriptor)
                || !descriptor.equals(javaTypeDescriptor(
                expressionDescriptor))) {
            issues.add("ARRAY_VALUE_JAVA_TYPE_MISMATCH");
        }
        String component = string(expression, "_component_java_type");
        if (!descriptor.startsWith("[")
                || !descriptor.substring(1).equals(component)
                || !component.equals(javaTypeDescriptor(component))) {
            issues.add("ARRAY_VALUE_COMPONENT_TYPE_MISMATCH");
        }
        if (!engineArrayId.equals(string(expression, "_engine_array_id"))
                || !"VM_ACTIVE_SYM_ARRAY_ID_V1".equals(string(expression,
                "_engine_array_id_authority"))
                || !string(row, "engineArrayIdAuthority").equals(
                string(expression, "_engine_array_id_authority"))) {
            issues.add("ARRAY_VALUE_ENGINE_ARRAY_ID_MISMATCH");
        }
        int length = integer(expression, "_concrete_length", -1);
        JsonElement lengthExpression = expression.get("_length_exp");
        if (length < 0 || !validArrayLengthExpression(lengthExpression,
                length)
                || lengthExpression == null
                || !lengthExpression.isJsonObject()
                || !"ConstExpr".equals(string(
                lengthExpression.getAsJsonObject(), "_type"))
                || !hasBoolean(expression, "_elements_complete")
                || !expression.get("_elements_complete").getAsBoolean()) {
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
            JsonElement value = element.get("expression");
            if (index != ordinal || index < 0 || index >= length
                    || !indices.add(index)) {
                issues.add("ARRAY_VALUE_ELEMENT_INDEX_INVALID:" + ordinal);
            }
            if (value == null || !value.isJsonObject()
                    || !validArrayElementProvenance(string(element,
                    "provenance"), value, component)
                    || !arrayElementTypeCompatible(value, component)) {
                issues.add("ARRAY_VALUE_ELEMENT_INVALID:" + ordinal);
            }
        }
    }

    private static String inputActionJavaType(JsonObject action) {
        String explicit = firstNonBlank(string(action, "javaType"),
                string(action, "declaredType"),
                string(action, "inputJavaType"));
        if (!explicit.isEmpty()) return explicit;
        String field = fieldJavaType(string(action, "field"));
        return !field.isEmpty() ? field
                : inputCellJavaType(string(action, "cell"));
    }

    private static String inputCellJavaType(String cell) {
        String fieldOrReturn = fieldJavaType(cell);
        if (!fieldOrReturn.isEmpty()) return fieldOrReturn;
        Matcher parameter = Pattern.compile(
                "\\.param[0-9]+:([^#]+)(?:#.*)?$").matcher(
                cell == null ? "" : cell);
        return parameter.find() ? parameter.group(1).trim() : "";
    }

    private static ArrayEventCatalog arrayEvents(JsonElement value) {
        ArrayEventCatalog result = new ArrayEventCatalog();
        collectArrayEvents(value, result);
        return result;
    }

    private static void collectArrayEvents(JsonElement value,
                                           ArrayEventCatalog result) {
        if (value == null || value.isJsonNull()) return;
        if (value.isJsonArray()) {
            for (JsonElement element : value.getAsJsonArray()) {
                collectArrayEvents(element, result);
            }
            return;
        }
        if (!value.isJsonObject()) return;
        JsonObject object = value.getAsJsonObject();
        if ("_array_expr".equals(string(object, "_type"))) {
            String id = string(object, "_arr_str");
            if (!hasBoolean(object, "_is_load")) {
                result.issues.add("ARRAY_EVENT_LOAD_FLAG_MISSING:"
                        + firstNonBlank(id, "<unnamed>"));
            } else if (!object.get("_is_load").getAsBoolean()) {
                result.issues.add("ENGINE_ARRAY_STORE_UNSUPPORTED:"
                        + firstNonBlank(id, "<unnamed>"));
            } else if (id.isEmpty()) {
                result.issues.add("ENGINE_ARRAY_LOAD_ID_MISSING");
            } else {
                result.loadIds.add(id);
            }
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            collectArrayEvents(entry.getValue(), result);
        }
    }

    private static OutputExpressionExtraction outputExpressions(
            JsonObject raw, JsonObject activation,
            RegionCaptureGoal captureGoal,
            PathNormalization normalization) {
        JsonObject result = new JsonObject();
        JsonElement rootExpression = copy(raw.get("rootOutputExpression"),
                new JsonObject());
        JsonObject requested = object(activation, "requestedOutput");
        String requestedPort = firstNonBlank(string(requested, "portId"),
                string(requested, "symbol"));
        // A true method return is exactly the region root output and remains
        // authorized by rootOutputExpression.  The unsafe case is a
        // SINK_STATE formal carried by an interior outbound call while the
        // selected root itself may return void.
        boolean fieldAssignmentCapture = hasOutputCaptureKind(activation,
                "FIELD_ASSIGNMENT_RHS");
        boolean methodReturnCapture = hasOutputCaptureKind(activation,
                "METHOD_RETURN_VALUE");
        boolean exactRequestedCapture = captureGoal.isOutputClosure()
                && (bool(activation, "requestedOutputCaptureRequired", false)
                || "SINK_STATE".equals(string(requested, "kind"))
                || fieldAssignmentCapture || methodReturnCapture);
        if (exactRequestedCapture) {
            return exactOutputCaptureExpressions(raw, activation,
                    requestedPort, normalization);
        }
        for (JsonElement element : array(activation, "outputs")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject output = element.getAsJsonObject();
            String symbol = string(output, "symbol");
            if (symbol.isEmpty()) {
                continue;
            }
            String location = string(output, "location");
            if ("THROW_OR_BRANCH".equals(location)) {
                JsonObject observation = new JsonObject();
                observation.addProperty("kind", "EXIT_OBSERVATION");
                observation.addProperty("exitKind", string(raw, "exitKind"));
                observation.addProperty("exceptionType",
                        string(raw, "exceptionType"));
                result.add(symbol, observation);
            } else {
                result.add(symbol, rootExpression.deepCopy());
            }
        }
        if (result.size() == 0) {
            result.add("$rootOutput", rootExpression.deepCopy());
        }
        return OutputExpressionExtraction.complete(result,
                "ROOT_RETURN_OR_HEAP_EFFECT");
    }

    private static boolean hasOutputCaptureKind(JsonObject activation,
                                                String captureKind) {
        for (JsonElement element : array(activation,
                "requestedOutputCapture")) {
            if (element.isJsonObject() && captureKind.equals(
                    outputCaptureKind(element.getAsJsonObject()))) {
                return true;
            }
        }
        return false;
    }

    private static String outputCaptureKind(JsonObject capture) {
        return firstNonBlank(string(capture, "captureKind"),
                "CALL_ARGUMENT");
    }

    private static OutputExpressionExtraction exactOutputCaptureExpressions(
            JsonObject raw, JsonObject activation, String requestedPort,
            PathNormalization normalization) {
        JsonObject expressions = new JsonObject();
        List<String> issues = new ArrayList<>();
        if (requestedPort.isEmpty()) {
            issues.add("MISSING_REQUESTED_OUTPUT_PORT");
            return new OutputExpressionExtraction(expressions, false,
                    issues, "EXACT_CALL_ARGUMENT");
        }
        List<JsonObject> requests = new ArrayList<>();
        for (JsonElement element : array(activation,
                "requestedOutputCapture")) {
            if (element.isJsonObject() && requestedPort.equals(string(
                    element.getAsJsonObject(), "outputPort"))) {
                requests.add(element.getAsJsonObject());
            }
        }
        if (!bool(activation, "requestedOutputCaptureComplete", false)) {
            issues.add("REQUESTED_OUTPUT_CAPTURE_PLAN_INCOMPLETE");
        }
        if (requests.size() != 1) {
            issues.add(requests.isEmpty()
                    ? "MISSING_EXACT_OUTPUT_CAPTURE_REQUEST"
                    : "AMBIGUOUS_EXACT_OUTPUT_CAPTURE_REQUEST:"
                    + requests.size());
        }

        boolean fieldAssignment = requests.size() == 1
                && "FIELD_ASSIGNMENT_RHS".equals(outputCaptureKind(
                requests.get(0)));
        boolean methodReturn = requests.size() == 1
                && "METHOD_RETURN_VALUE".equals(outputCaptureKind(
                requests.get(0)));
        boolean callArgument = requests.size() == 1
                && "CALL_ARGUMENT".equals(outputCaptureKind(
                requests.get(0)));
        if (fieldAssignment) {
            validateExactFieldAssignmentRequest(requests.get(0), activation,
                    requestedPort, issues);
            if (!"NORMAL".equals(string(raw, "exitKind"))) {
                issues.add("FIELD_ASSIGNMENT_RHS_REQUIRES_NORMAL_EXIT");
            }
        } else if (methodReturn) {
            validateExactMethodReturnRequest(requests.get(0), activation,
                    requestedPort, issues);
            if (!"NORMAL".equals(string(raw, "exitKind"))) {
                issues.add("METHOD_RETURN_VALUE_REQUIRES_NORMAL_EXIT");
            }
        } else if (requests.size() == 1 && !callArgument) {
            issues.add("UNSUPPORTED_EXACT_OUTPUT_CAPTURE_KIND:"
                    + outputCaptureKind(requests.get(0)));
        }

        List<JsonObject> matches = new ArrayList<>();
        for (JsonObject request : requests) {
            for (JsonElement element : array(raw, "outputCaptures")) {
                if (!element.isJsonObject()) continue;
                JsonObject capture = element.getAsJsonObject();
                if (exactOutputCaptureMatch(request, capture)) {
                    matches.add(capture);
                }
            }
        }
        if (matches.size() != 1) {
            issues.add(matches.isEmpty()
                    ? "MISSING_EXACT_OUTPUT_EXPRESSION_CAPTURE"
                    : "AMBIGUOUS_EXACT_OUTPUT_EXPRESSION_CAPTURE:"
                    + matches.size());
        }
        JsonElement expression = matches.size() == 1
                ? matches.get(0).get("expression") : null;
        ProjectedFieldOutputDischarge projectedFieldDischarge =
                fieldAssignment && matches.size() == 1
                        && !bool(matches.get(0), "expressionCaptured", false)
                        ? projectedFieldOutputDischarge(requests.get(0),
                        matches.get(0), activation)
                        : ProjectedFieldOutputDischarge.notApplicable();
        if (projectedFieldDischarge.complete) {
            expression = projectedFieldDischarge.expression;
        } else if (matches.size() == 1 && !bool(matches.get(0),
                "expressionCaptured", false)) {
            issues.add("OUTPUT_EXPRESSION_CAPTURE_FAILED");
        }
        if (fieldAssignment && matches.size() == 1) {
            validateExactFieldAssignmentCapture(matches.get(0), activation,
                    issues);
            if (isConstantExpression(expression)) {
                validateExactPrimitiveConstantCapture(requests.get(0),
                        matches.get(0), expression.getAsJsonObject(), issues);
            }
        } else if (methodReturn && matches.size() == 1) {
            validateExactMethodReturnCapture(requests.get(0), matches.get(0),
                    issues);
            if (isConstantExpression(expression)) {
                validateExactMethodReturnPrimitiveConstantCapture(
                        requests.get(0), matches.get(0),
                        expression.getAsJsonObject(), issues);
            }
        }
        if (requests.size() == 1) {
            validateExactArrayOutputExpression(requests.get(0), expression,
                    issues);
        }
        Set<String> sliceInputs = new LinkedHashSet<>();
        for (JsonElement input : array(object(activation,
                "requestedOutputSlice"), "inputPorts")) {
            if (input.isJsonPrimitive()) sliceInputs.add(input.getAsString());
        }
        Set<String> expressionSymbols = new LinkedHashSet<>();
        collectSymbolicExpressionSymbols(expression, expressionSymbols);
        ExactPathGuardDependency pathGuardDependency =
                (fieldAssignment || methodReturn)
                        && isConstantExpression(expression)
                        ? exactVmPathGuardDependency(raw, activation,
                        sliceInputs, normalization)
                        : ExactPathGuardDependency.notApplicable();
        boolean guardedConstant = pathGuardDependency.complete;
        boolean dependsOnSliceInput = false;
        boolean everySymbolHasExactSliceInput = true;
        for (String rawSymbol : expressionSymbols) {
            int matchingInputs = 0;
            for (String input : sliceInputs) {
                if (HeapPortResolver.containsSymbolReference(rawSymbol,
                        input)) {
                    dependsOnSliceInput = true;
                    matchingInputs++;
                }
            }
            if (matchingInputs != 1) {
                everySymbolHasExactSliceInput = false;
            }
        }
        if (expression == null || expression.isJsonNull()) {
            issues.add("NON_SYMBOLIC_OUTPUT_EXPRESSION");
        } else if (expressionSymbols.isEmpty() && !guardedConstant) {
            issues.add("NON_SYMBOLIC_OUTPUT_EXPRESSION");
            if ((fieldAssignment || methodReturn)
                    && isConstantExpression(expression)) {
                issues.addAll(pathGuardDependency.issues);
            }
        } else if (!dependsOnSliceInput) {
            if (!guardedConstant) {
                issues.add("OUTPUT_EXPRESSION_HAS_NO_SLICE_INPUT_DEPENDENCY");
            }
        }
        if (fieldAssignment && !expressionSymbols.isEmpty()
                && !everySymbolHasExactSliceInput) {
            issues.add("FIELD_ASSIGNMENT_RHS_RELATION_NOT_CLOSED_OVER_"
                    + "SLICE_INPUTS");
        }
        if (methodReturn && !expressionSymbols.isEmpty()
                && !everySymbolHasExactSliceInput) {
            issues.add("METHOD_RETURN_VALUE_RELATION_NOT_CLOSED_OVER_"
                    + "SLICE_INPUTS");
        }

        boolean outputActionFound = false;
        if (expression != null && !expression.isJsonNull()) {
            for (JsonElement element : array(activation, "outputs")) {
                if (!element.isJsonObject()) continue;
                JsonObject output = element.getAsJsonObject();
                String symbol = string(output, "symbol");
                if (requestedPort.equals(symbol)) {
                    expressions.add(symbol, expression.deepCopy());
                    outputActionFound = true;
                }
            }
        }
        if (!outputActionFound) {
            issues.add("REQUESTED_OUTPUT_ACTION_NOT_FOUND");
        }
        String authority;
        if (fieldAssignment) {
            authority = projectedFieldDischarge.complete
                    ? projectedFieldDischarge.authority
                    : guardedConstant
                    ? "EXACT_FIELD_ASSIGNMENT_RHS_WITH_VM_ATTESTED_PATH_GUARD"
                    : "EXACT_FIELD_ASSIGNMENT_RHS";
        } else if (methodReturn) {
            authority = guardedConstant
                    ? "EXACT_METHOD_RETURN_VALUE_WITH_VM_ATTESTED_PATH_GUARD"
                    : "EXACT_METHOD_RETURN_VALUE";
        } else {
            authority = "EXACT_CALL_ARGUMENT";
        }
        return new OutputExpressionExtraction(expressions,
                issues.isEmpty(), issues, authority);
    }

    /**
     * Discharges a missing VM expression for a reference-valued field write
     * only when the frozen output slice already proves that the RHS is one
     * exact projected field of one canonical input carrier.  The runtime
     * capture remains necessary: it certifies that the assigned reference is
     * exactly the value observed in the declared field after the write.
     *
     * <p>Several static ports can name successive aliases of the same
     * projected value (for example a call return and a callee local).  The
     * canonical carrier is therefore the unique projected binding that can
     * reach every other projected carrier and the assignment RHS in the
     * frozen causal graph.  Ambiguous roots, missing base-cell bindings, or
     * incomplete/external sink closure all fail closed.</p>
     */
    private static ProjectedFieldOutputDischarge
    projectedFieldOutputDischarge(JsonObject request, JsonObject capture,
                                  JsonObject activation) {
        if (!exactMissingReferenceExpressionCapture(capture, activation)) {
            return ProjectedFieldOutputDischarge.notApplicable();
        }
        String descriptor = javaTypeDescriptor(declaredFieldType(
                string(request, "fieldSignature")));
        if (!(descriptor.startsWith("L") || descriptor.startsWith("["))) {
            return ProjectedFieldOutputDischarge.notApplicable();
        }

        JsonObject slice = object(activation, "requestedOutputSlice");
        if (!requestedOutputSliceContractOperationallyAdmitted(activation)
                || !bool(slice,
                "requestedStateTransformerContractApplicable", false)
                || !bool(slice,
                "requestedStateTransformerContractComplete", false)
                || array(slice,
                "requestedStateTransformerContractIssues").size() != 0
                || !bool(slice, "structuralComplete", false)
                || bool(slice, "truncated", true)) {
            return ProjectedFieldOutputDischarge.notApplicable();
        }

        List<ProjectedInputCarrier> carriers = new ArrayList<>();
        Set<String> carrierKeys = new LinkedHashSet<>();
        for (JsonElement element : array(slice, "inputBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!"UNIQUE_EXACT_PROJECTED_VALUE_CARRIER".equals(
                    string(binding, "bindingAuthority"))) {
                continue;
            }
            String inputPort = string(binding, "inputPort");
            String dependencyCell = string(binding, "dependencyCell");
            String baseCell = projectedBaseCell(dependencyCell);
            List<String> fieldPath = projectedFieldPath(dependencyCell);
            if (inputPort.isEmpty() || baseCell.isEmpty()
                    || fieldPath.isEmpty()
                    || countString(slice.get("inputPorts"), inputPort) != 1
                    || !exactRequestedSinkBinding(binding, request)
                    || exactBaseInputBindingCount(slice, inputPort,
                    baseCell, request) != 1
                    || !carrierKeys.add(inputPort + "\n"
                    + dependencyCell)) {
                return ProjectedFieldOutputDischarge.notApplicable();
            }
            carriers.add(new ProjectedInputCarrier(inputPort,
                    dependencyCell, fieldPath));
        }
        if (carriers.isEmpty()) {
            return ProjectedFieldOutputDischarge.notApplicable();
        }

        List<String> expectedPath = carriers.get(0).fieldPath;
        for (ProjectedInputCarrier carrier : carriers) {
            if (!expectedPath.equals(carrier.fieldPath)) {
                return ProjectedFieldOutputDischarge.notApplicable();
            }
        }

        Map<String, Set<String>> graph = exactCausalCellGraph(slice);
        String rhsCell = string(request, "rhsCell");
        List<ProjectedInputCarrier> roots = new ArrayList<>();
        for (ProjectedInputCarrier candidate : carriers) {
            if (!causallyReaches(graph, candidate.dependencyCell,
                    rhsCell)) {
                continue;
            }
            boolean reachesAllCarriers = true;
            for (ProjectedInputCarrier other : carriers) {
                if (!candidate.dependencyCell.equals(other.dependencyCell)
                        && !causallyReaches(graph, candidate.dependencyCell,
                        other.dependencyCell)) {
                    reachesAllCarriers = false;
                    break;
                }
            }
            if (reachesAllCarriers) roots.add(candidate);
        }
        if (roots.size() != 1) {
            return ProjectedFieldOutputDischarge.notApplicable();
        }

        ProjectedInputCarrier root = roots.get(0);
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", descriptor);
        expression.addProperty("_exp", "M_L_projected_"
                + root.inputPort + "_" + projectionPathToken(
                root.fieldPath));
        expression.addProperty("_causynth_projection_kind",
                "EXACT_INPUT_FIELD_PROJECTION");
        expression.addProperty("_causynth_projection_input_port",
                root.inputPort);
        expression.addProperty("_causynth_projection_dependency_cell",
                root.dependencyCell);
        expression.add("_causynth_projection_field_path",
                GSON.toJsonTree(root.fieldPath));
        expression.addProperty("_causynth_projection_authority",
                "UNIQUE_EXACT_PROJECTED_VALUE_CARRIER_CHAIN_PLUS_"
                        + "RUNTIME_POST_ASSIGNMENT_REFERENCE_IDENTITY_V1");
        return ProjectedFieldOutputDischarge.complete(expression,
                "EXACT_FIELD_ASSIGNMENT_RHS_FROM_UNIQUE_PROJECTED_"
                        + "INPUT_CARRIER");
    }

    private static boolean exactMissingReferenceExpressionCapture(
            JsonObject capture, JsonObject activation) {
        JsonElement expression = capture.get("expression");
        long assignedToken = longInteger(capture,
                "assignedValueObjectToken", 0L);
        long observedToken = longInteger(capture,
                "observedFieldValueObjectToken", 0L);
        String assignedClass = string(capture, "assignedValueClass");
        String observedClass = string(capture, "observedFieldValueClass");
        return !bool(capture, "expressionCaptured", false)
                && (expression == null || expression.isJsonNull())
                && "ACTIVE_TOKEN_EXACT_POST_INSTANCE_FIELD_ASSIGNMENT"
                .equals(string(capture, "captureAuthority"))
                && bool(capture, "declaredFieldOwnerVerified", false)
                && bool(capture, "declaredFieldTypeVerified", false)
                && bool(capture, "observedFieldValueAvailable", false)
                && bool(capture, "assignmentIdentityVerified", false)
                && "REFERENCE_IDENTITY".equals(string(capture,
                "assignmentIdentityMode"))
                && "EXACT_DECLARED_FIELD_REFLECTION_AND_REFERENCE_IDENTITY"
                .equals(string(capture, "assignmentIdentityAuthority"))
                && bool(capture, "assignedValueObjectTokenKnown", false)
                && !bool(capture, "assignedValueWasNull", true)
                && !bool(capture, "observedFieldValueWasNull", true)
                && assignedToken > 0 && assignedToken == observedToken
                && !assignedClass.isEmpty() && !"null".equals(assignedClass)
                && assignedClass.equals(observedClass)
                && string(activation, "activationId").equals(
                string(capture, "objectTokenScope"))
                && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(capture, "objectTokenAuthority"));
    }

    private static boolean exactRequestedSinkBinding(
            JsonObject binding, JsonObject request) {
        JsonArray sinks = array(binding,
                "requestedStateTransformerSinkSites");
        return sinks.size() == 1
                && sinks.get(0).isJsonPrimitive()
                && string(request, "siteId").equals(
                sinks.get(0).getAsString())
                && bool(binding,
                "requestedStateTransformerSinkClosureComplete", false)
                && bool(binding,
                "requestedStateTransformerSinkExclusive", false)
                && array(binding,
                "requestedStateTransformerUnclassifiedEdgeIds").size() == 0
                && "STATIC_FORWARD_CAUSAL_CLOSURE_TO_EXACT_"
                .concat("REQUESTED_STATE_TRANSFORMERS").equals(
                        string(binding,
                                "requestedStateTransformerSinkAuthority"));
    }

    private static int exactBaseInputBindingCount(
            JsonObject slice, String inputPort, String baseCell,
            JsonObject request) {
        int count = 0;
        for (JsonElement element : array(slice, "inputBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (inputPort.equals(string(binding, "inputPort"))
                    && baseCell.equals(string(binding, "dependencyCell"))
                    && "EXACT_CELL_IDENTITY".equals(string(binding,
                    "bindingAuthority"))
                    && exactRequestedSinkBinding(binding, request)) {
                count++;
            }
        }
        return count;
    }

    private static String projectedBaseCell(String cell) {
        String value = cell == null ? "" : cell;
        int projection = value.indexOf("#field:");
        return projection <= 0 ? "" : value.substring(0, projection);
    }

    private static List<String> projectedFieldPath(String cell) {
        List<String> result = new ArrayList<>();
        String value = cell == null ? "" : cell;
        Matcher matcher = Pattern.compile("#field:([^#]+)").matcher(
                value);
        int consumed = projectedBaseCell(value).length();
        while (matcher.find()) {
            if (matcher.start() != consumed || matcher.group(1).trim()
                    .isEmpty()) {
                return Collections.emptyList();
            }
            result.add(matcher.group(1).trim());
            consumed = matcher.end();
        }
        return consumed == value.length() ? result
                : Collections.<String>emptyList();
    }

    private static Map<String, Set<String>> exactCausalCellGraph(
            JsonObject slice) {
        Map<String, Set<String>> result = new LinkedHashMap<>();
        for (JsonElement element : array(slice, "causalEdges")) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            String from = string(edge, "fromCell");
            String to = string(edge, "toCell");
            if (from.isEmpty() || to.isEmpty()
                    || string(edge, "edgeId").isEmpty()
                    || string(edge, "method").isEmpty()
                    || string(edge, "siteId").isEmpty()
                    || string(edge, "transferKind").isEmpty()
                    || string(edge, "kind").isEmpty()) {
                continue;
            }
            Set<String> successors = result.get(from);
            if (successors == null) {
                successors = new LinkedHashSet<>();
                result.put(from, successors);
            }
            successors.add(to);
        }
        return result;
    }

    private static boolean causallyReaches(Map<String, Set<String>> graph,
                                           String from, String to) {
        if (from.isEmpty() || to.isEmpty()) return false;
        if (from.equals(to)) return true;
        Set<String> visited = new LinkedHashSet<>();
        List<String> pending = new ArrayList<>();
        pending.add(from);
        for (int index = 0; index < pending.size(); index++) {
            String current = pending.get(index);
            if (!visited.add(current)) continue;
            Set<String> successors = graph.get(current);
            if (successors == null) continue;
            for (String successor : successors) {
                if (to.equals(successor)) return true;
                if (!visited.contains(successor)) pending.add(successor);
            }
        }
        return false;
    }

    private static String projectionPathToken(List<String> fieldPath) {
        StringBuilder result = new StringBuilder();
        for (String field : fieldPath) {
            if (result.length() > 0) result.append('_');
            for (int index = 0; index < field.length(); index++) {
                char current = field.charAt(index);
                result.append(Character.isLetterOrDigit(current)
                        ? current : '_');
            }
        }
        return result.length() == 0 ? "field" : result.toString();
    }

    private static final class ProjectedInputCarrier {
        private final String inputPort;
        private final String dependencyCell;
        private final List<String> fieldPath;

        private ProjectedInputCarrier(String inputPort,
                                      String dependencyCell,
                                      List<String> fieldPath) {
            this.inputPort = inputPort;
            this.dependencyCell = dependencyCell;
            this.fieldPath = new ArrayList<>(fieldPath);
        }
    }

    private static final class ProjectedFieldOutputDischarge {
        private final boolean complete;
        private final JsonObject expression;
        private final String authority;

        private ProjectedFieldOutputDischarge(boolean complete,
                                              JsonObject expression,
                                              String authority) {
            this.complete = complete;
            this.expression = expression;
            this.authority = authority;
        }

        private static ProjectedFieldOutputDischarge notApplicable() {
            return new ProjectedFieldOutputDischarge(false, null, "");
        }

        private static ProjectedFieldOutputDischarge complete(
                JsonObject expression, String authority) {
            return new ProjectedFieldOutputDischarge(true, expression,
                    authority);
        }
    }

    private static boolean isConstantExpression(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                && "ConstExpr".equals(string(
                expression.getAsJsonObject(), "_type"))
                && !string(expression.getAsJsonObject(), "_java_type")
                .isEmpty()
                && !string(expression.getAsJsonObject(), "_exp").isEmpty();
    }

    private static void validateExactPrimitiveConstantCapture(
            JsonObject request, JsonObject capture, JsonObject expression,
            List<String> issues) {
        String descriptor = javaTypeDescriptor(fieldJavaType(firstNonBlank(
                string(request, "fieldSignature"),
                string(request, "outputCell"))));
        if (!("Z".equals(descriptor) || "B".equals(descriptor)
                || "C".equals(descriptor) || "S".equals(descriptor)
                || "I".equals(descriptor) || "J".equals(descriptor))) {
            issues.add("GUARDED_CONSTANT_PRIMITIVE_TYPE_UNSUPPORTED");
            return;
        }
        String wrapper = primitiveWrapperClass(descriptor);
        String payload = string(expression, "_exp");
        String concrete = string(capture, "concretePrimitiveValue");
        boolean exactEnvelope = integer(capture,
                "expressionEnvelopeSchemaVersion", -1) == 1
                && bool(capture, "expressionEnvelopeActive", false)
                && "CONCRETE_PRIMITIVE".equals(string(capture,
                "expressionEnvelopeKind"))
                && !bool(capture, "expressionEnvelopeSymbolic", true)
                && "VM_EXACT_CONCRETE_BOXED_PRIMITIVE_V1".equals(string(
                capture, "expressionEnvelopeAuthority"))
                && descriptor.equals(string(capture,
                "expressionEnvelopeJavaTypeDescriptor"));
        if (!exactEnvelope) {
            issues.add("GUARDED_CONSTANT_VM_PRIMITIVE_ENVELOPE_INVALID");
        }
        if (!descriptor.equals(string(expression, "_java_type"))
                || wrapper.isEmpty()
                || !wrapper.equals(string(capture, "assignedValueClass"))
                || !wrapper.equals(string(capture,
                "observedFieldValueClass"))
                || bool(capture, "assignedValueWasNull", true)
                || bool(capture, "observedFieldValueWasNull", true)
                || !"BOXED_PRIMITIVE_VALUE_EQUALITY".equals(string(capture,
                "assignmentIdentityMode"))) {
            issues.add("GUARDED_CONSTANT_FIELD_TYPE_OR_WRAPPER_MISMATCH");
        }
        if (!validConcretePrimitiveLiteral(descriptor, payload)
                || !samePrimitiveLiteral(descriptor, payload, concrete)) {
            issues.add("GUARDED_CONSTANT_CAPTURE_VALUE_MISMATCH");
        }
    }

    /**
     * Validates a constant captured at an exact method return without
     * borrowing any of the field-assignment reflection contract.  The method
     * signature is the declared type authority; the VM envelope and the
     * concrete boxed value independently attest the captured runtime value.
     */
    private static void validateExactMethodReturnPrimitiveConstantCapture(
            JsonObject request, JsonObject capture, JsonObject expression,
            List<String> issues) {
        String descriptor = javaTypeDescriptor(declaredMethodReturnType(
                string(request, "method")));
        if (!("Z".equals(descriptor) || "B".equals(descriptor)
                || "C".equals(descriptor) || "S".equals(descriptor)
                || "I".equals(descriptor) || "J".equals(descriptor))) {
            issues.add("GUARDED_CONSTANT_METHOD_RETURN_PRIMITIVE_TYPE_"
                    + "UNSUPPORTED");
            return;
        }
        String wrapper = primitiveWrapperClass(descriptor);
        String payload = string(expression, "_exp");
        String concrete = string(capture, "concretePrimitiveValue");
        boolean exactEnvelope = integer(capture,
                "expressionEnvelopeSchemaVersion", -1) == 1
                && bool(capture, "expressionEnvelopeActive", false)
                && "CONCRETE_PRIMITIVE".equals(string(capture,
                "expressionEnvelopeKind"))
                && !bool(capture, "expressionEnvelopeSymbolic", true)
                && "VM_EXACT_CONCRETE_BOXED_PRIMITIVE_V1".equals(string(
                capture, "expressionEnvelopeAuthority"))
                && descriptor.equals(string(capture,
                "expressionEnvelopeJavaTypeDescriptor"));
        if (!exactEnvelope) {
            issues.add("GUARDED_CONSTANT_METHOD_RETURN_VM_PRIMITIVE_"
                    + "ENVELOPE_INVALID");
        }
        if (!descriptor.equals(string(expression, "_java_type"))
                || wrapper.isEmpty()
                || !wrapper.equals(string(capture, "concreteValueClass"))) {
            issues.add("GUARDED_CONSTANT_METHOD_RETURN_TYPE_OR_WRAPPER_"
                    + "MISMATCH");
        }
        if (!validConcretePrimitiveLiteral(descriptor, payload)
                || !samePrimitiveLiteral(descriptor, payload, concrete)) {
            issues.add("GUARDED_CONSTANT_METHOD_RETURN_CAPTURE_VALUE_"
                    + "MISMATCH");
        }
    }

    private static String primitiveWrapperClass(String descriptor) {
        if ("Z".equals(descriptor)) return "java.lang.Boolean";
        if ("B".equals(descriptor)) return "java.lang.Byte";
        if ("C".equals(descriptor)) return "java.lang.Character";
        if ("S".equals(descriptor)) return "java.lang.Short";
        if ("I".equals(descriptor)) return "java.lang.Integer";
        if ("J".equals(descriptor)) return "java.lang.Long";
        return "";
    }

    private static boolean samePrimitiveLiteral(String descriptor,
                                                String expression,
                                                String concrete) {
        String prefix = "Y_" + descriptor + "_";
        if (expression == null || !expression.startsWith(prefix)
                || concrete == null || concrete.trim().isEmpty()) {
            return false;
        }
        String encoded = expression.substring(prefix.length());
        if ("Z".equals(descriptor)) {
            Integer left = booleanLiteral(encoded);
            Integer right = booleanLiteral(concrete.trim());
            return left != null && left.equals(right);
        }
        try {
            return new java.math.BigInteger(encoded).equals(
                    new java.math.BigInteger(concrete.trim()));
        } catch (NumberFormatException malformed) {
            return false;
        }
    }

    private static Integer booleanLiteral(String value) {
        if ("1".equals(value) || "true".equalsIgnoreCase(value)) return 1;
        if ("0".equals(value) || "false".equalsIgnoreCase(value)) return 0;
        return null;
    }

    /**
     * A per-path constant is a relational output when the path guard itself
     * carries the input dependency.  Accept that case only from the exact VM
     * thread-context event contract; a textual branch mapping, an overridden
     * outcome, or an unowned PC index cannot turn a concrete value into a
     * summary relation.
     */
    private static ExactPathGuardDependency exactVmPathGuardDependency(
            JsonObject raw, JsonObject activation, Set<String> sliceInputs,
            PathNormalization normalization) {
        List<String> issues = new ArrayList<>();
        if (bool(raw, "branchOverrideUsed", false)) {
            issues.add("CONSTANT_OUTPUT_PATH_GUARD_USED_BRANCH_OVERRIDE");
            return new ExactPathGuardDependency(false, issues);
        }
        JsonArray enginePath = array(object(raw, "engineSummary"),
                "pathCondition");
        Set<String> sliceMethods = new LinkedHashSet<>();
        for (JsonElement method : array(object(activation,
                "requestedOutputSlice"), "methods")) {
            if (method.isJsonPrimitive()) {
                sliceMethods.add(method.getAsString());
            }
        }
        if (sliceMethods.isEmpty()) {
            issues.add("CONSTANT_OUTPUT_PATH_GUARD_MISSING_SLICE_METHODS");
        }
        int mappedCount = 0;
        boolean dependsOnSliceInput = false;
        for (JsonElement element : array(raw, "branchMappings")) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            int index = integer(mapping, "rawConditionIndex",
                    integer(mapping, "engineConditionIndex",
                            integer(mapping, "conditionIndex", -1)));
            String syntheticIdentity = certifiedConcreteGuardIdentity(
                    mapping);
            boolean certifiedSynthetic = index < 0
                    && normalization != null
                    && normalization.hasSynthetic(syntheticIdentity);
            if (index < 0 && !certifiedSynthetic) continue;
            mappedCount++;
            int occurrence = integer(mapping, "occurrence", -1);
            int baseline = integer(mapping, "rawPathConditionBaseline",
                    integer(mapping, "enginePathConditionBaseline", -1));
            int boundary = integer(mapping, "rawPathConditionSize",
                    integer(mapping, "enginePathConditionSize", -1));
            JsonElement rawCondition = mapping.get("rawCondition");
            JsonElement condition = mapping.get("condition");
            int normalizedIndex = normalization == null
                    ? -1 : certifiedSynthetic
                    ? normalization.syntheticIndex(syntheticIdentity)
                    : normalization.index(index);
            boolean exact = certifiedSynthetic
                    ? exactCertifiedConcretePathGuard(mapping,
                    syntheticIdentity, normalization, sliceMethods)
                    : index < enginePath.size()
                    && normalizedIndex >= 0
                    && normalizedIndex < normalization.conditions.size()
                    && normalization.isSemantic(index)
                    && occurrence > 0
                    && occurrence == integer(mapping, "vmOccurrence", -1)
                    && integer(mapping, "vmBranchEventId", 0) > 0
                    && longInteger(mapping, "vmThreadContextId", 0L) > 0L
                    && longInteger(mapping, "vmOwnerJavaThreadId", 0L) > 0L
                    && longInteger(mapping, "vmOwnerOsThreadId", 0L) > 0L
                    && bool(mapping, "vmBranchEventExpected", false)
                    && bool(mapping, "vmBranchEventValidated", false)
                    && !bool(mapping, "overrideApplied", false)
                    && "NONE".equals(string(mapping, "overrideMode"))
                    && bool(mapping, "outcome", false)
                    == bool(mapping, "observedOutcome", !bool(mapping,
                    "outcome", false))
                    && bool(mapping, "outcome", false)
                    == bool(mapping, "effectiveOutcome", !bool(mapping,
                    "outcome", false))
                    && "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1".equals(
                    string(mapping, "vmBranchEventAuthority"))
                    && "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_PC_INDEX"
                    .equals(string(mapping, "mappingPolicy"))
                    && "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_PC_INDEX"
                    .equals(string(mapping, "conditionAuthority"))
                    && baseline >= 0 && boundary > baseline
                    && index >= baseline && index < boundary
                    && containsInteger(array(mapping,
                    "vmConditionIndices"), index)
                    && rawCondition != null && condition != null
                    && GSON.toJson(enginePath.get(index)).equals(
                    GSON.toJson(rawCondition))
                    && validSemanticBranchCondition(mapping, rawCondition,
                    condition)
                    && sliceMethods.contains(string(mapping, "method"));
            if (!exact) {
                issues.add("CONSTANT_OUTPUT_PATH_GUARD_NOT_EXACT_VM_EVENT");
                continue;
            }
            Set<String> symbols = new LinkedHashSet<>();
            collectSymbolicExpressionSymbols(
                    normalization.conditions.get(normalizedIndex), symbols);
            if (symbols.isEmpty()) {
                issues.add("CONSTANT_OUTPUT_PATH_GUARD_HAS_NO_SYMBOL");
                continue;
            }
            boolean closed = true;
            for (String rawSymbol : symbols) {
                int matchingInputs = 0;
                for (String input : sliceInputs) {
                    if (HeapPortResolver.containsSymbolReference(rawSymbol,
                            input)) {
                        matchingInputs++;
                    }
                }
                if (matchingInputs != 1) {
                    closed = false;
                } else {
                    dependsOnSliceInput = true;
                }
            }
            if (!closed) {
                issues.add("CONSTANT_OUTPUT_PATH_GUARD_NOT_CLOSED_OVER_"
                        + "SLICE_INPUTS");
            }
        }
        if (mappedCount == 0) {
            issues.add("CONSTANT_OUTPUT_MISSING_EXACT_PATH_GUARD");
        }
        if (!dependsOnSliceInput) {
            issues.add("CONSTANT_OUTPUT_PATH_GUARD_HAS_NO_SLICE_INPUT_"
                    + "DEPENDENCY");
        }
        return new ExactPathGuardDependency(issues.isEmpty(), issues);
    }

    private static boolean exactCertifiedConcretePathGuard(
            JsonObject mapping, String identity,
            PathNormalization normalization, Set<String> sliceMethods) {
        int normalizedIndex = normalization.syntheticIndex(identity);
        return normalizedIndex >= 0
                && normalizedIndex < normalization.conditions.size()
                && Boolean.TRUE.equals(strictBoolean(mapping,
                "certifiedConcreteGuard"))
                && CERTIFIED_CONCRETE_GUARD_AUTHORITY.equals(strictString(
                mapping, "conditionAuthority"))
                && CONCRETE_GUARD_CERTIFICATE_AUTHORITY.equals(strictString(
                mapping, "concreteGuardCertificateAuthority"))
                && exactVmConcreteGuardEnvelope(mapping)
                && integer(mapping, "rawConditionIndex", -2) == -1
                && integer(mapping, "engineConditionIndex", -2) == -1
                && integer(mapping, "conditionIndex", -2) == -1
                && integer(mapping, "rawPathConditionBaseline", -1)
                == integer(mapping, "rawPathConditionSize", -2)
                && mapping.has("condition")
                && GSON.toJson(mapping.get("condition")).equals(GSON.toJson(
                normalization.conditions.get(normalizedIndex)))
                && sha256(GSON.toJson(mapping.get("condition"))).equals(
                string(mapping, "certificateConditionSha256"))
                && !exactReferenceNullConditionSymbol(
                mapping.get("condition")).isEmpty()
                && sliceMethods.contains(string(mapping, "method"));
    }

    private static boolean containsInteger(JsonArray values, int expected) {
        for (JsonElement value : values) {
            if (value.isJsonPrimitive() && value.getAsJsonPrimitive()
                    .isNumber() && value.getAsInt() == expected) {
                return true;
            }
        }
        return false;
    }

    private static boolean jsonArrayContainsString(JsonArray values,
                                                   String expected) {
        if (expected == null || expected.isEmpty()) return false;
        for (JsonElement value : values) {
            if (value.isJsonPrimitive()
                    && expected.equals(value.getAsString())) {
                return true;
            }
        }
        return false;
    }

    private static final class ExactPathGuardDependency {
        private final boolean complete;
        private final List<String> issues;

        private ExactPathGuardDependency(boolean complete,
                                         List<String> issues) {
            this.complete = complete;
            this.issues = new ArrayList<>(issues);
        }

        private static ExactPathGuardDependency notApplicable() {
            return new ExactPathGuardDependency(false,
                    Collections.<String>emptyList());
        }
    }

    /**
     * Validates the static/runtime-refined request for one interior scalar
     * method return.  The requested output must be exactly that method's
     * return cell, and the persisted causal edge must be the unique local
     * value passed to the exact return statement.  A call argument or a field
     * assignment cannot satisfy this contract by sharing a port name.
     */
    private static void validateExactMethodReturnRequest(
            JsonObject request, JsonObject activation, String requestedPort,
            List<String> issues) {
        JsonObject requested = object(activation, "requestedOutput");
        JsonObject slice = object(activation, "requestedOutputSlice");
        String requestedCell = string(requested, "cell");
        String method = string(request, "method");
        String site = string(request, "siteId");
        int unitIndex = integer(request, "unitIndex", -1);
        String unit = string(request, "unit").trim();
        String returnExpression = string(request, "returnExpression").trim();
        String returnCell = string(request, "returnCell");
        String edgeId = string(request, "causalEdgeId");

        if (!bool(activation, "requestedOutputCaptureRequired", false)
                || !bool(activation, "requestedOutputCaptureComplete", false)
                || !bool(activation, "requestedOutputSliceComplete", false)
                || !bool(slice, "complete", false)
                || !"RETURN".equals(string(requested, "kind"))
                || !requestedPort.equals(string(request, "outputPort"))
                || !requestedCell.equals(string(request, "outputCell"))
                || !requestedPort.equals(string(slice, "outputPort"))
                || !requestedCell.equals(string(slice, "outputCell"))) {
            issues.add("INVALID_METHOD_RETURN_REQUESTED_OUTPUT_BINDING");
        }
        if (string(request, "captureBindingId").isEmpty()
                || method.isEmpty() || site.isEmpty() || unitIndex < 0
                || !site.equals(method + "#u" + unitIndex)
                || !requestedCell.equals(method + ".return")
                || returnExpression.isEmpty()
                || !exactReturnExpressionCell(method, returnCell,
                returnExpression)
                || !unit.equals("return " + returnExpression)
                || edgeId.isEmpty()
                || !"VALUE_PASS".equals(string(request, "transferKind"))
                || !"method_return".equals(string(request, "bindingKind"))
                || !"STATIC_EXACT_METHOD_RETURN_VALUE".equals(string(
                request, "bindingAuthority"))) {
            issues.add("INVALID_EXACT_METHOD_RETURN_ENDPOINT");
        }
        if (integer(request, "occurrence", 0) < 1
                || !"RUNTIME_EXACT_METHOD_RETURN_OCCURRENCE".equals(string(
                request, "occurrenceAuthority"))) {
            issues.add("INVALID_RUNTIME_METHOD_RETURN_OCCURRENCE_BINDING");
        }
        String returnType = declaredMethodReturnType(method);
        String descriptor = javaTypeDescriptor(returnType);
        if (returnType.isEmpty() || "V".equals(descriptor)
                || !primitiveDescriptor(descriptor)) {
            issues.add("METHOD_RETURN_VALUE_REQUIRES_DECLARED_SCALAR_RETURN");
        }

        boolean exactEdge = false;
        for (JsonElement element : array(slice, "causalEdges")) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            if (edgeId.equals(string(edge, "edgeId"))
                    && method.equals(string(edge, "method"))
                    && site.equals(string(edge, "siteId"))
                    && requestedCell.equals(string(edge, "toCell"))
                    && returnCell.equals(string(edge, "fromCell"))
                    && "VALUE_PASS".equals(string(edge, "transferKind"))
                    && "local_def_use".equals(string(edge, "kind"))) {
                if (exactEdge) {
                    exactEdge = false;
                    break;
                }
                exactEdge = true;
            }
        }
        if (!exactEdge || !jsonArrayContainsString(array(slice,
                "causalEdgeIds"),
                edgeId)) {
            issues.add("METHOD_RETURN_VALUE_CAUSAL_EDGE_NOT_EXACT");
        }
        if (!jsonArrayContainsString(array(slice, "methods"), method)) {
            issues.add("METHOD_RETURN_VALUE_METHOD_NOT_IN_EXACT_SLICE");
        }
    }

    private static boolean exactReturnExpressionCell(
            String method, String cell, String expression) {
        return !method.isEmpty() && !expression.isEmpty()
                && (expression.equals(cell)
                || (method + "::" + expression).equals(cell));
    }

    private static void validateExactMethodReturnCapture(
            JsonObject request, JsonObject capture, List<String> issues) {
        int requestedOccurrence = integer(request, "occurrence", 0);
        if (!"ACTIVE_TOKEN_EXACT_METHOD_RETURN_VALUE".equals(string(
                capture, "captureAuthority"))) {
            issues.add("INVALID_EXACT_METHOD_RETURN_CAPTURE_AUTHORITY");
        }
        if (requestedOccurrence < 1
                || requestedOccurrence != integer(capture,
                "requestedOccurrence", -1)
                || requestedOccurrence != integer(capture,
                "occurrence", -2)) {
            issues.add("METHOD_RETURN_VALUE_CAPTURE_OCCURRENCE_MISMATCH");
        }
    }

    /**
     * Validates the static/runtime-refined half of a field-assignment output
     * capture.  The request must identify the exact putfield statement, its
     * owner expression, and an SMT-eligible RHS value-flow edge belonging to
     * the exact requested-state transformer contract.  Merely naming a void
     * method or a call argument cannot satisfy this contract.
     */
    private static void validateExactFieldAssignmentRequest(
            JsonObject request, JsonObject activation, String requestedPort,
            List<String> issues) {
        JsonObject requested = object(activation, "requestedOutput");
        JsonObject slice = object(activation, "requestedOutputSlice");
        String requestedCell = string(requested, "cell");
        String method = string(request, "method");
        String site = string(request, "siteId");
        int unitIndex = integer(request, "unitIndex", -1);
        String field = string(request, "fieldSignature");
        String ownerExpression = string(request, "fieldOwnerExpression");
        String ownerCell = string(request, "fieldOwnerCell");
        String ownerType = string(request, "fieldOwnerDeclaredType");
        String rhsExpression = string(request, "rhsExpression");
        String rhsCell = string(request, "rhsCell");
        String edgeId = string(request, "rhsCausalEdgeId");
        String unit = string(request, "unit");

        if (!bool(activation, "requestedOutputCaptureRequired", false)
                || !bool(activation, "requestedOutputCaptureComplete", false)
                || !"HEAP_STATE".equals(string(requested, "kind"))
                || !requestedPort.equals(string(request, "outputPort"))
                || !requestedCell.equals(string(request, "outputCell"))
                || !requestedPort.equals(string(slice, "outputPort"))
                || !requestedCell.equals(string(slice, "outputCell"))) {
            issues.add("INVALID_FIELD_ASSIGNMENT_REQUESTED_OUTPUT_BINDING");
        }
        if (string(request, "captureBindingId").isEmpty()
                || method.isEmpty() || site.isEmpty() || unitIndex < 0
                || !site.equals(method + "#u" + unitIndex)
                || !requestedCell.equals(field)
                || !"HEAP_WRITE".equals(string(request, "transferKind"))
                || !"field_write".equals(string(request, "bindingKind"))
                || !"STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_RHS".equals(
                string(request, "bindingAuthority"))) {
            issues.add("INVALID_EXACT_FIELD_ASSIGNMENT_ENDPOINT");
        }

        String declaredOwner = declaredFieldOwner(field);
        if (declaredOwner.isEmpty() || ownerExpression.isEmpty()
                || !ownerType.equals(declaredOwner)
                || !ownerCell.equals(method + "::" + ownerExpression)
                || !"INSTANCE_FIELD_LHS_BASE".equals(string(request,
                "fieldOwnerBindingKind"))
                || !"STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_LHS".equals(
                string(request, "fieldOwnerBindingAuthority"))) {
            issues.add("INVALID_EXACT_FIELD_OWNER_BINDING");
        }

        int equals = unit.indexOf(" = ");
        String lhs = equals < 0 ? "" : unit.substring(0, equals).trim();
        String rhs = equals < 0 ? "" : unit.substring(equals + 3).trim();
        if (!lhs.equals(ownerExpression + "." + field)
                || !rhs.equals(rhsExpression)
                || !exactAssignmentRhsCell(rhsCell, rhsExpression)
                || edgeId.isEmpty()
                || !edgeId.equals(string(request, "causalEdgeId"))
                || !"value_flow".equals(string(request, "rhsRelation"))
                || !bool(request, "rhsRelationComplete", false)
                || !"STATIC_EXACT_HEAP_WRITE_VALUE_FLOW".equals(
                string(request, "rhsRelationAuthority"))) {
            issues.add("INCOMPLETE_EXACT_FIELD_ASSIGNMENT_RHS_RELATION");
        }
        if (integer(request, "occurrence", 0) < 1
                || !"RUNTIME_UNIQUE_STATIC_FIELD_ASSIGNMENT_SITE_"
                .concat("LAST_WRITE_OCCURRENCE").equals(string(request,
                        "occurrenceAuthority"))
                || integer(request, "runtimeFieldOwnerObjectId", 0) <= 0
                || !"RUNTIME_EXACT_FIELD_WRITE_RECEIVER_IDENTITY".equals(
                string(request, "runtimeFieldOwnerBindingAuthority"))) {
            issues.add("INVALID_RUNTIME_FIELD_ASSIGNMENT_OCCURRENCE_BINDING");
        }

        boolean exactEdge = false;
        for (JsonElement element : array(slice, "causalEdges")) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            if (edgeId.equals(string(edge, "edgeId"))
                    && method.equals(string(edge, "method"))
                    && site.equals(string(edge, "siteId"))
                    && rhsCell.equals(string(edge, "fromCell"))
                    && requestedCell.equals(string(edge, "toCell"))
                    && "HEAP_WRITE".equals(string(edge, "transferKind"))
                    && "field_write".equals(string(edge, "kind"))) {
                if (exactEdge) {
                    exactEdge = false;
                    break;
                }
                exactEdge = true;
            }
        }
        if (!exactEdge) {
            issues.add("FIELD_ASSIGNMENT_RHS_CAUSAL_EDGE_NOT_EXACT");
        }

        boolean exactObligation = false;
        for (JsonElement element : array(slice,
                "requestedStateTransformerObligations")) {
            if (!element.isJsonObject()) continue;
            JsonObject obligation = element.getAsJsonObject();
            boolean containsEdge = false;
            for (JsonElement id : array(obligation, "causalEdgeIds")) {
                if (id.isJsonPrimitive()
                        && edgeId.equals(id.getAsString())) {
                    containsEdge = true;
                }
            }
            if (site.equals(string(obligation, "siteId"))
                    && method.equals(string(obligation, "method"))
                    && requestedCell.equals(string(obligation,
                    "targetCell"))
                    && "HEAP_WRITE".equals(string(obligation,
                    "transferKind"))
                    && "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL".equals(
                    string(obligation, "authority"))
                    && containsEdge) {
                if (exactObligation) {
                    exactObligation = false;
                    break;
                }
                exactObligation = true;
            }
        }
        boolean exactContract = integer(slice,
                "requestedStateTransformerContractVersion", -1) == 1
                && bool(slice,
                "requestedStateTransformerContractApplicable", false)
                && bool(slice,
                "requestedStateTransformerContractComplete", false)
                && requestedPort.equals(string(slice,
                "requestedStateTransformerContractOutputPort"))
                && requestedCell.equals(string(slice,
                "requestedStateTransformerContractOutputCell"))
                && "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1".equals(
                string(slice,
                        "requestedStateTransformerContractAuthority"))
                && array(slice,
                "requestedStateTransformerContractIssues").size() == 0;
        if (!exactContract || !exactObligation) {
            issues.add("FIELD_ASSIGNMENT_RHS_NOT_IN_EXACT_TRANSFORMER_"
                    + "CONTRACT");
        }
    }

    private static void validateExactFieldAssignmentCapture(
            JsonObject capture, JsonObject activation,
            List<String> issues) {
        String activationId = string(activation, "activationId");
        if (!"ACTIVE_TOKEN_EXACT_POST_INSTANCE_FIELD_ASSIGNMENT".equals(
                string(capture, "captureAuthority"))
                || !bool(capture, "declaredFieldOwnerVerified", false)
                || !bool(capture, "declaredFieldTypeVerified", false)
                || !bool(capture, "observedFieldValueAvailable", false)
                || !bool(capture, "assignmentIdentityVerified", false)
                || !bool(capture, "fieldOwnerObjectTokenKnown", false)
                || integer(capture, "fieldOwnerObjectToken", 0) <= 0
                || !"ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(capture, "objectTokenAuthority"))
                || activationId.isEmpty()
                || !activationId.equals(string(capture,
                "objectTokenScope"))) {
            issues.add("INVALID_POST_ASSIGNMENT_FIELD_OWNER_OR_VALUE_"
                    + "IDENTITY_PROOF");
        }
        if (integer(capture, "requestedOccurrence", -1)
                != integer(capture, "occurrence", -2)) {
            issues.add("FIELD_ASSIGNMENT_CAPTURE_OCCURRENCE_MISMATCH");
        }
    }

    /**
     * Prevents an array length expression from being admitted as the value of
     * an array-valued region port.  The current VM public API historically
     * returned {@code SymArr::get_length_exp()} for an array, which is a valid
     * scalar expression but is not a relational representation of the array.
     * Until the VM supplies the explicit finite snapshot contract below, an
     * exact array output therefore has to remain relationally incomplete.
     */
    private static void validateExactArrayOutputExpression(
            JsonObject request, JsonElement expression,
            List<String> issues) {
        String declaredType = requestedOutputJavaType(request);
        String expectedDescriptor = javaTypeDescriptor(declaredType);
        if (!expectedDescriptor.startsWith("[")) {
            return;
        }
        if (expression == null || !expression.isJsonObject()
                || !"ArrayValueExpression".equals(string(
                expression.getAsJsonObject(), "_type"))) {
            issues.add("ARRAY_OUTPUT_VALUE_EXPRESSION_REQUIRED");
            return;
        }

        JsonObject arrayValue = expression.getAsJsonObject();
        if (integer(arrayValue, "_schema_version", -1) != 1) {
            issues.add("ARRAY_OUTPUT_SCHEMA_VERSION_UNSUPPORTED");
        }
        if (!"VM_EXACT_FINITE_ARRAY_VALUE_V1".equals(string(arrayValue,
                "_authority"))) {
            issues.add("ARRAY_OUTPUT_AUTHORITY_INVALID");
        }
        String observedDescriptor = javaTypeDescriptor(string(arrayValue,
                "_java_type"));
        if (!expectedDescriptor.equals(observedDescriptor)) {
            issues.add("ARRAY_OUTPUT_JAVA_TYPE_MISMATCH");
        }
        String expectedComponent = expectedDescriptor.substring(1);
        String observedComponent = javaTypeDescriptor(string(arrayValue,
                "_component_java_type"));
        if (!expectedComponent.equals(observedComponent)) {
            issues.add("ARRAY_OUTPUT_COMPONENT_TYPE_MISMATCH");
        }

        int length = integer(arrayValue, "_concrete_length", -1);
        if (length < 0) {
            issues.add("ARRAY_OUTPUT_LENGTH_INVALID");
        }
        if (!validArrayLengthExpression(arrayValue.get("_length_exp"),
                length)) {
            issues.add("ARRAY_OUTPUT_LENGTH_EXPRESSION_INVALID");
        }
        if (!bool(arrayValue, "_elements_complete", false)) {
            issues.add("ARRAY_OUTPUT_ELEMENTS_INCOMPLETE");
        }

        JsonElement elementsValue = arrayValue.get("_elements");
        if (elementsValue == null || !elementsValue.isJsonArray()) {
            issues.add("ARRAY_OUTPUT_ELEMENTS_MISSING");
            return;
        }
        JsonArray elements = elementsValue.getAsJsonArray();
        if (length < 0 || elements.size() != length) {
            issues.add("ARRAY_OUTPUT_ELEMENT_COUNT_MISMATCH");
        }
        Set<Integer> indices = new LinkedHashSet<>();
        for (int ordinal = 0; ordinal < elements.size(); ordinal++) {
            JsonElement elementValue = elements.get(ordinal);
            if (!elementValue.isJsonObject()) {
                issues.add("ARRAY_OUTPUT_ELEMENT_MALFORMED:" + ordinal);
                continue;
            }
            JsonObject element = elementValue.getAsJsonObject();
            int index = integer(element, "index", -1);
            if (index != ordinal || index < 0 || index >= length
                    || !indices.add(index)) {
                issues.add("ARRAY_OUTPUT_ELEMENT_INDEX_INVALID:" + ordinal);
            }
            JsonElement valueExpression = element.get("expression");
            if (valueExpression == null || !valueExpression.isJsonObject()) {
                issues.add("ARRAY_OUTPUT_ELEMENT_EXPRESSION_MISSING:"
                        + ordinal);
                continue;
            }
            String provenance = string(element, "provenance");
            if (!validArrayElementProvenance(provenance, valueExpression,
                    expectedComponent)) {
                issues.add("ARRAY_OUTPUT_ELEMENT_PROVENANCE_UNSUPPORTED:"
                        + ordinal);
            }
            if (!arrayElementTypeCompatible(valueExpression,
                    expectedComponent)) {
                issues.add("ARRAY_OUTPUT_ELEMENT_TYPE_MISMATCH:" + ordinal);
            }
        }
    }

    private static String requestedOutputJavaType(JsonObject request) {
        String fieldType = fieldJavaType(firstNonBlank(string(request,
                "fieldSignature"), string(request, "outputCell")));
        if (!fieldType.isEmpty()) {
            return fieldType;
        }
        Matcher parameter = Pattern.compile(
                "\\.param[0-9]+:([^#]+)(?:#.*)?$").matcher(
                string(request, "outputCell"));
        if (parameter.find()) {
            return parameter.group(1).trim();
        }
        String method = string(request, "method");
        return string(request, "outputCell").equals(method + ".return")
                ? declaredMethodReturnType(method) : "";
    }

    private static boolean validArrayLengthExpression(JsonElement value,
                                                       int concreteLength) {
        if (concreteLength < 0 || value == null || !value.isJsonObject()) {
            return false;
        }
        JsonObject expression = value.getAsJsonObject();
        String type = string(expression, "_type");
        if (!("SymbolExpression".equals(type)
                || "ConSymbolExp".equals(type)
                || "ConstExpr".equals(type))
                || !"I".equals(string(expression, "_java_type"))) {
            return false;
        }
        if (!"ConstExpr".equals(type)) {
            return true;
        }
        String raw = string(expression, "_exp");
        Matcher literal = Pattern.compile("^Y_I_(-?[0-9]+)$")
                .matcher(raw);
        if (!literal.matches()) {
            return false;
        }
        try {
            return Integer.parseInt(literal.group(1)) == concreteLength;
        } catch (NumberFormatException malformed) {
            return false;
        }
    }

    private static boolean validArrayElementProvenance(
            String provenance, JsonElement expression,
            String componentDescriptor) {
        JsonObject value = expression.getAsJsonObject();
        if ("CONCRETE_NULL".equals(provenance)) {
            return (componentDescriptor.startsWith("L")
                    || componentDescriptor.startsWith("["))
                    && "SymbolExpression".equals(string(value, "_type"))
                    && "N".equals(string(value, "_exp"));
        }
        if ("CONCRETE_PRIMITIVE".equals(provenance)) {
            return primitiveDescriptor(componentDescriptor)
                    && "ConstExpr".equals(string(value, "_type"))
                    && componentDescriptor.equals(string(value,
                    "_java_type"))
                    && validConcretePrimitiveLiteral(componentDescriptor,
                    string(value, "_exp"));
        }
        return "ARRAY_SHADOW".equals(provenance)
                || "SYMBOLIC_ELEMENT".equals(provenance);
    }

    private static boolean arrayElementTypeCompatible(
            JsonElement expression, String componentDescriptor) {
        JsonObject value = expression.getAsJsonObject();
        if ("N".equals(string(value, "_exp"))) {
            return componentDescriptor.startsWith("L")
                    || componentDescriptor.startsWith("[");
        }
        return componentDescriptor.equals(javaTypeDescriptor(string(value,
                "_java_type")));
    }

    private static boolean primitiveDescriptor(String descriptor) {
        return descriptor.length() == 1
                && "ZBCSIJFD".contains(descriptor);
    }

    private static boolean engineArrayIdMatchesComponent(
            String engineArrayId, String arrayDescriptor) {
        if (arrayDescriptor == null || !arrayDescriptor.startsWith("[")
                || arrayDescriptor.length() < 2) return false;
        Matcher matcher = ENGINE_ARRAY_ID.matcher(firstNonBlank(
                engineArrayId));
        if (!matcher.matches()) return false;
        char component = arrayDescriptor.charAt(1);
        char expected = "ZBCSIJFD".indexOf(component) >= 0
                ? component : 'L';
        return matcher.group(1).charAt(0) == expected;
    }

    private static boolean validConcretePrimitiveLiteral(
            String descriptor, String expression) {
        if (!primitiveDescriptor(descriptor) || expression == null
                || !expression.startsWith("Y_" + descriptor + "_")) {
            return false;
        }
        String literal = expression.substring(4);
        if ("Z".equals(descriptor)) {
            return "true".equalsIgnoreCase(literal)
                    || "false".equalsIgnoreCase(literal)
                    || "0".equals(literal) || "1".equals(literal);
        }
        if ("F".equals(descriptor) || "D".equals(descriptor)) {
            return literal.matches("[-+]?(?:[0-9]+(?:\\.[0-9]*)?"
                    + "|\\.[0-9]+)(?:[eE][-+]?[0-9]+)?");
        }
        if (!literal.matches("-?(?:0|[1-9][0-9]*)")) {
            return false;
        }
        try {
            java.math.BigInteger value = new java.math.BigInteger(literal);
            if (!value.toString().equals(literal)) return false;
            if ("B".equals(descriptor)) {
                return value.compareTo(java.math.BigInteger.valueOf(
                        Byte.MIN_VALUE)) >= 0
                        && value.compareTo(java.math.BigInteger.valueOf(
                        Byte.MAX_VALUE)) <= 0;
            }
            if ("C".equals(descriptor)) {
                return value.signum() >= 0
                        && value.compareTo(java.math.BigInteger.valueOf(
                        Character.MAX_VALUE)) <= 0;
            }
            if ("S".equals(descriptor)) {
                return value.compareTo(java.math.BigInteger.valueOf(
                        Short.MIN_VALUE)) >= 0
                        && value.compareTo(java.math.BigInteger.valueOf(
                        Short.MAX_VALUE)) <= 0;
            }
            if ("I".equals(descriptor)) {
                return value.compareTo(java.math.BigInteger.valueOf(
                        Integer.MIN_VALUE)) >= 0
                        && value.compareTo(java.math.BigInteger.valueOf(
                        Integer.MAX_VALUE)) <= 0;
            }
            return "J".equals(descriptor)
                    && value.compareTo(java.math.BigInteger.valueOf(
                    Long.MIN_VALUE)) >= 0
                    && value.compareTo(java.math.BigInteger.valueOf(
                    Long.MAX_VALUE)) <= 0;
        } catch (NumberFormatException malformed) {
            return false;
        }
    }

    static boolean engineArrayIdMatchesComponentForTests(
            String engineArrayId, String arrayDescriptor) {
        return engineArrayIdMatchesComponent(engineArrayId, arrayDescriptor);
    }

    static boolean validConcretePrimitiveLiteralForTests(
            String descriptor, String expression) {
        return validConcretePrimitiveLiteral(descriptor, expression);
    }

    private static String declaredMethodReturnType(String method) {
        String value = method == null ? "" : method.trim();
        if (!value.startsWith("<") || !value.endsWith(">")) return "";
        int colon = value.indexOf(':');
        int open = value.indexOf('(', colon + 1);
        int methodName = open < 0 ? -1 : value.lastIndexOf(' ', open);
        if (colon < 0 || methodName <= colon + 1) return "";
        return value.substring(colon + 1, methodName).trim();
    }

    /** Normalizes source names and VM descriptors to one JVM descriptor. */
    private static String javaTypeDescriptor(String type) {
        String value = type == null ? "" : type.trim().replace('.', '/');
        if (value.isEmpty()) return "";
        if (value.startsWith("[")) {
            return value;
        }
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

    private static String declaredFieldOwner(String field) {
        Matcher matcher = Pattern.compile(
                "^<([^:]+):\\s+.+\\s+[^\\s()>]+>$")
                .matcher(field == null ? "" : field.trim());
        return matcher.matches() ? matcher.group(1) : "";
    }

    private static String declaredFieldType(String field) {
        Matcher matcher = Pattern.compile(
                "^<[^:]+:\\s+(.+)\\s+[^\\s()>]+>$")
                .matcher(field == null ? "" : field.trim());
        return matcher.matches() ? matcher.group(1).trim() : "";
    }

    private static String declaredFieldName(String field) {
        Matcher matcher = Pattern.compile(
                "^<[^:]+:\\s+.+\\s+([^\\s()>]+)>$")
                .matcher(field == null ? "" : field.trim());
        return matcher.matches() ? matcher.group(1) : "";
    }

    private static boolean exactAssignmentRhsCell(String cell,
                                                  String rhsExpression) {
        if (cell.isEmpty() || rhsExpression.isEmpty()) return false;
        if (cell.equals(rhsExpression)) return true;
        int local = cell.lastIndexOf("::");
        return local >= 0
                && cell.substring(local + 2).equals(rhsExpression);
    }

    private static void collectSymbolicExpressionSymbols(
            JsonElement expression, Set<String> result) {
        result.addAll(PathRelationInputClosure.freeSymbols(expression));
    }

    private static boolean exactOutputCaptureMatch(JsonObject request,
                                                   JsonObject capture) {
        if (!outputCaptureKind(request).equals(outputCaptureKind(capture))) {
            return false;
        }
        boolean common = string(request, "captureBindingId").equals(
                string(capture, "captureBindingId"))
                && string(request, "outputPort").equals(string(capture,
                "outputPort"))
                && string(request, "outputCell").equals(string(capture,
                "outputCell"))
                && integer(request, "unitIndex", -1) == integer(capture,
                "unitIndex", -2)
                && string(request, "siteId").equals(string(capture,
                "siteId"))
                && integer(request, "occurrence", 0) == integer(capture,
                "occurrence", -1);
        if (!common) return false;
        if ("FIELD_ASSIGNMENT_RHS".equals(outputCaptureKind(request))) {
            return string(request, "method").equals(string(capture,
                    "method"))
                    && string(request, "fieldSignature").equals(string(
                    capture, "fieldSignature"));
        }
        if ("METHOD_RETURN_VALUE".equals(outputCaptureKind(request))) {
            return !string(request, "method").isEmpty()
                    && string(request, "method").equals(string(capture,
                    "method"))
                    && integer(request, "occurrence", 0) == integer(capture,
                    "requestedOccurrence", -1);
        }
        if ("CALL_ARGUMENT".equals(outputCaptureKind(request))) {
            return string(request, "callerMethod").equals(string(capture,
                    "callerMethod"))
                    && string(request, "calleeMethod").equals(string(capture,
                    "calleeMethod"))
                    && integer(request, "argumentIndex", -1) == integer(
                    capture, "argumentIndex", -2);
        }
        return false;
    }

    private static final class OutputExpressionExtraction {
        private final JsonObject expressions;
        private final boolean complete;
        private final List<String> issues;
        private final String authority;

        private OutputExpressionExtraction(JsonObject expressions,
                                           boolean complete,
                                           List<String> issues,
                                           String authority) {
            this.expressions = expressions;
            this.complete = complete;
            this.issues = new ArrayList<>(issues);
            this.authority = authority;
        }

        private static OutputExpressionExtraction complete(
                JsonObject expressions, String authority) {
            return new OutputExpressionExtraction(expressions, true,
                    Collections.<String>emptyList(), authority);
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("complete", complete);
            result.addProperty("authority", authority);
            result.add("issues", GSON.toJsonTree(issues));
            return result;
        }
    }

    private static JsonArray pathSignature(JsonArray pathCondition) {
        JsonArray result = new JsonArray();
        int index = 0;
        for (JsonElement condition : pathCondition) {
            result.add("pc" + index++ + ":" + sha256(GSON.toJson(condition))
                    .substring(0, 12));
        }
        return result;
    }

    /**
     * Admits a semantic guard which has no raw VM path-condition member only
     * when the runtime proves that an exact solver model assignment wrote a
     * null reference and the exact VM branch event consumed that value.  The
     * synthetic condition is intentionally identified by a certificate key,
     * never by a fabricated raw engine index.
     */
    private static CertifiedConcreteGuardCatalog certifiedConcreteGuards(
            JsonObject raw, JsonObject activation, JsonArray rawConditions,
            JsonArray mappings, PathAdmissionPolicy admission) {
        List<CertifiedConcreteGuard> accepted = new ArrayList<>();
        List<String> issues = new ArrayList<>();
        ConcreteGuardProofCatalog proofCatalog = concreteGuardProofCatalog(
                raw, activation);
        issues.addAll(proofCatalog.issues);
        if (!issues.isEmpty()) {
            return new CertifiedConcreteGuardCatalog(accepted, issues);
        }
        Set<String> identities = new LinkedHashSet<>();
        Set<String> consumedProofs = new LinkedHashSet<>();
        int ordinal = 0;
        for (JsonElement element : mappings) {
            if (!element.isJsonObject()) {
                ordinal++;
                continue;
            }
            JsonObject mapping = element.getAsJsonObject();
            List<JsonObject> eventProofs = proofCatalog.forEvent(mapping);
            boolean selfDeclared = mapping.has("certifiedConcreteGuard")
                    || CERTIFIED_CONCRETE_GUARD_AUTHORITY.equals(string(
                    mapping, "conditionAuthority"))
                    || mapping.has("concreteGuardCertificateAuthority");
            if (!selfDeclared && eventProofs.isEmpty()) {
                ordinal++;
                continue;
            }
            JsonObject proof = eventProofs.size() == 1
                    ? eventProofs.get(0) : null;
            String rejection = proof == null
                    ? eventProofs.isEmpty()
                    ? "CERTIFICATE_HAS_NO_ACTIVATION_PROOF"
                    : "CERTIFICATE_EVENT_PROOF_NOT_UNIQUE"
                    : certifiedConcreteGuardRejection(raw, activation,
                    rawConditions, mapping, admission, proof);
            String identity = proof == null ? ""
                    : concreteGuardProofIdentity(proof);
            if (!rejection.isEmpty()) {
                issues.add(firstNonBlank(string(mapping, "siteId"),
                        "mapping@" + ordinal) + ":" + rejection);
            } else if (!identities.add(identity)
                    || !consumedProofs.add(identity)) {
                issues.add(string(mapping, "siteId")
                        + ":DUPLICATE_CERTIFICATE_IDENTITY");
            } else {
                accepted.add(new CertifiedConcreteGuard(identity,
                        integer(mapping, "rawPathConditionBaseline", -1),
                        ordinal, mapping.get("condition")));
            }
            ordinal++;
        }
        for (JsonObject proof : proofCatalog.proofs) {
            String identity = concreteGuardProofIdentity(proof);
            if (!consumedProofs.contains(identity)) {
                issues.add(strictString(proof, "siteId")
                        + ":ACTIVATION_PROOF_HAS_NO_CERTIFIED_MAPPING");
            }
        }
        Collections.sort(accepted, (left, right) -> {
            int byBoundary = Integer.compare(left.rawBoundary,
                    right.rawBoundary);
            return byBoundary != 0 ? byBoundary
                    : Integer.compare(left.mappingOrdinal,
                    right.mappingOrdinal);
        });
        return new CertifiedConcreteGuardCatalog(accepted, issues);
    }

    private static String certifiedConcreteGuardRejection(
            JsonObject raw, JsonObject activation, JsonArray rawConditions,
            JsonObject mapping, PathAdmissionPolicy admission,
            JsonObject proof) {
        Boolean certified = strictBoolean(mapping,
                "certifiedConcreteGuard");
        Integer conditionIndex = strictInteger(mapping,
                "conditionIndex");
        Integer rawIndex = strictInteger(mapping,
                "rawConditionIndex");
        Integer engineIndex = strictInteger(mapping,
                "engineConditionIndex");
        Integer baseline = strictInteger(mapping,
                "rawPathConditionBaseline");
        Integer size = strictInteger(mapping, "rawPathConditionSize");
        Integer added = strictInteger(mapping, "rawPathConditionsAdded");
        Integer candidates = strictInteger(mapping,
                "branchConditionCandidateCount");
        Integer targetAdded = strictInteger(mapping,
                "targetMethodConditionsAdded");
        Integer occurrence = strictInteger(mapping, "occurrence");
        Integer vmOccurrence = strictInteger(mapping, "vmOccurrence");
        Integer certificateOccurrence = strictInteger(mapping,
                "certificateOccurrence");
        Boolean outcome = strictBoolean(mapping, "outcome");
        Boolean observed = strictBoolean(mapping, "observedOutcome");
        Boolean effective = strictBoolean(mapping, "effectiveOutcome");
        Boolean certificateOutcome = strictBoolean(mapping,
                "certificateOutcome");
        if (!Boolean.TRUE.equals(certified)
                || !CERTIFIED_CONCRETE_GUARD_AUTHORITY.equals(
                strictString(mapping, "conditionAuthority"))
                || !CONCRETE_GUARD_CERTIFICATE_AUTHORITY.equals(
                strictString(mapping,
                        "concreteGuardCertificateAuthority"))) {
            return "CERTIFICATE_AUTHORITY_MISMATCH";
        }
        if (conditionIndex == null || conditionIndex != -1
                || rawIndex == null || rawIndex != -1
                || engineIndex == null || engineIndex != -1
                || mapping.has("rawCondition")) {
            return "SYNTHETIC_GUARD_CLAIMS_RAW_VM_INDEX";
        }
        if (baseline == null || size == null || baseline < 0
                || baseline != size || size > rawConditions.size()
                || added == null || added != 0
                || candidates == null || candidates != 0
                || targetAdded == null || targetAdded != 0
                || array(mapping, "vmConditionIndices").size() != 0) {
            return "RAW_PC_BOUNDARY_NOT_EXACTLY_EMPTY";
        }
        if (occurrence == null || occurrence <= 0
                || !occurrence.equals(vmOccurrence)
                || !occurrence.equals(certificateOccurrence)
                || outcome == null || !outcome.equals(observed)
                || !outcome.equals(effective)
                || !outcome.equals(certificateOutcome)) {
            return "BRANCH_EVENT_IDENTITY_MISMATCH";
        }
        String activationId = string(activation, "activationId");
        if (activationId.isEmpty()
                || !activationId.equals(string(raw, "activationId"))
                || !activationId.equals(strictString(mapping,
                "certificateActivationId"))
                || strictString(activation, "pathQueryKey").isEmpty()
                || !strictString(activation, "pathQueryKey").equals(
                strictString(mapping, "certificatePathQueryKey"))
                || !strictString(mapping, "siteId").equals(strictString(
                mapping, "certificateSiteId"))
                || !CONCRETE_GUARD_PROOF_AUTHORITY.equals(strictString(
                mapping, "certificateProofAuthority"))) {
            return "ACTIVATION_OR_SITE_CERTIFICATE_MISMATCH";
        }
        if (!exactCertificateProofJoin(mapping, proof)) {
            return "ACTIVATION_PROOF_CERTIFICATE_MISMATCH";
        }
        if (!exactVmConcreteGuardEnvelope(mapping, proof)) {
            return "VM_BRANCH_EVENT_ENVELOPE_NOT_EXACT";
        }
        String method = strictString(mapping, "method");
        String methodKey = ConcolicCodePosition.sootMethodKey(method);
        if (method.isEmpty() || methodKey.isEmpty()
                || !admission.methodKeys.contains(methodKey)) {
            return "GUARD_METHOD_OUTSIDE_ADMITTED_REGION";
        }
        JsonElement condition = mapping.get("condition");
        String assignmentKey = strictString(mapping,
                "certificateModelAssignmentKey");
        String engineSymbol = exactReferenceNullConditionSymbol(condition);
        if (assignmentKey.isEmpty() || engineSymbol.isEmpty()
                || !condition.equals(proof.get("condition"))
                || !engineSymbol.equals(strictString(mapping,
                "certificateEngineSymbol"))
                || strictString(mapping, "certificateInputSymbol").isEmpty()
                || strictString(mapping,
                "certificateTargetActionSha256").isEmpty()
                || !sha256(GSON.toJson(condition)).equals(strictString(
                mapping, "certificateConditionSha256"))) {
            return "REFERENCE_NULL_CONDITION_CERTIFICATE_MISMATCH";
        }
        JsonObject applied = uniqueAppliedNullAssignment(raw,
                assignmentKey, engineSymbol);
        if (applied == null) {
            return "APPLIED_NULL_MODEL_ASSIGNMENT_NOT_UNIQUE";
        }
        if (!strictString(mapping, "certificateInputSymbol").equals(
                strictString(applied, "inputSymbol"))
                || !strictString(mapping,
                "certificateTargetActionSha256").equals(strictString(
                applied, "targetActionSha256"))
                || !assignmentKey.equals(modelAssignmentKey(applied))) {
            return "APPLIED_NULL_MODEL_ASSIGNMENT_CERTIFICATE_MISMATCH";
        }
        JsonObject declared = uniqueDeclaredNullAssignment(activation,
                applied);
        if (declared == null) {
            return "DECLARED_NULL_MODEL_ASSIGNMENT_NOT_UNIQUE";
        }
        if (!exactAssignmentTarget(declared, applied, activation)) {
            return "MODEL_ASSIGNMENT_ACTION_CERTIFICATE_MISMATCH";
        }
        return "";
    }

    private static boolean exactCertificateProofJoin(
            JsonObject mapping, JsonObject proof) {
        return strictString(mapping, "certificateActivationId").equals(
                strictString(proof, "activationId"))
                && strictString(mapping, "certificatePathQueryKey").equals(
                strictString(proof, "pathQueryKey"))
                && strictString(mapping, "certificateSiteId").equals(
                strictString(proof, "siteId"))
                && java.util.Objects.equals(strictInteger(mapping,
                "certificateOccurrence"), strictInteger(proof,
                "occurrence"))
                && java.util.Objects.equals(strictBoolean(mapping,
                "certificateOutcome"), strictBoolean(proof, "outcome"))
                && strictString(mapping,
                "certificateModelAssignmentKey").equals(strictString(
                proof, "modelAssignmentKey"))
                && strictString(mapping, "certificateEngineSymbol").equals(
                strictString(proof, "engineSymbol"))
                && strictString(mapping, "certificateInputSymbol").equals(
                strictString(proof, "inputSymbol"))
                && strictString(mapping,
                "certificateTargetActionSha256").equals(strictString(
                proof, "targetActionSha256"))
                && strictString(mapping,
                "certificateConditionSha256").equals(strictString(proof,
                "conditionSha256"))
                && strictString(mapping, "certificateProofRole").equals(
                strictString(proof, "proofRole"))
                && java.util.Objects.equals(strictInteger(mapping,
                "certificateSourceConditionIndex"), strictInteger(proof,
                "sourceConditionIndex"))
                && java.util.Objects.equals(strictInteger(mapping,
                "certificateConstraintIndex"), strictInteger(proof,
                "constraintIndex"))
                && java.util.Objects.equals(strictInteger(mapping,
                "certificateExpectedBranchPrefixOrdinal"), strictInteger(
                proof, "expectedBranchPrefixOrdinal"))
                && strictString(mapping, "certificateProofAuthority")
                .equals(strictString(proof, "authority"));
    }

    private static boolean exactVmConcreteGuardEnvelope(
            JsonObject mapping, JsonObject proof) {
        Long eventId = strictLong(mapping, "vmBranchEventId");
        Long contextId = strictLong(mapping, "vmThreadContextId");
        Long javaThreadId = strictLong(mapping, "vmOwnerJavaThreadId");
        Long osThreadId = strictLong(mapping, "vmOwnerOsThreadId");
        JsonElement conditionIndices = mapping.get("vmConditionIndices");
        boolean common = Boolean.TRUE.equals(strictBoolean(mapping,
                "vmBranchEventExpected"))
                && Boolean.TRUE.equals(strictBoolean(mapping,
                "vmBranchEventValidated"))
                && eventId != null && eventId > 0L
                && contextId != null && contextId > 0L
                && javaThreadId != null && javaThreadId > 0L
                && osThreadId != null && osThreadId > 0L
                && "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1".equals(
                strictString(mapping, "vmBranchEventAuthority"))
                && "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_PC_INDEX"
                .equals(strictString(mapping, "mappingPolicy"))
                && Boolean.FALSE.equals(strictBoolean(mapping,
                "overrideApplied"))
                && "NONE".equals(strictString(mapping, "overrideMode"))
                && conditionIndices != null
                && conditionIndices.isJsonArray()
                && conditionIndices.getAsJsonArray().size() == 0
                && "PASS".equals(strictString(mapping,
                "replayValidation"));
        if (!common) return false;
        if ("TARGET".equals(strictString(proof, "proofRole"))) {
            return Boolean.TRUE.equals(strictBoolean(mapping,
                    "scheduledTarget"))
                    && strictBoolean(mapping, "scheduledDesiredOutcome")
                    != null
                    && strictBoolean(mapping, "scheduledDesiredOutcome")
                    .equals(strictBoolean(mapping, "observedOutcome"))
                    && Boolean.TRUE.equals(strictBoolean(mapping,
                    "scheduledOutcomeMatched"));
        }
        return "PREFIX".equals(strictString(proof, "proofRole"))
                && Boolean.FALSE.equals(strictBoolean(mapping,
                "scheduledTarget"))
                && !mapping.has("scheduledDesiredOutcome")
                && !mapping.has("scheduledOutcomeMatched");
    }

    private static boolean exactVmConcreteGuardEnvelope(JsonObject mapping) {
        JsonObject role = new JsonObject();
        role.addProperty("proofRole", strictString(mapping,
                "certificateProofRole"));
        return exactVmConcreteGuardEnvelope(mapping, role);
    }

    private static ConcreteGuardProofCatalog concreteGuardProofCatalog(
            JsonObject raw, JsonObject activation) {
        List<JsonObject> proofs = new ArrayList<>();
        List<String> issues = new ArrayList<>();
        JsonElement observedProofs = raw.get("concreteGuardReplayProofs");
        // The runtime emits an empty proof array for every activation as a
        // stable schema field.  That empty echo does not opt an ordinary seed
        // capture into the nullable-guard certificate protocol.  A malformed
        // or non-empty raw catalog still requires strict validation so that a
        // producer cannot bypass the activation-side declaration.
        boolean rawCatalogRequiresValidation = observedProofs != null
                && (!observedProofs.isJsonArray()
                || observedProofs.getAsJsonArray().size() > 0);
        boolean applicable = "REPLAY_OUTPUT_PATH_FLIP".equals(
                strictString(activation, "executionPhase"))
                || activation.has("concreteGuardReplayProofs")
                || rawCatalogRequiresValidation
                || activation.has("concreteGuardReplayProof")
                || raw.has("concreteGuardReplayProof");
        if (!applicable) {
            return new ConcreteGuardProofCatalog(proofs, issues);
        }
        if (activation.has("concreteGuardReplayProof")
                || raw.has("concreteGuardReplayProof")) {
            issues.add("SINGULAR_CONCRETE_GUARD_PROOF_IS_UNSUPPORTED");
        }
        JsonElement declaredElement = activation.get(
                "concreteGuardReplayProofs");
        JsonElement observedElement = raw.get("concreteGuardReplayProofs");
        if (declaredElement == null || !declaredElement.isJsonArray()
                || observedElement == null || !observedElement.isJsonArray()) {
            issues.add("CONCRETE_GUARD_PROOF_CATALOG_MISSING_OR_MALFORMED");
            return new ConcreteGuardProofCatalog(proofs, issues);
        }
        JsonArray declared = declaredElement.getAsJsonArray();
        JsonArray observed = observedElement.getAsJsonArray();
        if (!declared.equals(observed)) {
            issues.add("RUNTIME_CONCRETE_GUARD_PROOF_CATALOG_MISMATCH");
        }

        List<JsonObject> expected = expectedConcreteGuardProofs(
                activation, issues);
        Set<String> proofIdentities = new LinkedHashSet<>();
        Set<String> eventIdentities = new LinkedHashSet<>();
        Set<String> matchedExpected = new LinkedHashSet<>();
        for (int index = 0; index < declared.size(); index++) {
            JsonElement element = declared.get(index);
            if (!element.isJsonObject()) {
                issues.add("PROOF@" + index + ":PROOF_IS_NOT_OBJECT");
                continue;
            }
            JsonObject proof = element.getAsJsonObject();
            String rejection = concreteGuardProofRejection(activation,
                    proof);
            if (!rejection.isEmpty()) {
                issues.add("PROOF@" + index + ":" + rejection);
                continue;
            }
            String identity = concreteGuardProofIdentity(proof);
            String event = concreteGuardProofEventIdentity(proof);
            if (!proofIdentities.add(identity)) {
                issues.add("PROOF@" + index + ":DUPLICATE_PROOF_IDENTITY");
                continue;
            }
            if (!eventIdentities.add(event)) {
                issues.add("PROOF@" + index + ":DUPLICATE_PROOF_EVENT");
                continue;
            }
            JsonObject expectedProof = uniqueExpectedProof(expected, proof);
            if (expectedProof == null) {
                issues.add("PROOF@" + index
                        + ":PROOF_NOT_DERIVED_FROM_REPLAY_CONSTRAINT");
                continue;
            }
            matchedExpected.add(concreteGuardProofIdentity(expectedProof));
            proofs.add(proof);
        }
        for (JsonObject expectedProof : expected) {
            String identity = concreteGuardProofIdentity(expectedProof);
            if (!matchedExpected.contains(identity)) {
                issues.add(strictString(expectedProof, "siteId")
                        + ":DERIVED_NULL_GUARD_PROOF_MISSING");
            }
        }
        return new ConcreteGuardProofCatalog(proofs, issues);
    }

    private static List<JsonObject> expectedConcreteGuardProofs(
            JsonObject activation, List<String> issues) {
        JsonElement contractElement = activation.get("replayContract");
        if (contractElement != null) {
            return expectedConcreteGuardProofsFromContract(activation,
                    contractElement, issues);
        }
        List<JsonObject> result = new ArrayList<>();
        JsonElement constraintsElement = activation.get(
                "pathReplayConstraints");
        JsonElement prefixElement = activation.get("expectedBranchPrefix");
        JsonElement negated = activation.get("pathReplayNegatedCondition");
        Integer targetIndex = strictInteger(activation,
                "pathReplayTargetConditionIndex");
        JsonObject target = object(activation, "targetBranch");
        if (constraintsElement == null || !constraintsElement.isJsonArray()
                || prefixElement == null || !prefixElement.isJsonArray()
                || negated == null || !negated.isJsonObject()
                || targetIndex == null || targetIndex < 0) {
            issues.add("PATH_REPLAY_PROOF_SOURCE_MISSING_OR_MALFORMED");
            return result;
        }
        JsonArray constraints = constraintsElement.getAsJsonArray();
        JsonArray prefix = prefixElement.getAsJsonArray();
        if (constraints.size() != targetIndex + 1
                || targetIndex >= constraints.size()
                || !negated.equals(constraints.get(targetIndex))) {
            issues.add("PATH_REPLAY_CONSTRAINT_CARDINALITY_OR_TARGET_MISMATCH");
            return result;
        }
        Set<String> events = new LinkedHashSet<>();
        Set<Integer> prefixEventIndices = new LinkedHashSet<>();
        int previousSourceIndex = -1;
        for (int prefixOrdinal = 0; prefixOrdinal < prefix.size();
             prefixOrdinal++) {
            JsonElement rowElement = prefix.get(prefixOrdinal);
            if (!rowElement.isJsonObject()) {
                issues.add("PREFIX@" + prefixOrdinal + ":NOT_OBJECT");
                continue;
            }
            JsonObject row = rowElement.getAsJsonObject();
            Integer sourceIndex = strictInteger(row, "conditionIndex");
            String site = strictString(row, "siteId");
            Integer occurrence = strictInteger(row, "occurrence");
            Boolean outcome = strictBoolean(row, "outcome");
            Boolean proofRequired = strictBoolean(row,
                    "concreteGuardReplayProofRequired");
            if (sourceIndex == null || sourceIndex <= previousSourceIndex
                    || sourceIndex < 0 || sourceIndex >= targetIndex) {
                issues.add("PREFIX@" + prefixOrdinal
                        + ":CONDITION_INDEX_MALFORMED_OR_UNORDERED");
                continue;
            }
            previousSourceIndex = sourceIndex;
            prefixEventIndices.add(sourceIndex);
            if (site.isEmpty() || occurrence == null || occurrence <= 0
                    || outcome == null
                    || !events.add(site + "\u0000" + occurrence)) {
                issues.add("PREFIX@" + prefixOrdinal
                        + ":EVENT_IDENTITY_MALFORMED_OR_DUPLICATE");
                continue;
            }
            if (row.has("concreteGuardReplayProofRequired")
                    && proofRequired == null) {
                issues.add("PREFIX@" + prefixOrdinal
                        + ":CONCRETE_GUARD_PROOF_MARKER_MALFORMED");
                continue;
            }
            // Absence retains the legacy fail-closed meaning.  New worklist
            // rows always carry this exact boolean; false means the guard is
            // represented by its real VM path-condition member and therefore
            // must not also acquire a synthetic concrete-guard proof.
            if (!Boolean.FALSE.equals(proofRequired)) {
                addExpectedConcreteGuardProof(result, activation,
                        constraints, "PREFIX", site, occurrence, outcome,
                        sourceIndex, prefixOrdinal, issues);
            }
        }
        for (int sourceIndex = 0; sourceIndex < targetIndex; sourceIndex++) {
            String engineSymbol = exactReferenceNullConditionSymbol(
                    constraints.get(sourceIndex));
            if (!engineSymbol.isEmpty()
                    && !prefixEventIndices.contains(sourceIndex)) {
                issues.add("CONSTRAINT@" + sourceIndex
                        + ":NULL_GUARD_EVENT_ROW_MISSING");
            }
        }
        String targetSite = strictString(target, "siteId");
        Integer targetOccurrence = strictInteger(target, "occurrence");
        Boolean targetOutcome = strictBoolean(target, "desiredOutcome");
        Boolean targetProofRequired = strictBoolean(target,
                "concreteGuardReplayProofRequired");
        if (targetSite.isEmpty() || targetOccurrence == null
                || targetOccurrence <= 0 || targetOutcome == null
                || !events.add(targetSite + "\u0000" + targetOccurrence)) {
            issues.add("TARGET:EVENT_IDENTITY_MALFORMED_OR_DUPLICATE");
        } else if (target.has("concreteGuardReplayProofRequired")
                && targetProofRequired == null) {
            issues.add("TARGET:CONCRETE_GUARD_PROOF_MARKER_MALFORMED");
        } else if (!Boolean.FALSE.equals(targetProofRequired)) {
            addExpectedConcreteGuardProof(result, activation, constraints,
                    "TARGET", targetSite, targetOccurrence, targetOutcome,
                    targetIndex, -1, issues);
        }
        return result;
    }

    private static List<JsonObject> expectedConcreteGuardProofsFromContract(
            JsonObject activation, JsonElement encoded,
            List<String> issues) {
        List<JsonObject> result = new ArrayList<>();
        final BranchReplayContract contract;
        try {
            contract = BranchReplayContract.fromJson(
                    encoded.getAsJsonObject());
        } catch (RuntimeException malformed) {
            issues.add("BRANCH_REPLAY_CONTRACT_MALFORMED:"
                    + malformed.getMessage());
            return result;
        }
        JsonArray constraints = contract.requiredPathPredicates();
        Set<String> events = new LinkedHashSet<>();
        int ordinal = 0;
        for (BranchWitness witness : contract.orderedPrefix()) {
            if (!events.add(witness.siteId() + "\u0000"
                    + witness.occurrence())) {
                issues.add("PREFIX@" + ordinal
                        + ":DUPLICATE_BRANCH_EVENT");
            } else if (BranchWitness.CERTIFIED_NO_PC.equals(
                    witness.evidenceKind())) {
                addExpectedConcreteGuardProof(result, activation,
                        constraints, "PREFIX", witness.siteId(),
                        witness.occurrence(), witness.sourceTakenOutcome(),
                        ordinal, ordinal, issues);
            }
            ordinal++;
        }
        BranchWitness source = contract.source();
        if (!events.add(source.siteId() + "\u0000"
                + source.occurrence())) {
            issues.add("TARGET:DUPLICATE_BRANCH_EVENT");
        } else if (BranchWitness.CERTIFIED_NO_PC.equals(
                source.evidenceKind())) {
            addExpectedConcreteGuardProof(result, activation, constraints,
                    "TARGET", source.siteId(), source.occurrence(),
                    contract.requiredTakenOutcome(),
                    contract.orderedPrefix().size(), -1, issues);
        }
        return result;
    }

    private static void addExpectedConcreteGuardProof(
            List<JsonObject> result, JsonObject activation,
            JsonArray constraints, String role, String site, int occurrence,
            boolean outcome, int sourceIndex, int prefixOrdinal,
            List<String> issues) {
        JsonElement condition = constraints.get(sourceIndex);
        if (!condition.isJsonObject()) {
            issues.add(role + "@" + sourceIndex + ":CONDITION_NOT_OBJECT");
            return;
        }
        String engineSymbol = exactReferenceNullConditionSymbol(condition);
        if (engineSymbol.isEmpty()) return;
        JsonObject assignment = uniqueDeclaredNullAssignmentForEngine(
                activation, engineSymbol);
        if (assignment == null) {
            issues.add(role + "@" + sourceIndex
                    + ":NULL_CONDITION_ASSIGNMENT_NOT_UNIQUE");
            return;
        }
        String assignmentKey = modelAssignmentKey(assignment);
        String inputSymbol = strictString(assignment, "inputSymbol");
        JsonElement action = assignment.get("target");
        if (assignmentKey.isEmpty() || inputSymbol.isEmpty()
                || action == null || !action.isJsonObject()) {
            issues.add(role + "@" + sourceIndex
                    + ":NULL_ASSIGNMENT_IDENTITY_INCOMPLETE");
            return;
        }
        JsonObject expected = new JsonObject();
        expected.addProperty("schemaVersion", 1);
        expected.addProperty("kind", CONCRETE_GUARD_PROOF_KIND);
        expected.addProperty("authority", CONCRETE_GUARD_PROOF_AUTHORITY);
        expected.addProperty("activationId", strictString(activation,
                "activationId"));
        expected.addProperty("pathQueryKey", strictString(activation,
                "pathQueryKey"));
        expected.addProperty("proofRole", role);
        expected.addProperty("sourceConditionIndex", sourceIndex);
        expected.addProperty("constraintIndex", sourceIndex);
        expected.addProperty("expectedBranchPrefixOrdinal", prefixOrdinal);
        expected.addProperty("siteId", site);
        expected.addProperty("occurrence", occurrence);
        expected.addProperty("outcome", outcome);
        expected.addProperty("modelAssignmentKey", assignmentKey);
        expected.addProperty("engineSymbol", engineSymbol);
        expected.addProperty("inputSymbol", inputSymbol);
        expected.addProperty("targetActionSha256",
                sha256(GSON.toJson(action)));
        expected.add("condition", condition.deepCopy());
        expected.addProperty("conditionSha256",
                sha256(GSON.toJson(condition)));
        expected.addProperty("requiresExactVmBranchEvent", true);
        expected.addProperty("requiresZeroPathConditionSuffix", true);
        expected.addProperty("requiresUniqueAppliedNullModelAssignment",
                true);
        expected.addProperty("branchOverrideProhibited", true);
        result.add(expected);
    }

    private static JsonObject uniqueDeclaredNullAssignmentForEngine(
            JsonObject activation, String engineSymbol) {
        JsonObject result = null;
        for (JsonElement element : array(activation, "modelAssignments")) {
            if (!element.isJsonObject()) continue;
            JsonObject assignment = element.getAsJsonObject();
            if (!engineSymbol.equals(strictString(assignment,
                    "engineSymbol"))) continue;
            JsonElement targetElement = assignment.get("target");
            JsonObject target = targetElement != null
                    && targetElement.isJsonObject()
                    ? targetElement.getAsJsonObject() : null;
            if (result != null || target == null
                    || modelAssignmentKey(assignment).isEmpty()
                    || strictString(assignment, "solverSymbol").isEmpty()
                    || strictString(assignment, "inputSymbol").isEmpty()
                    || !strictString(assignment, "inputSymbol").equals(
                    strictString(target, "symbol"))
                    || !"NULL".equals(strictString(assignment,
                    "valueType"))
                    || !"null".equals(strictString(assignment, "value"))
                    || !"Z3_PATH_FLIP_MODEL".equals(strictString(
                    assignment, "authority"))
                    || !Boolean.TRUE.equals(strictBoolean(assignment,
                    "materializeAtRealDefinition"))
                    || !Boolean.TRUE.equals(strictBoolean(assignment,
                    "modelIsNull"))
                    || strictString(assignment,
                    "nullnessSolverSymbol").isEmpty()
                    || !exactReferenceAssignmentEncoding(assignment,
                    target)
                    || !exactTargetActionInRuntimeCatalog(activation,
                    target)) {
                return null;
            }
            String declaredHash = strictString(assignment,
                    "targetActionSha256");
            if (!declaredHash.isEmpty() && !declaredHash.equals(
                    sha256(GSON.toJson(target)))) return null;
            result = assignment;
        }
        return result;
    }

    private static boolean exactTargetActionInRuntimeCatalog(
            JsonObject activation, JsonObject target) {
        int matches = 0;
        for (JsonElement action : runtimeMaterializationActions(activation)) {
            if (target.equals(action)) matches++;
        }
        return matches == 1;
    }

    private static String concreteGuardProofRejection(
            JsonObject activation, JsonObject proof) {
        Integer schema = strictInteger(proof, "schemaVersion");
        Integer sourceIndex = strictInteger(proof,
                "sourceConditionIndex");
        Integer constraintIndex = strictInteger(proof, "constraintIndex");
        Integer prefixOrdinal = strictInteger(proof,
                "expectedBranchPrefixOrdinal");
        Integer occurrence = strictInteger(proof, "occurrence");
        Boolean outcome = strictBoolean(proof, "outcome");
        String role = strictString(proof, "proofRole");
        JsonElement condition = proof.get("condition");
        if (!Integer.valueOf(1).equals(schema)
                || !CONCRETE_GUARD_PROOF_KIND.equals(strictString(proof,
                "kind"))
                || !CONCRETE_GUARD_PROOF_AUTHORITY.equals(strictString(
                proof, "authority"))
                || sourceIndex == null || sourceIndex < 0
                || constraintIndex == null || constraintIndex < 0
                || !sourceIndex.equals(constraintIndex)
                || prefixOrdinal == null
                || !("PREFIX".equals(role) && prefixOrdinal >= 0
                || "TARGET".equals(role) && prefixOrdinal == -1)
                || occurrence == null || occurrence <= 0 || outcome == null
                || strictString(proof, "siteId").isEmpty()
                || strictString(proof, "modelAssignmentKey").isEmpty()
                || strictString(proof, "engineSymbol").isEmpty()
                || strictString(proof, "inputSymbol").isEmpty()
                || !strictString(proof, "targetActionSha256").matches(
                "[0-9a-f]{64}")
                || condition == null || !condition.isJsonObject()
                || !strictString(proof, "conditionSha256").matches(
                "[0-9a-f]{64}")
                || !Boolean.TRUE.equals(strictBoolean(proof,
                "requiresExactVmBranchEvent"))
                || !Boolean.TRUE.equals(strictBoolean(proof,
                "requiresZeroPathConditionSuffix"))
                || !Boolean.TRUE.equals(strictBoolean(proof,
                "requiresUniqueAppliedNullModelAssignment"))
                || !Boolean.TRUE.equals(strictBoolean(proof,
                "branchOverrideProhibited"))) {
            return "PROOF_SCHEMA_OR_REQUIRED_FLAGS_MALFORMED";
        }
        if (!strictString(activation, "activationId").equals(strictString(
                proof, "activationId"))
                || !strictString(activation, "pathQueryKey").equals(
                strictString(proof, "pathQueryKey"))) {
            return "PROOF_ACTIVATION_OR_QUERY_MISMATCH";
        }
        String engineSymbol = exactReferenceNullConditionSymbol(condition);
        if (!strictString(proof, "engineSymbol").equals(engineSymbol)
                || !strictString(proof, "conditionSha256").equals(
                sha256(GSON.toJson(condition)))) {
            return "PROOF_CONDITION_OR_HASH_MISMATCH";
        }
        JsonObject assignment = uniqueDeclaredNullAssignmentForEngine(
                activation, engineSymbol);
        if (assignment == null
                || !modelAssignmentKey(assignment).equals(strictString(
                proof, "modelAssignmentKey"))
                || !strictString(assignment, "inputSymbol").equals(
                strictString(proof, "inputSymbol"))
                || !sha256(GSON.toJson(assignment.get("target"))).equals(
                strictString(proof, "targetActionSha256"))) {
            return "PROOF_DECLARED_NULL_ASSIGNMENT_MISMATCH";
        }
        return "";
    }

    private static JsonObject uniqueExpectedProof(
            List<JsonObject> expected, JsonObject actual) {
        JsonObject result = null;
        for (JsonObject candidate : expected) {
            if (!candidate.equals(actual)) continue;
            if (result != null) return null;
            result = candidate;
        }
        return result;
    }

    private static String concreteGuardProofIdentity(JsonObject proof) {
        return strictString(proof, "activationId") + "\n"
                + strictString(proof, "pathQueryKey") + "\n"
                + strictString(proof, "proofRole") + "\n"
                + integer(proof, "sourceConditionIndex", -1) + "\n"
                + integer(proof, "constraintIndex", -1) + "\n"
                + integer(proof, "expectedBranchPrefixOrdinal", -2) + "\n"
                + strictString(proof, "siteId") + "\n"
                + integer(proof, "occurrence", -1) + "\n"
                + strictBoolean(proof, "outcome") + "\n"
                + strictString(proof, "modelAssignmentKey") + "\n"
                + strictString(proof, "conditionSha256");
    }

    private static String concreteGuardProofEventIdentity(JsonObject proof) {
        return strictString(proof, "siteId") + "\u0000"
                + integer(proof, "occurrence", -1);
    }

    private static JsonObject uniqueAppliedNullAssignment(
            JsonObject raw, String assignmentKey, String engineSymbol) {
        JsonObject result = null;
        for (JsonElement element : array(raw, "modelAssignmentsApplied")) {
            if (!element.isJsonObject()) continue;
            JsonObject assignment = element.getAsJsonObject();
            if (!assignmentKey.equals(strictString(assignment,
                    "modelAssignmentKey"))) continue;
            if (result != null
                    || !engineSymbol.equals(strictString(assignment,
                    "engineSymbol"))
                    || strictString(assignment, "inputSymbol").isEmpty()
                    || !"NULL".equals(strictString(assignment,
                    "valueType"))
                    || !"null".equals(strictString(assignment, "value"))
                    || !Boolean.TRUE.equals(strictBoolean(assignment,
                    "modelIsNull"))
                    || strictString(assignment,
                    "nullnessSolverSymbol").isEmpty()
                    || !("JAVA_STRING_CONTENT_PLUS_EXPLICIT_"
                    .concat("NULLNESS_BOOL_V1").equals(strictString(
                    assignment, "nullableStringEncodingAuthority"))
                    || "JAVA_REFERENCE_NULLNESS_AS_EXACT_REF_EQUALITY_V1"
                    .equals(strictString(assignment,
                    "referenceNullnessEncodingAuthority")))
                    || !"null".equals(strictString(assignment,
                    "concreteValueClass"))
                    || !Boolean.FALSE.equals(strictBoolean(assignment,
                    "branchOverride"))
                    || !"Z3_PATH_FLIP_MODEL".equals(strictString(
                    assignment, "authority"))
                    || !Boolean.TRUE.equals(strictBoolean(assignment,
                    "materializeAtRealDefinition"))) {
                return null;
            }
            result = assignment;
        }
        return result;
    }

    private static JsonObject uniqueDeclaredNullAssignment(
            JsonObject activation, JsonObject applied) {
        JsonObject result = null;
        for (JsonElement element : array(activation, "modelAssignments")) {
            if (!element.isJsonObject()) continue;
            JsonObject declared = element.getAsJsonObject();
            if (!strictString(applied, "engineSymbol").equals(
                    strictString(declared, "engineSymbol"))
                    || !strictString(applied, "inputSymbol").equals(
                    strictString(declared, "inputSymbol"))
                    || !"NULL".equals(strictString(declared,
                    "valueType"))
                    || !"null".equals(strictString(declared, "value"))
                    || !Boolean.TRUE.equals(strictBoolean(declared,
                    "modelIsNull"))
                    || !strictString(applied, "nullnessSolverSymbol")
                    .equals(strictString(declared,
                    "nullnessSolverSymbol"))
                    || !strictString(applied,
                    "nullableStringEncodingAuthority").equals(strictString(
                    declared, "nullableStringEncodingAuthority"))
                    || !strictString(applied,
                    "referenceNullnessEncodingAuthority").equals(
                    strictString(declared,
                            "referenceNullnessEncodingAuthority"))) {
                continue;
            }
            if (result != null) return null;
            result = declared;
        }
        return result;
    }

    private static boolean exactAssignmentTarget(
            JsonObject declared, JsonObject applied,
            JsonObject activation) {
        if (!strictString(declared, "authority").equals(strictString(
                applied, "authority"))
                || !Boolean.TRUE.equals(strictBoolean(declared,
                "materializeAtRealDefinition"))
                || !declared.has("target") || !applied.has("target")
                || !GSON.toJson(declared.get("target")).equals(
                GSON.toJson(applied.get("target")))) {
            return false;
        }
        String targetHash = sha256(GSON.toJson(declared.get("target")));
        String declaredHash = strictString(declared,
                "targetActionSha256");
        if (!declaredHash.isEmpty() && !targetHash.equals(declaredHash)) {
            return false;
        }
        if (!targetHash.equals(strictString(applied,
                "targetActionSha256"))) return false;
        JsonElement target = declared.get("target");
        if (!target.isJsonObject() || !strictString(declared,
                "inputSymbol").equals(strictString(target.getAsJsonObject(),
                "symbol"))
                || !exactReferenceAssignmentEncoding(declared,
                target.getAsJsonObject())
                || !exactReferenceAssignmentEncoding(applied,
                target.getAsJsonObject())) {
            return false;
        }
        int matches = 0;
        for (JsonElement action : runtimeMaterializationActions(activation)) {
            if (GSON.toJson(target).equals(GSON.toJson(action))) matches++;
        }
        return matches == 1;
    }

    private static boolean exactReferenceAssignmentEncoding(
            JsonObject assignment, JsonObject target) {
        String descriptor = javaTypeDescriptor(firstNonBlank(
                strictString(target, "javaType"),
                strictString(target, "inputJavaType")));
        boolean reference = descriptor.startsWith("L")
                || descriptor.startsWith("[");
        if (!reference) return false;
        String nullableString = strictString(assignment,
                "nullableStringEncodingAuthority");
        String nullableReference = strictString(assignment,
                "referenceNullnessEncodingAuthority");
        return "Ljava/lang/String;".equals(descriptor)
                ? "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1"
                .equals(nullableString) && nullableReference.isEmpty()
                : nullableString.isEmpty()
                && "JAVA_REFERENCE_NULLNESS_AS_EXACT_REF_EQUALITY_V1"
                .equals(nullableReference);
    }

    /** Returns the exact modeled reference symbol, or the empty string. */
    private static String exactReferenceNullConditionSymbol(
            JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) return "";
        JsonObject binary = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(strictString(binary, "_type"))
                || !"==".equals(strictString(binary, "_op"))) {
            return "";
        }
        JsonElement left = binary.get("_left");
        JsonElement right = binary.get("_right");
        JsonElement symbol = exactNullReferenceExpression(left) ? right
                : exactNullReferenceExpression(right) ? left : null;
        if (symbol == null || !symbol.isJsonObject()) return "";
        JsonObject object = symbol.getAsJsonObject();
        String type = strictString(object, "_type");
        String javaType = strictString(object, "_java_type");
        String rawSymbol = strictString(object, "_exp");
        boolean referenceType = javaType.startsWith("L")
                || javaType.startsWith("[")
                || rawSymbol.startsWith("M_L")
                || rawSymbol.startsWith("M_[");
        return ("SymbolExpression".equals(type)
                || "ConSymbolExp".equals(type))
                && referenceType && !rawSymbol.isEmpty()
                ? rawSymbol : "";
    }

    private static boolean exactNullReferenceExpression(JsonElement value) {
        if (value == null || !value.isJsonObject()) return false;
        JsonObject expression = value.getAsJsonObject();
        return "SymbolExpression".equals(strictString(expression, "_type"))
                && "N".equals(strictString(expression, "_exp"));
    }

    private static String certifiedConcreteGuardIdentity(
            JsonObject mapping) {
        return strictString(mapping, "certificateActivationId") + "\n"
                + strictString(mapping, "certificatePathQueryKey") + "\n"
                + strictString(mapping, "certificateProofRole") + "\n"
                + integer(mapping, "certificateSourceConditionIndex", -1)
                + "\n" + integer(mapping, "certificateConstraintIndex", -1)
                + "\n" + integer(mapping,
                "certificateExpectedBranchPrefixOrdinal", -2) + "\n"
                + strictString(mapping, "certificateSiteId") + "\n"
                + integer(mapping, "certificateOccurrence", -1) + "\n"
                + strictBoolean(mapping, "certificateOutcome") + "\n"
                + strictString(mapping, "certificateModelAssignmentKey")
                + "\n" + strictString(mapping,
                "certificateConditionSha256");
    }

    private static PathNormalization normalizePathCondition(
            JsonArray raw, PathAdmissionPolicy admission,
            Set<Integer> mappedConditions,
            Map<Integer, JsonElement> semanticBranchConditions,
            boolean requireMappedBranches, JsonObject activation,
            DynamicSemanticPcFallbackCatalog dynamicPcFallbacks,
            CertifiedConcreteGuardCatalog certifiedConcreteGuards) {
        JsonArray result = new JsonArray();
        int[] rawToNormalized = new int[raw.size()];
        String[] statuses = new String[raw.size()];
        String[] reasons = new String[raw.size()];
        String[] codePositions = new String[raw.size()];
        String[] admissionAuthorities = new String[raw.size()];
        int[] normalizedBoundaries = new int[raw.size() + 1];
        Map<String, Integer> syntheticToNormalized =
                new LinkedHashMap<>();
        Map<String, Integer> syntheticBaselines =
                new LinkedHashMap<>();
        Map<String, Integer> syntheticSizes = new LinkedHashMap<>();
        List<SyntheticConditionNormalization> syntheticRows =
                new ArrayList<>();
        String previous = null;
        int semanticCount = 0;
        int filteredCount = 0;
        int duplicateCount = 0;
        int semanticBranchConditionSubstitutionCount = 0;
        Set<String> mappedBinarySignatures = new LinkedHashSet<>();
        for (Integer mappedIndex : mappedConditions) {
            if (mappedIndex >= 0 && mappedIndex < raw.size()
                    && isBinaryCondition(raw.get(mappedIndex))) {
                mappedBinarySignatures.add(GSON.toJson(raw.get(mappedIndex)));
            }
        }
        for (int index = 0; index <= raw.size(); index++) {
            for (CertifiedConcreteGuard guard
                    : certifiedConcreteGuards.atBoundary(index)) {
                int normalizedBaseline = result.size();
                // Do not collapse certified occurrences.  Two consecutive
                // concrete guards may have the same predicate but remain two
                // distinct branch frontiers with different occurrences.
                result.add(guard.condition.deepCopy());
                int syntheticIndex = result.size() - 1;
                syntheticToNormalized.put(guard.identity, syntheticIndex);
                syntheticBaselines.put(guard.identity,
                        normalizedBaseline);
                syntheticSizes.put(guard.identity, result.size());
                syntheticRows.add(new SyntheticConditionNormalization(
                        guard.identity, index, syntheticIndex,
                        normalizedBaseline, result.size()));
                previous = GSON.toJson(guard.condition);
                semanticCount++;
            }
            // A raw boundary denotes the state immediately before raw[index]
            // and after all certified no-PC guards observed at that boundary.
            normalizedBoundaries[index] = result.size();
            if (index == raw.size()) break;
            JsonElement rawCondition = raw.get(index);
            JsonElement condition = semanticBranchConditions.containsKey(index)
                    ? semanticBranchConditions.get(index)
                    : dynamicPcFallbacks.byRawIndex.containsKey(index)
                    ? dynamicPcFallbacks.byRawIndex.get(index)
                    .semanticCondition : rawCondition;
            if (!GSON.toJson(rawCondition).equals(GSON.toJson(condition))) {
                semanticBranchConditionSubstitutionCount++;
            }
            String codePosition = codePosition(rawCondition);
            codePositions[index] = codePosition;
            String rejection = admission.rejectionReason(codePosition);
            String admissionAuthority = rejection.isEmpty()
                    ? "DECLARED_SEMANTIC_METHOD_BOUNDARY" : "";
            if (!rejection.isEmpty()
                    && requestedHeapMutationAdmission(rawCondition,
                    activation)) {
                rejection = "";
                admissionAuthority =
                        "REQUESTED_HEAP_RECEIVER_EXACT_PORT_BINDING";
            }
            if (rejection.isEmpty() && requireMappedBranches
                    && isBinaryCondition(rawCondition)
                    && !mappedConditions.contains(index)
                    && !dynamicPcFallbacks.byRawIndex.containsKey(index)
                    && !mappedBinarySignatures.contains(
                    GSON.toJson(rawCondition))) {
                rejection = "BINARY_CONDITION_WITHOUT_"
                        + "INSTRUMENTED_BRANCH_MAPPING";
            }
            if (rejection.isEmpty()
                    && dynamicPcFallbacks.byRawIndex.containsKey(index)) {
                admissionAuthority = dynamicPcFallbacks.byRawIndex.get(
                        index).authority;
            }
            if (!rejection.isEmpty()) {
                rawToNormalized[index] = -1;
                statuses[index] = "FILTERED";
                reasons[index] = rejection;
                admissionAuthorities[index] = "";
                filteredCount++;
                continue;
            }
            admissionAuthorities[index] = admissionAuthority;
            semanticCount++;
            String serialized = GSON.toJson(condition);
            boolean exactBranchOwned = mappedConditions.contains(index)
                    || dynamicPcFallbacks.byRawIndex.containsKey(index);
            // Branch-owned predicates are occurrence evidence.  Equal JSON
            // at adjacent loop iterations or after a certified zero-PC guard
            // still denotes a distinct frontier and must keep its own index.
            // Deduplication remains available only for unowned engine
            // bookkeeping expressions.
            if (exactBranchOwned || !serialized.equals(previous)) {
                result.add(condition.deepCopy());
                previous = serialized;
                statuses[index] = "RETAINED";
                reasons[index] = "";
            } else {
                statuses[index] = "DEDUPLICATED";
                reasons[index] = "CONSECUTIVE_SEMANTIC_DUPLICATE";
                duplicateCount++;
            }
            rawToNormalized[index] = result.size() - 1;
        }
        return new PathNormalization(result, rawToNormalized, statuses,
                reasons, codePositions, admissionAuthorities,
                semanticCount, filteredCount, duplicateCount,
                semanticBranchConditionSubstitutionCount,
                normalizedBoundaries, syntheticToNormalized,
                syntheticBaselines, syntheticSizes, syntheticRows);
    }

    /**
     * Replaces a raw JVM compare-trichotomy witness (for example {@code >})
     * with the exact Jimple branch predicate it witnessed (for example
     * {@code >=}).  The runtime keeps both expressions.  Import only accepts
     * the replacement when the declared raw expression is byte-for-byte the
     * engine path element and the two trees differ solely in their operator;
     * malformed or stale mappings therefore cannot rewrite a path condition.
     */
    private static Map<Integer, JsonElement> semanticBranchConditions(
            JsonArray mappings, JsonArray rawConditions) {
        Map<Integer, JsonElement> exact = new LinkedHashMap<>();
        Map<String, JsonElement> byRawSignature = new LinkedHashMap<>();
        Set<String> ambiguousRawSignatures = new LinkedHashSet<>();
        for (JsonElement element : mappings) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            BranchWitness witness = branchWitness(mapping);
            int index = witness != null
                    && BranchWitness.VM_PC.equals(witness.evidenceKind())
                    ? witness.vmPcIndex()
                    : integer(mapping, "rawConditionIndex",
                    integer(mapping, "engineConditionIndex",
                            integer(mapping, "conditionIndex", -1)));
            if (witness != null && index >= 0
                    && index < rawConditions.size()) {
                JsonElement engineRaw = rawConditions.get(index);
                JsonElement semantic = witness.sourceSatisfiedPredicate();
                if (!validWitnessSemanticCondition(witness, engineRaw,
                        semantic)) {
                    continue;
                }
                exact.put(index, semantic.deepCopy());
                String rawSignature = GSON.toJson(engineRaw);
                JsonElement previous = byRawSignature.get(rawSignature);
                if (previous != null && !GSON.toJson(previous).equals(
                        GSON.toJson(semantic))) {
                    ambiguousRawSignatures.add(rawSignature);
                } else if (previous == null) {
                    byRawSignature.put(rawSignature, semantic.deepCopy());
                }
                continue;
            }
            if (index < 0 || index >= rawConditions.size()
                    || !mapping.has("rawCondition")
                    || !mapping.has("condition")) {
                continue;
            }
            JsonElement engineRaw = rawConditions.get(index);
            JsonElement declaredRaw = mapping.get("rawCondition");
            JsonElement semantic = mapping.get("condition");
            if (!GSON.toJson(engineRaw).equals(GSON.toJson(declaredRaw))
                    || !validSemanticBranchCondition(mapping, declaredRaw,
                    semantic)) {
                continue;
            }
            exact.put(index, semantic.deepCopy());
            String rawSignature = GSON.toJson(engineRaw);
            JsonElement previous = byRawSignature.get(rawSignature);
            if (previous != null && !GSON.toJson(previous).equals(
                    GSON.toJson(semantic))) {
                ambiguousRawSignatures.add(rawSignature);
            } else if (previous == null) {
                byRawSignature.put(rawSignature, semantic.deepCopy());
            }
        }
        for (int index = 0; index < rawConditions.size(); index++) {
            if (exact.containsKey(index)) continue;
            String signature = GSON.toJson(rawConditions.get(index));
            if (!ambiguousRawSignatures.contains(signature)
                    && byRawSignature.containsKey(signature)) {
                exact.put(index, byRawSignature.get(signature).deepCopy());
            }
        }
        return exact;
    }

    private static boolean validWitnessSemanticCondition(
            BranchWitness witness, JsonElement raw, JsonElement semantic) {
        if (witness == null
                || !BranchWitness.VM_PC.equals(witness.evidenceKind())) {
            return false;
        }
        JsonObject event = object(witness.evidence(), "vmEvent");
        String normalization = string(event, "predicateNormalization");
        if ("IDENTITY".equals(normalization)) {
            return BranchPredicateAlgebra.equivalent(raw, semantic);
        }
        if (!"JVM_CMP_TRICHOTOMY_TO_JIMPLE_BRANCH_PREDICATE".equals(
                normalization)) {
            return false;
        }
        JsonObject provenance = new JsonObject();
        provenance.addProperty("conditionNormalization", normalization);
        return validSemanticBranchCondition(provenance, raw, semantic);
    }

    private static BranchWitness branchWitness(JsonObject mapping) {
        JsonElement encoded = mapping == null ? null : mapping.get("witness");
        if (encoded == null || !encoded.isJsonObject()) return null;
        try {
            return BranchWitness.fromJson(encoded.getAsJsonObject());
        } catch (IllegalArgumentException malformed) {
            return null;
        }
    }

    private static boolean validSemanticBranchCondition(JsonObject mapping,
                                                        JsonElement raw,
                                                        JsonElement semantic) {
        if (isExactBooleanStringPredicate(raw)
                || isExactBooleanStringPredicate(semantic)) {
            return isExactBooleanStringPredicate(raw)
                    && isExactBooleanStringPredicate(semantic)
                    && string(mapping, "conditionNormalization").isEmpty()
                    && GSON.toJson(raw).equals(GSON.toJson(semantic));
        }
        if (!isBinaryCondition(raw) || !isBinaryCondition(semantic)) {
            return false;
        }
        String rawOperator = string(raw.getAsJsonObject(), "_op");
        String semanticOperator = string(semantic.getAsJsonObject(), "_op");
        if (!supportedBinaryComparator(rawOperator)
                || !supportedBinaryComparator(semanticOperator)) {
            return false;
        }
        String normalization = string(mapping, "conditionNormalization");
        boolean sameOperator = rawOperator.equals(semanticOperator);
        if (sameOperator && !normalization.isEmpty()) {
            return false;
        }
        if (!sameOperator
                && (!"JVM_CMP_TRICHOTOMY_TO_JIMPLE_BRANCH_PREDICATE".equals(
                normalization)
                || !(">=".equals(semanticOperator)
                && (">".equals(rawOperator)
                || "==".equals(rawOperator))
                || "<=".equals(semanticOperator)
                && ("<".equals(rawOperator)
                || "==".equals(rawOperator))))) {
            return false;
        }
        JsonObject rawShape = raw.getAsJsonObject().deepCopy();
        JsonObject semanticShape = semantic.getAsJsonObject().deepCopy();
        rawShape.remove("_op");
        semanticShape.remove("_op");
        return GSON.toJson(rawShape).equals(GSON.toJson(semanticShape));
    }

    /**
     * Recognizes only Boolean-valued String IR nodes for which both concolic
     * SMT encoders provide exact semantics.  A VM branch event may use one of
     * these predicates directly while the corresponding Jimple branch tests
     * the returned Java boolean against zero.  Requiring byte-for-byte equal
     * raw and semantic nodes prevents this admission path from being used to
     * rewrite an operation, its operands, or its polarity.
     */
    private static boolean isExactBooleanStringPredicate(JsonElement value) {
        if (value == null || !value.isJsonObject()) return false;
        JsonObject expression = value.getAsJsonObject();
        if (!"OpStrExpression".equals(string(expression, "_type"))) {
            return false;
        }
        String operation = string(expression, "_name");
        int arity;
        if ("isEmpty".equals(operation)) {
            arity = 1;
        } else if ("contains".equals(operation)
                || "equals".equals(operation)
                || "startsWith".equals(operation)
                || "endsWith".equals(operation)) {
            arity = 2;
        } else {
            return false;
        }
        JsonArray parameters = array(expression, "_param_list");
        if (parameters.size() != arity) return false;
        for (JsonElement parameter : parameters) {
            if (!isStringExpression(parameter)) return false;
        }
        JsonElement polarity = expression.get("_is_not");
        return polarity == null || polarity.isJsonNull()
                || polarity.isJsonPrimitive()
                && polarity.getAsJsonPrimitive().isBoolean();
    }

    private static boolean isStringExpression(JsonElement value) {
        if (value == null || !value.isJsonObject()) return false;
        JsonObject expression = value.getAsJsonObject();
        String type = string(expression, "_type");
        String javaType = string(expression, "_java_type");
        if ("SymbolExpression".equals(type)
                || "ConSymbolExp".equals(type)
                || "ConStringSymbolExp".equals(type)) {
            return "java/lang/String".equals(javaType)
                    || "Ljava/lang/String;".equals(javaType)
                    || "String".equals(javaType);
        }
        if (!"OpStrExpression".equals(type)) return false;
        String operation = string(expression, "_name");
        JsonArray parameters = array(expression, "_param_list");
        if ("concat".equals(operation) && parameters.size() == 2) {
            return isStringExpression(parameters.get(0))
                    && isStringExpression(parameters.get(1));
        }
        return false;
    }

    private static boolean supportedBinaryComparator(String operator) {
        return "==".equals(operator) || "!=".equals(operator)
                || "<".equals(operator) || "<=".equals(operator)
                || ">".equals(operator) || ">=".equals(operator);
    }

    /**
     * Certifies the narrow case where the runtime observed a field-dependent
     * branch but its occurrence mapping was intentionally left unresolved
     * because the VM emitted more than one new binary condition.  The raw
     * condition is admitted only when the activation-local entry/value/field
     * identity join is complete and a mapped sibling occurrence at the same
     * branch site supplies one unambiguous JVM-to-Jimple operator template.
     */
    private static DynamicSemanticPcFallbackCatalog dynamicSemanticPcFallbacks(
            JsonObject raw, JsonObject activation, JsonArray pathCondition,
            JsonArray branchMappings, PathAdmissionPolicy admission) {
        Map<String, DynamicSemanticPcFallback> byDynamic =
                new LinkedHashMap<>();
        Map<Integer, DynamicSemanticPcFallback> byRaw =
                new LinkedHashMap<>();
        Set<String> ambiguousDynamics = new LinkedHashSet<>();
        Set<Integer> ambiguousRawIndices = new LinkedHashSet<>();
        JsonArray bindings = array(raw, "dynamicFieldBindings");
        JsonArray heapReads = array(raw, "runtimeHeapObservations");
        JsonArray fieldObservations = array(raw, "fieldObservations");
        String activationId = string(activation, "activationId");

        for (JsonElement bindingElement : bindings) {
            if (!bindingElement.isJsonObject()) continue;
            JsonObject binding = bindingElement.getAsJsonObject();
            if (integer(binding, "schemaVersion", -1) != 1
                    || !"DYNAMIC_MAP_ENTRY_FIELD_BINDING".equals(string(
                    binding, "kind"))
                    || !bool(binding, "complete", false)) {
                continue;
            }
            String dynamic = string(binding, "dynamicFieldSymbol");
            String bindingId = string(binding, "dynamicBindingId");
            String base = string(binding, "baseInputSymbol");
            String site = string(binding, "materializationSiteId");
            int occurrence = integer(binding,
                    "materializationOccurrence", -1);
            String entryReadId = string(binding,
                    "entryReadObservationId");
            String fieldSignature = string(binding, "fieldSignature");
            long leafToken = longInteger(binding,
                    "leafOwnerObjectToken", 0L);
            long entryValueOwnerToken = longInteger(binding,
                    "entryValueOwnerObjectToken", 0L);
            String expectedDynamic = base.isEmpty() || site.isEmpty()
                    || occurrence < 1 ? "" : base + ".field."
                    + sha256(site).substring(0, 12) + ".occ." + occurrence;
            if (dynamic.isEmpty() || !dynamic.equals(expectedDynamic)
                    || !bindingId.equals("DYNAMIC_FIELD:" + dynamic)
                    || entryReadId.isEmpty() || leafToken <= 0L
                    || entryValueOwnerToken <= 0L
                    || !activationId.equals(string(binding,
                    "objectTokenScope"))
                    || !"ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN"
                    .equals(string(binding, "objectTokenAuthority"))
                    || array(binding, "fieldPath").size() == 0) {
                continue;
            }

            List<JsonObject> reads = objectsWithField(heapReads,
                    "observationId", entryReadId);
            List<JsonObject> fields =
                    fieldObservationsForDynamicBinding(fieldObservations,
                            bindingId, dynamic);
            if (reads.size() != 1 || fields.size() != 1) continue;
            JsonObject read = reads.get(0);
            JsonObject field = fields.get(0);
            int pcBoundary = integer(read, "pcBoundary", -1);
            String originMethod = string(read, "originMethod");
            String leafOwnerClass = string(field, "leafOwnerClass");
            boolean identityJoin = pcBoundary >= 0
                    && entryValueOwnerToken == longInteger(read,
                    "valueObjectToken", -1L)
                    && activationId.equals(string(read,
                    "objectTokenScope"))
                    && bool(field, "available", false)
                    && bool(field, "complete", false)
                    && bool(field, "accessOwnerObjectTokenKnown", false)
                    && entryValueOwnerToken == longInteger(field,
                    "accessOwnerObjectToken", -1L)
                    && bool(field, "leafOwnerObjectTokenKnown", false)
                    && leafToken == longInteger(field,
                    "leafOwnerObjectToken", -1L)
                    && activationId.equals(string(field,
                    "objectTokenScope"))
                    && site.equals(string(field,
                    "materializationSiteId"))
                    && occurrence == integer(field,
                    "materializationOccurrence", -2)
                    && fieldSignature.equals(string(field,
                    "fieldSignature"))
                    && array(binding, "fieldPath").equals(array(field,
                    "fieldPath"))
                    && !leafOwnerClass.isEmpty();
            if (!identityJoin) continue;

            List<JsonObject> targets = new ArrayList<>();
            for (JsonElement mappingElement : branchMappings) {
                if (!mappingElement.isJsonObject()) continue;
                JsonObject mapping = mappingElement.getAsJsonObject();
                int rawIndex = integer(mapping, "rawConditionIndex",
                        integer(mapping, "engineConditionIndex",
                                integer(mapping, "conditionIndex", -1)));
                if (rawIndex < 0
                        && occurrence == integer(mapping,
                        "occurrence", -1)
                        && originMethod.equals(string(mapping, "method"))
                        && !string(mapping, "siteId").isEmpty()) {
                    targets.add(mapping);
                }
            }
            if (targets.size() != 1) continue;
            JsonObject target = targets.get(0);
            int baseline = integer(target, "rawPathConditionBaseline",
                    integer(target, "enginePathConditionBaseline", -1));
            int boundary = integer(target, "rawPathConditionSize",
                    integer(target, "enginePathConditionSize", -1));
            if (baseline < 0 || boundary <= baseline
                    || boundary > pathCondition.size()
                    || pcBoundary < baseline || pcBoundary >= boundary) {
                continue;
            }
            int nextEntryBoundary = nextEntryReadBoundary(heapReads,
                    originMethod, pcBoundary);
            int upper = nextEntryBoundary > pcBoundary
                    ? Math.min(boundary, nextEntryBoundary) : boundary;
            String descriptor = javaTypeDescriptor(fieldJavaType(
                    fieldSignature));
            if (descriptor.isEmpty() || descriptor.startsWith("[")) {
                continue;
            }
            String expectedRawSymbol = "M_" + descriptor + "_field_"
                    + dynamic + "_" + leafOwnerClass.replace('.', '/');
            List<DynamicRawPcCandidate> candidates = new ArrayList<>();
            for (int index = Math.max(pcBoundary, baseline);
                    index < upper; index++) {
                JsonElement condition = pathCondition.get(index);
                String codePosition = codePosition(condition);
                if (!isBinaryCondition(condition)
                        || !admission.rejectionReason(codePosition).isEmpty()) {
                    continue;
                }
                List<JsonObject> expressions =
                        exactRawSymbolExpressions(condition,
                                expectedRawSymbol);
                if (expressions.size() == 1) {
                    candidates.add(new DynamicRawPcCandidate(index,
                            condition.getAsJsonObject(), expressions.get(0),
                            codePosition));
                }
            }
            if (candidates.size() != 1) continue;
            DynamicRawPcCandidate candidate = candidates.get(0);

            Set<String> semanticOperators = new LinkedHashSet<>();
            String branchSiteId = string(target, "siteId");
            for (JsonElement mappingElement : branchMappings) {
                if (!mappingElement.isJsonObject()) continue;
                JsonObject sibling = mappingElement.getAsJsonObject();
                if (!branchSiteId.equals(string(sibling, "siteId"))
                        || integer(sibling, "rawConditionIndex", -1) < 0
                        || bool(sibling, "outcome", false)
                        != bool(target, "outcome", false)
                        || !candidate.codePosition.equals(firstNonBlank(
                        string(sibling, "conditionCodePosition"),
                        codePosition(sibling.get("rawCondition"))))
                        || !"JVM_CMP_TRICHOTOMY_TO_JIMPLE_BRANCH_PREDICATE"
                        .equals(string(sibling,
                        "conditionNormalization"))
                        || !sibling.has("rawCondition")
                        || !sibling.has("condition")
                        || !validSemanticBranchCondition(sibling,
                        sibling.get("rawCondition"),
                        sibling.get("condition"))
                        || !string(candidate.rawCondition, "_op").equals(
                        string(sibling.getAsJsonObject("rawCondition"),
                                "_op"))) {
                    continue;
                }
                String semanticOperator = string(
                        sibling.getAsJsonObject("condition"), "_op");
                if (supportedBinaryComparator(semanticOperator)) {
                    semanticOperators.add(semanticOperator);
                }
            }
            if (semanticOperators.size() != 1) continue;
            JsonObject semantic = candidate.rawCondition.deepCopy();
            semantic.addProperty("_op",
                    semanticOperators.iterator().next());
            DynamicSemanticPcFallback fallback =
                    new DynamicSemanticPcFallback(dynamic, base,
                            entryReadId, branchSiteId, candidate.rawIndex,
                            candidate.rawCondition,
                            candidate.fieldExpression, semantic,
                            candidate.codePosition,
                            "CERTIFIED_DYNAMIC_MAP_ENTRY_FIELD_RAW_PC_"
                                    + "SIBLING_BRANCH_TEMPLATE_V1");
            DynamicSemanticPcFallback sameDynamic = byDynamic.get(dynamic);
            DynamicSemanticPcFallback sameRaw = byRaw.get(
                    candidate.rawIndex);
            if (sameDynamic != null || sameRaw != null
                    || ambiguousDynamics.contains(dynamic)
                    || ambiguousRawIndices.contains(candidate.rawIndex)) {
                List<DynamicSemanticPcFallback> conflicts =
                        new ArrayList<>();
                conflicts.add(fallback);
                if (sameDynamic != null) conflicts.add(sameDynamic);
                if (sameRaw != null && sameRaw != sameDynamic) {
                    conflicts.add(sameRaw);
                }
                for (DynamicSemanticPcFallback conflict : conflicts) {
                    ambiguousDynamics.add(conflict.dynamicFieldSymbol);
                    ambiguousRawIndices.add(conflict.rawIndex);
                    byDynamic.remove(conflict.dynamicFieldSymbol);
                    byRaw.remove(conflict.rawIndex);
                }
                ambiguousDynamics.add(dynamic);
                ambiguousRawIndices.add(candidate.rawIndex);
                continue;
            }
            byDynamic.put(dynamic, fallback);
            byRaw.put(candidate.rawIndex, fallback);
        }
        return new DynamicSemanticPcFallbackCatalog(byDynamic, byRaw);
    }

    private static List<JsonObject> objectsWithField(
            JsonArray values, String field, String expected) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : values) {
            if (element.isJsonObject() && expected.equals(string(
                    element.getAsJsonObject(), field))) {
                result.add(element.getAsJsonObject());
            }
        }
        return result;
    }

    private static int nextEntryReadBoundary(JsonArray observations,
                                             String method, int boundary) {
        int next = Integer.MAX_VALUE;
        for (JsonElement element : observations) {
            if (!element.isJsonObject()) continue;
            JsonObject observation = element.getAsJsonObject();
            int candidate = integer(observation, "pcBoundary", -1);
            if (method.equals(string(observation, "originMethod"))
                    && candidate > boundary && candidate < next) {
                next = candidate;
            }
        }
        return next == Integer.MAX_VALUE ? -1 : next;
    }

    private static List<JsonObject> exactRawSymbolExpressions(
            JsonElement expression, String exactRawSymbol) {
        List<JsonObject> result = new ArrayList<>();
        collectExactRawSymbolExpressions(expression, exactRawSymbol,
                result);
        return result;
    }

    private static void collectExactRawSymbolExpressions(
            JsonElement expression, String exactRawSymbol,
            List<JsonObject> result) {
        if (expression == null || expression.isJsonNull()) return;
        if (expression.isJsonArray()) {
            for (JsonElement element : expression.getAsJsonArray()) {
                collectExactRawSymbolExpressions(element, exactRawSymbol,
                        result);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject object = expression.getAsJsonObject();
        if (("SymbolExpression".equals(string(object, "_type"))
                || "ConSymbolExp".equals(string(object, "_type")))
                && exactRawSymbol.equals(string(object, "_exp"))) {
            result.add(object.deepCopy());
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            if (!"_exp".equals(entry.getKey())
                    && !"_code_position".equals(entry.getKey())) {
                collectExactRawSymbolExpressions(entry.getValue(),
                        exactRawSymbol, result);
            }
        }
    }

    private static boolean requestedHeapMutationAdmission(
            JsonElement condition, JsonObject activation) {
        if (condition == null || !condition.isJsonObject()
                || !RegionCaptureGoal.from(activation).isOutputClosure()
                || !requestedOutputSliceContractOperationallyAdmitted(
                activation)) {
            return false;
        }
        JsonObject expression = condition.getAsJsonObject();
        if (!"MethodExpression".equals(string(expression, "_type"))) {
            return false;
        }
        MapMethod method = MapMethod.parse(string(expression, "_name"));
        if (method == null || !method.mapOwner
                || (MapMutationKind.fromMethod(method.method) == null
                && !isPotentialMapMutation(method.method))
                || !isContainerImplementationCodePosition(method,
                string(expression, "_code_position"))) {
            return false;
        }
        JsonArray parameters = array(expression, "_param_list");
        if (parameters.size() == 0 || parameters.get(0).isJsonNull()) {
            return false;
        }
        return new HeapPortResolver(activation).requestedOutputBinding(
                parameters.get(0)).resolved;
    }

    private static boolean isContainerImplementationCodePosition(
            MapMethod method, String codePosition) {
        if (!method.owner.startsWith("java/util/")) {
            return false;
        }
        String methodKey = ConcolicCodePosition.vmMethodKey(codePosition);
        int separator = methodKey.lastIndexOf('#');
        if (separator <= 0) {
            return false;
        }
        String codeOwner = methodKey.substring(0, separator);
        String mapOwner = method.owner.replace('/', '.');
        return codeOwner.equals(mapOwner)
                || codeOwner.startsWith(mapOwner + "$");
    }

    private static Set<Integer> mappedConditionIndices(JsonArray mappings) {
        Set<Integer> result = new LinkedHashSet<>();
        for (JsonElement element : mappings) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject mapping = element.getAsJsonObject();
            BranchWitness witness = branchWitness(mapping);
            int index = witness != null
                    && BranchWitness.VM_PC.equals(witness.evidenceKind())
                    ? witness.vmPcIndex()
                    : integer(mapping, "rawConditionIndex",
                    integer(mapping, "engineConditionIndex",
                            integer(mapping, "conditionIndex", -1)));
            if (index >= 0) {
                result.add(index);
            }
        }
        return result;
    }

    private static List<String> branchWitnessIssues(JsonArray mappings) {
        List<String> issues = new ArrayList<>();
        Set<String> identities = new LinkedHashSet<>();
        int ordinal = 0;
        for (JsonElement element : mappings) {
            if (!element.isJsonObject()) {
                ordinal++;
                continue;
            }
            JsonObject mapping = element.getAsJsonObject();
            JsonElement encoded = mapping.get("witness");
            if (encoded == null) {
                ordinal++;
                continue;
            }
            if (!encoded.isJsonObject()) {
                issues.add("mapping@" + ordinal
                        + ":WITNESS_MUST_BE_AN_OBJECT");
                ordinal++;
                continue;
            }
            try {
                BranchWitness witness = BranchWitness.fromJson(
                        encoded.getAsJsonObject());
                if (!identities.add(witness.witnessId())) {
                    issues.add(witness.witnessId()
                            + ":DUPLICATE_WITNESS_ID");
                }
            } catch (IllegalArgumentException malformed) {
                issues.add("mapping@" + ordinal + ":"
                        + malformed.getMessage());
            }
            ordinal++;
        }
        return issues;
    }

    private static boolean isBinaryCondition(JsonElement condition) {
        return condition != null && condition.isJsonObject()
                && "BinaryExpression".equals(string(
                condition.getAsJsonObject(), "_type"));
    }

    private static JsonArray normalizeBranchMappings(
            JsonArray rawMappings, PathNormalization normalization) {
        JsonArray result = new JsonArray();
        for (JsonElement element : rawMappings) {
            if (!element.isJsonObject()) {
                result.add(element.deepCopy());
                continue;
            }
            JsonObject mapping = element.getAsJsonObject().deepCopy();
            BranchWitness witness = branchWitness(mapping);
            int rawIndex = witness != null
                    && BranchWitness.VM_PC.equals(witness.evidenceKind())
                    ? witness.vmPcIndex()
                    : integer(mapping, "rawConditionIndex",
                    integer(mapping, "engineConditionIndex",
                            integer(mapping, "conditionIndex", -1)));
            String syntheticIdentity = certifiedConcreteGuardIdentity(
                    mapping);
            boolean certifiedSynthetic = normalization.hasSynthetic(
                    syntheticIdentity);
            int normalizedIndex = certifiedSynthetic
                    ? normalization.syntheticIndex(syntheticIdentity)
                    : normalization.index(rawIndex);
            if (witness != null) {
                // The witness remains byte-for-byte immutable.  This is the
                // sole bridge from the VM-PC namespace owned by its evidence
                // to the normalized summary-PC namespace owned here.
                mapping.addProperty("summaryPcIndex", normalizedIndex);
            }
            if (mapping.has("conditionIndex")
                    || mapping.has("rawConditionIndex")
                    || mapping.has("engineConditionIndex")) {
                mapping.addProperty("rawConditionIndex", rawIndex);
                mapping.addProperty("engineConditionIndex", rawIndex);
                mapping.addProperty("normalizedConditionIndex",
                        normalizedIndex);
                mapping.addProperty("conditionIndex", normalizedIndex);
            }
            if (certifiedSynthetic) {
                mapping.addProperty("syntheticCondition", true);
                mapping.addProperty("syntheticConditionKey",
                        syntheticIdentity);
                mapping.addProperty("syntheticConditionAuthority",
                        CERTIFIED_CONCRETE_GUARD_AUTHORITY);
            }
            if (mapping.has("condition")) {
                if (!certifiedSynthetic && !mapping.has("rawCondition")) {
                    mapping.add("rawCondition",
                            mapping.get("condition").deepCopy());
                }
                if (normalizedIndex >= 0
                        && normalizedIndex < normalization.conditions.size()) {
                    mapping.add("condition", normalization.conditions
                            .get(normalizedIndex).deepCopy());
                } else {
                    mapping.remove("condition");
                }
            }
            int rawSize = integer(mapping, "rawPathConditionSize",
                    integer(mapping, "enginePathConditionSize",
                            integer(mapping, "pathConditionSize", -1)));
            int normalizedSize = certifiedSynthetic
                    ? normalization.syntheticSize(syntheticIdentity)
                    : rawIndex >= 0 && normalizedIndex >= 0
                    && rawSize == rawIndex + 1
                    // raw[index] is appended before any later zero-PC
                    // guards at boundary index+1.  The final boundary table
                    // includes those later guards, so it is not this
                    // mapping's temporal size.
                    ? normalizedIndex + 1
                    : normalization.boundary(rawSize);
            if (rawSize >= 0) {
                mapping.addProperty("rawPathConditionSize", rawSize);
                mapping.addProperty("enginePathConditionSize", rawSize);
                mapping.addProperty("normalizedPathConditionSize",
                        normalizedSize);
                mapping.addProperty("pathConditionSize",
                        normalizedSize);
            }
            int rawBaseline = integer(mapping, "rawPathConditionBaseline",
                    integer(mapping, "enginePathConditionBaseline",
                            integer(mapping, "pathConditionBaseline", -1)));
            if (rawBaseline >= 0) {
                int normalizedBaseline = certifiedSynthetic
                        ? normalization.syntheticBaseline(syntheticIdentity)
                        : normalization.boundary(rawBaseline);
                mapping.addProperty("rawPathConditionBaseline", rawBaseline);
                mapping.addProperty("enginePathConditionBaseline",
                        rawBaseline);
                mapping.addProperty("normalizedPathConditionBaseline",
                        normalizedBaseline);
                mapping.addProperty("pathConditionBaseline",
                        normalizedBaseline);
                mapping.addProperty("rawPathConditionsAdded",
                        Math.max(0, rawSize - rawBaseline));
                mapping.addProperty("pathConditionsAdded", Math.max(0,
                        normalizedSize - normalizedBaseline));
            }
            if (rawIndex >= 0 && normalizedIndex < 0) {
                mapping.addProperty("mappingWarning",
                        "raw condition was excluded by semantic path filtering");
            }
            result.add(mapping);
        }
        return result;
    }

    private static HeapEffectExtraction extractHeapEffects(
            JsonObject raw, JsonArray rawPathCondition,
            PathNormalization normalization,
            JsonElement runtimeHeapEffects,
            JsonElement runtimeHeapObservations,
            JsonElement fieldObservations,
            JsonElement dynamicFieldBindings, JsonArray rawBranchMappings,
            JsonObject activation, String regionId,
            DynamicSemanticPcFallbackCatalog dynamicPcFallbacks,
            JsonArray engineArrayInputBindings) {
        List<HeapMutation> mutations = new ArrayList<>();
        List<HeapEffectIssue> issues = new ArrayList<>();
        Map<String, Integer> occurrences = new LinkedHashMap<>();
        int candidateCount = 0;
        int unsupportedCount = 0;
        int malformedCount = 0;

        for (int rawIndex = 0; rawIndex < rawPathCondition.size(); rawIndex++) {
            if (!normalization.isSemantic(rawIndex)) {
                continue;
            }
            JsonElement element = rawPathCondition.get(rawIndex);
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject expression = element.getAsJsonObject();
            if (!"MethodExpression".equals(string(expression, "_type"))) {
                continue;
            }
            MapMethod method = MapMethod.parse(string(expression, "_name"));
            if (method == null || !method.mapOwner) {
                continue;
            }
            MapMutationKind kind = MapMutationKind.fromMethod(method.method);
            if (kind == null) {
                if (isPotentialMapMutation(method.method)) {
                    candidateCount++;
                    unsupportedCount++;
                    issues.add(new HeapEffectIssue(
                            "UNSUPPORTED_MAP_MUTATION_OPERATION", rawIndex,
                            string(expression, "_code_position"),
                            method.qualifiedName));
                }
                continue;
            }

            candidateCount++;
            JsonArray parameters = array(expression, "_param_list");
            String parameterNormalization = "";
            if (kind == MapMutationKind.MAP_REMOVE
                    && parameters.size() == 5) {
                // HashMap.removeNode(hash, key, value, matchValue, movable)
                // is exported by the VM after null expressions are removed.
                // Iterator.remove supplies value=null, yielding
                // [map, hash, key, matchValue, movable].  Only the
                // matchValue=false form has unconditional Map.remove(key)
                // semantics represented by MAP_REMOVE.
                if (!"java/util/HashMap".equals(method.owner)
                        || !isConcreteFalseBoolean(parameters.get(3))) {
                    unsupportedCount++;
                    issues.add(new HeapEffectIssue(
                            "UNSUPPORTED_MAP_MUTATION_OPERATION", rawIndex,
                            string(expression, "_code_position"),
                            method.qualifiedName
                                    + "/conditional-internal-removeNode"));
                    continue;
                }
                JsonArray normalized = new JsonArray();
                normalized.add(parameters.get(0).deepCopy());
                normalized.add(parameters.get(2).deepCopy());
                parameters = normalized;
                parameterNormalization =
                        "JDK_HASHMAP_REMOVENODE_MATCH_VALUE_FALSE";
            }
            // Java 8 Map.remove(key, value) is conditional and cannot be
            // represented as an unconditional MAP_REMOVE transformer.
            if (kind == MapMutationKind.MAP_REMOVE
                    && parameters.size() == 3) {
                unsupportedCount++;
                issues.add(new HeapEffectIssue(
                        "UNSUPPORTED_MAP_MUTATION_OPERATION", rawIndex,
                        string(expression, "_code_position"),
                        method.qualifiedName + "/conditional"));
                continue;
            }
            if (parameters.size() != kind.parameterCount
                    || parameters.size() == 0
                    || parameters.get(0).isJsonNull()
                    || kind == MapMutationKind.MAP_PUT_ALL
                    && parameters.get(1).isJsonNull()) {
                malformedCount++;
                issues.add(new HeapEffectIssue(
                        "MALFORMED_MAP_MUTATION_EXPRESSION", rawIndex,
                        string(expression, "_code_position"),
                        method.qualifiedName + "/arity=" + parameters.size()));
                continue;
            }

            String codePosition = string(expression, "_code_position");
            String siteId = codePosition + "::" + method.qualifiedName;
            int occurrence = occurrences.containsKey(siteId)
                    ? occurrences.get(siteId) + 1 : 1;
            occurrences.put(siteId, occurrence);
            mutations.add(new HeapMutation(kind, method, rawIndex,
                    normalization.index(rawIndex),
                    normalization.status(rawIndex), codePosition, siteId,
                    occurrence, parameters, expression.get("_res_exp"),
                    parameterNormalization,
                    normalization.admissionAuthority(rawIndex)));
        }

        RuntimeHeapEvidenceSelection runtimeHeapEvidence =
                selectRuntimeHeapEvidence(runtimeHeapEffects,
                        runtimeHeapObservations, activation,
                        rawBranchMappings);
        RuntimeHeapObservationCatalog observationCatalog =
                validateRuntimeHeapObservations(rawPathCondition,
                        runtimeHeapEvidence.observations,
                        activation, raw);
        issues.addAll(observationCatalog.issues);
        HeapPortResolver ports = new HeapPortResolver(activation);
        DynamicFieldBindingCatalog dynamicBindingCatalog =
                validateDynamicFieldBindings(dynamicFieldBindings,
                        observationCatalog, activation, fieldObservations,
                        rawBranchMappings, raw.get(
                        "mapValueElementProjectionObservations"),
                        raw.get("symbolizedInputs"), mutations, ports);
        issues.addAll(dynamicBindingCatalog.issues);
        RuntimeHeapEffectJoin runtimeJoin = joinRuntimeHeapEffects(
                rawPathCondition, mutations, runtimeHeapEvidence.effects,
                observationCatalog);
        issues.addAll(runtimeJoin.issues);
        for (HeapMutation mutation : mutations) {
            mutation.runtimeProvenance = runtimeJoin.bindings.get(
                    mutation.rawIndex);
        }

        Map<String, Integer> totals = new LinkedHashMap<>();
        for (HeapMutation mutation : mutations) {
            Integer count = totals.get(mutation.mapIdentity);
            totals.put(mutation.mapIdentity, count == null ? 1 : count + 1);
        }

        Map<String, MapStateTracker> trackers = new LinkedHashMap<>();
        JsonArray initializers = new JsonArray();
        JsonArray runtimeMapInputSnapshots = new JsonArray();
        JsonArray effects = new JsonArray();
        Map<String, HeapOutputBinding> outputBindings = new LinkedHashMap<>();
        int syntheticInputCount = 0;
        int initializedInputCount = 0;
        int unboundFinalOutputCount = 0;
        int intermediateStateCount = 0;
        int effectOrdinal = 0;

        for (HeapMutation mutation : mutations) {
            MapStateTracker tracker = trackers.get(mutation.mapIdentity);
            if (tracker == null) {
                int mapOrdinal = trackers.size();
                String inputPort = ports.inputPort(mutation.mapExpression);
                RuntimeMapStateInputResolution runtimeMapInput =
                        inputPort.isEmpty()
                                ? runtimeMapStateInputResolution(mutation,
                                observationCatalog, ports, activation, raw)
                                : RuntimeMapStateInputResolution.none();
                if (runtimeMapInput.resolved()) {
                    inputPort = runtimeMapInput.inputPort();
                }
                FreshMapInitializerResolution initializer = inputPort.isEmpty()
                        ? ports.freshMapInitializer(mutation)
                        : FreshMapInitializerResolution.none();
                boolean freshInitialized = initializer.resolved();
                boolean syntheticInput = inputPort.isEmpty()
                        && !freshInitialized;
                if (freshInitialized) {
                    inputPort = regionId + ".state.heapMap" + mapOrdinal
                            + ".empty";
                    initializedInputCount++;
                }
                if (syntheticInput) {
                    inputPort = regionId + ".in.heapMap" + mapOrdinal
                            + ".state0";
                    syntheticInputCount++;
                    issues.add(new HeapEffectIssue(
                            "UNBOUND_MAP_PRE_STATE_PORT", mutation.rawIndex,
                            mutation.codePosition, mutation.method.qualifiedName));
                }
                if (initializer.ambiguous()) {
                    issues.add(new HeapEffectIssue(
                            "AMBIGUOUS_MAP_ALLOCATION_INITIALIZER",
                            mutation.rawIndex, mutation.codePosition,
                            mutation.method.qualifiedName));
                }
                String outputPort = freshInitialized
                        ? initializer.outputPort()
                        : ports.outputPort(inputPort);
                if (outputPort.isEmpty()) {
                    unboundFinalOutputCount++;
                    issues.add(new HeapEffectIssue(
                            "UNBOUND_MAP_POST_STATE_PORT", mutation.rawIndex,
                            mutation.codePosition, mutation.method.qualifiedName));
                }
                tracker = new MapStateTracker(regionId, mapOrdinal,
                        totals.get(mutation.mapIdentity), inputPort, outputPort,
                        syntheticInput, freshInitialized, runtimeMapInput);
                trackers.put(mutation.mapIdentity, tracker);
                if (runtimeMapInput.resolved()) {
                    runtimeMapInputSnapshots.add(
                            runtimeMapInput.toFiniteSnapshot(inputPort));
                }
                if (freshInitialized) {
                    initializers.add(initializer.toSummary(
                            "HEAP_INITIALIZER." + regionId + "."
                                    + mapOrdinal,
                            inputPort, tracker.stateFamily,
                            tracker.stateFamily + ".0"));
                }
            }

            int before = tracker.seen;
            int after = before + 1;
            boolean last = after == tracker.totalEffects;
            String outputPort;
            String outputBinding;
            if (last && !tracker.finalOutputPort.isEmpty()) {
                outputPort = tracker.finalOutputPort;
                outputBinding = tracker.freshInitialized
                        ? "STATIC_FRESH_ALLOCATION_TO_REQUESTED_OUTPUT"
                        : "ACTIVATION_HEAP_OUTPUT";
            } else {
                outputPort = regionId + ".out.heapMap" + tracker.mapOrdinal
                        + ".state" + after;
                outputBinding = last ? "SYNTHETIC_FINAL_STATE"
                        : "SYNTHETIC_INTERMEDIATE_STATE";
                if (!last) {
                    intermediateStateCount++;
                }
            }
            String preState = tracker.stateFamily + "." + before;
            String postState = tracker.stateFamily + "." + after;
            String effectId = "HEAP_EFFECT." + regionId + "."
                    + effectOrdinal++;

            JsonObject effect = mutation.toEffect(effectId,
                    tracker.currentPort, outputPort, tracker.stateFamily,
                    preState, postState, before, after,
                    before == 0 ? (tracker.freshInitialized
                            ? "STATIC_FRESH_EMPTY_MAP"
                            : tracker.syntheticInput
                            ? "SYNTHETIC_PRE_STATE"
                            : "ACTIVATION_SYMBOL") : "PREVIOUS_EFFECT",
                    outputBinding);
            tracker.runtimeMapInput.attach(effect);
            effects.add(effect);
            tracker.currentPort = outputPort;
            tracker.seen = after;
            if (last && !tracker.finalOutputPort.isEmpty()) {
                outputBindings.put(outputPort, new HeapOutputBinding(
                        postState, tracker.stateFamily, effectId,
                        outputPort));
            }
        }

        HeapObservationExtraction heapObservations =
                materializeHeapObservations(observationCatalog, effects,
                        ports, activation, rawBranchMappings,
                        fieldObservations, dynamicBindingCatalog,
                        rawPathCondition, normalization,
                        dynamicPcFallbacks, regionId,
                        candidateCount == 0 && mutations.isEmpty()
                                && effects.size() == 0
                                && unsupportedCount == 0
                                && malformedCount == 0
                                && runtimeHeapEvidence.ignoredEvidence.size()
                                == 0
                                && !runtimeJoin.legacy
                                && runtimeJoin.recordCount == 0
                                && runtimeJoin.joinedCount == 0
                                && runtimeJoin.bindings.isEmpty()
                                && runtimeJoin.issues.isEmpty()
                                && !supportedMapStateField(string(object(
                                activation, "requestedOutput"), "cell")));
        issues.addAll(heapObservations.issues);
        issues.addAll(associateHeapObservationsWithEffects(effects,
                heapObservations));
        JsonArray finiteMapSnapshots = runtimeMapInputSnapshots.deepCopy();
        JsonArray entryReadSnapshots = exactRuntimeFiniteMapSnapshots(
                fieldObservations, heapObservations.observations, effects,
                activation);
        for (JsonElement snapshot : entryReadSnapshots) {
            finiteMapSnapshots.add(snapshot.deepCopy());
        }

        OutputExpressionExtraction fieldAssignmentCapture =
                hasOutputCaptureKind(activation, "FIELD_ASSIGNMENT_RHS")
                        ? exactOutputCaptureExpressions(raw, activation,
                        firstNonBlank(string(object(activation,
                                "requestedOutput"), "portId"),
                                string(object(activation,
                                        "requestedOutput"), "symbol")),
                        normalization)
                        : null;
        StaticHeapTransformerCoverage staticCoverage =
                staticHeapTransformerCoverage(activation, effects,
                        runtimeJoin.legacy, observationCatalog.legacy,
                        rawBranchMappings,
                        fieldObservations, fieldAssignmentCapture,
                        rawPathCondition, normalization,
                        dynamicBindingCatalog.normalizedBindings(),
                        engineArrayInputBindings);
        issues.addAll(staticCoverage.issues);
        String captureDischargeIssue =
                heapEffectCaptureDischargeIssue(activation);
        if (!captureDischargeIssue.isEmpty()) {
            issues.add(new HeapEffectIssue(
                    "INVALID_HEAP_EFFECT_CAPTURE_DISCHARGE", -1,
                    "requestedOutputSlice", captureDischargeIssue));
        }

        int identityEffectCount = addGuardedMapIdentityEffect(
                mutations, heapObservations, staticCoverage, effects,
                outputBindings, ports, activation, regionId, effectOrdinal,
                issues);
        int mapStateFamilyCount = trackers.size()
                + (identityEffectCount > 0 ? 1 : 0);

        return new HeapEffectExtraction(initializers, effects,
                heapObservations.observations, finiteMapSnapshots,
                dynamicBindingCatalog.normalizedBindings(),
                runtimeHeapEvidence.ignoredEvidence, issues,
                outputBindings,
                candidateCount, mapStateFamilyCount, unsupportedCount,
                malformedCount, syntheticInputCount, initializedInputCount,
                unboundFinalOutputCount, intermediateStateCount,
                identityEffectCount, staticCoverage, runtimeJoin,
                heapObservations);
    }

    private static RuntimeMapStateInputResolution
    runtimeMapStateInputResolution(
            HeapMutation mutation, RuntimeHeapObservationCatalog catalog,
            HeapPortResolver ports, JsonObject activation, JsonObject raw) {
        List<RuntimeMapStateInputObservation> candidates = new ArrayList<>();
        JsonObject requested = object(activation, "requestedOutput");
        String requestedPort = firstNonBlank(string(requested, "portId"),
                string(requested, "symbol"));
        String requestedCell = string(requested, "cell");
        for (RuntimeMapStateInputObservation candidate
                : catalog.mapStateInputsById.values()) {
            JsonObject record = candidate.record;
            String inputPort = string(record, "inputSymbol");
            String inputCell = string(record, "inputCell");
            if (integer(record, "entryCount", -1) != 0
                    || !requestedCell.equals(inputCell)
                    || !requestedPort.equals(ports.outputPort(inputPort))
                    || !exactHeapStateBinding(activation, inputPort,
                    requestedPort, requestedCell)
                    || !mapImplementationMatchesMutation(record, mutation)
                    || !exactRequestedMapTransformer(activation, mutation,
                    requestedPort, requestedCell)
                    || !stableMapInputAtExit(raw, record)) {
                continue;
            }
            candidates.add(candidate);
        }
        return candidates.size() == 1
                ? RuntimeMapStateInputResolution.resolved(candidates.get(0))
                : RuntimeMapStateInputResolution.none();
    }

    private static boolean exactHeapStateBinding(
            JsonObject activation, String inputPort, String outputPort,
            String cell) {
        int matches = 0;
        for (JsonElement element : array(activation, "heapStateBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (inputPort.equals(string(binding, "inputPort"))
                    && outputPort.equals(string(binding, "outputPort"))
                    && cell.equals(string(binding, "cell"))
                    && "STATIC_CELL_IDENTITY_PLUS_RUNTIME_READ_FROM".equals(
                    string(binding, "bindingAuthority"))) {
                matches++;
            }
        }
        return matches == 1;
    }

    private static boolean mapImplementationMatchesMutation(
            JsonObject record, HeapMutation mutation) {
        String implementation = HeapPortResolver.normalizeType(string(
                record, "mapImplementationClass"));
        String owner = HeapPortResolver.normalizeType(mutation.method.owner);
        String expressionType = mutation.mapExpression.isJsonObject()
                ? HeapPortResolver.normalizeType(string(
                mutation.mapExpression.getAsJsonObject(), "_java_type"))
                : "";
        return !implementation.isEmpty()
                && (implementation.equals(owner)
                || implementation.equals(expressionType));
    }

    private static boolean exactRequestedMapTransformer(
            JsonObject activation, HeapMutation mutation,
            String requestedPort, String requestedCell) {
        JsonObject slice = object(activation, "requestedOutputSlice");
        if (!requestedOutputSliceContractOperationallyAdmitted(activation)
                || integer(slice,
                "requestedStateTransformerContractVersion", -1) != 1
                || !bool(slice,
                "requestedStateTransformerContractApplicable", false)
                || !bool(slice,
                "requestedStateTransformerContractComplete", false)
                || !requestedPort.equals(string(slice,
                "requestedStateTransformerContractOutputPort"))
                || !requestedCell.equals(string(slice,
                "requestedStateTransformerContractOutputCell"))
                || !"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1".equals(
                string(slice,
                        "requestedStateTransformerContractAuthority"))
                || array(slice,
                "requestedStateTransformerContractIssues").size() != 0) {
            return false;
        }
        String methodKey = ConcolicCodePosition.vmMethodKey(
                mutation.codePosition);
        int matches = 0;
        for (JsonElement element : array(slice,
                "requestedStateTransformerObligations")) {
            if (!element.isJsonObject()) continue;
            JsonObject obligation = element.getAsJsonObject();
            if (methodKey.equals(ConcolicCodePosition.sootMethodKey(
                    string(obligation, "method")))
                    && requestedCell.equals(string(obligation,
                    "targetCell"))
                    && "HEAP_WRITE".equals(string(obligation,
                    "transferKind"))
                    && "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL".equals(
                    string(obligation, "authority"))
                    && array(obligation, "causalEdgeIds").size() > 0) {
                matches++;
            }
        }
        return matches == 1;
    }

    private static boolean stableMapInputAtExit(JsonObject raw,
                                                JsonObject input) {
        String symbol = string(input, "inputSymbol");
        long mapToken = longInteger(input, "mapObjectToken", -1L);
        int matches = 0;
        for (JsonElement element : array(raw, "finalFieldObservations")) {
            if (!element.isJsonObject()) continue;
            JsonObject exit = element.getAsJsonObject();
            if (symbol.equals(string(exit, "symbol"))
                    && "AT_REGION_EXIT".equals(string(exit, "phase"))
                    && bool(exit, "available", false)
                    && bool(exit, "valueObjectTokenKnown", false)
                    && mapToken > 0L
                    && mapToken == longInteger(exit,
                    "valueObjectToken", -1L)
                    && string(input, "mapImplementationClass").equals(
                    string(exit, "valueClass"))
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                    string(exit, "objectTokenAuthority"))
                    && string(input, "objectTokenScope").equals(
                    string(exit, "objectTokenScope"))
                    && array(input, "path").equals(array(exit, "path"))
                    && bool(input, "leafOwnerObjectTokenKnown", false)
                    && bool(exit, "leafOwnerObjectTokenKnown", false)
                    && longInteger(input, "leafOwnerObjectToken", -1L)
                    == longInteger(exit, "leafOwnerObjectToken", -2L)) {
                matches++;
            }
        }
        return matches == 1;
    }

    /**
     * Certifies the exact finite domain of a runtime-bounded Map input only
     * when the materialization snapshot and the pre-mutation entry reads are
     * a bijection.  A collection size by itself, or a handful of iterator
     * reads by themselves, are deliberately insufficient.
     */
    private static JsonArray exactRuntimeFiniteMapSnapshots(
            JsonElement declaredFieldObservations, JsonArray observations,
            JsonArray effects, JsonObject activation) {
        JsonArray result = new JsonArray();
        if (declaredFieldObservations == null
                || !declaredFieldObservations.isJsonArray()) {
            return result;
        }
        String activationId = string(activation, "activationId");
        Set<String> certifiedPorts = new LinkedHashSet<>();
        for (JsonElement fieldElement
                : declaredFieldObservations.getAsJsonArray()) {
            if (!fieldElement.isJsonObject()) continue;
            JsonObject field = fieldElement.getAsJsonObject();
            String statePort = string(field, "symbol");
            String valueClass = string(field, "valueClass");
            JsonElement mapKeysElement = field.get("mapKeys");
            int cardinality = integer(field, "collectionSize", -1);
            long backingToken = longInteger(field, "valueObjectToken", -1L);
            if (!"AT_MATERIALIZATION".equals(string(field, "phase"))
                    || !bool(field, "available", false)
                    || statePort.isEmpty()
                    || !("java.util.HashMap".equals(valueClass)
                    || "java.util.LinkedHashMap".equals(valueClass))
                    || cardinality < 0 || cardinality > 32
                    || mapKeysElement == null
                    || !mapKeysElement.isJsonArray()
                    || mapKeysElement.getAsJsonArray().size() != cardinality
                    || !bool(field, "valueObjectTokenKnown", false)
                    || backingToken <= 0
                    || !activationId.equals(string(field,
                    "objectTokenScope"))
                    || !certifiedPorts.add(statePort)) {
                continue;
            }

            int firstMutation = Integer.MAX_VALUE;
            for (JsonElement effectElement : effects) {
                if (!effectElement.isJsonObject()) continue;
                JsonObject effect = effectElement.getAsJsonObject();
                if (statePort.equals(string(effect, "inputPort"))) {
                    firstMutation = Math.min(firstMutation, integer(effect,
                            "rawConditionIndex", Integer.MAX_VALUE));
                }
            }
            if (firstMutation == Integer.MAX_VALUE) continue;

            List<JsonObject> reads = new ArrayList<>();
            Set<Long> sequences = new LinkedHashSet<>();
            Set<String> observationIds = new LinkedHashSet<>();
            boolean valid = true;
            for (JsonElement observationElement : observations) {
                if (!observationElement.isJsonObject()) continue;
                JsonObject observation = observationElement.getAsJsonObject();
                if (!"MAP_ENTRY_READ".equals(string(observation, "kind"))
                        || !statePort.equals(string(observation,
                        "statePort"))
                        || longInteger(observation,
                        "backingMapObjectToken", -1L) != backingToken
                        || !activationId.equals(string(observation,
                        "objectTokenScope"))) {
                    continue;
                }
                long sequence = longInteger(observation, "eventSequence", -1L);
                String observationId = string(observation, "observationId");
                if (!bool(observation, "complete", false)
                        || !"EXACT_ACTIVATION_MAP_INPUT_EXPRESSION".equals(
                        string(observation, "stateBindingAuthority"))
                        || !"JAVA_MAP_ENTRY_FROM_BOUND_ENTRY_SET_NEXT".equals(
                        string(observation, "entryBindingAuthority"))
                        || !"SAME_MAP_ENTRY_GET_KEY_AT_NEXT".equals(
                        string(observation, "keyBindingAuthority"))
                        || !"SAME_MAP_ENTRY_GET_VALUE_AT_NEXT".equals(
                        string(observation, "valueBindingAuthority"))
                        || observation.get("keyExpression") == null
                        || !observation.get("keyExpression").isJsonObject()
                        || observation.get("valueExpression") == null
                        || !observation.get("valueExpression").isJsonObject()
                        || integer(observation, "pcBoundary", -1)
                        >= firstMutation
                        || sequence < 0 || !sequences.add(sequence)
                        || observationId.isEmpty()
                        || !observationIds.add(observationId)) {
                    valid = false;
                    break;
                }
                reads.add(observation);
            }
            if (!valid || reads.size() != cardinality) continue;
            reads.sort(Comparator.comparingLong(value -> longInteger(value,
                    "eventSequence", -1L)));

            Map<String, JsonObject> readsByKey = new LinkedHashMap<>();
            for (JsonObject read : reads) {
                String key = finiteSnapshotObservedKey(
                        read.getAsJsonObject("keyExpression"));
                if (key.isEmpty() || readsByKey.put(key, read) != null) {
                    valid = false;
                    break;
                }
            }
            if (!valid) continue;
            Set<String> unmatched = new LinkedHashSet<>(readsByKey.keySet());
            for (JsonElement runtimeKey : mapKeysElement.getAsJsonArray()) {
                String match = "";
                for (String observedKey : unmatched) {
                    if (finiteSnapshotRuntimeKeyMatches(runtimeKey,
                            observedKey)) {
                        if (!match.isEmpty()) {
                            valid = false;
                            break;
                        }
                        match = observedKey;
                    }
                }
                if (!valid || match.isEmpty()) {
                    valid = false;
                    break;
                }
                unmatched.remove(match);
            }
            if (!valid || !unmatched.isEmpty()) continue;

            JsonObject snapshot = new JsonObject();
            snapshot.addProperty("schemaVersion", 1);
            snapshot.addProperty("kind",
                    "EXACT_RUNTIME_FINITE_MAP_SNAPSHOT");
            snapshot.addProperty("snapshotId", "FINITE_MAP_SNAPSHOT:"
                    + statePort + ":" + backingToken);
            snapshot.addProperty("statePort", statePort);
            snapshot.addProperty("cardinality", cardinality);
            snapshot.addProperty("implementationClass", valueClass);
            snapshot.addProperty("backingMapObjectToken", backingToken);
            snapshot.addProperty("objectTokenScope", activationId);
            snapshot.addProperty("firstMutationRawConditionIndex",
                    firstMutation);
            snapshot.addProperty("mapKeysFullyCaptured", true);
            snapshot.addProperty("entryReadBijectionComplete", true);
            snapshot.addProperty("authority",
                    "INITIAL_EXACT_MAP_SIZE_AND_KEYS_PLUS_COMPLETE_ENTRY_"
                            + "READ_BIJECTION_V1");
            JsonArray entries = new JsonArray();
            JsonArray proofObservationIds = new JsonArray();
            for (JsonObject read : reads) {
                JsonObject entry = new JsonObject();
                entry.addProperty("observationId", string(read,
                        "observationId"));
                entry.add("keyExpression",
                        read.get("keyExpression").deepCopy());
                entry.add("valueExpression",
                        read.get("valueExpression").deepCopy());
                entries.add(entry);
                proofObservationIds.add(string(read, "observationId"));
            }
            snapshot.add("entries", entries);
            snapshot.add("proofObservationIds", proofObservationIds);
            snapshot.addProperty("complete", true);
            result.add(snapshot);
        }
        return result;
    }

    private static String finiteSnapshotObservedKey(JsonObject expression) {
        if (!"ConstExpr".equals(string(expression, "_type"))) return "";
        String raw = string(expression, "_exp");
        if (!raw.startsWith("Y_") || raw.length() < 5
                || raw.charAt(3) != '_') return "";
        char kind = raw.charAt(2);
        if ("ZBCSIJ".indexOf(kind) < 0) return "";
        String payload = raw.substring(4);
        try {
            java.math.BigInteger value = new java.math.BigInteger(payload);
            if (!value.toString().equals(payload)) return "";
            return kind + ":" + payload;
        } catch (NumberFormatException ignored) {
            return "";
        }
    }

    private static boolean finiteSnapshotRuntimeKeyMatches(
            JsonElement runtimeKey, String observedKey) {
        if (runtimeKey == null || !runtimeKey.isJsonPrimitive()
                || observedKey.length() < 3 || observedKey.charAt(1) != ':') {
            return false;
        }
        char kind = observedKey.charAt(0);
        String payload = observedKey.substring(2);
        try {
            if (kind == 'Z' && runtimeKey.getAsJsonPrimitive().isBoolean()) {
                return (runtimeKey.getAsBoolean() ? "1" : "0").equals(
                        payload);
            }
            if ("BCSIJ".indexOf(kind) >= 0
                    && runtimeKey.getAsJsonPrimitive().isNumber()) {
                return new java.math.BigInteger(runtimeKey.getAsString())
                        .toString().equals(payload);
            }
        } catch (NumberFormatException ignored) {
            return false;
        }
        return false;
    }

    /**
     * Validates the runtime planner's narrow replacement for an assignment
     * RHS capture on mutation-only heap paths.  It authorizes no semantics by
     * itself: supported runtime Map effects and complete static transformer
     * coverage remain independently mandatory in {@link HeapEffectExtraction}.
     */
    private static String heapEffectCaptureDischargeIssue(
            JsonObject activation) {
        JsonObject slice = object(activation, "requestedOutputSlice");
        if (!bool(slice, "captureDischargedByHeapEffectTransformer",
                false)) {
            return "";
        }
        JsonObject requested = object(activation, "requestedOutput");
        String outputPort = string(slice, "captureDischargeOutputPort");
        String outputCell = string(slice, "captureDischargeOutputCell");
        String inputPort = string(slice, "captureDischargeInputPort");
        if (!"HEAP_EFFECT_STATE_TRANSFORMER".equals(string(slice,
                "captureDischargeAuthority"))
                || bool(activation, "requestedOutputCaptureRequired", true)
                || !bool(activation, "requestedOutputCaptureComplete",
                false)
                || array(activation, "requestedOutputCapture").size() != 0
                || !"HEAP_STATE".equals(string(requested, "kind"))
                || outputPort.isEmpty() || outputCell.isEmpty()
                || inputPort.isEmpty()
                || !outputPort.equals(string(requested, "portId"))
                || !outputCell.equals(string(requested, "cell"))
                || !outputPort.equals(string(slice, "outputPort"))
                || !outputCell.equals(string(slice, "outputCell"))
                || !supportedMapStateField(outputCell)) {
            return "MALFORMED_HEAP_EFFECT_CAPTURE_DISCHARGE";
        }
        if (integer(slice, "requestedStateTransformerContractVersion", -1)
                != 1
                || !bool(slice,
                "requestedStateTransformerContractApplicable", false)
                || !bool(slice,
                "requestedStateTransformerContractComplete", false)
                || !outputPort.equals(string(slice,
                "requestedStateTransformerContractOutputPort"))
                || !outputCell.equals(string(slice,
                "requestedStateTransformerContractOutputCell"))
                || !"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1".equals(
                string(slice,
                        "requestedStateTransformerContractAuthority"))
                || array(slice,
                "requestedStateTransformerContractIssues").size() != 0) {
            return "INCOMPLETE_HEAP_EFFECT_TRANSFORMER_CONTRACT";
        }
        JsonArray obligations = array(slice,
                "requestedStateTransformerObligations");
        if (obligations.size() == 0
                || integer(slice,
                "requestedStateTransformerObligationCount", -1)
                != obligations.size()) {
            return "MISSING_HEAP_EFFECT_TRANSFORMER_OBLIGATIONS";
        }
        for (JsonElement element : obligations) {
            if (!element.isJsonObject()) {
                return "MALFORMED_HEAP_EFFECT_TRANSFORMER_OBLIGATION";
            }
            JsonObject obligation = element.getAsJsonObject();
            if (!"field_mutation".equals(string(obligation, "kind"))
                    || !"HEAP_WRITE".equals(string(obligation,
                    "transferKind"))
                    || !outputCell.equals(string(obligation, "targetCell"))
                    || string(obligation, "siteId").isEmpty()
                    || string(obligation, "method").isEmpty()
                    || array(obligation, "causalEdgeIds").size() == 0) {
                return "NON_MUTATION_HEAP_EFFECT_TRANSFORMER_OBLIGATION";
            }
        }
        int matches = 0;
        for (JsonElement element : array(activation,
                "heapStateBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (inputPort.equals(string(binding, "inputPort"))
                    && outputPort.equals(string(binding, "outputPort"))
                    && outputCell.equals(string(binding, "cell"))
                    && "STATIC_CELL_IDENTITY_PLUS_RUNTIME_READ_FROM".equals(
                    string(binding, "bindingAuthority"))) {
                matches++;
            }
        }
        return matches == 1 ? ""
                : "EXACT_SAME_CELL_HEAP_STATE_BINDING_COUNT=" + matches;
    }

    private static boolean supportedMapStateField(String field) {
        String type = declaredFieldType(field);
        return "java.util.Map".equals(type)
                || "java.util.SortedMap".equals(type)
                || "java.util.NavigableMap".equals(type)
                || "java.util.HashMap".equals(type)
                || "java.util.LinkedHashMap".equals(type)
                || "java.util.TreeMap".equals(type)
                || "java.util.Hashtable".equals(type)
                || "java.util.WeakHashMap".equals(type)
                || "java.util.IdentityHashMap".equals(type)
                || "java.util.concurrent.ConcurrentMap".equals(type)
                || "java.util.concurrent.ConcurrentHashMap".equals(type)
                || "java.util.concurrent.ConcurrentNavigableMap".equals(type)
                || "java.util.concurrent.ConcurrentSkipListMap".equals(type);
    }

    /**
     * Runtime map instrumentation is activation-wide, whereas an output
     * closure is intentionally narrower.  Discarding unrelated evidence is
     * safe for relational completeness only under a frozen, structurally
     * complete slice and only when neither the evidence site/cell nor its
     * condition-linked branch occurs in that slice.  Map-valued requested
     * outputs stay fail-closed because the runtime record may name the same
     * state even when its map expression was not captured.
     */
    private static RuntimeHeapEvidenceSelection selectRuntimeHeapEvidence(
            JsonElement effects, JsonElement observations,
            JsonObject activation, JsonArray branchMappings) {
        JsonArray ignored = new JsonArray();
        JsonElement selectedEffects = selectRuntimeHeapEvidenceArray(
                effects, false, activation, branchMappings, ignored);
        JsonElement selectedObservations = selectRuntimeHeapEvidenceArray(
                observations, true, activation, branchMappings, ignored);
        return new RuntimeHeapEvidenceSelection(selectedEffects,
                selectedObservations, ignored);
    }

    private static JsonElement selectRuntimeHeapEvidenceArray(
            JsonElement declared, boolean observation,
            JsonObject activation, JsonArray branchMappings,
            JsonArray ignored) {
        if (declared == null || declared.isJsonNull()
                || !declared.isJsonArray()) {
            return declared;
        }
        JsonArray selected = new JsonArray();
        JsonArray records = declared.getAsJsonArray();
        for (int ordinal = 0; ordinal < records.size(); ordinal++) {
            JsonElement element = records.get(ordinal);
            if (!element.isJsonObject()
                    || !outsideRequestedOutputSlice(
                    element.getAsJsonObject(), observation, activation,
                    branchMappings)) {
                selected.add(element.deepCopy());
                continue;
            }
            JsonObject record = element.getAsJsonObject();
            JsonObject approximation = new JsonObject();
            approximation.addProperty("classification", "APPROXIMATION");
            approximation.addProperty("reason",
                    "OUTSIDE_REQUESTED_OUTPUT_SLICE");
            approximation.addProperty("source", observation
                    ? "runtimeHeapObservations" : "runtimeHeapEffects");
            approximation.addProperty("ordinal", ordinal);
            approximation.addProperty("kind", string(record, "kind"));
            approximation.addProperty("evidenceId", firstNonBlank(
                    string(record, "observationId"),
                    string(record, "effectId")));
            approximation.addProperty("siteId", string(record, "siteId"));
            approximation.addProperty("requestedOutputCell", string(
                    object(activation, "requestedOutput"), "cell"));
            approximation.addProperty("authority",
                    "FROZEN_REQUESTED_OUTPUT_CAUSAL_SITE_CELL_EXCLUSION_V1");
            ignored.add(approximation);
        }
        return selected;
    }

    private static boolean outsideRequestedOutputSlice(
            JsonObject record, boolean observation, JsonObject activation,
            JsonArray branchMappings) {
        String kind = string(record, "kind");
        if (observation
                ? !("MAP_ENTRY_READ".equals(kind)
                || "FINITE_MAP_ENTRY_SNAPSHOT".equals(kind))
                : !"MAP_REMOVE".equals(kind)) {
            return false;
        }
        JsonObject requested = object(activation, "requestedOutput");
        String requestedCell = string(requested, "cell");
        JsonObject slice = object(activation, "requestedOutputSlice");
        if (requestedCell.isEmpty()
                || !requestedOutputSliceContractOperationallyAdmitted(
                activation)
                || !bool(slice, "structuralComplete", false)
                || bool(slice, "truncated", true)
                || requestedOutputMayBeMapState(requestedCell, slice)) {
            return false;
        }

        Set<String> causalSites = new LinkedHashSet<>();
        Set<String> causalCells = new LinkedHashSet<>();
        collectNamedStrings(slice, "site", causalSites);
        collectNamedStrings(slice, "cell", causalCells);
        collectNamedStrings(slice, "port", causalCells);
        causalCells.add(requestedCell);
        String requestedPort = string(requested, "portId");
        if (!requestedPort.isEmpty()) causalCells.add(requestedPort);

        Set<String> evidenceSites = new LinkedHashSet<>();
        Set<String> evidenceCells = new LinkedHashSet<>();
        collectNamedStrings(record, "site", evidenceSites);
        collectNamedStrings(record, "cell", evidenceCells);
        collectNamedStrings(record, "port", evidenceCells);
        String originMethod = string(record, "originMethod");
        int originUnit = integer(record, "originUnitIndex", -1);
        if (!originMethod.isEmpty() && originUnit >= 0) {
            evidenceSites.add(originMethod + "#u" + originUnit);
        }
        int conditionIndex = observation
                ? integer(record, "rawPathConditionBoundary",
                integer(record, "pcBoundary", -1))
                : integer(record, "vmConditionIndex", -1);
        if (conditionIndex >= 0) {
            for (JsonElement element : branchMappings) {
                if (!element.isJsonObject()) continue;
                JsonObject mapping = element.getAsJsonObject();
                if (integer(mapping, "rawConditionIndex", -1)
                        == conditionIndex) {
                    String site = string(mapping, "siteId");
                    if (!site.isEmpty()) evidenceSites.add(site);
                }
            }
        }
        return !evidenceSites.isEmpty()
                && Collections.disjoint(evidenceSites, causalSites)
                && Collections.disjoint(evidenceCells, causalCells);
    }

    private static boolean requestedOutputMayBeMapState(
            String requestedCell, JsonObject slice) {
        if (supportedMapStateField(requestedCell)) return true;
        for (JsonElement element : array(slice, "causalEdges")) {
            if (element.isJsonObject()
                    && mapTransfer(element.getAsJsonObject())) return true;
        }
        for (JsonElement element : array(slice,
                "requestedStateTransformerObligations")) {
            if (element.isJsonObject()
                    && mapTransfer(element.getAsJsonObject())) return true;
        }
        return false;
    }

    private static boolean mapTransfer(JsonObject value) {
        String transfer = string(value, "transferKind").toUpperCase();
        String kind = string(value, "kind").toUpperCase();
        return transfer.startsWith("MAP_") || kind.startsWith("MAP_")
                || kind.contains("MAP_MUTATION");
    }

    private static void collectNamedStrings(JsonElement value,
                                            String nameFragment,
                                            Set<String> result) {
        if (value == null || value.isJsonNull()) return;
        if (value.isJsonArray()) {
            for (JsonElement element : value.getAsJsonArray()) {
                collectNamedStrings(element, nameFragment, result);
            }
            return;
        }
        if (!value.isJsonObject()) return;
        for (Map.Entry<String, JsonElement> entry
                : value.getAsJsonObject().entrySet()) {
            JsonElement child = entry.getValue();
            if (entry.getKey().toLowerCase().contains(nameFragment)) {
                collectPrimitiveStrings(child, result);
            }
            collectNamedStrings(child, nameFragment, result);
        }
    }

    private static void collectPrimitiveStrings(JsonElement value,
                                                Set<String> result) {
        if (value == null || value.isJsonNull()) return;
        if (value.isJsonPrimitive() && value.getAsJsonPrimitive().isString()) {
            String string = value.getAsString();
            if (!string.isEmpty()) result.add(string);
        } else if (value.isJsonArray()) {
            for (JsonElement element : value.getAsJsonArray()) {
                collectPrimitiveStrings(element, result);
            }
        }
    }

    private static RuntimeHeapObservationCatalog validateRuntimeHeapObservations(
            JsonArray rawPathCondition, JsonElement declaredObservations,
            JsonObject activation, JsonObject raw) {
        String activationId = string(activation, "activationId");
        if (declaredObservations == null) {
            return RuntimeHeapObservationCatalog.legacy();
        }
        List<HeapEffectIssue> issues = new ArrayList<>();
        Map<String, RuntimeHeapObservation> byId = new LinkedHashMap<>();
        Map<String, RuntimeFiniteMapSnapshot> finiteMapSnapshotsById =
                new LinkedHashMap<>();
        Map<String, RuntimeMapStateInputObservation> mapStateInputsById =
                new LinkedHashMap<>();
        if (!declaredObservations.isJsonArray()) {
            issues.add(new HeapEffectIssue(
                    "MALFORMED_RUNTIME_HEAP_OBSERVATIONS", -1,
                    "runtimeHeapObservations", "expected JSON array"));
            return new RuntimeHeapObservationCatalog(false, 0, byId,
                    finiteMapSnapshotsById, mapStateInputsById, issues);
        }

        JsonArray records = declaredObservations.getAsJsonArray();
        Set<Long> eventSequences = new LinkedHashSet<>();
        Set<String> siteOccurrences = new LinkedHashSet<>();
        Map<Integer, JsonObject> finiteMapSnapshotRecords =
                new LinkedHashMap<>();
        for (int ordinal = 0; ordinal < records.size(); ordinal++) {
            JsonElement element = records.get(ordinal);
            if (!element.isJsonObject()) {
                issues.add(new HeapEffectIssue(
                        "MALFORMED_RUNTIME_HEAP_OBSERVATION", -1,
                        "runtimeHeapObservations[" + ordinal + "]",
                        "expected JSON object"));
                continue;
            }
            JsonObject record = element.getAsJsonObject();
            String kind = string(record, "kind");
            if ("MAP_STATE_INPUT_OBSERVATION".equals(kind)) {
                String observationId = string(record, "observationId");
                String siteId = string(record, "siteId");
                String symbol = string(record, "inputSymbol");
                long eventSequence = longInteger(record,
                        "eventSequence", -1L);
                JsonObject action = uniqueObservationInputAction(
                        activation, symbol,
                        "MAP_STATE_INPUT_OBSERVATION");
                long selectedToken = action == null ? -1L
                        : exactFirstContainerSelectionToken(raw, action);
                boolean complete = action != null && selectedToken > 0L
                        && completeMapStateInputObservation(record,
                        activation, action, selectedToken);
                if (!complete) {
                    issues.add(new HeapEffectIssue(
                            "INCOMPLETE_RUNTIME_MAP_STATE_INPUT_OBSERVATION",
                            -1, observationId, siteId));
                    continue;
                }
                boolean duplicate = byId.containsKey(observationId)
                        || mapStateInputsById.containsKey(observationId)
                        || !eventSequences.add(eventSequence)
                        || !siteOccurrences.add(siteId + "#" + symbol);
                if (duplicate) {
                    issues.add(new HeapEffectIssue(
                            "DUPLICATE_RUNTIME_MAP_STATE_INPUT_OBSERVATION",
                            -1, observationId, siteId));
                    continue;
                }
                mapStateInputsById.put(observationId,
                        new RuntimeMapStateInputObservation(record));
                continue;
            }
            if ("FINITE_MAP_ENTRY_SNAPSHOT".equals(kind)) {
                finiteMapSnapshotRecords.put(ordinal, record);
                continue;
            }
            if (!"MAP_ENTRY_READ".equals(kind)) {
                issues.add(new HeapEffectIssue(
                        "UNSUPPORTED_RUNTIME_HEAP_OBSERVATION_KIND", -1,
                        "runtimeHeapObservations[" + ordinal + "]",
                        string(record, "kind")));
                continue;
            }
            String originMethod = string(record, "originMethod");
            int originUnitIndex = integer(record, "originUnitIndex", -1);
            String siteId = string(record, "siteId");
            int occurrence = integer(record, "occurrence", -1);
            String observationId = string(record, "observationId");
            long eventSequence = longInteger(record, "eventSequence", -1L);
            int boundary = integer(record, "pcBoundary", -1);
            int rawBoundary = integer(record, "rawPathConditionBoundary", -2);
            String expectedId = "MAP_ENTRY_READ:" + siteId + "#"
                    + occurrence;
            boolean complete = integer(record, "schemaVersion", -1) == 1
                    && "java.util.Iterator.next".equals(string(record,
                    "operation"))
                    && !originMethod.isEmpty() && originUnitIndex >= 0
                    && siteId.equals(originMethod + "#u" + originUnitIndex)
                    && occurrence >= 1 && observationId.equals(expectedId)
                    && eventSequence > 0L
                    && boundary >= 0 && boundary <= rawPathCondition.size()
                    && rawBoundary == boundary
                    && "ENTRY_SET".equals(string(record, "viewKind"))
                    && "ACTIVATION_LOCAL_BACKED_ENTRY_SET_IDENTITY_AT_NEXT"
                    .equals(string(record, "provenanceAuthority"))
                    && "BOUND_ENTRY_SET_VIEW_BACKING_MAP_IDENTITY".equals(
                    string(record, "mapBindingAuthority"))
                    && "JAVA_MAP_ENTRY_FROM_BOUND_ENTRY_SET_NEXT".equals(
                    string(record, "entryBindingAuthority"))
                    && "SAME_MAP_ENTRY_GET_KEY_AT_NEXT".equals(
                    string(record, "keyBindingAuthority"))
                    && "SAME_MAP_ENTRY_GET_VALUE_AT_NEXT".equals(
                    string(record, "valueBindingAuthority"))
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                    string(record, "objectTokenAuthority"))
                    && !activationId.isEmpty()
                    && activationId.equals(string(record,
                    "objectTokenScope"))
                    && validObservationExpressionAuthorities(record,
                    activationId)
                    && bool(record, "entryBindingComplete", false)
                    && bool(record, "expressionBindingComplete", false)
                    && bool(record, "objectTokenBindingComplete", false)
                    && bool(record, "bindingAuthorityComplete", false)
                    && bool(record, "runtimeProvenanceComplete", false)
                    && bool(record, "complete", false)
                    && completeObservationExpressions(record)
                    && completeObservationTokens(record);
            if (!complete) {
                issues.add(new HeapEffectIssue(
                        "INCOMPLETE_RUNTIME_HEAP_OBSERVATION", boundary,
                        observationId, siteId));
                continue;
            }
            boolean duplicate = byId.containsKey(observationId)
                    || !eventSequences.add(eventSequence)
                    || !siteOccurrences.add(siteId + "#" + occurrence);
            if (duplicate) {
                issues.add(new HeapEffectIssue(
                        "DUPLICATE_RUNTIME_HEAP_OBSERVATION", boundary,
                        observationId, siteId));
                continue;
            }
            byId.put(observationId, new RuntimeHeapObservation(record));
        }
        Set<Long> snapshotEventSequences = new LinkedHashSet<>();
        Set<String> snapshotSiteOccurrences = new LinkedHashSet<>();
        for (Map.Entry<Integer, JsonObject> entry
                : finiteMapSnapshotRecords.entrySet()) {
            int ordinal = entry.getKey();
            JsonObject record = entry.getValue();
            String siteId = string(record, "siteId");
            int occurrence = finiteMapSnapshotOccurrence(record, siteId);
            String observationId = string(record, "observationId");
            long eventSequence = longInteger(record, "eventSequence", -1L);
            boolean complete = completeRuntimeFiniteMapSnapshot(record,
                    activationId, byId, occurrence);
            if (!complete) {
                issues.add(new HeapEffectIssue(
                        "INCOMPLETE_RUNTIME_FINITE_MAP_SNAPSHOT", -1,
                        observationId,
                        "runtimeHeapObservations[" + ordinal + "]"));
                continue;
            }
            boolean duplicate = byId.containsKey(observationId)
                    || mapStateInputsById.containsKey(observationId)
                    || finiteMapSnapshotsById.containsKey(observationId)
                    || !snapshotEventSequences.add(eventSequence)
                    || !snapshotSiteOccurrences.add(siteId + "#"
                    + occurrence);
            if (duplicate) {
                issues.add(new HeapEffectIssue(
                        "DUPLICATE_RUNTIME_FINITE_MAP_SNAPSHOT", -1,
                        observationId, siteId));
                continue;
            }
            finiteMapSnapshotsById.put(observationId,
                    new RuntimeFiniteMapSnapshot(record));
        }
        return new RuntimeHeapObservationCatalog(false, records.size(), byId,
                finiteMapSnapshotsById, mapStateInputsById, issues);
    }

    private static JsonObject uniqueObservationInputAction(
            JsonObject activation, String symbol, String bindingMode) {
        JsonObject match = null;
        for (JsonElement element : runtimeMaterializationActions(activation)) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            if (!symbol.equals(string(action, "symbol"))
                    || !bindingMode.equals(string(action,
                    "bindingMode"))) {
                continue;
            }
            if (match != null) return null;
            match = action;
        }
        return match;
    }

    private static int finiteMapSnapshotOccurrence(JsonObject record,
                                                   String siteId) {
        String prefix = "FINITE_MAP_ENTRY_SNAPSHOT:" + siteId + "#";
        String observationId = string(record, "observationId");
        if (siteId.isEmpty() || !observationId.startsWith(prefix)) return -1;
        String suffix = observationId.substring(prefix.length());
        if (!suffix.matches("[1-9][0-9]*")) return -1;
        try {
            int occurrence = Integer.parseInt(suffix);
            return record.has("occurrence")
                    && integer(record, "occurrence", -1) != occurrence
                    ? -1 : occurrence;
        } catch (NumberFormatException invalid) {
            return -1;
        }
    }

    private static boolean completeRuntimeFiniteMapSnapshot(
            JsonObject record, String activationId,
            Map<String, RuntimeHeapObservation> entryReads,
            int occurrence) {
        String originMethod = string(record, "originMethod");
        int originUnitIndex = integer(record, "originUnitIndex", -1);
        String siteId = string(record, "siteId");
        long eventSequence = longInteger(record, "eventSequence", -1L);
        long backingToken = longInteger(record,
                "backingMapObjectToken", -1L);
        int count = integer(record, "entryCount", -1);
        JsonArray keys = array(record, "keyExpressions");
        JsonArray keyTokens = array(record, "keyObjectTokens");
        JsonArray values = array(record, "valueExpressions");
        JsonArray valueTokens = array(record, "valueObjectTokens");
        JsonArray entries = array(record, "entries");
        boolean complete = integer(record, "schemaVersion", -1) == 1
                && "FINITE_MAP_ENTRY_SNAPSHOT".equals(string(record,
                "kind"))
                && "java.util.Map.entrySet".equals(string(record,
                "operation"))
                && occurrence > 0
                && !originMethod.isEmpty() && originUnitIndex >= 0
                && siteId.equals(originMethod + "#u" + originUnitIndex)
                && eventSequence > 0L
                && "SAME_ITERATOR_NEXT_AS_MAP_ENTRY_READ".equals(
                string(record, "eventSequenceAuthority"))
                && "ENTRY_SET".equals(string(record, "viewKind"))
                && MATERIALIZATION_HOOK_SITE.matcher(string(record,
                "viewOriginSiteId")).matches()
                && MATERIALIZATION_HOOK_SITE.matcher(string(record,
                "iteratorOriginSiteId")).matches()
                && ("java.util.HashMap".equals(string(record,
                "mapImplementationClass"))
                || "java.util.LinkedHashMap".equals(string(record,
                "mapImplementationClass")))
                && "EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_LINKEDHASHMAP_"
                .concat("JAVA_EQUALS_HASHCODE_EXTENSIONAL_V1").equals(
                string(record, "mapImplementationAuthority"))
                && backingToken > 0L
                && longInteger(record, "mapObjectToken", -1L)
                == backingToken
                && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(record, "objectTokenAuthority"))
                && !activationId.isEmpty()
                && activationId.equals(string(record, "objectTokenScope"))
                && record.get("mapExpression") != null
                && record.get("mapExpression").isJsonObject()
                && ("CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_FIRST_ENTRY_SET_"
                .concat("NEXT").equals(string(record,
                        "mapExpressionAuthority"))
                || "CONCRETE_REPLAY_RUNTIME_VALUE_AT_FIRST_ENTRY_SET_NEXT"
                .equals(string(record, "mapExpressionAuthority")))
                && count >= 1 && count <= 4096
                && integer(record, "finiteEntryBound", -1) == 4096
                && integer(record, "sizeBefore", -1) == count
                && integer(record, "entrySetSizeBefore", -1) == count
                && integer(record, "sizeAfter", -1) == count
                && integer(record, "entrySetSizeAfter", -1) == count
                && keys.size() == count && keyTokens.size() == count
                && values.size() == count && valueTokens.size() == count
                && entries.size() == count
                && "CONCRETE_IMMUTABLE_MAP_ENTRY_KEYS_AT_SAME_EXECUTION_"
                .concat("ENTRY_SET_SNAPSHOT").equals(string(record,
                        "keyExpressionAuthority"))
                && "PER_ENTRY_EXACT_RUNTIME_NULL_OR_ACTIVATION_LOCAL_OBJECT_"
                .concat("TOKEN_REF_WITNESS_V1").equals(string(record,
                        "valueExpressionAuthority"))
                && bool(record, "keysDistinct", false)
                && bool(record, "firstIteratorEntryMatched", false)
                && bool(record, "sizeStable", false)
                && bool(record, "entrySetStable", false)
                && bool(record, "preRemove", false)
                && "FIRST_BOUND_ENTRY_SET_ITERATOR_NEXT_EXACT_HASHMAP_OR_"
                .concat("LINKEDHASHMAP_SAME_EXECUTION_PRE_REMOVE_STABLE_SIZE_")
                .concat("AND_ENTRY_SET_DISTINCT_IMMUTABLE_KEYS_V1").equals(
                        string(record, "authority"))
                && bool(record, "complete", false);
        if (!complete) return false;

        Set<String> distinctKeys = new LinkedHashSet<>();
        Set<Long> distinctKeyTokens = new LinkedHashSet<>();
        for (int index = 0; index < count; index++) {
            JsonElement entryElement = entries.get(index);
            if (!entryElement.isJsonObject()) return false;
            JsonObject row = entryElement.getAsJsonObject();
            long keyToken = strictNonNegativeLong(keyTokens.get(index));
            long valueToken = strictNonNegativeLong(valueTokens.get(index));
            String key = runtimeFiniteMapKey(keys.get(index));
            if (integer(row, "index", -1) != index
                    || key.isEmpty() || !distinctKeys.add(key)
                    || keyToken <= 0L || !distinctKeyTokens.add(keyToken)
                    || !keys.get(index).equals(row.get("keyExpression"))
                    || longInteger(row, "keyObjectToken", -1L) != keyToken
                    || !values.get(index).equals(row.get("valueExpression"))
                    || longInteger(row, "valueObjectToken", -1L)
                    != valueToken
                    || !validRuntimeFiniteMapValue(row, valueToken,
                    activationId)) {
                return false;
            }
        }

        RuntimeHeapObservation matchingRead = null;
        for (RuntimeHeapObservation read : entryReads.values()) {
            if (read.eventSequence != eventSequence) continue;
            if (matchingRead != null) return false;
            matchingRead = read;
        }
        if (matchingRead == null) return false;
        JsonObject first = entries.get(0).getAsJsonObject();
        JsonObject read = matchingRead.record;
        return originMethod.equals(string(read, "originMethod"))
                && originUnitIndex == integer(read, "originUnitIndex", -1)
                && siteId.equals(string(read, "siteId"))
                && activationId.equals(string(read, "objectTokenScope"))
                && backingToken == longInteger(read,
                "backingMapObjectToken", -1L)
                && record.get("mapExpression").equals(
                read.get("mapExpression"))
                && runtimeFiniteMapKey(first.get("keyExpression")).equals(
                runtimeFiniteMapReadKey(read.get("keyExpression")))
                && longInteger(first, "keyObjectToken", -1L)
                == longInteger(read, "keyObjectToken", -2L)
                && longInteger(first, "valueObjectToken", -1L)
                == longInteger(read, "valueObjectToken", -2L);
    }

    private static long strictNonNegativeLong(JsonElement value) {
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()
                || !value.getAsString().matches("0|[1-9][0-9]*")) {
            return -1L;
        }
        try {
            return Long.parseLong(value.getAsString());
        } catch (NumberFormatException invalid) {
            return -1L;
        }
    }

    private static String runtimeFiniteMapKey(JsonElement element) {
        if (element == null || !element.isJsonObject()) return "";
        JsonObject expression = element.getAsJsonObject();
        if (!"ConstExpr".equals(string(expression, "_type"))) return "";
        String raw = string(expression, "_exp");
        if (!raw.startsWith("Y_") || raw.length() < 4
                || raw.charAt(3) != '_') return "";
        char kind = raw.charAt(2);
        String type = string(expression, "_java_type").replace('.', '/');
        char declared = "java/lang/Boolean".equals(type) ? 'Z'
                : "java/lang/Byte".equals(type) ? 'B'
                : "java/lang/Character".equals(type) ? 'C'
                : "java/lang/Short".equals(type) ? 'S'
                : "java/lang/Integer".equals(type) ? 'I'
                : "java/lang/Long".equals(type) ? 'J'
                : "java/lang/String".equals(type) ? 'L' : 0;
        if (kind != declared || declared == 0) return "";
        String payload = raw.substring(4);
        if (kind == 'L') return "L:" + payload;
        try {
            java.math.BigInteger integer = new java.math.BigInteger(payload);
            if (!integer.toString().equals(payload)) return "";
            java.math.BigInteger lower;
            java.math.BigInteger upper;
            if (kind == 'Z') {
                lower = java.math.BigInteger.ZERO;
                upper = java.math.BigInteger.ONE;
            } else if (kind == 'B') {
                lower = java.math.BigInteger.valueOf(Byte.MIN_VALUE);
                upper = java.math.BigInteger.valueOf(Byte.MAX_VALUE);
            } else if (kind == 'C') {
                lower = java.math.BigInteger.ZERO;
                upper = java.math.BigInteger.valueOf(Character.MAX_VALUE);
            } else if (kind == 'S') {
                lower = java.math.BigInteger.valueOf(Short.MIN_VALUE);
                upper = java.math.BigInteger.valueOf(Short.MAX_VALUE);
            } else if (kind == 'I') {
                lower = java.math.BigInteger.valueOf(Integer.MIN_VALUE);
                upper = java.math.BigInteger.valueOf(Integer.MAX_VALUE);
            } else if (kind == 'J') {
                lower = java.math.BigInteger.valueOf(Long.MIN_VALUE);
                upper = java.math.BigInteger.valueOf(Long.MAX_VALUE);
            } else {
                return "";
            }
            return integer.compareTo(lower) >= 0
                    && integer.compareTo(upper) <= 0
                    ? kind + ":" + payload : "";
        } catch (NumberFormatException invalid) {
            return "";
        }
    }

    private static String runtimeFiniteMapReadKey(JsonElement element) {
        String structured = runtimeFiniteMapKey(element);
        if (!structured.isEmpty()) return structured;
        if (element == null || !element.isJsonObject()) return "";
        JsonObject expression = element.getAsJsonObject();
        JsonElement value = expression.get("value");
        if (!"CONCRETE_RUNTIME_VALUE".equals(string(expression, "kind"))
                || bool(expression, "symbolic", true)
                || value == null || !value.isJsonPrimitive()) {
            return "";
        }
        String type = string(expression, "valueType").replace('.', '/');
        char kind = "java/lang/Boolean".equals(type) ? 'Z'
                : "java/lang/Byte".equals(type) ? 'B'
                : "java/lang/Character".equals(type) ? 'C'
                : "java/lang/Short".equals(type) ? 'S'
                : "java/lang/Integer".equals(type) ? 'I'
                : "java/lang/Long".equals(type) ? 'J'
                : "java/lang/String".equals(type) ? 'L' : 0;
        if (kind == 0) return "";
        String payload;
        try {
            if (kind == 'Z') {
                if (!value.getAsJsonPrimitive().isBoolean()) return "";
                payload = value.getAsBoolean() ? "1" : "0";
            } else if (kind == 'C') {
                if (!value.getAsJsonPrimitive().isString()
                        || value.getAsString().length() != 1) return "";
                payload = Integer.toString(value.getAsString().charAt(0));
            } else {
                payload = value.getAsString();
            }
        } catch (RuntimeException malformed) {
            return "";
        }
        JsonObject normalized = new JsonObject();
        normalized.addProperty("_type", "ConstExpr");
        normalized.addProperty("_java_type", type);
        normalized.addProperty("_exp", "Y_" + kind + "_" + payload);
        return runtimeFiniteMapKey(normalized);
    }

    private static boolean validRuntimeFiniteMapValue(
            JsonObject row, long valueToken, String activationId) {
        JsonElement expressionElement = row.get("valueExpression");
        if (expressionElement == null || !expressionElement.isJsonObject()) {
            return false;
        }
        JsonObject expression = expressionElement.getAsJsonObject();
        if (bool(row, "valueWasNull", false)) {
            return valueToken == 0L
                    && "EXACT_RUNTIME_NULL_AT_SAME_EXECUTION_ENTRY_SET_"
                    .concat("SNAPSHOT").equals(string(row,
                            "valueExpressionAuthority"))
                    && "SymbolExpression".equals(string(expression,
                    "_type"))
                    && "L".equals(string(expression, "_java_type"))
                    && "N".equals(string(expression, "_exp"));
        }
        return valueToken > 0L
                && VALUE_REF_WITNESS_AUTHORITY.equals(string(row,
                "valueExpressionAuthority"))
                && "SymbolExpression".equals(string(expression, "_type"))
                && "L".equals(string(expression, "_java_type"))
                && valueRefWitnessSymbol(activationId, valueToken).equals(
                string(expression, "_exp"));
    }

    private static boolean completeObservationExpressions(JsonObject record) {
        return hasNonNull(record, "mapExpression")
                && hasNonNull(record, "keyExpression")
                && hasNonNull(record, "valueExpression");
    }

    private static boolean validObservationExpressionAuthorities(
            JsonObject record, String activationId) {
        String expression = string(record, "expressionAuthority");
        String key = string(record, "keyExpressionAuthority");
        String value = string(record, "valueExpressionAuthority");
        boolean generic = "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT"
                .equals(expression)
                || "CONCRETE_REPLAY_RUNTIME_VALUE_AT_ITERATOR_NEXT".equals(
                expression)
                || MAP_REF_WITNESS_AUTHORITY.equals(expression)
                && validMapRefWitness(record, activationId);
        boolean keyExact =
                "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT".equals(key)
                || "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT".equals(key)
                || "CONCRETE_REPLAY_RUNTIME_VALUE_AT_ITERATOR_NEXT".equals(
                key);
        boolean valueExact =
                "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT".equals(
                        value)
                || "AFTER_MATCHED_FIELD_SYMBOLIZATION".equals(value)
                || "BEFORE_ITERATOR_REMOVE_JOIN".equals(value)
                || "CONCRETE_REPLAY_RUNTIME_VALUE_AT_ITERATOR_NEXT".equals(
                value)
                || VALUE_REF_WITNESS_AUTHORITY.equals(value)
                && validValueRefWitness(record, activationId);
        return generic && keyExact && valueExact;
    }

    private static boolean validMapRefWitness(JsonObject record,
                                              String activationId) {
        if (record == null
                || !MAP_REF_WITNESS_AUTHORITY.equals(string(record,
                "expressionAuthority"))
                || integer(record, "mapExpressionWitnessSchemaVersion", -1)
                != 1
                || !MAP_REF_WITNESS_KIND.equals(string(record,
                "mapExpressionWitnessKind"))
                || !VALUE_REF_WITNESS_TOKEN_AUTHORITY.equals(string(record,
                "mapExpressionWitnessAuthority"))) {
            return false;
        }
        long mapToken = longInteger(record,
                "backingMapObjectToken", 0L);
        long witnessToken = longInteger(record,
                "mapExpressionWitnessObjectToken", 0L);
        String witnessScope = string(record,
                "mapExpressionWitnessObjectTokenScope");
        JsonElement expressionElement = record.get("mapExpression");
        if (mapToken <= 0L || witnessToken != mapToken
                || activationId == null || activationId.isEmpty()
                || !activationId.equals(string(record, "objectTokenScope"))
                || !activationId.equals(witnessScope)
                || expressionElement == null
                || !expressionElement.isJsonObject()) {
            return false;
        }
        JsonObject mapExpression = expressionElement.getAsJsonObject();
        return "SymbolExpression".equals(string(mapExpression, "_type"))
                && "L".equals(string(mapExpression, "_java_type"))
                && valueRefWitnessSymbol(activationId, mapToken).equals(
                string(mapExpression, "_exp"));
    }

    private static boolean validValueRefWitness(JsonObject record,
                                                String activationId) {
        if (record == null
                || !VALUE_REF_WITNESS_AUTHORITY.equals(string(record,
                "valueExpressionAuthority"))
                || integer(record, "valueExpressionWitnessSchemaVersion", -1)
                != 1
                || !VALUE_REF_WITNESS_KIND.equals(string(record,
                "valueExpressionWitnessKind"))
                || !VALUE_REF_WITNESS_TOKEN_AUTHORITY.equals(string(record,
                "valueExpressionWitnessAuthority"))) {
            return false;
        }
        long valueToken = longInteger(record, "valueObjectToken", 0L);
        long witnessToken = longInteger(record,
                "valueExpressionWitnessObjectToken", 0L);
        String witnessScope = string(record,
                "valueExpressionWitnessObjectTokenScope");
        JsonElement expressionElement = record.get("valueExpression");
        if (valueToken <= 0L || witnessToken != valueToken
                || activationId == null || activationId.isEmpty()
                || !activationId.equals(string(record, "objectTokenScope"))
                || !activationId.equals(witnessScope)
                || expressionElement == null
                || !expressionElement.isJsonObject()) {
            return false;
        }
        JsonObject expression = expressionElement.getAsJsonObject();
        return "SymbolExpression".equals(string(expression, "_type"))
                && "L".equals(string(expression, "_java_type"))
                && valueRefWitnessSymbol(activationId, valueToken).equals(
                string(expression, "_exp"));
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

    private static boolean importerCertifiedValueRefWitness(
            JsonObject record) {
        long token = longInteger(record,
                "valueExpressionWitnessObjectToken", 0L);
        return VALUE_REF_WITNESS_AUTHORITY.equals(string(record,
                "valueExpressionAuthority"))
                && bool(record, "valueExpressionWitnessCertified", false)
                && VALUE_REF_WITNESS_CERTIFICATION_AUTHORITY.equals(string(
                record, "valueExpressionWitnessCertificationAuthority"))
                && token > 0L
                && token == longInteger(record,
                "valueExpressionWitnessCertifiedObjectToken", 0L)
                && string(record,
                "valueExpressionWitnessObjectTokenScope").equals(string(
                record,
                "valueExpressionWitnessCertifiedObjectTokenScope"));
    }

    private static void copyValueRefWitnessMetadata(JsonObject source,
                                                    JsonObject target) {
        String[] fields = {
                "valueExpressionAuthority", "objectTokenScope",
                "valueExpressionWitnessSchemaVersion",
                "valueExpressionWitnessKind",
                "valueExpressionWitnessObjectToken",
                "valueExpressionWitnessObjectTokenScope",
                "valueExpressionWitnessAuthority",
                "valueExpressionWitnessCertified",
                "valueExpressionWitnessCertificationAuthority",
                "valueExpressionWitnessCertifiedObjectToken",
                "valueExpressionWitnessCertifiedObjectTokenScope"
        };
        for (String field : fields) {
            if (source.has(field) && !source.get(field).isJsonNull()) {
                target.add(field, source.get(field).deepCopy());
            }
        }
    }

    private static void copyMapRefWitnessMetadata(JsonObject source,
                                                  JsonObject target) {
        String[] fields = {
                "expressionAuthority", "objectTokenScope",
                "mapExpressionWitnessSchemaVersion",
                "mapExpressionWitnessKind",
                "mapExpressionWitnessObjectToken",
                "mapExpressionWitnessObjectTokenScope",
                "mapExpressionWitnessAuthority"
        };
        for (String field : fields) {
            if (source.has(field) && !source.get(field).isJsonNull()) {
                target.add(field, source.get(field).deepCopy());
            }
        }
    }

    private static boolean completeObservationTokens(JsonObject record) {
        return bool(record, "backingMapObjectTokenKnown", false)
                && longInteger(record, "backingMapObjectToken", 0L) > 0L
                && bool(record, "entryObjectTokenKnown", false)
                && longInteger(record, "entryObjectToken", 0L) > 0L
                && !bool(record, "entryWasNull", true)
                && bool(record, "keyObjectTokenKnown", false)
                && validNullableKeyToken(record)
                && bool(record, "valueObjectTokenKnown", false)
                && longInteger(record, "valueObjectToken", 0L) > 0L
                && !bool(record, "valueWasNull", true);
    }

    /**
     * Validates the runtime's occurrence-sensitive field instances without
     * turning their static base input into a scalar alias.  Object tokens are
     * admitted only as same-activation evidence joining one field access to
     * one MAP_ENTRY_READ value; the site/occurrence selector is the stable
     * replay identity.
     */
    private static DynamicFieldBindingCatalog validateDynamicFieldBindings(
            JsonElement declaredBindings,
            RuntimeHeapObservationCatalog observations,
            JsonObject activation, JsonElement fieldObservations,
            JsonArray branchMappings,
            JsonElement mapProjectionObservations,
            JsonElement symbolizedInputs, List<HeapMutation> mutations,
            HeapPortResolver ports) {
        if (declaredBindings == null) {
            return DynamicFieldBindingCatalog.legacy();
        }
        List<HeapEffectIssue> issues = new ArrayList<>();
        Map<String, RuntimeDynamicFieldBinding> byId = new LinkedHashMap<>();
        Map<String, RuntimeDynamicFieldBinding> byDynamicSymbol =
                new LinkedHashMap<>();
        if (!declaredBindings.isJsonArray()) {
            issues.add(new HeapEffectIssue(
                    "MALFORMED_DYNAMIC_FIELD_BINDINGS", -1,
                    "dynamicFieldBindings", "expected JSON array"));
            return new DynamicFieldBindingCatalog(false, 0, byId,
                    byDynamicSymbol, issues);
        }

        Map<String, JsonObject> actions = new LinkedHashMap<>();
        Set<String> duplicateActions = new LinkedHashSet<>();
        for (JsonElement element : runtimeMaterializationActions(
                activation)) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            String symbol = string(action, "symbol");
            String bindingMode = string(action, "bindingMode");
            if (!("FIELD_ACCESS".equals(bindingMode)
                    || "CONTAINER_INPUT_OBSERVATION".equals(bindingMode))
                    || symbol.isEmpty()) {
                continue;
            }
            if (actions.put(symbol, action) != null) {
                duplicateActions.add(symbol);
            }
        }
        Map<String, JsonObject> declaredActions = new LinkedHashMap<>();
        Set<String> duplicateDeclaredActions = new LinkedHashSet<>();
        for (JsonElement element : array(activation, "symbolize")) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            String symbol = string(action, "symbol");
            if (!"FIELD_ACCESS".equals(string(action, "bindingMode"))
                    || symbol.isEmpty()) {
                continue;
            }
            if (declaredActions.put(symbol, action) != null) {
                duplicateDeclaredActions.add(symbol);
            }
        }

        JsonArray records = declaredBindings.getAsJsonArray();
        Set<String> siteOccurrences = new LinkedHashSet<>();
        Set<String> entryBasePairs = new LinkedHashSet<>();
        Set<String> containerSelectorTuples = new LinkedHashSet<>();
        Set<String> containerIdentityTuples = new LinkedHashSet<>();
        Set<String> containerBridgeTuples = new LinkedHashSet<>();
        Map<String, List<Integer>> mapProjectionIndices =
                new LinkedHashMap<>();
        Map<String, Integer> mapProjectionExpectedCounts =
                new LinkedHashMap<>();
        for (int ordinal = 0; ordinal < records.size(); ordinal++) {
            JsonElement element = records.get(ordinal);
            if (!element.isJsonObject()) {
                issues.add(new HeapEffectIssue(
                        "MALFORMED_DYNAMIC_FIELD_BINDING", -1,
                        "dynamicFieldBindings[" + ordinal + "]",
                        "expected JSON object"));
                continue;
            }
            JsonObject record = element.getAsJsonObject();
            if ("DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING"
                    .equals(string(record, "kind"))) {
                MapProjectionDynamicFieldValidation validated =
                        validateMapProjectionDynamicFieldBinding(record,
                                activation, fieldObservations,
                                mapProjectionObservations,
                                symbolizedInputs);
                String bindingId = string(record, "dynamicBindingId");
                String dynamic = string(record, "dynamicFieldSymbol");
                if (validated == null) {
                    issues.add(new HeapEffectIssue(
                            "INCOMPLETE_MAP_PROJECTION_DYNAMIC_FIELD_BINDING",
                            -1, firstNonBlank(bindingId,
                            "dynamicFieldBindings[" + ordinal + "]"),
                            string(record, "materializationSiteId")));
                    continue;
                }
                boolean duplicate = byId.containsKey(bindingId)
                        || byDynamicSymbol.containsKey(dynamic)
                        || !siteOccurrences.add(validated.siteOccurrence)
                        || !containerSelectorTuples.add(
                        validated.selectorTuple)
                        || !containerIdentityTuples.add(
                        validated.identityTuple);
                if (duplicate) {
                    issues.add(new HeapEffectIssue(
                            "DUPLICATE_MAP_PROJECTION_DYNAMIC_FIELD_BINDING",
                            -1, bindingId, validated.selectorTuple));
                    continue;
                }
                RuntimeDynamicFieldBinding binding =
                        new RuntimeDynamicFieldBinding(
                                validated.normalized);
                byId.put(bindingId, binding);
                byDynamicSymbol.put(dynamic, binding);
                List<Integer> indices = mapProjectionIndices.get(
                        validated.staticBindingId);
                if (indices == null) {
                    indices = new ArrayList<>();
                    mapProjectionIndices.put(validated.staticBindingId,
                            indices);
                }
                indices.add(validated.outputIndex);
                Integer expected = mapProjectionExpectedCounts.put(
                        validated.staticBindingId,
                        validated.snapshotElementCount);
                if (expected != null && expected.intValue()
                        != validated.snapshotElementCount) {
                    issues.add(new HeapEffectIssue(
                            "MAP_PROJECTION_SNAPSHOT_LENGTH_MISMATCH", -1,
                            validated.staticBindingId,
                            expected + " != "
                                    + validated.snapshotElementCount));
                }
                continue;
            }
            if ("DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(
                    string(record, "kind"))) {
                ContainerDynamicFieldValidation validated =
                        validateContainerDynamicFieldBinding(record,
                                activation, actions, duplicateActions,
                                declaredActions, duplicateDeclaredActions,
                                fieldObservations, branchMappings,
                                symbolizedInputs, mutations, ports);
                String bindingId = string(record, "dynamicBindingId");
                String dynamic = string(record, "dynamicFieldSymbol");
                if (validated == null) {
                    issues.add(new HeapEffectIssue(
                            "INCOMPLETE_DYNAMIC_FIELD_BINDING", -1,
                            firstNonBlank(bindingId,
                                    "dynamicFieldBindings[" + ordinal + "]"),
                            string(record, "materializationSiteId")));
                    continue;
                }
                boolean duplicate = byId.containsKey(bindingId)
                        || byDynamicSymbol.containsKey(dynamic)
                        || !siteOccurrences.add(validated.siteOccurrence)
                        || !containerSelectorTuples.add(
                        validated.selectorTuple)
                        || !containerIdentityTuples.add(
                        validated.identityTuple)
                        || !containerBridgeTuples.add(
                        validated.bridgeTuple);
                if (duplicate) {
                    issues.add(new HeapEffectIssue(
                            "DUPLICATE_DYNAMIC_FIELD_BINDING", -1,
                            bindingId, validated.selectorTuple));
                    continue;
                }
                RuntimeDynamicFieldBinding binding =
                        new RuntimeDynamicFieldBinding(validated.normalized);
                byId.put(bindingId, binding);
                byDynamicSymbol.put(dynamic, binding);
                continue;
            }
            String bindingId = string(record, "dynamicBindingId");
            String base = string(record, "baseInputSymbol");
            String dynamic = string(record, "dynamicFieldSymbol");
            String site = string(record, "materializationSiteId");
            int occurrence = integer(record, "materializationOccurrence", -1);
            String fieldSignature = string(record, "fieldSignature");
            String entryReadId = string(record, "entryReadObservationId");
            long leafOwnerToken = longInteger(record,
                    "leafOwnerObjectToken", 0L);
            long entryValueOwnerToken = longInteger(record,
                    "entryValueOwnerObjectToken", 0L);
            String keyAuthority = string(record, "keyExpressionAuthority");
            JsonObject action = actions.get(base);
            RuntimeHeapObservation entryRead = observations.byId.get(
                    entryReadId);
            String expectedDynamic = base.isEmpty() || site.isEmpty()
                    || occurrence < 1 ? ""
                    : base + ".field." + sha256(site).substring(0, 12)
                    + ".occ." + occurrence;
            boolean keyAuthorityValid =
                    "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT".equals(
                            keyAuthority)
                    || "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT".equals(
                            keyAuthority)
                    || "CONCRETE_REPLAY_RUNTIME_VALUE_AT_ITERATOR_NEXT".equals(
                            keyAuthority);
            boolean structureComplete = integer(record, "schemaVersion", -1)
                    == 1
                    && "DYNAMIC_MAP_ENTRY_FIELD_BINDING".equals(string(record,
                    "kind"))
                    && !bindingId.isEmpty()
                    && bindingId.equals("DYNAMIC_FIELD:" + dynamic)
                    && !base.isEmpty() && !dynamic.isEmpty()
                    && dynamic.equals(expectedDynamic)
                    && !site.isEmpty() && occurrence >= 1
                    && !fieldSignature.isEmpty()
                    && array(record, "fieldPath").size() > 0
                    && leafOwnerToken > 0L && entryValueOwnerToken > 0L
                    && !entryReadId.isEmpty()
                    && hasNonNull(record, "keyExpression")
                    && keyAuthorityValid
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                    string(record, "objectTokenAuthority"))
                    && string(activation, "activationId").equals(string(
                    record, "objectTokenScope"))
                    && bool(record, "complete", false)
                    && "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                    .concat("FIELD_SITE_OCCURRENCE").equals(string(record,
                    "authority"));
            if (action == null || duplicateActions.contains(base)
                    || !fieldSignature.equals(firstNonBlank(string(action,
                    "field"), string(action, "cell")))
                    || !array(record, "fieldPath").equals(array(action,
                    "fieldPath"))) {
                structureComplete = false;
            }
            if (entryRead == null
                    || entryValueOwnerToken != longInteger(entryRead.record,
                    "valueObjectToken", 0L)
                    || !hasNonNull(record, "keyExpression")
                    || !hasNonNull(entryRead.record, "keyExpression")
                    || !record.get("keyExpression").equals(
                    entryRead.record.get("keyExpression"))
                    || !keyAuthority.equals(string(entryRead.record,
                    "keyExpressionAuthority"))) {
                structureComplete = false;
            }
            boolean entryUsesValueRefWitness = entryRead != null
                    && VALUE_REF_WITNESS_AUTHORITY.equals(string(
                    entryRead.record, "valueExpressionAuthority"));
            if (entryUsesValueRefWitness
                    && (!validValueRefWitness(entryRead.record,
                    string(activation, "activationId"))
                    || entryValueOwnerToken != longInteger(entryRead.record,
                    "valueExpressionWitnessObjectToken", 0L))) {
                // Repeat the activation/token check at the semantic field join,
                // rather than treating raw-observation admission as authority
                // for the later entry-value/leaf-owner relation.
                structureComplete = false;
            }

            List<JsonObject> fieldCandidates =
                    fieldObservationsForDynamicBinding(fieldObservations,
                            bindingId, dynamic);
            if (fieldCandidates.size() != 1
                    || !completeDynamicFieldObservation(
                    fieldCandidates.isEmpty() ? null : fieldCandidates.get(0),
                    record)) {
                structureComplete = false;
            }
            boolean duplicate = byId.containsKey(bindingId)
                    || byDynamicSymbol.containsKey(dynamic)
                    || !siteOccurrences.add(base + "\u0000" + site + "\u0000"
                    + occurrence)
                    || !entryBasePairs.add(entryReadId + "\u0000" + base
                    + "\u0000" + GSON.toJson(array(record, "fieldPath")));
            if (!structureComplete) {
                issues.add(new HeapEffectIssue(
                        "INCOMPLETE_DYNAMIC_FIELD_BINDING", -1,
                        firstNonBlank(bindingId,
                                "dynamicFieldBindings[" + ordinal + "]"),
                        firstNonBlank(entryReadId, site)));
                continue;
            }
            if (duplicate) {
                issues.add(new HeapEffectIssue(
                        "DUPLICATE_DYNAMIC_FIELD_BINDING", -1,
                        bindingId, entryReadId));
                continue;
            }
            if (entryUsesValueRefWitness) {
                certifyValueRefWitnessJoin(entryRead.record, record,
                        entryValueOwnerToken,
                        string(activation, "activationId"));
            }
            RuntimeDynamicFieldBinding binding =
                    new RuntimeDynamicFieldBinding(record);
            byId.put(bindingId, binding);
            byDynamicSymbol.put(dynamic, binding);
        }
        for (JsonElement declarationElement : array(activation,
                "mapValueElementFieldProjections")) {
            if (!declarationElement.isJsonObject()) continue;
            JsonObject declaration = declarationElement.getAsJsonObject();
            if (integer(declaration, "schemaVersion", -1) != 1
                    || !"MAP_VALUE_TO_OUTPUT_ARRAY_ELEMENT_FIELD".equals(
                    string(declaration, "kind"))) continue;
            String staticBindingId = string(declaration, "bindingId");
            List<Integer> indices = mapProjectionIndices.get(
                    staticBindingId);
            Integer expected = mapProjectionExpectedCounts.get(
                    staticBindingId);
            boolean orderedAndComplete = indices != null && expected != null
                    && expected > 0 && indices.size() == expected;
            if (orderedAndComplete) {
                for (int index = 0; index < expected; index++) {
                    if (indices.get(index) != index) {
                        orderedAndComplete = false;
                        break;
                    }
                }
            }
            if (!orderedAndComplete) {
                issues.add(new HeapEffectIssue(
                        "MAP_PROJECTION_BINDING_ORDER_OR_LENGTH_INVALID", -1,
                        firstNonBlank(staticBindingId,
                                "mapValueElementFieldProjections"),
                        indices == null ? "missing" : indices.toString()
                                + "/expected=" + expected));
            }
        }
        return new DynamicFieldBindingCatalog(false, records.size(), byId,
                byDynamicSymbol, issues);
    }

    private static void certifyValueRefWitnessJoin(
            JsonObject entryRead, JsonObject dynamicBinding,
            long entryValueOwnerObjectToken, String activationId) {
        if (!validValueRefWitness(entryRead, activationId)
                || entryValueOwnerObjectToken <= 0L
                || entryValueOwnerObjectToken != longInteger(entryRead,
                "valueExpressionWitnessObjectToken", 0L)) {
            return;
        }
        entryRead.addProperty("valueExpressionWitnessCertified", true);
        entryRead.addProperty("valueExpressionWitnessCertificationAuthority",
                VALUE_REF_WITNESS_CERTIFICATION_AUTHORITY);
        entryRead.addProperty("valueExpressionWitnessCertifiedObjectToken",
                entryValueOwnerObjectToken);
        entryRead.addProperty(
                "valueExpressionWitnessCertifiedObjectTokenScope",
                activationId);
        dynamicBinding.addProperty("entryValueRefWitnessJoinCertified", true);
        dynamicBinding.addProperty(
                "entryValueRefWitnessJoinCertificationAuthority",
                VALUE_REF_WITNESS_CERTIFICATION_AUTHORITY);
        dynamicBinding.addProperty(
                "entryValueRefWitnessJoinObjectToken",
                entryValueOwnerObjectToken);
        dynamicBinding.addProperty(
                "entryValueRefWitnessJoinObjectTokenScope", activationId);
    }

    /**
     * Admits one producer-side Map-view element field only after joining the
     * schema-v3 runtime row to one schema-v1 static declaration, the unique
     * same-activation entry snapshot and output-identity validation, and the
     * exact symbolizeField observation for that element identity.
     */
    private static MapProjectionDynamicFieldValidation
    validateMapProjectionDynamicFieldBinding(
            JsonObject record, JsonObject activation,
            JsonElement fieldObservations,
            JsonElement projectionObservations,
            JsonElement symbolizedInputs) {
        String activationId = string(activation, "activationId");
        String id = string(record, "dynamicBindingId");
        String base = string(record, "baseInputSymbol");
        String dynamic = string(record, "dynamicFieldSymbol");
        String site = string(record, "materializationSiteId");
        int occurrence = integer(record, "materializationOccurrence", -1);
        String signature = string(record, "fieldSignature");
        JsonArray path = array(record, "fieldPath");
        long leafToken = longInteger(record, "leafOwnerObjectToken", 0L);
        JsonObject selector = object(record, "mapProjectionSelector");
        String staticBindingId = string(selector, "bindingId");
        int outputIndex = integer(selector, "outputIndex", -1);

        List<JsonObject> declarations = new ArrayList<>();
        for (JsonElement element : array(activation,
                "mapValueElementFieldProjections")) {
            if (element.isJsonObject() && staticBindingId.equals(string(
                    element.getAsJsonObject(), "bindingId"))) {
                declarations.add(element.getAsJsonObject());
            }
        }
        if (declarations.size() != 1) return null;
        JsonObject declaration = declarations.get(0);
        String mapPort = string(declaration, "mapInputPort");
        String mapCell = string(declaration, "mapInputCell");
        String outputPort = string(declaration, "outputPort");
        String outputCell = string(declaration, "outputCell");
        String operation = string(declaration, "mapProjectionOperation");
        String declaredOwner = normalizeContainerType(string(declaration,
                "declaredFieldOwnerClass"));
        String declaredType = normalizeContainerType(string(declaration,
                "declaredFieldType"));
        String declaredName = string(declaration, "declaredFieldName");
        String outputValidationMode = string(declaration,
                "outputValidationMode");
        String outputFieldName = declaredFieldName(outputCell);
        String groupId = mapPort + "\n" + outputPort + "\n" + outputCell
                + "\n" + operation;
        String expectedSite = string(declaration, "snapshotSiteId")
                + "#map-element:" + staticBindingId;
        String expectedDynamic = base.isEmpty() || site.isEmpty()
                || occurrence < 1 ? "" : base + ".field."
                + sha256(site).substring(0, 12) + ".occ." + occurrence;

        boolean complete = integer(declaration, "schemaVersion", -1) == 1
                && "MAP_VALUE_TO_OUTPUT_ARRAY_ELEMENT_FIELD".equals(
                string(declaration, "kind"))
                && bool(declaration, "complete", false)
                && !staticBindingId.isEmpty() && !mapPort.isEmpty()
                && !mapCell.isEmpty() && !outputPort.isEmpty()
                && !outputCell.isEmpty()
                && "MAP_VALUES_VIEW".equals(operation)
                && ("EXACT_REQUESTED_OUTPUT_CAPTURE".equals(
                outputValidationMode)
                || "ROOT_RETURN_PROJECTED_FIELD".equals(
                outputValidationMode))
                && !string(declaration, "mapViewSiteId").isEmpty()
                && !string(declaration, "snapshotSiteId").isEmpty()
                && !string(declaration,
                "downstreamRegionInstance").isEmpty()
                && !string(declaration, "downstreamInputPort").isEmpty()
                && !string(declaration,
                "downstreamBaseInputSymbol").isEmpty()
                && !string(declaration,
                "downstreamContainerBindingId").isEmpty()
                && "CURRENT_EXECUTION_ENTRY_SNAPSHOT_THEN_EXACT_"
                .concat("OUTPUT_INDEX_IDENTITY").equals(string(
                        declaration, "selectorAuthority"))
                && array(declaration,
                "projectionProofCausalEdgeIds").size() > 0
                && signature.equals(string(declaration,
                "declaredFieldSignature"))
                && path.equals(array(declaration, "fieldPath"))
                && path.size() == 1
                && declaredName.equals(path.get(0).getAsString())
                && (outputFieldName.isEmpty()
                ? array(declaration, "outputFieldPath").size() == 0
                : array(declaration, "outputFieldPath").size() == 1
                && outputFieldName.equals(array(declaration,
                "outputFieldPath").get(0).getAsString()))
                && declaredOwner.equals(normalizeContainerType(
                declaredFieldOwner(signature)))
                && declaredType.equals(normalizeContainerType(
                fieldJavaType(signature)))
                && bool(declaration,
                "recursiveElementProjectionComposable", false);

        List<JsonObject> mapActions = new ArrayList<>();
        for (JsonElement element : runtimeMaterializationActions(
                activation)) {
            if (element.isJsonObject() && mapPort.equals(string(
                    element.getAsJsonObject(), "symbol"))) {
                mapActions.add(element.getAsJsonObject());
            }
        }
        complete &= mapActions.size() == 1
                && mapCell.equals(string(mapActions.isEmpty()
                ? new JsonObject() : mapActions.get(0), "cell"));

        complete &= integer(record, "schemaVersion", -1) == 3
                && "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING"
                .equals(string(record, "kind"))
                && !activationId.isEmpty() && id.equals(
                "DYNAMIC_FIELD:" + dynamic)
                && base.equals(mapPort) && site.equals(expectedSite)
                && dynamic.equals(expectedDynamic) && occurrence > 0
                && outputIndex == occurrence - 1
                && leafToken > 0L
                && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(record, "objectTokenAuthority"))
                && activationId.equals(string(record,
                "objectTokenScope"))
                && "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                .concat("EXACT_OUTPUT_IDENTITY").equals(string(
                        record, "authority"))
                && bool(record, "complete", false)
                && !record.has("containerSelector")
                && !record.has("entryReadObservationId")
                && !record.has("keyExpression");

        complete &= "MAP_OUTPUT_ARRAY_INDEX".equals(string(selector,
                "kind"))
                && mapPort.equals(string(selector, "mapInputPort"))
                && mapCell.equals(string(selector, "mapInputCell"))
                && outputPort.equals(string(selector, "outputPort"))
                && outputCell.equals(string(selector, "outputCell"))
                && operation.equals(string(selector,
                "mapProjectionOperation"))
                && outputIndex >= 0
                && occurrence == integer(selector,
                "elementOccurrence", -2)
                && declaredOwner.equals(normalizeContainerType(string(
                selector, "declaredFieldOwnerClass")))
                && declaredType.equals(normalizeContainerType(string(
                selector, "declaredFieldType")))
                && signature.equals(string(selector,
                "declaredFieldSignature"))
                && longInteger(selector, "mapObjectToken", 0L) > 0L
                && longInteger(selector, "elementObjectToken", 0L)
                == leafToken
                && longInteger(selector, "outputArrayObjectToken", 0L)
                > 0L
                && bool(selector, "outputIdentityVerified", false)
                && supportedMapProjectionImplementation(selector)
                && bool(selector, "entryConcreteFieldValueCaptured", false)
                && bool(selector, "noInterveningFieldWriteVerified", false)
                && bool(selector, "outputFieldValueVerified", false)
                && "SAME_EXECUTION_BOUNDED_OBSERVED_SCHEDULE_EXACT_"
                .concat("DECLARED_FIELD_ENTRY_VALUE_PLUS_NO_INTERVENING_")
                .concat("RUNTIME_FIELD_WRITE_AND_EXACT_OUTPUT_RECHECK")
                .equals(string(selector, "fieldValueFlowAuthority"))
                && !string(selector,
                "outputVerificationAuthority").isEmpty()
                && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(selector, "objectTokenAuthority"))
                && activationId.equals(string(selector,
                "objectTokenScope"))
                && "NONE".equals(string(selector,
                "crossExecutionOrdinalAuthority"))
                && exactImmutableMapKeyExpression(selector.get(
                "expectedMapKey"))
                && "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT"
                .equals(string(selector, "expectedMapKeyAuthority"))
                && "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                .concat("POSITIONAL_REFERENCE_EQUALITY").equals(string(
                        selector, "sourceOutputIndexAuthority"))
                && "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_AND_"
                .concat("EXACT_OUTPUT_IDENTITY").equals(string(selector,
                        "replaySelectionAuthority"))
                && "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                .concat("EXACT_OUTPUT_IDENTITY").equals(string(
                        selector, "authority"))
                && bool(selector, "complete", false);

        List<JsonObject> entries = projectionObservations(
                projectionObservations, groupId, "ENTRY_SNAPSHOT");
        List<JsonObject> outputs = projectionObservations(
                projectionObservations, groupId,
                "OUTPUT_IDENTITY_VALIDATION");
        if (entries.size() != 1 || outputs.size() != 1) return null;
        JsonObject entry = entries.get(0);
        JsonObject output = outputs.get(0);
        int snapshotCount = integer(entry, "snapshotElementCount", -1);
        JsonArray snapshotTokens = array(entry,
                "snapshotElementObjectTokens");
        JsonArray snapshotKeys = array(entry,
                "snapshotEntryKeyExpressions");
        complete &= completeMapProjectionObservation(entry, activationId,
                groupId, mapPort, outputPort, outputCell, operation)
                && completeMapProjectionObservation(output, activationId,
                groupId, mapPort, outputPort, outputCell, operation)
                && snapshotCount > 0 && snapshotTokens.size() == snapshotCount
                && snapshotKeys.size() == snapshotCount
                && outputIndex < snapshotCount
                && bool(entry, "entrySnapshotComplete", false)
                && bool(entry, "entrySetViewOrderVerified", false)
                && "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT"
                .equals(string(entry, "entryKeyExpressionAuthority"))
                && "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                .concat("POSITIONAL_REFERENCE_EQUALITY").equals(string(
                        entry, "entrySetViewOrderAuthority"))
                && selector.get("expectedMapKey") != null
                && selector.get("expectedMapKey").equals(
                        snapshotKeys.get(outputIndex))
                && bool(output, "outputIdentityVerified", false)
                && bool(output, "outputFieldValueFlowVerified", false)
                && integer(output, "projectedFieldBindingCount", -1) > 0
                && integer(output, "outputFieldValueVerifiedCount", -2)
                == integer(output, "projectedFieldBindingCount", -1)
                && "SAME_EXECUTION_BOUNDED_OBSERVED_SCHEDULE_EXACT_"
                .concat("DECLARED_FIELD_ENTRY_VALUE_PLUS_NO_INTERVENING_")
                .concat("RUNTIME_FIELD_WRITE_AND_EXACT_OUTPUT_RECHECK")
                .equals(string(output, "fieldValueFlowAuthority"))
                && longInteger(output, "outputArrayObjectToken", 0L)
                == longInteger(selector, "outputArrayObjectToken", 0L)
                && string(output, "outputVerificationAuthority").equals(
                string(selector, "outputVerificationAuthority"))
                && validMapProjectionOutputAuthority(activation,
                declaration, string(output,
                        "outputVerificationAuthority"))
                && string(entry, "mapImplementationClass").equals(
                string(selector, "mapImplementationClass"))
                && string(output, "mapImplementationClass").equals(
                string(selector, "mapImplementationClass"))
                && string(entry, "mapImplementationAuthority").equals(
                string(selector, "mapImplementationAuthority"))
                && string(output, "mapImplementationAuthority").equals(
                string(selector, "mapImplementationAuthority"))
                && longInteger(entry, "mapObjectToken", 0L)
                == longInteger(selector, "mapObjectToken", 0L)
                && longInteger(output, "mapObjectToken", 0L)
                == longInteger(selector, "mapObjectToken", 0L);
        complete &= projectionObservationOrdinal(projectionObservations,
                groupId, "ENTRY_SNAPSHOT")
                < projectionObservationOrdinal(projectionObservations,
                groupId, "OUTPUT_IDENTITY_VALIDATION");
        Set<Long> uniqueTokens = new LinkedHashSet<>();
        Set<String> uniqueKeys = new LinkedHashSet<>();
        for (int index = 0; index < snapshotTokens.size(); index++) {
            long token;
            try {
                token = snapshotTokens.get(index).getAsLong();
            } catch (RuntimeException malformed) {
                token = 0L;
            }
            complete &= token > 0L && uniqueTokens.add(token);
            JsonElement key = snapshotKeys.get(index);
            String stableKey = stableImmutableMapKeySelector(key);
            complete &= !stableKey.isEmpty()
                    && uniqueKeys.add(stableKey);
            if (index == outputIndex) complete &= token == leafToken;
        }

        List<JsonObject> observed = mapProjectionFieldObservations(
                fieldObservations, id, dynamic);
        complete &= observed.size() == 1
                && completeMapProjectionFieldObservation(
                observed.isEmpty() ? null : observed.get(0), record,
                selector, activationId);
        complete &= countString(symbolizedInputs, dynamic) == 1;
        if (!complete) return null;

        JsonObject normalized = record.deepCopy();
        normalized.addProperty("fieldJavaType", fieldJavaType(signature));
        normalized.addProperty("outputValidationMode",
                outputValidationMode);
        normalized.addProperty("entrySnapshotElementCount", snapshotCount);
        normalized.addProperty("outputElementCount", snapshotCount);
        normalized.add("entrySnapshotElementObjectTokens",
                snapshotTokens.deepCopy());
        normalized.add("entrySnapshotMapKeyExpressions",
                snapshotKeys.deepCopy());
        normalized.addProperty("entryKeyExpressionAuthority",
                string(entry, "entryKeyExpressionAuthority"));
        normalized.addProperty("entrySetViewOrderAuthority",
                string(entry, "entrySetViewOrderAuthority"));
        normalized.addProperty("runtimeSymbolizationAuthority",
                "EXACT_SYMBOLIZE_FIELD_OBSERVATION_AND_SYMBOLIZED_INPUT");
        normalized.addProperty("projectionEvidenceAuthority",
                "UNIQUE_ENTRYSET_KEYED_SNAPSHOT_AND_OUTPUT_IDENTITY_"
                        + "VALIDATION");
        return new MapProjectionDynamicFieldValidation(normalized,
                base + "\u0000" + site + "\u0000" + occurrence,
                staticBindingId + "\u0000" + mapPort + "\u0000"
                        + outputPort + "\u0000" + outputCell + "\u0000"
                        + operation + "\u0000" + outputIndex + "\u0000"
                        + signature + "\u0000" + GSON.toJson(path)
                        + "\u0000" + GSON.toJson(selector.get(
                        "expectedMapKey")),
                activationId + "\u0000" + longInteger(selector,
                        "mapObjectToken", 0L) + "\u0000" + leafToken
                        + "\u0000" + longInteger(selector,
                        "outputArrayObjectToken", 0L),
                staticBindingId, outputIndex, snapshotCount);
    }

    private static List<JsonObject> projectionObservations(
            JsonElement observations, String groupId, String phase) {
        List<JsonObject> result = new ArrayList<>();
        if (observations == null || !observations.isJsonArray()) return result;
        for (JsonElement element : observations.getAsJsonArray()) {
            if (element.isJsonObject()
                    && groupId.equals(string(element.getAsJsonObject(),
                    "groupId"))
                    && phase.equals(string(element.getAsJsonObject(),
                    "phase"))) result.add(element.getAsJsonObject());
        }
        return result;
    }

    private static int projectionObservationOrdinal(
            JsonElement observations, String groupId, String phase) {
        if (observations == null || !observations.isJsonArray()) return -1;
        JsonArray rows = observations.getAsJsonArray();
        for (int index = 0; index < rows.size(); index++) {
            JsonElement element = rows.get(index);
            if (element.isJsonObject()
                    && groupId.equals(string(element.getAsJsonObject(),
                    "groupId"))
                    && phase.equals(string(element.getAsJsonObject(),
                    "phase"))) return index;
        }
        return -1;
    }

    private static boolean validMapProjectionOutputAuthority(
            JsonObject activation, JsonObject declaration,
            String authority) {
        String mode = string(declaration, "outputValidationMode");
        if ("ROOT_RETURN_PROJECTED_FIELD".equals(mode)) {
            return "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD".equals(
                    authority);
        }
        if (!"EXACT_REQUESTED_OUTPUT_CAPTURE".equals(mode)) return false;
        List<JsonObject> captures = new ArrayList<>();
        for (JsonElement element : array(activation,
                "requestedOutputCapture")) {
            if (!element.isJsonObject()) continue;
            JsonObject capture = element.getAsJsonObject();
            if (string(declaration, "outputPort").equals(firstNonBlank(
                    string(capture, "outputPort"),
                    string(capture, "portId")))
                    && string(declaration, "outputCell").equals(
                    firstNonBlank(string(capture, "outputCell"),
                            string(capture, "cell")))) {
                captures.add(capture);
            }
        }
        if (captures.size() != 1) return false;
        String kind = firstNonBlank(string(captures.get(0), "captureKind"),
                "CALL_ARGUMENT");
        if ("FIELD_ASSIGNMENT_RHS".equals(kind)) {
            return "ACTIVE_TOKEN_EXACT_POST_INSTANCE_FIELD_ASSIGNMENT"
                    .equals(authority);
        }
        return "CALL_ARGUMENT".equals(kind)
                && "ACTIVE_TOKEN_EXACT_ORIGINAL_CALL_ARGUMENT".equals(
                authority);
    }

    private static boolean completeMapProjectionObservation(
            JsonObject row, String activationId, String groupId,
            String mapPort, String outputPort, String outputCell,
            String operation) {
        return integer(row, "schemaVersion", -1) == 1
                && "MAP_VALUE_OUTPUT_ARRAY_PROJECTION".equals(string(row,
                "kind"))
                && groupId.equals(string(row, "groupId"))
                && mapPort.equals(string(row, "mapInputPort"))
                && outputPort.equals(string(row, "outputPort"))
                && outputCell.equals(string(row, "outputCell"))
                && operation.equals(string(row, "mapProjectionOperation"))
                && supportedMapProjectionImplementation(row)
                && longInteger(row, "mapObjectToken", 0L) > 0L
                && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(row, "objectTokenAuthority"))
                && activationId.equals(string(row, "objectTokenScope"))
                && "NONE".equals(string(row,
                "crossExecutionOrdinalAuthority"))
                && "ENTRYSET_KEY_AND_MAP_VIEW_ELEMENT_SAME_EXECUTION_"
                .concat("POSITIONAL_REFERENCE_EQUALITY").equals(string(row,
                        "identityPolicy"))
                && bool(row, "entrySetViewOrderVerified", false)
                && "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                .concat("POSITIONAL_REFERENCE_EQUALITY").equals(string(row,
                        "entrySetViewOrderAuthority"))
                && bool(row, "complete", false);
    }

    private static boolean supportedMapProjectionImplementation(
            JsonObject row) {
        String implementation = string(row, "mapImplementationClass");
        return ("java.util.HashMap".equals(implementation)
                || "java.util.LinkedHashMap".equals(implementation))
                && "EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_LINKEDHASHMAP_"
                .concat("JAVA_EQUALS_HASHCODE_EXTENSIONAL_V1").equals(
                        string(row, "mapImplementationAuthority"));
    }

    private static boolean completeMapProjectionFieldObservation(
            JsonObject observation, JsonObject binding, JsonObject selector,
            String activationId) {
        if (observation == null) return false;
        JsonObject observedSelector = object(observation,
                "mapProjectionSelector");
        return bool(observation, "available", false)
                && "AT_MAP_PROJECTION_ENTRY".equals(string(observation,
                "phase"))
                && string(binding, "dynamicFieldSymbol").equals(string(
                observation, "symbol"))
                && string(binding, "dynamicBindingId").equals(string(
                observation, "dynamicBindingId"))
                && string(binding, "kind").equals(string(observation,
                "dynamicFieldBindingKind"))
                && array(binding, "fieldPath").equals(array(observation,
                "path"))
                && string(binding, "fieldSignature").equals(string(
                observation, "exactFieldSignature"))
                && "BYTECODE_GETFIELD_DECLARING_OWNER_NAME_AND_TYPE".equals(
                string(observation, "exactFieldSignatureAuthority"))
                && longInteger(binding, "leafOwnerObjectToken", 0L)
                == longInteger(observation, "accessOwnerObjectToken", -1L)
                && longInteger(binding, "leafOwnerObjectToken", 0L)
                == longInteger(observation, "leafOwnerObjectToken", -2L)
                && bool(observation, "accessOwnerObjectTokenKnown", false)
                && bool(observation, "leafOwnerObjectTokenKnown", false)
                && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(observation, "objectTokenAuthority"))
                && activationId.equals(string(observation,
                "objectTokenScope"))
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "bindingId")
                && "MAP_OUTPUT_ARRAY_INDEX".equals(string(observedSelector,
                "kind"))
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "mapInputPort")
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "mapInputCell")
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "outputPort")
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "outputCell")
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "mapProjectionOperation")
                && integer(selector, "outputIndex", -1) == integer(
                observedSelector, "outputIndex", -2)
                && integer(selector, "elementOccurrence", -1) == integer(
                observedSelector, "elementOccurrence", -2)
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "declaredFieldOwnerClass")
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "declaredFieldType")
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "declaredFieldSignature")
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "mapImplementationClass")
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "mapImplementationAuthority")
                && selector.get("expectedMapKey") != null
                && selector.get("expectedMapKey").equals(
                        observedSelector.get("expectedMapKey"))
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "expectedMapKeyAuthority")
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "sourceOutputIndexAuthority")
                && sameMapProjectionSelectorMember(selector,
                observedSelector, "replaySelectionAuthority")
                && longInteger(selector, "mapObjectToken", 0L)
                == longInteger(observedSelector, "mapObjectToken", -1L)
                && longInteger(selector, "elementObjectToken", 0L)
                == longInteger(observedSelector,
                "elementObjectToken", -2L)
                && longInteger(observedSelector,
                "outputArrayObjectToken", -1L) == 0L
                && !bool(observedSelector,
                "outputIdentityVerified", true)
                && supportedMapProjectionImplementation(observedSelector)
                && bool(observedSelector,
                "entryConcreteFieldValueCaptured", false)
                && !bool(observedSelector,
                "noInterveningFieldWriteVerified", true)
                && !bool(observedSelector,
                "outputFieldValueVerified", true)
                && string(observedSelector,
                "fieldValueFlowAuthority").isEmpty()
                && !bool(observedSelector, "complete", true)
                && activationId.equals(string(observedSelector,
                "objectTokenScope"))
                && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(observedSelector, "objectTokenAuthority"))
                && "NONE".equals(string(observedSelector,
                "crossExecutionOrdinalAuthority"))
                && string(selector, "authority").equals(string(
                observedSelector, "authority"));
    }

    private static boolean sameMapProjectionSelectorMember(
            JsonObject left, JsonObject right, String member) {
        return !string(left, member).isEmpty()
                && string(left, member).equals(string(right, member));
    }

    /** Exact ConstExpr subset emitted by Runtime for immutable Map keys. */
    private static boolean exactImmutableMapKeyExpression(
            JsonElement element) {
        if (element == null || !element.isJsonObject()) return false;
        JsonObject expression = element.getAsJsonObject();
        if (!"ConstExpr".equals(string(expression, "_type"))) return false;
        String encoded = string(expression, "_exp");
        if (!encoded.startsWith("Y_") || encoded.length() < 4
                || encoded.charAt(3) != '_') return false;
        char kind = encoded.charAt(2);
        String type = string(expression, "_java_type").replace('.', '/');
        char declared = 0;
        if ("java/lang/Boolean".equals(type)) declared = 'Z';
        else if ("java/lang/Byte".equals(type)) declared = 'B';
        else if ("java/lang/Character".equals(type)) declared = 'C';
        else if ("java/lang/Short".equals(type)) declared = 'S';
        else if ("java/lang/Integer".equals(type)) declared = 'I';
        else if ("java/lang/Long".equals(type)) declared = 'J';
        else if ("java/lang/String".equals(type)) declared = 'L';
        if (kind != declared) return false;
        String payload = encoded.substring(4);
        try {
            java.math.BigInteger integer;
            if (kind == 'Z') return "0".equals(payload)
                    || "1".equals(payload);
            if (kind == 'B' || kind == 'C' || kind == 'S'
                    || kind == 'I' || kind == 'J') {
                integer = new java.math.BigInteger(payload);
                if (!integer.toString().equals(payload)) return false;
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

    private static String stableImmutableMapKeySelector(JsonElement key) {
        if (!exactImmutableMapKeyExpression(key)) return "";
        JsonObject expression = key.getAsJsonObject();
        String raw = string(expression, "_exp");
        char kind = raw.charAt(2);
        String value = raw.substring(4);
        return kind + ":" + value.length() + ":" + value;
    }

    private static int countString(JsonElement values, String target) {
        if (values == null || !values.isJsonArray()) return 0;
        int count = 0;
        for (JsonElement value : values.getAsJsonArray()) {
            if (value.isJsonPrimitive() && target.equals(value.getAsString()))
                count++;
        }
        return count;
    }

    private static List<JsonObject> mapProjectionFieldObservations(
            JsonElement observations, String bindingId, String dynamic) {
        List<JsonObject> result = new ArrayList<>();
        if (observations == null || !observations.isJsonArray()) return result;
        for (JsonElement element : observations.getAsJsonArray()) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if (bindingId.equals(string(row, "dynamicBindingId"))
                    && dynamic.equals(string(row, "symbol"))
                    && "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING"
                    .equals(string(row, "dynamicFieldBindingKind"))) {
                result.add(row);
            }
        }
        return result;
    }

    /**
     * Closes the runtime container-element selector back to the exact static
     * declaration, concrete field observation, and VM guard expression.  A
     * container binding has no map-entry/key selector fallback: every member
     * of this join is mandatory and activation-local.
     */
    private static ContainerDynamicFieldValidation
    validateContainerDynamicFieldBinding(
            JsonObject record, JsonObject activation,
            Map<String, JsonObject> actions, Set<String> duplicateActions,
            Map<String, JsonObject> declaredActions,
            Set<String> duplicateDeclaredActions,
            JsonElement fieldObservations, JsonArray branchMappings,
            JsonElement symbolizedInputs, List<HeapMutation> mutations,
            HeapPortResolver ports) {
        String activationId = string(activation, "activationId");
        String bindingId = string(record, "dynamicBindingId");
        String base = string(record, "baseInputSymbol");
        String dynamic = string(record, "dynamicFieldSymbol");
        String site = string(record, "materializationSiteId");
        int occurrence = integer(record, "materializationOccurrence", -1);
        String fieldSignature = string(record, "fieldSignature");
        JsonArray fieldPath = array(record, "fieldPath");
        String firstFieldPathSegment = fieldPath.size() > 0
                && fieldPath.get(0).isJsonPrimitive()
                && fieldPath.get(0).getAsJsonPrimitive().isString()
                ? fieldPath.get(0).getAsString() : "";
        long leafToken = longInteger(record, "leafOwnerObjectToken", 0L);
        JsonObject selector = object(record, "containerSelector");
        String selectorBindingId = string(selector, "bindingId");
        String containerPort = string(selector, "containerInputPort");
        String containerCell = string(selector, "containerInputCell");
        String selectorAuthority = string(selector, "selectorAuthority");
        String resolvedFrom = string(selector,
                "resolvedFromSelectorAuthority");
        int elementIndex = integer(selector, "elementIndex", -1);
        int elementOccurrence = integer(selector,
                "elementOccurrence", -1);
        String declaredOwner = normalizeContainerType(string(selector,
                "declaredFieldOwnerClass"));
        String declaredType = normalizeContainerType(string(selector,
                "declaredFieldType"));
        long containerToken = longInteger(selector,
                "containerObjectToken", 0L);
        long elementToken = longInteger(selector,
                "elementObjectToken", 0L);
        String actualHookSite = string(record, "actualHookSiteId");
        int actualHookOccurrence = integer(record,
                "actualHookOccurrence", -1);
        String effectiveSite = string(record,
                "effectiveMaterializationSiteId");
        int effectiveOccurrence = integer(record,
                "effectiveMaterializationOccurrence", -1);
        String bridgeAuthority = string(record,
                "materializationSiteBridgeAuthority");
        String bridgeBindingId = string(record,
                "materializationSiteBridgeBindingId");
        long bridgeElementToken = longInteger(record,
                "materializationSiteBridgeElementObjectToken", 0L);
        String bridgeTokenScope = string(record,
                "materializationSiteBridgeObjectTokenScope");

        List<JsonObject> declarations = new ArrayList<>();
        for (JsonElement element : array(activation,
                "containerElementFieldBindings")) {
            if (element.isJsonObject() && selectorBindingId.equals(string(
                    element.getAsJsonObject(), "bindingId"))) {
                declarations.add(element.getAsJsonObject());
            }
        }
        JsonObject declaration = declarations.size() == 1
                ? declarations.get(0) : null;
        boolean snapshotDeclaration = declaration != null
                && integer(declaration, "schemaVersion", -1) == 2
                && "CONTAINER_SNAPSHOT".equals(string(declaration,
                "materializationMode"))
                && "STATIC_EXACT_DIRECT_ARRAY_ELEMENT_FIELD_PATH_CHAIN_V1"
                .equals(string(declaration, "proofAuthority"));

        String expectedDynamic = base.isEmpty() || site.isEmpty()
                || occurrence < 1 ? ""
                : base + ".field." + sha256(site).substring(0, 12)
                + ".occ." + occurrence;
        boolean complete = integer(record, "schemaVersion", -1) == 2
                && "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(
                string(record, "kind"))
                && !activationId.isEmpty()
                && !bindingId.isEmpty()
                && bindingId.equals("DYNAMIC_FIELD:" + dynamic)
                && !base.isEmpty() && dynamic.equals(expectedDynamic)
                && !site.isEmpty() && occurrence > 0
                && !fieldSignature.isEmpty() && fieldPath.size() > 0
                && leafToken > 0L
                && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(record, "objectTokenAuthority"))
                && activationId.equals(string(record, "objectTokenScope"))
                && "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_"
                .concat("AND_STABLE_FIELD_SITE_OCCURRENCE").equals(
                        string(record, "authority"))
                && bool(record, "complete", false)
                && !record.has("entryReadObservationId")
                && !record.has("keyExpression")
                && !record.has("keyExpressionAuthority");

        boolean exactMaterializationOrigin = snapshotDeclaration
                ? ("CONTAINER_SNAPSHOT:" + selectorBindingId).equals(
                actualHookSite)
                : MATERIALIZATION_HOOK_SITE.matcher(actualHookSite)
                .matches();
        complete &= exactMaterializationOrigin
                && actualHookOccurrence > 0
                && site.equals(effectiveSite)
                && occurrence == effectiveOccurrence
                && CONTAINER_SITE_BRIDGE_AUTHORITY.equals(bridgeAuthority)
                && selectorBindingId.equals(bridgeBindingId)
                && (snapshotDeclaration
                ? bridgeElementToken == elementToken
                : leafToken == bridgeElementToken)
                && activationId.equals(bridgeTokenScope);

        complete &= "ARRAY_INDEX".equals(string(selector, "kind"))
                && !selectorBindingId.isEmpty()
                && !containerPort.isEmpty() && !containerCell.isEmpty()
                && "EXACT_ARRAY_INDEX".equals(selectorAuthority)
                && ("EXACT_ARRAY_INDEX".equals(resolvedFrom)
                || "DISCOVER_UNIQUE_IDENTITY_INDEX".equals(resolvedFrom))
                && elementIndex >= 0
                && elementOccurrence == occurrence
                && !declaredOwner.isEmpty() && !declaredType.isEmpty()
                && containerToken > 0L && elementToken > 0L
                && (snapshotDeclaration || leafToken == elementToken)
                && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(selector, "objectTokenAuthority"))
                && activationId.equals(string(selector,
                "objectTokenScope"))
                && "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                .concat("ACTIVATION_LOCAL_ELEMENT_IDENTITY").equals(
                        string(selector, "authority"))
                && bool(selector, "complete", false)
                && selectorBindingId.equals(string(record,
                "containerBindingId"))
                && containerPort.equals(string(record,
                "containerInputPort"))
                && containerCell.equals(string(record,
                "containerInputCell"))
                && selectorAuthority.equals(string(record,
                "selectorAuthority"))
                && resolvedFrom.equals(string(record,
                "resolvedFromSelectorAuthority"))
                && elementIndex == integer(record, "elementIndex", -2)
                && elementOccurrence == integer(record,
                "elementOccurrence", -2)
                && declaredOwner.equals(normalizeContainerType(string(record,
                "declaredFieldOwnerClass")))
                && declaredType.equals(normalizeContainerType(string(record,
                "declaredFieldType")));

        JsonObject action = snapshotDeclaration
                ? declaredActions.get(base) : actions.get(base);
        JsonObject containerAction = actions.get(containerPort);
        complete &= action != null && containerAction != null
                && !(snapshotDeclaration
                ? duplicateDeclaredActions.contains(base)
                : duplicateActions.contains(base))
                && !duplicateActions.contains(containerPort)
                && !base.equals(containerPort)
                && fieldSignature.equals(firstNonBlank(string(action,
                "field"), string(action, "cell")))
                && fieldPath.equals(array(action, "fieldPath"))
                && containerCell.equals(string(containerAction, "cell"));
        if (snapshotDeclaration && action != null) {
            complete &= "FIELD_ACCESS".equals(string(action,
                    "bindingMode"))
                    && "HEAP_OBJECT_FIELD".equals(string(action,
                    "location"))
                    && "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1"
                    .equals(string(action, "fieldPathAuthority"))
                    && fieldSignature.equals(string(action,
                    "leafFieldSignature"))
                    && declaredFieldOwner(fieldSignature).equals(string(
                    action, "leafOwnerClass"))
                    && declaredFieldName(fieldSignature).equals(string(
                    action, "leafField"))
                    && firstFieldPathSegment.equals(string(action,
                    "accessField"))
                    && !string(action, "accessFieldSignature").isEmpty();
        }
        if (declaration == null) {
            complete = false;
        } else {
            String declaredSelector = string(declaration,
                    "selectorAuthority");
            int declaredIndex = integer(declaration, "elementIndex", -2);
            int declaredOccurrence = integer(declaration,
                    "elementOccurrence", -2);
            boolean exactDeclaration = "EXACT_ARRAY_INDEX".equals(
                    declaredSelector)
                    && declaredIndex == elementIndex
                    && declaredOccurrence == occurrence;
            boolean discoveryDeclaration =
                    "DISCOVER_UNIQUE_IDENTITY_INDEX".equals(
                            declaredSelector)
                    && declaredIndex == -1
                    && (declaredOccurrence == -1
                    || declaredOccurrence == occurrence);
            boolean declarationSchemaComplete = snapshotDeclaration
                    ? exactSchema2ContainerSnapshotDeclaration(declaration,
                    fieldSignature, fieldPath, activation)
                    && exactDeclaration
                    : integer(declaration, "schemaVersion", -1) == 1
                    && (exactDeclaration || discoveryDeclaration);
            complete &= declarationSchemaComplete
                    && "ARRAY_ELEMENT_FIELD".equals(string(declaration,
                    "kind"))
                    && base.equals(string(declaration,
                    "baseInputSymbol"))
                    && containerPort.equals(string(declaration,
                    "containerInputPort"))
                    && containerCell.equals(string(declaration,
                    "containerInputCell"))
                    && fieldPath.equals(array(declaration, "fieldPath"))
                    && site.equals(string(declaration,
                    "fieldMaterializationSiteId"))
                    && declaredOwner.equals(normalizeContainerType(string(
                    declaration, "declaredFieldOwnerClass")))
                    && declaredType.equals(normalizeContainerType(string(
                    declaration, "declaredFieldType")))
                    && resolvedFrom.equals(declaredSelector)
                    && (!snapshotDeclaration
                    || fieldSignature.equals(string(declaration,
                    "declaredFieldSignature")));
        }

        String signatureOwner = normalizeContainerType(
                declaredFieldOwner(fieldSignature));
        String signatureType = normalizeContainerType(
                fieldJavaType(fieldSignature));
        complete &= declaredOwner.equals(signatureOwner)
                && declaredType.equals(signatureType);

        List<JsonObject> observed = fieldObservationsForDynamicBinding(
                fieldObservations, bindingId, dynamic);
        JsonObject observation = observed.size() == 1
                ? observed.get(0) : null;
        complete &= observed.size() == 1
                && completeContainerDynamicFieldObservation(observation,
                record, selector, activationId);
        if (snapshotDeclaration && observation != null && action != null) {
            complete &= bool(observation, "accessOwnerObjectTokenKnown",
                    false)
                    && longInteger(observation,
                    "accessOwnerObjectToken", 0L) == elementToken
                    && string(observation, "accessOwnerClass").equals(
                    declaredFieldOwner(string(action,
                            "accessFieldSignature")))
                    && string(observation, "leafOwnerClass").equals(
                    declaredFieldOwner(fieldSignature));
        }

        List<ContainerPutConsumerWitness> consumers = snapshotDeclaration
                ? Collections.<ContainerPutConsumerWitness>emptyList()
                : exactContainerPutConsumerWitnesses(mutations, ports,
                activation, dynamic);
        List<ContainerSnapshotBranchWitness> branchConsumers =
                snapshotDeclaration
                        ? exactContainerSnapshotBranchWitnesses(activation,
                        branchMappings, dynamic, fieldSignature)
                        : Collections.<ContainerSnapshotBranchWitness>
                        emptyList();
        complete &= snapshotDeclaration
                ? countString(symbolizedInputs, dynamic) == 1
                && branchConsumers.size() == 1
                : consumers.size() == 1;
        if (!complete) return null;

        JsonObject normalized = record.deepCopy();
        normalized.addProperty("fieldJavaType", fieldJavaType(
                fieldSignature));
        if (snapshotDeclaration) {
            ContainerSnapshotBranchWitness consumer =
                    branchConsumers.get(0);
            normalized.add("fieldExpression",
                    consumer.fieldExpression.deepCopy());
            normalized.addProperty("fieldExpressionAuthority",
                    "EXACT_BRANCH_MAPPING_DYNAMIC_SYMBOL");
            normalized.addProperty("consumerWitnessSiteId",
                    consumer.siteId);
            normalized.addProperty("consumerWitnessOccurrence",
                    consumer.occurrence);
            normalized.addProperty("consumerWitnessOperation", "BRANCH");
            normalized.addProperty("consumerWitnessAuthority",
                    CONTAINER_SNAPSHOT_BRANCH_CONSUMER_AUTHORITY);
        } else {
            ContainerPutConsumerWitness consumer = consumers.get(0);
            normalized.add("fieldExpression",
                    consumer.mutation.keyExpression.deepCopy());
            normalized.addProperty("fieldExpressionAuthority",
                    "EXACT_REQUESTED_OUTPUT_MAP_PUT_KEY_DYNAMIC_SYMBOL");
            normalized.addProperty("consumerWitnessRawConditionIndex",
                    consumer.mutation.rawIndex);
            normalized.addProperty("consumerWitnessCodePosition",
                    consumer.mutation.codePosition);
            normalized.addProperty("consumerWitnessSiteId",
                    consumer.mutation.siteId);
            normalized.addProperty("consumerWitnessOccurrence",
                    consumer.mutation.occurrence);
            normalized.addProperty("consumerWitnessInputPort",
                    consumer.binding.inputPort);
            normalized.addProperty("consumerWitnessOutputPort",
                    consumer.binding.outputPort);
            normalized.addProperty("consumerWitnessOperation", "MAP_PUT");
            normalized.addProperty("consumerWitnessAuthority",
                    CONTAINER_PUT_CONSUMER_AUTHORITY);
        }
        String selectorTuple = selectorBindingId + "\u0000" + base
                + "\u0000" + containerPort + "\u0000" + containerCell
                + "\u0000" + elementIndex + "\u0000" + occurrence
                + "\u0000" + site + "\u0000" + GSON.toJson(fieldPath);
        String identityTuple = activationId + "\u0000" + containerToken
                + "\u0000" + elementToken + "\u0000" + fieldSignature
                + "\u0000" + GSON.toJson(fieldPath);
        String bridgeTuple = activationId + "\u0000" + bridgeBindingId
                + "\u0000" + bridgeElementToken + "\u0000"
                + actualHookSite + "\u0000" + actualHookOccurrence
                + "\u0000" + effectiveSite + "\u0000"
                + effectiveOccurrence;
        return new ContainerDynamicFieldValidation(normalized,
                base + "\u0000" + site + "\u0000" + occurrence,
                selectorTuple, identityTuple, bridgeTuple);
    }

    private static boolean exactSchema2ContainerSnapshotDeclaration(
            JsonObject declaration, String fieldSignature,
            JsonArray fieldPath, JsonObject activation) {
        if (integer(declaration, "schemaVersion", -1) != 2
                || !"CONTAINER_SNAPSHOT".equals(string(declaration,
                "materializationMode"))
                || !"STATIC_EXACT_DIRECT_ARRAY_ELEMENT_FIELD_PATH_CHAIN_V1"
                .equals(string(declaration, "proofAuthority"))
                || !bool(declaration, "complete", false)
                || !fieldSignature.equals(string(declaration,
                "declaredFieldSignature"))
                || !"boolean".equals(fieldJavaType(fieldSignature))
                || !declaredFieldOwner(fieldSignature).equals(string(
                declaration, "declaredFieldOwnerClass"))
                || !"boolean".equals(string(declaration,
                "declaredFieldType"))
                || fieldPath.size() < 2 || fieldPath.size() > 4
                || array(declaration, "proofCausalEdgeIds").size()
                != 4 * fieldPath.size()
                || !MATERIALIZATION_HOOK_SITE.matcher(string(declaration,
                "fieldMaterializationSiteId")).matches()
                || !MATERIALIZATION_HOOK_SITE.matcher(string(declaration,
                "arrayLoadSiteId")).matches()) {
            return false;
        }
        Set<String> proofIds = new LinkedHashSet<>();
        Set<String> sliceEdgeIds = new LinkedHashSet<>();
        JsonObject slice = object(activation, "requestedOutputSlice");
        for (JsonElement edgeId : array(slice, "causalEdgeIds")) {
            if (edgeId.isJsonPrimitive()) {
                sliceEdgeIds.add(edgeId.getAsString());
            }
        }
        for (JsonElement edge : array(slice, "causalEdges")) {
            if (edge.isJsonObject()) {
                String edgeId = string(edge.getAsJsonObject(), "edgeId");
                if (!edgeId.isEmpty()) sliceEdgeIds.add(edgeId);
            }
        }
        for (JsonElement proof : array(declaration,
                "proofCausalEdgeIds")) {
            if (!proof.isJsonPrimitive()
                    || proof.getAsString().trim().isEmpty()
                    || !proofIds.add(proof.getAsString())
                    || !sliceEdgeIds.contains(proof.getAsString())) {
                return false;
            }
        }
        for (JsonElement segment : fieldPath) {
            if (!segment.isJsonPrimitive()
                    || !segment.getAsJsonPrimitive().isString()
                    || segment.getAsString().trim().isEmpty()) {
                return false;
            }
        }
        JsonElement leaf = fieldPath.get(fieldPath.size() - 1);
        return leaf.isJsonPrimitive()
                && leaf.getAsJsonPrimitive().isString()
                && declaredFieldName(fieldSignature).equals(
                leaf.getAsString())
                && declaredFieldName(fieldSignature).equals(string(
                declaration, "declaredFieldName"));
    }

    /**
     * A schema-v2 snapshot leaf is admitted only when one in-slice VM branch
     * consumes the byte-exact Boolean symbol created for that dynamic leaf.
     * Prefix matches and owner-wide aliases are deliberately rejected.
     */
    private static List<ContainerSnapshotBranchWitness>
    exactContainerSnapshotBranchWitnesses(
            JsonObject activation, JsonArray branchMappings,
            String dynamicFieldSymbol, String fieldSignature) {
        List<ContainerSnapshotBranchWitness> result = new ArrayList<>();
        String owner = declaredFieldOwner(fieldSignature);
        if (!"boolean".equals(fieldJavaType(fieldSignature))
                || owner.isEmpty() || dynamicFieldSymbol.isEmpty()) {
            return result;
        }
        String expectedRaw = "M_Z_field_" + dynamicFieldSymbol + "_"
                + owner.replace('.', '/');
        Set<String> applicationMethods = new LinkedHashSet<>();
        String rootMethod = ConcolicCodePosition.sootMethodKey(string(
                activation, "rootMethod"));
        if (!rootMethod.isEmpty()) applicationMethods.add(rootMethod);
        JsonObject slice = object(activation, "requestedOutputSlice");
        for (JsonElement method : array(slice, "methods")) {
            if (!method.isJsonPrimitive()) continue;
            String key = ConcolicCodePosition.sootMethodKey(
                    method.getAsString());
            if (!key.isEmpty()) applicationMethods.add(key);
        }
        for (JsonElement edge : array(slice, "causalEdges")) {
            if (!edge.isJsonObject()) continue;
            String key = ConcolicCodePosition.sootMethodKey(string(
                    edge.getAsJsonObject(), "method"));
            if (!key.isEmpty()) applicationMethods.add(key);
        }

        for (JsonElement element : branchMappings) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            JsonElement condition = mapping.get("condition");
            SnapshotDynamicExpressionScan scan =
                    new SnapshotDynamicExpressionScan();
            collectSnapshotDynamicExpressions(condition,
                    dynamicFieldSymbol, expectedRaw, scan);
            if (scan.referenceCount == 0) continue;
            String method = ConcolicCodePosition.sootMethodKey(string(
                    mapping, "method"));
            int unitIndex = integer(mapping, "unitIndex", -1);
            int occurrence = integer(mapping, "occurrence", -1);
            int conditionIndex = integer(mapping, "conditionIndex", -1);
            int rawConditionIndex = integer(mapping,
                    "rawConditionIndex", -1);
            String siteId = string(mapping, "siteId");
            boolean exact = !scan.invalid
                    && scan.referenceCount == 1
                    && scan.expression != null
                    && !method.isEmpty()
                    && applicationMethods.contains(method)
                    && unitIndex >= 0
                    && siteId.equals(string(mapping, "method")
                    + "#u" + unitIndex)
                    && occurrence > 0
                    && conditionIndex >= 0
                    && conditionIndex == rawConditionIndex
                    && !bool(mapping, "overrideApplied", true)
                    && "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_"
                    .concat("PC_INDEX").equals(string(mapping,
                            "mappingPolicy"))
                    && bool(mapping, "vmBranchEventValidated", false)
                    && "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_PC_INDEX"
                    .equals(string(mapping, "conditionAuthority"));
            if (!exact) {
                return Collections.emptyList();
            }
            result.add(new ContainerSnapshotBranchWitness(
                    scan.expression, siteId, occurrence));
        }
        return result;
    }

    private static void collectSnapshotDynamicExpressions(
            JsonElement expression, String dynamicFieldSymbol,
            String expectedRaw, SnapshotDynamicExpressionScan scan) {
        if (expression == null || expression.isJsonNull()) return;
        if (expression.isJsonArray()) {
            for (JsonElement item : expression.getAsJsonArray()) {
                collectSnapshotDynamicExpressions(item, dynamicFieldSymbol,
                        expectedRaw, scan);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        String raw = string(object, "_exp");
        if (("SymbolExpression".equals(type)
                || "ConSymbolExp".equals(type))
                && HeapPortResolver.containsSymbolReference(raw,
                dynamicFieldSymbol)) {
            scan.referenceCount++;
            if (!expectedRaw.equals(raw)
                    || !"Z".equals(string(object, "_java_type"))
                    || scan.expression != null) {
                scan.invalid = true;
            } else {
                scan.expression = object.deepCopy();
            }
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            if (!"_exp".equals(entry.getKey())
                    && !"_code_position".equals(entry.getKey())) {
                collectSnapshotDynamicExpressions(entry.getValue(),
                        dynamicFieldSymbol, expectedRaw, scan);
            }
        }
    }

    /**
     * A container field is an input only because its value is consumed by the
     * requested heap transformer.  Guard mention is intentionally
     * insufficient: the raw semantic PC must contain one MAP_PUT whose exact
     * key expression is this dynamic field and whose receiver resolves to the
     * activation's requested output state family.
     */
    private static List<ContainerPutConsumerWitness>
    exactContainerPutConsumerWitnesses(
            List<HeapMutation> mutations, HeapPortResolver ports,
            JsonObject activation, String dynamicFieldSymbol) {
        Set<String> applicationMethods = new LinkedHashSet<>();
        String rootMethod = ConcolicCodePosition.sootMethodKey(string(
                activation, "rootMethod"));
        if (!rootMethod.isEmpty()) applicationMethods.add(rootMethod);
        JsonObject slice = object(activation, "requestedOutputSlice");
        for (JsonElement element : array(slice, "methods")) {
            if (!element.isJsonPrimitive()) continue;
            String method = ConcolicCodePosition.sootMethodKey(
                    element.getAsString());
            if (!method.isEmpty()) applicationMethods.add(method);
        }
        for (JsonElement element : array(slice, "causalEdges")) {
            if (!element.isJsonObject()) continue;
            String method = ConcolicCodePosition.sootMethodKey(string(
                    element.getAsJsonObject(), "method"));
            if (!method.isEmpty()) applicationMethods.add(method);
        }
        for (JsonElement element : array(slice,
                "requestedStateTransformerObligations")) {
            if (!element.isJsonObject()) continue;
            String method = ConcolicCodePosition.sootMethodKey(string(
                    element.getAsJsonObject(), "method"));
            if (!method.isEmpty()) applicationMethods.add(method);
        }

        List<ContainerPutConsumerWitness> result = new ArrayList<>();
        for (HeapMutation mutation : mutations) {
            if (mutation.kind != MapMutationKind.MAP_PUT
                    || !directDynamicSymbolExpression(
                    mutation.keyExpression, dynamicFieldSymbol)) {
                continue;
            }
            String applicationMethod = ConcolicCodePosition.vmMethodKey(
                    mutation.codePosition);
            if (applicationMethod.isEmpty()
                    || !applicationMethods.contains(applicationMethod)) {
                continue;
            }
            HeapPortBinding binding = ports.requestedOutputBinding(
                    mutation.mapExpression);
            if (binding.resolved) {
                result.add(new ContainerPutConsumerWitness(mutation,
                        binding));
            }
        }
        return result;
    }

    private static boolean directDynamicSymbolExpression(
            JsonElement expression, String dynamicFieldSymbol) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        String raw = string(object, "_exp");
        return ("SymbolExpression".equals(type)
                || "ConSymbolExp".equals(type))
                && !string(object, "_java_type").isEmpty()
                && !raw.isEmpty()
                && HeapPortResolver.containsSymbolReference(raw,
                dynamicFieldSymbol);
    }

    private static boolean completeContainerDynamicFieldObservation(
            JsonObject observation, JsonObject binding, JsonObject selector,
            String activationId) {
        if (observation == null
                || observation.has("entryReadObservationId")
                || observation.has("entryReadObservationIds")
                || observation.has("keyExpression")
                || observation.has("keyExpressionAuthority")) {
            return false;
        }
        JsonObject observedSelector = object(observation,
                "containerSelector");
        return bool(observation, "available", false)
                && "AT_MATERIALIZATION".equals(string(observation,
                "phase"))
                && string(binding, "baseInputSymbol").equals(string(
                observation, "baseInputSymbol"))
                && string(binding, "dynamicBindingId").equals(string(
                observation, "dynamicBindingId"))
                && string(binding, "dynamicFieldSymbol").equals(string(
                observation, "dynamicFieldSymbol"))
                && string(binding, "materializationSiteId").equals(string(
                observation, "materializationSiteId"))
                && integer(binding, "materializationOccurrence", -1)
                == integer(observation, "materializationOccurrence", -2)
                && string(binding, "actualHookSiteId").equals(string(
                observation, "actualHookSiteId"))
                && integer(binding, "actualHookOccurrence", -1)
                == integer(observation, "actualHookOccurrence", -2)
                && string(binding, "effectiveMaterializationSiteId").equals(
                string(observation, "effectiveMaterializationSiteId"))
                && integer(binding,
                "effectiveMaterializationOccurrence", -1)
                == integer(observation,
                "effectiveMaterializationOccurrence", -2)
                && string(binding,
                "materializationSiteBridgeAuthority").equals(string(
                observation, "materializationSiteBridgeAuthority"))
                && string(binding,
                "materializationSiteBridgeBindingId").equals(string(
                observation, "materializationSiteBridgeBindingId"))
                && longInteger(binding,
                "materializationSiteBridgeElementObjectToken", 0L)
                == longInteger(observation,
                "materializationSiteBridgeElementObjectToken", -1L)
                && string(binding,
                "materializationSiteBridgeObjectTokenScope").equals(string(
                observation,
                "materializationSiteBridgeObjectTokenScope"))
                && integer(observation,
                "dynamicFieldBindingSchemaVersion", -1) == 2
                && "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(string(
                observation, "dynamicFieldBindingKind"))
                && string(binding, "fieldSignature").equals(string(
                observation, "fieldSignature"))
                && array(binding, "fieldPath").equals(array(observation,
                "fieldPath"))
                && array(binding, "fieldPath").equals(array(observation,
                "path"))
                && bool(observation, "leafOwnerObjectTokenKnown", false)
                && longInteger(binding, "leafOwnerObjectToken", 0L)
                == longInteger(observation, "leafOwnerObjectToken", -1L)
                && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(observation, "objectTokenAuthority"))
                && activationId.equals(string(observation,
                "objectTokenScope"))
                && selector.equals(observedSelector)
                && sameContainerSelectorFlatFields(observation, selector)
                && string(binding, "authority").equals(string(observation,
                "dynamicFieldBindingAuthority"))
                && bool(observation, "dynamicFieldBindingComplete", false)
                && bool(observation, "complete", false);
    }

    private static boolean sameContainerSelectorFlatFields(
            JsonObject target, JsonObject selector) {
        return string(selector, "bindingId").equals(string(target,
                "containerBindingId"))
                && string(selector, "containerInputPort").equals(string(
                target, "containerInputPort"))
                && string(selector, "containerInputCell").equals(string(
                target, "containerInputCell"))
                && string(selector, "selectorAuthority").equals(string(
                target, "selectorAuthority"))
                && string(selector, "resolvedFromSelectorAuthority").equals(
                string(target, "resolvedFromSelectorAuthority"))
                && integer(selector, "elementIndex", -1)
                == integer(target, "elementIndex", -2)
                && integer(selector, "elementOccurrence", -1)
                == integer(target, "elementOccurrence", -2)
                && normalizeContainerType(string(selector,
                "declaredFieldOwnerClass")).equals(normalizeContainerType(
                string(target, "declaredFieldOwnerClass")))
                && normalizeContainerType(string(selector,
                "declaredFieldType")).equals(normalizeContainerType(
                string(target, "declaredFieldType")));
    }

    private static String normalizeContainerType(String type) {
        return type == null ? "" : type.trim().replace('/', '.');
    }

    private static List<JsonObject> fieldObservationsForDynamicBinding(
            JsonElement fieldObservations, String bindingId,
            String dynamicSymbol) {
        List<JsonObject> result = new ArrayList<>();
        if (fieldObservations == null || !fieldObservations.isJsonArray()) {
            return result;
        }
        for (JsonElement element : fieldObservations.getAsJsonArray()) {
            if (!element.isJsonObject()) continue;
            JsonObject observation = element.getAsJsonObject();
            if (bindingId.equals(string(observation, "dynamicBindingId"))
                    && dynamicSymbol.equals(string(observation,
                    "dynamicFieldSymbol"))
                    && dynamicSymbol.equals(string(observation, "symbol"))) {
                result.add(observation);
            }
        }
        return result;
    }

    private static boolean completeDynamicFieldObservation(
            JsonObject observation, JsonObject binding) {
        if (observation == null) return false;
        String entryReadId = string(binding, "entryReadObservationId");
        return bool(observation, "available", false)
                && "AT_MATERIALIZATION".equals(string(observation, "phase"))
                && string(binding, "baseInputSymbol").equals(string(
                observation, "baseInputSymbol"))
                && string(binding, "dynamicBindingId").equals(string(
                observation, "dynamicBindingId"))
                && string(binding, "dynamicFieldSymbol").equals(string(
                observation, "dynamicFieldSymbol"))
                && string(binding, "materializationSiteId").equals(string(
                observation, "materializationSiteId"))
                && integer(binding, "materializationOccurrence", -1)
                == integer(observation, "materializationOccurrence", -2)
                && string(binding, "fieldSignature").equals(string(
                observation, "fieldSignature"))
                && array(binding, "fieldPath").equals(array(observation,
                "fieldPath"))
                && array(binding, "fieldPath").equals(array(observation,
                "path"))
                && longInteger(binding, "leafOwnerObjectToken", 0L)
                == longInteger(observation, "leafOwnerObjectToken", -1L)
                && bool(observation, "leafOwnerObjectTokenKnown", false)
                && longInteger(binding,
                "entryValueOwnerObjectToken", 0L)
                == longInteger(observation,
                "accessOwnerObjectToken", -1L)
                && bool(observation,
                "accessOwnerObjectTokenKnown", false)
                && entryReadId.equals(string(observation,
                "entryReadObservationId"))
                && arrayContainsString(array(observation,
                "entryReadObservationIds"), entryReadId)
                && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(observation, "objectTokenAuthority"))
                && string(binding, "objectTokenScope").equals(string(
                observation, "objectTokenScope"))
                && "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                .concat("FIELD_SITE_OCCURRENCE").equals(string(observation,
                "dynamicFieldBindingAuthority"))
                && bool(observation, "dynamicFieldBindingComplete", false);
    }

    private static boolean arrayContainsString(JsonArray values,
                                               String expected) {
        for (JsonElement value : values) {
            if (value.isJsonPrimitive()
                    && expected.equals(value.getAsString())) {
                return true;
            }
        }
        return false;
    }

    private static boolean validNullableKeyToken(JsonObject record) {
        boolean wasNull = bool(record, "keyWasNull", false);
        long token = longInteger(record, "keyObjectToken", -1L);
        return wasNull ? token == 0L && isNullEngineExpression(
                record.get("keyExpression")) : token > 0L;
    }

    private static boolean isNullEngineExpression(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) {
            return false;
        }
        JsonObject object = expression.getAsJsonObject();
        return "N".equals(string(object, "_exp"));
    }

    private static boolean hasNonNull(JsonObject object, String field) {
        return object.has(field) && !object.get(field).isJsonNull();
    }

    private static RuntimeHeapEffectJoin joinRuntimeHeapEffects(
            JsonArray rawPathCondition, List<HeapMutation> mutations,
            JsonElement declaredEffects,
            RuntimeHeapObservationCatalog observationCatalog) {
        if (declaredEffects == null) {
            return RuntimeHeapEffectJoin.legacy();
        }

        List<HeapEffectIssue> issues = new ArrayList<>();
        Map<Integer, RuntimeHeapProvenance> bindings = new LinkedHashMap<>();
        Set<String> associatedObservationIds = new LinkedHashSet<>();
        if (!declaredEffects.isJsonArray()) {
            issues.add(new HeapEffectIssue(
                    "MALFORMED_RUNTIME_HEAP_EFFECTS", -1,
                    "runtimeHeapEffects", "expected JSON array"));
            addMissingRuntimeProvenanceIssues(mutations, bindings, issues);
            return new RuntimeHeapEffectJoin(false, 0, 0, bindings, issues);
        }

        JsonArray records = declaredEffects.getAsJsonArray();
        Map<Integer, List<JsonObject>> removesByIndex = new LinkedHashMap<>();
        for (int ordinal = 0; ordinal < records.size(); ordinal++) {
            JsonElement element = records.get(ordinal);
            if (!element.isJsonObject()) {
                issues.add(new HeapEffectIssue(
                        "MALFORMED_RUNTIME_HEAP_EFFECT", -1,
                        "runtimeHeapEffects[" + ordinal + "]",
                        "expected JSON object"));
                continue;
            }
            JsonObject record = element.getAsJsonObject();
            if (!"MAP_REMOVE".equals(string(record, "kind"))) {
                issues.add(new HeapEffectIssue(
                        "UNSUPPORTED_RUNTIME_HEAP_EFFECT_KIND", -1,
                        "runtimeHeapEffects[" + ordinal + "]",
                        string(record, "kind")));
                continue;
            }
            int index = integer(record, "vmConditionIndex", -1);
            List<JsonObject> atIndex = removesByIndex.get(index);
            if (atIndex == null) {
                atIndex = new ArrayList<>();
                removesByIndex.put(index, atIndex);
            }
            atIndex.add(record);
        }

        for (Map.Entry<Integer, List<JsonObject>> entry
                : removesByIndex.entrySet()) {
            int index = entry.getKey();
            List<JsonObject> atIndex = entry.getValue();
            if (atIndex.size() != 1) {
                issues.add(new HeapEffectIssue(
                        "AMBIGUOUS_RUNTIME_HEAP_EFFECT_JOIN", index,
                        "runtimeHeapEffects", "MAP_REMOVE/count="
                        + atIndex.size()));
                continue;
            }
            JsonObject record = atIndex.get(0);
            if (!bool(record, "complete", false)
                    || !bool(record, "runtimeProvenanceComplete", false)
                    || !bool(record, "transformerComplete", false)
                    || !bool(record, "guardValueBindingComplete", false)
                    || !bool(record, "applied", false)
                    || !"UNIQUE_MATCH".equals(string(record,
                    "vmJoinStatus"))) {
                issues.add(new HeapEffectIssue(
                        "INCOMPLETE_RUNTIME_HEAP_EFFECT", index,
                        string(record, "siteId"), firstNonBlank(
                        string(record, "unresolvedReason"),
                        string(record, "vmJoinStatus"))));
                continue;
            }
            if (index < 0 || index >= rawPathCondition.size()) {
                issues.add(new HeapEffectIssue(
                        "RUNTIME_HEAP_EFFECT_INDEX_MISMATCH", index,
                        string(record, "siteId"), "MAP_REMOVE"));
                continue;
            }
            HeapMutation mutation = mutationAt(mutations, index);
            if (mutation == null || mutation.kind != MapMutationKind.MAP_REMOVE
                    || !"MAP_REMOVE".equals(string(record, "kind"))) {
                issues.add(new HeapEffectIssue(
                        "RUNTIME_HEAP_EFFECT_KIND_MISMATCH", index,
                        string(record, "siteId"), string(record, "kind")));
                continue;
            }
            if (!record.has("vmExpression")
                    || !rawPathCondition.get(index).equals(
                    record.get("vmExpression"))) {
                issues.add(new HeapEffectIssue(
                        "RUNTIME_HEAP_EFFECT_VM_EXPRESSION_MISMATCH", index,
                        string(record, "siteId"), "MAP_REMOVE"));
                continue;
            }
            boolean exactKeyExpression = record.has("keyExpression")
                    && mutation.keyExpression != null
                    && mutation.keyExpression.equals(
                    record.get("keyExpression"));
            boolean runtimeBoundEntryKey =
                    runtimeBoundEntryKeyJoin(record, mutation,
                            rawPathCondition, index,
                            !observationCatalog.legacy);
            if (!record.has("mapExpression")
                    || !mutation.mapExpression.equals(
                    record.get("mapExpression"))
                    || !exactKeyExpression && !runtimeBoundEntryKey) {
                issues.add(new HeapEffectIssue(
                        "RUNTIME_HEAP_EFFECT_EXPRESSION_MISMATCH", index,
                        string(record, "siteId"), "map/key"));
                continue;
            }
            String originMethod = string(record, "originMethod");
            int originUnitIndex = integer(record, "originUnitIndex", -1);
            String applicationSiteId = string(record, "siteId");
            String provenanceAuthority = string(record,
                    "provenanceAuthority");
            if (integer(record, "schemaVersion", -1) != 1
                    || !"java.util.Iterator.remove".equals(
                    string(record, "operation"))
                    || integer(record, "occurrence", 0) < 1
                    || originMethod.isEmpty() || originUnitIndex < 0
                    || applicationSiteId.isEmpty()
                    || !applicationSiteId.equals(originMethod + "#u"
                    + originUnitIndex)
                    || provenanceAuthority.isEmpty()
                    || !completeRuntimeBackedViewProvenance(record,
                    observationCatalog.legacy)) {
                issues.add(new HeapEffectIssue(
                        "INCOMPLETE_RUNTIME_HEAP_EFFECT_PROVENANCE", index,
                        applicationSiteId, originMethod));
                continue;
            }
            RuntimeHeapObservation entryRead = null;
            if (!observationCatalog.legacy
                    && "ENTRY_SET".equals(string(record, "viewKind"))) {
                entryRead = associatedEntryRead(record, observationCatalog,
                        associatedObservationIds, index, issues);
                if (entryRead == null) {
                    continue;
                }
            }
            if (runtimeBoundEntryKey && (entryRead == null
                    || !"CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT".equals(
                    string(record, "keyExpressionAuthority"))
                    || !string(record, "keyExpressionAuthority").equals(
                    string(entryRead.record,
                            "keyExpressionAuthority")))) {
                issues.add(new HeapEffectIssue(
                        "RUNTIME_ENTRY_KEY_REBIND_ASSOCIATION_MISMATCH",
                        index, string(record, "entryReadObservationId"),
                        string(record, "siteId")));
                continue;
            }
            bindings.put(index, new RuntimeHeapProvenance(record,
                    entryRead));
        }

        addMissingRuntimeProvenanceIssues(mutations, bindings, issues);
        return new RuntimeHeapEffectJoin(false, records.size(),
                bindings.size(), bindings, issues);
    }

    private static boolean runtimeBoundEntryKeyJoin(
            JsonObject record, HeapMutation mutation,
            JsonArray rawPathCondition, int index,
            boolean runtimeEntryObservationsDeclared) {
        if (!runtimeEntryObservationsDeclared
                || !"ENTRY_SET".equals(string(record, "viewKind"))
                || !"UNIQUE_HASHMAP_REMOVENODE_RECEIVER_RESULT_HASH_PLUS_"
                .concat("RUNTIME_ENTRY_KEY_V1").equals(string(record,
                "vmKeyJoinAuthority"))
                || mutation == null || mutation.keyExpression == null
                || !record.has("keyExpression")
                || !record.has("nativeKeyExpression")
                || !record.has("mapExpression")
                || !record.has("valueExpression")
                || !mutation.keyExpression.equals(
                record.get("nativeKeyExpression"))) {
            return false;
        }
        JsonElement nativeKey = record.get("nativeKeyExpression");
        if (!opaqueNativeIntegerKey(nativeKey)) {
            return false;
        }
        int start = integer(record, "rawPathConditionStart", -1);
        int end = integer(record, "rawPathConditionEnd", -1);
        if (start < 0 || start > index || index >= end
                || end > rawPathCondition.size()) {
            return false;
        }
        int receiverCandidates = 0;
        int receiverCandidateIndex = -1;
        for (int rawIndex = start; rawIndex < end; rawIndex++) {
            if (unconditionalInternalHashMapRemoveOnReceiver(
                    rawPathCondition.get(rawIndex),
                    record.get("mapExpression"))) {
                receiverCandidates++;
                receiverCandidateIndex = rawIndex;
            }
        }
        if (receiverCandidates != 1 || receiverCandidateIndex != index) {
            return false;
        }
        JsonObject expression = rawPathCondition.get(index)
                .getAsJsonObject();
        JsonArray parameters = array(expression, "_param_list");
        Integer runtimeKey = boxedIntegerConstant(
                record.get("keyExpression"));
        return parameters.size() == 5
                && parameters.get(2).equals(nativeKey)
                && runtimeKey != null
                && exactIntConstant(parameters.get(1),
                runtimeKey ^ runtimeKey >>> 16)
                && expression.has("_res_exp")
                && expression.get("_res_exp").equals(
                record.get("valueExpression"));
    }

    private static boolean unconditionalInternalHashMapRemoveOnReceiver(
            JsonElement candidate, JsonElement receiver) {
        if (candidate == null || !candidate.isJsonObject()
                || receiver == null) {
            return false;
        }
        JsonObject expression = candidate.getAsJsonObject();
        JsonArray parameters = array(expression, "_param_list");
        return "MethodExpression".equals(string(expression, "_type"))
                && "java/util/HashMap remove".equals(string(expression,
                "_name"))
                && parameters.size() == 5
                && receiver.equals(parameters.get(0))
                && isConcreteFalseBoolean(parameters.get(3))
                && isConcreteFalseBoolean(parameters.get(4));
    }

    private static boolean opaqueNativeIntegerKey(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        return "SymbolExpression".equals(string(object, "_type"))
                && "java/lang/Integer".equals(string(object, "_java_type"))
                && "P_L'java/lang/Integer'_".equals(string(object,
                "_exp"));
    }

    private static Integer boxedIntegerConstant(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject object = expression.getAsJsonObject();
        String encoded = string(object, "_exp");
        if (!"ConstExpr".equals(string(object, "_type"))
                || !"java/lang/Integer".equals(string(object,
                "_java_type")) || !encoded.startsWith("Y_I_")) {
            return null;
        }
        try {
            int value = Integer.parseInt(encoded.substring(4));
            return ("Y_I_" + value).equals(encoded) ? value : null;
        } catch (NumberFormatException malformed) {
            return null;
        }
    }

    private static boolean exactIntConstant(JsonElement expression,
                                            int expected) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        return "ConstExpr".equals(string(object, "_type"))
                && "I".equals(string(object, "_java_type"))
                && ("Y_I_" + expected).equals(string(object, "_exp"));
    }

    private static boolean completeRuntimeBackedViewProvenance(
            JsonObject record, boolean legacyObservations) {
        if (!"ENTRY_SET".equals(string(record, "viewKind"))) {
            return true;
        }
        boolean common = "JAVA_MAP_ENTRY_FROM_BOUND_ENTRY_SET_NEXT".equals(
                string(record, "entryBindingAuthority"))
                && "SAME_MAP_ENTRY_GET_KEY_AT_NEXT".equals(
                string(record, "keyBindingAuthority"))
                && "SAME_MAP_ENTRY_GET_VALUE_AT_NEXT".equals(
                string(record, "valueBindingAuthority"))
                && record.has("valueExpression")
                && !record.get("valueExpression").isJsonNull();
        if (!common) {
            return false;
        }
        if (legacyObservations) {
            return bool(record, "backingMapIdentityKnown", false)
                && bool(record, "keyIdentityKnown", false)
                && bool(record, "valueIdentityKnown", false)
                && !bool(record, "valueWasNull", true)
                && integer(record, "valueIdentity", 0) != 0;
        }
        return "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(record, "objectTokenAuthority"))
                && bool(record, "backingMapObjectTokenKnown", false)
                && longInteger(record, "backingMapObjectToken", 0L) > 0L
                && bool(record, "keyObjectTokenKnown", false)
                && validNullableKeyToken(record)
                && bool(record, "valueObjectTokenKnown", false)
                && longInteger(record, "valueObjectToken", 0L) > 0L
                && bool(record, "entryObjectTokenKnown", false)
                && longInteger(record, "entryObjectToken", 0L) > 0L
                && bool(record, "entryReadObservationComplete", false)
                && !string(record, "entryReadObservationId").isEmpty()
                && longInteger(record, "entryReadObservationSequence", 0L)
                > 0L;
    }

    private static RuntimeHeapObservation associatedEntryRead(
            JsonObject effect, RuntimeHeapObservationCatalog catalog,
            Set<String> associatedObservationIds, int rawIndex,
            List<HeapEffectIssue> issues) {
        String observationId = string(effect, "entryReadObservationId");
        RuntimeHeapObservation observation = catalog.byId.get(observationId);
        if (observation == null) {
            issues.add(new HeapEffectIssue(
                    "MISSING_RUNTIME_MAP_ENTRY_READ_ASSOCIATION", rawIndex,
                    observationId, string(effect, "siteId")));
            return null;
        }
        JsonObject read = observation.record;
        long readSequence = longInteger(read, "eventSequence", -1L);
        long effectSequence = longInteger(effect, "eventSequence", -1L);
        boolean matches = bool(effect, "entryReadObservationComplete", false)
                && longInteger(effect, "entryReadObservationSequence", -1L)
                == readSequence
                && effectSequence > readSequence
                && observation.pcBoundary <= integer(effect,
                "vmConditionIndex", -1)
                && string(effect, "originMethod").equals(string(read,
                "originMethod"))
                && string(effect, "objectTokenScope").equals(string(read,
                "objectTokenScope"))
                && effect.get("mapExpression").equals(
                read.get("mapExpression"))
                && effect.get("keyExpression").equals(
                read.get("keyExpression"))
                && effect.get("valueExpression").equals(
                read.get("valueExpression"))
                && sameValueRefWitnessMetadata(effect, read)
                && sameObjectToken(effect, read, "backingMapObjectToken")
                && sameNullableKeyToken(effect, read)
                && sameObjectToken(effect, read, "valueObjectToken")
                && sameObjectToken(effect, read, "entryObjectToken");
        if (!matches || !associatedObservationIds.add(observationId)) {
            issues.add(new HeapEffectIssue(
                    "RUNTIME_MAP_REMOVE_ENTRY_READ_ASSOCIATION_MISMATCH",
                    rawIndex, observationId, string(effect, "siteId")));
            return null;
        }
        return observation;
    }

    private static boolean sameValueRefWitnessMetadata(JsonObject effect,
                                                       JsonObject read) {
        if (!VALUE_REF_WITNESS_AUTHORITY.equals(string(read,
                "valueExpressionAuthority"))) {
            return true;
        }
        String activationId = string(read, "objectTokenScope");
        return validValueRefWitness(read, activationId)
                && validValueRefWitness(effect, activationId)
                && string(effect, "valueExpressionAuthority").equals(string(
                read, "valueExpressionAuthority"))
                && longInteger(effect,
                "valueExpressionWitnessObjectToken", 0L)
                == longInteger(read,
                "valueExpressionWitnessObjectToken", -1L)
                && string(effect,
                "valueExpressionWitnessObjectTokenScope").equals(string(read,
                "valueExpressionWitnessObjectTokenScope"));
    }

    private static boolean sameObjectToken(JsonObject left, JsonObject right,
                                           String field) {
        return longInteger(left, field, 0L) > 0L
                && longInteger(left, field, 0L)
                == longInteger(right, field, -1L);
    }

    private static boolean sameNullableKeyToken(JsonObject left,
                                                JsonObject right) {
        return validNullableKeyToken(left) && validNullableKeyToken(right)
                && bool(left, "keyWasNull", false)
                == bool(right, "keyWasNull", false)
                && longInteger(left, "keyObjectToken", -1L)
                == longInteger(right, "keyObjectToken", -2L);
    }

    private static HeapMutation mutationAt(List<HeapMutation> mutations,
                                           int rawIndex) {
        for (HeapMutation mutation : mutations) {
            if (mutation.rawIndex == rawIndex) {
                return mutation;
            }
        }
        return null;
    }

    private static void addMissingRuntimeProvenanceIssues(
            List<HeapMutation> mutations,
            Map<Integer, RuntimeHeapProvenance> bindings,
            List<HeapEffectIssue> issues) {
        for (HeapMutation mutation : mutations) {
            if (mutation.kind == MapMutationKind.MAP_REMOVE
                    && "REQUESTED_HEAP_RECEIVER_EXACT_PORT_BINDING".equals(
                    mutation.semanticAdmissionAuthority)
                    && !bindings.containsKey(mutation.rawIndex)) {
                issues.add(new HeapEffectIssue(
                        "MISSING_RUNTIME_HEAP_EFFECT_PROVENANCE",
                        mutation.rawIndex, mutation.codePosition,
                        mutation.method.qualifiedName));
            }
        }
    }

    private static HeapObservationExtraction materializeHeapObservations(
            RuntimeHeapObservationCatalog catalog, JsonArray effects,
            HeapPortResolver ports, JsonObject activation,
            JsonArray branchMappings, JsonElement fieldObservations,
            DynamicFieldBindingCatalog dynamicBindings,
            JsonArray rawPathCondition, PathNormalization normalization,
            DynamicSemanticPcFallbackCatalog dynamicPcFallbacks,
            String regionId,
            boolean nonMutatingDynamicRead) {
        if (catalog.legacy) {
            return HeapObservationExtraction.legacy(catalog);
        }
        JsonArray observations = new JsonArray();
        List<HeapEffectIssue> issues = new ArrayList<>();
        JsonObject slice = object(activation, "requestedOutputSlice");
        Map<String, List<GuardedMutationProof>> guardedMutations =
                guardedMutationProofs(slice);
        for (RuntimeHeapObservation runtime : catalog.byId.values()) {
            ObservationFieldBindings fieldBindings =
                    observationFieldBindings(runtime, activation, slice,
                            guardedMutations, branchMappings,
                            fieldObservations, dynamicBindings,
                            rawPathCondition, normalization,
                            dynamicPcFallbacks, nonMutatingDynamicRead);
            issues.addAll(fieldBindings.issues);
            ObservationStateResolution state = observationState(
                    runtime, effects, ports);
            if (!state.resolved && !state.ambiguous) {
                state = nonMutatingDynamicObservationState(runtime,
                        effects, activation, regionId, dynamicBindings,
                        fieldBindings, nonMutatingDynamicRead);
            }
            if (!state.resolved) {
                issues.add(new HeapEffectIssue(
                        state.ambiguous
                                ? "AMBIGUOUS_HEAP_OBSERVATION_STATE_PORT"
                                : "UNRESOLVED_HEAP_OBSERVATION_STATE_PORT",
                        runtime.pcBoundary, runtime.observationId,
                        string(runtime.record, "siteId")));
            }

            JsonObject observation = new JsonObject();
            observation.addProperty("schemaVersion", 1);
            observation.addProperty("kind", "MAP_ENTRY_READ");
            observation.addProperty("observationId", runtime.observationId);
            observation.addProperty("eventSequence", runtime.eventSequence);
            observation.addProperty("originMethod", string(runtime.record,
                    "originMethod"));
            observation.addProperty("originUnitIndex", integer(runtime.record,
                    "originUnitIndex", -1));
            observation.addProperty("siteId", string(runtime.record,
                    "siteId"));
            observation.addProperty("pcBoundary", runtime.pcBoundary);
            observation.addProperty("statePort", state.statePort);
            observation.addProperty("stateBindingAuthority", state.authority);
            if (!state.effectId.isEmpty()) {
                observation.addProperty("stateEffectId", state.effectId);
            }
            if (state.stateBaseProof != null) {
                observation.addProperty("stateBaseComplete", true);
                observation.add("stateBaseProof",
                        state.stateBaseProof.deepCopy());
            }
            observation.add("mapExpression", runtime.record.get(
                    "mapExpression").deepCopy());
            observation.add("keyExpression", runtime.record.get(
                    "keyExpression").deepCopy());
            observation.add("valueExpression", runtime.record.get(
                    "valueExpression").deepCopy());
            copyMapRefWitnessMetadata(runtime.record, observation);
            copyValueRefWitnessMetadata(runtime.record, observation);
            if (hasNonNull(runtime.record, "entryExpression")) {
                observation.add("entryExpression", runtime.record.get(
                        "entryExpression").deepCopy());
            }
            observation.addProperty("entryBindingAuthority", string(
                    runtime.record, "entryBindingAuthority"));
            observation.addProperty("keyBindingAuthority", string(
                    runtime.record, "keyBindingAuthority"));
            observation.addProperty("valueBindingAuthority", string(
                    runtime.record, "valueBindingAuthority"));
            observation.addProperty("objectTokenAuthority", string(
                    runtime.record, "objectTokenAuthority"));
            observation.addProperty("backingMapObjectToken", longInteger(
                    runtime.record, "backingMapObjectToken", 0L));
            observation.addProperty("keyObjectToken", longInteger(
                    runtime.record, "keyObjectToken", 0L));
            observation.addProperty("valueObjectToken", longInteger(
                    runtime.record, "valueObjectToken", 0L));
            observation.addProperty("entryObjectToken", longInteger(
                    runtime.record, "entryObjectToken", 0L));
            observation.add("entryFieldBindings",
                    fieldBindings.bindings.deepCopy());
            observation.addProperty("entryValueFieldBindingComplete",
                    fieldBindings.complete);
            observation.addProperty("complete",
                    state.resolved && fieldBindings.complete);
            observations.add(observation);
        }
        return new HeapObservationExtraction(catalog, observations, issues);
    }

    private static ObservationStateResolution observationState(
            RuntimeHeapObservation observation, JsonArray effects,
            HeapPortResolver ports) {
        JsonElement mapExpression = observation.record.get("mapExpression");
        List<JsonObject> latest = new ArrayList<>();
        int latestRawIndex = -1;
        for (JsonElement element : effects) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject effect = element.getAsJsonObject();
            int rawIndex = integer(effect, "rawConditionIndex", -1);
            if (rawIndex < 0 || rawIndex >= observation.pcBoundary
                    || !mapExpression.equals(effect.get("mapExpression"))) {
                continue;
            }
            if (rawIndex > latestRawIndex) {
                latest.clear();
                latestRawIndex = rawIndex;
            }
            if (rawIndex == latestRawIndex) {
                latest.add(effect);
            }
        }
        if (latest.size() > 1) {
            return ObservationStateResolution.ambiguous();
        }
        if (latest.size() == 1) {
            JsonObject effect = latest.get(0);
            String statePort = string(effect, "outputPort");
            return statePort.isEmpty()
                    ? ObservationStateResolution.unresolved()
                    : ObservationStateResolution.resolved(statePort,
                    "LATEST_CANONICAL_EFFECT_BEFORE_PC_BOUNDARY",
                    string(effect, "effectId"));
        }
        Set<String> inputPorts = ports.inputPortCandidates(mapExpression);
        if (inputPorts.size() > 1) {
            return ObservationStateResolution.ambiguous();
        }
        if (inputPorts.isEmpty()) {
            return ObservationStateResolution.unresolved();
        }
        return ObservationStateResolution.resolved(
                inputPorts.iterator().next(),
                "EXACT_ACTIVATION_MAP_INPUT_EXPRESSION", "");
    }

    private static ObservationStateResolution
    nonMutatingDynamicObservationState(
            RuntimeHeapObservation observation, JsonArray effects,
            JsonObject activation, String regionId,
            DynamicFieldBindingCatalog catalog,
            ObservationFieldBindings fieldBindings,
            boolean nonMutatingDynamicRead) {
        if (!nonMutatingDynamicRead || effects.size() != 0
                || !fieldBindings.complete
                || fieldBindings.bindings.size() != 1) {
            return ObservationStateResolution.unresolved();
        }
        JsonElement element = fieldBindings.bindings.get(0);
        if (!element.isJsonObject()) {
            return ObservationStateResolution.unresolved();
        }
        JsonObject binding = element.getAsJsonObject();
        String base = string(binding, "baseInputSymbol");
        String dynamicSymbol = string(binding, "dynamicFieldSymbol");
        String bindingId = string(binding, "dynamicBindingId");
        String activationId = string(activation, "activationId");
        List<RuntimeDynamicFieldBinding> candidates = catalog.forEntry(
                observation.observationId, base);
        if (base.isEmpty() || dynamicSymbol.isEmpty() || bindingId.isEmpty()
                || candidates.size() != 1
                || !NON_MUTATING_DYNAMIC_FIELD_EXPRESSION_AUTHORITY.equals(
                string(binding, "fieldExpressionAuthority"))
                || !NON_MUTATING_MAP_ENTRY_READ_STATE_AUTHORITY.equals(
                string(binding, "observationStateBindingAuthority"))
                || activationId.isEmpty()
                || !activationId.equals(string(observation.record,
                "objectTokenScope"))) {
            return ObservationStateResolution.unresolved();
        }
        RuntimeDynamicFieldBinding dynamic = candidates.get(0);
        if (!bindingId.equals(dynamic.dynamicBindingId)
                || !dynamicSymbol.equals(dynamic.dynamicFieldSymbol)
                || !activationId.equals(string(dynamic.record,
                "objectTokenScope"))
                || !bool(dynamic.record, "complete", false)) {
            return ObservationStateResolution.unresolved();
        }
        if (!validMapRefWitness(observation.record, activationId)) {
            return ObservationStateResolution.unresolved();
        }
        String selectorDigest = sha256(observation.observationId + "\n"
                + base + "\n" + bindingId);
        String statePort = regionId + ".state.heapObservation."
                + selectorDigest.substring(0, 12);
        JsonObject proof = new JsonObject();
        proof.addProperty("schemaVersion", 1);
        proof.addProperty("kind",
                "NON_MUTATING_MAP_ENTRY_READ_STATE_BASE");
        proof.addProperty("statePort", statePort);
        proof.addProperty("observationId", observation.observationId);
        proof.addProperty("entryReadObservationId",
                observation.observationId);
        proof.addProperty("regionId", regionId);
        proof.addProperty("activationId", activationId);
        proof.addProperty("baseInputSymbol", base);
        proof.addProperty("dynamicBindingId", bindingId);
        proof.addProperty("dynamicFieldSymbol", dynamicSymbol);
        proof.add("mapExpression", observation.record.get(
                "mapExpression").deepCopy());
        proof.addProperty("expressionAuthority", string(
                observation.record, "expressionAuthority"));
        proof.addProperty("backingMapObjectToken", longInteger(
                observation.record, "backingMapObjectToken", 0L));
        proof.addProperty("objectTokenScope", string(observation.record,
                "objectTokenScope"));
        proof.addProperty("mapExpressionWitnessSchemaVersion", integer(
                observation.record, "mapExpressionWitnessSchemaVersion",
                -1));
        proof.addProperty("mapExpressionWitnessKind", string(
                observation.record, "mapExpressionWitnessKind"));
        proof.addProperty("mapExpressionWitnessObjectToken", longInteger(
                observation.record, "mapExpressionWitnessObjectToken",
                0L));
        proof.addProperty("mapExpressionWitnessObjectTokenScope", string(
                observation.record,
                "mapExpressionWitnessObjectTokenScope"));
        proof.addProperty("mapExpressionWitnessAuthority", string(
                observation.record, "mapExpressionWitnessAuthority"));
        proof.addProperty("candidateMutationCount", 0);
        proof.addProperty("heapEffectCount", 0);
        proof.addProperty("associatedHeapEffectCount", 0);
        proof.addProperty("runtimeHeapEffectRecordCount", 0);
        proof.addProperty("runtimeHeapEffectJoinedCount", 0);
        proof.addProperty("ignoredRuntimeHeapEvidenceCount", 0);
        proof.addProperty("selectorDigest", selectorDigest);
        proof.addProperty("statePortDerivationAuthority",
                "REGION_AND_STATIC_OBSERVATION_SELECTOR_SHA256_V1");
        proof.addProperty("authority",
                NON_MUTATING_MAP_ENTRY_READ_STATE_AUTHORITY);
        proof.addProperty("complete", true);
        return ObservationStateResolution.resolved(statePort,
                NON_MUTATING_MAP_ENTRY_READ_STATE_AUTHORITY, "", proof);
    }

    private static ObservationFieldBindings observationFieldBindings(
            RuntimeHeapObservation observation, JsonObject activation,
            JsonObject slice,
            Map<String, List<GuardedMutationProof>> guardedMutations,
            JsonArray branchMappings, JsonElement fieldObservations,
            DynamicFieldBindingCatalog dynamicBindings,
            JsonArray rawPathCondition, PathNormalization normalization,
            DynamicSemanticPcFallbackCatalog dynamicPcFallbacks,
            boolean nonMutatingDynamicRead) {
        List<HeapEffectIssue> issues = new ArrayList<>();
        JsonArray bindings = new JsonArray();
        Set<String> guardSites = new LinkedHashSet<>();
        String method = string(observation.record, "originMethod");
        for (List<GuardedMutationProof> proofs : guardedMutations.values()) {
            for (GuardedMutationProof proof : proofs) {
                if (method.equals(proof.method)) {
                    guardSites.add(proof.guardSiteId);
                }
            }
        }

        Set<String> expressionSymbols = new LinkedHashSet<>();
        int guardMappingCount = 0;
        for (JsonElement element : branchMappings) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject mapping = element.getAsJsonObject();
            if (!guardSites.contains(string(mapping, "siteId"))) {
                continue;
            }
            guardMappingCount++;
            JsonElement condition = mapping.has("condition")
                    ? mapping.get("condition") : mapping.get("rawCondition");
            HeapPortResolver.collectExpressionSymbols(condition,
                    expressionSymbols);
        }
        if (!guardSites.isEmpty() && guardMappingCount == 0) {
            issues.add(new HeapEffectIssue(
                    "MISSING_RUNTIME_MAP_ENTRY_READ_GUARD_OBSERVATION",
                    observation.pcBoundary, observation.observationId,
                    method));
        }

        if (!dynamicBindings.legacy) {
            return dynamicObservationFieldBindings(observation, activation,
                    expressionSymbols, branchMappings, dynamicBindings,
                    issues, guardSites, rawPathCondition, normalization,
                    dynamicPcFallbacks, nonMutatingDynamicRead);
        }

        Set<String> requestedInputs = new LinkedHashSet<>();
        for (JsonElement element : array(slice, "inputPorts")) {
            if (element.isJsonPrimitive()) {
                requestedInputs.add(element.getAsString());
            }
        }
        Map<String, JsonObject> actions = new LinkedHashMap<>();
        Set<String> duplicates = new LinkedHashSet<>();
        for (JsonElement element : runtimeMaterializationActions(
                activation)) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject action = element.getAsJsonObject();
            String symbol = string(action, "symbol");
            if (!"FIELD_ACCESS".equals(string(action, "bindingMode"))
                    || symbol.isEmpty() || !requestedInputs.contains(symbol)
                    || array(action, "fieldPath").size() == 0
                    || !referencesAnySymbol(expressionSymbols, symbol)) {
                continue;
            }
            if (actions.put(symbol, action) != null) {
                duplicates.add(symbol);
            }
        }

        long valueToken = longInteger(observation.record,
                "valueObjectToken", 0L);
        for (Map.Entry<String, JsonObject> entry : actions.entrySet()) {
            String symbol = entry.getKey();
            JsonObject action = entry.getValue();
            if (duplicates.contains(symbol)) {
                issues.add(new HeapEffectIssue(
                        "AMBIGUOUS_MAP_ENTRY_READ_FIELD_ACTION",
                        observation.pcBoundary, symbol,
                        observation.observationId));
                continue;
            }
            List<JsonObject> candidates = observationsForSymbol(
                    fieldObservations, symbol);
            if (candidates.size() != 1) {
                issues.add(new HeapEffectIssue(candidates.isEmpty()
                        ? "MISSING_MAP_ENTRY_READ_FIELD_OBSERVATION"
                        : "AMBIGUOUS_MAP_ENTRY_READ_FIELD_OBSERVATION",
                        observation.pcBoundary, symbol,
                        observation.observationId));
                continue;
            }
            JsonObject field = candidates.get(0);
            String fieldSignature = firstNonBlank(string(action, "field"),
                    string(action, "cell"));
            String fieldType = fieldJavaType(fieldSignature);
            boolean structureComplete = bool(field, "available", false)
                    && "AT_MATERIALIZATION".equals(string(field, "phase"))
                    && array(action, "fieldPath").equals(array(field, "path"))
                    && !fieldSignature.isEmpty() && !fieldType.isEmpty()
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                    string(field, "objectTokenAuthority"))
                    && string(observation.record, "objectTokenScope").equals(
                    string(field, "objectTokenScope"))
                    && bool(field, "leafOwnerObjectTokenKnown", false);
            if (!structureComplete) {
                issues.add(new HeapEffectIssue(
                        "INCOMPLETE_MAP_ENTRY_READ_FIELD_OBSERVATION",
                        observation.pcBoundary, symbol,
                        observation.observationId));
                continue;
            }
            long ownerToken = longInteger(field, "leafOwnerObjectToken", 0L);
            if (valueToken <= 0L || ownerToken != valueToken) {
                issues.add(new HeapEffectIssue(
                        "MAP_ENTRY_READ_FIELD_OWNER_TOKEN_MISMATCH",
                        observation.pcBoundary, symbol,
                        observation.observationId));
                continue;
            }
            JsonObject binding = new JsonObject();
            binding.addProperty("fieldSymbol", symbol);
            binding.addProperty("fieldSignature", fieldSignature);
            binding.addProperty("fieldJavaType", fieldType);
            binding.add("fieldPath", array(field, "path").deepCopy());
            binding.addProperty("authority",
                    "ACTIVATION_LOCAL_OBJECT_TOKEN_EQUALS_ENTRY_VALUE");
            bindings.add(binding);
        }
        return new ObservationFieldBindings(bindings, issues.isEmpty(),
                issues);
    }

    private static ObservationFieldBindings dynamicObservationFieldBindings(
            RuntimeHeapObservation observation, JsonObject activation,
            Set<String> guardExpressionSymbols, JsonArray branchMappings,
            DynamicFieldBindingCatalog catalog,
            List<HeapEffectIssue> inheritedIssues, Set<String> guardSites,
            JsonArray rawPathCondition, PathNormalization normalization,
            DynamicSemanticPcFallbackCatalog dynamicPcFallbacks,
            boolean nonMutatingDynamicRead) {
        List<HeapEffectIssue> issues = new ArrayList<>(inheritedIssues);
        JsonArray bindings = new JsonArray();
        if (nonMutatingDynamicRead && guardSites.isEmpty()) {
            return nonMutatingDynamicObservationFieldBindings(observation,
                    activation, branchMappings, catalog, issues,
                    rawPathCondition, normalization);
        }
        Set<String> requestedInputs = new LinkedHashSet<>();
        JsonObject slice = object(activation, "requestedOutputSlice");
        for (JsonElement element : array(slice, "inputPorts")) {
            if (element.isJsonPrimitive()) {
                requestedInputs.add(element.getAsString());
            }
        }

        Map<String, JsonObject> expectedActions = new LinkedHashMap<>();
        Set<String> duplicateActions = new LinkedHashSet<>();
        for (JsonElement element : runtimeMaterializationActions(
                activation)) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            String base = string(action, "symbol");
            if (!"FIELD_ACCESS".equals(string(action, "bindingMode"))
                    || base.isEmpty() || !requestedInputs.contains(base)
                    || array(action, "fieldPath").size() == 0
                    || !referencesAnySymbol(guardExpressionSymbols, base)
                    && !dynamicPcFallbacks.hasBase(base)) {
                continue;
            }
            if (expectedActions.put(base, action) != null) {
                duplicateActions.add(base);
            }
        }

        for (Map.Entry<String, JsonObject> entry : expectedActions.entrySet()) {
            String base = entry.getKey();
            if (duplicateActions.contains(base)) {
                issues.add(new HeapEffectIssue(
                        "AMBIGUOUS_MAP_ENTRY_READ_FIELD_ACTION",
                        observation.pcBoundary, base,
                        observation.observationId));
                continue;
            }
            List<RuntimeDynamicFieldBinding> candidates = catalog.forEntry(
                    observation.observationId, base);
            if (candidates.size() != 1) {
                issues.add(new HeapEffectIssue(candidates.isEmpty()
                        ? "MISSING_MAP_ENTRY_READ_DYNAMIC_FIELD_BINDING"
                        : "AMBIGUOUS_MAP_ENTRY_READ_DYNAMIC_FIELD_BINDING",
                        observation.pcBoundary, base,
                        observation.observationId));
                continue;
            }
            RuntimeDynamicFieldBinding dynamic = candidates.get(0);
            List<JsonObject> expressions = exactGuardSymbolExpressions(
                    branchMappings, guardExpressionSymbols,
                    dynamic.dynamicFieldSymbol);
            DynamicSemanticPcFallback fallback = expressions.isEmpty()
                    ? dynamicPcFallbacks.byDynamicSymbol.get(
                    dynamic.dynamicFieldSymbol) : null;
            boolean exactFallback = fallback != null
                    && fallback.entryReadObservationId.equals(
                    observation.observationId)
                    && guardSites.contains(fallback.branchSiteId)
                    && fallback.rawIndex >= 0
                    && fallback.rawIndex < rawPathCondition.size()
                    && normalization.isSemantic(fallback.rawIndex)
                    && GSON.toJson(rawPathCondition.get(fallback.rawIndex))
                    .equals(GSON.toJson(fallback.rawCondition));
            if (expressions.size() != 1 && !exactFallback) {
                issues.add(new HeapEffectIssue(expressions.size() > 1
                        ? "AMBIGUOUS_DYNAMIC_FIELD_EXPRESSION"
                        : "MISSING_DYNAMIC_FIELD_EXPRESSION",
                        observation.pcBoundary, dynamic.dynamicBindingId,
                        observation.observationId));
                continue;
            }
            JsonObject expression = expressions.size() == 1
                    ? expressions.get(0) : fallback.fieldExpression;
            String fieldType = fieldJavaType(dynamic.fieldSignature);
            if (fieldType.isEmpty()) {
                issues.add(new HeapEffectIssue(
                        "INCOMPLETE_DYNAMIC_FIELD_TYPE",
                        observation.pcBoundary, dynamic.dynamicBindingId,
                        dynamic.fieldSignature));
                continue;
            }
            JsonObject binding = new JsonObject();
            binding.addProperty("schemaVersion", 1);
            binding.addProperty("kind",
                    "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
            binding.addProperty("dynamicBindingId",
                    dynamic.dynamicBindingId);
            binding.addProperty("baseInputSymbol", base);
            binding.addProperty("dynamicFieldSymbol",
                    dynamic.dynamicFieldSymbol);
            binding.add("fieldExpression", expression.deepCopy());
            binding.addProperty("fieldSignature", dynamic.fieldSignature);
            binding.addProperty("fieldJavaType", fieldType);
            binding.add("fieldPath", array(dynamic.record,
                    "fieldPath").deepCopy());
            binding.addProperty("materializationSiteId",
                    string(dynamic.record, "materializationSiteId"));
            binding.addProperty("materializationOccurrence", integer(
                    dynamic.record, "materializationOccurrence", -1));
            binding.addProperty("entryReadObservationId",
                    observation.observationId);
            binding.add("keyExpression", dynamic.record.get(
                    "keyExpression").deepCopy());
            binding.addProperty("keyExpressionAuthority", string(
                    dynamic.record, "keyExpressionAuthority"));
            binding.addProperty("baseInputRole",
                    "FIELD_FAMILY_TEMPLATE_ONLY");
            binding.addProperty("authority",
                    "RUNTIME_DYNAMIC_FIELD_INSTANCE_EXACT_EXPRESSION_AND_"
                            + "ENTRY_VALUE_TOKEN_JOIN");
            if (exactFallback) {
                binding.addProperty("fieldExpressionAuthority",
                        "EXACT_SEMANTIC_RAW_PC_DYNAMIC_SYMBOL_FALLBACK");
                binding.addProperty("fieldExpressionRawConditionIndex",
                        fallback.rawIndex);
                binding.addProperty(
                        "fieldExpressionNormalizedConditionIndex",
                        normalization.index(fallback.rawIndex));
                binding.addProperty("fieldExpressionCodePosition",
                        fallback.codePosition);
                binding.addProperty("fieldExpressionFallbackAuthority",
                        fallback.authority);
            } else {
                binding.addProperty("fieldExpressionAuthority",
                        "EXACT_BRANCH_MAPPING_DYNAMIC_SYMBOL");
            }
            bindings.add(binding);
        }
        return new ObservationFieldBindings(bindings,
                issues.isEmpty() && bindings.size() == expectedActions.size()
                        && bindings.size() > 0,
                issues);
    }

    /**
     * A read-only producer has no map mutation guard from which to discover
     * the dynamic entry field.  Admit that field only from the independent
     * exact witnesses already present in the activation and VM result.  This
     * path is deliberately disjoint from guarded-mutation materialization.
     */
    private static ObservationFieldBindings
    nonMutatingDynamicObservationFieldBindings(
            RuntimeHeapObservation observation, JsonObject activation,
            JsonArray branchMappings, DynamicFieldBindingCatalog catalog,
            List<HeapEffectIssue> inheritedIssues,
            JsonArray rawPathCondition, PathNormalization normalization) {
        List<HeapEffectIssue> issues = new ArrayList<>(inheritedIssues);
        JsonArray bindings = new JsonArray();
        List<RuntimeDynamicFieldBinding> dynamicCandidates =
                catalog.forObservation(observation.observationId);
        if (dynamicCandidates.size() != 1) {
            issues.add(new HeapEffectIssue(dynamicCandidates.isEmpty()
                    ? "MISSING_MAP_ENTRY_READ_DYNAMIC_FIELD_BINDING"
                    : "AMBIGUOUS_MAP_ENTRY_READ_DYNAMIC_FIELD_BINDING",
                    observation.pcBoundary, observation.observationId,
                    "NON_MUTATING_MAP_ENTRY_READ"));
            return new ObservationFieldBindings(bindings, false, issues);
        }
        RuntimeDynamicFieldBinding dynamic = dynamicCandidates.get(0);
        List<JsonObject> actions = new ArrayList<>();
        for (JsonElement element : runtimeMaterializationActions(
                activation)) {
            if (element.isJsonObject() && dynamic.baseInputSymbol.equals(
                    string(element.getAsJsonObject(), "symbol"))) {
                actions.add(element.getAsJsonObject());
            }
        }
        if (actions.size() != 1) {
            issues.add(new HeapEffectIssue(actions.isEmpty()
                    ? "MISSING_MAP_ENTRY_READ_FIELD_ACTION"
                    : "AMBIGUOUS_MAP_ENTRY_READ_FIELD_ACTION",
                    observation.pcBoundary, dynamic.baseInputSymbol,
                    observation.observationId));
            return new ObservationFieldBindings(bindings, false, issues);
        }
        JsonObject action = actions.get(0);
        if (!exactRequestedNonMutatingFieldBase(activation, action,
                dynamic)) {
            issues.add(new HeapEffectIssue(
                    "INCOMPLETE_NON_MUTATING_MAP_ENTRY_READ_FIELD_BASE",
                    observation.pcBoundary, dynamic.baseInputSymbol,
                    observation.observationId));
            return new ObservationFieldBindings(bindings, false, issues);
        }
        List<JsonObject> expressions =
                exactNonMutatingDynamicBranchExpressions(branchMappings,
                        rawPathCondition, normalization, activation, action,
                        dynamic);
        if (expressions.size() != 1) {
            issues.add(new HeapEffectIssue(expressions.size() > 1
                    ? "AMBIGUOUS_DYNAMIC_FIELD_EXPRESSION"
                    : "MISSING_DYNAMIC_FIELD_EXPRESSION",
                    observation.pcBoundary, dynamic.dynamicBindingId,
                    observation.observationId));
            return new ObservationFieldBindings(bindings, false, issues);
        }
        String fieldType = fieldJavaType(dynamic.fieldSignature);
        if (fieldType.isEmpty()) {
            issues.add(new HeapEffectIssue("INCOMPLETE_DYNAMIC_FIELD_TYPE",
                    observation.pcBoundary, dynamic.dynamicBindingId,
                    dynamic.fieldSignature));
            return new ObservationFieldBindings(bindings, false, issues);
        }

        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("dynamicBindingId", dynamic.dynamicBindingId);
        binding.addProperty("baseInputSymbol", dynamic.baseInputSymbol);
        binding.addProperty("dynamicFieldSymbol", dynamic.dynamicFieldSymbol);
        binding.add("fieldExpression", expressions.get(0).deepCopy());
        binding.addProperty("fieldExpressionAuthority",
                NON_MUTATING_DYNAMIC_FIELD_EXPRESSION_AUTHORITY);
        binding.addProperty("fieldSignature", dynamic.fieldSignature);
        binding.addProperty("fieldJavaType", fieldType);
        binding.add("fieldPath", array(dynamic.record,
                "fieldPath").deepCopy());
        binding.addProperty("materializationSiteId", string(dynamic.record,
                "materializationSiteId"));
        binding.addProperty("materializationOccurrence", integer(
                dynamic.record, "materializationOccurrence", -1));
        binding.addProperty("entryReadObservationId",
                observation.observationId);
        binding.add("keyExpression", dynamic.record.get(
                "keyExpression").deepCopy());
        binding.addProperty("keyExpressionAuthority", string(
                dynamic.record, "keyExpressionAuthority"));
        binding.addProperty("baseInputRole", "FIELD_FAMILY_TEMPLATE_ONLY");
        binding.addProperty("authority",
                "RUNTIME_DYNAMIC_FIELD_INSTANCE_EXACT_EXPRESSION_AND_"
                        + "ENTRY_VALUE_TOKEN_JOIN");
        binding.addProperty("observationStateBindingAuthority",
                NON_MUTATING_MAP_ENTRY_READ_STATE_AUTHORITY);
        bindings.add(binding);
        return new ObservationFieldBindings(bindings, issues.isEmpty(),
                issues);
    }

    private static boolean exactRequestedNonMutatingFieldBase(
            JsonObject activation, JsonObject action,
            RuntimeDynamicFieldBinding dynamic) {
        JsonObject slice = object(activation, "requestedOutputSlice");
        String base = dynamic.baseInputSymbol;
        String cell = string(action, "cell");
        String accessMethod = string(action, "accessMethod");
        JsonArray fieldPath = array(action, "fieldPath");
        List<String> projectedPath = new ArrayList<>();
        String projectedBase = projectedBaseCell(cell);
        String baseField = declaredFieldName(projectedBase);
        if (!baseField.isEmpty()) projectedPath.add(baseField);
        projectedPath.addAll(projectedFieldPath(cell));
        if (!bool(activation, "requestedOutputSliceComplete", false)
                || !bool(slice, "complete", false)
                || !bool(slice, "structuralComplete", false)
                || bool(slice, "truncated", true)
                || countString(slice.get("inputPorts"), base) != 1
                || countString(slice.get("methods"), accessMethod) != 1
                || !"FIELD_ACCESS".equals(string(action, "bindingMode"))
                || !"HEAP_OBJECT_FIELD".equals(string(action, "location"))
                || !"STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1".equals(
                string(action, "fieldPathAuthority"))
                || base.isEmpty() || cell.isEmpty() || accessMethod.isEmpty()
                || fieldPath.size() < 2
                || projectedPath.size() != fieldPath.size()
                || !dynamic.fieldSignature.equals(firstNonBlank(
                string(action, "leafFieldSignature"),
                string(action, "field")))) {
            return false;
        }
        for (int index = 0; index < fieldPath.size(); index++) {
            if (!fieldPath.get(index).isJsonPrimitive()
                    || !projectedPath.get(index).equals(
                    fieldPath.get(index).getAsString())) {
                return false;
            }
        }
        List<JsonObject> bindings = new ArrayList<>();
        for (JsonElement element : array(slice, "inputBindings")) {
            if (element.isJsonObject() && base.equals(string(
                    element.getAsJsonObject(), "inputPort"))) {
                bindings.add(element.getAsJsonObject());
            }
        }
        if (bindings.size() != 1) {
            return false;
        }
        JsonObject binding = bindings.get(0);
        return cell.equals(string(binding, "dependencyCell"))
                && "EXACT_CELL_IDENTITY".equals(string(binding,
                "bindingAuthority"))
                && countString(binding.get("dependencyMethods"),
                accessMethod) == 1;
    }

    private static List<JsonObject> exactNonMutatingDynamicBranchExpressions(
            JsonArray branchMappings, JsonArray rawPathCondition,
            PathNormalization normalization, JsonObject activation,
            JsonObject action, RuntimeDynamicFieldBinding dynamic) {
        List<JsonObject> result = new ArrayList<>();
        String descriptor = javaTypeDescriptor(fieldJavaType(
                dynamic.fieldSignature));
        String owner = declaredFieldOwner(dynamic.fieldSignature);
        if (descriptor.length() != 1
                || "ZCBSIFJDL".indexOf(descriptor.charAt(0)) < 0
                || owner.isEmpty()) {
            return result;
        }
        String expectedEngineSymbol = "M_" + descriptor + "_field_"
                + dynamic.dynamicFieldSymbol + "_"
                + owner.replace('.', '/');
        for (JsonElement element : branchMappings) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            DynamicBranchExpressionScan scan =
                    new DynamicBranchExpressionScan();
            collectNonMutatingDynamicExpressions(mapping.get("condition"),
                    dynamic.dynamicFieldSymbol, expectedEngineSymbol,
                    descriptor, scan);
            if (scan.referenceCount == 0) continue;
            if (scan.invalid || scan.referenceCount != 1
                    || scan.expression == null
                    || !exactNonMutatingBranchMapping(mapping,
                    rawPathCondition, normalization, activation, action)) {
                return Collections.emptyList();
            }
            result.add(scan.expression);
        }
        return result;
    }

    private static boolean exactNonMutatingBranchMapping(
            JsonObject mapping, JsonArray rawPathCondition,
            PathNormalization normalization, JsonObject activation,
            JsonObject action) {
        int rawIndex = integer(mapping, "rawConditionIndex", -1);
        int conditionIndex = integer(mapping, "conditionIndex", -1);
        int engineIndex = integer(mapping, "engineConditionIndex", rawIndex);
        int baseline = integer(mapping, "rawPathConditionBaseline", -1);
        int boundary = integer(mapping, "rawPathConditionSize", -1);
        int occurrence = integer(mapping, "occurrence", -1);
        int unitIndex = integer(mapping, "unitIndex", -1);
        String method = string(mapping, "method");
        JsonElement rawCondition = mapping.get("rawCondition");
        JsonElement condition = mapping.get("condition");
        int normalizedIndex = normalization.index(rawIndex);
        return rawIndex >= 0 && rawIndex < rawPathCondition.size()
                && conditionIndex == rawIndex && engineIndex == rawIndex
                && normalization.isSemantic(rawIndex)
                && normalizedIndex >= 0
                && normalizedIndex < normalization.conditions.size()
                && rawCondition != null && condition != null
                && GSON.toJson(rawPathCondition.get(rawIndex)).equals(
                GSON.toJson(rawCondition))
                && GSON.toJson(normalization.conditions.get(normalizedIndex))
                .equals(GSON.toJson(condition))
                && validSemanticBranchCondition(mapping, rawCondition,
                condition)
                && method.equals(string(action, "accessMethod"))
                && countString(object(activation,
                "requestedOutputSlice").get("methods"), method) == 1
                && unitIndex >= 0
                && string(mapping, "siteId").equals(method + "#u"
                + unitIndex)
                && occurrence > 0
                && occurrence == integer(mapping, "vmOccurrence", -1)
                && integer(mapping, "vmBranchEventId", 0) > 0
                && longInteger(mapping, "vmThreadContextId", 0L) > 0L
                && longInteger(mapping, "vmOwnerJavaThreadId", 0L) > 0L
                && longInteger(mapping, "vmOwnerOsThreadId", 0L) > 0L
                && bool(mapping, "vmBranchEventExpected", false)
                && bool(mapping, "vmBranchEventValidated", false)
                && "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1".equals(
                string(mapping, "vmBranchEventAuthority"))
                && "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_PC_INDEX"
                .equals(string(mapping, "mappingPolicy"))
                && "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_PC_INDEX".equals(
                string(mapping, "conditionAuthority"))
                && !bool(mapping, "overrideApplied", true)
                && "NONE".equals(string(mapping, "overrideMode"))
                && bool(mapping, "outcome", false) == bool(mapping,
                "observedOutcome", !bool(mapping, "outcome", false))
                && bool(mapping, "outcome", false) == bool(mapping,
                "effectiveOutcome", !bool(mapping, "outcome", false))
                && baseline >= 0 && boundary > baseline
                && rawIndex >= baseline && rawIndex < boundary
                && containsInteger(array(mapping, "vmConditionIndices"),
                rawIndex);
    }

    private static void collectNonMutatingDynamicExpressions(
            JsonElement expression, String dynamicFieldSymbol,
            String expectedEngineSymbol, String descriptor,
            DynamicBranchExpressionScan scan) {
        if (expression == null || expression.isJsonNull()) return;
        if (expression.isJsonArray()) {
            for (JsonElement item : expression.getAsJsonArray()) {
                collectNonMutatingDynamicExpressions(item,
                        dynamicFieldSymbol, expectedEngineSymbol,
                        descriptor, scan);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject object = expression.getAsJsonObject();
        String raw = string(object, "_exp");
        if (("SymbolExpression".equals(string(object, "_type"))
                || "ConSymbolExp".equals(string(object, "_type")))
                && HeapPortResolver.containsSymbolReference(raw,
                dynamicFieldSymbol)) {
            scan.referenceCount++;
            if (!expectedEngineSymbol.equals(raw)
                    || !descriptor.equals(string(object, "_java_type"))
                    || scan.expression != null) {
                scan.invalid = true;
            } else {
                scan.expression = object.deepCopy();
            }
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            if (!"_exp".equals(entry.getKey())
                    && !"_code_position".equals(entry.getKey())) {
                collectNonMutatingDynamicExpressions(entry.getValue(),
                        dynamicFieldSymbol, expectedEngineSymbol,
                        descriptor, scan);
            }
        }
    }

    private static List<JsonObject> exactGuardSymbolExpressions(
            JsonArray branchMappings, Set<String> admittedRawSymbols,
            String dynamicFieldSymbol) {
        Map<String, JsonObject> unique = new LinkedHashMap<>();
        for (JsonElement element : branchMappings) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            JsonElement condition = mapping.has("condition")
                    ? mapping.get("condition") : mapping.get("rawCondition");
            collectExactSymbolExpressions(condition, admittedRawSymbols,
                    dynamicFieldSymbol, unique);
        }
        return new ArrayList<>(unique.values());
    }

    private static void collectExactSymbolExpressions(
            JsonElement expression, Set<String> admittedRawSymbols,
            String dynamicFieldSymbol, Map<String, JsonObject> result) {
        if (expression == null || expression.isJsonNull()) return;
        if (expression.isJsonArray()) {
            for (JsonElement item : expression.getAsJsonArray()) {
                collectExactSymbolExpressions(item, admittedRawSymbols,
                        dynamicFieldSymbol, result);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject object = expression.getAsJsonObject();
        String raw = string(object, "_exp");
        if (("SymbolExpression".equals(string(object, "_type"))
                || "ConSymbolExp".equals(string(object, "_type")))
                && admittedRawSymbols.contains(raw)
                && HeapPortResolver.containsSymbolReference(raw,
                dynamicFieldSymbol)) {
            result.put(GSON.toJson(object), object.deepCopy());
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            if (!"_exp".equals(entry.getKey())
                    && !"_code_position".equals(entry.getKey())) {
                collectExactSymbolExpressions(entry.getValue(),
                        admittedRawSymbols, dynamicFieldSymbol, result);
            }
        }
    }

    private static List<JsonObject> observationsForSymbol(
            JsonElement fieldObservations, String symbol) {
        List<JsonObject> result = new ArrayList<>();
        if (fieldObservations == null || !fieldObservations.isJsonArray()) {
            return result;
        }
        for (JsonElement element : fieldObservations.getAsJsonArray()) {
            if (element.isJsonObject() && symbol.equals(string(
                    element.getAsJsonObject(), "symbol"))) {
                result.add(element.getAsJsonObject());
            }
        }
        return result;
    }

    private static String fieldJavaType(String fieldSignature) {
        if (fieldSignature == null) {
            return "";
        }
        String value = fieldSignature.trim();
        int colon = value.indexOf(':');
        int end = value.lastIndexOf('>');
        if (!value.startsWith("<") || colon < 0 || end <= colon) {
            return "";
        }
        String declaration = value.substring(colon + 1, end).trim();
        int separator = declaration.indexOf(' ');
        return separator <= 0 ? "" : declaration.substring(0, separator);
    }

    private static List<HeapEffectIssue> associateHeapObservationsWithEffects(
            JsonArray effects, HeapObservationExtraction extraction) {
        List<HeapEffectIssue> issues = new ArrayList<>();
        Map<String, JsonObject> byId = new LinkedHashMap<>();
        for (JsonElement element : extraction.observations) {
            if (element.isJsonObject()) {
                JsonObject observation = element.getAsJsonObject();
                byId.put(string(observation, "observationId"), observation);
            }
        }
        for (JsonElement element : effects) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject effect = element.getAsJsonObject();
            String observationId = string(effect, "entryReadObservationId");
            if (observationId.isEmpty()) {
                continue;
            }
            JsonObject observation = byId.get(observationId);
            if (observation == null) {
                issues.add(new HeapEffectIssue(
                        "MISSING_IMPORTED_MAP_ENTRY_READ_ASSOCIATION",
                        integer(effect, "rawConditionIndex", -1),
                        observationId, string(effect, "applicationSiteId")));
                continue;
            }
            effect.addProperty("heapObservationId", observationId);
            effect.addProperty("entryReadStatePort", string(observation,
                    "statePort"));
            effect.add("entryFieldBindings", array(observation,
                    "entryFieldBindings").deepCopy());
            boolean complete = bool(observation,
                    "entryValueFieldBindingComplete", false)
                    && bool(observation, "complete", false);
            effect.addProperty("entryValueFieldBindingComplete", complete);
            if (!complete) {
                issues.add(new HeapEffectIssue(
                        "INCOMPLETE_ASSOCIATED_MAP_ENTRY_READ",
                        integer(effect, "rawConditionIndex", -1),
                        observationId, string(effect, "applicationSiteId")));
            }
        }
        return issues;
    }

    private static int addGuardedMapIdentityEffect(
            List<HeapMutation> mutations,
            HeapObservationExtraction observations,
            StaticHeapTransformerCoverage coverage, JsonArray effects,
            Map<String, HeapOutputBinding> outputBindings,
            HeapPortResolver ports, JsonObject activation, String regionId,
            int effectOrdinal, List<HeapEffectIssue> issues) {
        String requestedCell = string(object(activation,
                "requestedOutput"), "cell");
        if (!supportedMapStateField(requestedCell)) {
            return 0;
        }
        if (!mutations.isEmpty()) {
            return 0;
        }
        if (!coverage.allWritesGuardExcluded()) {
            if (!observations.catalog.legacy) {
                issues.add(new HeapEffectIssue(
                        "UNPROVEN_GUARDED_MAP_IDENTITY", -1,
                        string(object(activation, "requestedOutput"),
                                "portId"),
                        "all requested-state writes must be guard-excluded"));
            }
            return 0;
        }
        if (!observations.complete() || observations.observations.size() == 0) {
            if (observations.issues.isEmpty()) {
                issues.add(new HeapEffectIssue(
                        "MISSING_MAP_ENTRY_READ_FOR_GUARDED_MAP_IDENTITY", -1,
                        string(object(activation, "requestedOutput"), "portId"),
                        "runtimeHeapObservations"));
            }
            return 0;
        }
        JsonElement mapExpression = null;
        String inputPort = "";
        boolean ambiguous = false;
        for (JsonElement element : observations.observations) {
            JsonObject observation = element.getAsJsonObject();
            JsonElement candidateMap = observation.get("mapExpression");
            String candidatePort = string(observation, "statePort");
            if (mapExpression == null) {
                mapExpression = candidateMap;
                inputPort = candidatePort;
            } else if (!mapExpression.equals(candidateMap)
                    || !inputPort.equals(candidatePort)) {
                ambiguous = true;
                break;
            }
        }
        String exactInput = mapExpression == null ? ""
                : ports.inputPort(mapExpression);
        String outputPort = ports.outputPort(inputPort);
        String requestedPort = firstNonBlank(string(object(activation,
                "requestedOutput"), "portId"), string(object(activation,
                "requestedOutput"), "symbol"));
        if (ambiguous || inputPort.isEmpty() || !inputPort.equals(exactInput)
                || outputPort.isEmpty() || !outputPort.equals(requestedPort)) {
            issues.add(new HeapEffectIssue(
                    ambiguous ? "AMBIGUOUS_GUARDED_MAP_IDENTITY_STATE"
                            : "UNRESOLVED_GUARDED_MAP_IDENTITY_STATE", -1,
                    inputPort, requestedPort));
            return 0;
        }

        String effectId = "HEAP_EFFECT." + regionId + "." + effectOrdinal;
        String stateFamily = "MAP_STATE." + regionId + ".0";
        JsonObject identity = new JsonObject();
        identity.addProperty("effectId", effectId);
        identity.addProperty("kind", "MAP_IDENTITY");
        identity.addProperty("rawConditionIndex", -1);
        identity.addProperty("normalizedConditionIndex", -1);
        identity.addProperty("normalizationStatus",
                "RUNTIME_GUARD_EXCLUDED_ALL_STATIC_WRITES");
        identity.addProperty("siteId", "MAP_IDENTITY." + regionId);
        identity.addProperty("occurrence", 1);
        identity.addProperty("provenanceAuthority",
                "RUNTIME_OBSERVED_DOMINATING_GUARDS_EXCLUDE_ALL_WRITES");
        identity.addProperty("stateFamily", stateFamily);
        identity.addProperty("preState", stateFamily + ".0");
        identity.addProperty("postState", stateFamily + ".1");
        identity.addProperty("stateOrdinalBefore", 0);
        identity.addProperty("stateOrdinalAfter", 1);
        identity.addProperty("inputPort", inputPort);
        identity.addProperty("outputPort", outputPort);
        identity.addProperty("inputBinding", "ACTIVATION_SYMBOL");
        identity.addProperty("outputBinding", "ACTIVATION_HEAP_OUTPUT");
        identity.add("mapExpression", mapExpression.deepCopy());
        identity.addProperty("identityAuthority",
                "RUNTIME_OBSERVED_DOMINATING_GUARD_EXCLUDES_WRITE");
        effects.add(identity);
        outputBindings.put(outputPort, new HeapOutputBinding(
                stateFamily + ".1", stateFamily, effectId, outputPort));
        return 1;
    }

    /**
     * Treats a complete requested-output heap slice as a contract, rather
     * than accepting the set of mutations emitted by the VM as self-proving.
     *
     * <p>Schema-v1 slices declare the exact HEAP_WRITE sites whose target cell
     * is the requested heap output.  Other heap writes can be causal
     * prerequisites without transforming that output, and a void helper is
     * not an obligation merely because it appears in the slice method list.
     * Historical slices retain the older conservative policy and are never
     * silently upgraded to the exact-contract authority.</p>
     */
    private static StaticHeapTransformerCoverage staticHeapTransformerCoverage(
            JsonObject activation, JsonArray effects,
            boolean legacyRuntimeHeapEffects,
            boolean legacyRuntimeHeapObservations,
            JsonArray rawBranchMappings,
            JsonElement fieldObservations,
            OutputExpressionExtraction fieldAssignmentCapture,
            JsonArray rawPathCondition, PathNormalization normalization,
            JsonArray dynamicFieldBindings,
            JsonArray engineArrayInputBindings) {
        RegionCaptureGoal goal = RegionCaptureGoal.from(activation);
        JsonObject requestedOutput = object(activation, "requestedOutput");
        JsonObject slice = object(activation, "requestedOutputSlice");
        if (!goal.isOutputClosure()
                || !"HEAP_STATE".equals(string(requestedOutput, "kind"))
                || !requestedOutputSliceContractOperationallyAdmitted(
                activation)) {
            return StaticHeapTransformerCoverage.notApplicable();
        }

        String requestedPort = firstNonBlank(string(requestedOutput,
                "portId"), string(requestedOutput, "symbol"));
        String requestedCell = string(requestedOutput, "cell");
        boolean exactTransformerContract = slice.has(
                "requestedStateTransformerContractVersion");
        List<HeapEffectIssue> transformerContractIssues = new ArrayList<>();
        JsonArray transformerContractGaps = new JsonArray();
        Map<String, Set<String>> causalSitesByMethod = new LinkedHashMap<>();
        Map<String, Set<String>> writeSitesByMethod = new LinkedHashMap<>();
        Map<String, String> signaturesByMethod = new LinkedHashMap<>();
        Map<String, JsonObject> causalWriteBySite = new LinkedHashMap<>();
        Map<String, JsonObject> causalByEdgeId = new LinkedHashMap<>();
        Map<String, Set<String>> exactCausalEdgeIdsBySite =
                new LinkedHashMap<>();
        for (JsonElement element : array(slice, "causalEdges")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject edge = element.getAsJsonObject();
            String signature = string(edge, "method");
            String methodKey = ConcolicCodePosition.sootMethodKey(signature);
            if (methodKey.isEmpty()) {
                continue;
            }
            signaturesByMethod.put(methodKey, signature);
            String siteId = firstNonBlank(string(edge, "siteId"),
                    string(edge, "edgeId"));
            if (siteId.isEmpty()) {
                siteId = GSON.toJson(edge);
            }
            addToSet(causalSitesByMethod, methodKey, siteId);
            String edgeId = string(edge, "edgeId");
            if (!edgeId.isEmpty()) {
                JsonObject previous = causalByEdgeId.put(edgeId, edge);
                if (exactTransformerContract && previous != null) {
                    addTransformerContractIssue(transformerContractIssues,
                            transformerContractGaps,
                            "DUPLICATE_CAUSAL_EDGE_ID:" + edgeId);
                }
            }
            if ("HEAP_WRITE".equals(string(edge, "transferKind"))) {
                causalWriteBySite.put(siteId, edge);
                if (exactTransformerContract
                        && requestedCell.equals(string(edge, "toCell"))
                        && !edgeId.isEmpty()) {
                    addToSet(exactCausalEdgeIdsBySite, siteId, edgeId);
                }
                if (!exactTransformerContract) {
                    addToSet(writeSitesByMethod, methodKey, siteId);
                }
            }
        }
        if (exactTransformerContract) {
            boolean headerValid = integer(slice,
                    "requestedStateTransformerContractVersion", -1) == 1
                    && bool(slice,
                    "requestedStateTransformerContractApplicable", false)
                    && bool(slice,
                    "requestedStateTransformerContractComplete", false)
                    && "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1".equals(
                    string(slice,
                            "requestedStateTransformerContractAuthority"))
                    && requestedPort.equals(string(slice,
                    "requestedStateTransformerContractOutputPort"))
                    && requestedCell.equals(string(slice,
                    "requestedStateTransformerContractOutputCell"))
                    && array(slice,
                    "requestedStateTransformerContractIssues").size() == 0
                    && integer(slice,
                    "requestedStateTransformerObligationCount", -1)
                    == array(slice,
                    "requestedStateTransformerObligations").size();
            if (!headerValid) {
                addTransformerContractIssue(transformerContractIssues,
                        transformerContractGaps,
                        "INVALID_OR_INCOMPLETE_CONTRACT_HEADER");
            }
            Set<String> obligationSites = new LinkedHashSet<>();
            Map<String, Set<String>> obligationEdgeIdsBySite =
                    new LinkedHashMap<>();
            for (JsonElement element : array(slice,
                    "requestedStateTransformerObligations")) {
                if (!element.isJsonObject()) {
                    addTransformerContractIssue(transformerContractIssues,
                            transformerContractGaps,
                            "NON_OBJECT_TRANSFORMER_OBLIGATION");
                    continue;
                }
                JsonObject obligation = element.getAsJsonObject();
                String site = string(obligation, "siteId");
                String signature = string(obligation, "method");
                String methodKey = ConcolicCodePosition.sootMethodKey(
                        signature);
                JsonObject causal = causalWriteBySite.get(site);
                Set<String> obligationEdgeIds = strictPrimitiveStrings(
                        array(obligation, "causalEdgeIds"));
                boolean exactCausalEdges = obligationEdgeIds != null
                        && !obligationEdgeIds.isEmpty();
                if (exactCausalEdges) {
                    for (String edgeId : obligationEdgeIds) {
                        JsonObject referenced = causalByEdgeId.get(edgeId);
                        if (referenced == null
                                || !site.equals(string(referenced,
                                "siteId"))
                                || !signature.equals(string(referenced,
                                "method"))
                                || !"HEAP_WRITE".equals(string(referenced,
                                "transferKind"))
                                || !requestedCell.equals(string(referenced,
                                "toCell"))) {
                            exactCausalEdges = false;
                            break;
                        }
                    }
                }
                boolean valid = !site.isEmpty() && !methodKey.isEmpty()
                        && obligationSites.add(site)
                        && requestedCell.equals(string(obligation,
                        "targetCell"))
                        && "HEAP_WRITE".equals(string(obligation,
                        "transferKind"))
                        && "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL".equals(
                        string(obligation, "authority"))
                        && exactCausalEdges
                        && causal != null
                        && signature.equals(string(causal, "method"))
                        && requestedCell.equals(string(causal, "toCell"));
                if (!valid) {
                    addTransformerContractIssue(transformerContractIssues,
                            transformerContractGaps,
                            "INVALID_TRANSFORMER_OBLIGATION:" + site);
                    continue;
                }
                signaturesByMethod.put(methodKey, signature);
                addToSet(writeSitesByMethod, methodKey, site);
                obligationEdgeIdsBySite.put(site, obligationEdgeIds);
            }
            if (!obligationSites.equals(
                    exactCausalEdgeIdsBySite.keySet())) {
                addTransformerContractIssue(transformerContractIssues,
                        transformerContractGaps,
                        "OBLIGATION_SITES_DO_NOT_EQUAL_EXACT_TARGET_WRITES");
            } else {
                for (String site : obligationSites) {
                    if (!exactCausalEdgeIdsBySite.get(site).equals(
                            obligationEdgeIdsBySite.get(site))) {
                        addTransformerContractIssue(
                                transformerContractIssues,
                                transformerContractGaps,
                                "OBLIGATION_EDGE_IDS_INCOMPLETE:" + site);
                    }
                }
            }
        }
        Map<String, List<GuardedMutationProof>> guardsByMutationSite =
                guardedMutationProofs(slice);

        Map<String, String> voidTransformerSignatures = new LinkedHashMap<>();
        Set<String> processedVoidMethods = new LinkedHashSet<>();
        for (JsonElement element : exactTransformerContract
                ? new JsonArray() : array(slice, "methods")) {
            if (!element.isJsonPrimitive()) {
                continue;
            }
            String signature = element.getAsString();
            String methodKey = ConcolicCodePosition.sootMethodKey(signature);
            if (!methodKey.isEmpty() && processedVoidMethods.add(methodKey)
                    && isVoidMethodSignature(signature)
                    && !causalSitesByMethod.containsKey(methodKey)) {
                voidTransformerSignatures.put(methodKey, signature);
            }
        }

        Set<String> requestedStateFamilies = new LinkedHashSet<>();
        for (JsonElement element : effects) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject effect = element.getAsJsonObject();
            if (requestedPort.equals(string(effect, "outputPort"))) {
                String family = string(effect, "stateFamily");
                if (!family.isEmpty()) {
                    requestedStateFamilies.add(family);
                }
            }
        }

        Map<String, List<JsonObject>> observedEffectsByMethod =
                new LinkedHashMap<>();
        List<JsonObject> requestedStateEffects = new ArrayList<>();
        List<JsonObject> libraryRequestedStateEffects = new ArrayList<>();
        for (JsonElement element : effects) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject effect = element.getAsJsonObject();
            if (!requestedStateFamilies.contains(string(effect,
                    "stateFamily"))) {
                continue;
            }
            requestedStateEffects.add(effect);
            if (effect.has("applicationSiteId")) {
                continue;
            }
            String methodKey = ConcolicCodePosition.vmMethodKey(
                    string(effect, "codePosition"));
            List<JsonObject> observed = observedEffectsByMethod.get(methodKey);
            if (observed == null) {
                observed = new ArrayList<>();
                observedEffectsByMethod.put(methodKey, observed);
            }
            observed.add(effect);
            boolean exactRequestedStateBinding = exactTransformerContract
                    && requestedPort.equals(string(effect, "outputPort"))
                    && !string(effect, "inputPort").isEmpty()
                    && "ACTIVATION_SYMBOL".equals(string(effect,
                    "inputBinding"))
                    && "ACTIVATION_HEAP_OUTPUT".equals(string(effect,
                    "outputBinding"));
            boolean exactRuntimeMapSnapshotBinding =
                    bool(effect, "runtimeMapStateInputBindingComplete",
                            false)
                    && !string(effect,
                    "runtimeMapStateInputObservationId").isEmpty()
                    && !string(effect,
                    "runtimeMapStateInputSnapshotId").isEmpty()
                    && longInteger(effect,
                    "runtimeMapStateInputObjectToken", -1L) > 0L
                    && "EXACT_STABLE_FIELD_OBJECT_TOKEN_PLUS_STATIC_"
                    .concat("REQUESTED_MAP_TRANSFORMER_V1").equals(
                            string(effect,
                                    "runtimeMapStateInputBindingAuthority"));
            if (exactRuntimeMapSnapshotBinding
                    || legacyRuntimeHeapEffects
                    && ("REQUESTED_HEAP_RECEIVER_EXACT_PORT_BINDING".equals(
                    string(effect, "semanticAdmissionAuthority"))
                    || exactRequestedStateBinding)) {
                libraryRequestedStateEffects.add(effect);
            }
        }

        Set<String> exactCoveredWriteSites = new LinkedHashSet<>();
        Set<String> exactCoveredVoidMethods = new LinkedHashSet<>();
        List<JsonObject> unmatchedApplicationProvenance = new ArrayList<>();
        Map<String, JsonObject> exactMatches = new LinkedHashMap<>();
        ExactOrderedPutBijection orderedPutBijection =
                exactTransformerContract
                        ? exactOrderedPutBijection(activation,
                        writeSitesByMethod, requestedStateEffects,
                        rawPathCondition, normalization,
                        dynamicFieldBindings, engineArrayInputBindings,
                        requestedPort, requestedCell)
                        : ExactOrderedPutBijection.notApplicable();
        if (orderedPutBijection.complete) {
            exactCoveredWriteSites.addAll(
                    orderedPutBijection.coveredWriteSites);
            for (JsonElement matchElement : orderedPutBijection.matches) {
                JsonObject match = matchElement.getAsJsonObject();
                exactMatches.put("WRITE::" + string(match, "siteId"),
                        match.deepCopy());
            }
        }
        if (fieldAssignmentCapture != null
                && fieldAssignmentCapture.complete) {
            JsonObject exactRequest = null;
            for (JsonElement element : array(activation,
                    "requestedOutputCapture")) {
                if (!element.isJsonObject()
                        || !"FIELD_ASSIGNMENT_RHS".equals(
                        outputCaptureKind(element.getAsJsonObject()))) {
                    continue;
                }
                if (exactRequest != null) {
                    exactRequest = null;
                    break;
                }
                exactRequest = element.getAsJsonObject();
            }
            if (exactRequest != null) {
                String site = string(exactRequest, "siteId");
                String signature = string(exactRequest, "method");
                String methodKey = ConcolicCodePosition.sootMethodKey(
                        signature);
                if (writeSitesByMethod.containsKey(methodKey)
                        && writeSitesByMethod.get(methodKey).contains(site)) {
                    exactCoveredWriteSites.add(site);
                    JsonObject match = new JsonObject();
                    match.addProperty("obligationKind",
                            "DECLARED_HEAP_WRITE_SITE");
                    match.addProperty("method", signature);
                    match.addProperty("siteId", site);
                    match.addProperty("requestedOutputPort",
                            requestedPort);
                    match.addProperty("captureBindingId", string(
                            exactRequest, "captureBindingId"));
                    match.addProperty("authority",
                            "RUNTIME_EXACT_FIELD_ASSIGNMENT_RHS_CAPTURE");
                    match.add("effectIds", new JsonArray());
                    exactMatches.put("WRITE::" + site, match);
                }
            }
        }
        for (JsonObject effect : requestedStateEffects) {
            String applicationSiteId = string(effect, "applicationSiteId");
            if (applicationSiteId.isEmpty()) {
                continue;
            }
            String originMethod = string(effect, "originMethod");
            String methodKey = ConcolicCodePosition.sootMethodKey(
                    originMethod);
            String obligationKey = "";
            String obligationKind = "";
            String signature = originMethod;
            if (writeSitesByMethod.containsKey(methodKey)
                    && writeSitesByMethod.get(methodKey).contains(
                    applicationSiteId)) {
                exactCoveredWriteSites.add(applicationSiteId);
                obligationKey = "WRITE::" + applicationSiteId;
                obligationKind = "DECLARED_HEAP_WRITE_SITE";
                signature = firstNonBlank(signaturesByMethod.get(methodKey),
                        originMethod);
            } else if (voidTransformerSignatures.containsKey(methodKey)) {
                exactCoveredVoidMethods.add(methodKey);
                obligationKey = "VOID::" + methodKey;
                obligationKind = "EDGE_FREE_VOID_SLICE_METHOD";
                signature = voidTransformerSignatures.get(methodKey);
            } else {
                unmatchedApplicationProvenance.add(effect);
                continue;
            }
            JsonObject match = exactMatches.get(obligationKey);
            if (match == null) {
                match = new JsonObject();
                match.addProperty("obligationKind", obligationKind);
                match.addProperty("method", signature);
                if ("DECLARED_HEAP_WRITE_SITE".equals(obligationKind)) {
                    match.addProperty("siteId", applicationSiteId);
                }
                match.addProperty("requestedOutputPort", requestedPort);
                match.addProperty("stateFamily", string(effect,
                        "stateFamily"));
                match.add("effectIds", new JsonArray());
                match.addProperty("authority",
                        "RUNTIME_APPLICATION_SITE_EXACT_STATIC_OBLIGATION");
                exactMatches.put(obligationKey, match);
            }
            match.getAsJsonArray("effectIds").add(string(effect,
                    "effectId"));
        }

        List<HeapEffectIssue> entryFieldBindingIssues =
                legacyRuntimeHeapObservations
                ? bindEntryValueFieldObservations(activation, slice,
                        requestedStateEffects, guardsByMutationSite,
                        rawBranchMappings, fieldObservations)
                : Collections.<HeapEffectIssue>emptyList();

        Map<String, RuntimeGuardExclusion> guardExcludedWriteSites =
                new LinkedHashMap<>();
        for (Set<String> sites : writeSitesByMethod.values()) {
            for (String site : sites) {
                if (exactCoveredWriteSites.contains(site)) {
                    continue;
                }
                RuntimeGuardExclusion exclusion = runtimeGuardExclusion(
                        guardsByMutationSite.get(site), rawBranchMappings);
                if (exclusion != null) {
                    guardExcludedWriteSites.put(site, exclusion);
                }
            }
        }

        List<StaticTransformerObligation> remaining = new ArrayList<>();
        int declaredWriteSiteCount = 0;
        int coveredWriteSiteCount = exactCoveredWriteSites.size()
                + guardExcludedWriteSites.size();
        for (Map.Entry<String, Set<String>> entry
                : writeSitesByMethod.entrySet()) {
            int declared = entry.getValue().size();
            List<String> uncoveredByExactProvenance = new ArrayList<>();
            for (String site : entry.getValue()) {
                if (!exactCoveredWriteSites.contains(site)
                        && !guardExcludedWriteSites.containsKey(site)) {
                    uncoveredByExactProvenance.add(site);
                }
            }
            int observed = observedEffectsByMethod.containsKey(entry.getKey())
                    ? observedEffectsByMethod.get(entry.getKey()).size() : 0;
            int covered = exactTransformerContract ? 0
                    : Math.min(uncoveredByExactProvenance.size(), observed);
            declaredWriteSiteCount += declared;
            coveredWriteSiteCount += covered;
            int ordinal = 0;
            for (String site : uncoveredByExactProvenance) {
                if (ordinal++ < covered) {
                    continue;
                }
                remaining.add(StaticTransformerObligation.heapWrite(
                        entry.getKey(), firstNonBlank(
                                signaturesByMethod.get(entry.getKey()),
                                entry.getKey()), site));
            }
        }

        for (Map.Entry<String, String> entry
                : voidTransformerSignatures.entrySet()) {
            String methodKey = entry.getKey();
            if (exactCoveredVoidMethods.contains(methodKey)
                    || observedEffectsByMethod.containsKey(methodKey)) {
                continue;
            }
            remaining.add(StaticTransformerObligation.edgeFreeVoid(
                    methodKey, entry.getValue()));
        }

        JsonArray matches = new JsonArray();
        for (JsonObject match : exactMatches.values()) {
            matches.add(match);
        }
        for (Map.Entry<String, RuntimeGuardExclusion> entry
                : guardExcludedWriteSites.entrySet()) {
            matches.add(entry.getValue().toMatch(entry.getKey(),
                    requestedPort));
        }
        int applicationProvenanceMatchedTransformerCount =
                exactMatches.size() - orderedPutBijection.matchedCount;
        int guardExcludedWriteSiteCount = guardExcludedWriteSites.size();
        int statePortMatchedTransformerCount =
                orderedPutBijection.matchedCount;
        int unresolvedStatePortEffectCount = 0;
        Set<String> libraryFamilies = new LinkedHashSet<>();
        for (JsonObject effect : libraryRequestedStateEffects) {
            libraryFamilies.add(string(effect, "stateFamily"));
        }
        if (requestedStateFamilies.size() > 1) {
            unresolvedStatePortEffectCount = requestedStateEffects.size();
        } else if (!orderedPutBijection.applicable
                && remaining.size() == 1
                && !libraryRequestedStateEffects.isEmpty()
                && libraryFamilies.size() == 1
                && libraryEffectsMatchUniqueTransformer(
                libraryRequestedStateEffects, remaining.get(0),
                exactTransformerContract)) {
            StaticTransformerObligation matched = remaining.remove(0);
            statePortMatchedTransformerCount += 1;
            if (matched.heapWrite) {
                coveredWriteSiteCount++;
            }
            JsonObject match = new JsonObject();
            match.addProperty("obligationKind", matched.kind());
            match.addProperty("method", matched.signature);
            if (!matched.siteId.isEmpty()) {
                match.addProperty("siteId", matched.siteId);
            }
            match.addProperty("requestedOutputPort", requestedPort);
            match.addProperty("stateFamily",
                    libraryFamilies.iterator().next());
            JsonArray effectIds = new JsonArray();
            for (JsonObject effect : libraryRequestedStateEffects) {
                effectIds.add(string(effect, "effectId"));
            }
            match.add("effectIds", effectIds);
            match.addProperty("authority",
                    exactTransformerContract
                            ? "UNIQUE_EXACT_TRANSFORMER_PLUS_REQUESTED_STATE_"
                            + "PORT_AND_APPLICATION_METHOD"
                            : "UNIQUE_UNRESOLVED_TRANSFORMER_AND_REQUESTED_"
                            + "STATE_FAMILY");
            matches.add(match);
        } else if (!remaining.isEmpty()
                && !libraryRequestedStateEffects.isEmpty()) {
            unresolvedStatePortEffectCount =
                    libraryRequestedStateEffects.size();
        }

        List<HeapEffectIssue> issues = new ArrayList<>(
                transformerContractIssues);
        issues.addAll(entryFieldBindingIssues);
        issues.addAll(orderedPutBijection.issues);
        JsonArray gaps = transformerContractGaps.deepCopy();
        for (JsonElement gapElement : orderedPutBijection.gaps) {
            JsonObject gap = gapElement.getAsJsonObject();
            gaps.add(gap.deepCopy());
        }
        for (JsonObject effect : unmatchedApplicationProvenance) {
            JsonObject gap = new JsonObject();
            gap.addProperty("kind",
                    "APPLICATION_HEAP_EFFECT_STATIC_PROVENANCE_MISMATCH");
            gap.addProperty("originMethod", string(effect, "originMethod"));
            gap.addProperty("applicationSiteId", string(effect,
                    "applicationSiteId"));
            gap.addProperty("effectId", string(effect, "effectId"));
            gaps.add(gap);
            issues.add(new HeapEffectIssue(
                    "APPLICATION_HEAP_EFFECT_STATIC_PROVENANCE_MISMATCH",
                    integer(effect, "rawConditionIndex", -1),
                    string(effect, "applicationSiteId"),
                    string(effect, "originMethod")));
        }
        Map<String, List<StaticTransformerObligation>> writeGaps =
                new LinkedHashMap<>();
        int edgeFreeVoidMethodCount = 0;
        for (StaticTransformerObligation obligation : remaining) {
            if (obligation.heapWrite) {
                List<StaticTransformerObligation> methodGaps =
                        writeGaps.get(obligation.methodKey);
                if (methodGaps == null) {
                    methodGaps = new ArrayList<>();
                    writeGaps.put(obligation.methodKey, methodGaps);
                }
                methodGaps.add(obligation);
                continue;
            }
            edgeFreeVoidMethodCount++;
            JsonObject gap = new JsonObject();
            gap.addProperty("kind",
                    "UNMODELED_DECLARED_HEAP_TRANSFORMER");
            gap.addProperty("method", obligation.signature);
            gap.addProperty("reason",
                    "VOID_SLICE_METHOD_HAS_NO_CAUSAL_EDGE_OR_RUNTIME_EFFECT");
            gaps.add(gap);
            issues.add(new HeapEffectIssue(
                    "UNMODELED_DECLARED_HEAP_TRANSFORMER", -1,
                    "requestedOutputSlice.methods", obligation.signature));
        }

        int uncoveredWriteSiteCount = 0;
        for (Map.Entry<String, List<StaticTransformerObligation>> entry
                : writeGaps.entrySet()) {
            uncoveredWriteSiteCount += entry.getValue().size();
            StaticTransformerObligation first = entry.getValue().get(0);
            JsonArray sites = new JsonArray();
            for (StaticTransformerObligation obligation : entry.getValue()) {
                sites.add(obligation.siteId);
            }
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", "UNOBSERVED_DECLARED_HEAP_WRITE");
            gap.addProperty("method", first.signature);
            gap.addProperty("uncoveredSiteCount", entry.getValue().size());
            gap.add("declaredSites", sites);
            gaps.add(gap);
            issues.add(new HeapEffectIssue(
                    "UNOBSERVED_DECLARED_HEAP_WRITE", -1,
                    GSON.toJson(sites), first.signature));
        }
        if (unresolvedStatePortEffectCount > 0) {
            JsonObject gap = new JsonObject();
            gap.addProperty("kind",
                    "UNRESOLVED_REQUESTED_HEAP_EFFECT_PROVENANCE");
            gap.addProperty("requestedOutputPort", requestedPort);
            gap.addProperty("effectCount", unresolvedStatePortEffectCount);
            gap.addProperty("remainingTransformerObligationCount",
                    remaining.size());
            gaps.add(gap);
            issues.add(new HeapEffectIssue(
                    "UNRESOLVED_REQUESTED_HEAP_EFFECT_PROVENANCE", -1,
                    requestedPort, "requested-output-state-family"));
        }

        Set<String> declaredWriteSites = new LinkedHashSet<>();
        for (Set<String> sites : writeSitesByMethod.values()) {
            declaredWriteSites.addAll(sites);
        }
        return new StaticHeapTransformerCoverage(true,
                exactTransformerContract,
                exactTransformerContract
                        && transformerContractIssues.isEmpty(),
                declaredWriteSiteCount, coveredWriteSiteCount,
                uncoveredWriteSiteCount, edgeFreeVoidMethodCount,
                applicationProvenanceMatchedTransformerCount,
                guardExcludedWriteSiteCount,
                statePortMatchedTransformerCount,
                unresolvedStatePortEffectCount, matches, gaps, issues,
                declaredWriteSites, guardExcludedWriteSites);
    }

    /**
     * Discharges the exact four-site array-to-map transformer only through a
     * one-to-one runtime witness.  This is deliberately narrower than the
     * historical method-count fallback: every static array selector, raw
     * array load, dynamic key field, map-state transition and requested
     * output port must join in the same order.
     */
    private static ExactOrderedPutBijection exactOrderedPutBijection(
            JsonObject activation,
            Map<String, Set<String>> writeSitesByMethod,
            List<JsonObject> requestedStateEffects,
            JsonArray rawPathCondition, PathNormalization normalization,
            JsonArray dynamicFieldBindings,
            JsonArray engineArrayInputBindings,
            String requestedPort, String requestedCell) {
        Map<String, List<JsonObject>> declarationsByMethod =
                new LinkedHashMap<>();
        for (JsonElement element : array(activation,
                "containerElementFieldBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject declaration = element.getAsJsonObject();
            String methodKey = ConcolicCodePosition.sootMethodKey(string(
                    declaration, "method"));
            if (methodKey.isEmpty()
                    || !"ARRAY_ELEMENT_FIELD".equals(string(declaration,
                    "kind"))) {
                continue;
            }
            List<JsonObject> group = declarationsByMethod.get(methodKey);
            if (group == null) {
                group = new ArrayList<>();
                declarationsByMethod.put(methodKey, group);
            }
            group.add(declaration);
        }

        List<String> candidateMethods = new ArrayList<>();
        for (Map.Entry<String, List<JsonObject>> entry
                : declarationsByMethod.entrySet()) {
            int writeCount = writeSitesByMethod.containsKey(entry.getKey())
                    ? writeSitesByMethod.get(entry.getKey()).size() : 0;
            if (entry.getValue().size() == 4 || writeCount == 4) {
                candidateMethods.add(entry.getKey());
            }
        }
        if (candidateMethods.isEmpty()) {
            return ExactOrderedPutBijection.notApplicable();
        }
        if (candidateMethods.size() != 1) {
            return ExactOrderedPutBijection.failed(
                    "AMBIGUOUS_APPLICATION_METHOD_GROUP", -1);
        }
        String methodKey = candidateMethods.get(0);
        List<JsonObject> declarations = new ArrayList<>(
                declarationsByMethod.get(methodKey));
        if (declarations.size() != 4) {
            return ExactOrderedPutBijection.failed(
                    "STATIC_CONTAINER_DECLARATION_CARDINALITY", -1);
        }
        Collections.sort(declarations, new Comparator<JsonObject>() {
            @Override
            public int compare(JsonObject left, JsonObject right) {
                return Integer.compare(integer(left, "elementIndex", -1),
                        integer(right, "elementIndex", -1));
            }
        });

        Set<String> methodWriteSites = writeSitesByMethod.get(methodKey);
        if (methodWriteSites == null) {
            return ExactOrderedPutBijection.failed(
                    "STATIC_WRITE_OBLIGATION_CARDINALITY", -1);
        }
        List<String> obligationSites = new ArrayList<>(methodWriteSites);
        Collections.sort(obligationSites, new Comparator<String>() {
            @Override
            public int compare(String left, String right) {
                return Integer.compare(siteUnitIndex(left),
                        siteUnitIndex(right));
            }
        });
        if (obligationSites.size() != 4) {
            return ExactOrderedPutBijection.failed(
                    "STATIC_WRITE_OBLIGATION_CARDINALITY", -1);
        }

        String baseInput = string(declarations.get(0),
                "baseInputSymbol");
        String containerPort = string(declarations.get(0),
                "containerInputPort");
        String containerCell = string(declarations.get(0),
                "containerInputCell");
        String methodSignature = string(declarations.get(0), "method");
        if (baseInput.isEmpty() || containerPort.isEmpty()
                || containerCell.isEmpty() || methodSignature.isEmpty()) {
            return ExactOrderedPutBijection.failed(
                    "STATIC_CONTAINER_ENDPOINT_MISSING", -1);
        }

        int previousWriteUnit = -1;
        for (int index = 0; index < 4; index++) {
            JsonObject declaration = declarations.get(index);
            int loadUnit = siteUnitIndex(string(declaration,
                    "arrayLoadSiteId"));
            int fieldUnit = siteUnitIndex(string(declaration,
                    "fieldMaterializationSiteId"));
            int writeUnit = siteUnitIndex(obligationSites.get(index));
            int nextLoadUnit = index + 1 < declarations.size()
                    ? siteUnitIndex(string(declarations.get(index + 1),
                    "arrayLoadSiteId")) : Integer.MAX_VALUE;
            Set<String> proofEdgeIds = strictPrimitiveStrings(array(
                    declaration, "proofCausalEdgeIds"));
            boolean exactStaticOrder = integer(declaration,
                    "schemaVersion", -1) == 1
                    && bool(declaration, "complete", false)
                    && "EXACT_ARRAY_INDEX".equals(string(declaration,
                    "selectorAuthority"))
                    && integer(declaration, "elementIndex", -1) == index
                    && integer(declaration,
                    "elementOccurrence", -1) == 1
                    && baseInput.equals(string(declaration,
                    "baseInputSymbol"))
                    && containerPort.equals(string(declaration,
                    "containerInputPort"))
                    && containerCell.equals(string(declaration,
                    "containerInputCell"))
                    && methodSignature.equals(string(declaration, "method"))
                    && methodKey.equals(ConcolicCodePosition.sootMethodKey(
                    string(declaration, "arrayLoadSiteId")))
                    && methodKey.equals(ConcolicCodePosition.sootMethodKey(
                    string(declaration,
                            "fieldMaterializationSiteId")))
                    && methodKey.equals(ConcolicCodePosition.sootMethodKey(
                    obligationSites.get(index)))
                    && "STATIC_EXACT_CONTAINER_ARRAY_ACCESSOR_DECLARED_"
                    .concat("FIELD_FOUR_EDGE_JOIN_V1").equals(string(
                            declaration, "proofAuthority"))
                    && proofEdgeIds != null && proofEdgeIds.size() == 4
                    && loadUnit >= 0 && loadUnit < fieldUnit
                    && fieldUnit < writeUnit && writeUnit < nextLoadUnit
                    && writeUnit > previousWriteUnit;
            if (!exactStaticOrder) {
                return ExactOrderedPutBijection.failed(
                        "STATIC_SELECTOR_OR_SITE_ORDER", -1);
            }
            previousWriteUnit = writeUnit;
        }

        List<JsonObject> containerInputBindings = new ArrayList<>();
        for (JsonElement element : array(object(activation,
                "requestedOutputSlice"), "inputBindings")) {
            if (element.isJsonObject() && containerPort.equals(string(
                    element.getAsJsonObject(), "inputPort"))) {
                containerInputBindings.add(element.getAsJsonObject());
            }
        }
        if (containerInputBindings.size() != 1) {
            return ExactOrderedPutBijection.failed(
                    "CONTAINER_INPUT_PORT_BINDING_CARDINALITY", -1);
        }
        JsonObject containerInputBinding = containerInputBindings.get(0);
        Set<String> declaredSinkSites = strictPrimitiveStrings(array(
                containerInputBinding,
                "requestedStateTransformerSinkSites"));
        if (declaredSinkSites == null
                || !declaredSinkSites.equals(new LinkedHashSet<>(
                obligationSites))
                || !containerCell.equals(string(containerInputBinding,
                "dependencyCell"))
                || !"EXACT_CELL_IDENTITY".equals(string(
                containerInputBinding, "bindingAuthority"))
                || !bool(containerInputBinding,
                "requestedStateTransformerSinkClosureComplete", false)
                || !bool(containerInputBinding,
                "requestedStateTransformerSinkExclusive", false)
                || array(containerInputBinding,
                "requestedStateTransformerUnclassifiedEdgeIds").size()
                != 0
                || !"STATIC_FORWARD_CAUSAL_CLOSURE_TO_EXACT_REQUESTED_"
                .concat("STATE_TRANSFORMERS").equals(string(
                        containerInputBinding,
                        "requestedStateTransformerSinkAuthority"))) {
            return ExactOrderedPutBijection.failed(
                    "CONTAINER_INPUT_TO_WRITE_SITES_JOIN", -1);
        }

        List<JsonObject> putEffects = new ArrayList<>();
        for (JsonObject effect : requestedStateEffects) {
            if ("MAP_PUT".equals(string(effect, "kind"))) {
                putEffects.add(effect);
            }
        }
        if (putEffects.size() != 4) {
            return ExactOrderedPutBijection.failed(
                    "RUNTIME_MAP_PUT_CARDINALITY", -1);
        }
        String stateFamily = string(putEffects.get(0), "stateFamily");
        JsonElement mapExpression = putEffects.get(0).get("mapExpression");
        HeapPortBinding receiver = new HeapPortResolver(activation)
                .requestedOutputBinding(mapExpression);
        if (stateFamily.isEmpty() || mapExpression == null
                || !receiver.resolved
                || !requestedPort.equals(receiver.outputPort)) {
            return ExactOrderedPutBijection.failed(
                    "REQUESTED_OUTPUT_PORT_OR_RECEIVER", integer(
                    putEffects.get(0), "rawConditionIndex", -1));
        }
        int previousRawIndex = -1;
        int previousStateAfter = -1;
        String previousPostState = "";
        String previousOutputPort = "";
        for (int index = 0; index < putEffects.size(); index++) {
            JsonObject effect = putEffects.get(index);
            int rawIndex = integer(effect, "rawConditionIndex", -1);
            int before = integer(effect, "stateOrdinalBefore", -1);
            int after = integer(effect, "stateOrdinalAfter", -1);
            boolean exactRuntimeOrder = methodKey.equals(
                    ConcolicCodePosition.vmMethodKey(string(effect,
                            "codePosition")))
                    && stateFamily.equals(string(effect, "stateFamily"))
                    && mapExpression.equals(effect.get("mapExpression"))
                    && rawIndex > previousRawIndex
                    && rawIndex >= 0
                    && normalization.isSemantic(rawIndex)
                    && before >= 0 && after == before + 1
                    && (index == 0 || before == previousStateAfter
                    && previousPostState.equals(string(effect, "preState"))
                    && previousOutputPort.equals(string(effect,
                            "inputPort")))
                    && (index + 1 < putEffects.size()
                    || requestedPort.equals(string(effect, "outputPort")));
            if (!exactRuntimeOrder) {
                return ExactOrderedPutBijection.failed(
                        "RUNTIME_EFFECT_ORDER_OR_STATE_CHAIN", rawIndex);
            }
            previousRawIndex = rawIndex;
            previousStateAfter = after;
            previousPostState = string(effect, "postState");
            previousOutputPort = string(effect, "outputPort");
        }

        List<JsonObject> arrays = new ArrayList<>();
        for (JsonElement element : engineArrayInputBindings) {
            if (element.isJsonObject() && containerPort.equals(string(
                    element.getAsJsonObject(), "inputPort"))) {
                arrays.add(element.getAsJsonObject());
            }
        }
        if (arrays.size() != 1) {
            return ExactOrderedPutBijection.failed(
                    "ENGINE_ARRAY_BINDING_CARDINALITY", -1);
        }
        JsonObject engineArray = arrays.get(0);
        JsonObject arrayValue = object(engineArray,
                "arrayValueExpression");
        JsonArray engineElements = array(arrayValue, "_elements");
        String engineArrayId = string(engineArray, "engineArrayId");
        long arrayObjectToken = longInteger(engineArray,
                "arrayObjectToken", 0L);
        String activationId = string(activation, "activationId");
        boolean completeEngineArray = bool(engineArray, "complete", false)
                && !engineArrayId.isEmpty() && arrayObjectToken > 0L
                && activationId.equals(string(engineArray,
                "objectTokenScope"))
                && "VM_ACTIVE_SYM_ARRAY_ID_V1".equals(string(engineArray,
                "engineArrayIdAuthority"))
                && "VM_EXACT_FINITE_ARRAY_VALUE_V1".equals(string(
                arrayValue, "_authority"))
                && bool(arrayValue, "_elements_complete", false)
                && integer(arrayValue, "_concrete_length", -1) == 4
                && engineElements.size() == 4;
        for (int index = 0; index < engineElements.size(); index++) {
            completeEngineArray &= engineElements.get(index).isJsonObject()
                    && integer(engineElements.get(index).getAsJsonObject(),
                    "index", -1) == index
                    && hasNonNull(engineElements.get(index).getAsJsonObject(),
                    "expression");
        }
        if (!completeEngineArray) {
            return ExactOrderedPutBijection.failed(
                    "ENGINE_ARRAY_BINDING_INCOMPLETE", -1);
        }

        List<JsonObject> orderedBindings = new ArrayList<>();
        for (JsonObject declaration : declarations) {
            String staticBindingId = string(declaration, "bindingId");
            List<JsonObject> matches = new ArrayList<>();
            for (JsonElement element : dynamicFieldBindings) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if ("DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(
                        string(binding, "kind"))
                        && staticBindingId.equals(string(object(binding,
                        "containerSelector"), "bindingId"))) {
                    matches.add(binding);
                }
            }
            if (matches.size() != 1) {
                return ExactOrderedPutBijection.failed(
                        "DYNAMIC_FIELD_BINDING_CARDINALITY", -1);
            }
            orderedBindings.add(matches.get(0));
        }

        JsonArray runtimeMatches = new JsonArray();
        Set<Integer> consumerRawIndices = new LinkedHashSet<>();
        for (int index = 0; index < 4; index++) {
            JsonObject declaration = declarations.get(index);
            JsonObject binding = orderedBindings.get(index);
            JsonObject selector = object(binding, "containerSelector");
            JsonObject effect = putEffects.get(index);
            int rawIndex = integer(effect, "rawConditionIndex", -1);
            int loadIndex = rawIndex - 1;
            boolean exactDynamicKey = bool(binding, "complete", false)
                    && string(declaration, "bindingId").equals(string(
                    selector, "bindingId"))
                    && baseInput.equals(string(binding,
                    "baseInputSymbol"))
                    && containerPort.equals(string(selector,
                    "containerInputPort"))
                    && containerCell.equals(string(selector,
                    "containerInputCell"))
                    && integer(selector, "elementIndex", -1) == index
                    && integer(selector,
                    "elementOccurrence", -1) == 1
                    && longInteger(selector,
                    "containerObjectToken", 0L) == arrayObjectToken
                    && longInteger(selector,
                    "elementObjectToken", 0L) > 0L
                    && activationId.equals(string(selector,
                    "objectTokenScope"))
                    && string(declaration,
                    "fieldMaterializationSiteId").equals(string(binding,
                    "effectiveMaterializationSiteId"))
                    && integer(binding,
                    "effectiveMaterializationOccurrence", -1) == 1
                    && CONTAINER_SITE_BRIDGE_AUTHORITY.equals(string(binding,
                    "materializationSiteBridgeAuthority"))
                    && string(declaration, "bindingId").equals(string(
                    binding, "materializationSiteBridgeBindingId"))
                    && longInteger(selector, "elementObjectToken", 0L)
                    == longInteger(binding,
                    "materializationSiteBridgeElementObjectToken", -1L)
                    && activationId.equals(string(binding,
                    "materializationSiteBridgeObjectTokenScope"))
                    && hasNonNull(binding, "fieldExpression")
                    && binding.get("fieldExpression").equals(effect.get(
                    "keyExpression"))
                    && "EXACT_REQUESTED_OUTPUT_MAP_PUT_KEY_DYNAMIC_SYMBOL"
                    .equals(string(binding, "fieldExpressionAuthority"))
                    && integer(binding,
                    "consumerWitnessRawConditionIndex", -1) == rawIndex
                    && consumerRawIndices.add(rawIndex)
                    && receiver.inputPort.equals(string(binding,
                    "consumerWitnessInputPort"))
                    && requestedPort.equals(string(binding,
                    "consumerWitnessOutputPort"))
                    && "MAP_PUT".equals(string(binding,
                    "consumerWitnessOperation"))
                    && CONTAINER_PUT_CONSUMER_AUTHORITY.equals(string(binding,
                    "consumerWitnessAuthority"))
                    && string(effect, "siteId").equals(string(binding,
                    "consumerWitnessSiteId"));
            if (!exactDynamicKey) {
                return ExactOrderedPutBijection.failed(
                        "DYNAMIC_KEY_BINDING_OR_RECEIVER", rawIndex);
            }

            if (loadIndex < 0 || loadIndex >= rawPathCondition.size()
                    || !normalization.isSemantic(loadIndex)
                    || !rawPathCondition.get(loadIndex).isJsonObject()) {
                return ExactOrderedPutBijection.failed(
                        "ARRAY_LOAD_NOT_IMMEDIATELY_BEFORE_PUT", rawIndex);
            }
            JsonObject load = rawPathCondition.get(loadIndex)
                    .getAsJsonObject();
            JsonObject rawPut = rawPathCondition.get(rawIndex)
                    .getAsJsonObject();
            JsonArray rawParameters = array(rawPut, "_param_list");
            boolean exactLoad = "_array_expr".equals(string(load, "_type"))
                    && bool(load, "_is_load", false)
                    && engineArrayId.equals(string(load, "_arr_str"))
                    && exactIntConstant(object(load, "_index_exp"), index)
                    && hasNonNull(load, "_value_exp")
                    && load.get("_value_exp").equals(effect.get(
                    "valueExpression"))
                    && methodKey.equals(ConcolicCodePosition.vmMethodKey(
                    codePosition(load)))
                    && "MethodExpression".equals(string(rawPut, "_type"))
                    && "java/util/HashMap put".equals(string(rawPut,
                    "_name"))
                    && rawParameters.size() == 3
                    && rawParameters.get(0).equals(effect.get(
                    "mapExpression"))
                    && rawParameters.get(1).equals(effect.get(
                    "keyExpression"))
                    && rawParameters.get(2).equals(effect.get(
                    "valueExpression"));
            if (!exactLoad) {
                return ExactOrderedPutBijection.failed(
                        "ARRAY_LOAD_VALUE_INDEX_OR_RAW_PUT_JOIN", rawIndex);
            }

            JsonObject match = new JsonObject();
            match.addProperty("obligationKind",
                    "DECLARED_HEAP_WRITE_SITE");
            match.addProperty("method", methodSignature);
            match.addProperty("siteId", obligationSites.get(index));
            match.addProperty("requestedOutputPort", requestedPort);
            match.addProperty("requestedOutputCell", requestedCell);
            match.addProperty("stateFamily", stateFamily);
            JsonArray effectIds = new JsonArray();
            effectIds.add(string(effect, "effectId"));
            match.add("effectIds", effectIds);
            match.addProperty("dynamicBindingId", string(binding,
                    "dynamicBindingId"));
            match.addProperty("containerBindingId", string(declaration,
                    "bindingId"));
            match.addProperty("elementIndex", index);
            match.addProperty("rawConditionIndex", rawIndex);
            match.addProperty("arrayLoadRawConditionIndex", loadIndex);
            match.addProperty("engineArrayId", engineArrayId);
            match.addProperty("authority",
                    "RUNTIME_ORDERED_MAP_PUT_TO_EXACT_STATIC_WRITE_AND_"
                            + "CONTAINER_ELEMENT_FIELD_V1");
            runtimeMatches.add(match);
        }
        return ExactOrderedPutBijection.complete(obligationSites,
                runtimeMatches);
    }

    private static int siteUnitIndex(String siteId) {
        if (siteId == null) return -1;
        int marker = siteId.lastIndexOf("#u");
        if (marker < 0 || marker + 2 >= siteId.length()) return -1;
        try {
            return Integer.parseInt(siteId.substring(marker + 2));
        } catch (NumberFormatException malformed) {
            return -1;
        }
    }

    private static boolean exactIntConstant(JsonObject expression,
                                            int expected) {
        return "ConstExpr".equals(string(expression, "_type"))
                && "I".equals(string(expression, "_java_type"))
                && ("Y_I_" + expected).equals(string(expression, "_exp"));
    }

    private static void addTransformerContractIssue(
            List<HeapEffectIssue> issues, JsonArray gaps, String detail) {
        JsonObject gap = new JsonObject();
        gap.addProperty("kind",
                "INVALID_REQUESTED_STATE_TRANSFORMER_CONTRACT");
        gap.addProperty("detail", detail);
        gaps.add(gap);
        issues.add(new HeapEffectIssue(
                "INVALID_REQUESTED_STATE_TRANSFORMER_CONTRACT", -1,
                detail, "requestedOutputSlice"));
    }

    private static boolean libraryEffectsMatchUniqueTransformer(
            List<JsonObject> effects,
            StaticTransformerObligation obligation,
            boolean exactTransformerContract) {
        if (!exactTransformerContract) {
            return true;
        }
        if (effects.isEmpty() || obligation.methodKey.isEmpty()) {
            return false;
        }
        for (JsonObject effect : effects) {
            if (!obligation.methodKey.equals(ConcolicCodePosition.vmMethodKey(
                    string(effect, "codePosition")))) {
                return false;
            }
        }
        return true;
    }

    private static List<HeapEffectIssue> bindEntryValueFieldObservations(
            JsonObject activation, JsonObject slice,
            List<JsonObject> effects,
            Map<String, List<GuardedMutationProof>> guardsByMutationSite,
            JsonArray branchMappings, JsonElement fieldObservations) {
        List<HeapEffectIssue> issues = new ArrayList<>();
        Set<String> requestedInputs = new LinkedHashSet<>();
        for (JsonElement element : array(slice, "inputPorts")) {
            if (element.isJsonPrimitive()) {
                requestedInputs.add(element.getAsString());
            }
        }

        for (JsonObject effect : effects) {
            if (!effect.has("removedValueExpression")) {
                continue;
            }
            JsonArray bindings = new JsonArray();
            effect.add("entryFieldBindings", bindings);
            boolean complete = true;
            int valueIdentity = integer(effect, "entryValueIdentity", 0);
            String mutationSite = string(effect, "applicationSiteId");
            List<GuardedMutationProof> proofs = guardsByMutationSite.get(
                    mutationSite);
            if (valueIdentity == 0) {
                complete = false;
                issues.add(new HeapEffectIssue(
                        "MISSING_RUNTIME_ENTRY_VALUE_IDENTITY",
                        integer(effect, "rawConditionIndex", -1),
                        mutationSite, string(effect, "originMethod")));
            }
            if (proofs == null || proofs.isEmpty()) {
                effect.addProperty("entryValueFieldBindingComplete",
                        complete);
                continue;
            }

            Set<String> guardSites = new LinkedHashSet<>();
            for (GuardedMutationProof proof : proofs) {
                guardSites.add(proof.guardSiteId);
            }
            JsonArray guardSiteEvidence = new JsonArray();
            for (String guardSite : guardSites) {
                guardSiteEvidence.add(guardSite);
            }
            effect.add("entryValueGuardSiteIds", guardSiteEvidence);

            Set<String> guardExpressionSymbols = new LinkedHashSet<>();
            int observedGuardMappingCount = 0;
            for (JsonElement element : branchMappings) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject mapping = element.getAsJsonObject();
                if (!guardSites.contains(string(mapping, "siteId"))) {
                    continue;
                }
                observedGuardMappingCount++;
                JsonElement condition = mapping.has("condition")
                        ? mapping.get("condition")
                        : mapping.get("rawCondition");
                HeapPortResolver.collectExpressionSymbols(condition,
                        guardExpressionSymbols);
            }
            if (observedGuardMappingCount == 0) {
                complete = false;
                issues.add(new HeapEffectIssue(
                        "MISSING_RUNTIME_ENTRY_VALUE_GUARD_OBSERVATION",
                        integer(effect, "rawConditionIndex", -1),
                        GSON.toJson(guardSiteEvidence), mutationSite));
            }

            Map<String, JsonObject> fieldActions = new LinkedHashMap<>();
            Set<String> duplicateActionSymbols = new LinkedHashSet<>();
            for (JsonElement element : runtimeMaterializationActions(
                    activation)) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject action = element.getAsJsonObject();
                String symbol = string(action, "symbol");
                if (!"FIELD_ACCESS".equals(string(action, "bindingMode"))
                        || symbol.isEmpty()
                        || !requestedInputs.contains(symbol)
                        || array(action, "fieldPath").size() == 0
                        || !referencesAnySymbol(guardExpressionSymbols,
                        symbol)) {
                    continue;
                }
                if (fieldActions.put(symbol, action) != null) {
                    duplicateActionSymbols.add(symbol);
                }
            }

            for (Map.Entry<String, JsonObject> actionEntry
                    : fieldActions.entrySet()) {
                String symbol = actionEntry.getKey();
                JsonObject action = actionEntry.getValue();
                if (duplicateActionSymbols.contains(symbol)) {
                    complete = false;
                    issues.add(new HeapEffectIssue(
                            "AMBIGUOUS_ENTRY_VALUE_FIELD_ACTION",
                            integer(effect, "rawConditionIndex", -1),
                            symbol, mutationSite));
                    continue;
                }
                List<JsonObject> observations = new ArrayList<>();
                if (fieldObservations != null
                        && fieldObservations.isJsonArray()) {
                    for (JsonElement observationElement
                            : fieldObservations.getAsJsonArray()) {
                        if (observationElement.isJsonObject()
                                && symbol.equals(string(
                                observationElement.getAsJsonObject(),
                                "symbol"))) {
                            observations.add(
                                    observationElement.getAsJsonObject());
                        }
                    }
                }
                if (observations.size() != 1) {
                    complete = false;
                    issues.add(new HeapEffectIssue(
                            observations.isEmpty()
                                    ? "MISSING_ENTRY_VALUE_FIELD_OBSERVATION"
                                    : "AMBIGUOUS_ENTRY_VALUE_FIELD_OBSERVATION",
                            integer(effect, "rawConditionIndex", -1),
                            symbol, mutationSite));
                    continue;
                }
                JsonObject observation = observations.get(0);
                String fieldSignature = firstNonBlank(
                        string(action, "field"), string(action, "cell"));
                String fieldType = fieldJavaType(fieldSignature);
                boolean structurallyComplete = bool(observation,
                        "available", false)
                        && "AT_MATERIALIZATION".equals(string(observation,
                        "phase"))
                        && array(action, "fieldPath").equals(
                        array(observation, "path"))
                        && !fieldSignature.isEmpty()
                        && !fieldType.isEmpty();
                if (!structurallyComplete) {
                    complete = false;
                    issues.add(new HeapEffectIssue(
                            "INCOMPLETE_ENTRY_VALUE_FIELD_OBSERVATION",
                            integer(effect, "rawConditionIndex", -1),
                            symbol, mutationSite));
                    continue;
                }
                int ownerIdentity = integer(observation,
                        "leafOwnerIdentity", 0);
                if (ownerIdentity == 0 || ownerIdentity != valueIdentity) {
                    complete = false;
                    issues.add(new HeapEffectIssue(
                            "ENTRY_VALUE_FIELD_OWNER_IDENTITY_MISMATCH",
                            integer(effect, "rawConditionIndex", -1),
                            symbol, mutationSite));
                    continue;
                }
                JsonObject binding = new JsonObject();
                binding.addProperty("fieldSymbol", symbol);
                binding.addProperty("fieldSignature", fieldSignature);
                binding.addProperty("fieldJavaType", fieldType);
                binding.add("fieldPath", array(observation, "path")
                        .deepCopy());
                binding.addProperty("ownerIdentity", ownerIdentity);
                binding.addProperty("authority",
                        "LEGACY_IDENTITY_HASH_EQUALS_REMOVED_ENTRY_VALUE");
                bindings.add(binding);
            }
            effect.addProperty("entryValueFieldBindingComplete", complete);
        }
        return issues;
    }

    private static boolean referencesAnySymbol(Set<String> expressions,
                                               String symbol) {
        for (String expression : expressions) {
            if (HeapPortResolver.containsSymbolReference(expression, symbol)) {
                return true;
            }
        }
        return false;
    }

    private static Map<String, List<GuardedMutationProof>>
    guardedMutationProofs(JsonObject slice) {
        Map<String, LinkedHashMap<String, GuardedMutationProof>> deduped =
                new LinkedHashMap<>();
        for (JsonElement element : array(slice, "causalEdges")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject edge = element.getAsJsonObject();
            if (!"heap_mutation_path_guard".equals(string(edge, "kind"))
                    || !"STATIC_CONTROL_DEPENDENCE_PER_MUTATION_SITE".equals(
                    string(edge, "guardedMutationsAuthority"))) {
                continue;
            }
            String edgeGuardSite = string(edge, "guardSiteId");
            JsonArray guarded = array(edge, "guardedMutations");
            if (edgeGuardSite.isEmpty() || guarded.size() == 0
                    || integer(edge, "guardedMutationCount", -1)
                    != guarded.size()) {
                continue;
            }
            for (JsonElement guardedElement : guarded) {
                if (!guardedElement.isJsonObject()) {
                    continue;
                }
                JsonObject item = guardedElement.getAsJsonObject();
                String guardSite = string(item, "guardSiteId");
                String mutationSite = string(item,
                        "guardedMutationSiteId");
                String method = string(item, "method");
                int unitIndex = integer(item, "unitIndex", -1);
                if (!edgeGuardSite.equals(guardSite)
                        || mutationSite.isEmpty() || method.isEmpty()
                        || unitIndex < 0
                        || !mutationSite.equals(method + "#u" + unitIndex)
                        || !hasBoolean(item, "requiredOutcome")) {
                    continue;
                }
                boolean requiredOutcome = item.get("requiredOutcome")
                        .getAsBoolean();
                GuardedMutationProof proof = new GuardedMutationProof(
                        guardSite, mutationSite, method, unitIndex,
                        requiredOutcome);
                LinkedHashMap<String, GuardedMutationProof> byGuard =
                        deduped.get(mutationSite);
                if (byGuard == null) {
                    byGuard = new LinkedHashMap<>();
                    deduped.put(mutationSite, byGuard);
                }
                byGuard.put(guardSite + "::" + requiredOutcome, proof);
            }
        }
        Map<String, List<GuardedMutationProof>> result =
                new LinkedHashMap<>();
        for (Map.Entry<String, LinkedHashMap<String, GuardedMutationProof>>
                entry : deduped.entrySet()) {
            result.put(entry.getKey(), new ArrayList<>(
                    entry.getValue().values()));
        }
        return result;
    }

    private static RuntimeGuardExclusion runtimeGuardExclusion(
            List<GuardedMutationProof> proofs, JsonArray branchMappings) {
        if (proofs == null || proofs.isEmpty()) {
            return null;
        }
        for (GuardedMutationProof proof : proofs) {
            List<JsonObject> observed = new ArrayList<>();
            for (JsonElement element : branchMappings) {
                if (element.isJsonObject()
                        && proof.guardSiteId.equals(string(
                        element.getAsJsonObject(), "siteId"))) {
                    observed.add(element.getAsJsonObject());
                }
            }
            if (observed.isEmpty()) {
                continue;
            }
            Set<Integer> occurrences = new LinkedHashSet<>();
            int maximumOccurrence = 0;
            boolean complete = true;
            for (JsonObject mapping : observed) {
                int occurrence = integer(mapping, "occurrence", -1);
                if (occurrence < 1 || !occurrences.add(occurrence)
                        || !proof.method.equals(string(mapping, "method"))
                        || !hasBoolean(mapping, "observedOutcome")
                        || !hasBoolean(mapping, "effectiveOutcome")
                        || !hasBoolean(mapping, "outcome")
                        || !hasBoolean(mapping, "overrideApplied")
                        || mapping.get("overrideApplied").getAsBoolean()
                        || mapping.get("observedOutcome").getAsBoolean()
                        != mapping.get("effectiveOutcome").getAsBoolean()
                        || mapping.get("observedOutcome").getAsBoolean()
                        != mapping.get("outcome").getAsBoolean()) {
                    complete = false;
                    break;
                }
                maximumOccurrence = Math.max(maximumOccurrence, occurrence);
                if (mapping.get("observedOutcome").getAsBoolean()
                        == proof.requiredOutcome) {
                    complete = false;
                    break;
                }
            }
            if (!complete || maximumOccurrence != occurrences.size()) {
                continue;
            }
            boolean contiguous = true;
            for (int occurrence = 1; occurrence <= maximumOccurrence;
                    occurrence++) {
                if (!occurrences.contains(occurrence)) {
                    contiguous = false;
                    break;
                }
            }
            if (contiguous) {
                return new RuntimeGuardExclusion(proof,
                        maximumOccurrence);
            }
        }
        return null;
    }

    private static boolean hasBoolean(JsonObject object, String name) {
        return object.has(name) && object.get(name).isJsonPrimitive()
                && object.get(name).getAsJsonPrimitive().isBoolean();
    }

    private static void addToSet(Map<String, Set<String>> values,
                                 String key, String value) {
        Set<String> items = values.get(key);
        if (items == null) {
            items = new LinkedHashSet<>();
            values.put(key, items);
        }
        items.add(value);
    }

    private static JsonArray strings(Iterable<String> values) {
        JsonArray result = new JsonArray();
        for (String value : values) {
            result.add(value);
        }
        return result;
    }

    private static boolean isVoidMethodSignature(String signature) {
        if (signature == null) {
            return false;
        }
        String value = signature.trim();
        int colon = value.indexOf(':');
        int arguments = value.indexOf('(', colon + 1);
        if (colon < 0 || arguments < 0) {
            return false;
        }
        String declaration = value.substring(colon + 1, arguments).trim();
        return declaration.startsWith("void ");
    }

    private static boolean isConcreteFalseBoolean(JsonElement expression) {
        if (expression == null || expression.isJsonNull()) {
            return false;
        }
        if (expression.isJsonPrimitive()
                && expression.getAsJsonPrimitive().isBoolean()) {
            return !expression.getAsBoolean();
        }
        if (!expression.isJsonObject()) {
            return false;
        }
        JsonObject value = expression.getAsJsonObject();
        return "ConstExpr".equals(string(value, "_type"))
                && "Z".equals(string(value, "_java_type"))
                && "Y_Z_0".equals(string(value, "_exp"));
    }

    private static boolean isPotentialMapMutation(String method) {
        return "putIfAbsent".equals(method)
                || "replace".equals(method)
                || "replaceAll".equals(method)
                || "compute".equals(method)
                || "computeIfAbsent".equals(method)
                || "computeIfPresent".equals(method)
                || "merge".equals(method);
    }

    private static JsonElement expressionOrNull(JsonElement value) {
        if (value == null || value.isJsonNull()) {
            JsonObject nullExpression = new JsonObject();
            nullExpression.addProperty("_type", "SymbolExpression");
            nullExpression.addProperty("_java_type", "");
            nullExpression.addProperty("_exp", "N");
            return nullExpression;
        }
        return value.deepCopy();
    }

    private static PathAdmissionPolicy pathAdmissionPolicy(
            JsonObject region, JsonObject activation) {
        Set<String> methodKeys = new LinkedHashSet<>();
        List<String> boundaries = new ArrayList<>();
        JsonArray activationMethods = array(activation,
                "requestedOutputMethods");
        boolean outputSliceRestricted = RegionCaptureGoal.from(activation)
                .isOutputClosure()
                && activationMethods.size() > 0;
        if (outputSliceRestricted) {
            collectMethods(methodKeys, activationMethods);
        } else {
            collectMethods(methodKeys, array(region, "methods"));
            collectMethod(methodKeys, string(region, "rootMethod"));
            collectMethod(methodKeys, string(region, "anchorMethod"));
            collectMethods(methodKeys, activationMethods);
        }
        // Activation files can be regenerated independently of region JSON.
        // Its root is therefore admitted as an explicit fallback identity.
        collectMethod(methodKeys, string(activation, "rootMethod"));
        return new PathAdmissionPolicy(methodKeys, boundaries,
                outputSliceRestricted
                        ? "REQUESTED_OUTPUT_SLICE_METHOD"
                        : "REGION_METHOD");
    }

    private static void collectMethods(Set<String> result, JsonArray methods) {
        for (JsonElement element : methods) {
            if (element.isJsonPrimitive()) {
                collectMethod(result, element.getAsString());
            }
        }
    }

    private static void collectMethod(Set<String> result, String signature) {
        String key = ConcolicCodePosition.sootMethodKey(signature);
        if (!key.isEmpty()) {
            result.add(key);
        }
    }

    private static String codePosition(JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) {
            return "";
        }
        return string(condition.getAsJsonObject(), "_code_position");
    }

    /**
     * Rejects a capture whose raw VM path condition contains branches from
     * GraphChecker's Java runtime hooks.  Those branches are instrumentation
     * bookkeeping, not constraints of the selected application region.  It
     * is deliberately not enough for semantic normalization to filter them:
     * their presence means the capture boundary itself was not isolated.
     */
    private static RuntimePathContamination runtimePathContamination(
            JsonArray pathCondition) {
        JsonArray conditionIndexes = new JsonArray();
        JsonArray codePositions = new JsonArray();
        for (int index = 0; index < pathCondition.size(); index++) {
            Set<String> positions = new LinkedHashSet<>();
            collectCodePositions(pathCondition.get(index), positions);
            boolean contaminated = false;
            for (String position : positions) {
                if (isGraphCheckerRuntimePosition(position)) {
                    codePositions.add(position);
                    contaminated = true;
                }
            }
            if (contaminated) {
                conditionIndexes.add(index);
            }
        }
        return new RuntimePathContamination(pathCondition.size(),
                conditionIndexes, codePositions);
    }

    private static void collectCodePositions(JsonElement expression,
                                             Set<String> result) {
        if (expression == null || expression.isJsonNull()) {
            return;
        }
        if (expression.isJsonArray()) {
            for (JsonElement item : expression.getAsJsonArray()) {
                collectCodePositions(item, result);
            }
            return;
        }
        if (!expression.isJsonObject()) {
            return;
        }
        for (Map.Entry<String, JsonElement> entry
                : expression.getAsJsonObject().entrySet()) {
            JsonElement value = entry.getValue();
            if ("_code_position".equals(entry.getKey())
                    && value != null && value.isJsonPrimitive()
                    && value.getAsJsonPrimitive().isString()) {
                result.add(value.getAsString());
            } else {
                collectCodePositions(value, result);
            }
        }
    }

    private static boolean isGraphCheckerRuntimePosition(String position) {
        String method = ConcolicCodePosition.vmMethodKey(position);
        if (method.isEmpty()) {
            method = ConcolicCodePosition.sootMethodKey(position);
        }
        int separator = method.lastIndexOf('#');
        String owner = separator < 0 ? "" : method.substring(0, separator);
        return owner.equals("edu.uva.liftlab.graphchecker.runtime")
                || owner.startsWith(
                "edu.uva.liftlab.graphchecker.runtime.");
    }

    private static JsonObject diagnostic(JsonObject raw, String code,
                                         String detail) {
        JsonObject value = new JsonObject();
        value.addProperty("code", code);
        value.addProperty("detail", detail);
        value.addProperty("activationId", string(raw, "activationId"));
        value.addProperty("regionId", string(raw, "regionId"));
        value.addProperty("event", string(raw, "event"));
        return value;
    }

    private static ReplayAdmission replayAdmission(JsonObject raw,
                                                   JsonObject activation,
                                                   JsonObject region,
                                                   RegionCaptureGoal goal) {
        String phase = strictString(activation, "executionPhase");
        JsonArray expectedMaterializations = array(activation,
                "replayMaterializations");
        JsonArray appliedMaterializations = array(raw,
                "replayMaterializationsApplied");
        JsonArray expectedAssignments = array(activation,
                "modelAssignments");
        JsonArray appliedAssignments = array(raw,
                "modelAssignmentsApplied");
        boolean outputPathFlip = "REPLAY_OUTPUT_PATH_FLIP".equals(phase);
        boolean replayPhase = outputPathFlip
                || "REPLAY_DIRECTED_TARGET".equals(phase)
                || "REPLAY_REBASED_TARGET".equals(phase);
        boolean required = Boolean.TRUE.equals(strictBoolean(activation,
                "targetReplayRequired"))
                || replayPhase
                || expectedMaterializations.size() > 0
                || appliedMaterializations.size() > 0
                || expectedAssignments.size() > 0
                || appliedAssignments.size() > 0;
        JsonArray failures = new JsonArray();
        // A target seed is solver provenance, not merely a diagnostic trace.
        // Its observed path condition is therefore subject to the same
        // no-override rule as the later directed replay.  In particular, a
        // --force-branch-validation plan must never become a seed summary.
        if (bool(raw, "branchOverrideUsed", false)
                || hasAppliedBranchOverride(array(raw, "branchMappings"))) {
            failures.add("BRANCH_OVERRIDE_USED");
        }
        if (array(activation, "forcedBranches").size() > 0
                || array(raw, "forcedBranches").size() > 0
                || bool(raw, "forcedBranchUsed", false)
                || integer(raw, "forcedBranchCount", 0) > 0) {
            failures.add("FORCED_BRANCH_PLAN_OR_RESULT_PRESENT");
        }
        if (failures.size() > 0) {
            return new ReplayAdmission(required, false, failures, "NONE");
        }
        if (!required) return new ReplayAdmission(false, true, failures,
                "OBSERVED_UNFORCED_TARGET_SEED_PATH_ONLY");

        if (!Boolean.FALSE.equals(strictBoolean(raw,
                "branchOverrideUsed"))) {
            failures.add("BRANCH_OVERRIDE_ATTESTATION_MISSING_OR_MALFORMED");
        }

        JsonElement replayContract = activation.get("replayContract");
        if (replayContract != null) {
            validateReplayContractObservation(raw, replayContract,
                    failures);
            String activationQueryKey = strictString(activation,
                    "pathQueryKey");
            if (activationQueryKey.isEmpty()
                    || !activationQueryKey.equals(strictString(raw,
                    "pathQueryKey"))) {
                failures.add("PATH_QUERY_KEY_MISMATCH");
            }
        } else {
            // Kept temporarily for non-canonical unit fixtures.  Production
            // path-flip activations carry exactly one replayContract; this
            // legacy branch is removed with those fixtures below.
            JsonObject target = object(activation, "targetBranch");
            if (target.size() == 0 || !observedTargetBranch(
                    array(raw, "branchMappings"), target)) {
                failures.add("DIRECTED_TARGET_BRANCH_NOT_OBSERVED");
            }
            boolean validProvenance = outputPathFlip
                    ? validOutputPathFlipProvenance(raw, activation, target)
                    : validDirectedTargetQuery(activation, target);
            if (!validProvenance) {
                failures.add("DIRECTED_TARGET_QUERY_PROVENANCE_MISSING");
            }
        }

        if (expectedMaterializations.size() != appliedMaterializations.size()) {
            failures.add("REPLAY_MATERIALIZATION_COUNT_MISMATCH");
        }
        for (JsonElement expected : expectedMaterializations) {
            if (!expected.isJsonObject() || !containsMaterialization(
                    appliedMaterializations, expected.getAsJsonObject())) {
                failures.add("EXPECTED_REPLAY_MATERIALIZATION_NOT_APPLIED");
            }
        }

        if (expectedAssignments.size() != appliedAssignments.size()
                || expectedAssignments.size() > 0
                && (!Boolean.TRUE.equals(strictBoolean(raw,
                "allModelAssignmentsApplied"))
                || !Integer.valueOf(expectedAssignments.size()).equals(
                strictInteger(raw, "modelAssignmentAppliedCount"))
                || !exactAppliedModelAssignments(expectedAssignments,
                appliedAssignments))) {
            failures.add("MODEL_ASSIGNMENTS_NOT_FULLY_APPLIED");
        }

        // A region can contain statically shared failure outputs even when
        // this activation is replaying an ordinary producer output.  Only a
        // target/fatal replay promises to observe that exception; an output
        // closure is validated by its requested output and exact path replay
        // evidence instead.
        boolean exceptionObservationRequired = goal.isTargetBranch()
                || Boolean.TRUE.equals(strictBoolean(activation,
                "targetReplayRequired"));
        Set<String> expectedExceptions = exceptionObservationRequired
                ? failureExceptions(region) : Collections.<String>emptySet();
        if (!expectedExceptions.isEmpty()) {
            if (!"THROW".equals(string(raw, "exitKind"))) {
                failures.add("FATAL_REGION_DID_NOT_THROW");
            }
            if (!containsException(raw, expectedExceptions)) {
                failures.add("EXPECTED_FATAL_EXCEPTION_NOT_IN_CHAIN");
            }
        }
        boolean valid = failures.size() == 0;
        String successAuthority = exceptionObservationRequired
                ? "SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_"
                + "EXCEPTION_OBSERVATION"
                : goal.isOutputClosure()
                ? "SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_REQUESTED_"
                + "OUTPUT_REPLAY_VALIDATION"
                : "SOLVER_MODEL_PLUS_UNFORCED_BRANCH_OBSERVATION";
        return new ReplayAdmission(true, valid, failures, valid
                ? successAuthority : "NONE");
    }

    /**
     * Revalidates the immutable witness stream once at the importer trust
     * boundary.  The replay contract derives the target polarity itself, so
     * no targetBranch/expectedPrefix/negatedCondition aliases participate in
     * admission.
     */
    private static void validateReplayContractObservation(
            JsonObject raw, JsonElement encodedContract,
            JsonArray failures) {
        if (!encodedContract.isJsonObject()) {
            failures.add("REPLAY_CONTRACT_MALFORMED");
            return;
        }
        final BranchReplayContract contract;
        try {
            contract = BranchReplayContract.fromJson(
                    encodedContract.getAsJsonObject());
        } catch (IllegalArgumentException malformed) {
            failures.add("REPLAY_CONTRACT_MALFORMED:"
                    + malformed.getMessage());
            return;
        }
        List<BranchWitness> observed = new ArrayList<>();
        for (JsonElement element : array(raw, "branchMappings")) {
            if (!element.isJsonObject()) continue;
            BranchWitness witness = branchWitness(element.getAsJsonObject());
            if (witness != null) observed.add(witness);
        }
        BranchReplayObservationValidator.Result validation =
                BranchReplayObservationValidator.validate(contract,
                        observed);
        if (!validation.valid()) {
            for (String failure : validation.failures()) {
                failures.add("BRANCH_REPLAY_CONTRACT:" + failure);
            }
        }
    }

    private static boolean validDirectedTargetQuery(JsonObject activation,
                                                    JsonObject target) {
        String instance = string(activation, "regionInstanceId");
        JsonObject query = object(activation, "directedTargetQuery");
        JsonObject context = object(query, "symbolicContext");
        return !instance.isEmpty()
                && instance.equals(string(context, "regionInstanceId"))
                && string(activation, "activationId").equals(string(query,
                "activationId"))
                && string(activation, "regionId").equals(string(query,
                "regionId"))
                && string(target, "siteId").equals(string(query, "siteId"))
                && integer(target, "occurrence", -1) == integer(query,
                "occurrence", -2)
                && bool(target, "desiredOutcome", false) == bool(query,
                "desiredOutcome", true)
                && bool(query, "readyForSolver", false)
                && query.has("originalTargetCondition")
                && query.has("negatedTargetCondition")
                && array(query, "constraints").size() > 0;
    }

    private static boolean validOutputPathFlipProvenance(
            JsonObject raw, JsonObject activation, JsonObject target) {
        String activationId = strictString(activation, "activationId");
        String pathQueryKey = strictString(activation, "pathQueryKey");
        JsonElement prefix = activation.get("expectedBranchPrefix");
        Integer occurrence = strictInteger(target, "occurrence");
        Boolean desired = strictBoolean(target, "desiredOutcome");
        return !activationId.isEmpty() && !pathQueryKey.isEmpty()
                && pathQueryKey.equals(strictString(raw, "pathQueryKey"))
                && "REPLAY_OUTPUT_PATH_FLIP".equals(strictString(
                activation, "executionPhase"))
                && prefix != null && prefix.isJsonArray()
                && !strictString(target, "siteId").isEmpty()
                && occurrence != null && occurrence > 0
                && desired != null
                && Boolean.TRUE.equals(strictBoolean(target,
                "validationOnly"))
                && Boolean.FALSE.equals(strictBoolean(target,
                "branchOverrideAllowed"))
                && Boolean.TRUE.equals(strictBoolean(activation,
                "branchOverrideProhibited"))
                && array(activation, "forcedBranches").size() == 0
                && array(activation, "replayMaterializations").size() == 0;
    }

    private static InputAdmission inputAdmission(JsonObject raw,
                                                 JsonObject activation,
                                                 boolean outputClosure,
                                                 StaticHeapTransformerCoverage
                                                         staticCoverage,
                                                 JsonArray pathCondition,
                                                 OutputExpressionExtraction
                                                         outputExtraction) {
        if (!outputClosure) return new InputAdmission(true,
                new LinkedHashSet<String>(), new LinkedHashSet<String>(),
                new LinkedHashSet<String>(), new LinkedHashSet<String>(),
                new LinkedHashSet<String>(),
                new LinkedHashSet<String>(), new JsonArray(),
                new LinkedHashSet<String>(),
                new JsonArray(), new JsonArray());
        Set<String> globalRequired = primitiveStrings(array(object(activation,
                "requestedOutputSlice"), "inputPorts"));
        Set<String> required = new LinkedHashSet<>(globalRequired);
        Set<String> observed = primitiveStrings(array(raw,
                "symbolizedInputs"));
        Set<String> admittedObservedInputs =
                exactObservedContainerInputs(raw, activation);
        Set<String> scheduledConcreteFallbacks = actionSymbols(array(
                activation, "concreteFallbacks"));
        Set<String> admittedConcreteFallbacks = new LinkedHashSet<>();
        Set<String> missing = new LinkedHashSet<>();
        Set<String> pathInactive = new LinkedHashSet<>();
        JsonArray pathInactiveProofs = new JsonArray();
        Set<String> admittedVmIntrinsicPlaceholders =
                new LinkedHashSet<>();
        JsonArray unforcedEnvironmentValidationRequirements =
                new JsonArray();
        JsonArray placeholderFailures = new JsonArray();
        for (String requiredInput : globalRequired) {
            boolean found = coversSliceInput(observed, requiredInput)
                    || coversSliceInput(admittedObservedInputs,
                    requiredInput);
            if (coversSliceInput(scheduledConcreteFallbacks,
                    requiredInput)) {
                required.remove(requiredInput);
                admittedConcreteFallbacks.add(requiredInput);
                continue;
            }
            JsonObject inactiveProof = found ? null
                    : pathInactiveInputProof(raw, activation, requiredInput,
                    staticCoverage);
            if (inactiveProof == null && !found) {
                inactiveProof = PathRelationInputClosure
                        .proveGuardedConstantUnusedInput(
                                activation, requiredInput, pathCondition,
                                outputExtraction.expressions,
                                outputExtraction.complete,
                                outputExtraction.authority,
                                requestedOutputSliceOperationallyAdmitted(
                                        activation));
            }
            if (inactiveProof != null) {
                required.remove(requiredInput);
                pathInactive.add(requiredInput);
                pathInactiveProofs.add(inactiveProof);
                continue;
            }
            VmIntrinsicPlaceholderAdmission placeholderAdmission =
                    vmIntrinsicPlaceholderAdmission(raw, activation,
                            requiredInput);
            if (placeholderAdmission.applicable && found) {
                missing.add(requiredInput);
                placeholderFailures.add(
                        "VM_INTRINSIC_PLACEHOLDER_MUST_REMAIN_UNFORCED:"
                                + requiredInput);
            } else if (placeholderAdmission.admitted) {
                admittedVmIntrinsicPlaceholders.add(requiredInput);
                unforcedEnvironmentValidationRequirements.add(
                        placeholderAdmission.requirement.deepCopy());
            } else if (placeholderAdmission.applicable) {
                missing.add(requiredInput);
                if (!placeholderAdmission.failure.isEmpty()) {
                    placeholderFailures.add(placeholderAdmission.failure);
                }
            } else if (!found) {
                missing.add(requiredInput);
            }
        }
        JsonArray failures = new JsonArray();
        if (!requestedOutputSliceOperationallyAdmitted(activation)) {
            failures.add("REQUESTED_OUTPUT_SLICE_INCOMPLETE");
        }
        for (JsonElement placeholderFailure : placeholderFailures) {
            failures.add(placeholderFailure.deepCopy());
        }
        for (String symbol : missing) {
            failures.add("SLICE_INPUT_NOT_SYMBOLIZED:" + symbol);
        }
        for (JsonElement unresolved : array(raw, "unresolvedInputs")) {
            if (!unresolved.isJsonPrimitive()) continue;
            String detail = unresolved.getAsString();
            for (String symbol : required) {
                if (detail.equals(symbol) || detail.startsWith(symbol + ":")
                        || detail.startsWith(symbol + ".")) {
                    failures.add("SLICE_INPUT_UNRESOLVED:" + detail);
                    break;
                }
            }
        }
        return new InputAdmission(failures.size() == 0, globalRequired,
                required, observed, admittedObservedInputs,
                admittedConcreteFallbacks,
                pathInactive, pathInactiveProofs,
                admittedVmIntrinsicPlaceholders,
                unforcedEnvironmentValidationRequirements, failures);
    }

    private static Set<String> exactObservedContainerInputs(
            JsonObject raw, JsonObject activation) {
        Set<String> result = new LinkedHashSet<>();
        Map<String, List<JsonObject>> actions = new LinkedHashMap<>();
        for (JsonElement element : runtimeMaterializationActions(activation)) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            String mode = string(action, "bindingMode");
            String symbol = string(action, "symbol");
            if (symbol.isEmpty()
                    || !("MAP_STATE_INPUT_OBSERVATION".equals(mode)
                    || "CONTAINER_INPUT_OBSERVATION".equals(mode))) {
                continue;
            }
            List<JsonObject> same = actions.get(symbol);
            if (same == null) {
                same = new ArrayList<>();
                actions.put(symbol, same);
            }
            same.add(action);
        }
        for (Map.Entry<String, List<JsonObject>> entry : actions.entrySet()) {
            if (entry.getValue().size() != 1) continue;
            JsonObject action = entry.getValue().get(0);
            long selectedToken = exactFirstContainerSelectionToken(
                    raw, action);
            if (selectedToken <= 0L) continue;
            if ("MAP_STATE_INPUT_OBSERVATION".equals(
                    string(action, "bindingMode"))
                    && exactMapStateInputRecords(raw, activation, action,
                    selectedToken).size() != 1) {
                continue;
            }
            result.add(entry.getKey());
        }
        return result;
    }

    private static long exactFirstContainerSelectionToken(
            JsonObject raw, JsonObject action) {
        String symbol = string(action, "symbol");
        String cell = string(action, "cell");
        String authority = string(action, "containerObservationAuthority");
        long token = -1L;
        int matches = 0;
        for (JsonElement element : array(raw, "runtimeApproximations")) {
            if (!element.isJsonObject()) continue;
            JsonObject evidence = element.getAsJsonObject();
            long candidate = longInteger(evidence,
                    "selectedObjectToken", -1L);
            if (integer(evidence, "schemaVersion", -1) == 1
                    && "BOUNDED_CONTAINER_INPUT_OBSERVATION".equals(
                    string(evidence, "kind"))
                    && authority.equals(string(evidence, "authority"))
                    && !authority.isEmpty()
                    && symbol.equals(string(evidence, "inputSymbol"))
                    && cell.equals(string(evidence, "inputCell"))
                    && "FIRST_MATCHING_CONTAINER_SELECTED".equals(
                    string(evidence, "outcome"))
                    && !string(evidence, "siteId").isEmpty()
                    && candidate > 0L
                    && bool(evidence, "complete", false)) {
                matches++;
                token = candidate;
            }
        }
        return matches == 1 ? token : -1L;
    }

    private static List<JsonObject> exactMapStateInputRecords(
            JsonObject raw, JsonObject activation, JsonObject action,
            long selectedToken) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : array(raw, "runtimeHeapObservations")) {
            if (!element.isJsonObject()) continue;
            JsonObject record = element.getAsJsonObject();
            if (completeMapStateInputObservation(record, activation, action,
                    selectedToken)) {
                result.add(record);
            }
        }
        return result;
    }

    private static boolean completeMapStateInputObservation(
            JsonObject record, JsonObject activation, JsonObject action,
            long selectedToken) {
        String activationId = string(activation, "activationId");
        String symbol = string(action, "symbol");
        String cell = string(action, "cell");
        String authority = string(action, "containerObservationAuthority");
        String site = string(record, "siteId");
        int unit = integer(record, "originUnitIndex", -1);
        int entryCount = integer(record, "entryCount", -1);
        int bound = integer(record, "finiteEntryBound", -1);
        long token = longInteger(record, "mapObjectToken", -1L);
        JsonArray keys = array(record, "keyExpressions");
        JsonArray runtimeKeys = array(record, "mapKeys");
        JsonArray valueTokens = array(record, "valueObjectTokens");
        JsonArray entries = array(record, "entries");
        if (integer(record, "schemaVersion", -1) != 1
                || !"MAP_STATE_INPUT_OBSERVATION".equals(
                string(record, "kind"))
                || !symbol.equals(string(record, "inputSymbol"))
                || !symbol.equals(string(record, "symbol"))
                || !cell.equals(string(record, "inputCell"))
                || !"MAP_STATE_INPUT_OBSERVATION".equals(
                string(record, "bindingMode"))
                || !authority.equals(string(record, "selectionAuthority"))
                || authority.isEmpty()
                || bool(record, "modelControllable", true)
                || bool(record, "vmReferenceSymbolized", true)
                || string(record, "originMethod").isEmpty() || unit < 0
                || !site.equals(string(record, "originMethod") + "#u"
                + unit)
                || !string(record, "observationId").equals(
                "MAP_STATE_INPUT:" + site + "#" + symbol)
                || longInteger(record, "eventSequence", -1L) <= 0L
                || token <= 0L || token != selectedToken
                || token != longInteger(record,
                "backingMapObjectToken", -1L)
                || token != longInteger(record,
                "mapStateInputObjectToken", -1L)
                || !bool(record, "identityBindingComplete", false)
                || !bool(record, "snapshotComplete", false)
                || !bool(record, "mapStateInputBindingComplete", false)
                || !bool(record, "complete", false)
                || !"ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(record, "objectTokenAuthority"))
                || !activationId.equals(string(record,
                "objectTokenScope"))
                || !symbol.equals(string(record, "mapStateInputSymbol"))
                || !cell.equals(string(record, "mapStateInputCell"))
                || !string(record, "observationId").equals(string(record,
                "mapStateInputObservationId"))
                || !authority.equals(string(record,
                "mapStateInputBindingAuthority"))
                || !"SAME_FIELD_HOOK_STABLE_BOUNDED_ENTRY_SET_SNAPSHOT_V1"
                .equals(string(record, "snapshotAuthority"))
                || string(record, "mapImplementationClass").isEmpty()
                || !string(record, "mapImplementationClass").equals(
                string(record, "valueClass"))
                || !bool(record, "accessOwnerObjectTokenKnown", false)
                || !bool(record, "leafOwnerObjectTokenKnown", false)
                || longInteger(record,
                "accessOwnerObjectToken", -1L) <= 0L
                || longInteger(record, "accessOwnerObjectToken", -1L)
                != longInteger(record, "leafOwnerObjectToken", -2L)
                || array(record, "path").size() == 0
                || entryCount < 0 || bound < entryCount || bound > 4096
                || keys.size() != entryCount
                || runtimeKeys.size() != entryCount
                || valueTokens.size() != entryCount
                || entries.size() != entryCount
                || integer(record, "collectionSize", -1) != entryCount
                || !bool(record, "available", false)
                || !bool(record, "valueObjectTokenKnown", false)
                || longInteger(record, "valueObjectToken", -1L) != token) {
            return false;
        }
        Set<String> selectors = new LinkedHashSet<>();
        for (int index = 0; index < entryCount; index++) {
            JsonElement key = keys.get(index);
            JsonElement entryElement = entries.get(index);
            if (!key.isJsonObject() || !entryElement.isJsonObject()) {
                return false;
            }
            JsonObject row = entryElement.getAsJsonObject();
            String selector = finiteSnapshotObservedKey(
                    key.getAsJsonObject());
            long valueToken = strictNonNegativeLong(valueTokens.get(index));
            if (selector.isEmpty() || !selectors.add(selector)
                    || integer(row, "index", -1) != index
                    || !key.equals(row.get("keyExpression"))
                    || valueToken < 0L
                    || valueToken != longInteger(row,
                    "valueObjectToken", -1L)
                    || (valueToken == 0L) != bool(row,
                    "valueWasNull", false)) {
                return false;
            }
        }
        Set<String> unmatched = new LinkedHashSet<>(selectors);
        for (JsonElement runtimeKey : runtimeKeys) {
            String match = "";
            for (String selector : unmatched) {
                if (finiteSnapshotRuntimeKeyMatches(runtimeKey, selector)) {
                    if (!match.isEmpty()) return false;
                    match = selector;
                }
            }
            if (match.isEmpty()) return false;
            unmatched.remove(match);
        }
        if (!unmatched.isEmpty()) return false;
        return true;
    }

    private static Set<String> actionSymbols(JsonArray actions) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : actions) {
            if (!element.isJsonObject()) continue;
            String symbol = firstNonBlank(string(element.getAsJsonObject(),
                    "symbol"), string(element.getAsJsonObject(),
                    "inputPort"));
            if (!symbol.isEmpty()) result.add(symbol);
        }
        return result;
    }

    private static boolean coversSliceInput(Set<String> candidates,
                                             String requiredInput) {
        for (String candidate : candidates) {
            if (candidate.equals(requiredInput)
                    || candidate.startsWith(requiredInput + ".")) {
                return true;
            }
        }
        return false;
    }

    /**
     * Proves that one globally selected slice input has no effect on this
     * concrete runtime path.  This is intentionally narrower than ordinary
     * liveness: every statically complete sink for the input must be an exact
     * requested-state transformer, and every such sink must be excluded by a
     * contiguous, unforced runtime observation of a dominating guard.  A
     * guard whose own condition depends on the missing input cannot discharge
     * that input's demand.
     */
    private static JsonObject pathInactiveInputProof(
            JsonObject raw, JsonObject activation, String inputPort,
            StaticHeapTransformerCoverage coverage) {
        if (coverage == null || !coverage.applicable
                || !coverage.exactTransformerContract
                || !coverage.transformerContractValid
                || unresolvedInput(raw, inputPort)) {
            return null;
        }
        JsonObject slice = object(activation, "requestedOutputSlice");
        Set<String> sinkSites = new LinkedHashSet<>();
        Set<String> dependentGuardSites = new LinkedHashSet<>();
        int bindingCount = 0;
        for (JsonElement element : array(slice, "inputBindings")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject binding = element.getAsJsonObject();
            if (!inputPort.equals(string(binding, "inputPort"))) {
                continue;
            }
            bindingCount++;
            if (!"STATIC_FORWARD_CAUSAL_CLOSURE_TO_EXACT_"
                    .concat("REQUESTED_STATE_TRANSFORMERS").equals(
                            string(binding,
                                    "requestedStateTransformerSinkAuthority"))
                    || !hasBoolean(binding,
                    "requestedStateTransformerSinkClosureComplete")
                    || !binding.get(
                    "requestedStateTransformerSinkClosureComplete")
                    .getAsBoolean()
                    || !hasBoolean(binding,
                    "requestedStateTransformerSinkExclusive")
                    || !binding.get(
                    "requestedStateTransformerSinkExclusive")
                    .getAsBoolean()
                    || !binding.has(
                    "requestedStateTransformerSinkSites")
                    || !binding.has(
                    "requestedStateTransformerGuardSites")
                    || !binding.has(
                    "requestedStateTransformerUnclassifiedEdgeIds")
                    || array(binding,
                    "requestedStateTransformerUnclassifiedEdgeIds")
                    .size() != 0) {
                return null;
            }
            Set<String> bindingSinks = strictPrimitiveStrings(array(binding,
                    "requestedStateTransformerSinkSites"));
            Set<String> bindingGuards = strictPrimitiveStrings(array(binding,
                    "requestedStateTransformerGuardSites"));
            if (bindingSinks == null || bindingSinks.isEmpty()
                    || bindingGuards == null) {
                return null;
            }
            sinkSites.addAll(bindingSinks);
            dependentGuardSites.addAll(bindingGuards);
        }
        if (bindingCount == 0 || sinkSites.isEmpty()) {
            return null;
        }

        JsonArray exclusions = new JsonArray();
        String requestedPort = firstNonBlank(string(object(activation,
                "requestedOutput"), "portId"), string(object(activation,
                "requestedOutput"), "symbol"));
        for (String sinkSite : sinkSites) {
            RuntimeGuardExclusion exclusion =
                    coverage.guardExcludedWriteSites.get(sinkSite);
            if (!coverage.declaredWriteSites.contains(sinkSite)
                    || exclusion == null
                    || exclusion.observedOccurrenceCount < 1
                    || exclusion.proof.guardSiteId.isEmpty()
                    || dependentGuardSites.contains(
                    exclusion.proof.guardSiteId)) {
                return null;
            }
            exclusions.add(exclusion.toMatch(sinkSite, requestedPort));
        }
        JsonObject proof = new JsonObject();
        proof.addProperty("inputPort", inputPort);
        proof.addProperty("bindingCount", bindingCount);
        proof.add("exactTransformerSinkSites",
                GSON.toJsonTree(sinkSites));
        proof.add("inputDependentGuardSites",
                GSON.toJsonTree(dependentGuardSites));
        proof.add("runtimeGuardExclusions", exclusions);
        proof.addProperty("authority",
                "STATIC_COMPLETE_INPUT_TO_EXACT_TRANSFORMER_SINKS_PLUS_"
                        + "RUNTIME_STRICT_GUARD_EXCLUSION");
        return proof;
    }

    private static boolean unresolvedInput(JsonObject raw,
                                           String inputPort) {
        for (JsonElement element : array(raw, "unresolvedInputs")) {
            if (!element.isJsonPrimitive()) {
                return true;
            }
            String detail = element.getAsString();
            if (detail.equals(inputPort)
                    || detail.startsWith(inputPort + ":")
                    || detail.startsWith(inputPort + ".")) {
                return true;
            }
        }
        return false;
    }

    private static Set<String> strictPrimitiveStrings(JsonArray values) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement value : values) {
            if (!value.isJsonPrimitive()
                    || !value.getAsJsonPrimitive().isString()) {
                return null;
            }
            String text = value.getAsString();
            if (text.isEmpty() || !result.add(text)) {
                return null;
            }
        }
        return result;
    }

    /**
     * Admits the one VM-owned wall-clock input that the customized JDK
     * represents as a PlaceholderExpression.  This is deliberately separate
     * from runtime symbolization admission: the value is existential in SMT
     * and must remain unforced during replay.
     */
    private static VmIntrinsicPlaceholderAdmission
    vmIntrinsicPlaceholderAdmission(JsonObject raw, JsonObject activation,
                                    String requiredInput) {
        JsonArray materializations = array(activation, "materializations");
        List<JsonObject> samePort = new ArrayList<>();
        boolean placeholderCandidate = false;
        for (JsonElement element : materializations) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject action = element.getAsJsonObject();
            if (!requiredInput.equals(string(action, "symbol"))) {
                continue;
            }
            samePort.add(action);
            placeholderCandidate |= "VM_INTRINSIC_PLACEHOLDER".equals(
                    string(action, "bindingMode"))
                    || "ENVIRONMENT".equals(string(action, "sourceKind"))
                    || "ENVIRONMENT_MODEL".equals(
                    string(action, "location"))
                    || action.has("placeholderFunction")
                    || action.has("captureAuthority");
        }
        for (JsonElement element : array(activation, "symbolize")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject action = element.getAsJsonObject();
            if (requiredInput.equals(string(action, "symbol"))
                    && ("ENVIRONMENT".equals(
                    string(action, "sourceKind"))
                    || "ENVIRONMENT_MODEL".equals(
                    string(action, "location"))
                    || SymbolicEnvironment.isCurrentTimeMillisReturn(
                    string(action, "cell")))) {
                placeholderCandidate = true;
            }
        }
        if (!placeholderCandidate) {
            return VmIntrinsicPlaceholderAdmission.notApplicable();
        }
        if (samePort.size() != 1
                || !exactCurrentTimeMillisBinding(samePort.get(0))) {
            return VmIntrinsicPlaceholderAdmission.failure(
                    "VM_INTRINSIC_PLACEHOLDER_BINDING_INVALID:"
                            + requiredInput);
        }

        Set<String> evidenceIdentities = new LinkedHashSet<>();
        collectCurrentTimeMillisPlaceholderEvidence(object(raw,
                "engineSummary"), evidenceIdentities);
        if (evidenceIdentities.isEmpty()) {
            return VmIntrinsicPlaceholderAdmission.failure(
                    "VM_INTRINSIC_PLACEHOLDER_EVIDENCE_MISSING_OR_INVALID:"
                            + requiredInput);
        }

        JsonObject action = samePort.get(0);
        JsonObject requirement = new JsonObject();
        requirement.addProperty("kind",
                "UNFORCED_ENVIRONMENT_VALIDATION_REQUIREMENT");
        requirement.addProperty("inputPort", requiredInput);
        requirement.addProperty("cell", string(action, "cell"));
        requirement.addProperty("sourceKind", "ENVIRONMENT");
        requirement.addProperty("bindingMode",
                "VM_INTRINSIC_PLACEHOLDER");
        requirement.addProperty("placeholderFunction",
                "currentTimeMills");
        requirement.addProperty("captureAuthority",
                "CUSTOM_JDK_SYMBOLIC_ND_FUNC");
        requirement.addProperty("modelControllable", false);
        requirement.addProperty("replayPolicy",
                "UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION");
        requirement.addProperty("evidenceAuthority",
                "CUSTOM_JDK_STRUCTURED_PLACEHOLDER_EXPRESSION");
        requirement.add("placeholderEvidenceIdentities",
                GSON.toJsonTree(evidenceIdentities));
        requirement.addProperty("required", true);
        return VmIntrinsicPlaceholderAdmission.admitted(requirement);
    }

    private static boolean exactCurrentTimeMillisBinding(JsonObject action) {
        return SymbolicEnvironment.isCurrentTimeMillisReturn(
                string(action, "cell"))
                && "ENVIRONMENT".equals(string(action, "sourceKind"))
                && "ENVIRONMENT_MODEL".equals(string(action, "location"))
                && "VM_INTRINSIC_PLACEHOLDER".equals(
                string(action, "bindingMode"))
                && "currentTimeMills".equals(
                string(action, "placeholderFunction"))
                && "CUSTOM_JDK_SYMBOLIC_ND_FUNC".equals(
                string(action, "captureAuthority"))
                && action.has("modelControllable")
                && !bool(action, "modelControllable", true)
                && "UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION".equals(
                string(action, "replayPolicy"));
    }

    private static void collectCurrentTimeMillisPlaceholderEvidence(
            JsonElement element, Set<String> identities) {
        if (element == null || element.isJsonNull()) {
            return;
        }
        if (element.isJsonArray()) {
            for (JsonElement child : element.getAsJsonArray()) {
                collectCurrentTimeMillisPlaceholderEvidence(child,
                        identities);
            }
            return;
        }
        if (!element.isJsonObject()) {
            return;
        }
        JsonObject object = element.getAsJsonObject();
        if ("PlaceholderExpression".equals(string(object, "_type"))
                && "currentTimeMills".equals(
                string(object, "_place_holder_func"))
                && positiveIntegralJsonNumber(object.get("_count"))) {
            identities.add("currentTimeMills#"
                    + object.get("_count").getAsString());
        }
        for (Map.Entry<String, JsonElement> child : object.entrySet()) {
            collectCurrentTimeMillisPlaceholderEvidence(child.getValue(),
                    identities);
        }
    }

    private static boolean positiveIntegralJsonNumber(JsonElement value) {
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isNumber()
                && value.getAsString().matches("[1-9][0-9]*");
    }

    /**
     * Turns an admitted, unforced VM intrinsic into a case-local expression
     * binding only when this normalized path uses exactly one authenticated
     * placeholder identity.  The input port is the owner; equal VM counters
     * from another execution never enter this certificate.
     */
    private static VmIntrinsicPlaceholderBindingExtraction
    vmIntrinsicPlaceholderBindings(JsonArray pathCondition,
                                   InputAdmission admission) {
        Map<String, Set<String>> usedByFunction = new LinkedHashMap<>();
        collectUsedPlaceholderIdentities(pathCondition, usedByFunction);
        List<JsonObject> candidates = new ArrayList<>();
        JsonArray failures = new JsonArray();
        for (JsonElement element
                : admission.unforcedEnvironmentValidationRequirements) {
            if (!element.isJsonObject()) {
                failures.add("VM_INTRINSIC_PLACEHOLDER_REQUIREMENT_MALFORMED");
                continue;
            }
            JsonObject requirement = element.getAsJsonObject();
            String port = string(requirement, "inputPort");
            String function = string(requirement, "placeholderFunction");
            Set<String> evidence = strictPrimitiveStrings(array(requirement,
                    "placeholderEvidenceIdentities"));
            boolean exact = "UNFORCED_ENVIRONMENT_VALIDATION_REQUIREMENT"
                    .equals(string(requirement, "kind"))
                    && bool(requirement, "required", false)
                    && admission.admittedVmIntrinsicPlaceholders.contains(port)
                    && admission.globalRequired.contains(port)
                    && admission.required.contains(port)
                    && SymbolicEnvironment.isCurrentTimeMillisReturn(
                    string(requirement, "cell"))
                    && "ENVIRONMENT".equals(string(requirement,
                    "sourceKind"))
                    && "VM_INTRINSIC_PLACEHOLDER".equals(string(requirement,
                    "bindingMode"))
                    && "currentTimeMills".equals(function)
                    && "CUSTOM_JDK_SYMBOLIC_ND_FUNC".equals(
                    string(requirement, "captureAuthority"))
                    && requirement.has("modelControllable")
                    && !bool(requirement, "modelControllable", true)
                    && "UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION".equals(
                    string(requirement, "replayPolicy"))
                    && "CUSTOM_JDK_STRUCTURED_PLACEHOLDER_EXPRESSION".equals(
                    string(requirement, "evidenceAuthority"))
                    && evidence != null && !evidence.isEmpty();
            if (!exact) {
                failures.add("VM_INTRINSIC_PLACEHOLDER_REQUIREMENT_INVALID:"
                        + port);
                continue;
            }
            Set<String> used = usedByFunction.get(function);
            if (used == null || used.size() != 1) {
                failures.add("VM_INTRINSIC_PLACEHOLDER_USED_IDENTITY_NOT_"
                        + "UNIQUE:" + port);
                continue;
            }
            String identity = used.iterator().next();
            if (!evidence.contains(identity)
                    || !identity.matches("currentTimeMills#[1-9][0-9]*")) {
                failures.add("VM_INTRINSIC_PLACEHOLDER_USED_IDENTITY_NOT_"
                        + "EVIDENCED:" + port + ":" + identity);
                continue;
            }
            int separator = identity.lastIndexOf('#');
            int count;
            try {
                count = Integer.parseInt(identity.substring(separator + 1));
            } catch (NumberFormatException invalidCount) {
                failures.add("VM_INTRINSIC_PLACEHOLDER_COUNT_INVALID:"
                        + identity);
                continue;
            }
            JsonObject binding = new JsonObject();
            binding.addProperty("schemaVersion", 1);
            binding.addProperty("kind",
                    "VM_INTRINSIC_PLACEHOLDER_PORT_BINDING");
            binding.addProperty("placeholderIdentity", identity);
            binding.addProperty("placeholderFunction", function);
            binding.addProperty("placeholderCount", count);
            binding.addProperty("inputPort", port);
            binding.addProperty("cell", string(requirement, "cell"));
            binding.addProperty("javaTypeDescriptor", "J");
            binding.addProperty("sourceKind", "ENVIRONMENT");
            binding.addProperty("bindingMode",
                    "VM_INTRINSIC_PLACEHOLDER");
            binding.addProperty("captureAuthority",
                    "CUSTOM_JDK_SYMBOLIC_ND_FUNC");
            binding.addProperty("evidenceAuthority",
                    "CUSTOM_JDK_STRUCTURED_PLACEHOLDER_EXPRESSION");
            binding.addProperty("modelControllable", false);
            binding.addProperty("replayPolicy",
                    "UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION");
            binding.addProperty("ownerAuthority",
                    "UNIQUE_USED_PLACEHOLDER_IDENTITY_TO_EXACT_SLICE_INPUT");
            binding.addProperty("required", true);
            candidates.add(binding);
        }

        Map<String, Integer> identityOwners = new LinkedHashMap<>();
        Map<String, Integer> portOwners = new LinkedHashMap<>();
        for (JsonObject candidate : candidates) {
            increment(identityOwners, string(candidate,
                    "placeholderIdentity"));
            increment(portOwners, string(candidate, "inputPort"));
        }
        JsonArray bindings = new JsonArray();
        for (JsonObject candidate : candidates) {
            String identity = string(candidate, "placeholderIdentity");
            String port = string(candidate, "inputPort");
            if (identityOwners.get(identity) != 1
                    || portOwners.get(port) != 1) {
                failures.add("VM_INTRINSIC_PLACEHOLDER_OWNER_AMBIGUOUS:"
                        + port + ":" + identity);
                continue;
            }
            bindings.add(candidate);
        }
        return new VmIntrinsicPlaceholderBindingExtraction(bindings,
                failures);
    }

    private static void increment(Map<String, Integer> counts, String key) {
        Integer previous = counts.get(key);
        counts.put(key, previous == null ? 1 : previous + 1);
    }

    private static void collectUsedPlaceholderIdentities(
            JsonElement element, Map<String, Set<String>> identities) {
        if (element == null || element.isJsonNull()) return;
        if (element.isJsonArray()) {
            for (JsonElement child : element.getAsJsonArray()) {
                collectUsedPlaceholderIdentities(child, identities);
            }
            return;
        }
        if (!element.isJsonObject()) return;
        JsonObject object = element.getAsJsonObject();
        if ("PlaceholderExpression".equals(string(object, "_type"))
                && positiveIntegralJsonNumber(object.get("_count"))) {
            String function = string(object, "_place_holder_func");
            Set<String> values = identities.get(function);
            if (values == null) {
                values = new LinkedHashSet<>();
                identities.put(function, values);
            }
            values.add(function + "#" + object.get("_count").getAsString());
        }
        for (Map.Entry<String, JsonElement> child : object.entrySet()) {
            collectUsedPlaceholderIdentities(child.getValue(), identities);
        }
    }

    private static Set<String> primitiveStrings(JsonArray values) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement value : values) {
            if (value.isJsonPrimitive()) result.add(value.getAsString());
        }
        return result;
    }

    private static boolean hasAppliedBranchOverride(JsonArray mappings) {
        for (JsonElement element : mappings) {
            if (element.isJsonObject() && bool(element.getAsJsonObject(),
                    "overrideApplied", false)) return true;
        }
        return false;
    }

    private static boolean observedTargetBranch(JsonArray mappings,
                                                JsonObject target) {
        String site = strictString(target, "siteId");
        Integer occurrence = strictInteger(target, "occurrence");
        Boolean desired = strictBoolean(target, "desiredOutcome");
        if (site.isEmpty() || occurrence == null || occurrence <= 0
                || desired == null) return false;
        int matches = 0;
        for (JsonElement element : mappings) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            if (!site.equals(strictString(mapping, "siteId"))
                    || !occurrence.equals(strictInteger(mapping,
                    "occurrence"))) continue;
            if (!desired.equals(strictBoolean(mapping,
                    "observedOutcome"))
                    || !desired.equals(strictBoolean(mapping,
                    "effectiveOutcome"))
                    || !Boolean.FALSE.equals(strictBoolean(mapping,
                    "overrideApplied"))
                    || !Boolean.TRUE.equals(strictBoolean(mapping,
                    "scheduledTarget"))
                    || !desired.equals(strictBoolean(mapping,
                    "scheduledDesiredOutcome"))
                    || !Boolean.TRUE.equals(strictBoolean(mapping,
                    "scheduledOutcomeMatched"))) {
                return false;
            }
            matches++;
        }
        return matches == 1;
    }

    private static boolean exactAppliedModelAssignments(
            JsonArray expected, JsonArray applied) {
        if (expected.size() != applied.size()) return false;
        Map<String, JsonObject> appliedByKey = new LinkedHashMap<>();
        for (JsonElement element : applied) {
            if (!element.isJsonObject()) return false;
            JsonObject row = element.getAsJsonObject();
            String key = strictString(row, "modelAssignmentKey");
            if (key.isEmpty() || appliedByKey.put(key, row) != null) {
                return false;
            }
        }
        Set<String> expectedKeys = new LinkedHashSet<>();
        for (JsonElement element : expected) {
            if (!element.isJsonObject()) return false;
            JsonObject planned = element.getAsJsonObject();
            String key = modelAssignmentKey(planned);
            JsonObject observed = appliedByKey.get(key);
            if (key.isEmpty() || !expectedKeys.add(key)
                    || observed == null
                    || !sameModelAssignmentCore(planned, observed)) {
                return false;
            }
        }
        return expectedKeys.size() == appliedByKey.size();
    }

    private static String modelAssignmentKey(JsonObject assignment) {
        String explicit = strictString(assignment, "modelAssignmentKey");
        String dynamic = strictString(assignment, "dynamicBindingId");
        String engineSymbol = strictString(assignment, "engineSymbol");
        String inputSymbol = strictString(assignment, "inputSymbol");
        String materializationPath = strictStringPath(array(assignment,
                "materializationPath"));
        if (materializationPath == null) return "";
        String derived = !dynamic.isEmpty() ? dynamic
                : !engineSymbol.isEmpty() ? engineSymbol
                : inputSymbol.isEmpty() ? ""
                : inputSymbol + ":" + materializationPath;
        return explicit.isEmpty() || explicit.equals(derived)
                ? derived : "";
    }

    private static String strictStringPath(JsonArray path) {
        StringBuilder result = new StringBuilder();
        for (JsonElement element : path) {
            if (!element.isJsonPrimitive()
                    || !element.getAsJsonPrimitive().isString()) return null;
            if (result.length() > 0) result.append('.');
            result.append(element.getAsString());
        }
        return result.toString();
    }

    private static boolean sameModelAssignmentCore(
            JsonObject planned, JsonObject applied) {
        String[] exactStrings = new String[]{"engineSymbol", "inputSymbol",
                "baseInputSymbol", "valueType", "value", "authority",
                "dynamicBindingId", "dynamicFieldSymbol",
                "nullnessSolverSymbol", "nullableStringEncodingAuthority",
                "referenceNullnessEncodingAuthority"};
        for (String field : exactStrings) {
            if (!strictString(planned, field).equals(strictString(applied,
                    field))) return false;
        }
        if (planned.has("modelIsNull")) {
            Boolean expectedNull = strictBoolean(planned, "modelIsNull");
            if (expectedNull == null || !expectedNull.equals(strictBoolean(
                    applied, "modelIsNull"))) return false;
        }
        if (planned.has("materializeAtRealDefinition")) {
            Boolean expectedRealDefinition = strictBoolean(planned,
                    "materializeAtRealDefinition");
            if (expectedRealDefinition == null
                    || !expectedRealDefinition.equals(strictBoolean(applied,
                    "materializeAtRealDefinition"))) return false;
        }
        JsonElement plannedTarget = planned.get("target");
        if (plannedTarget != null) {
            if (!plannedTarget.equals(applied.get("target"))) return false;
            String targetHash = sha256(GSON.toJson(plannedTarget));
            if (!targetHash.equals(strictString(applied,
                    "targetActionSha256"))) return false;
            String declaredHash = strictString(planned,
                    "targetActionSha256");
            if (!declaredHash.isEmpty() && !targetHash.equals(
                    declaredHash)) return false;
        }
        return true;
    }

    private static boolean containsMaterialization(JsonArray applied,
                                                   JsonObject expected) {
        for (JsonElement element : applied) {
            if (!element.isJsonObject()) continue;
            JsonObject value = element.getAsJsonObject();
            if (string(expected, "kind").equals(string(value, "kind"))
                    && string(expected, "method").equals(string(value,
                    "method"))
                    && integer(expected, "unitIndex", -1) == integer(value,
                    "unitIndex", -2)
                    && Math.max(1, integer(expected, "occurrence", 1))
                    == Math.max(1, integer(value, "occurrence", 1))
                    && string(expected, "desiredResult").equals(string(value,
                    "desiredResult"))
                    && bool(value, "solverDerived", false)) return true;
        }
        return false;
    }

    private static Set<String> failureExceptions(JsonObject region) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : array(region, "outputs")) {
            if (!element.isJsonObject()) continue;
            JsonObject output = element.getAsJsonObject();
            if (!"FAILURE_PREDICATE".equals(string(output, "kind"))) continue;
            Matcher matcher = FAILURE_EXCEPTION.matcher(string(output,
                    "cell"));
            if (matcher.find()) result.add(matcher.group(1));
        }
        return result;
    }

    private static boolean containsException(JsonObject raw,
                                             Set<String> expected) {
        if (expected.contains(string(raw, "exceptionType"))) return true;
        for (JsonElement element : array(raw, "exceptionChain")) {
            if (element.isJsonObject() && expected.contains(string(
                    element.getAsJsonObject(), "type"))) return true;
        }
        return false;
    }

    private static void writeCacheEntry(Path directory, String key,
                                        JsonObject summary) throws IOException {
        Files.createDirectories(directory);
        Path target = directory.resolve(key + ".json");
        if (Files.isRegularFile(target)) {
            return;
        }
        writeAtomic(target, (GSON.toJson(summary) + System.lineSeparator())
                .getBytes(StandardCharsets.UTF_8));
    }

    private static void writeJsonlAtomic(Path target, List<JsonObject> rows)
            throws IOException {
        StringBuilder builder = new StringBuilder();
        for (JsonObject row : rows) {
            builder.append(GSON.toJson(row)).append(System.lineSeparator());
        }
        writeAtomic(target, builder.toString().getBytes(StandardCharsets.UTF_8));
    }

    private static void writeAtomic(Path target, byte[] contents) throws IOException {
        Path absolute = target.toAbsolutePath();
        Path parent = absolute.getParent();
        if (parent != null) {
            Files.createDirectories(parent);
        }
        Path temporary = Files.createTempFile(parent, absolute.getFileName().toString(),
                ".tmp");
        Files.write(temporary, contents);
        try {
            Files.move(temporary, absolute, StandardCopyOption.ATOMIC_MOVE,
                    StandardCopyOption.REPLACE_EXISTING);
        } catch (AtomicMoveNotSupportedException ignored) {
            Files.move(temporary, absolute, StandardCopyOption.REPLACE_EXISTING);
        }
    }

    private static Map<String, JsonObject> index(List<JsonObject> rows,
                                                  String keyField) {
        Map<String, JsonObject> result = new LinkedHashMap<>();
        for (JsonObject row : rows) {
            String key = string(row, keyField);
            if (!key.isEmpty()) {
                result.put(key, row);
            }
        }
        return result;
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
                if (line.trim().isEmpty()) {
                    continue;
                }
                JsonElement parsed = JsonParser.parseString(line);
                if (parsed.isJsonObject()) {
                    result.add(parsed.getAsJsonObject());
                }
            }
        }
        return result;
    }

    private static String sha256(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(value.getBytes(StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte item : bytes) {
                result.append(String.format("%02x", item & 0xff));
            }
            return result.toString();
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException(impossible);
        }
    }

    private static JsonObject object(JsonObject parent, String field) {
        JsonElement value = parent == null ? null : parent.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static JsonArray array(JsonObject parent, String field) {
        JsonElement value = parent == null ? null : parent.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static String string(JsonObject parent, String field) {
        JsonElement value = parent == null ? null : parent.get(field);
        return value == null || value.isJsonNull() ? "" : value.getAsString();
    }

    private static String strictString(JsonObject parent, String field) {
        JsonElement value = parent == null ? null : parent.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isString()
                ? value.getAsString() : "";
    }

    private static Boolean strictBoolean(JsonObject parent, String field) {
        JsonElement value = parent == null ? null : parent.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean()
                ? value.getAsBoolean() : null;
    }

    private static Integer strictInteger(JsonObject parent, String field) {
        JsonElement value = parent == null ? null : parent.get(field);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()) {
            return null;
        }
        String text = value.getAsString();
        if (!text.matches("-?(?:0|[1-9][0-9]*)")) return null;
        try {
            return Integer.valueOf(text);
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    private static Long strictLong(JsonObject parent, String field) {
        JsonElement value = parent == null ? null : parent.get(field);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()) {
            return null;
        }
        String text = value.getAsString();
        if (!text.matches("-?(?:0|[1-9][0-9]*)")) return null;
        try {
            return Long.valueOf(text);
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    private static boolean bool(JsonObject parent, String field,
                                boolean fallback) {
        JsonElement value = parent == null ? null : parent.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    /**
     * A bounded partial slice remains incomplete discovery metadata.  This
     * explicit scheduler bit only changes whether the slice may participate
     * in operational import/composition; it never rewrites that metadata.
     */
    private static boolean requestedOutputSliceOperationallyAdmitted(
            JsonObject value) {
        return bool(value, "requestedOutputSliceComplete", false)
                || bool(value, "boundedPartialOutputSliceAdmitted", false);
    }

    private static boolean requestedOutputSliceContractOperationallyAdmitted(
            JsonObject value) {
        return requestedOutputSliceOperationallyAdmitted(value)
                && (bool(object(value, "requestedOutputSlice"), "complete",
                false) || bool(value,
                "boundedPartialOutputSliceAdmitted", false));
    }

    private static int integer(JsonObject parent, String field, int fallback) {
        JsonElement value = parent == null ? null : parent.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longInteger(JsonObject parent, String field,
                                    long fallback) {
        JsonElement value = parent == null ? null : parent.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsLong();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static JsonElement copy(JsonElement value, JsonElement fallback) {
        return value == null || value.isJsonNull() ? fallback : value.deepCopy();
    }

    private static JsonElement firstElement(JsonObject object,
                                            String... names) {
        if (object == null) return null;
        for (String name : names) {
            JsonElement value = object.get(name);
            if (value != null && !value.isJsonNull()) return value;
        }
        return null;
    }

    private static Map<String, String> parseArgs(String[] args) {
        Map<String, String> result = new LinkedHashMap<>();
        for (int index = 0; args != null && index < args.length; index++) {
            String value = args[index];
            if (!value.startsWith("--")) {
                continue;
            }
            String key = value.substring(2);
            String next = index + 1 < args.length ? args[index + 1] : "";
            if (!next.startsWith("--")) {
                result.put(key, next);
                index++;
            } else {
                result.put(key, "true");
            }
        }
        return result;
    }

    private static Path required(Map<String, String> options, String key) {
        String value = options.get(key);
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException("Missing --" + key);
        }
        return Paths.get(value);
    }

    private static Path sibling(Path path, String name) {
        Path parent = path.toAbsolutePath().getParent();
        return (parent == null ? Paths.get(".") : parent).resolve(name);
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

    public static final class BoundedIteratorResult {
        public final int candidateCount;
        public final int generatedSummaryCount;
        public final JsonArray diagnostics;
        public final Path output;

        private BoundedIteratorResult(int candidateCount,
                                      int generatedSummaryCount,
                                      JsonArray diagnostics, Path output) {
            this.candidateCount = candidateCount;
            this.generatedSummaryCount = generatedSummaryCount;
            this.diagnostics = diagnostics;
            this.output = output;
        }

        public JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 1);
            result.addProperty("kind",
                    "BOUNDED_ONE_ENTRY_MAP_ITERATOR_SUMMARY_SYNTHESIS");
            result.addProperty("candidateCount", candidateCount);
            result.addProperty("generatedSummaryCount",
                    generatedSummaryCount);
            result.addProperty("diagnosticCount", diagnostics.size());
            result.add("diagnostics", diagnostics.deepCopy());
            result.addProperty("output", output.toAbsolutePath().toString());
            result.addProperty("complete", candidateCount > 0
                    && candidateCount == generatedSummaryCount
                    && diagnostics.size() == 0);
            result.addProperty("authority",
                    "EXACT_STATIC_ITERATOR_REMOVE_AND_CMP_PORTS_PLUS_"
                            + "RUNTIME_EMPTY_MAP_BOUNDED_APPROXIMATION_V1");
            return result;
        }
    }

    private static final class CmpGuardResolution {
        private final boolean complete;
        private final String leftPort;
        private final String rightPort;
        private final String operator;
        private final String guardSite;
        private final String guardEdgeId;
        private final List<String> definitionEdgeIds;

        private CmpGuardResolution(boolean complete, String leftPort,
                                   String rightPort, String operator,
                                   String guardSite, String guardEdgeId,
                                   List<String> definitionEdgeIds) {
            this.complete = complete;
            this.leftPort = leftPort;
            this.rightPort = rightPort;
            this.operator = operator;
            this.guardSite = guardSite;
            this.guardEdgeId = guardEdgeId;
            this.definitionEdgeIds = definitionEdgeIds;
        }

        private static CmpGuardResolution none() {
            return new CmpGuardResolution(false, "", "", "", "", "",
                    Collections.<String>emptyList());
        }
    }

    private static final class BoundedIteratorEvidence {
        private final boolean applicable;
        private final boolean complete;
        private final String issue;
        private final String detail;
        private final String outputPort;
        private final String outputCell;
        private final String mapInputPort;
        private final String keyPort;
        private final String fieldPort;
        private final String environmentPort;
        private final String fieldSignature;
        private final String fieldName;
        private final String fieldType;
        private final String fieldOwner;
        private final String mutationSite;
        private final String guardSite;
        private final String emptySnapshotId;
        private final JsonArray proofEdgeIds;

        private BoundedIteratorEvidence(
                boolean applicable, boolean complete, String issue,
                String detail, String outputPort, String outputCell,
                String mapInputPort, String keyPort, String fieldPort,
                String environmentPort, String fieldSignature,
                String fieldName, String fieldType, String fieldOwner,
                String mutationSite, String guardSite,
                String emptySnapshotId, JsonArray proofEdgeIds) {
            this.applicable = applicable;
            this.complete = complete;
            this.issue = issue;
            this.detail = detail;
            this.outputPort = outputPort;
            this.outputCell = outputCell;
            this.mapInputPort = mapInputPort;
            this.keyPort = keyPort;
            this.fieldPort = fieldPort;
            this.environmentPort = environmentPort;
            this.fieldSignature = fieldSignature;
            this.fieldName = fieldName;
            this.fieldType = fieldType;
            this.fieldOwner = fieldOwner;
            this.mutationSite = mutationSite;
            this.guardSite = guardSite;
            this.emptySnapshotId = emptySnapshotId;
            this.proofEdgeIds = proofEdgeIds;
        }

        private static BoundedIteratorEvidence notApplicable() {
            return new BoundedIteratorEvidence(false, false, "", "", "",
                    "", "", "", "", "", "", "", "", "", "", "",
                    "", new JsonArray());
        }

        private static BoundedIteratorEvidence gap(String issue,
                                                   String detail) {
            return new BoundedIteratorEvidence(true, false, issue, detail,
                    "", "", "", "", "", "", "", "", "", "", "",
                    "", "", new JsonArray());
        }

        private static BoundedIteratorEvidence complete(
                String outputPort, String outputCell, String mapInputPort,
                String keyPort, String fieldPort, String environmentPort,
                String fieldSignature, String fieldName, String fieldType,
                String fieldOwner, String mutationSite, String guardSite,
                String emptySnapshotId, JsonArray proofEdgeIds) {
            return new BoundedIteratorEvidence(true, true, "", "",
                    outputPort, outputCell, mapInputPort, keyPort, fieldPort,
                    environmentPort, fieldSignature, fieldName, fieldType,
                    fieldOwner, mutationSite, guardSite, emptySnapshotId,
                    proofEdgeIds);
        }

        private JsonObject diagnostic(JsonObject summary) {
            JsonObject result = new JsonObject();
            result.addProperty("summaryId", string(summary, "summaryId"));
            result.addProperty("activationId", string(summary,
                    "activationId"));
            result.addProperty("regionId", string(summary, "regionId"));
            result.addProperty("issue", issue);
            result.addProperty("detail", detail);
            return result;
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 1);
            result.addProperty("kind",
                    "BOUNDED_ONE_ENTRY_MAP_ITERATOR_REMOVE");
            result.addProperty("complete", complete);
            result.addProperty("approximation", true);
            result.addProperty("scope",
                    "ONE_RELEVANT_PRESTATE_MAP_ENTRY_AND_ONE_ITERATION");
            result.addProperty("outputPort", outputPort);
            result.addProperty("outputCell", outputCell);
            result.addProperty("mapInputPort", mapInputPort);
            result.addProperty("keyPort", keyPort);
            result.addProperty("fieldPort", fieldPort);
            result.addProperty("environmentPort", environmentPort);
            result.addProperty("fieldSignature", fieldSignature);
            result.addProperty("fieldName", fieldName);
            result.addProperty("fieldType", fieldType);
            result.addProperty("fieldOwner", fieldOwner);
            result.addProperty("guardFormula", fieldPort + " < "
                    + environmentPort);
            result.addProperty("mutationSite", mutationSite);
            result.addProperty("guardSite", guardSite);
            result.addProperty("sourceEmptySnapshotId", emptySnapshotId);
            result.add("proofEdgeIds", proofEdgeIds.deepCopy());
            result.addProperty("authority",
                    "EXACT_STATIC_ITERATOR_REMOVE_CMP_AND_PROJECTED_PORTS_"
                            + "PLUS_RUNTIME_EMPTY_MAP_BOUNDED_"
                            + "APPROXIMATION_V1");
            return result;
        }
    }

    public static final class ImportResult {
        public final int rawResultCount;
        public final int validSummaryCount;
        public final int diagnosticCount;
        public final int skippedEventCount;
        public final JsonObject summary = new JsonObject();

        private ImportResult(int rawResultCount, int validSummaryCount,
                             int diagnosticCount, int skippedEventCount) {
            this.rawResultCount = rawResultCount;
            this.validSummaryCount = validSummaryCount;
            this.diagnosticCount = diagnosticCount;
            this.skippedEventCount = skippedEventCount;
        }
    }

    private static final class RuntimePathContamination {
        private final int rawConditionCount;
        private final JsonArray conditionIndexes;
        private final JsonArray codePositions;

        private RuntimePathContamination(int rawConditionCount,
                                         JsonArray conditionIndexes,
                                         JsonArray codePositions) {
            this.rawConditionCount = rawConditionCount;
            this.conditionIndexes = conditionIndexes;
            this.codePositions = codePositions;
        }

        private boolean valid() {
            return conditionIndexes.size() == 0;
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("policy",
                    "REJECT_GRAPH_CHECKER_RUNTIME_CODE_POSITIONS");
            result.addProperty("rawConditionCount", rawConditionCount);
            result.add("contaminatedConditionIndexes",
                    conditionIndexes.deepCopy());
            result.add("runtimeCodePositions", codePositions.deepCopy());
            return result;
        }
    }

    private static final class ReplayAdmission {
        private final boolean required;
        private final boolean valid;
        private final JsonArray failures;
        private final String authority;

        private ReplayAdmission(boolean required, boolean valid,
                                JsonArray failures, String authority) {
            this.required = required;
            this.valid = valid;
            this.failures = failures;
            this.authority = authority;
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("kind", required
                    ? "DIRECTED_TARGET_REPLAY_ADMISSION"
                    : "TARGET_SEED_PATH_ADMISSION");
            result.addProperty("required", required);
            result.addProperty("valid", valid);
            result.addProperty("branchOverrideAccepted", false);
            result.add("failures", failures.deepCopy());
            result.addProperty("failureCount", failures.size());
            result.addProperty("authority", authority);
            return result;
        }
    }

    private static final class VmIntrinsicPlaceholderBindingExtraction {
        private final JsonArray bindings;
        private final JsonArray failures;
        private final boolean complete;

        private VmIntrinsicPlaceholderBindingExtraction(JsonArray bindings,
                                                         JsonArray failures) {
            this.bindings = bindings;
            this.failures = failures;
            this.complete = failures.size() == 0;
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 1);
            result.addProperty("kind",
                    "VM_INTRINSIC_PLACEHOLDER_BINDING_ADMISSION");
            result.addProperty("complete", complete);
            result.addProperty("bindingCount", bindings.size());
            result.add("bindings", bindings.deepCopy());
            result.add("failures", failures.deepCopy());
            result.addProperty("authority",
                    "OWNER_EXACT_UNIQUE_USED_CUSTOM_JDK_PLACEHOLDER_V1");
            return result;
        }
    }

    private static final class InputAdmission {
        private final boolean complete;
        private final Set<String> globalRequired;
        private final Set<String> required;
        private final Set<String> observed;
        private final Set<String> admittedObservedInputs;
        private final Set<String> admittedConcreteFallbacks;
        private final Set<String> pathInactive;
        private final JsonArray pathInactiveProofs;
        private final Set<String> admittedVmIntrinsicPlaceholders;
        private final JsonArray unforcedEnvironmentValidationRequirements;
        private final JsonArray failures;

        private InputAdmission(boolean complete,
                               Set<String> globalRequired,
                               Set<String> required,
                               Set<String> observed,
                               Set<String> admittedObservedInputs,
                               Set<String> admittedConcreteFallbacks,
                               Set<String> pathInactive,
                               JsonArray pathInactiveProofs,
                               Set<String> admittedVmIntrinsicPlaceholders,
                               JsonArray unforcedEnvironmentValidationRequirements,
                               JsonArray failures) {
            this.complete = complete;
            this.globalRequired = globalRequired;
            this.required = required;
            this.observed = observed;
            this.admittedObservedInputs = admittedObservedInputs;
            this.admittedConcreteFallbacks =
                    admittedConcreteFallbacks;
            this.pathInactive = pathInactive;
            this.pathInactiveProofs = pathInactiveProofs;
            this.admittedVmIntrinsicPlaceholders =
                    admittedVmIntrinsicPlaceholders;
            this.unforcedEnvironmentValidationRequirements =
                    unforcedEnvironmentValidationRequirements;
            this.failures = failures;
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("complete", complete);
            result.add("globalSliceInputs",
                    GSON.toJsonTree(globalRequired));
            result.add("requiredSliceInputs", GSON.toJsonTree(required));
            result.add("pathInactiveSliceInputs",
                    GSON.toJsonTree(pathInactive));
            result.add("pathInactiveProofs",
                    pathInactiveProofs.deepCopy());
            result.add("observedSymbolizedInputs",
                    GSON.toJsonTree(observed));
            result.add("admittedObservedInputs",
                    GSON.toJsonTree(admittedObservedInputs));
            result.addProperty("admittedObservedInputAuthority",
                    "SCHEDULED_OBSERVATION_ONLY_INPUT_PLUS_UNIQUE_COMPLETE_"
                            + "FIRST_CONTAINER_RUNTIME_EVIDENCE_V1");
            result.add("admittedConcreteFallbackInputs",
                    GSON.toJsonTree(admittedConcreteFallbacks));
            result.add("admittedVmIntrinsicPlaceholderInputs",
                    GSON.toJsonTree(admittedVmIntrinsicPlaceholders));
            result.add("unforcedEnvironmentValidationRequirements",
                    unforcedEnvironmentValidationRequirements.deepCopy());
            result.add("failures", failures.deepCopy());
            result.addProperty("authority",
                    "STATIC_GLOBAL_SLICE_DEMAND_REFINED_BY_EXACT_"
                            + "TRANSFORMER_RUNTIME_PATH_PROOFS_AND_"
                            + "EXPLICIT_CONCRETE_FALLBACKS");
            result.addProperty("vmIntrinsicPlaceholderAuthority",
                    "EXACT_SCHEDULER_BINDING_PLUS_CUSTOM_JDK_STRUCTURED_"
                            + "PLACEHOLDER_EVIDENCE");
            return result;
        }
    }

    private static final class VmIntrinsicPlaceholderAdmission {
        private final boolean applicable;
        private final boolean admitted;
        private final JsonObject requirement;
        private final String failure;

        private VmIntrinsicPlaceholderAdmission(boolean applicable,
                                                boolean admitted,
                                                JsonObject requirement,
                                                String failure) {
            this.applicable = applicable;
            this.admitted = admitted;
            this.requirement = requirement;
            this.failure = failure;
        }

        private static VmIntrinsicPlaceholderAdmission admitted(
                JsonObject requirement) {
            return new VmIntrinsicPlaceholderAdmission(true, true,
                    requirement, "");
        }

        private static VmIntrinsicPlaceholderAdmission failure(
                String failure) {
            return new VmIntrinsicPlaceholderAdmission(true, false,
                    new JsonObject(), failure);
        }

        private static VmIntrinsicPlaceholderAdmission notApplicable() {
            return new VmIntrinsicPlaceholderAdmission(false, false,
                    new JsonObject(), "");
        }
    }

    private enum MapMutationKind {
        MAP_PUT("put", 3),
        MAP_REMOVE("remove", 2),
        MAP_CLEAR("clear", 1),
        MAP_PUT_ALL("putAll", 2);

        private final String method;
        private final int parameterCount;

        MapMutationKind(String method, int parameterCount) {
            this.method = method;
            this.parameterCount = parameterCount;
        }

        private static MapMutationKind fromMethod(String method) {
            for (MapMutationKind value : values()) {
                if (value.method.equals(method)) {
                    return value;
                }
            }
            return null;
        }
    }

    private static final class MapMethod {
        private final String owner;
        private final String method;
        private final String qualifiedName;
        private final boolean mapOwner;

        private MapMethod(String owner, String method) {
            this.owner = owner;
            this.method = method;
            this.qualifiedName = owner + " " + method;
            int separator = owner.lastIndexOf('/');
            String simple = separator < 0 ? owner
                    : owner.substring(separator + 1);
            this.mapOwner = simple.endsWith("Map")
                    || "Hashtable".equals(simple);
        }

        private static MapMethod parse(String qualifiedName) {
            if (qualifiedName == null) {
                return null;
            }
            int separator = qualifiedName.lastIndexOf(' ');
            if (separator <= 0 || separator + 1 >= qualifiedName.length()) {
                return null;
            }
            return new MapMethod(qualifiedName.substring(0, separator),
                    qualifiedName.substring(separator + 1));
        }
    }

    private static final class HeapMutation {
        private final MapMutationKind kind;
        private final MapMethod method;
        private final int rawIndex;
        private final int normalizedIndex;
        private final String normalizationStatus;
        private final String codePosition;
        private final String siteId;
        private final int occurrence;
        private final JsonElement mapExpression;
        private final String mapIdentity;
        private final JsonElement keyExpression;
        private final JsonElement valueExpression;
        private final JsonElement sourceExpression;
        private final JsonElement resultExpression;
        private final String parameterNormalization;
        private final String semanticAdmissionAuthority;
        private RuntimeHeapProvenance runtimeProvenance;

        private HeapMutation(MapMutationKind kind, MapMethod method,
                             int rawIndex, int normalizedIndex,
                             String normalizationStatus, String codePosition,
                             String siteId, int occurrence, JsonArray parameters,
                             JsonElement resultExpression,
                             String parameterNormalization,
                             String semanticAdmissionAuthority) {
            this.kind = kind;
            this.method = method;
            this.rawIndex = rawIndex;
            this.normalizedIndex = normalizedIndex;
            this.normalizationStatus = normalizationStatus;
            this.codePosition = codePosition;
            this.siteId = siteId;
            this.occurrence = occurrence;
            this.mapExpression = expressionOrNull(parameters.get(0));
            this.mapIdentity = GSON.toJson(this.mapExpression);
            this.keyExpression = kind == MapMutationKind.MAP_PUT
                    || kind == MapMutationKind.MAP_REMOVE
                    ? expressionOrNull(parameters.get(1)) : null;
            this.valueExpression = kind == MapMutationKind.MAP_PUT
                    ? expressionOrNull(parameters.get(2)) : null;
            this.sourceExpression = kind == MapMutationKind.MAP_PUT_ALL
                    ? expressionOrNull(parameters.get(1)) : null;
            this.resultExpression = expressionOrNull(resultExpression);
            this.parameterNormalization = parameterNormalization;
            this.semanticAdmissionAuthority = semanticAdmissionAuthority;
            this.runtimeProvenance = null;
        }

        private JsonObject toEffect(String effectId, String inputPort,
                                    String outputPort, String stateFamily,
                                    String preState, String postState,
                                    int before, int after,
                                    String inputBinding,
                                    String outputBinding) {
            JsonObject effect = new JsonObject();
            effect.addProperty("effectId", effectId);
            effect.addProperty("kind", kind.name());
            effect.addProperty("methodOwner", method.owner);
            effect.addProperty("methodName", method.method);
            effect.addProperty("methodExpressionName", method.qualifiedName);
            effect.addProperty("rawConditionIndex", rawIndex);
            effect.addProperty("normalizedConditionIndex", normalizedIndex);
            effect.addProperty("normalizationStatus", normalizationStatus);
            effect.addProperty("codePosition", codePosition);
            effect.addProperty("siteId", siteId);
            effect.addProperty("occurrence", occurrence);
            effect.addProperty("provenanceAuthority",
                    "VM_CODE_POSITION_AND_RAW_PATH_ORDER");
            if (!semanticAdmissionAuthority.isEmpty()) {
                effect.addProperty("semanticAdmissionAuthority",
                        semanticAdmissionAuthority);
            }
            if (!parameterNormalization.isEmpty()) {
                effect.addProperty("parameterNormalization",
                        parameterNormalization);
            }
            effect.addProperty("stateFamily", stateFamily);
            effect.addProperty("preState", preState);
            effect.addProperty("postState", postState);
            effect.addProperty("stateOrdinalBefore", before);
            effect.addProperty("stateOrdinalAfter", after);
            effect.addProperty("inputPort", inputPort);
            effect.addProperty("outputPort", outputPort);
            effect.addProperty("inputBinding", inputBinding);
            effect.addProperty("outputBinding", outputBinding);
            effect.add("mapExpression", mapExpression.deepCopy());
            effect.add("resultExpression", resultExpression.deepCopy());
            if (keyExpression != null) {
                effect.add("keyExpression", keyExpression.deepCopy());
            }
            if (valueExpression != null) {
                effect.add("valueExpression", valueExpression.deepCopy());
            }
            if (sourceExpression != null) {
                effect.add("sourceExpression", sourceExpression.deepCopy());
            }
            if (runtimeProvenance != null) {
                runtimeProvenance.attach(effect);
            }
            return effect;
        }
    }

    private static final class MapStateTracker {
        private final int mapOrdinal;
        private final int totalEffects;
        private final String finalOutputPort;
        private final boolean syntheticInput;
        private final boolean freshInitialized;
        private final RuntimeMapStateInputResolution runtimeMapInput;
        private final String stateFamily;
        private String currentPort;
        private int seen;

        private MapStateTracker(String regionId, int mapOrdinal,
                                int totalEffects, String inputPort,
                                String finalOutputPort,
                                boolean syntheticInput,
                                boolean freshInitialized,
                                RuntimeMapStateInputResolution
                                        runtimeMapInput) {
            this.mapOrdinal = mapOrdinal;
            this.totalEffects = totalEffects;
            this.currentPort = inputPort;
            this.finalOutputPort = finalOutputPort;
            this.syntheticInput = syntheticInput;
            this.freshInitialized = freshInitialized;
            this.runtimeMapInput = runtimeMapInput;
            this.stateFamily = "MAP_STATE." + regionId + "." + mapOrdinal;
        }
    }

    private static final class HeapEffectIssue {
        private final String code;
        private final int rawIndex;
        private final String codePosition;
        private final String method;

        private HeapEffectIssue(String code, int rawIndex,
                                String codePosition, String method) {
            this.code = code;
            this.rawIndex = rawIndex;
            this.codePosition = codePosition;
            this.method = method;
        }

        private String detail() {
            return "rawConditionIndex=" + rawIndex + ";method=" + method
                    + ";codePosition=" + codePosition;
        }
    }

    private static final class RuntimeHeapObservation {
        private final JsonObject record;
        private final String observationId;
        private final long eventSequence;
        private final int pcBoundary;

        private RuntimeHeapObservation(JsonObject record) {
            this.record = record.deepCopy();
            this.observationId = string(record, "observationId");
            this.eventSequence = longInteger(record, "eventSequence", -1L);
            this.pcBoundary = integer(record, "pcBoundary", -1);
        }
    }

    private static final class RuntimeHeapEvidenceSelection {
        private final JsonElement effects;
        private final JsonElement observations;
        private final JsonArray ignoredEvidence;

        private RuntimeHeapEvidenceSelection(JsonElement effects,
                                             JsonElement observations,
                                             JsonArray ignoredEvidence) {
            this.effects = effects;
            this.observations = observations;
            this.ignoredEvidence = ignoredEvidence;
        }
    }

    private static final class RuntimeFiniteMapSnapshot {
        private final JsonObject record;

        private RuntimeFiniteMapSnapshot(JsonObject record) {
            this.record = record.deepCopy();
        }
    }

    private static final class RuntimeMapStateInputObservation {
        private final JsonObject record;

        private RuntimeMapStateInputObservation(JsonObject record) {
            this.record = record.deepCopy();
        }
    }

    private static final class RuntimeMapStateInputResolution {
        private final RuntimeMapStateInputObservation observation;

        private RuntimeMapStateInputResolution(
                RuntimeMapStateInputObservation observation) {
            this.observation = observation;
        }

        private static RuntimeMapStateInputResolution resolved(
                RuntimeMapStateInputObservation observation) {
            return new RuntimeMapStateInputResolution(observation);
        }

        private static RuntimeMapStateInputResolution none() {
            return new RuntimeMapStateInputResolution(null);
        }

        private boolean resolved() {
            return observation != null;
        }

        private String inputPort() {
            return resolved() ? string(observation.record, "inputSymbol")
                    : "";
        }

        private String snapshotId() {
            return "MAP_STATE_INPUT_SNAPSHOT:"
                    + string(observation.record, "observationId");
        }

        private JsonObject toFiniteSnapshot(String statePort) {
            JsonObject record = observation.record;
            JsonObject snapshot = new JsonObject();
            snapshot.addProperty("schemaVersion", 1);
            snapshot.addProperty("kind",
                    "EXACT_RUNTIME_FINITE_MAP_SNAPSHOT");
            snapshot.addProperty("snapshotId", snapshotId());
            snapshot.addProperty("statePort", statePort);
            snapshot.addProperty("cardinality", 0);
            snapshot.addProperty("implementationClass", string(record,
                    "mapImplementationClass"));
            snapshot.addProperty("backingMapObjectToken", longInteger(
                    record, "mapObjectToken", -1L));
            snapshot.addProperty("objectTokenScope", string(record,
                    "objectTokenScope"));
            snapshot.addProperty("mapKeysFullyCaptured", true);
            snapshot.addProperty("entryReadBijectionComplete", true);
            snapshot.add("entries", new JsonArray());
            snapshot.add("proofObservationIds", new JsonArray());
            snapshot.addProperty("complete", true);
            snapshot.addProperty("authority",
                    "INITIAL_EXACT_MAP_SIZE_AND_KEYS_PLUS_COMPLETE_"
                            + "ENTRY_READ_BIJECTION_V1");
            snapshot.addProperty("sourceObservationId", string(record,
                    "observationId"));
            snapshot.addProperty("sourceAuthority", string(record,
                    "snapshotAuthority"));
            return snapshot;
        }

        private void attach(JsonObject effect) {
            if (!resolved()) return;
            JsonObject record = observation.record;
            effect.addProperty("runtimeMapStateInputObservationId",
                    string(record, "observationId"));
            effect.addProperty("runtimeMapStateInputSnapshotId",
                    snapshotId());
            effect.addProperty("runtimeMapStateInputObjectToken",
                    longInteger(record, "mapObjectToken", -1L));
            effect.addProperty("runtimeMapStateInputBindingComplete", true);
            effect.addProperty("runtimeMapStateInputBindingAuthority",
                    "EXACT_STABLE_FIELD_OBJECT_TOKEN_PLUS_STATIC_REQUESTED_"
                            + "MAP_TRANSFORMER_V1");
        }
    }

    private static final class RuntimeHeapObservationCatalog {
        private final boolean legacy;
        private final int recordCount;
        private final Map<String, RuntimeHeapObservation> byId;
        private final Map<String, RuntimeFiniteMapSnapshot>
                finiteMapSnapshotsById;
        private final Map<String, RuntimeMapStateInputObservation>
                mapStateInputsById;
        private final List<HeapEffectIssue> issues;

        private RuntimeHeapObservationCatalog(
                boolean legacy, int recordCount,
                Map<String, RuntimeHeapObservation> byId,
                Map<String, RuntimeFiniteMapSnapshot> finiteMapSnapshotsById,
                Map<String, RuntimeMapStateInputObservation>
                        mapStateInputsById,
                List<HeapEffectIssue> issues) {
            this.legacy = legacy;
            this.recordCount = recordCount;
            this.byId = byId;
            this.finiteMapSnapshotsById = finiteMapSnapshotsById;
            this.mapStateInputsById = mapStateInputsById;
            this.issues = issues;
        }

        private static RuntimeHeapObservationCatalog legacy() {
            return new RuntimeHeapObservationCatalog(true, 0,
                    Collections.<String, RuntimeHeapObservation>emptyMap(),
                    Collections.<String, RuntimeFiniteMapSnapshot>emptyMap(),
                    Collections.<String,
                            RuntimeMapStateInputObservation>emptyMap(),
                    Collections.<HeapEffectIssue>emptyList());
        }
    }

    private static final class RuntimeDynamicFieldBinding {
        private final JsonObject record;
        private final String dynamicBindingId;
        private final String baseInputSymbol;
        private final String dynamicFieldSymbol;
        private final String entryReadObservationId;
        private final String fieldSignature;

        private RuntimeDynamicFieldBinding(JsonObject record) {
            this.record = record.deepCopy();
            this.dynamicBindingId = string(record, "dynamicBindingId");
            this.baseInputSymbol = string(record, "baseInputSymbol");
            this.dynamicFieldSymbol = string(record, "dynamicFieldSymbol");
            this.entryReadObservationId = string(record,
                    "entryReadObservationId");
            this.fieldSignature = string(record, "fieldSignature");
        }
    }

    private static final class ContainerDynamicFieldValidation {
        private final JsonObject normalized;
        private final String siteOccurrence;
        private final String selectorTuple;
        private final String identityTuple;
        private final String bridgeTuple;

        private ContainerDynamicFieldValidation(
                JsonObject normalized, String siteOccurrence,
                String selectorTuple, String identityTuple,
                String bridgeTuple) {
            this.normalized = normalized;
            this.siteOccurrence = siteOccurrence;
            this.selectorTuple = selectorTuple;
            this.identityTuple = identityTuple;
            this.bridgeTuple = bridgeTuple;
        }
    }

    private static final class ContainerPutConsumerWitness {
        private final HeapMutation mutation;
        private final HeapPortBinding binding;

        private ContainerPutConsumerWitness(
                HeapMutation mutation, HeapPortBinding binding) {
            this.mutation = mutation;
            this.binding = binding;
        }
    }

    private static final class SnapshotDynamicExpressionScan {
        private int referenceCount;
        private boolean invalid;
        private JsonObject expression;
    }

    private static final class DynamicBranchExpressionScan {
        private int referenceCount;
        private boolean invalid;
        private JsonObject expression;
    }

    private static final class ContainerSnapshotBranchWitness {
        private final JsonObject fieldExpression;
        private final String siteId;
        private final int occurrence;

        private ContainerSnapshotBranchWitness(
                JsonObject fieldExpression, String siteId, int occurrence) {
            this.fieldExpression = fieldExpression.deepCopy();
            this.siteId = siteId;
            this.occurrence = occurrence;
        }
    }

    private static final class MapProjectionDynamicFieldValidation {
        private final JsonObject normalized;
        private final String siteOccurrence;
        private final String selectorTuple;
        private final String identityTuple;
        private final String staticBindingId;
        private final int outputIndex;
        private final int snapshotElementCount;

        private MapProjectionDynamicFieldValidation(
                JsonObject normalized, String siteOccurrence,
                String selectorTuple, String identityTuple,
                String staticBindingId, int outputIndex,
                int snapshotElementCount) {
            this.normalized = normalized;
            this.siteOccurrence = siteOccurrence;
            this.selectorTuple = selectorTuple;
            this.identityTuple = identityTuple;
            this.staticBindingId = staticBindingId;
            this.outputIndex = outputIndex;
            this.snapshotElementCount = snapshotElementCount;
        }
    }

    private static final class DynamicFieldBindingCatalog {
        private final boolean legacy;
        private final int recordCount;
        private final Map<String, RuntimeDynamicFieldBinding> byId;
        private final Map<String, RuntimeDynamicFieldBinding> byDynamicSymbol;
        private final List<HeapEffectIssue> issues;

        private DynamicFieldBindingCatalog(
                boolean legacy, int recordCount,
                Map<String, RuntimeDynamicFieldBinding> byId,
                Map<String, RuntimeDynamicFieldBinding> byDynamicSymbol,
                List<HeapEffectIssue> issues) {
            this.legacy = legacy;
            this.recordCount = recordCount;
            this.byId = byId;
            this.byDynamicSymbol = byDynamicSymbol;
            this.issues = issues;
        }

        private static DynamicFieldBindingCatalog legacy() {
            return new DynamicFieldBindingCatalog(true, 0,
                    Collections.<String, RuntimeDynamicFieldBinding>emptyMap(),
                    Collections.<String, RuntimeDynamicFieldBinding>emptyMap(),
                    Collections.<HeapEffectIssue>emptyList());
        }

        private List<RuntimeDynamicFieldBinding> forEntry(
                String observationId, String baseInputSymbol) {
            List<RuntimeDynamicFieldBinding> result = new ArrayList<>();
            for (RuntimeDynamicFieldBinding binding : byId.values()) {
                if (observationId.equals(binding.entryReadObservationId)
                        && baseInputSymbol.equals(binding.baseInputSymbol)) {
                    result.add(binding);
                }
            }
            return result;
        }

        private List<RuntimeDynamicFieldBinding> forObservation(
                String observationId) {
            List<RuntimeDynamicFieldBinding> result = new ArrayList<>();
            for (RuntimeDynamicFieldBinding binding : byId.values()) {
                if (observationId.equals(binding.entryReadObservationId)) {
                    result.add(binding);
                }
            }
            return result;
        }

        private JsonArray normalizedBindings() {
            JsonArray result = new JsonArray();
            for (RuntimeDynamicFieldBinding binding : byId.values()) {
                result.add(binding.record.deepCopy());
            }
            return result;
        }
    }

    private static final class ObservationStateResolution {
        private final boolean resolved;
        private final boolean ambiguous;
        private final String statePort;
        private final String authority;
        private final String effectId;
        private final JsonObject stateBaseProof;

        private ObservationStateResolution(boolean resolved,
                                           boolean ambiguous,
                                           String statePort,
                                           String authority,
                                           String effectId,
                                           JsonObject stateBaseProof) {
            this.resolved = resolved;
            this.ambiguous = ambiguous;
            this.statePort = statePort;
            this.authority = authority;
            this.effectId = effectId;
            this.stateBaseProof = stateBaseProof == null ? null
                    : stateBaseProof.deepCopy();
        }

        private static ObservationStateResolution resolved(
                String statePort, String authority, String effectId) {
            return new ObservationStateResolution(true, false, statePort,
                    authority, effectId, null);
        }

        private static ObservationStateResolution resolved(
                String statePort, String authority, String effectId,
                JsonObject stateBaseProof) {
            return new ObservationStateResolution(true, false, statePort,
                    authority, effectId, stateBaseProof);
        }

        private static ObservationStateResolution unresolved() {
            return new ObservationStateResolution(false, false, "", "", "",
                    null);
        }

        private static ObservationStateResolution ambiguous() {
            return new ObservationStateResolution(false, true, "", "", "",
                    null);
        }
    }

    private static final class ObservationFieldBindings {
        private final JsonArray bindings;
        private final boolean complete;
        private final List<HeapEffectIssue> issues;

        private ObservationFieldBindings(JsonArray bindings,
                                         boolean complete,
                                         List<HeapEffectIssue> issues) {
            this.bindings = bindings;
            this.complete = complete;
            this.issues = issues;
        }
    }

    private static final class HeapObservationExtraction {
        private final RuntimeHeapObservationCatalog catalog;
        private final JsonArray observations;
        private final List<HeapEffectIssue> issues;

        private HeapObservationExtraction(
                RuntimeHeapObservationCatalog catalog,
                JsonArray observations, List<HeapEffectIssue> issues) {
            this.catalog = catalog;
            this.observations = observations;
            this.issues = issues;
        }

        private static HeapObservationExtraction legacy(
                RuntimeHeapObservationCatalog catalog) {
            return new HeapObservationExtraction(catalog, new JsonArray(),
                    Collections.<HeapEffectIssue>emptyList());
        }

        private boolean complete() {
            return catalog.issues.isEmpty() && issues.isEmpty()
                    && (catalog.legacy
                    || observations.size() == catalog.byId.size()
                    && catalog.byId.size()
                    + catalog.finiteMapSnapshotsById.size()
                    + catalog.mapStateInputsById.size()
                    == catalog.recordCount);
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("policy",
                    "RUNTIME_MAP_ENTRY_READ_EXACT_STATE_AND_TOKEN_JOIN_V1");
            result.addProperty("legacy", catalog.legacy);
            result.addProperty("declared", !catalog.legacy);
            result.addProperty("recordCount", catalog.recordCount);
            result.addProperty("validatedCount", catalog.byId.size()
                    + catalog.finiteMapSnapshotsById.size()
                    + catalog.mapStateInputsById.size());
            result.addProperty("mapEntryReadCount", catalog.byId.size());
            result.addProperty("finiteMapSnapshotCount",
                    catalog.finiteMapSnapshotsById.size());
            result.addProperty("mapStateInputObservationCount",
                    catalog.mapStateInputsById.size());
            result.addProperty("observationCount", observations.size());
            result.addProperty("issueCount",
                    catalog.issues.size() + issues.size());
            result.addProperty("complete", complete());
            return result;
        }
    }

    private static final class RuntimeHeapProvenance {
        private final JsonObject record;
        private final RuntimeHeapObservation entryRead;

        private RuntimeHeapProvenance(JsonObject record,
                                      RuntimeHeapObservation entryRead) {
            this.record = record.deepCopy();
            this.entryRead = entryRead;
        }

        private void attach(JsonObject effect) {
            boolean runtimeBoundEntryKey =
                    "UNIQUE_HASHMAP_REMOVENODE_RECEIVER_RESULT_HASH_PLUS_"
                            .concat("RUNTIME_ENTRY_KEY_V1").equals(
                            string(record, "vmKeyJoinAuthority"));
            if (runtimeBoundEntryKey) {
                effect.add("nativeKeyExpression",
                        effect.get("keyExpression").deepCopy());
                effect.add("keyExpression",
                        record.get("keyExpression").deepCopy());
            }
            effect.addProperty("originMethod", string(record,
                    "originMethod"));
            effect.addProperty("originUnitIndex", integer(record,
                    "originUnitIndex", -1));
            effect.addProperty("applicationSiteId", string(record,
                    "siteId"));
            effect.addProperty("applicationOccurrence", integer(record,
                    "occurrence", 1));
            effect.addProperty("applicationProvenanceAuthority",
                    string(record, "provenanceAuthority"));
            effect.addProperty("runtimeHeapEffectVmConditionIndex",
                    integer(record, "vmConditionIndex", -1));
            effect.addProperty("runtimeHeapEffectJoinAuthority",
                    runtimeBoundEntryKey
                            ? "EXACT_INDEX_RECEIVER_VM_RESULT_INTEGER_HASH_"
                            + "AND_RUNTIME_ENTRY_KEY_V1"
                            : "EXACT_INDEX_KIND_MAP_KEY_AND_VM_EXPRESSION");
            if (entryRead != null) {
                effect.addProperty("entryReadObservationId",
                        entryRead.observationId);
                effect.addProperty("entryReadAssociationAuthority",
                        "EXACT_ID_SEQUENCE_EXPRESSIONS_AND_OBJECT_TOKENS");
            }
            if (hasExactEntryValueBinding()) {
                effect.add("removedValueExpression",
                        record.get("valueExpression").deepCopy());
                effect.addProperty("removedValueExpressionAuthority", string(
                        record, "valueExpressionAuthority"));
                if (entryRead != null) {
                    copyValueRefWitnessMetadata(entryRead.record, effect);
                }
                effect.addProperty("requiresKeyPresent", true);
                effect.addProperty("entryValueIdentity", integer(record,
                        "valueIdentity", 0));
                if (entryRead != null) {
                    effect.addProperty("entryValueObjectToken", longInteger(
                            record, "valueObjectToken", 0L));
                }
                effect.addProperty("entryBindingAuthority", string(record,
                        "entryBindingAuthority"));
                effect.addProperty("keyBindingAuthority", string(record,
                        "keyBindingAuthority"));
                effect.addProperty("valueBindingAuthority", string(record,
                        "valueBindingAuthority"));
            }
            effect.add("applicationProvenance", record.deepCopy());
        }

        private boolean hasExactEntryValueBinding() {
            return bool(record, "complete", false)
                    && "ENTRY_SET".equals(string(record, "viewKind"))
                    && "JAVA_MAP_ENTRY_FROM_BOUND_ENTRY_SET_NEXT".equals(
                    string(record, "entryBindingAuthority"))
                    && "SAME_MAP_ENTRY_GET_KEY_AT_NEXT".equals(
                    string(record, "keyBindingAuthority"))
                    && "SAME_MAP_ENTRY_GET_VALUE_AT_NEXT".equals(
                    string(record, "valueBindingAuthority"))
                    && record.has("valueExpression")
                    && !record.get("valueExpression").isJsonNull()
                    && (!VALUE_REF_WITNESS_AUTHORITY.equals(string(record,
                    "valueExpressionAuthority"))
                    || entryRead != null
                    && importerCertifiedValueRefWitness(entryRead.record))
                    && (entryRead != null
                    && longInteger(record, "valueObjectToken", 0L) > 0L
                    || entryRead == null
                    && bool(record, "valueIdentityKnown", false)
                    && !bool(record, "valueWasNull", true)
                    && integer(record, "valueIdentity", 0) != 0);
        }
    }

    private static final class RuntimeHeapEffectJoin {
        private final boolean legacy;
        private final int recordCount;
        private final int joinedCount;
        private final Map<Integer, RuntimeHeapProvenance> bindings;
        private final List<HeapEffectIssue> issues;

        private RuntimeHeapEffectJoin(
                boolean legacy, int recordCount, int joinedCount,
                Map<Integer, RuntimeHeapProvenance> bindings,
                List<HeapEffectIssue> issues) {
            this.legacy = legacy;
            this.recordCount = recordCount;
            this.joinedCount = joinedCount;
            this.bindings = bindings;
            this.issues = issues;
        }

        private static RuntimeHeapEffectJoin legacy() {
            return new RuntimeHeapEffectJoin(true, 0, 0,
                    Collections.<Integer, RuntimeHeapProvenance>emptyMap(),
                    Collections.<HeapEffectIssue>emptyList());
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("policy",
                    "RUNTIME_HEAP_EFFECT_EXACT_VM_APPLICATION_JOIN_V1");
            result.addProperty("legacy", legacy);
            result.addProperty("declared", !legacy);
            result.addProperty("recordCount", recordCount);
            result.addProperty("joinedCount", joinedCount);
            result.addProperty("issueCount", issues.size());
            result.addProperty("complete", issues.isEmpty());
            return result;
        }
    }

    private static final class HeapOutputBinding {
        private final String stateId;
        private final String stateFamily;
        private final String effectId;
        private final String sourcePort;

        private HeapOutputBinding(String stateId, String stateFamily,
                                  String effectId, String sourcePort) {
            this.stateId = stateId;
            this.stateFamily = stateFamily;
            this.effectId = effectId;
            this.sourcePort = sourcePort;
        }
    }

    private static final class StaticTransformerObligation {
        private final boolean heapWrite;
        private final String methodKey;
        private final String signature;
        private final String siteId;

        private StaticTransformerObligation(boolean heapWrite,
                                            String methodKey,
                                            String signature,
                                            String siteId) {
            this.heapWrite = heapWrite;
            this.methodKey = methodKey;
            this.signature = signature;
            this.siteId = siteId;
        }

        private static StaticTransformerObligation heapWrite(
                String methodKey, String signature, String siteId) {
            return new StaticTransformerObligation(true, methodKey,
                    signature, siteId);
        }

        private static StaticTransformerObligation edgeFreeVoid(
                String methodKey, String signature) {
            return new StaticTransformerObligation(false, methodKey,
                    signature, "");
        }

        private String kind() {
            return heapWrite ? "DECLARED_HEAP_WRITE_SITE"
                    : "EDGE_FREE_VOID_SLICE_METHOD";
        }
    }

    private static final class GuardedMutationProof {
        private final String guardSiteId;
        private final String mutationSiteId;
        private final String method;
        private final int mutationUnitIndex;
        private final boolean requiredOutcome;

        private GuardedMutationProof(String guardSiteId,
                                     String mutationSiteId,
                                     String method, int mutationUnitIndex,
                                     boolean requiredOutcome) {
            this.guardSiteId = guardSiteId;
            this.mutationSiteId = mutationSiteId;
            this.method = method;
            this.mutationUnitIndex = mutationUnitIndex;
            this.requiredOutcome = requiredOutcome;
        }
    }

    private static final class RuntimeGuardExclusion {
        private final GuardedMutationProof proof;
        private final int observedOccurrenceCount;

        private RuntimeGuardExclusion(GuardedMutationProof proof,
                                      int observedOccurrenceCount) {
            this.proof = proof;
            this.observedOccurrenceCount = observedOccurrenceCount;
        }

        private JsonObject toMatch(String writeSiteId,
                                   String requestedOutputPort) {
            JsonObject match = new JsonObject();
            match.addProperty("obligationKind",
                    "DECLARED_HEAP_WRITE_SITE");
            match.addProperty("method", proof.method);
            match.addProperty("siteId", writeSiteId);
            match.addProperty("guardSiteId", proof.guardSiteId);
            match.addProperty("requiredOutcome", proof.requiredOutcome);
            match.addProperty("observedOutcome", !proof.requiredOutcome);
            match.addProperty("observedOccurrenceCount",
                    observedOccurrenceCount);
            match.addProperty("requestedOutputPort", requestedOutputPort);
            match.addProperty("authority",
                    "RUNTIME_OBSERVED_DOMINATING_GUARD_EXCLUDES_WRITE");
            return match;
        }
    }

    private static final class ExactOrderedPutBijection {
        private final boolean applicable;
        private final boolean complete;
        private final int matchedCount;
        private final Set<String> coveredWriteSites;
        private final JsonArray matches;
        private final JsonArray gaps;
        private final List<HeapEffectIssue> issues;

        private ExactOrderedPutBijection(
                boolean applicable, boolean complete, int matchedCount,
                Set<String> coveredWriteSites, JsonArray matches,
                JsonArray gaps, List<HeapEffectIssue> issues) {
            this.applicable = applicable;
            this.complete = complete;
            this.matchedCount = matchedCount;
            this.coveredWriteSites = coveredWriteSites;
            this.matches = matches;
            this.gaps = gaps;
            this.issues = issues;
        }

        private static ExactOrderedPutBijection notApplicable() {
            return new ExactOrderedPutBijection(false, false, 0,
                    Collections.<String>emptySet(), new JsonArray(),
                    new JsonArray(),
                    Collections.<HeapEffectIssue>emptyList());
        }

        private static ExactOrderedPutBijection failed(String reason,
                                                       int rawIndex) {
            JsonObject gap = new JsonObject();
            gap.addProperty("kind",
                    "EXACT_ORDERED_MAP_PUT_BIJECTION_FAILED");
            gap.addProperty("reason", reason);
            gap.addProperty("rawConditionIndex", rawIndex);
            JsonArray gaps = new JsonArray();
            gaps.add(gap);
            List<HeapEffectIssue> issues = new ArrayList<>();
            issues.add(new HeapEffectIssue(
                    "EXACT_ORDERED_MAP_PUT_BIJECTION_FAILED", rawIndex,
                    reason, "requested-output-container-transformer"));
            return new ExactOrderedPutBijection(true, false, 0,
                    Collections.<String>emptySet(), new JsonArray(), gaps,
                    issues);
        }

        private static ExactOrderedPutBijection complete(
                List<String> coveredSites, JsonArray matches) {
            return new ExactOrderedPutBijection(true, true,
                    coveredSites.size(),
                    new LinkedHashSet<>(coveredSites), matches.deepCopy(),
                    new JsonArray(),
                    Collections.<HeapEffectIssue>emptyList());
        }
    }

    private static final class StaticHeapTransformerCoverage {
        private final boolean applicable;
        private final boolean exactTransformerContract;
        private final boolean transformerContractValid;
        private final int declaredWriteSiteCount;
        private final int coveredWriteSiteCount;
        private final int uncoveredWriteSiteCount;
        private final int edgeFreeVoidMethodCount;
        private final int applicationProvenanceMatchedTransformerCount;
        private final int guardExcludedWriteSiteCount;
        private final int statePortMatchedTransformerCount;
        private final int unresolvedStatePortEffectCount;
        private final JsonArray matches;
        private final JsonArray gaps;
        private final List<HeapEffectIssue> issues;
        private final Set<String> declaredWriteSites;
        private final Map<String, RuntimeGuardExclusion>
                guardExcludedWriteSites;

        private StaticHeapTransformerCoverage(
                boolean applicable, boolean exactTransformerContract,
                boolean transformerContractValid,
                int declaredWriteSiteCount,
                int coveredWriteSiteCount, int uncoveredWriteSiteCount,
                int edgeFreeVoidMethodCount,
                int applicationProvenanceMatchedTransformerCount,
                int guardExcludedWriteSiteCount,
                int statePortMatchedTransformerCount,
                int unresolvedStatePortEffectCount, JsonArray matches,
                JsonArray gaps, List<HeapEffectIssue> issues,
                Set<String> declaredWriteSites,
                Map<String, RuntimeGuardExclusion>
                        guardExcludedWriteSites) {
            this.applicable = applicable;
            this.exactTransformerContract = exactTransformerContract;
            this.transformerContractValid = transformerContractValid;
            this.declaredWriteSiteCount = declaredWriteSiteCount;
            this.coveredWriteSiteCount = coveredWriteSiteCount;
            this.uncoveredWriteSiteCount = uncoveredWriteSiteCount;
            this.edgeFreeVoidMethodCount = edgeFreeVoidMethodCount;
            this.applicationProvenanceMatchedTransformerCount =
                    applicationProvenanceMatchedTransformerCount;
            this.guardExcludedWriteSiteCount = guardExcludedWriteSiteCount;
            this.statePortMatchedTransformerCount =
                    statePortMatchedTransformerCount;
            this.unresolvedStatePortEffectCount =
                    unresolvedStatePortEffectCount;
            this.matches = matches;
            this.gaps = gaps;
            this.issues = issues;
            this.declaredWriteSites = new LinkedHashSet<>(
                    declaredWriteSites);
            this.guardExcludedWriteSites = new LinkedHashMap<>(
                    guardExcludedWriteSites);
        }

        private static StaticHeapTransformerCoverage notApplicable() {
            return new StaticHeapTransformerCoverage(false, false, false,
                    0, 0, 0, 0, 0, 0, 0, 0, new JsonArray(),
                    new JsonArray(),
                    Collections.<HeapEffectIssue>emptyList(),
                    Collections.<String>emptySet(),
                    Collections.<String, RuntimeGuardExclusion>emptyMap());
        }

        private boolean complete() {
            return issues.isEmpty()
                    && uncoveredWriteSiteCount == 0
                    && edgeFreeVoidMethodCount == 0
                    && unresolvedStatePortEffectCount == 0;
        }

        private boolean allWritesGuardExcluded() {
            return applicable && complete()
                    && declaredWriteSiteCount > 0
                    && guardExcludedWriteSiteCount
                    == declaredWriteSiteCount;
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("policy",
                    exactTransformerContract
                            ? "EXACT_REQUESTED_STATE_TRANSFORMER_"
                            + "RUNTIME_PATH_COVERAGE_V5"
                            : "REQUESTED_OUTPUT_RUNTIME_PATH_"
                            + "TRANSFORMER_COVERAGE_V4_LEGACY_FAIL_CLOSED");
            result.addProperty("applicable", applicable);
            result.addProperty("exactRequestedStateTransformerContract",
                    exactTransformerContract);
            result.addProperty("requestedStateTransformerContractValid",
                    transformerContractValid);
            result.addProperty("declaredWriteSiteCount",
                    declaredWriteSiteCount);
            result.addProperty("coveredWriteSiteCount",
                    coveredWriteSiteCount);
            result.addProperty("uncoveredWriteSiteCount",
                    uncoveredWriteSiteCount);
            result.addProperty("edgeFreeVoidMethodCount",
                    edgeFreeVoidMethodCount);
            result.addProperty(
                    "applicationProvenanceMatchedTransformerCount",
                    applicationProvenanceMatchedTransformerCount);
            result.addProperty("guardExcludedWriteSiteCount",
                    guardExcludedWriteSiteCount);
            result.addProperty("statePortMatchedTransformerCount",
                    statePortMatchedTransformerCount);
            result.addProperty("unresolvedStatePortEffectCount",
                    unresolvedStatePortEffectCount);
            result.add("matches", matches.deepCopy());
            result.add("gaps", gaps.deepCopy());
            result.addProperty("complete", complete());
            return result;
        }
    }

    private static final class HeapEffectExtraction {
        private final JsonArray initializers;
        private final JsonArray effects;
        private final JsonArray observations;
        private final JsonArray finiteMapSnapshots;
        private final JsonArray dynamicFieldBindings;
        private final JsonArray ignoredEvidence;
        private final List<HeapEffectIssue> issues;
        private final Map<String, HeapOutputBinding> outputBindings;
        private final int candidateCount;
        private final int mapStateFamilyCount;
        private final int unsupportedMutationCount;
        private final int malformedMutationCount;
        private final int syntheticInputCount;
        private final int initializedInputCount;
        private final int unboundFinalOutputCount;
        private final int intermediateStateCount;
        private final int identityEffectCount;
        private final StaticHeapTransformerCoverage staticCoverage;
        private final RuntimeHeapEffectJoin runtimeJoin;
        private final HeapObservationExtraction observationExtraction;

        private HeapEffectExtraction(
                JsonArray initializers, JsonArray effects,
                JsonArray observations, JsonArray finiteMapSnapshots,
                JsonArray dynamicFieldBindings,
                JsonArray ignoredEvidence,
                List<HeapEffectIssue> issues,
                Map<String, HeapOutputBinding> outputBindings,
                int candidateCount, int mapStateFamilyCount,
                int unsupportedMutationCount, int malformedMutationCount,
                int syntheticInputCount, int initializedInputCount,
                int unboundFinalOutputCount,
                int intermediateStateCount,
                int identityEffectCount,
                StaticHeapTransformerCoverage staticCoverage,
                RuntimeHeapEffectJoin runtimeJoin,
                HeapObservationExtraction observationExtraction) {
            this.initializers = initializers;
            this.effects = effects;
            this.observations = observations;
            this.finiteMapSnapshots = finiteMapSnapshots;
            this.dynamicFieldBindings = dynamicFieldBindings;
            this.ignoredEvidence = ignoredEvidence;
            this.issues = issues;
            this.outputBindings = outputBindings;
            this.candidateCount = candidateCount;
            this.mapStateFamilyCount = mapStateFamilyCount;
            this.unsupportedMutationCount = unsupportedMutationCount;
            this.malformedMutationCount = malformedMutationCount;
            this.syntheticInputCount = syntheticInputCount;
            this.initializedInputCount = initializedInputCount;
            this.unboundFinalOutputCount = unboundFinalOutputCount;
            this.intermediateStateCount = intermediateStateCount;
            this.identityEffectCount = identityEffectCount;
            this.staticCoverage = staticCoverage;
            this.runtimeJoin = runtimeJoin;
            this.observationExtraction = observationExtraction;
        }

        private JsonObject model() {
            JsonObject model = new JsonObject();
            model.addProperty("policy",
                    "RAW_SEMANTIC_PATH_ORDER_MAP_STATE_SSA");
            model.addProperty("candidateMutationCount", candidateCount);
            model.addProperty("effectCount", effects.size());
            model.addProperty("observationCount", observations.size());
            model.addProperty("finiteMapSnapshotCount",
                    finiteMapSnapshots.size());
            model.addProperty("ignoredRuntimeHeapEvidenceCount",
                    ignoredEvidence.size());
            model.add("ignoredRuntimeHeapEvidence",
                    ignoredEvidence.deepCopy());
            model.addProperty("identityEffectCount", identityEffectCount);
            model.addProperty("mapStateFamilyCount", mapStateFamilyCount);
            model.addProperty("unsupportedMutationCount",
                    unsupportedMutationCount);
            model.addProperty("malformedMutationCount",
                    malformedMutationCount);
            model.addProperty("syntheticInputCount", syntheticInputCount);
            model.addProperty("initializedInputCount",
                    initializedInputCount);
            model.addProperty("initializerCount", initializers.size());
            model.addProperty("unboundFinalOutputCount",
                    unboundFinalOutputCount);
            model.addProperty("intermediateStateCount",
                    intermediateStateCount);
            model.add("staticTransformerCoverage",
                    staticCoverage.toJson());
            model.add("runtimeHeapEffectJoin", runtimeJoin.toJson());
            model.add("runtimeHeapObservationImport",
                    observationExtraction.toJson());
            model.addProperty("complete", complete());
            return model;
        }

        private boolean complete() {
            return issues.isEmpty() && staticCoverage.complete()
                    && observationExtraction.complete();
        }

        private void bindOutputExpressions(JsonObject outputs) {
            for (Map.Entry<String, HeapOutputBinding> entry
                    : outputBindings.entrySet()) {
                HeapOutputBinding binding = entry.getValue();
                JsonObject expression = new JsonObject();
                expression.addProperty("kind", "HEAP_STATE_VERSION");
                expression.addProperty("stateId", binding.stateId);
                expression.addProperty("stateFamily", binding.stateFamily);
                expression.addProperty("effectId", binding.effectId);
                expression.addProperty("sourcePort", binding.sourcePort);
                outputs.add(entry.getKey(), expression);
            }
        }
    }

    private static final class FreshMapInitializerResolution {
        private final JsonObject evidence;
        private final int candidateCount;

        private FreshMapInitializerResolution(JsonObject evidence,
                                              int candidateCount) {
            this.evidence = evidence;
            this.candidateCount = candidateCount;
        }

        private static FreshMapInitializerResolution none() {
            return new FreshMapInitializerResolution(null, 0);
        }

        private static FreshMapInitializerResolution of(
                List<JsonObject> candidates) {
            return new FreshMapInitializerResolution(
                    candidates.size() == 1 ? candidates.get(0) : null,
                    candidates.size());
        }

        private boolean resolved() {
            return evidence != null && candidateCount == 1;
        }

        private boolean ambiguous() {
            return candidateCount > 1;
        }

        private String outputPort() {
            return resolved() ? string(evidence, "outputPort") : "";
        }

        private JsonObject toSummary(String initializerId,
                                     String statePort,
                                     String stateFamily,
                                     String stateId) {
            JsonObject result = new JsonObject();
            result.addProperty("initializerId", initializerId);
            result.addProperty("kind", "MAP_EMPTY");
            result.addProperty("statePort", statePort);
            result.addProperty("stateFamily", stateFamily);
            result.addProperty("stateId", stateId);
            result.addProperty("requestedOutputPort",
                    string(evidence, "outputPort"));
            result.addProperty("allocatedType",
                    string(evidence, "allocatedType"));
            result.addProperty("staticInitializerId",
                    string(evidence, "initializerId"));
            result.addProperty("allocationEdgeId",
                    string(evidence, "allocationEdgeId"));
            result.addProperty("allocationMethod",
                    string(evidence, "allocationMethod"));
            result.addProperty("allocationSiteId",
                    string(evidence, "allocationSiteId"));
            result.addProperty("constructor",
                    string(evidence, "constructor"));
            result.addProperty("constructorArgumentCount",
                    integer(evidence, "constructorArgumentCount", -1));
            result.add("proofEdgeIds", copy(evidence.get("proofEdgeIds"),
                    new JsonArray()));
            result.addProperty("proofComplete",
                    bool(evidence, "proofComplete", false));
            result.addProperty("bindingAuthority",
                    "STATIC_UNIQUE_DEFAULT_ALLOCATION_TO_REQUESTED_OUTPUT_"
                            + "PLUS_RUNTIME_UNIQUE_MAP_RECEIVER");
            result.addProperty("emptyStateAuthority",
                    "JAVA_PLATFORM_DEFAULT_MAP_CONSTRUCTOR_SEMANTICS");
            return result;
        }
    }

    private static final class HeapPortBinding {
        private final boolean resolved;
        private final String inputPort;
        private final String outputPort;

        private HeapPortBinding(boolean resolved, String inputPort,
                                String outputPort) {
            this.resolved = resolved;
            this.inputPort = inputPort;
            this.outputPort = outputPort;
        }

        private static HeapPortBinding resolved(String inputPort,
                                                String outputPort) {
            return new HeapPortBinding(true, inputPort, outputPort);
        }

        private static HeapPortBinding unresolved() {
            return new HeapPortBinding(false, "", "");
        }
    }

    private static final class HeapPortResolver {
        private final JsonObject activation;
        private final JsonArray symbolize;
        private final JsonArray outputs;

        private HeapPortResolver(JsonObject activation) {
            this.activation = activation;
            this.symbolize = runtimeMaterializationActions(activation);
            this.outputs = array(activation, "outputs");
        }

        private FreshMapInitializerResolution freshMapInitializer(
                HeapMutation mutation) {
            if (!requestedOutputSliceContractOperationallyAdmitted(
                    activation)) {
                return FreshMapInitializerResolution.none();
            }
            JsonObject requested = object(activation, "requestedOutput");
            String requestedPort = firstNonBlank(string(requested, "portId"),
                    string(requested, "symbol"));
            if (requestedPort.isEmpty()
                    || !"HEAP_STATE".equals(string(requested, "kind"))) {
                return FreshMapInitializerResolution.none();
            }
            JsonObject slice = object(activation, "requestedOutputSlice");
            if (!requestedPort.equals(string(slice, "outputPort"))) {
                return FreshMapInitializerResolution.none();
            }

            String methodOwner = normalizeType(mutation.method.owner);
            String expressionType = mutation.mapExpression.isJsonObject()
                    ? normalizeType(string(
                    mutation.mapExpression.getAsJsonObject(), "_java_type"))
                    : "";
            List<JsonObject> candidates = new ArrayList<>();
            for (JsonElement element : array(slice, "heapInitializers")) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject initializer = element.getAsJsonObject();
                String allocatedType = normalizeType(string(initializer,
                        "allocatedType"));
                String constructor = string(initializer, "constructor");
                String allocationEdgeId = string(initializer,
                        "allocationEdgeId");
                JsonArray proofEdgeIds = array(initializer, "proofEdgeIds");
                if (!"FRESH_DEFAULT_CONSTRUCTED_OBJECT".equals(
                        string(initializer, "kind"))
                        || !bool(initializer, "proofComplete", false)
                        || integer(initializer,
                        "constructorArgumentCount", -1) != 0
                        || !"STATIC_ALLOCATION_CONSTRUCTOR_AND_"
                        .concat("FORWARD_CAUSAL_PATH").equals(
                                string(initializer, "selectionAuthority"))
                        || allocationEdgeId.isEmpty()
                        || !containsString(proofEdgeIds, allocationEdgeId)
                        || !defaultConstructorMatches(constructor,
                        allocatedType)
                        || !requestedPort.equals(string(initializer,
                        "outputPort"))
                        || !"REGION_ROOT_ENTRY_PRECEDES_ALLOCATION".equals(
                        string(initializer,
                                "captureBoundaryRequirement"))
                        || !knownEmptyMapType(allocatedType)
                        || (!allocatedType.equals(methodOwner)
                        && !allocatedType.equals(expressionType))) {
                    continue;
                }
                candidates.add(initializer);
            }
            return FreshMapInitializerResolution.of(candidates);
        }

        private static String normalizeType(String type) {
            return type == null ? "" : type.trim().replace('/', '.');
        }

        private static boolean defaultConstructorMatches(String constructor,
                                                         String type) {
            String normalized = normalizeType(constructor);
            return !type.isEmpty()
                    && normalized.contains("<" + type + ":")
                    && normalized.contains("<init>()");
        }

        private static boolean containsString(JsonArray values,
                                              String expected) {
            for (JsonElement value : values) {
                if (value.isJsonPrimitive()
                        && expected.equals(value.getAsString())) {
                    return true;
                }
            }
            return false;
        }

        private static boolean knownEmptyMapType(String type) {
            return "java.util.HashMap".equals(type)
                    || "java.util.LinkedHashMap".equals(type)
                    || "java.util.TreeMap".equals(type)
                    || "java.util.Hashtable".equals(type)
                    || "java.util.WeakHashMap".equals(type)
                    || "java.util.IdentityHashMap".equals(type)
                    || "java.util.concurrent.ConcurrentHashMap".equals(type)
                    || "java.util.concurrent.ConcurrentSkipListMap".equals(
                    type);
        }

        private String inputPort(JsonElement mapExpression) {
            Set<String> best = inputPortCandidates(mapExpression);
            return best.size() == 1 ? best.iterator().next() : "";
        }

        private Set<String> inputPortCandidates(JsonElement mapExpression) {
            Set<String> expressionSymbols = new LinkedHashSet<>();
            collectExpressionSymbols(mapExpression, expressionSymbols);
            Set<String> candidates = new LinkedHashSet<>();
            for (JsonElement element : symbolize) {
                if (!element.isJsonObject()) {
                    continue;
                }
                String symbol = string(element.getAsJsonObject(), "symbol");
                if (symbol.isEmpty()) {
                    continue;
                }
                for (String expressionSymbol : expressionSymbols) {
                    if (containsSymbolReference(expressionSymbol, symbol)) {
                        candidates.add(symbol);
                        break;
                    }
                }
            }
            if (candidates.isEmpty()) {
                for (String expressionSymbol : expressionSymbols) {
                    Matcher matcher = REGION_INPUT_PORT.matcher(
                            expressionSymbol);
                    while (matcher.find()) {
                        candidates.add(matcher.group(1));
                    }
                }
            }
            int longest = 0;
            Set<String> best = new LinkedHashSet<>();
            for (String candidate : candidates) {
                if (candidate.length() > longest) {
                    best.clear();
                    longest = candidate.length();
                }
                if (candidate.length() == longest) {
                    best.add(candidate);
                }
            }
            return best;
        }

        private HeapPortBinding requestedOutputBinding(
                JsonElement mapExpression) {
            JsonObject requested = object(activation, "requestedOutput");
            String requestedPort = firstNonBlank(
                    string(requested, "portId"),
                    string(requested, "symbol"));
            JsonObject slice = object(activation, "requestedOutputSlice");
            String slicePort = string(slice, "outputPort");
            if (!"HEAP_STATE".equals(string(requested, "kind"))
                    || requestedPort.isEmpty()
                    || !slicePort.isEmpty()
                    && !requestedPort.equals(slicePort)) {
                return HeapPortBinding.unresolved();
            }
            String inputPort = inputPort(mapExpression);
            if (inputPort.isEmpty()) {
                return HeapPortBinding.unresolved();
            }
            String outputPort = outputPort(inputPort);
            return requestedPort.equals(outputPort)
                    ? HeapPortBinding.resolved(inputPort, outputPort)
                    : HeapPortBinding.unresolved();
        }

        private static void collectExpressionSymbols(
                JsonElement expression, Set<String> result) {
            if (expression == null || expression.isJsonNull()) {
                return;
            }
            if (expression.isJsonArray()) {
                for (JsonElement item : expression.getAsJsonArray()) {
                    collectExpressionSymbols(item, result);
                }
                return;
            }
            if (!expression.isJsonObject()) {
                return;
            }
            JsonObject object = expression.getAsJsonObject();
            JsonElement symbol = object.get("_exp");
            if (symbol != null && symbol.isJsonPrimitive()
                    && symbol.getAsJsonPrimitive().isString()) {
                result.add(symbol.getAsString());
            }
            for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
                if (!"_exp".equals(entry.getKey())
                        && !"_code_position".equals(entry.getKey())) {
                    collectExpressionSymbols(entry.getValue(), result);
                }
            }
        }

        private static boolean containsSymbolReference(String expression,
                                                       String symbol) {
            int start = expression.indexOf(symbol);
            while (start >= 0) {
                int end = start + symbol.length();
                boolean leftBoundary = start == 0
                        || !Character.isLetterOrDigit(
                        expression.charAt(start - 1));
                boolean rightBoundary = end == expression.length()
                        || !Character.isLetterOrDigit(expression.charAt(end));
                if (leftBoundary && rightBoundary) {
                    return true;
                }
                start = expression.indexOf(symbol, start + 1);
            }
            return false;
        }

        private String outputPort(String inputPort) {
            Set<String> matches = new LinkedHashSet<>();
            for (JsonElement element : array(activation,
                    "heapStateBindings")) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject binding = element.getAsJsonObject();
                String declaredInput = firstNonBlank(
                        string(binding, "inputPort"),
                        string(binding, "inputSymbol"),
                        string(binding, "mapInputPort"));
                if (inputPort.equals(declaredInput)) {
                    String declaredOutput = firstNonBlank(
                            string(binding, "outputPort"),
                            string(binding, "outputSymbol"),
                            string(binding, "mapOutputPort"));
                    if (!declaredOutput.isEmpty()) {
                        matches.add(declaredOutput);
                    }
                }
            }

            JsonObject input = symbolizeAction(inputPort);
            if (input != null) {
                String explicit = firstNonBlank(
                        string(input, "outputPort"),
                        string(input, "heapOutputPort"),
                        string(input, "postStatePort"));
                if (!explicit.isEmpty()) {
                    matches.add(explicit);
                }
                String byField = uniqueHeapOutput(string(input, "field"));
                if (!byField.isEmpty()) {
                    matches.add(byField);
                }
                String byCell = uniqueHeapOutput(string(input, "cell"));
                if (!byCell.isEmpty()) {
                    matches.add(byCell);
                }
            }
            return matches.size() == 1 ? matches.iterator().next() : "";
        }

        private JsonObject symbolizeAction(String inputPort) {
            for (JsonElement element : symbolize) {
                if (element.isJsonObject()
                        && inputPort.equals(string(element.getAsJsonObject(),
                        "symbol"))) {
                    return element.getAsJsonObject();
                }
            }
            return null;
        }

        private String uniqueHeapOutput(String cell) {
            if (cell.isEmpty()) {
                return "";
            }
            Set<String> matches = new LinkedHashSet<>();
            for (JsonElement element : outputs) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject output = element.getAsJsonObject();
                if (!"HEAP_STATE".equals(string(output, "kind"))
                        || !cell.equals(string(output, "cell"))) {
                    continue;
                }
                String symbol = firstNonBlank(string(output, "symbol"),
                        string(output, "portId"));
                if (!symbol.isEmpty()) {
                    matches.add(symbol);
                }
            }
            return matches.size() == 1 ? matches.iterator().next() : "";
        }
    }

    private static final class ArrayEventCatalog {
        private final Set<String> loadIds = new LinkedHashSet<>();
        private final List<String> issues = new ArrayList<>();
    }

    private static final class EngineArrayInputBindingIssue {
        private final String code;
        private final String detail;

        private EngineArrayInputBindingIssue(String code, String detail) {
            this.code = code;
            this.detail = detail;
        }
    }

    private static final class EngineArrayInputBindingExtraction {
        private final JsonArray bindings;
        private final boolean complete;
        private final List<EngineArrayInputBindingIssue> issues;

        private EngineArrayInputBindingExtraction(
                JsonArray bindings, boolean complete,
                List<EngineArrayInputBindingIssue> issues) {
            this.bindings = bindings;
            this.complete = complete;
            this.issues = issues;
        }
    }

    private static final class PathAdmissionPolicy {
        private final Set<String> methodKeys;
        private final List<String> boundaries;
        private final String policy;

        private PathAdmissionPolicy(Set<String> methodKeys,
                                    List<String> boundaries, String policy) {
            this.methodKeys = methodKeys;
            this.boundaries = boundaries;
            this.policy = policy;
        }

        private String rejectionReason(String codePosition) {
            if (codePosition == null || codePosition.trim().isEmpty()) {
                return "MISSING_CODE_POSITION";
            }
            String methodKey = ConcolicCodePosition.vmMethodKey(codePosition);
            if (!methodKey.isEmpty() && methodKeys.contains(methodKey)) {
                return "";
            }
            String normalized = codePosition.replace('/', '.');
            for (String boundary : boundaries) {
                if (normalized.contains(boundary)) {
                    return "";
                }
            }
            return methodKeys.isEmpty() && boundaries.isEmpty()
                    ? "NO_DECLARED_SEMANTIC_METHOD_BOUNDARY"
                    : "OUTSIDE_REGION_SEMANTIC_METHOD_BOUNDARY";
        }
    }

    private static final class DynamicRawPcCandidate {
        private final int rawIndex;
        private final JsonObject rawCondition;
        private final JsonObject fieldExpression;
        private final String codePosition;

        private DynamicRawPcCandidate(int rawIndex, JsonObject rawCondition,
                                      JsonObject fieldExpression,
                                      String codePosition) {
            this.rawIndex = rawIndex;
            this.rawCondition = rawCondition.deepCopy();
            this.fieldExpression = fieldExpression.deepCopy();
            this.codePosition = codePosition;
        }
    }

    private static final class DynamicSemanticPcFallback {
        private final String dynamicFieldSymbol;
        private final String baseInputSymbol;
        private final String entryReadObservationId;
        private final String branchSiteId;
        private final int rawIndex;
        private final JsonObject rawCondition;
        private final JsonObject fieldExpression;
        private final JsonObject semanticCondition;
        private final String codePosition;
        private final String authority;

        private DynamicSemanticPcFallback(
                String dynamicFieldSymbol, String baseInputSymbol,
                String entryReadObservationId, String branchSiteId,
                int rawIndex, JsonObject rawCondition,
                JsonObject fieldExpression, JsonObject semanticCondition,
                String codePosition, String authority) {
            this.dynamicFieldSymbol = dynamicFieldSymbol;
            this.baseInputSymbol = baseInputSymbol;
            this.entryReadObservationId = entryReadObservationId;
            this.branchSiteId = branchSiteId;
            this.rawIndex = rawIndex;
            this.rawCondition = rawCondition.deepCopy();
            this.fieldExpression = fieldExpression.deepCopy();
            this.semanticCondition = semanticCondition.deepCopy();
            this.codePosition = codePosition;
            this.authority = authority;
        }
    }

    private static final class DynamicSemanticPcFallbackCatalog {
        private final Map<String, DynamicSemanticPcFallback> byDynamicSymbol;
        private final Map<Integer, DynamicSemanticPcFallback> byRawIndex;

        private DynamicSemanticPcFallbackCatalog(
                Map<String, DynamicSemanticPcFallback> byDynamicSymbol,
                Map<Integer, DynamicSemanticPcFallback> byRawIndex) {
            this.byDynamicSymbol = byDynamicSymbol;
            this.byRawIndex = byRawIndex;
        }

        private boolean hasBase(String baseInputSymbol) {
            for (DynamicSemanticPcFallback fallback
                    : byDynamicSymbol.values()) {
                if (baseInputSymbol.equals(fallback.baseInputSymbol)) {
                    return true;
                }
            }
            return false;
        }
    }

    private static final class CertifiedConcreteGuardCatalog {
        private final List<CertifiedConcreteGuard> guards;
        private final List<String> issues;

        private CertifiedConcreteGuardCatalog(
                List<CertifiedConcreteGuard> guards,
                List<String> issues) {
            this.guards = new ArrayList<>(guards);
            this.issues = new ArrayList<>(issues);
        }

        private List<CertifiedConcreteGuard> atBoundary(int boundary) {
            List<CertifiedConcreteGuard> result = new ArrayList<>();
            for (CertifiedConcreteGuard guard : guards) {
                if (guard.rawBoundary == boundary) result.add(guard);
            }
            return result;
        }
    }

    private static final class ConcreteGuardProofCatalog {
        private final List<JsonObject> proofs;
        private final List<String> issues;

        private ConcreteGuardProofCatalog(List<JsonObject> proofs,
                                          List<String> issues) {
            this.proofs = new ArrayList<>(proofs);
            this.issues = new ArrayList<>(issues);
        }

        private List<JsonObject> forEvent(JsonObject mapping) {
            List<JsonObject> result = new ArrayList<>();
            String site = strictString(mapping, "siteId");
            Integer occurrence = strictInteger(mapping, "occurrence");
            if (site.isEmpty() || occurrence == null) return result;
            for (JsonObject proof : proofs) {
                if (site.equals(strictString(proof, "siteId"))
                        && occurrence.equals(strictInteger(proof,
                        "occurrence"))) {
                    result.add(proof);
                }
            }
            return result;
        }
    }

    private static final class CertifiedConcreteGuard {
        private final String identity;
        private final int rawBoundary;
        private final int mappingOrdinal;
        private final JsonElement condition;

        private CertifiedConcreteGuard(String identity, int rawBoundary,
                                       int mappingOrdinal,
                                       JsonElement condition) {
            this.identity = identity;
            this.rawBoundary = rawBoundary;
            this.mappingOrdinal = mappingOrdinal;
            this.condition = condition.deepCopy();
        }
    }

    private static final class SyntheticConditionNormalization {
        private final String identity;
        private final int rawBoundary;
        private final int normalizedIndex;
        private final int normalizedBaseline;
        private final int normalizedSize;

        private SyntheticConditionNormalization(
                String identity, int rawBoundary, int normalizedIndex,
                int normalizedBaseline, int normalizedSize) {
            this.identity = identity;
            this.rawBoundary = rawBoundary;
            this.normalizedIndex = normalizedIndex;
            this.normalizedBaseline = normalizedBaseline;
            this.normalizedSize = normalizedSize;
        }
    }

    private static final class PathNormalization {
        private final JsonArray conditions;
        private final int[] rawToNormalized;
        private final String[] statuses;
        private final String[] reasons;
        private final String[] codePositions;
        private final String[] admissionAuthorities;
        private final int semanticConditionCount;
        private final int filteredConditionCount;
        private final int duplicateConditionCount;
        private final int semanticBranchConditionSubstitutionCount;
        private final int[] normalizedBoundaries;
        private final Map<String, Integer> syntheticToNormalized;
        private final Map<String, Integer> syntheticBaselines;
        private final Map<String, Integer> syntheticSizes;
        private final List<SyntheticConditionNormalization> syntheticRows;
        private final int syntheticConditionCount;

        private PathNormalization(JsonArray conditions,
                                  int[] rawToNormalized,
                                  String[] statuses,
                                  String[] reasons,
                                  String[] codePositions,
                                  String[] admissionAuthorities,
                                  int semanticConditionCount,
                                  int filteredConditionCount,
                                  int duplicateConditionCount,
                                  int semanticBranchConditionSubstitutionCount,
                                  int[] normalizedBoundaries,
                                  Map<String, Integer> syntheticToNormalized,
                                  Map<String, Integer> syntheticBaselines,
                                  Map<String, Integer> syntheticSizes,
                                  List<SyntheticConditionNormalization>
                                          syntheticRows) {
            this.conditions = conditions;
            this.rawToNormalized = rawToNormalized;
            this.statuses = statuses;
            this.reasons = reasons;
            this.codePositions = codePositions;
            this.admissionAuthorities = admissionAuthorities;
            this.semanticConditionCount = semanticConditionCount;
            this.filteredConditionCount = filteredConditionCount;
            this.duplicateConditionCount = duplicateConditionCount;
            this.semanticBranchConditionSubstitutionCount =
                    semanticBranchConditionSubstitutionCount;
            this.normalizedBoundaries = normalizedBoundaries.clone();
            this.syntheticToNormalized = new LinkedHashMap<>(
                    syntheticToNormalized);
            this.syntheticBaselines = new LinkedHashMap<>(
                    syntheticBaselines);
            this.syntheticSizes = new LinkedHashMap<>(syntheticSizes);
            this.syntheticRows = new ArrayList<>(syntheticRows);
            this.syntheticConditionCount = syntheticRows.size();
        }

        private int index(int rawIndex) {
            return rawIndex < 0 || rawIndex >= rawToNormalized.length
                    ? -1 : rawToNormalized[rawIndex];
        }

        private boolean isSemantic(int rawIndex) {
            return rawIndex >= 0 && rawIndex < statuses.length
                    && !"FILTERED".equals(statuses[rawIndex]);
        }

        private String status(int rawIndex) {
            return rawIndex < 0 || rawIndex >= statuses.length
                    ? "UNKNOWN" : statuses[rawIndex];
        }

        private String admissionAuthority(int rawIndex) {
            return rawIndex < 0 || rawIndex >= admissionAuthorities.length
                    ? "" : admissionAuthorities[rawIndex];
        }

        private int boundary(int rawBoundary) {
            if (rawBoundary < 0) {
                return 0;
            }
            int boundary = Math.min(rawBoundary,
                    normalizedBoundaries.length - 1);
            return normalizedBoundaries[boundary];
        }

        private boolean hasSynthetic(String identity) {
            return identity != null && !identity.isEmpty()
                    && syntheticToNormalized.containsKey(identity);
        }

        private int syntheticIndex(String identity) {
            Integer value = syntheticToNormalized.get(identity);
            return value == null ? -1 : value;
        }

        private int syntheticBaseline(String identity) {
            Integer value = syntheticBaselines.get(identity);
            return value == null ? -1 : value;
        }

        private int syntheticSize(String identity) {
            Integer value = syntheticSizes.get(identity);
            return value == null ? -1 : value;
        }

        private JsonArray indexMap() {
            JsonArray result = new JsonArray();
            for (int index = 0; index < rawToNormalized.length; index++) {
                JsonObject item = new JsonObject();
                item.addProperty("rawConditionIndex", index);
                item.addProperty("normalizedConditionIndex",
                        rawToNormalized[index]);
                item.addProperty("status", statuses[index]);
                item.addProperty("codePosition", codePositions[index]);
                if (admissionAuthorities[index] != null
                        && !admissionAuthorities[index].isEmpty()) {
                    item.addProperty("admissionAuthority",
                            admissionAuthorities[index]);
                }
                if (reasons[index] != null && !reasons[index].isEmpty()) {
                    item.addProperty("reason", reasons[index]);
                }
                result.add(item);
            }
            for (SyntheticConditionNormalization synthetic
                    : syntheticRows) {
                JsonObject item = new JsonObject();
                item.addProperty("rawConditionIndex", -1);
                item.addProperty("rawBoundary", synthetic.rawBoundary);
                item.addProperty("syntheticConditionKey",
                        synthetic.identity);
                item.addProperty("normalizedConditionIndex",
                        synthetic.normalizedIndex);
                item.addProperty("normalizedPathConditionBaseline",
                        synthetic.normalizedBaseline);
                item.addProperty("normalizedPathConditionSize",
                        synthetic.normalizedSize);
                item.addProperty("status", "SYNTHETIC_RETAINED");
                item.addProperty("admissionAuthority",
                        CERTIFIED_CONCRETE_GUARD_AUTHORITY);
                result.add(item);
            }
            return result;
        }

        private JsonArray filteredConditions() {
            JsonArray result = new JsonArray();
            for (int index = 0; index < rawToNormalized.length; index++) {
                if (!"FILTERED".equals(statuses[index])) {
                    continue;
                }
                JsonObject item = new JsonObject();
                item.addProperty("rawConditionIndex", index);
                item.addProperty("codePosition", codePositions[index]);
                item.addProperty("reason", reasons[index]);
                result.add(item);
            }
            return result;
        }
    }
}
