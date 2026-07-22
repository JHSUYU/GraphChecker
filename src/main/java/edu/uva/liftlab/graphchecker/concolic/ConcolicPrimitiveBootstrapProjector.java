package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
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
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Projects one Z3-selected Boolean root valuation from a structurally complete
 * bootstrap composition onto real producer activation inputs.
 *
 * <p>The result is an ALL bundle: producer rows materialize only their real
 * input definitions and execute in concrete-replay mode, while the target row
 * remains engine-backed and observes the directed bug branch.  The projector
 * never accepts a caller-provided formula or valuation.  It consumes the
 * exhaustive bootstrap report, rechecks the selected valuation in Z3, and
 * uses the composer's case selectors to choose exact source summaries and
 * activation rows.</p>
 */
public final class ConcolicPrimitiveBootstrapProjector {
    private static final String NULLABLE_STRING_ENCODING_AUTHORITY =
            "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1";
    private static final String DYNAMIC_CONTAINER_FIELD_KIND =
            "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING";
    private static final String DYNAMIC_MAP_ENTRY_FIELD_KIND =
            "DYNAMIC_MAP_ENTRY_FIELD_BINDING";
    private static final String DYNAMIC_CONTAINER_FIELD_AUTHORITY =
            "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_AND_"
                    + "STABLE_FIELD_SITE_OCCURRENCE";
    private static final String DYNAMIC_MAP_ENTRY_FIELD_AUTHORITY =
            "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                    + "FIELD_SITE_OCCURRENCE";
    private static final String FRESH_MAP_ENTRY_REBINDING_AUTHORITY =
            "EXACT_BASE_PORT_GETTER_SITE_OCCURRENCE_THEN_"
                    + "FRESH_ENTRY_REBIND_V1";
    private static final String CONTAINER_REPLAY_REBINDING_AUTHORITY =
            "EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                    + "IDENTITY_REBIND_V1";
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();
    private static final Gson JSONL_GSON = new GsonBuilder()
            .disableHtmlEscaping().create();
    private static final Pattern SAFE_SMT_ATOM = Pattern.compile(
            "[A-Za-z_~!@$%^&*+=<>.?/][A-Za-z0-9_~!@$%^&*+\\-=<>.?/]*");

    private ConcolicPrimitiveBootstrapProjector() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        Result result = project(arguments);
        writeJsonl(arguments.output, result.activations);
        JsonObject manifest = result.manifest.deepCopy();
        manifest.add("activationPlanArtifact", artifact(arguments.output));
        write(arguments.manifest, GSON.toJson(manifest)
                + System.lineSeparator());
        System.out.println(GSON.toJson(manifest));
    }

    static Result project(Arguments arguments) throws Exception {
        require(arguments.smt, "bootstrap SMT");
        require(arguments.compositionManifest, "composition manifest");
        require(arguments.reachReport, "bootstrap Boolean report");
        require(arguments.summaries, "producer summary ledger");
        require(arguments.activations, "producer activation ledger");
        require(arguments.targetActivations, "target activation plan");
        require(arguments.fatalQueries, "bootstrap fatal query");

        String smt = readText(arguments.smt);
        JsonObject composition = readJson(arguments.compositionManifest);
        JsonObject reach = readJson(arguments.reachReport);
        validateBootstrapInputs(composition, reach, smt, arguments);

        JsonObject valuation = selectedValuation(reach);
        Map<String, JsonObject> assignmentByPort = valuationAssignments(
                valuation, array(reach, "rootBooleanInputs"));
        ScalarRootCatalog scalarRoots = scalarRootCatalog(reach,
                assignmentByPort.keySet());
        List<JsonObject> cases = objects(array(composition,
                "caseProjectionCatalog"));
        List<String> selectors = selectors(cases);
        List<String> rootTerms = new ArrayList<>();
        for (JsonObject assignment : assignmentByPort.values()) {
            rootTerms.add(string(assignment, "solverTerm"));
        }
        LinkedHashSet<String> queried = new LinkedHashSet<>();
        queried.addAll(selectors);
        queried.addAll(rootTerms);
        queried.addAll(scalarRoots.solverTerms());
        String solverInput = solverInput(smt, assignmentByPort.values(),
                queried);
        SolverIdentity solverIdentity = attestSolver(arguments.z3,
                arguments.timeoutMillis);
        SolverOutput solver = run(solverIdentity, solverInput,
                arguments.timeoutMillis);
        if (solver.timedOut || solver.exitCode != 0
                || !"sat".equals(firstLine(solver.stdout))) {
            throw new IOException("Bootstrap model projection solver failed: "
                    + (solver.timedOut ? "timeout" : firstLine(solver.stdout))
                    + " " + solver.stderr.trim());
        }
        Map<String, String> values = parseValues(solver.stdout, queried);
        for (String term : queried) {
            if (!values.containsKey(term)) {
                throw new IOException("Z3 omitted projected term " + term);
            }
        }
        validateRootModel(assignmentByPort, values);

        Map<String, JsonObject> selectedCases = selectedCases(cases, values);
        Map<String, JsonObject> summaries = uniqueIndex(
                readJsonl(arguments.summaries), "summaryId");
        Map<String, JsonObject> activations = uniqueIndex(
                readJsonl(arguments.activations), "activationId");
        JsonObject fatal = selectFatal(readJsonl(arguments.fatalQueries));
        JsonObject targetSource = selectTarget(
                readJsonl(arguments.targetActivations), fatal);
        validateFatalBinding(composition, fatal, targetSource, arguments,
                smt);

        List<JsonObject> producerRows = new ArrayList<>();
        JsonArray caseManifest = new JsonArray();
        JsonArray existentialScalarManifest = new JsonArray();
        Set<String> usedActivationIds = new LinkedHashSet<>();
        Map<String, List<Map.Entry<String, JsonObject>>> rootsByRegion =
                new LinkedHashMap<>();
        for (Map.Entry<String, JsonObject> entry
                : assignmentByPort.entrySet()) {
            String region = string(entry.getValue(), "regionId");
            List<Map.Entry<String, JsonObject>> regionRoots =
                    rootsByRegion.get(region);
            if (regionRoots == null) {
                regionRoots = new ArrayList<>();
                rootsByRegion.put(region, regionRoots);
            }
            regionRoots.add(entry);
        }
        for (String region : scalarRoots.regionIds()) {
            if (!rootsByRegion.containsKey(region)) {
                rootsByRegion.put(region,
                        new ArrayList<Map.Entry<String, JsonObject>>());
            }
        }
        int projectedPrimitiveInputCount = 0;
        int existentialNonBooleanRootAssignmentCount = 0;
        int nullableStringAssignmentCount = 0;
        int nullStringAssignmentCount = 0;
        for (Map.Entry<String, List<Map.Entry<String, JsonObject>>>
                regionEntry : rootsByRegion.entrySet()) {
            String region = regionEntry.getKey();
            List<Map.Entry<String, JsonObject>> regionRoots =
                    regionEntry.getValue();
            JsonObject selectedCase = selectedCases.get(region);
            if (selectedCase == null) {
                throw gap("ROOT_REGION_HAS_NO_SELECTED_CASE:" + region);
            }
            String summaryId = string(selectedCase, "sourceSummaryId");
            String activationId = string(selectedCase,
                    "sourceActivationId");
            validateCompositionSummaryMembership(composition,
                    selectedCase);
            JsonObject summary = summaries.get(summaryId);
            JsonObject source = activations.get(activationId);
            validateSource(region, summaryId, activationId, summary, source);
            JsonArray replayAssignments = new JsonArray();
            Set<String> rootPorts = new LinkedHashSet<>();
            JsonObject selected = new JsonObject();
            selected.addProperty("regionId", region);
            selected.addProperty("caseId", string(selectedCase, "caseId"));
            selected.addProperty("sourceSummaryId", summaryId);
            selected.addProperty("sourceActivationId", activationId);
            selected.addProperty("selectorSolverSymbol", string(selectedCase,
                    "selectorSolverSymbol"));
            JsonArray rootProjectionRows = new JsonArray();
            for (Map.Entry<String, JsonObject> rootEntry : regionRoots) {
                String port = rootEntry.getKey();
                JsonObject rootAssignment = rootEntry.getValue();
                rootPorts.add(port);
                JsonObject mapping = exactPortMapping(selectedCase, port, smt);
                JsonObject dynamicBinding = exactDynamicLeafBinding(
                        selectedCase, summary, mapping, port);
                JsonObject action = exactAction(summary, source, port,
                        dynamicBinding);
                String actionIdentity = actionIdentitySha256(action);
                JsonObject modelAssignment = modelAssignment(mapping,
                        rootAssignment, action, actionIdentity);
                if (dynamicBinding != null) {
                    retainDynamicLeafSelector(modelAssignment,
                            dynamicBinding);
                }
                replayAssignments.add(modelAssignment);
                projectedPrimitiveInputCount++;

                JsonObject projection = projectedInputManifest(region, port,
                        selectedCase, mapping, string(rootAssignment,
                                "solverTerm"), string(rootAssignment,
                                "value"), action, actionIdentity);
                projection.addProperty("projectionRole", "ROOT_BOOLEAN");
                rootProjectionRows.add(projection);
            }
            List<JsonObject> scalarMappings = catalogScalarMappings(
                    selectedCase, scalarRoots.rootsForRegion(region),
                    rootPorts, smt);
            for (JsonObject mapping : scalarMappings) {
                String port = string(mapping, "canonicalPort");
                String solverTerm = canonicalProjectionTerm(mapping);
                String modelValue = values.get(solverTerm);
                if (modelValue == null) {
                    throw gap("Z3_SUPPLEMENTAL_VALUE_MISSING:" + port);
                }
                JsonObject dynamicBinding = exactDynamicLeafBinding(
                        selectedCase, summary, mapping, port);
                JsonObject action = exactAction(summary, source, port,
                        dynamicBinding);
                JsonObject scalarRoot = scalarRoots.rootForPort(port);
                String valueType = scalarPrimitiveValueType(action, mapping,
                        port, string(scalarRoot, "javaType"),
                        string(scalarRoot, "javaTypeDescriptor"));
                String nullnessSolverTerm = canonicalNullnessProjectionTerm(
                        mapping);
                String nullnessModelValue = "";
                if ("STRING".equals(valueType)) {
                    nullnessModelValue = values.get(nullnessSolverTerm);
                    if (!("true".equals(nullnessModelValue)
                            || "false".equals(nullnessModelValue))) {
                        throw gap("Z3_STRING_NULLNESS_VALUE_INVALID:"
                                + port + ":" + nullnessModelValue);
                    }
                    if ("true".equals(nullnessModelValue)) {
                        valueType = "NULL";
                    }
                }
                String floatingDescriptor = scalarFloatingDescriptor(action,
                        mapping, string(scalarRoot, "javaType"),
                        string(scalarRoot, "javaTypeDescriptor"));
                String normalizedValue = "NULL".equals(valueType) ? "null"
                        : normalizePrimitiveModelValue(valueType, modelValue,
                        port, floatingDescriptor);
                String actionIdentity = actionIdentitySha256(action);
                JsonObject modelAssignment = primitiveModelAssignment(mapping,
                        port, valueType, normalizedValue, action,
                        actionIdentity);
                if (!nullnessSolverTerm.isEmpty()) {
                    addNullableStringModelProvenance(modelAssignment,
                            nullnessSolverTerm, nullnessModelValue,
                            solverTerm, modelValue);
                    nullableStringAssignmentCount++;
                    if ("true".equals(nullnessModelValue)) {
                        nullStringAssignmentCount++;
                    }
                }
                if (!floatingDescriptor.isEmpty()) {
                    modelAssignment.addProperty("floatingPointFormat",
                            floatingDescriptor);
                    modelAssignment.addProperty("modelFloatingPointTerm",
                            modelValue);
                }
                if (dynamicBinding != null) {
                    retainDynamicLeafSelector(modelAssignment,
                            dynamicBinding);
                }
                replayAssignments.add(modelAssignment);
                projectedPrimitiveInputCount++;

                JsonObject projection = projectedInputManifest(region, port,
                        selectedCase, mapping, solverTerm, normalizedValue,
                        action, actionIdentity);
                if (!nullnessSolverTerm.isEmpty()) {
                    addNullableStringModelProvenance(projection,
                            nullnessSolverTerm, nullnessModelValue,
                            solverTerm, modelValue);
                }
                projection.addProperty("projectionRole",
                        "EXISTENTIAL_NON_BOOLEAN_ROOT");
                rootProjectionRows.add(projection.deepCopy());
                existentialScalarManifest.add(projection.deepCopy());
                existentialNonBooleanRootAssignmentCount++;
            }

            if (rootProjectionRows.size() == 0) {
                throw gap("SELECTED_PRODUCER_CASE_HAS_NO_ROOT_INPUT:"
                        + region);
            }
            JsonObject firstRoot = rootProjectionRows.get(0)
                    .getAsJsonObject();
            selected.addProperty("rootInputPort", string(firstRoot,
                    "inputPort"));
            selected.addProperty("rawEngineSymbol", string(firstRoot,
                    "rawEngineSymbol"));
            selected.addProperty("canonicalSolverTerm", string(firstRoot,
                    "canonicalSolverTerm"));
            selected.addProperty("modelValue", string(firstRoot,
                    "modelValue"));
            selected.addProperty("materializationActionIdentitySha256",
                    string(firstRoot,
                            "materializationActionIdentitySha256"));
            selected.add("materializationActionIdentity", object(firstRoot,
                    "materializationActionIdentity").deepCopy());
            selected.add("rootInputProjections", rootProjectionRows);

            JsonObject replay = producerReplay(source, replayAssignments);
            if (!usedActivationIds.add(activationId)) {
                throw gap("ONE_PRODUCER_ACTIVATION_CONTROLS_MULTIPLE_ROOTS:"
                        + activationId);
            }
            producerRows.add(replay);
            caseManifest.add(selected);
        }
        if (existentialNonBooleanRootAssignmentCount
                != scalarRoots.size()) {
            throw gap("EXISTENTIAL_NON_BOOLEAN_ROOT_CARDINALITY_MISMATCH");
        }
        Collections.sort(producerRows, Comparator.comparing(
                row -> string(row, "regionId")));

        JsonObject target = targetReplay(targetSource, fatal);
        if (!usedActivationIds.add(string(target, "activationId"))) {
            throw gap("TARGET_ACTIVATION_COLLIDES_WITH_PRODUCER");
        }
        String stable = sha256(solverInput + GSON.toJson(caseManifest))
                .substring(0, 16);
        String schedule = "SCHEDULE.BOOTSTRAP." + stable;
        int bundleSize = producerRows.size() + 1;
        List<JsonObject> output = new ArrayList<>();
        JsonArray supportIds = new JsonArray();
        for (int index = 0; index < producerRows.size(); index++) {
            JsonObject producer = producerRows.get(index);
            bundle(producer, schedule, string(target, "activationId"), index,
                    bundleSize, "REACHABILITY_SUPPORT");
            producer.addProperty("reachabilitySupportForActivationId",
                    string(target, "activationId"));
            supportIds.add(string(producer, "activationId"));
            output.add(producer);
        }
        bundle(target, schedule, string(target, "activationId"),
                producerRows.size(), bundleSize, "PRIMARY");
        target.add("reachabilitySupportActivationIds", supportIds.deepCopy());
        output.add(target);

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("kind",
                "CONCOLIC_PRIMITIVE_BOOTSTRAP_MODEL_PROJECTION");
        manifest.addProperty("compositionStage", "BOOTSTRAP");
        manifest.addProperty("status", "SAT_UPSTREAM_BOOLEAN_MODEL_READY");
        manifest.addProperty("complete", true);
        manifest.addProperty("projectionComplete", true);
        manifest.addProperty("reportableFinalReachCondition", false);
        manifest.addProperty("callerProvidedFormulaUsed", false);
        manifest.addProperty("callerProvidedValuationUsed", false);
        manifest.addProperty("solver", solver.identity.resolvedPath);
        manifest.add("solverIdentity", solver.identity.toJson());
        manifest.addProperty("solverStatus", "sat");
        manifest.addProperty("solverInputSha256", sha256(solverInput));
        manifest.addProperty("selectedValuationOrdinal", integer(valuation,
                "ordinal", -1));
        manifest.addProperty("selectedValuationKey", string(valuation,
                "valuationKey"));
        manifest.addProperty("rootBooleanInputCount", assignmentByPort.size());
        manifest.addProperty("existentialNonBooleanRootInputCount",
                scalarRoots.size());
        manifest.addProperty("existentialNonBooleanRootAssignmentCount",
                existentialNonBooleanRootAssignmentCount);
        manifest.add("existentialNonBooleanRootAssignments",
                existentialScalarManifest);
        manifest.addProperty("totalProjectedPrimitiveInputCount",
                projectedPrimitiveInputCount);
        manifest.addProperty("nullableJavaStringModeled",
                nullableStringAssignmentCount > 0);
        manifest.addProperty("nullableStringAssignmentCount",
                nullableStringAssignmentCount);
        manifest.addProperty("nullStringAssignmentCount",
                nullStringAssignmentCount);
        if (nullableStringAssignmentCount > 0) {
            manifest.addProperty("nullableStringEncodingAuthority",
                    NULLABLE_STRING_ENCODING_AUTHORITY);
        }
        manifest.addProperty("selectedProducerCaseCount", caseManifest.size());
        manifest.add("selectedProducerCases", caseManifest);
        manifest.addProperty("producerReplayActivationCount",
                producerRows.size());
        manifest.add("producerReplayActivationIds", supportIds);
        manifest.addProperty("targetReplayActivationId",
                string(target, "activationId"));
        manifest.addProperty("activationSelection", "ALL");
        manifest.addProperty("activationBundleScheduleId", schedule);
        manifest.addProperty("activationBundleSize", bundleSize);
        manifest.addProperty("upstreamModelAssignmentCount",
                projectedPrimitiveInputCount);
        manifest.addProperty("downstreamModelAssignmentCount", 0);
        manifest.addProperty("downstreamReplayMaterializationCount", 0);
        manifest.addProperty("downstreamBranchOverrideCount", 0);
        manifest.addProperty("downstreamInjectionForbidden", true);
        manifest.addProperty("targetUnforcedReplayRequired", true);
        manifest.addProperty("projectionAuthority",
                "BOOTSTRAP_SMT_Z3_MODEL_PLUS_EXACT_CASE_SELECTOR_AND_REAL_"
                        + "ACTIVATION_DEFINITION_BINDING_V2");
        manifest.addProperty("inputArtifactBindingAuthority",
                "PROJECTOR_EXACT_CLI_INPUT_SHA256_AND_SELECTED_IDENTITY_V1");
        manifest.add("bootstrapSmtArtifact", artifact(arguments.smt));
        manifest.add("compositionManifestArtifact",
                artifact(arguments.compositionManifest));
        manifest.add("bootstrapReachReportArtifact",
                artifact(arguments.reachReport));
        manifest.add("summaryLedgerArtifact", artifact(arguments.summaries));
        manifest.add("producerActivationLedgerArtifact",
                artifact(arguments.activations));
        manifest.add("targetActivationPlanArtifact",
                artifact(arguments.targetActivations));
        manifest.add("fatalQueryArtifact", artifact(arguments.fatalQueries));
        return new Result(output, manifest);
    }

    private static void validateBootstrapInputs(JsonObject composition,
                                                JsonObject reach, String smt,
                                                Arguments arguments)
            throws IOException {
        if (!"CONCOLIC_COMPOSED_SMT".equals(string(composition, "kind"))
                || !"BOOTSTRAP".equals(string(composition,
                "compositionStage"))
                || !bool(composition, "structurallyComplete", false)
                || !bool(composition, "eligibleForBootstrapModel", false)
                || bool(composition, "fatalReplayValidated", true)
                || bool(composition, "complete", true)
                || bool(composition,
                "eligibleToReportAutomaticRelationship", true)
                || !bool(composition, "caseProjectionCatalogComplete",
                false)
                || integer(composition, "caseProjectionCatalogCount", -1)
                != array(composition, "caseProjectionCatalog").size()) {
            throw gap("COMPOSITION_IS_NOT_A_MODEL_ELIGIBLE_BOOTSTRAP");
        }
        if (!"BOOLEAN_REACH_CONDITION_REPORT".equals(string(reach, "kind"))
                || !"BOOTSTRAP_REPLAY_MODEL".equals(string(reach,
                "extractionMode"))
                || !bool(reach, "replayBootstrapOnly", false)
                || bool(reach, "reportableFinalReachCondition", true)
                || !bool(reach, "complete", false)
                || !"COMPLETE_BOOTSTRAP_BOOLEAN_REPLAY_MODEL".equals(
                string(reach, "status"))
                || !sha256(smt).equals(string(reach,
                "composedSmtSha256"))) {
            throw gap("BOOLEAN_REPORT_IS_NOT_AN_EXACT_BOOTSTRAP_MODEL");
        }
        JsonObject reportSmt = object(reach, "composedSmtArtifact");
        JsonObject reportManifest = object(reach,
                "compositionManifestArtifact");
        if (!sha256(arguments.smt).equals(string(reportSmt, "sha256"))
                || !sha256(arguments.compositionManifest).equals(string(
                reportManifest, "sha256"))) {
            throw gap("BOOTSTRAP_REPORT_ARTIFACT_HASH_MISMATCH");
        }
    }

    private static void validateFatalBinding(JsonObject composition,
                                             JsonObject fatal,
                                             JsonObject target,
                                             Arguments arguments,
                                             String smt)
            throws IOException {
        String activationId = string(fatal, "activationId");
        String regionId = string(fatal, "regionId");
        String instanceId = firstNonBlank(string(fatal,
                "regionInstanceId"), string(object(fatal,
                "symbolicContext"), "regionInstanceId"));
        BranchReplayContract contract = replayContract(fatal);
        SolverPathContext solverPathContext = solverPathContext(fatal);
        String siteId = contract.source().siteId();
        int occurrence = contract.source().occurrence();
        boolean desiredOutcome = contract.requiredTakenOutcome();
        if (activationId.isEmpty() || regionId.isEmpty()
                || instanceId.isEmpty() || siteId.isEmpty()
                || occurrence < 1
                || !activationId.equals(string(composition,
                "fatalActivation"))
                || !regionId.equals(string(composition, "fatalRegion"))
                || !instanceId.equals(string(composition,
                "fatalRegionInstanceId"))
                || !siteId.equals(string(composition, "fatalSite"))
                || occurrence != integer(composition, "fatalOccurrence", -1)
                || desiredOutcome != bool(composition,
                "fatalDesiredOutcome", !desiredOutcome)
                || integer(composition, "fatalConditionCount", -1)
                != contract.requiredPathPredicates().size()
                + solverPathContext.size()
                || !contract.contractId().equals(string(composition,
                "fatalReplayContractId"))
                || bool(composition, "fatalReplayValidated", true)
                || !string(composition, "validatedSummaryId").isEmpty()
                || !string(composition,
                "validatedFatalReplaySummary").isEmpty()) {
            throw gap("COMPOSITION_FATAL_QUERY_IDENTITY_MISMATCH");
        }
        if (!artifactMatches(object(composition, "composedSmtArtifact"),
                arguments.smt, sha256(smt))
                || !artifactMatches(object(composition,
                "fatalQueriesArtifact"), arguments.fatalQueries,
                sha256(arguments.fatalQueries))) {
            throw gap("COMPOSITION_FATAL_OR_SMT_ARTIFACT_MISMATCH");
        }
        requireMaterializations(target, "TARGET_ACTIVATION");
        BranchCaptureSelector branch;
        try {
            branch = BranchCaptureSelector.fromJson(object(target,
                    "branchCaptureSelector"));
        } catch (IllegalArgumentException malformed) {
            throw gap("TARGET_CAPTURE_SELECTOR_INVALID:"
                    + malformed.getMessage());
        }
        JsonObject goal = object(target, "captureGoal");
        if (!activationId.equals(string(target, "activationId"))
                || !regionId.equals(string(target, "regionId"))
                || !instanceId.equals(string(target, "regionInstanceId"))
                || !"TARGET_BRANCH".equals(string(goal, "kind"))
                || !siteId.equals(branch.siteId())
                || occurrence != branch.occurrence()
                || desiredOutcome != branch.desiredOutcome()
                || !bool(target, "replayable", false)
                || !bool(target, "symbolicReady", false)
                || !bool(target, "schedulerReady", false)
                || !bool(target, "branchOverrideProhibited", false)) {
            throw gap("TARGET_ACTIVATION_EXACT_BINDING_MISMATCH");
        }
    }

    private static boolean artifactMatches(JsonObject artifact, Path path,
                                           String expectedSha)
            throws IOException {
        return path.toAbsolutePath().normalize().toString().equals(
                string(artifact, "path"))
                && expectedSha.equals(string(artifact, "sha256"))
                && Files.size(path) == longInteger(artifact, "sizeBytes", -1L);
    }

    private static void validateCompositionSummaryMembership(
            JsonObject composition, JsonObject selectedCase)
            throws IOException {
        String summaryId = string(selectedCase, "sourceSummaryId");
        String activationId = string(selectedCase, "sourceActivationId");
        String regionId = string(selectedCase, "regionId");
        String caseId = string(selectedCase, "caseId");
        String pathKey = string(selectedCase, "pathKey");
        String parent = string(selectedCase,
                "compositionInputSummaryId");
        JsonArray included = array(composition, "includedSummaries");
        int catalogMatches = 0;
        for (JsonElement element : array(composition,
                "caseProjectionCatalog")) {
            if (!element.isJsonObject()) continue;
            JsonObject candidate = element.getAsJsonObject();
            if (parent.equals(string(candidate,
                    "compositionInputSummaryId"))
                    && regionId.equals(string(candidate, "regionId"))
                    && caseId.equals(string(candidate, "caseId"))
                    && pathKey.equals(string(candidate, "pathKey"))
                    && summaryId.equals(string(candidate,
                    "sourceSummaryId"))
                    && activationId.equals(string(candidate,
                    "sourceActivationId"))) {
                catalogMatches++;
            }
        }
        if (summaryId.isEmpty() || activationId.isEmpty()
                || regionId.isEmpty() || caseId.isEmpty()
                || pathKey.isEmpty() || parent.isEmpty()
                || countString(included, parent) != 1
                || catalogMatches != 1) {
            throw gap("SELECTED_SOURCE_SUMMARY_NOT_IN_COMPOSITION_INPUT:"
                    + summaryId);
        }
    }

    private static JsonObject selectedValuation(JsonObject reach)
            throws IOException {
        JsonObject selected = null;
        for (JsonElement element : array(reach, "truthTable")) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if (!bool(row, "reachesBug", false)
                    || !"sat".equals(string(row, "solverStatus"))) continue;
            if (selected == null || integer(row, "ordinal", Integer.MAX_VALUE)
                    < integer(selected, "ordinal", Integer.MAX_VALUE)) {
                selected = row;
            }
        }
        if (selected == null) throw gap("BOOTSTRAP_FORMULA_HAS_NO_SAT_WITNESS");
        return selected.deepCopy();
    }

    private static Map<String, JsonObject> valuationAssignments(
            JsonObject valuation, JsonArray roots) throws IOException {
        Map<String, JsonObject> rootByPort = new LinkedHashMap<>();
        for (JsonElement element : roots) {
            if (!element.isJsonObject()) continue;
            JsonObject root = element.getAsJsonObject();
            String port = string(root, "portId");
            String solverTerm = string(root, "solverTerm");
            if (port.isEmpty() || rootByPort.put(port, root) != null
                    || !bool(root, "root", false)
                    || bool(root, "upstreamSupplied", true)
                    || !safeSmtAtom(solverTerm)
                    || !("Z".equals(string(root, "javaTypeDescriptor"))
                    || "Ljava/lang/Boolean;".equals(string(root,
                    "javaTypeDescriptor")))) {
                throw gap("INVALID_OR_DUPLICATE_BOOLEAN_ROOT:" + port);
            }
        }
        Map<String, JsonObject> result = new LinkedHashMap<>();
        for (JsonElement element : array(valuation, "assignments")) {
            if (!element.isJsonObject()) continue;
            JsonObject assignment = element.getAsJsonObject();
            String port = string(assignment, "portId");
            JsonObject root = rootByPort.get(port);
            String solverTerm = string(assignment, "solverTerm");
            boolean value = bool(assignment, "value", false);
            String canonicalLiteral = "(= " + solverTerm + " "
                    + (value ? "1" : "0") + ")";
            if (root == null || result.put(port, assignment.deepCopy()) != null
                    || !string(root, "solverTerm").equals(solverTerm)
                    || !safeSmtAtom(solverTerm)
                    || !assignment.has("value")
                    || !assignment.get("value").isJsonPrimitive()
                    || !assignment.get("value").getAsJsonPrimitive()
                    .isBoolean()
                    || !canonicalLiteral.equals(string(assignment,
                    "solverLiteral"))) {
                throw gap("INVALID_BOOTSTRAP_VALUATION_ASSIGNMENT:" + port);
            }
            JsonObject enriched = result.get(port);
            enriched.addProperty("regionId", string(root, "regionId"));
        }
        if (result.size() != rootByPort.size()) {
            throw gap("BOOTSTRAP_VALUATION_ROOT_CARDINALITY_MISMATCH");
        }
        return result;
    }

    /** Reads the extractor-owned allow-list of non-Boolean root inputs. */
    private static ScalarRootCatalog scalarRootCatalog(
            JsonObject reach, Set<String> booleanRootPorts)
            throws IOException {
        if (!reach.has("existentialNonBooleanRootInputs")
                || !reach.has("existentialNonBooleanRootInputCount")
                || !isArray(reach, "existentialNonBooleanRootInputs")) {
            throw gap("EXISTENTIAL_NON_BOOLEAN_ROOT_CATALOG_MALFORMED");
        }
        JsonArray inputs = array(reach,
                "existentialNonBooleanRootInputs");
        if (integer(reach, "existentialNonBooleanRootInputCount", -1)
                != inputs.size()
                || !"STATIC_JAVA_SCALAR_PORT_TYPE_PLUS_COMPOSER_"
                .concat("CANONICAL_TERM_AND_RUNTIME_RELATIONSHIP_"
                        + "DIRECTION_V1").equals(string(reach,
                        "existentialNonBooleanRootInputDiscoveryAuthority"))) {
            throw gap("EXISTENTIAL_NON_BOOLEAN_ROOT_CATALOG_MALFORMED");
        }
        Map<String, JsonObject> byPort = new LinkedHashMap<>();
        Map<String, List<JsonObject>> byRegion = new LinkedHashMap<>();
        Set<String> solverTerms = new LinkedHashSet<>();
        int ordinal = 0;
        for (JsonElement element : inputs) {
            if (!element.isJsonObject()) {
                throw gap("INVALID_EXISTENTIAL_NON_BOOLEAN_ROOT:");
            }
            JsonObject root = element.getAsJsonObject();
            String port = string(root, "portId");
            String region = string(root, "regionId");
            String descriptor = string(root, "javaTypeDescriptor");
            String solverTerm = string(root, "solverTerm");
            String solverSort = string(root, "solverSort");
            String nullnessSolverTerm = string(root,
                    "nullnessSolverTerm");
            boolean stringRoot = "String".equals(solverSort)
                    && "Ljava/lang/String;".equals(descriptor);
            if (port.isEmpty() || region.isEmpty()
                    || !port.startsWith(region + ".in.")
                    || booleanRootPorts.contains(port)
                    || byPort.put(port, root.deepCopy()) != null
                    || !bool(root, "root", false)
                    || bool(root, "upstreamSupplied", true)
                    || !safeSmtAtom(solverTerm)
                    || !solverTerms.add(solverTerm)
                    || stringRoot && (!safeSmtAtom(nullnessSolverTerm)
                    || !solverTerms.add(nullnessSolverTerm)
                    || !"Bool".equals(string(root,
                    "nullnessSolverSort"))
                    || !NULLABLE_STRING_ENCODING_AUTHORITY.equals(string(
                    root, "nullableStringEncodingAuthority")))
                    || !scalarDescriptorMatchesSort(descriptor, solverSort)
                    || string(root, "cell").isEmpty()
                    || string(root, "javaType").isEmpty()
                    || integer(root, "ordinal", -1) != ordinal
                    || !"EXISTENTIALLY_QUANTIFIED_IN_BOOLEAN_PROJECTION"
                    .equals(string(root, "projectionRole"))
                    || !"STATIC_JAVA_SCALAR_PORT_PLUS_COMPOSED_SMT_"
                    .concat("CANONICAL_BINDING_AND_RUNTIME_RELATIONSHIP_"
                            + "DIRECTION_V1").equals(string(root,
                            "authority"))
                    || !isArray(root, "caseProjectionEvidence")
                    || array(root, "caseProjectionEvidence").size() == 0) {
                throw gap("INVALID_EXISTENTIAL_NON_BOOLEAN_ROOT:" + port);
            }
            List<JsonObject> regionRoots = byRegion.get(region);
            if (regionRoots == null) {
                regionRoots = new ArrayList<>();
                byRegion.put(region, regionRoots);
            }
            regionRoots.add(root.deepCopy());
            ordinal++;
        }
        return new ScalarRootCatalog(byPort, byRegion);
    }

    private static boolean scalarDescriptorMatchesSort(String descriptor,
                                                       String solverSort) {
        if ("Int".equals(solverSort)) {
            return "B".equals(descriptor) || "C".equals(descriptor)
                    || "S".equals(descriptor) || "I".equals(descriptor)
                    || "J".equals(descriptor)
                    || "Ljava/lang/Byte;".equals(descriptor)
                    || "Ljava/lang/Character;".equals(descriptor)
                    || "Ljava/lang/Short;".equals(descriptor)
                    || "Ljava/lang/Integer;".equals(descriptor)
                    || "Ljava/lang/Long;".equals(descriptor);
        }
        if ("(_ FloatingPoint 8 24)".equals(solverSort)) {
            return "F".equals(descriptor)
                    || "Ljava/lang/Float;".equals(descriptor);
        }
        if ("(_ FloatingPoint 11 53)".equals(solverSort)) {
            return "D".equals(descriptor)
                    || "Ljava/lang/Double;".equals(descriptor);
        }
        return "String".equals(solverSort)
                && "Ljava/lang/String;".equals(descriptor);
    }

    private static List<String> selectors(List<JsonObject> cases)
            throws IOException {
        Set<String> result = new LinkedHashSet<>();
        for (JsonObject pathCase : cases) {
            String selector = string(pathCase, "selectorSolverSymbol");
            if (!safeSmtAtom(selector) || !result.add(selector)
                    || !bool(pathCase, "complete", false)) {
                throw gap("INVALID_OR_DUPLICATE_CASE_SELECTOR:" + selector);
            }
        }
        if (result.isEmpty()) throw gap("BOOTSTRAP_HAS_NO_CASE_SELECTORS");
        return new ArrayList<>(result);
    }

    private static Map<String, JsonObject> selectedCases(
            List<JsonObject> cases, Map<String, String> values)
            throws IOException {
        Map<String, JsonObject> result = new LinkedHashMap<>();
        Set<String> regions = new LinkedHashSet<>();
        for (JsonObject pathCase : cases) {
            String region = string(pathCase, "regionId");
            regions.add(region);
            if (!"true".equals(values.get(string(pathCase,
                    "selectorSolverSymbol")))) continue;
            if (region.isEmpty() || result.put(region, pathCase) != null) {
                throw gap("MULTIPLE_SELECTED_CASES_FOR_REGION:" + region);
            }
        }
        if (result.size() != regions.size()) {
            throw gap("ONE_SELECTED_CASE_REQUIRED_PER_REGION");
        }
        return result;
    }

    private static void validateRootModel(Map<String, JsonObject> assignments,
                                          Map<String, String> values)
            throws IOException {
        for (Map.Entry<String, JsonObject> entry : assignments.entrySet()) {
            JsonObject assignment = entry.getValue();
            boolean expected = bool(assignment, "value", false);
            String actual = values.get(string(assignment, "solverTerm"));
            if (!(expected ? "1" : "0").equals(actual)) {
                throw gap("Z3_ROOT_MODEL_DIFFERS_FROM_TRUTH_TABLE:"
                        + entry.getKey());
            }
        }
    }

    private static void validateSource(String region, String summaryId,
                                       String activationId,
                                       JsonObject summary, JsonObject source)
            throws IOException {
        requireMaterializations(source, "SELECTED_SOURCE_ACTIVATION");
        if (summary == null || source == null
                || !summaryId.equals(string(summary, "summaryId"))
                || !activationId.equals(string(source, "activationId"))
                || !bool(summary, "valid", false)
                || !bool(summary, "relationallyComplete", false)
                || !region.equals(string(summary, "regionId"))
                || !region.equals(string(source, "regionId"))
                || !activationId.equals(string(summary, "activationId"))
                || !string(summary, "regionInstanceId").equals(string(source,
                "regionInstanceId"))) {
            throw gap("SELECTED_CASE_SOURCE_NOT_EXACT:" + summaryId + ":"
                    + activationId);
        }
    }

    private static JsonObject exactPortMapping(JsonObject pathCase,
                                               String port, String smt)
            throws IOException {
        JsonArray catalog = array(pathCase, "rawEngineSymbolMappings");
        if (!"GUARDED_CASE_PROJECTION_CATALOG".equals(string(pathCase,
                "kind"))
                || integer(pathCase, "schemaVersion", -1) != 1
                || !bool(pathCase, "complete", false)
                || !"EMITTER_ACTUAL_TERM_CAPTURE_IN_CASE_SCOPE".equals(
                string(pathCase, "rawEngineSymbolMappingAuthority"))
                || integer(pathCase, "rawEngineSymbolMappingCount", -1)
                != catalog.size()) {
            throw gap("CASE_INPUT_MAPPING_CATALOG_NOT_EXACT:" + port);
        }
        JsonObject selected = null;
        for (JsonElement element : catalog) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            if (!port.equals(string(mapping, "canonicalPort"))) continue;
            if (selected != null) {
                throw gap("AMBIGUOUS_CASE_INPUT_MAPPING:" + port);
            }
            selected = mapping;
        }
        if (selected == null || string(selected, "rawEngineSymbol").isEmpty()
                || string(selected, "solverTerm").isEmpty()
                || !"EMITTER_ACTUAL_TERM".equals(string(selected,
                "authority"))) {
            throw gap("MISSING_CASE_INPUT_MAPPING:" + port);
        }
        String canonical = canonicalProjectionTerm(selected);
        if ("STRING".equals(string(selected, "sort"))
                && (!safeSmtAtom(canonicalNullnessProjectionTerm(selected))
                || !NULLABLE_STRING_ENCODING_AUTHORITY.equals(string(
                selected, "nullableStringEncodingAuthority")))) {
            throw gap("CASE_STRING_NULLNESS_MAPPING_NOT_EXACT:" + port);
        }
        if (!string(selected, "solverTerm").equals(canonical)
                && !exactDynamicCanonicalBridge(pathCase, selected, port,
                canonical, smt)) {
            throw gap("CASE_DYNAMIC_CANONICAL_BRIDGE_NOT_EXACT:" + port);
        }
        return selected.deepCopy();
    }

    private static List<JsonObject> catalogScalarMappings(
            JsonObject selectedCase, List<JsonObject> catalogRoots,
            Set<String> booleanRootPorts, String smt) throws IOException {
        List<JsonObject> result = new ArrayList<>();
        Set<String> selectedPorts = new LinkedHashSet<>();
        for (JsonObject root : catalogRoots) {
            String port = string(root, "portId");
            if (booleanRootPorts.contains(port)
                    || !selectedPorts.add(port)) {
                throw gap("DUPLICATE_SELECTED_SCALAR_ROOT:" + port);
            }
            JsonObject mapping = exactPortMapping(selectedCase, port, smt);
            String solverTerm = canonicalProjectionTerm(mapping);
            String solverSort = string(root, "solverSort");
            String expectedMappingSort = "Int".equals(solverSort)
                    ? "INT" : "(_ FloatingPoint 8 24)".equals(solverSort)
                    ? "FLOAT32" : "(_ FloatingPoint 11 53)".equals(
                    solverSort) ? "FLOAT64" : "String".equals(solverSort)
                    ? "STRING" : "";
            String rootNullness = string(root, "nullnessSolverTerm");
            String mappingNullness = canonicalNullnessProjectionTerm(mapping);
            if (!scalarCanonicalMapping(mapping)
                    || !string(root, "solverTerm").equals(solverTerm)
                    || !solverSort.equals(string(mapping, "solverSort"))
                    || !expectedMappingSort.equals(string(mapping,
                    "sort"))
                    || "STRING".equals(expectedMappingSort)
                    && (!rootNullness.equals(mappingNullness)
                    || !NULLABLE_STRING_ENCODING_AUTHORITY.equals(string(
                    mapping, "nullableStringEncodingAuthority")))) {
                throw gap("EXISTENTIAL_SCALAR_ROOT_MAPPING_MISMATCH:"
                        + port);
            }
            result.add(mapping);
        }
        Collections.sort(result, Comparator.comparing(
                value -> string(value, "canonicalPort")));
        return result;
    }

    private static boolean scalarCanonicalMapping(JsonObject mapping) {
        String port = string(mapping, "canonicalPort");
        String termKind = string(mapping, "termKind");
        String sort = string(mapping, "sort");
        String solverSort = string(mapping, "solverSort");
        boolean scalarSort = "INT".equals(sort) && "Int".equals(solverSort)
                || "FLOAT32".equals(sort)
                && "(_ FloatingPoint 8 24)".equals(solverSort)
                || "FLOAT64".equals(sort)
                && "(_ FloatingPoint 11 53)".equals(solverSort)
                || "STRING".equals(sort) && "String".equals(solverSort);
        return !port.isEmpty()
                && scalarSort
                && ("CANONICAL_PORT_TERM".equals(termKind)
                || "SCOPED_DYNAMIC_FIELD".equals(termKind));
    }

    private static String canonicalProjectionTerm(JsonObject mapping) {
        return firstNonBlank(string(mapping, "canonicalSolverTerm"),
                string(mapping, "solverTerm"));
    }

    private static String canonicalNullnessProjectionTerm(
            JsonObject mapping) {
        if (!"STRING".equals(string(mapping, "sort"))) return "";
        return firstNonBlank(string(mapping,
                "canonicalNullnessSolverTerm"), string(mapping,
                "nullnessSolverTerm"));
    }

    static boolean exactDynamicCanonicalBridge(
            JsonObject pathCase, JsonObject mapping, String port,
            String canonical, String smt) {
        String actual = string(mapping, "solverTerm");
        String sort = string(mapping, "sort");
        String solverSort = string(mapping, "solverSort");
        String suffix = "INT".equals(sort) && "Int".equals(solverSort)
                ? "int" : "FLOAT32".equals(sort)
                && "(_ FloatingPoint 8 24)".equals(solverSort)
                ? "float32" : "FLOAT64".equals(sort)
                && "(_ FloatingPoint 11 53)".equals(solverSort)
                ? "float64" : "STRING".equals(sort)
                && "String".equals(solverSort) ? "string" : "";
        boolean stringTerm = "STRING".equals(sort);
        String actualNullness = string(mapping, "nullnessSolverTerm");
        String canonicalNullness = canonicalNullnessProjectionTerm(mapping);
        String guard = string(mapping, "canonicalBridgeGuard");
        String expression = stringTerm
                ? "(and (= " + actual + " " + canonical + ") (= "
                + actualNullness + " " + canonicalNullness + "))"
                : "(= " + actual + " " + canonical + ")";
        String formula = "(=> " + guard + " " + expression + ")";
        String assertionName = string(mapping,
                "canonicalBridgeAssertionName");
        String assertion = "(assert (! " + formula + " :named "
                + assertionName + "))";
        JsonArray ids = array(mapping, "dynamicBindingIds");
        if (actual.isEmpty() || canonical.isEmpty()
                || actual.equals(canonical)
                || !safeSmtAtom(actual) || !safeSmtAtom(canonical)
                || suffix.isEmpty()
                || !canonical.equals("sym__port__" + smtName(port)
                + "__" + suffix)
                || stringTerm && (!safeSmtAtom(actualNullness)
                || !safeSmtAtom(canonicalNullness)
                || !NULLABLE_STRING_ENCODING_AUTHORITY.equals(string(
                mapping, "nullableStringEncodingAuthority")))
                || !port.equals(string(mapping, "canonicalPort"))
                || !port.startsWith(string(pathCase, "regionId") + ".in.")
                || !guard.equals(string(pathCase,
                "selectorSolverSymbol"))
                || assertionName.isEmpty()
                || !expression.equals(string(mapping,
                "canonicalBridgeExpression"))
                || !formula.equals(string(mapping,
                "canonicalBridgeFormula"))
                || !assertion.equals(string(mapping,
                "canonicalBridgeAssertion"))
                || !sha256(assertion).equals(string(mapping,
                "canonicalBridgeAssertionSha256"))
                || !"CASE_UNIQUE_DYNAMIC_BASE_TO_CANONICAL_PORT_"
                .concat("GUARDED_EQUALITY_V1").equals(string(mapping,
                        "canonicalBridgeAuthority"))
                || !"SCOPED_DYNAMIC_FIELD".equals(string(mapping,
                "termKind"))
                || ids.size() != 1 || !ids.get(0).isJsonPrimitive()
                || !ids.get(0).getAsJsonPrimitive().isString()
                || !exactSmtLine(smt, assertion)) {
            return false;
        }
        String id = ids.get(0).getAsString();
        JsonObject selected = null;
        for (JsonElement element : array(pathCase,
                "dynamicFieldBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!id.equals(string(binding, "dynamicBindingId"))) continue;
            if (selected != null) return false;
            selected = binding;
        }
        return selected != null
                && port.equals(string(selected, "baseInputSymbol"))
                && actual.equals(string(selected, "solverTerm"))
                && (!stringTerm || actualNullness.equals(string(selected,
                "nullnessSolverTerm")))
                && string(mapping, "rawEngineSymbol").equals(string(selected,
                "fieldExpressionRawEngineSymbol"))
                && bool(selected, "complete", false)
                && bool(selected, "observationMatched", false)
                && (!stringTerm
                || NULLABLE_STRING_ENCODING_AUTHORITY.equals(string(
                selected, "nullableStringEncodingAuthority")))
                && "EMITTER_ACTUAL_DYNAMIC_FIELD_TERM".equals(string(
                selected, "termBindingAuthority"));
    }

    private static boolean exactSmtLine(String smt, String expected) {
        if (smt == null || expected == null || expected.isEmpty()) {
            return false;
        }
        int matches = 0;
        for (String line : smt.split("\\R", -1)) {
            if (expected.equals(line)) matches++;
        }
        return matches == 1;
    }

    /**
     * Resolves a dynamic scalar leaf only through the selected case's exact VM
     * term.  The selected-case metadata is joined back to the byte-for-byte
     * runtime binding retained by its source summary; neither a base-field
     * prefix nor an unselected occurrence may authorize replay.
     */
    private static JsonObject exactDynamicLeafBinding(
            JsonObject selectedCase, JsonObject summary, JsonObject mapping,
            String port) throws IOException {
        String raw = string(mapping, "rawEngineSymbol");
        JsonArray selectedBindings = array(selectedCase,
                "dynamicFieldBindings");
        JsonArray mappingBindingIds = array(mapping,
                "dynamicBindingIds");
        if (selectedCase.has("dynamicFieldBindingCount")
                && integer(selectedCase, "dynamicFieldBindingCount", -1)
                != selectedBindings.size()) {
            throw gap("SELECTED_CASE_DYNAMIC_BINDING_COUNT_MISMATCH:" + port);
        }

        JsonObject selected = null;
        for (JsonElement element : selectedBindings) {
            if (!element.isJsonObject()) continue;
            JsonObject candidate = element.getAsJsonObject();
            if (!raw.equals(string(candidate,
                    "fieldExpressionRawEngineSymbol"))) {
                continue;
            }
            if (selected != null) {
                throw gap("AMBIGUOUS_SELECTED_CASE_DYNAMIC_BINDING:" + raw);
            }
            selected = candidate;
        }
        boolean mappingClaimsDynamic = "SCOPED_DYNAMIC_FIELD".equals(
                string(mapping, "termKind"))
                || mappingBindingIds.size() > 0;
        if (mappingClaimsDynamic) {
            int baseMatches = 0;
            for (JsonElement element : selectedBindings) {
                if (!element.isJsonObject()) continue;
                JsonObject candidate = element.getAsJsonObject();
                String kind = string(candidate, "kind");
                if (port.equals(string(candidate, "baseInputSymbol"))
                        && (DYNAMIC_CONTAINER_FIELD_KIND.equals(kind)
                        || DYNAMIC_MAP_ENTRY_FIELD_KIND.equals(kind))) {
                    baseMatches++;
                }
            }
            if (baseMatches != 1) {
                throw gap("SELECTED_CASE_DYNAMIC_BASE_NOT_UNIQUE:" + port
                        + ":" + baseMatches);
            }
        }
        if (selected == null) {
            if (mappingClaimsDynamic) {
                throw gap("SELECTED_CASE_DYNAMIC_MAPPING_WITHOUT_BINDING:"
                        + raw);
            }
            return null;
        }

        JsonObject runtime = object(selected, "runtimeBinding");
        String kind = string(runtime, "kind");
        if (runtime.size() == 0
                || !(DYNAMIC_CONTAINER_FIELD_KIND.equals(kind)
                || DYNAMIC_MAP_ENTRY_FIELD_KIND.equals(kind))
                || !kind.equals(string(selected, "kind"))
                || !bool(selected, "complete", false)
                || !bool(selected, "observationMatched", false)
                || !bool(runtime, "complete", false)) {
            throw gap("SELECTED_CASE_DYNAMIC_BINDING_INCOMPLETE:" + raw);
        }
        if (!raw.equals(string(selected,
                "fieldExpressionRawEngineSymbol"))
                || !string(mapping, "solverTerm").equals(string(selected,
                "solverTerm"))
                || !"EMITTER_ACTUAL_DYNAMIC_FIELD_TERM".equals(
                string(selected, "termBindingAuthority"))) {
            throw gap("SELECTED_CASE_DYNAMIC_TERM_MISMATCH:" + raw);
        }

        String base = string(runtime, "baseInputSymbol");
        String dynamic = string(runtime, "dynamicFieldSymbol");
        String id = string(runtime, "dynamicBindingId");
        String site = string(runtime, "materializationSiteId");
        int occurrence = integer(runtime, "materializationOccurrence", -1);
        String expectedDynamic = base + ".field."
                + sha256(site).substring(0, 12) + ".occ." + occurrence;
        if (mappingBindingIds.size() != 1
                || !mappingBindingIds.get(0).isJsonPrimitive()
                || !mappingBindingIds.get(0).getAsJsonPrimitive().isString()
                || !id.equals(mappingBindingIds.get(0).getAsString())
                || !port.equals(base) || dynamic.isEmpty()
                || !id.equals("DYNAMIC_FIELD:" + dynamic)
                || site.isEmpty() || occurrence < 1
                || !expectedDynamic.equals(dynamic)
                || !exactEngineSymbol(raw, dynamic)
                || string(runtime, "fieldSignature").isEmpty()
                || array(runtime, "fieldPath").size() == 0) {
            throw gap("SELECTED_CASE_DYNAMIC_BINDING_IDENTITY_MISMATCH:" + raw);
        }

        if (DYNAMIC_CONTAINER_FIELD_KIND.equals(kind)) {
            validateContainerDynamicBinding(runtime, raw);
        } else {
            validateMapEntryDynamicBinding(runtime, raw);
        }

        JsonObject sourceBinding = null;
        for (JsonElement element : array(summary, "dynamicFieldBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject candidate = element.getAsJsonObject();
            if (!id.equals(string(candidate, "dynamicBindingId"))) continue;
            if (sourceBinding != null) {
                throw gap("AMBIGUOUS_SOURCE_SUMMARY_DYNAMIC_BINDING:" + id);
            }
            sourceBinding = candidate;
        }
        if (sourceBinding == null || !runtime.equals(sourceBinding)) {
            throw gap("SELECTED_CASE_SOURCE_DYNAMIC_BINDING_MISMATCH:" + id);
        }
        return runtime.deepCopy();
    }

    private static void validateContainerDynamicBinding(JsonObject binding,
                                                        String raw)
            throws IOException {
        JsonObject selector = object(binding, "containerSelector");
        int occurrence = integer(binding, "materializationOccurrence", -1);
        if (integer(binding, "schemaVersion", -1) != 2
                || !DYNAMIC_CONTAINER_FIELD_AUTHORITY.equals(string(binding,
                "authority"))
                || !"ARRAY_INDEX".equals(string(selector, "kind"))
                || !bool(selector, "complete", false)
                || string(selector, "bindingId").isEmpty()
                || string(selector, "containerInputPort").isEmpty()
                || string(selector, "containerInputCell").isEmpty()
                || !"EXACT_ARRAY_INDEX".equals(string(selector,
                "selectorAuthority"))
                || integer(selector, "elementIndex", -1) < 0
                || integer(selector, "elementOccurrence", -1) != occurrence
                || string(selector, "declaredFieldOwnerClass").isEmpty()
                || string(selector, "declaredFieldType").isEmpty()
                || longInteger(selector, "containerObjectToken", 0L) <= 0L
                || longInteger(selector, "elementObjectToken", 0L) <= 0L
                || !"ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(selector, "objectTokenAuthority"))
                || string(selector, "objectTokenScope").isEmpty()
                || !("EXACT_ARRAY_INDEX".equals(string(selector,
                "resolvedFromSelectorAuthority"))
                || "DISCOVER_UNIQUE_IDENTITY_INDEX".equals(string(selector,
                "resolvedFromSelectorAuthority")))
                || !"EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                .concat("ACTIVATION_LOCAL_ELEMENT_IDENTITY").equals(
                        string(selector, "authority"))) {
            throw gap("SELECTED_CASE_CONTAINER_SELECTOR_INCOMPLETE:" + raw);
        }
    }

    private static void validateMapEntryDynamicBinding(JsonObject binding,
                                                       String raw)
            throws IOException {
        if (integer(binding, "schemaVersion", -1) != 1
                || !DYNAMIC_MAP_ENTRY_FIELD_AUTHORITY.equals(string(binding,
                "authority"))
                || string(binding, "entryReadObservationId").isEmpty()
                || binding.get("keyExpression") == null
                || !binding.get("keyExpression").isJsonObject()
                || string(binding, "keyExpressionAuthority").isEmpty()) {
            throw gap("SELECTED_CASE_MAP_ENTRY_BINDING_INCOMPLETE:" + raw);
        }
    }

    private static JsonObject exactAction(JsonObject summary,
                                          JsonObject activation, String port,
                                          JsonObject dynamicBinding)
            throws IOException {
        validateInputAdmission(summary, port, dynamicBinding);
        JsonArray source = dynamicBinding != null
                && DYNAMIC_CONTAINER_FIELD_KIND.equals(string(
                dynamicBinding, "kind"))
                ? array(activation, "symbolize")
                : array(activation, "materializations");
        JsonObject selected = null;
        for (JsonElement element : source) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            if (!port.equals(string(action, "symbol"))) continue;
            if (selected != null) throw gap("AMBIGUOUS_INPUT_ACTION:" + port);
            selected = action;
        }
        if (selected == null || bool(selected, "deferred", false)
                || bool(selected, "deferredResolution", false)) {
            throw gap("ROOT_INPUT_HAS_NO_REAL_MATERIALIZATION:" + port);
        }
        String bindingMode = string(selected, "bindingMode");
        String location = string(selected, "location");
        String cell = string(selected, "cell");
        if (bindingMode.isEmpty() || location.isEmpty() || cell.isEmpty()) {
            throw gap("ROOT_INPUT_ACTION_IDENTITY_INCOMPLETE:" + port);
        }
        if (dynamicBinding != null) {
            if (!"FIELD_ACCESS".equals(bindingMode)) {
                throw gap("DYNAMIC_ROOT_INPUT_IS_NOT_FIELD_ACCESS:" + port);
            }
            validateDynamicFieldAction(selected, dynamicBinding, port);
            if (DYNAMIC_CONTAINER_FIELD_KIND.equals(string(dynamicBinding,
                    "kind"))) {
                JsonObject selector = object(dynamicBinding,
                        "containerSelector");
                requireContainerAction(activation, selector);
            }
        } else if ("LOCAL_DEFINITION".equals(bindingMode)) {
            validateLocalDefinitionIdentity(selected, port);
        } else if ("ROOT_ENTRY".equals(bindingMode)) {
            validateRootEntryIdentity(selected, port);
        } else if ("FIELD_ACCESS".equals(bindingMode)) {
            validateScalarFieldAction(selected, port);
        } else {
            throw gap("ROOT_INPUT_ACTION_BINDING_NOT_MODEL_CONTROLLABLE:"
                    + port + ":" + bindingMode);
        }
        return selected.deepCopy();
    }

    private static void validateScalarFieldAction(JsonObject action,
                                                  String port)
            throws IOException {
        String signature = firstNonBlank(string(action,
                "accessFieldSignature"), string(action, "field"),
                string(action, "cell"));
        Matcher declared = Pattern.compile(
                "^<([^:<>]+):\\s*([^\\s<>]+)\\s+([^\\s<>]+)>$")
                .matcher(signature);
        if (!declared.matches()) {
            throw gap("SCALAR_FIELD_ACTION_DECLARATION_INVALID:" + port);
        }
        String owner = declared.group(1);
        String type = declared.group(2);
        String field = declared.group(3);
        String method = string(action, "accessMethod");
        int unitIndex = integer(action, "accessUnitIndex", -1);
        String site = string(action, "accessSiteId");
        String authority = string(action, "accessSiteAuthority");
        JsonArray path = array(action, "fieldPath");
        boolean pathExact = path.size() == 0
                || path.size() == 1 && path.get(0).isJsonPrimitive()
                && field.equals(path.get(0).getAsString());
        if (!port.equals(string(action, "symbol"))
                || !"FIELD_ACCESS".equals(string(action, "bindingMode"))
                || !"HEAP_OBJECT_FIELD".equals(string(action, "location"))
                || !isSupportedScalarJavaType(type)
                || !signature.equals(firstNonBlank(string(action, "field"),
                string(action, "cell")))
                || !owner.equals(string(action, "accessOwnerClass"))
                || !field.equals(string(action, "accessField"))
                || !type.equals(string(action, "accessFieldType"))
                || method.isEmpty() || unitIndex < 0
                || !site.equals(method + "#u" + unitIndex)
                || !("STATIC_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1"
                .equals(authority)
                || "RUNTIME_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1"
                .equals(authority))
                || !pathExact) {
            throw gap("SCALAR_FIELD_ACTION_IDENTITY_INCOMPLETE:" + port);
        }
    }

    private static void validateDynamicFieldAction(JsonObject action,
                                                   JsonObject binding,
                                                   String port)
            throws IOException {
        String fieldSignature = string(binding, "fieldSignature");
        JsonArray fieldPath = array(binding, "fieldPath");
        boolean validPath = fieldPath.size() > 0;
        for (JsonElement segment : fieldPath) {
            validPath &= segment.isJsonPrimitive()
                    && segment.getAsJsonPrimitive().isString()
                    && !segment.getAsString().isEmpty();
        }
        if (!port.equals(string(action, "symbol"))
                || !"HEAP_OBJECT_FIELD".equals(string(action, "location"))
                || !fieldSignature.equals(firstNonBlank(
                string(action, "field"), string(action, "cell")))
                || !fieldPath.equals(array(action, "fieldPath"))
                || !validPath) {
            throw gap("DYNAMIC_FIELD_ACTION_IDENTITY_INCOMPLETE:" + port);
        }
        if (DYNAMIC_CONTAINER_FIELD_KIND.equals(string(binding, "kind"))) {
            JsonObject selector = object(binding, "containerSelector");
            boolean exactLeafDeclaration = fieldSignature.equals(string(
                    action,
                    "leafFieldSignature"))
                    && string(selector, "declaredFieldOwnerClass").equals(
                    string(action, "leafOwnerClass"))
                    && fieldPath.get(fieldPath.size() - 1).getAsString()
                    .equals(string(action, "leafField"));
            boolean directPath = fieldPath.size() == 1
                    && exactLeafDeclaration
                    && fieldSignature.equals(string(action,
                    "accessFieldSignature"))
                    && fieldPath.get(0).getAsString().equals(string(action,
                    "accessField"));
            boolean deepPath = fieldPath.size() >= 2
                    && fieldPath.size() <= 4
                    && exactLeafDeclaration
                    && "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1"
                    .equals(string(action, "fieldPathAuthority"))
                    && fieldPath.get(0).getAsString().equals(string(action,
                    "accessField"))
                    && !string(action, "accessFieldSignature").isEmpty();
            if (!directPath && !deepPath) {
                throw gap("DYNAMIC_CONTAINER_DECLARED_ACTION_INCOMPLETE:"
                        + port);
            }
        }
    }

    private static void requireContainerAction(JsonObject activation,
                                               JsonObject selector)
            throws IOException {
        String port = string(selector, "containerInputPort");
        String cell = string(selector, "containerInputCell");
        JsonObject selected = null;
        JsonArray source = array(activation, "symbolize");
        for (JsonElement element : source) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            if (!port.equals(string(action, "symbol"))) continue;
            if (selected != null) {
                throw gap("AMBIGUOUS_DYNAMIC_CONTAINER_ACTION:" + port);
            }
            selected = action;
        }
        if (selected == null || !cell.equals(string(selected, "cell"))
                || !"CONTAINER_INPUT_OBSERVATION".equals(string(selected,
                "bindingMode"))
                || !bool(selected, "arrayFieldObservationOnly", false)
                || bool(selected, "modelControllable", true)) {
            throw gap("DYNAMIC_CONTAINER_ACTION_MISSING:" + port);
        }
    }

    private static void validateInputAdmission(JsonObject summary,
                                               String port,
                                               JsonObject dynamicBinding)
            throws IOException {
        JsonObject admission = object(summary,
                "inputMaterializationAdmission");
        String authority = string(admission, "authority");
        boolean explicitFallbackAuthority =
                ("STATIC_GLOBAL_SLICE_DEMAND_REFINED_BY_EXACT_"
                        + "TRANSFORMER_RUNTIME_PATH_PROOFS_AND_EXPLICIT_"
                        + "CONCRETE_FALLBACKS").equals(authority);
        String observedSymbol = dynamicBinding == null ? port
                : string(dynamicBinding, "dynamicFieldSymbol");
        if (observedSymbol.isEmpty()
                || !bool(admission, "complete", false)
                || !exactInputMaterializationAuthority(authority)
                || array(admission, "failures").size() != 0
                || countString(array(admission, "globalSliceInputs"), port)
                != 1
                || countString(array(admission, "requiredSliceInputs"), port)
                != 1
                || countString(array(admission,
                "observedSymbolizedInputs"), observedSymbol) != 1
                || countString(array(admission,
                "pathInactiveSliceInputs"), port) != 0
                || (explicitFallbackAuthority
                && (!isArray(admission, "admittedObservedInputs")
                || !isArray(admission, "admittedConcreteFallbackInputs")
                || !isArray(admission,
                "admittedVmIntrinsicPlaceholderInputs")
                || !isArray(admission,
                "unforcedEnvironmentValidationRequirements")
                || !("SCHEDULED_OBSERVATION_ONLY_INPUT_PLUS_UNIQUE_"
                + "COMPLETE_FIRST_CONTAINER_RUNTIME_EVIDENCE_V1").equals(
                string(admission, "admittedObservedInputAuthority"))))
                || coversInput(array(admission, "admittedObservedInputs"),
                port)
                || coversInput(array(admission,
                "admittedConcreteFallbackInputs"), port)
                || coversInput(array(admission,
                "admittedVmIntrinsicPlaceholderInputs"), port)
                || requirementsCoverInput(array(admission,
                "unforcedEnvironmentValidationRequirements"), port)) {
            throw gap("SELECTED_SUMMARY_INPUT_ADMISSION_NOT_EXACT:" + port);
        }
    }

    private static boolean exactInputMaterializationAuthority(
            String authority) {
        String base = "STATIC_GLOBAL_SLICE_DEMAND_REFINED_BY_EXACT_"
                + "TRANSFORMER_RUNTIME_PATH_PROOFS";
        return base.equals(authority)
                || (base + "_AND_EXPLICIT_CONCRETE_FALLBACKS").equals(
                authority);
    }

    private static boolean coversInput(JsonArray values, String port) {
        for (JsonElement value : values) {
            if (value == null || !value.isJsonPrimitive()
                    || !value.getAsJsonPrimitive().isString()) {
                continue;
            }
            String candidate = value.getAsString();
            if (candidate.equals(port) || candidate.startsWith(port + ".")) {
                return true;
            }
        }
        return false;
    }

    private static boolean requirementsCoverInput(JsonArray requirements,
                                                  String port) {
        for (JsonElement element : requirements) {
            if (!element.isJsonObject()) continue;
            String candidate = string(element.getAsJsonObject(),
                    "inputPort");
            if (candidate.equals(port) || candidate.startsWith(port + ".")) {
                return true;
            }
        }
        return false;
    }

    private static void validateLocalDefinitionIdentity(JsonObject action,
                                                        String port)
            throws IOException {
        String location = string(action, "location");
        boolean regionLiveIn = "REGION_LIVE_IN".equals(location);
        boolean callReturnDefinition = "CALL_RETURN".equals(location)
                && "CALL_RETURN_DEFINITION".equals(string(action,
                "sourceBindingMode"))
                && "OPAQUE_CALL".equals(string(action, "sourceKind"))
                && "return".equals(string(action, "projection"))
                && string(action, "cell").endsWith(">.return");
        String method = string(action, "method");
        String local = string(action, "local");
        JsonArray sites = array(action, "definitionSites");
        if ((!regionLiveIn && !callReturnDefinition)
                || method.isEmpty() || local.isEmpty()
                || sites.size() != 1 || !sites.get(0).isJsonObject()
                || !"STATIC_DATAFLOW_DEF_SITE".equals(string(action,
                "definitionAuthority"))) {
            throw gap("LOCAL_DEFINITION_ACTION_IDENTITY_INCOMPLETE:" + port);
        }
        JsonObject site = sites.get(0).getAsJsonObject();
        int unit = integer(site, "unitIndex", -1);
        if (unit < 0 || !method.equals(string(site, "method"))
                || !local.equals(string(site, "local"))
                || (!string(site, "siteId").isEmpty()
                && !string(site, "siteId").equals(method + "#u" + unit))) {
            throw gap("LOCAL_DEFINITION_ACTION_SITE_MISMATCH:" + port);
        }
    }

    private static void validateRootEntryIdentity(JsonObject action,
                                                  String port)
            throws IOException {
        String location = string(action, "location");
        boolean argument = "ARGUMENT".equals(location)
                || "ARGUMENT_FIELD".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location);
        boolean receiver = "RECEIVER_FIELD".equals(location);
        if ((!argument && !receiver)
                || (argument && integer(action, "index", -1) < 0)
                || (receiver && string(action, "field").isEmpty())) {
            throw gap("ROOT_ENTRY_ACTION_IDENTITY_INCOMPLETE:" + port);
        }
    }

    private static JsonObject modelAssignment(JsonObject mapping,
                                              JsonObject root,
                                              JsonObject action,
                                              String actionIdentity)
            throws IOException {
        String canonical = string(root, "solverTerm");
        if (!canonical.equals(canonicalProjectionTerm(mapping))) {
            throw gap("CASE_MAPPING_IS_NOT_CANONICAL_ROOT_TERM:"
                    + string(root, "portId"));
        }
        JsonObject result = new JsonObject();
        result.addProperty("engineSymbol", string(mapping,
                "rawEngineSymbol"));
        result.addProperty("solverSymbol", canonical);
        result.addProperty("actualCaseSolverTerm", string(mapping,
                "solverTerm"));
        result.addProperty("inputSymbol", string(root, "portId"));
        result.addProperty("valueType", "BOOL");
        result.addProperty("value", bool(root, "value", false)
                ? "true" : "false");
        result.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        result.addProperty("materializeAtRealDefinition", true);
        result.add("target", action.deepCopy());
        result.addProperty("targetActionIdentitySha256", actionIdentity);
        result.add("targetActionIdentity", actionIdentity(action));
        result.addProperty("projectionAuthority",
                "BOOTSTRAP_COMPOSED_SMT_EXACT_SELECTED_CASE_ROOT_TERM_"
                        + "AND_ACTION_IDENTITY_V2");
        if (!string(mapping, "canonicalSolverTerm").isEmpty()) {
            JsonObject bridge = new JsonObject();
            for (String member : new String[]{"canonicalPort",
                    "canonicalSolverTerm", "canonicalBridgeGuard",
                    "canonicalBridgeExpression", "canonicalBridgeFormula",
                    "canonicalBridgeAssertionName",
                    "canonicalBridgeAssertion",
                    "canonicalBridgeAssertionSha256",
                    "canonicalBridgeAuthority"}) {
                copy(mapping, bridge, member);
            }
            bridge.add("dynamicBindingIds", array(mapping,
                    "dynamicBindingIds").deepCopy());
            result.add("canonicalDynamicRootBridge", bridge);
        }
        return result;
    }

    private static JsonObject primitiveModelAssignment(JsonObject mapping,
                                                       String port,
                                                       String valueType,
                                                       String value,
                                                       JsonObject action,
                                                       String actionIdentity) {
        String canonical = canonicalProjectionTerm(mapping);
        JsonObject result = new JsonObject();
        result.addProperty("engineSymbol", string(mapping,
                "rawEngineSymbol"));
        result.addProperty("solverSymbol", canonical);
        result.addProperty("actualCaseSolverTerm", string(mapping,
                "solverTerm"));
        result.addProperty("inputSymbol", port);
        result.addProperty("valueType", valueType);
        result.addProperty("value", value);
        result.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        result.addProperty("materializeAtRealDefinition", true);
        result.add("target", action.deepCopy());
        result.addProperty("targetActionIdentitySha256", actionIdentity);
        result.add("targetActionIdentity", actionIdentity(action));
        result.addProperty("projectionAuthority",
                "BOOTSTRAP_COMPOSED_SMT_SELECTED_CASE_FREE_PRIMITIVE_"
                        + "TERM_AND_ACTION_IDENTITY_V1");
        return result;
    }

    private static String scalarPrimitiveValueType(JsonObject action,
                                                   JsonObject mapping,
                                                   String port,
                                                   String catalogJavaType,
                                                   String catalogDescriptor)
            throws IOException {
        String sort = string(mapping, "sort");
        String solverSort = string(mapping, "solverSort");
        String type = firstNonBlank(string(action, "accessFieldType"),
                string(action, "javaType"), catalogJavaType,
                catalogDescriptor);
        if ("INT".equals(sort) && "Int".equals(solverSort)) {
            if ("boolean".equals(type) || "java.lang.Boolean".equals(type)
                    || "Ljava/lang/Boolean;".equals(type)
                    || "Z".equals(type)) {
                return "BOOL";
            }
            if (isIntegralPrimitiveType(type)) return "INT";
        } else if (("FLOAT32".equals(sort)
                && "(_ FloatingPoint 8 24)".equals(solverSort)
                || "FLOAT64".equals(sort)
                && "(_ FloatingPoint 11 53)".equals(solverSort))) {
            if (isRealPrimitiveType(type)) return "REAL";
        } else if ("STRING".equals(sort)
                && "String".equals(solverSort)) {
            if (isStringType(type)) return "STRING";
        } else {
            throw gap("SUPPLEMENTAL_PRIMITIVE_SORT_UNSUPPORTED:" + port
                    + ":" + sort + "/" + solverSort);
        }
        throw gap("SUPPLEMENTAL_PRIMITIVE_SORT_TYPE_MISMATCH:" + port
                + ":" + sort + "/" + solverSort + ":" + type);
    }

    private static boolean isIntegralPrimitiveType(String type) {
        return "boolean".equals(type) || "byte".equals(type)
                || "char".equals(type) || "short".equals(type)
                || "int".equals(type) || "long".equals(type)
                || "java.lang.Byte".equals(type)
                || "java.lang.Character".equals(type)
                || "java.lang.Short".equals(type)
                || "java.lang.Integer".equals(type)
                || "java.lang.Long".equals(type)
                || "Z".equals(type) || "B".equals(type)
                || "C".equals(type) || "S".equals(type)
                || "I".equals(type) || "J".equals(type)
                || "Ljava/lang/Byte;".equals(type)
                || "Ljava/lang/Character;".equals(type)
                || "Ljava/lang/Short;".equals(type)
                || "Ljava/lang/Integer;".equals(type)
                || "Ljava/lang/Long;".equals(type);
    }

    private static boolean isRealPrimitiveType(String type) {
        return "float".equals(type) || "double".equals(type)
                || "java.lang.Float".equals(type)
                || "java.lang.Double".equals(type)
                || "Ljava/lang/Float;".equals(type)
                || "Ljava/lang/Double;".equals(type)
                || "F".equals(type) || "D".equals(type);
    }

    private static boolean isStringType(String type) {
        return "String".equals(type) || "java.lang.String".equals(type)
                || "java/lang/String".equals(type)
                || "Ljava/lang/String;".equals(type);
    }

    private static boolean isSupportedScalarJavaType(String type) {
        return isIntegralPrimitiveType(type) || isRealPrimitiveType(type)
                || isStringType(type);
    }

    private static String normalizePrimitiveModelValue(String valueType,
                                                       String value,
                                                       String port,
                                                       String floatingDescriptor)
            throws IOException {
        String normalized = value == null ? "" : value.trim();
        if ("BOOL".equals(valueType)) {
            if ("1".equals(normalized) || "true".equals(normalized)) {
                return "true";
            }
            if ("0".equals(normalized) || "false".equals(normalized)) {
                return "false";
            }
        } else if ("INT".equals(valueType)
                && normalized.matches("-?(?:0|[1-9][0-9]*)")) {
            return normalized;
        } else if ("REAL".equals(valueType)) {
            String decoded = SmtModelValueCodec
                    .floatingPointTermToJavaLiteral(normalized,
                            floatingDescriptor);
            if (decoded != null) return decoded;
        } else if ("STRING".equals(valueType)
                && validSmtStringValue(normalized)) {
            return normalized;
        }
        throw gap("SUPPLEMENTAL_PRIMITIVE_MODEL_VALUE_UNSUPPORTED:" + port
                + ":" + normalized);
    }

    private static String scalarFloatingDescriptor(JsonObject action,
                                                   JsonObject mapping,
                                                   String catalogJavaType,
                                                   String catalogDescriptor) {
        String sort = string(mapping, "sort");
        String type = firstNonBlank(string(action, "accessFieldType"),
                string(action, "javaType"), catalogJavaType,
                catalogDescriptor);
        if ("FLOAT32".equals(sort) && isFloatType(type)) return "F";
        if ("FLOAT64".equals(sort) && isDoubleType(type)) return "D";
        return "";
    }

    private static boolean isFloatType(String type) {
        return "float".equals(type) || "java.lang.Float".equals(type)
                || "java/lang/Float".equals(type)
                || "Ljava/lang/Float;".equals(type) || "F".equals(type);
    }

    private static boolean isDoubleType(String type) {
        return "double".equals(type) || "java.lang.Double".equals(type)
                || "java/lang/Double".equals(type)
                || "Ljava/lang/Double;".equals(type) || "D".equals(type);
    }

    private static boolean validSmtRealValue(String value) {
        String atom = "-?(?:0|[1-9][0-9]*)(?:\\.[0-9]+)?";
        if (value.matches(atom)) return true;
        if (value.matches("\\(/\\s+" + atom + "\\s+" + atom + "\\)")) {
            return !value.matches(".*\\s-?0(?:\\.0+)?\\)");
        }
        return value.matches("\\(-\\s+" + atom + "\\)")
                || value.matches("\\(-\\s+\\(/\\s+" + atom + "\\s+"
                + atom + "\\)\\)")
                && !value.matches(".*\\s-?0(?:\\.0+)?\\)\\)");
    }

    private static boolean validSmtStringValue(String value) {
        if (value == null || value.length() < 2 || value.charAt(0) != '"'
                || value.charAt(value.length() - 1) != '"') {
            return false;
        }
        for (int index = 1; index < value.length() - 1; index++) {
            if (value.charAt(index) != '"') continue;
            if (index + 1 >= value.length() - 1
                    || value.charAt(index + 1) != '"') return false;
            index++;
        }
        return true;
    }

    private static JsonObject projectedInputManifest(
            String region, String port, JsonObject selectedCase,
            JsonObject mapping, String solverTerm, String modelValue,
            JsonObject action, String actionIdentity) {
        JsonObject result = new JsonObject();
        result.addProperty("regionId", region);
        result.addProperty("inputPort", port);
        result.addProperty("caseId", string(selectedCase, "caseId"));
        result.addProperty("sourceSummaryId", string(selectedCase,
                "sourceSummaryId"));
        result.addProperty("sourceActivationId", string(selectedCase,
                "sourceActivationId"));
        result.addProperty("selectorSolverSymbol", string(selectedCase,
                "selectorSolverSymbol"));
        result.addProperty("rawEngineSymbol", string(mapping,
                "rawEngineSymbol"));
        result.addProperty("canonicalSolverTerm", solverTerm);
        result.addProperty("modelValue", modelValue);
        result.addProperty("materializationActionIdentitySha256",
                actionIdentity);
        result.add("materializationActionIdentity", actionIdentity(action));
        return result;
    }

    private static void addNullableStringModelProvenance(
            JsonObject target, String nullnessSolverTerm,
            String nullnessModelValue, String contentSolverTerm,
            String contentModelValue) {
        target.addProperty("nullnessSolverTerm", nullnessSolverTerm);
        target.addProperty("nullnessModelValue", nullnessModelValue);
        target.addProperty("contentSolverTerm", contentSolverTerm);
        target.addProperty("contentModelValue", contentModelValue);
        target.addProperty("nullableStringEncodingAuthority",
                NULLABLE_STRING_ENCODING_AUTHORITY);
    }

    private static void retainDynamicLeafSelector(JsonObject assignment,
                                                  JsonObject binding)
            throws IOException {
        String kind = string(binding, "kind");
        String base = string(binding, "baseInputSymbol");
        String dynamic = string(binding, "dynamicFieldSymbol");
        String site = string(binding, "materializationSiteId");
        int occurrence = integer(binding, "materializationOccurrence", -1);
        assignment.addProperty("inputSymbol", base);
        copy(binding, assignment, "dynamicBindingId");
        copy(binding, assignment, "baseInputSymbol");
        copy(binding, assignment, "dynamicFieldSymbol");
        copy(binding, assignment, "materializationSiteId");
        copy(binding, assignment, "materializationOccurrence");
        copy(binding, assignment, "fieldSignature");
        copy(binding, assignment, "fieldPath");
        assignment.addProperty("dynamicFieldBindingKind", kind);
        assignment.add("materializationPath",
                array(binding, "fieldPath").deepCopy());

        JsonObject selector = new JsonObject();
        selector.addProperty("materializationSiteId", site);
        selector.addProperty("materializationOccurrence", occurrence);
        if (DYNAMIC_CONTAINER_FIELD_KIND.equals(kind)) {
            JsonObject runtimeSelector = object(binding,
                    "containerSelector");
            JsonObject containerSelector = new JsonObject();
            for (String member : new String[]{"kind", "bindingId",
                    "containerInputPort", "containerInputCell",
                    "selectorAuthority", "elementIndex",
                    "elementOccurrence", "declaredFieldOwnerClass",
                    "declaredFieldType"}) {
                copy(runtimeSelector, containerSelector, member);
            }
            assignment.add("containerSelector",
                    containerSelector.deepCopy());
            selector.add("containerSelector",
                    containerSelector.deepCopy());
            assignment.addProperty("containerReplayRebindingAuthority",
                    CONTAINER_REPLAY_REBINDING_AUTHORITY);
            assignment.addProperty(
                    "sourceContainerObjectTokensRetained", false);
            for (String member : new String[]{"containerBindingId",
                    "containerInputPort", "containerInputCell",
                    "selectorAuthority", "elementIndex",
                    "elementOccurrence", "declaredFieldOwnerClass",
                    "declaredFieldType"}) {
                copy(binding, assignment, member);
            }
        } else if (DYNAMIC_MAP_ENTRY_FIELD_KIND.equals(kind)) {
            // A source JVM's entry id, key and observation id are not stable
            // replay selectors.  Runtime rebinds the exact static field site
            // and occurrence to the fresh entry selected in the replay JVM.
            assignment.addProperty("dynamicReplayRebindingAuthority",
                    FRESH_MAP_ENTRY_REBINDING_AUTHORITY);
            assignment.addProperty("sourceEntrySelectorRetained", false);
            selector.addProperty("replayRebindingAuthority",
                    FRESH_MAP_ENTRY_REBINDING_AUTHORITY);
            selector.addProperty("sourceEntrySelectorRetained", false);
        } else {
            throw gap("UNSUPPORTED_DYNAMIC_LEAF_BINDING_KIND:" + kind);
        }
        assignment.add("dynamicSelector", selector);

        if (!exactEngineSymbol(string(assignment, "engineSymbol"), dynamic)) {
            throw gap("DYNAMIC_ASSIGNMENT_ENGINE_SYMBOL_MISMATCH:" + dynamic);
        }
    }

    private static void copy(JsonObject source, JsonObject target,
                             String member) {
        JsonElement value = source.get(member);
        if (value != null) target.add(member, value.deepCopy());
    }

    private static boolean exactEngineSymbol(String raw, String symbol) {
        if (raw == null || symbol == null || symbol.isEmpty()) return false;
        if (raw.equals(symbol)) return true;
        if (raw.length() <= 10 || raw.charAt(0) != 'M'
                || raw.charAt(1) != '_'
                || "ZCBSIFJDL".indexOf(raw.charAt(2)) < 0
                || !raw.startsWith("_field_", 3)) {
            return false;
        }
        String payload = raw.substring(10);
        if (payload.equals(symbol)) return true;
        String boundary = symbol + "_";
        return payload.startsWith(boundary)
                && legalVmOwnerSuffix(payload.substring(boundary.length()));
    }

    private static boolean legalVmOwnerSuffix(String suffix) {
        return suffix != null && suffix.matches(
                "[A-Za-z_$][A-Za-z0-9_$]*"
                        + "(?:/[A-Za-z_$][A-Za-z0-9_$]*)*");
    }

    private static JsonObject actionIdentity(JsonObject action) {
        JsonObject result = new JsonObject();
        result.addProperty("symbol", string(action, "symbol"));
        result.addProperty("bindingMode", string(action, "bindingMode"));
        result.addProperty("location", string(action, "location"));
        result.addProperty("cell", string(action, "cell"));
        result.addProperty("method", string(action, "method"));
        result.addProperty("local", string(action, "local"));
        result.addProperty("index", integer(action, "index", -1));
        result.add("definitionSites", array(action,
                "definitionSites").deepCopy());
        result.addProperty("canonicalActionSha256",
                actionIdentitySha256(action));
        result.addProperty("authority",
                "CANONICAL_FULL_ACTION_JSON_PLUS_EXACT_BINDING_FIELDS_V1");
        return result;
    }

    private static String actionIdentitySha256(JsonObject action) {
        return sha256(canonicalJson(action));
    }

    private static String canonicalJson(JsonElement element) {
        if (element == null || element.isJsonNull()) return "null";
        if (element.isJsonArray()) {
            StringBuilder result = new StringBuilder("[");
            boolean first = true;
            for (JsonElement item : element.getAsJsonArray()) {
                if (!first) result.append(',');
                result.append(canonicalJson(item));
                first = false;
            }
            return result.append(']').toString();
        }
        if (element.isJsonObject()) {
            JsonObject object = element.getAsJsonObject();
            List<String> names = new ArrayList<>(object.keySet());
            Collections.sort(names);
            StringBuilder result = new StringBuilder("{");
            boolean first = true;
            for (String name : names) {
                if (!first) result.append(',');
                result.append(GSON.toJson(name)).append(':')
                        .append(canonicalJson(object.get(name)));
                first = false;
            }
            return result.append('}').toString();
        }
        return GSON.toJson(element);
    }

    private static JsonObject producerReplay(JsonObject source,
                                             JsonArray assignments) {
        JsonObject result = source.deepCopy();
        result.add("modelAssignments", assignments.deepCopy());
        result.add("forcedBranches", new JsonArray());
        result.add("replayMaterializations", new JsonArray());
        result.remove("targetBranch");
        result.remove("expectedBranchPrefix");
        result.addProperty("executionPhase",
                "BOOTSTRAP_UPSTREAM_MODEL_REPLAY");
        result.addProperty("concreteReplayOnly", true);
        result.addProperty("observationOnlyReplay", false);
        result.addProperty("boundedProducerBroadcast", true);
        result.addProperty("branchOverrideProhibited", true);
        result.addProperty("targetReplayRequired", false);
        result.addProperty("modelProjectionAuthority",
                "BOOTSTRAP_COMPOSED_SMT_EXACT_SELECTED_CASE_ROOT_TERM_V1");
        return result;
    }

    private static JsonObject targetReplay(JsonObject source,
                                           JsonObject fatal)
            throws IOException {
        String activationId = string(source, "activationId");
        String regionId = string(source, "regionId");
        String instance = string(source, "regionInstanceId");
        if (!activationId.equals(string(fatal, "activationId"))
                || !regionId.equals(string(fatal, "regionId"))
                || !instance.equals(string(fatal, "regionInstanceId"))
                || !bool(fatal, "readyForSolver", false)) {
            throw gap("TARGET_FATAL_QUERY_IDENTITY_OR_FORMULA_MISMATCH");
        }
        BranchReplayContract contract = replayContract(fatal);
        solverPathContext(fatal);
        JsonObject result = source.deepCopy();
        result.add("modelAssignments", new JsonArray());
        result.add("replayMaterializations", new JsonArray());
        result.remove("forcedBranches");
        result.remove("targetBranch");
        result.remove("branchCaptureSelector");
        result.remove("directedTargetQuery");
        result.remove("branchOverrideProhibited");
        result.add("replayContract", contract.toJson());
        result.addProperty("executionPhase", "REPLAY_DIRECTED_TARGET");
        result.addProperty("targetReplayRequired", true);
        result.addProperty("branchOverrideProhibited", true);
        result.addProperty("concreteReplayOnly", false);
        result.addProperty("observationOnlyReplay", true);
        result.addProperty("downstreamInjectionForbidden", true);
        return result;
    }

    private static BranchReplayContract replayContract(JsonObject query)
            throws IOException {
        JsonElement encoded = query == null ? null
                : query.get("replayContract");
        if (encoded == null || !encoded.isJsonObject()) {
            throw gap("TARGET_REPLAY_CONTRACT_MISSING");
        }
        try {
            return BranchReplayContract.fromJson(
                    encoded.getAsJsonObject());
        } catch (IllegalArgumentException malformed) {
            throw gap("TARGET_REPLAY_CONTRACT_INVALID:"
                    + malformed.getMessage());
        }
    }

    private static SolverPathContext solverPathContext(JsonObject query)
            throws IOException {
        JsonElement encoded = query == null ? null
                : query.get("solverPathContext");
        if (encoded == null || !encoded.isJsonObject()) {
            throw gap("TARGET_SOLVER_PATH_CONTEXT_MISSING");
        }
        try {
            return SolverPathContext.fromJson(encoded.getAsJsonObject());
        } catch (IllegalArgumentException malformed) {
            throw gap("TARGET_SOLVER_PATH_CONTEXT_INVALID:"
                    + malformed.getMessage());
        }
    }

    private static void bundle(JsonObject row, String schedule, String root,
                               int index, int size, String role) {
        row.addProperty("scheduleId", schedule);
        row.addProperty("activationSelectionRequired", "ALL");
        row.addProperty("activationBundleRootActivationId", root);
        row.addProperty("activationBundleScheduleId", schedule);
        row.addProperty("activationBundleSize", size);
        row.addProperty("activationBundleIndex", index);
        row.addProperty("activationBundleMemberRole", role);
    }

    private static JsonObject selectFatal(List<JsonObject> rows)
            throws IOException {
        JsonObject selected = null;
        for (JsonObject row : rows) {
            if (!bool(row, "readyForSolver", false)) continue;
            if (selected != null) throw gap("AMBIGUOUS_BOOTSTRAP_FATAL_QUERY");
            selected = row;
        }
        if (selected == null) throw gap("BOOTSTRAP_FATAL_QUERY_MISSING");
        return selected.deepCopy();
    }

    private static JsonObject selectTarget(List<JsonObject> rows,
                                           JsonObject fatal)
            throws IOException {
        JsonObject selected = null;
        for (JsonObject row : rows) {
            if (!string(fatal, "activationId").equals(string(row,
                    "activationId"))
                    || !string(fatal, "regionId").equals(string(row,
                    "regionId"))
                    || !string(fatal, "regionInstanceId").equals(string(row,
                    "regionInstanceId"))) continue;
            if (selected != null) throw gap("AMBIGUOUS_TARGET_ACTIVATION");
            selected = row;
        }
        if (selected == null) throw gap("TARGET_ACTIVATION_MISSING");
        return selected.deepCopy();
    }

    private static String solverInput(String smt,
                                      Iterable<JsonObject> assignments,
                                      Set<String> terms) {
        StringBuilder result = new StringBuilder(
                SmtLibQueries.stripSolverCommands(smt));
        if (result.length() > 0
                && result.charAt(result.length() - 1) != '\n') {
            result.append('\n');
        }
        for (JsonObject assignment : assignments) {
            result.append("(assert (= ").append(string(assignment,
                    "solverTerm")).append(' ')
                    .append(bool(assignment, "value", false) ? '1' : '0')
                    .append("))\n");
        }
        result.append("(check-sat)\n(get-value (");
        boolean first = true;
        for (String term : terms) {
            if (!first) result.append(' ');
            result.append(term);
            first = false;
        }
        return result.append("))\n").toString();
    }

    private static SolverIdentity attestSolver(Path configured,
                                               long timeoutMillis)
            throws IOException, InterruptedException {
        Path resolved = resolveExecutable(configured);
        Process process = new ProcessBuilder(resolved.toString(),
                "-version").start();
        boolean finished = process.waitFor(Math.max(1L, timeoutMillis),
                TimeUnit.MILLISECONDS);
        if (!finished) {
            process.destroyForcibly();
            process.waitFor();
            throw new IOException("Z3 identity command timed out: "
                    + resolved);
        }
        String stdout = read(process.getInputStream());
        String stderr = read(process.getErrorStream());
        String evidence = (stdout + "\n" + stderr).trim();
        if (process.exitValue() != 0) {
            throw new IOException("Z3 identity command failed with exit "
                    + process.exitValue() + ": " + evidence);
        }
        if (!Pattern.compile("(?i)\\bZ3\\b").matcher(evidence).find()) {
            throw new IOException("Solver identity is not Z3: " + evidence);
        }
        boolean regular = Files.isRegularFile(resolved);
        return new SolverIdentity(configured.toString(),
                resolved.toString(), firstLine(evidence), regular,
                regular ? sha256(resolved) : "");
    }

    private static Path resolveExecutable(Path configured)
            throws IOException {
        if (configured == null || configured.toString().trim().isEmpty()) {
            throw new IOException("Z3 executable is empty");
        }
        String command = configured.toString();
        if (configured.isAbsolute() || command.contains(File.separator)) {
            Path candidate = configured.toAbsolutePath().normalize();
            if (!Files.isRegularFile(candidate)
                    || !Files.isExecutable(candidate)) {
                throw new IOException("Z3 executable is not executable: "
                        + candidate);
            }
            return candidate.toRealPath();
        }
        String path = System.getenv("PATH");
        if (path != null) {
            for (String directory : path.split(Pattern.quote(
                    File.pathSeparator))) {
                if (directory.isEmpty()) continue;
                Path candidate = Paths.get(directory).resolve(command);
                if (Files.isRegularFile(candidate)
                        && Files.isExecutable(candidate)) {
                    return candidate.toRealPath();
                }
            }
        }
        throw new IOException("Z3 executable not found on PATH: " + command);
    }

    private static SolverOutput run(SolverIdentity identity, String input,
                                    long timeoutMillis)
            throws IOException, InterruptedException {
        Process process = new ProcessBuilder(identity.resolvedPath, "-in",
                "-smt2").start();
        try (OutputStream stream = process.getOutputStream()) {
            stream.write(input.getBytes(StandardCharsets.UTF_8));
        }
        boolean finished = process.waitFor(Math.max(1L, timeoutMillis),
                TimeUnit.MILLISECONDS);
        if (!finished) {
            process.destroyForcibly();
            process.waitFor();
            return new SolverOutput(-1, true, read(process.getInputStream()),
                    read(process.getErrorStream()), identity);
        }
        return new SolverOutput(process.exitValue(), false,
                read(process.getInputStream()), read(process.getErrorStream()),
                identity);
    }

    private static Map<String, String> parseValues(String output,
                                                   Set<String> terms)
            throws IOException {
        Map<String, String> result = new LinkedHashMap<>();
        for (String term : terms) {
            Pattern pattern = Pattern.compile("\\(\\s*"
                    + Pattern.quote(term) + "(?=\\s)");
            Matcher matcher = pattern.matcher(output);
            if (!matcher.find()) {
                throw gap("Z3_VALUE_MISSING_OR_DUPLICATE:" + term);
            }
            SmtValue value = smtValue(output, matcher.end());
            if (value == null || !closesValuePair(output, value.end)) {
                throw gap("Z3_VALUE_MISSING_OR_DUPLICATE:" + term);
            }
            if (matcher.find()) {
                throw gap("Z3_VALUE_MISSING_OR_DUPLICATE:" + term);
            }
            String normalized = normalizeSmtValue(value.text);
            if (normalized.startsWith("(- ")
                    && normalized.endsWith(")")
                    && normalized.substring(3,
                    normalized.length() - 1).matches("[0-9]+")) {
                normalized = "-" + normalized.substring(3,
                        normalized.length() - 1);
            }
            result.put(term, normalized);
        }
        return result;
    }

    private static SmtValue smtValue(String text, int start) {
        int cursor = start;
        while (cursor < text.length()
                && Character.isWhitespace(text.charAt(cursor))) cursor++;
        if (cursor >= text.length()) return null;
        int begin = cursor;
        char first = text.charAt(cursor);
        if (first == '"') {
            cursor++;
            while (cursor < text.length()) {
                if (text.charAt(cursor) != '"') {
                    cursor++;
                    continue;
                }
                if (cursor + 1 < text.length()
                        && text.charAt(cursor + 1) == '"') {
                    cursor += 2;
                    continue;
                }
                cursor++;
                return new SmtValue(text.substring(begin, cursor), cursor);
            }
            return null;
        }
        if (first == '(') {
            int depth = 0;
            boolean quoted = false;
            for (; cursor < text.length(); cursor++) {
                char value = text.charAt(cursor);
                if (value == '"') {
                    if (quoted && cursor + 1 < text.length()
                            && text.charAt(cursor + 1) == '"') {
                        cursor++;
                    } else {
                        quoted = !quoted;
                    }
                } else if (!quoted && value == '(') {
                    depth++;
                } else if (!quoted && value == ')' && --depth == 0) {
                    cursor++;
                    return new SmtValue(text.substring(begin, cursor),
                            cursor);
                }
            }
            return null;
        }
        while (cursor < text.length()
                && !Character.isWhitespace(text.charAt(cursor))
                && text.charAt(cursor) != ')') cursor++;
        return cursor == begin ? null
                : new SmtValue(text.substring(begin, cursor), cursor);
    }

    private static boolean closesValuePair(String text, int start) {
        int cursor = start;
        while (cursor < text.length()
                && Character.isWhitespace(text.charAt(cursor))) cursor++;
        return cursor < text.length() && text.charAt(cursor) == ')';
    }

    private static String normalizeSmtValue(String value) {
        if (value == null || value.isEmpty() || value.charAt(0) == '"') {
            return value == null ? "" : value;
        }
        StringBuilder result = new StringBuilder(value.length());
        boolean whitespace = false;
        for (int index = 0; index < value.length(); index++) {
            char character = value.charAt(index);
            if (Character.isWhitespace(character)) {
                whitespace = true;
            } else {
                if (whitespace && result.length() > 0
                        && result.charAt(result.length() - 1) != '(') {
                    result.append(' ');
                }
                result.append(character);
                whitespace = false;
            }
        }
        return result.toString();
    }

    private static final class SmtValue {
        private final String text;
        private final int end;

        private SmtValue(String text, int end) {
            this.text = text;
            this.end = end;
        }
    }

    private static String read(InputStream stream) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[4096];
        int read;
        while ((read = stream.read(buffer)) >= 0) output.write(buffer, 0, read);
        return new String(output.toByteArray(), StandardCharsets.UTF_8);
    }

    private static String firstLine(String value) {
        if (value == null) return "";
        for (String line : value.split("\\R")) {
            if (!line.trim().isEmpty()) return line.trim();
        }
        return "";
    }

    private static Map<String, JsonObject> uniqueIndex(
            List<JsonObject> rows, String field) throws IOException {
        Map<String, JsonObject> result = new LinkedHashMap<>();
        for (JsonObject row : rows) {
            String key = string(row, field);
            if (key.isEmpty()) continue;
            JsonObject previous = result.put(key, row);
            if (previous != null && !previous.equals(row)) {
                throw gap("CONFLICTING_DUPLICATE_" + field + ":" + key);
            }
        }
        return result;
    }

    private static List<JsonObject> objects(JsonArray array) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : array) {
            if (element.isJsonObject()) result.add(element.getAsJsonObject());
        }
        return result;
    }

    private static JsonObject artifact(Path path) throws IOException {
        JsonObject result = new JsonObject();
        result.addProperty("path", path.toAbsolutePath().normalize().toString());
        result.addProperty("sha256", sha256(path));
        result.addProperty("sizeBytes", Files.size(path));
        return result;
    }

    private static String sha256(Path path) throws IOException {
        return sha256(Files.readAllBytes(path));
    }

    private static String sha256(String value) {
        return sha256(value.getBytes(StandardCharsets.UTF_8));
    }

    private static String sha256(byte[] value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            StringBuilder result = new StringBuilder();
            for (byte item : digest.digest(value)) {
                result.append(String.format("%02x", item & 0xff));
            }
            return result.toString();
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException(impossible);
        }
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        List<JsonObject> result = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            int number = 0;
            while ((line = reader.readLine()) != null) {
                number++;
                if (line.trim().isEmpty()) continue;
                JsonElement parsed;
                try {
                    parsed = JsonParser.parseString(line);
                } catch (RuntimeException exception) {
                    throw new IOException("Malformed JSONL " + path + ":"
                            + number, exception);
                }
                if (!parsed.isJsonObject()) {
                    throw new IOException("Non-object JSONL " + path + ":"
                            + number);
                }
                result.add(parsed.getAsJsonObject());
            }
        }
        return result;
    }

    private static JsonObject readJson(Path path) throws IOException {
        JsonElement parsed = JsonParser.parseString(readText(path));
        if (!parsed.isJsonObject()) throw new IOException(
                "Expected JSON object: " + path);
        return parsed.getAsJsonObject();
    }

    private static String readText(Path path) throws IOException {
        require(path, "input");
        return new String(Files.readAllBytes(path), StandardCharsets.UTF_8);
    }

    private static void writeJsonl(Path path, List<JsonObject> rows)
            throws IOException {
        StringBuilder result = new StringBuilder();
        for (JsonObject row : rows) {
            result.append(JSONL_GSON.toJson(row)).append('\n');
        }
        write(path, result.toString());
    }

    private static void write(Path path, String value) throws IOException {
        Path parent = path.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        Files.write(path, value.getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING,
                StandardOpenOption.WRITE);
    }

    private static void require(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException(label + " not found: " + path);
        }
    }

    private static IOException gap(String value) {
        return new IOException("BOOTSTRAP_PROJECTION_GAP:" + value);
    }

    private static JsonArray array(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static boolean isArray(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonArray();
    }

    private static JsonArray requireMaterializations(JsonObject activation,
                                                     String role)
            throws IOException {
        if (!isArray(activation, "materializations")) {
            throw gap(role + "_MATERIALIZATIONS_MALFORMED");
        }
        JsonArray actions = activation.getAsJsonArray("materializations");
        for (JsonElement element : actions) {
            if (!element.isJsonObject()) {
                throw gap(role + "_MATERIALIZATIONS_MALFORMED");
            }
        }
        return actions;
    }

    private static JsonObject object(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static String string(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static boolean bool(JsonObject object, String field,
                                boolean fallback) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int integer(JsonObject object, String field, int fallback) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longInteger(JsonObject object, String field,
                                    long fallback) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsLong();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int countString(JsonArray values, String expected) {
        int count = 0;
        for (JsonElement value : values) {
            if (value != null && value.isJsonPrimitive()
                    && value.getAsJsonPrimitive().isString()
                    && expected.equals(value.getAsString())) {
                count++;
            }
        }
        return count;
    }

    private static boolean safeSmtAtom(String value) {
        return value != null && SAFE_SMT_ATOM.matcher(value).matches();
    }

    private static String smtName(String value) {
        String normalized = firstNonBlank(value, "anonymous")
                .replaceAll("[^A-Za-z0-9_]", "_");
        if (normalized.isEmpty()) normalized = "anonymous";
        if (Character.isDigit(normalized.charAt(0))) {
            normalized = "n_" + normalized;
        }
        return normalized;
    }

    private static String firstNonBlank(String... values) {
        if (values == null) return "";
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) return value;
        }
        return "";
    }

    private static final class ScalarRootCatalog {
        private final Map<String, JsonObject> byPort;
        private final Map<String, List<JsonObject>> byRegion;

        private ScalarRootCatalog(Map<String, JsonObject> byPort,
                                  Map<String, List<JsonObject>> byRegion) {
            this.byPort = byPort;
            this.byRegion = byRegion;
        }

        private int size() {
            return byPort.size();
        }

        private Set<String> regionIds() {
            return byRegion.keySet();
        }

        private List<JsonObject> rootsForRegion(String region) {
            List<JsonObject> roots = byRegion.get(region);
            return roots == null ? Collections.<JsonObject>emptyList()
                    : roots;
        }

        private JsonObject rootForPort(String port) {
            JsonObject root = byPort.get(port);
            return root == null ? new JsonObject() : root;
        }

        private Set<String> solverTerms() {
            Set<String> result = new LinkedHashSet<>();
            for (JsonObject root : byPort.values()) {
                result.add(string(root, "solverTerm"));
                String nullness = string(root, "nullnessSolverTerm");
                if (!nullness.isEmpty()) result.add(nullness);
            }
            return result;
        }
    }

    static final class Result {
        final List<JsonObject> activations;
        final JsonObject manifest;

        private Result(List<JsonObject> activations, JsonObject manifest) {
            this.activations = activations;
            this.manifest = manifest;
        }
    }

    private static final class SolverOutput {
        private final int exitCode;
        private final boolean timedOut;
        private final String stdout;
        private final String stderr;
        private final SolverIdentity identity;

        private SolverOutput(int exitCode, boolean timedOut, String stdout,
                             String stderr, SolverIdentity identity) {
            this.exitCode = exitCode;
            this.timedOut = timedOut;
            this.stdout = stdout;
            this.stderr = stderr;
            this.identity = identity;
        }
    }

    private static final class SolverIdentity {
        private final String configuredPath;
        private final String resolvedPath;
        private final String version;
        private final boolean regularFile;
        private final String binarySha256;

        private SolverIdentity(String configuredPath, String resolvedPath,
                               String version, boolean regularFile,
                               String binarySha256) {
            this.configuredPath = configuredPath;
            this.resolvedPath = resolvedPath;
            this.version = version;
            this.regularFile = regularFile;
            this.binarySha256 = binarySha256;
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("configuredPath", configuredPath);
            result.addProperty("resolvedPath", resolvedPath);
            result.addProperty("version", version);
            result.addProperty("regularFile", regularFile);
            result.addProperty("binarySha256", binarySha256);
            result.addProperty("identityAuthority",
                    "SUCCESSFUL_Z3_VERSION_AND_RESOLVED_EXECUTABLE_SHA256_V1");
            return result;
        }
    }

    static final class Arguments {
        private Path smt;
        private Path compositionManifest;
        private Path reachReport;
        private Path summaries;
        private Path activations;
        private Path targetActivations;
        private Path fatalQueries;
        private Path output;
        private Path manifest;
        private Path z3 = Paths.get("z3");
        private long timeoutMillis = 20_000L;

        static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; argv != null && index < argv.length; index++) {
                String item = argv[index];
                if (!item.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException(
                            "Expected --key value, got " + item);
                }
                values.put(item.substring(2), argv[++index]);
            }
            Arguments result = new Arguments();
            result.smt = required(values, "smt");
            result.compositionManifest = required(values,
                    "composition-manifest");
            result.reachReport = required(values, "reach-report");
            result.summaries = required(values, "summaries");
            result.activations = required(values, "activations");
            result.targetActivations = required(values, "target-activations");
            result.fatalQueries = required(values, "fatal-query");
            result.output = required(values, "output");
            result.manifest = values.containsKey("manifest")
                    ? Paths.get(values.get("manifest"))
                    : sibling(result.output,
                    "primitive_bootstrap_projection_manifest.json");
            if (values.containsKey("z3")) result.z3 =
                    Paths.get(values.get("z3"));
            if (values.containsKey("timeout-ms")) result.timeoutMillis =
                    Long.parseLong(values.get("timeout-ms"));
            if (result.timeoutMillis < 1L) throw new IllegalArgumentException(
                    "--timeout-ms must be positive");
            return result;
        }

        private static Path required(Map<String, String> values, String key) {
            String value = values.get(key);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return Paths.get(value);
        }

        private static Path sibling(Path path, String name) {
            Path parent = path.toAbsolutePath().getParent();
            return (parent == null ? Paths.get(".") : parent).resolve(name);
        }
    }
}
