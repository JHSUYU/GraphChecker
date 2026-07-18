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
        Set<String> usedActivationIds = new LinkedHashSet<>();
        for (Map.Entry<String, JsonObject> entry
                : assignmentByPort.entrySet()) {
            String port = entry.getKey();
            JsonObject rootAssignment = entry.getValue();
            String region = string(rootAssignment, "regionId");
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
            JsonObject mapping = exactPortMapping(selectedCase, port);
            JsonObject action = exactAction(summary, source, port);
            String actionIdentity = actionIdentitySha256(action);
            JsonObject modelAssignment = modelAssignment(mapping,
                    rootAssignment, action, actionIdentity);
            JsonObject replay = producerReplay(source, modelAssignment);
            if (!usedActivationIds.add(activationId)) {
                throw gap("ONE_PRODUCER_ACTIVATION_CONTROLS_MULTIPLE_ROOTS:"
                        + activationId);
            }
            producerRows.add(replay);

            JsonObject selected = new JsonObject();
            selected.addProperty("regionId", region);
            selected.addProperty("rootInputPort", port);
            selected.addProperty("caseId", string(selectedCase, "caseId"));
            selected.addProperty("sourceSummaryId", summaryId);
            selected.addProperty("sourceActivationId", activationId);
            selected.addProperty("selectorSolverSymbol", string(selectedCase,
                    "selectorSolverSymbol"));
            selected.addProperty("rawEngineSymbol", string(mapping,
                    "rawEngineSymbol"));
            selected.addProperty("canonicalSolverTerm", string(rootAssignment,
                    "solverTerm"));
            selected.addProperty("modelValue", string(rootAssignment,
                    "value"));
            selected.addProperty("materializationActionIdentitySha256",
                    actionIdentity);
            selected.add("materializationActionIdentity",
                    actionIdentity(action));
            caseManifest.add(selected);
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
                producerRows.size());
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
        String siteId = string(fatal, "siteId");
        int occurrence = integer(fatal, "occurrence", -1);
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
                || !sameBoolean(fatal, composition, "desiredOutcome",
                "fatalDesiredOutcome")
                || integer(composition, "fatalConditionCount", -1)
                != array(fatal, "constraints").size()
                || bool(composition, "fatalReplayValidated", true)
                || !string(composition, "validatedSummaryId").isEmpty()
                || !string(composition,
                "validatedFatalReplaySummary").isEmpty()
                || bool(fatal, "targetReplayValidated", false)
                || bool(fatal, "replayAlreadyValidated", false)) {
            throw gap("COMPOSITION_FATAL_QUERY_IDENTITY_MISMATCH");
        }
        if (!artifactMatches(object(composition, "composedSmtArtifact"),
                arguments.smt, sha256(smt))
                || !artifactMatches(object(composition,
                "fatalQueriesArtifact"), arguments.fatalQueries,
                sha256(arguments.fatalQueries))) {
            throw gap("COMPOSITION_FATAL_OR_SMT_ARTIFACT_MISMATCH");
        }
        JsonObject branch = object(target, "targetBranch");
        JsonObject goal = object(target, "captureGoal");
        if (!activationId.equals(string(target, "activationId"))
                || !regionId.equals(string(target, "regionId"))
                || !instanceId.equals(string(target, "regionInstanceId"))
                || !"TARGET_BRANCH".equals(string(goal, "kind"))
                || !siteId.equals(string(branch, "siteId"))
                || occurrence != integer(branch, "occurrence", -1)
                || !sameBoolean(fatal, branch, "desiredOutcome",
                "desiredOutcome")
                || !bool(target, "replayable", false)
                || !bool(target, "symbolicReady", false)
                || !bool(target, "schedulerReady", false)
                || !bool(target, "branchOverrideProhibited", false)) {
            throw gap("TARGET_ACTIVATION_EXACT_BINDING_MISMATCH");
        }
    }

    private static boolean sameBoolean(JsonObject left, JsonObject right,
                                       String leftField,
                                       String rightField) {
        JsonElement leftValue = left == null ? null : left.get(leftField);
        JsonElement rightValue = right == null ? null : right.get(rightField);
        return leftValue != null && rightValue != null
                && leftValue.isJsonPrimitive()
                && rightValue.isJsonPrimitive()
                && leftValue.getAsJsonPrimitive().isBoolean()
                && rightValue.getAsJsonPrimitive().isBoolean()
                && leftValue.getAsBoolean() == rightValue.getAsBoolean();
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
        if (result.size() != rootByPort.size() || result.isEmpty()) {
            throw gap("BOOTSTRAP_VALUATION_ROOT_CARDINALITY_MISMATCH");
        }
        return result;
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
                                               String port)
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
        return selected.deepCopy();
    }

    private static JsonObject exactAction(JsonObject summary,
                                          JsonObject activation, String port)
            throws IOException {
        validateInputAdmission(summary, port);
        JsonArray source = array(activation, "materializations");
        if (source.size() == 0) source = array(activation, "symbolize");
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
        if ("LOCAL_DEFINITION".equals(bindingMode)) {
            validateLocalDefinitionIdentity(selected, port);
        } else if ("ROOT_ENTRY".equals(bindingMode)) {
            validateRootEntryIdentity(selected, port);
        } else {
            throw gap("ROOT_INPUT_ACTION_BINDING_NOT_MODEL_CONTROLLABLE:"
                    + port + ":" + bindingMode);
        }
        return selected.deepCopy();
    }

    private static void validateInputAdmission(JsonObject summary,
                                               String port)
            throws IOException {
        JsonObject admission = object(summary,
                "inputMaterializationAdmission");
        String authority = string(admission, "authority");
        boolean explicitFallbackAuthority =
                ("STATIC_GLOBAL_SLICE_DEMAND_REFINED_BY_EXACT_"
                        + "TRANSFORMER_RUNTIME_PATH_PROOFS_AND_EXPLICIT_"
                        + "CONCRETE_FALLBACKS").equals(authority);
        if (!bool(admission, "complete", false)
                || !exactInputMaterializationAuthority(authority)
                || array(admission, "failures").size() != 0
                || countString(array(admission, "globalSliceInputs"), port)
                != 1
                || countString(array(admission, "requiredSliceInputs"), port)
                != 1
                || countString(array(admission,
                "observedSymbolizedInputs"), port) != 1
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
        if (!canonical.equals(string(mapping, "solverTerm"))) {
            throw gap("CASE_MAPPING_IS_NOT_CANONICAL_ROOT_TERM:"
                    + string(root, "portId"));
        }
        JsonObject result = new JsonObject();
        result.addProperty("engineSymbol", string(mapping,
                "rawEngineSymbol"));
        result.addProperty("solverSymbol", canonical);
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
        return result;
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
                                             JsonObject assignment) {
        JsonObject result = source.deepCopy();
        JsonArray assignments = new JsonArray();
        assignments.add(assignment);
        result.add("modelAssignments", assignments);
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
                || !bool(fatal, "readyForSolver", false)
                || !fatal.has("originalTargetCondition")
                || !fatal.has("negatedTargetCondition")
                || array(fatal, "constraints").size() == 0) {
            throw gap("TARGET_FATAL_QUERY_IDENTITY_OR_FORMULA_MISMATCH");
        }
        JsonObject result = source.deepCopy();
        result.add("modelAssignments", new JsonArray());
        result.add("forcedBranches", new JsonArray());
        result.add("replayMaterializations", new JsonArray());
        result.add("directedTargetQuery", fatal.deepCopy());
        JsonObject target = new JsonObject();
        target.addProperty("siteId", string(fatal, "siteId"));
        target.addProperty("occurrence", integer(fatal, "occurrence", -1));
        target.addProperty("desiredOutcome", bool(fatal,
                "desiredOutcome", false));
        target.addProperty("validationOnly", true);
        target.addProperty("branchOverrideAllowed", false);
        result.add("targetBranch", target);
        result.addProperty("executionPhase", "REPLAY_DIRECTED_TARGET");
        result.addProperty("targetReplayRequired", true);
        result.addProperty("branchOverrideProhibited", true);
        result.addProperty("concreteReplayOnly", false);
        result.addProperty("observationOnlyReplay", true);
        result.addProperty("downstreamInjectionForbidden", true);
        return result;
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
                SymbolicRelationshipVerifier.stripSolverCommands(smt));
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
                    + Pattern.quote(term)
                    + "\\s+(true|false|-?[0-9]+|\\(-\\s+[0-9]+\\))\\s*\\)");
            Matcher matcher = pattern.matcher(output);
            if (!matcher.find()) {
                throw gap("Z3_VALUE_MISSING_OR_DUPLICATE:" + term);
            }
            String value = matcher.group(1);
            if (matcher.find()) {
                throw gap("Z3_VALUE_MISSING_OR_DUPLICATE:" + term);
            }
            value = value.replaceAll("\\s+", "");
            if (value.startsWith("(-") && value.endsWith(")")) {
                value = "-" + value.substring(2, value.length() - 1);
            }
            result.put(term, value);
        }
        return result;
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

    private static String firstNonBlank(String... values) {
        if (values == null) return "";
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) return value;
        }
        return "";
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
