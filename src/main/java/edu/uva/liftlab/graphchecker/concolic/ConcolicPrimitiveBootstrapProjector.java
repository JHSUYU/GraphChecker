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
        SolverOutput solver = run(arguments.z3, solverInput,
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
            JsonObject summary = summaries.get(summaryId);
            JsonObject source = activations.get(activationId);
            validateSource(region, summaryId, activationId, summary, source);
            JsonObject mapping = exactPortMapping(selectedCase, port);
            JsonObject action = exactAction(source, port);
            JsonObject modelAssignment = modelAssignment(mapping,
                    rootAssignment, action);
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
        manifest.addProperty("solver", arguments.z3.toString());
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
                        + "ACTIVATION_DEFINITION_BINDING_V1");
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
                false)) {
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
            if (port.isEmpty() || rootByPort.put(port, root) != null
                    || !bool(root, "root", false)
                    || bool(root, "upstreamSupplied", true)
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
            if (root == null || result.put(port, assignment.deepCopy()) != null
                    || !string(root, "solverTerm").equals(string(assignment,
                    "solverTerm"))
                    || !assignment.has("value")
                    || !assignment.get("value").isJsonPrimitive()
                    || !assignment.get("value").getAsJsonPrimitive()
                    .isBoolean()
                    || string(assignment, "solverLiteral").isEmpty()) {
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
            if (selector.isEmpty() || !result.add(selector)
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
        JsonObject selected = null;
        for (JsonElement element : array(pathCase,
                "rawEngineSymbolMappings")) {
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

    private static JsonObject exactAction(JsonObject activation, String port)
            throws IOException {
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
        if (selected == null
                || "UNSUPPORTED".equals(string(selected, "bindingMode"))
                || bool(selected, "deferred", false)) {
            throw gap("ROOT_INPUT_HAS_NO_REAL_MATERIALIZATION:" + port);
        }
        return selected.deepCopy();
    }

    private static JsonObject modelAssignment(JsonObject mapping,
                                              JsonObject root,
                                              JsonObject action)
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
        result.addProperty("projectionAuthority",
                "BOOTSTRAP_COMPOSED_SMT_EXACT_SELECTED_CASE_ROOT_TERM_V1");
        return result;
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
            result.append("(assert ").append(string(assignment,
                    "solverLiteral")).append(")\n");
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

    private static SolverOutput run(Path executable, String input,
                                    long timeoutMillis)
            throws IOException, InterruptedException {
        Process process = new ProcessBuilder(executable.toString(), "-in",
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
                    read(process.getErrorStream()));
        }
        return new SolverOutput(process.exitValue(), false,
                read(process.getInputStream()), read(process.getErrorStream()));
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
        for (JsonObject row : rows) result.append(GSON.toJson(row)).append('\n');
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

        private SolverOutput(int exitCode, boolean timedOut, String stdout,
                             String stderr) {
            this.exitCode = exitCode;
            this.timedOut = timedOut;
            this.stdout = stdout;
            this.stderr = stderr;
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
