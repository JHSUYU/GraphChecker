package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
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
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Projects a complete composed bug-path SMT formula onto its finite Boolean
 * root-input domain.
 *
 * <p>The extractor never accepts caller-authored reachability formulas.  It
 * discovers Java Boolean input ports from the static region IR, joins them to
 * the exact canonical terms already emitted by {@link ConcolicSmtComposer},
 * removes inputs supplied by composed producer-output relationships, and asks
 * Z3 about every remaining Boolean valuation.  The resulting truth table and
 * canonical DNF are therefore derived artifacts of the final composed SMT.</p>
 */
public final class BooleanReachConditionExtractor {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();
    private static final Gson BINDING_GSON = new GsonBuilder()
            .disableHtmlEscaping().serializeNulls().create();
    private static final Pattern FIELD_CELL = Pattern.compile(
            "^<[^:]+:\\s+([^()<>\\s]+)\\s+[^()<>\\s]+>(?:#.*)?$");
    private static final Pattern RETURN_CELL = Pattern.compile(
            "^<[^:]+:\\s+([^<>\\s]+)\\s+[^<>\\s(]+\\([^>]*\\)>"
                    + "\\.return(?:#.*)?$");
    private static final Pattern PARAMETER_CELL = Pattern.compile(
            ">\\.param[0-9]+:([^#]+)(?:#.*)?$");
    private BooleanReachConditionExtractor() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        JsonObject manifest = readJson(arguments.manifest);
        Path relationshipsPath = arguments.relationships != null
                ? arguments.relationships
                : referencedPath(manifest, "relationshipCandidates",
                arguments.manifest);
        String smt = readText(arguments.smt);
        JsonObject relationships = readJson(relationshipsPath);
        List<JsonObject> regions = readJsonl(arguments.regions);
        validateArtifactBindings(arguments.smt, arguments.regions,
                relationshipsPath, manifest, relationships);
        Z3Solver solver = new Z3Solver(arguments.z3,
                arguments.timeoutMillis);
        Extraction extraction = extract(smt, manifest, regions,
                relationships, solver,
                arguments.maxInputs, arguments.maxValuations,
                arguments.mode);
        JsonObject report = extraction.report;
        report.add("composedSmtArtifact", artifact(arguments.smt));
        report.add("compositionManifestArtifact",
                artifact(arguments.manifest));
        report.add("staticRegionsArtifact", artifact(arguments.regions));
        report.add("relationshipCandidatesArtifact",
                artifact(relationshipsPath));
        report.add("solverArtifact", solver.artifact());
        write(arguments.output, GSON.toJson(report)
                + System.lineSeparator());
        System.out.println(GSON.toJson(report));
        if (!bool(report, "complete", false)) System.exit(2);
    }

    static Extraction extract(String composedSmt, JsonObject manifest,
                              List<JsonObject> regions,
                              JsonObject relationships, Solver solver,
                              int maxInputs, int maxValuations)
            throws IOException, InterruptedException {
        return extract(composedSmt, manifest, regions, relationships, solver,
                maxInputs, maxValuations, Mode.FINAL_REPORT);
    }

    static Extraction extract(String composedSmt, JsonObject manifest,
                              List<JsonObject> regions,
                              JsonObject relationships, Solver solver,
                              int maxInputs, int maxValuations, Mode mode)
            throws IOException, InterruptedException {
        Mode effectiveMode = mode == null ? Mode.FINAL_REPORT : mode;
        JsonObject report = new JsonObject();
        report.addProperty("schemaVersion", 1);
        report.addProperty("kind", "BOOLEAN_REACH_CONDITION_REPORT");
        report.addProperty("projectionMethod",
                "EXHAUSTIVE_JAVA_BOOLEAN_ROOT_INPUT_ENUMERATION");
        report.addProperty("conditionForm",
                "CANONICAL_DNF_WITH_CONSTANT_FOLDING");
        report.addProperty("callerProvidedConditionUsed", false);
        report.addProperty("composedBugPathAlreadyConstrained", true);
        report.addProperty("composedSmtSha256", sha256(composedSmt));
        report.addProperty("extractionMode", effectiveMode.name());
        report.addProperty("replayBootstrapOnly",
                effectiveMode == Mode.BOOTSTRAP_REPLAY_MODEL);
        report.addProperty("reportableFinalReachCondition",
                effectiveMode == Mode.FINAL_REPORT);

        List<String> gaps = new ArrayList<>();
        validateCompositionAuthority(manifest, relationships, effectiveMode,
                gaps);
        if (firstNonBlank(composedSmt).isEmpty()) {
            gaps.add("COMPOSED_SMT_EMPTY");
        }

        PortCatalog ports = PortCatalog.from(regions, gaps);
        Discovery discovery = discover(composedSmt, manifest,
                relationships, ports, gaps);
        List<BooleanInput> inputs = discovery.rootInputs;
        report.addProperty("staticBooleanInputCount",
                discovery.staticBooleanInputCount);
        report.addProperty("usedBooleanInputCount",
                discovery.usedBooleanInputCount);
        report.addProperty("upstreamSuppliedBooleanInputCount",
                discovery.upstreamSuppliedBooleanInputCount);
        report.addProperty("rootBooleanInputCount", inputs.size());
        report.add("rootBooleanInputs", inputCatalog(inputs));
        report.addProperty("rootInputDiscoveryAuthority",
                "STATIC_BOOLEAN_PORT_TYPE_PLUS_COMPOSER_CANONICAL_TERM_"
                        + "AND_RUNTIME_RELATIONSHIP_DIRECTION_V1");
        report.addProperty("projectionDomain",
                "JAVA_BOOLEAN_CANONICAL_INT_TERMS_ARE_0_OR_1");
        report.addProperty("projectionDomainInputCount",
                discovery.booleanDomainInputs.size());
        report.add("projectionDomainAssertions",
                domainAssertionCatalog(discovery.booleanDomainInputs));
        report.addProperty("maxInputCount", Math.max(0, maxInputs));
        report.addProperty("maxValuationCount",
                Math.max(1, maxValuations));

        long valuationCount = inputs.size() >= 63
                ? Long.MAX_VALUE : 1L << inputs.size();
        if (inputs.size() > Math.max(0, maxInputs)) {
            gaps.add("ROOT_BOOLEAN_INPUT_LIMIT_EXCEEDED:" + inputs.size()
                    + ">" + Math.max(0, maxInputs));
        }
        if (valuationCount > Math.max(1, maxValuations)) {
            gaps.add("BOOLEAN_VALUATION_LIMIT_EXCEEDED:" + valuationCount
                    + ">" + Math.max(1, maxValuations));
        }
        report.addProperty("valuationCount", valuationCount);
        if (!gaps.isEmpty()) {
            return incomplete(report, gaps,
                    "REACH_CONDITION_DISCOVERY_WITH_GAPS");
        }

        String base = SymbolicRelationshipVerifier.stripSolverCommands(
                composedSmt);
        String domainBase = appendBooleanDomain(base,
                discovery.booleanDomainInputs);
        List<Valuation> valuations = new ArrayList<>();
        JsonArray truthTable = new JsonArray();
        int solverInvocations = 0;
        int satisfying = 0;
        int unsatisfying = 0;
        int solverErrors = 0;
        int count = (int) valuationCount;
        for (int ordinal = 0; ordinal < count; ordinal++) {
            boolean[] values = valuation(ordinal, inputs.size());
            String query = valuationQuery(domainBase, inputs, values);
            SolverResult result = solver.check(query);
            solverInvocations++;
            Valuation valuation = new Valuation(ordinal, values,
                    result.status);
            valuations.add(valuation);
            JsonObject row = valuation.toJson(inputs);
            if ("sat".equals(result.status)) {
                row.addProperty("reachesBug", true);
                satisfying++;
            } else if ("unsat".equals(result.status)) {
                row.addProperty("reachesBug", false);
                unsatisfying++;
            } else {
                row.addProperty("reachesBug", false);
                row.addProperty("solverOutput", result.output);
                solverErrors++;
            }
            truthTable.add(row);
        }

        Dnf dnf = Dnf.from(inputs, valuations);
        report.add("truthTable", truthTable);
        report.addProperty("satisfyingValuationCount", satisfying);
        report.addProperty("unsatisfyingValuationCount", unsatisfying);
        report.addProperty("solverErrorCount", solverErrors);
        report.add("reachCondition", dnf.toJson());
        report.addProperty("reachConditionSmtLib", dnf.formula);
        report.addProperty("reachConditionSha256", sha256(dnf.formula));

        String implicationStatus = "not_checked";
        String implicationOutput = "";
        if (solverErrors == 0) {
            SolverResult proof = solver.check(domainBase
                    + "(assert (not " + dnf.formula + "))"
                    + System.lineSeparator() + "(check-sat)"
                    + System.lineSeparator());
            solverInvocations++;
            implicationStatus = proof.status;
            implicationOutput = proof.output;
        }
        report.addProperty("baseImpliesReachConditionStatus",
                implicationStatus);
        report.addProperty("baseImpliesReachCondition",
                "unsat".equals(implicationStatus));
        report.addProperty("implicationPremise",
                "COMPOSED_SMT_AND_JAVA_BOOLEAN_PROJECTION_DOMAIN");
        if (!("unsat".equals(implicationStatus)
                || "not_checked".equals(implicationStatus))) {
            report.addProperty("baseImplicationSolverOutput",
                    implicationOutput);
        }
        report.addProperty("solverInvocationCount", solverInvocations);
        report.addProperty("truthTableComplete", solverErrors == 0
                && satisfying + unsatisfying == valuationCount);
        report.addProperty("exactFiniteProjection",
                solverErrors == 0 && "unsat".equals(implicationStatus));
        boolean complete = solverErrors == 0
                && "unsat".equals(implicationStatus)
                && satisfying + unsatisfying == valuationCount;
        report.add("discoveryGaps", new JsonArray());
        report.addProperty("complete", complete);
        report.addProperty("status", complete
                ? effectiveMode == Mode.FINAL_REPORT
                ? "COMPLETE_EXACT_BOOLEAN_REACH_CONDITION"
                : "COMPLETE_BOOTSTRAP_BOOLEAN_REPLAY_MODEL"
                : "BOOLEAN_REACH_CONDITION_WITH_SOLVER_GAPS");
        return new Extraction(report);
    }

    private static void validateCompositionAuthority(
            JsonObject manifest, JsonObject relationships, Mode mode,
            List<String> gaps) {
        boolean commonManifest = manifest != null
                && integer(manifest, "schemaVersion", -1) == 1
                && "CONCOLIC_COMPOSED_SMT".equals(string(manifest, "kind"))
                && bool(manifest, "caseProjectionCatalogComplete", false);
        boolean commonRelationships = relationships != null
                && integer(relationships, "schemaVersion", -1) == 1
                && "SYMBOLIC_RELATIONSHIP_CANDIDATES".equals(string(
                relationships, "kind"));
        if (mode == Mode.BOOTSTRAP_REPLAY_MODEL) {
            if (!commonManifest
                    || !"BOOTSTRAP".equals(string(manifest,
                    "compositionStage"))
                    || !bool(manifest, "structurallyComplete", false)
                    || bool(manifest, "fatalReplayValidated", true)
                    || bool(manifest, "complete", true)
                    || !bool(manifest, "eligibleForBootstrapModel", false)
                    || bool(manifest,
                    "eligibleToReportAutomaticRelationship", true)) {
                gaps.add("COMPOSITION_MANIFEST_NOT_BOOTSTRAP_MODEL_ELIGIBLE");
            }
            if (!commonRelationships
                    || !"BOOTSTRAP".equals(string(relationships,
                    "compositionStage"))
                    || !bool(relationships, "structurallyComplete", false)
                    || bool(relationships, "fatalReplayValidated", true)
                    || !bool(relationships,
                    "eligibleForBootstrapModel", false)
                    || bool(relationships,
                    "eligibleForAutomaticVerification", true)) {
                gaps.add("RELATIONSHIP_CATALOG_NOT_BOOTSTRAP_MODEL_ELIGIBLE");
            }
            return;
        }
        if (!commonManifest
                || !"VALIDATED_FINAL".equals(string(manifest,
                "compositionStage"))
                || !bool(manifest, "structurallyComplete", false)
                || !bool(manifest, "complete", false)
                || !bool(manifest, "fatalReplayValidated", false)
                || bool(manifest, "eligibleForBootstrapModel", true)
                || !bool(manifest,
                "eligibleToReportAutomaticRelationship", false)) {
            gaps.add("COMPOSITION_MANIFEST_NOT_COMPLETE_AND_ELIGIBLE");
        }
        if (!commonRelationships
                || !"VALIDATED_FINAL".equals(string(relationships,
                "compositionStage"))
                || !bool(relationships, "structurallyComplete", false)
                || !bool(relationships, "fatalReplayValidated", false)
                || bool(relationships, "eligibleForBootstrapModel", true)
                || !bool(relationships,
                "eligibleForAutomaticVerification", false)) {
            gaps.add("RELATIONSHIP_CATALOG_NOT_COMPLETE_AND_ELIGIBLE");
        }
    }

    private static Discovery discover(String smt, JsonObject manifest,
                                      JsonObject relationships,
                                      PortCatalog ports,
                                      List<String> gaps) {
        Map<String, List<JsonObject>> mappingsByPort =
                new LinkedHashMap<>();
        JsonArray cases = array(manifest, "caseProjectionCatalog");
        if (integer(manifest, "caseProjectionCatalogCount", -1)
                != cases.size()) {
            gaps.add("CASE_PROJECTION_CATALOG_COUNT_MISMATCH");
        }
        for (int caseIndex = 0; caseIndex < cases.size(); caseIndex++) {
            JsonElement caseElement = cases.get(caseIndex);
            if (!caseElement.isJsonObject()) {
                gaps.add("NON_OBJECT_CASE_PROJECTION:" + caseIndex);
                continue;
            }
            JsonObject pathCase = caseElement.getAsJsonObject();
            if (integer(pathCase, "schemaVersion", -1) != 1
                    || !"GUARDED_CASE_PROJECTION_CATALOG".equals(string(
                    pathCase, "kind"))
                    || !bool(pathCase, "complete", false)
                    || !"EMITTER_ACTUAL_TERM_CAPTURE_IN_CASE_SCOPE".equals(
                    string(pathCase,
                            "rawEngineSymbolMappingAuthority"))) {
                gaps.add("INCOMPLETE_CASE_PROJECTION:" + caseIndex);
                continue;
            }
            for (JsonElement mappingElement : array(pathCase,
                    "rawEngineSymbolMappings")) {
                if (!mappingElement.isJsonObject()) continue;
                JsonObject mapping = mappingElement.getAsJsonObject();
                String port = string(mapping, "canonicalPort");
                if (port.isEmpty()) continue;
                List<JsonObject> values = mappingsByPort.get(port);
                if (values == null) {
                    values = new ArrayList<>();
                    mappingsByPort.put(port, values);
                }
                JsonObject evidence = mapping.deepCopy();
                evidence.addProperty("caseId", string(pathCase, "caseId"));
                evidence.addProperty("regionId", string(pathCase,
                        "regionId"));
                evidence.addProperty("sourceSummaryId", string(pathCase,
                        "sourceSummaryId"));
                evidence.addProperty("sourceActivationId", string(pathCase,
                        "sourceActivationId"));
                values.add(evidence);
            }
        }

        Set<String> upstreamSupplied = suppliedInputs(relationships, ports,
                gaps);
        List<BooleanInput> roots = new ArrayList<>();
        List<BooleanInput> domainInputs = new ArrayList<>();
        int staticBoolean = 0;
        int usedBoolean = 0;
        int suppliedBoolean = 0;
        for (PortInfo port : ports.sortedInputs()) {
            if (!port.javaBoolean) continue;
            staticBoolean++;
            String solverTerm = "sym__port__" + smtName(port.id) + "__int";
            String portTerm = "port__" + smtName(port.id);
            boolean declared = smt.contains("(declare-const " + solverTerm
                    + " Int)")
                    && smt.contains("(declare-const " + portTerm + " Value)")
                    && (smt.contains("(= " + portTerm + " (VInt "
                    + solverTerm + "))")
                    || smt.contains("(= (VInt " + solverTerm + ") "
                    + portTerm + ")"));
            List<JsonObject> evidence = mappingsByPort.get(port.id);
            if (!declared && (evidence == null || evidence.isEmpty())) {
                continue;
            }
            usedBoolean++;
            if (!declared) {
                gaps.add("BOOLEAN_PORT_WITHOUT_CANONICAL_SMT_BINDING:"
                        + port.id);
                continue;
            }
            if (evidence != null) {
                for (JsonObject mapping : evidence) {
                    if (!solverTerm.equals(string(mapping, "solverTerm"))
                            || !"Int".equals(string(mapping, "solverSort"))
                            || !"EMITTER_ACTUAL_TERM".equals(string(mapping,
                            "authority"))) {
                        gaps.add("BOOLEAN_CASE_TERM_MISMATCH:" + port.id);
                        break;
                    }
                }
            }
            BooleanInput input = new BooleanInput(port, solverTerm, "Int",
                    evidence);
            domainInputs.add(input);
            if (upstreamSupplied.contains(port.id)) {
                suppliedBoolean++;
                continue;
            }
            roots.add(input);
        }
        Collections.sort(roots, Comparator.comparing(value -> value.port.id));
        Collections.sort(domainInputs, Comparator.comparing(
                value -> value.port.id));
        return new Discovery(roots, domainInputs, staticBoolean,
                usedBoolean, suppliedBoolean);
    }

    private static Set<String> suppliedInputs(JsonObject relationships,
                                              PortCatalog ports,
                                              List<String> gaps) {
        Set<String> result = new LinkedHashSet<>();
        JsonArray rows = array(relationships, "relationships");
        if (integer(relationships, "candidateCount", -1) != rows.size()) {
            gaps.add("RELATIONSHIP_CANDIDATE_COUNT_MISMATCH");
        }
        for (int index = 0; index < rows.size(); index++) {
            JsonElement element = rows.get(index);
            if (!element.isJsonObject()) {
                gaps.add("NON_OBJECT_RELATIONSHIP_CANDIDATE:" + index);
                continue;
            }
            JsonObject roles = object(element.getAsJsonObject(), "roles");
            String left = string(roles, "left");
            String right = string(roles, "right");
            if (ports.isInput(left) && ports.isOutput(right)) {
                result.add(left);
            }
            if (ports.isInput(right) && ports.isOutput(left)) {
                result.add(right);
            }
        }
        return result;
    }

    private static String valuationQuery(String base,
                                         List<BooleanInput> inputs,
                                         boolean[] values) {
        StringBuilder query = new StringBuilder(base);
        for (int index = 0; index < inputs.size(); index++) {
            query.append("(assert ")
                    .append(inputs.get(index).literal(values[index]))
                    .append(")").append(System.lineSeparator());
        }
        return query.append("(check-sat)")
                .append(System.lineSeparator()).toString();
    }

    private static String appendBooleanDomain(String base,
                                              List<BooleanInput> inputs) {
        StringBuilder result = new StringBuilder(base);
        for (BooleanInput input : inputs) {
            result.append("(assert ").append(input.domainFormula())
                    .append(")").append(System.lineSeparator());
        }
        return result.toString();
    }

    private static JsonArray domainAssertionCatalog(
            List<BooleanInput> inputs) {
        JsonArray result = new JsonArray();
        for (BooleanInput input : inputs) {
            JsonObject row = new JsonObject();
            row.addProperty("portId", input.port.id);
            row.addProperty("solverTerm", input.solverTerm);
            row.addProperty("solverSort", input.solverSort);
            row.addProperty("formula", input.domainFormula());
            row.addProperty("authority", "STATIC_JAVA_BOOLEAN_TYPE");
            result.add(row);
        }
        return result;
    }

    private static boolean[] valuation(int ordinal, int width) {
        boolean[] result = new boolean[width];
        for (int index = 0; index < width; index++) {
            int shift = width - index - 1;
            result[index] = ((ordinal >>> shift) & 1) != 0;
        }
        return result;
    }

    private static JsonArray inputCatalog(List<BooleanInput> inputs) {
        JsonArray result = new JsonArray();
        for (int index = 0; index < inputs.size(); index++) {
            JsonObject row = inputs.get(index).toJson();
            row.addProperty("ordinal", index);
            result.add(row);
        }
        return result;
    }

    private static Extraction incomplete(JsonObject report,
                                         List<String> gaps,
                                         String status) {
        report.add("truthTable", new JsonArray());
        report.add("discoveryGaps", GSON.toJsonTree(gaps));
        report.addProperty("solverInvocationCount", 0);
        report.addProperty("truthTableComplete", false);
        report.addProperty("exactFiniteProjection", false);
        report.addProperty("complete", false);
        report.addProperty("status", status);
        return new Extraction(report);
    }

    interface Solver {
        SolverResult check(String smt) throws IOException,
                InterruptedException;
    }

    static final class SolverResult {
        final String status;
        final String output;

        SolverResult(String status, String output) {
            this.status = firstNonBlank(status, "unknown");
            this.output = firstNonBlank(output);
        }
    }

    static final class Z3Solver implements Solver {
        private final Path executable;
        private final long timeoutMillis;
        private final String version;
        private final JsonObject artifact;

        Z3Solver(String executable, long timeoutMillis)
                throws IOException, InterruptedException {
            this.timeoutMillis = Math.max(1L, timeoutMillis);
            this.executable = resolveExecutable(firstNonBlank(executable,
                    "z3"));
            this.version = validateVersion(this.executable,
                    this.timeoutMillis);
            this.artifact = BooleanReachConditionExtractor.artifact(
                    this.executable);
            this.artifact.addProperty("version", version);
            this.artifact.addProperty("identityAuthority",
                    "RESOLVED_REGULAR_FILE_SHA256_PLUS_Z3_VERSION_V1");
        }

        JsonObject artifact() {
            return artifact.deepCopy();
        }

        @Override
        public SolverResult check(String smt) throws IOException,
                InterruptedException {
            Path directory = Files.createTempDirectory(
                    "graphchecker-reach-z3-");
            Path query = directory.resolve("query.smt2");
            Path stdout = directory.resolve("stdout.txt");
            Path stderr = directory.resolve("stderr.txt");
            try {
                Files.write(query, smt.getBytes(StandardCharsets.UTF_8));
                Process process = new ProcessBuilder(executable.toString(),
                        "-smt2", query.toString())
                        .redirectOutput(stdout.toFile())
                        .redirectError(stderr.toFile()).start();
                boolean finished = process.waitFor(timeoutMillis,
                        TimeUnit.MILLISECONDS);
                if (!finished) {
                    process.destroyForcibly();
                    process.waitFor();
                    return new SolverResult("timeout", "solver timeout");
                }
                String out = Files.isRegularFile(stdout)
                        ? readText(stdout) : "";
                String err = Files.isRegularFile(stderr)
                        ? readText(stderr) : "";
                String status = process.exitValue() == 0
                        ? solverStatus(out) : "error";
                return new SolverResult(status, combinedOutput(out, err));
            } finally {
                Files.deleteIfExists(query);
                Files.deleteIfExists(stdout);
                Files.deleteIfExists(stderr);
                Files.deleteIfExists(directory);
            }
        }

        private static Path resolveExecutable(String requested)
                throws IOException {
            Path direct = Paths.get(requested);
            if (direct.isAbsolute() || requested.contains(File.separator)) {
                return regularExecutable(direct);
            }
            String path = firstNonBlank(System.getenv("PATH"));
            for (String entry : path.split(Pattern.quote(
                    File.pathSeparator), -1)) {
                Path directory = entry.isEmpty()
                        ? Paths.get("").toAbsolutePath() : Paths.get(entry);
                Path candidate = directory.resolve(requested);
                if (Files.isRegularFile(candidate)
                        && Files.isExecutable(candidate)) {
                    return candidate.toRealPath();
                }
            }
            throw new IOException("Z3 executable not found on PATH: "
                    + requested);
        }

        private static Path regularExecutable(Path candidate)
                throws IOException {
            Path resolved = candidate.toAbsolutePath().normalize()
                    .toRealPath();
            if (!Files.isRegularFile(resolved)
                    || !Files.isExecutable(resolved)) {
                throw new IOException("Z3 executable is not an executable "
                        + "regular file: " + resolved);
            }
            return resolved;
        }

        private static String validateVersion(Path executable,
                                              long timeoutMillis)
                throws IOException, InterruptedException {
            Path directory = Files.createTempDirectory(
                    "graphchecker-reach-z3-version-");
            Path output = directory.resolve("version.txt");
            try {
                Process process = new ProcessBuilder(executable.toString(),
                        "-version").redirectErrorStream(true)
                        .redirectOutput(output.toFile()).start();
                boolean finished = process.waitFor(timeoutMillis,
                        TimeUnit.MILLISECONDS);
                if (!finished) {
                    process.destroyForcibly();
                    process.waitFor();
                    throw new IOException("Z3 -version timed out");
                }
                String text = Files.isRegularFile(output)
                        ? readText(output).trim() : "";
                if (process.exitValue() != 0 || !text.contains("Z3")) {
                    throw new IOException("Invalid Z3 executable identity: "
                            + text);
                }
                return text;
            } finally {
                Files.deleteIfExists(output);
                Files.deleteIfExists(directory);
            }
        }

        private static String combinedOutput(String stdout, String stderr) {
            String out = firstNonBlank(stdout);
            String err = firstNonBlank(stderr);
            if (out.isEmpty()) return err;
            if (err.isEmpty()) return out;
            return out + System.lineSeparator() + err;
        }
    }

    static String solverStatus(String output) {
        for (String line : firstNonBlank(output).split("\\r?\\n")) {
            String value = line.trim();
            if (value.isEmpty()) continue;
            return "sat".equals(value) || "unsat".equals(value)
                    || "unknown".equals(value) ? value : "unknown";
        }
        return "unknown";
    }

    static final class Extraction {
        final JsonObject report;

        Extraction(JsonObject report) {
            this.report = report;
        }
    }

    private static final class Discovery {
        private final List<BooleanInput> rootInputs;
        private final List<BooleanInput> booleanDomainInputs;
        private final int staticBooleanInputCount;
        private final int usedBooleanInputCount;
        private final int upstreamSuppliedBooleanInputCount;

        private Discovery(List<BooleanInput> rootInputs,
                          List<BooleanInput> booleanDomainInputs,
                          int staticBooleanInputCount,
                          int usedBooleanInputCount,
                          int upstreamSuppliedBooleanInputCount) {
            this.rootInputs = rootInputs;
            this.booleanDomainInputs = booleanDomainInputs;
            this.staticBooleanInputCount = staticBooleanInputCount;
            this.usedBooleanInputCount = usedBooleanInputCount;
            this.upstreamSuppliedBooleanInputCount =
                    upstreamSuppliedBooleanInputCount;
        }
    }

    private static final class BooleanInput {
        private final PortInfo port;
        private final String solverTerm;
        private final String solverSort;
        private final List<JsonObject> caseEvidence;

        private BooleanInput(PortInfo port, String solverTerm,
                             String solverSort,
                             List<JsonObject> caseEvidence) {
            this.port = port;
            this.solverTerm = solverTerm;
            this.solverSort = solverSort;
            this.caseEvidence = caseEvidence == null
                    ? Collections.<JsonObject>emptyList()
                    : new ArrayList<>(caseEvidence);
        }

        private String literal(boolean value) {
            if ("Bool".equals(solverSort)) {
                return value ? solverTerm : "(not " + solverTerm + ")";
            }
            return "(= " + solverTerm + " " + (value ? "1" : "0") + ")";
        }

        private String domainFormula() {
            if ("Bool".equals(solverSort)) return "true";
            return "(or (= " + solverTerm + " 0) (= " + solverTerm
                    + " 1))";
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("portId", port.id);
            result.addProperty("regionId", port.regionId);
            result.addProperty("cell", port.cell);
            result.addProperty("javaType", port.javaType);
            result.addProperty("javaTypeDescriptor", port.descriptor);
            result.addProperty("solverTerm", solverTerm);
            result.addProperty("solverSort", solverSort);
            result.addProperty("booleanEncoding", "Bool".equals(solverSort)
                    ? "SMT_BOOL" : "JAVA_BOOLEAN_AS_INT_0_1");
            result.addProperty("root", true);
            result.addProperty("upstreamSupplied", false);
            JsonArray cases = new JsonArray();
            Set<String> seen = new LinkedHashSet<>();
            for (JsonObject evidence : caseEvidence) {
                String key = string(evidence, "regionId") + "\u0000"
                        + string(evidence, "caseId");
                if (!seen.add(key)) continue;
                JsonObject row = new JsonObject();
                row.addProperty("regionId", string(evidence, "regionId"));
                row.addProperty("caseId", string(evidence, "caseId"));
                row.addProperty("sourceSummaryId", string(evidence,
                        "sourceSummaryId"));
                row.addProperty("sourceActivationId", string(evidence,
                        "sourceActivationId"));
                row.addProperty("rawEngineSymbol", string(evidence,
                        "rawEngineSymbol"));
                cases.add(row);
            }
            result.add("caseProjectionEvidence", cases);
            result.addProperty("authority",
                    "STATIC_BOOLEAN_PORT_PLUS_FINAL_SMT_CANONICAL_BINDING");
            return result;
        }
    }

    private static final class Valuation {
        private final int ordinal;
        private final boolean[] values;
        private final String status;

        private Valuation(int ordinal, boolean[] values, String status) {
            this.ordinal = ordinal;
            this.values = values.clone();
            this.status = firstNonBlank(status, "unknown");
        }

        private JsonObject toJson(List<BooleanInput> inputs) {
            JsonObject result = new JsonObject();
            result.addProperty("ordinal", ordinal);
            StringBuilder key = new StringBuilder();
            JsonArray assignments = new JsonArray();
            for (int index = 0; index < inputs.size(); index++) {
                key.append(values[index] ? '1' : '0');
                JsonObject assignment = new JsonObject();
                assignment.addProperty("portId", inputs.get(index).port.id);
                assignment.addProperty("solverTerm",
                        inputs.get(index).solverTerm);
                assignment.addProperty("value", values[index]);
                assignment.addProperty("solverLiteral",
                        inputs.get(index).literal(values[index]));
                assignments.add(assignment);
            }
            result.addProperty("valuationKey", key.toString());
            result.add("assignments", assignments);
            result.addProperty("solverStatus", status);
            return result;
        }
    }

    private static final class Dnf {
        private final String formula;
        private final JsonArray clauses;
        private final int satisfyingCount;
        private final int valuationCount;

        private Dnf(String formula, JsonArray clauses, int satisfyingCount,
                    int valuationCount) {
            this.formula = formula;
            this.clauses = clauses;
            this.satisfyingCount = satisfyingCount;
            this.valuationCount = valuationCount;
        }

        private static Dnf from(List<BooleanInput> inputs,
                                List<Valuation> valuations) {
            List<String> terms = new ArrayList<>();
            JsonArray clauses = new JsonArray();
            for (Valuation valuation : valuations) {
                if (!"sat".equals(valuation.status)) continue;
                List<String> literals = new ArrayList<>();
                JsonObject clause = new JsonObject();
                clause.addProperty("valuationOrdinal", valuation.ordinal);
                JsonArray members = new JsonArray();
                for (int index = 0; index < inputs.size(); index++) {
                    String literal = inputs.get(index).literal(
                            valuation.values[index]);
                    literals.add(literal);
                    JsonObject member = new JsonObject();
                    member.addProperty("portId", inputs.get(index).port.id);
                    member.addProperty("solverTerm",
                            inputs.get(index).solverTerm);
                    member.addProperty("value", valuation.values[index]);
                    member.addProperty("formula", literal);
                    members.add(member);
                }
                String conjunction = join("and", literals, "true");
                clause.add("literals", members);
                clause.addProperty("formula", conjunction);
                clauses.add(clause);
                terms.add(conjunction);
            }
            String formula;
            if (terms.isEmpty()) {
                formula = "false";
            } else if (terms.size() == valuations.size()) {
                formula = "true";
            } else {
                formula = join("or", terms, "false");
            }
            return new Dnf(formula, clauses, terms.size(),
                    valuations.size());
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 1);
            result.addProperty("kind", "CANONICAL_DNF");
            result.addProperty("formula", formula);
            result.addProperty("satisfyingValuationCount", satisfyingCount);
            result.addProperty("valuationCount", valuationCount);
            result.addProperty("constantFolded",
                    "true".equals(formula) || "false".equals(formula));
            result.add("clauses", clauses.deepCopy());
            result.addProperty("clauseCount", clauses.size());
            result.addProperty("authority",
                    "EXACT_SAT_ROWS_FROM_EXHAUSTIVE_BOOLEAN_TRUTH_TABLE");
            return result;
        }
    }

    private static String join(String operator, List<String> terms,
                               String empty) {
        if (terms.isEmpty()) return empty;
        if (terms.size() == 1) return terms.get(0);
        StringBuilder result = new StringBuilder("(").append(operator);
        for (String term : terms) result.append(' ').append(term);
        return result.append(')').toString();
    }

    private static final class PortCatalog {
        private final Map<String, PortInfo> inputs = new LinkedHashMap<>();
        private final Map<String, PortInfo> outputs = new LinkedHashMap<>();

        private static PortCatalog from(List<JsonObject> regions,
                                        List<String> gaps) {
            PortCatalog result = new PortCatalog();
            for (JsonObject region : safe(regions)) {
                String regionId = string(region, "regionId");
                for (JsonElement element : array(region,
                        "symbolicInputs")) {
                    if (element.isJsonObject()) result.add(regionId,
                            element.getAsJsonObject(), true, gaps);
                }
                for (JsonElement element : array(region, "outputs")) {
                    if (element.isJsonObject()) result.add(regionId,
                            element.getAsJsonObject(), false, gaps);
                }
            }
            return result;
        }

        private void add(String regionId, JsonObject row, boolean input,
                         List<String> gaps) {
            String id = firstNonBlank(string(row, "portId"),
                    string(row, "symbol"));
            if (id.isEmpty()) {
                gaps.add("STATIC_PORT_WITHOUT_ID:" + regionId);
                return;
            }
            String cell = string(row, "cell");
            String javaType = firstNonBlank(string(row, "javaType"),
                    string(row, "declaredType"), cellJavaType(cell));
            PortInfo value = new PortInfo(id, regionId, cell, javaType,
                    input);
            Map<String, PortInfo> own = input ? inputs : outputs;
            Map<String, PortInfo> other = input ? outputs : inputs;
            PortInfo previous = own.put(id, value);
            if (previous != null && !previous.sameSchema(value)) {
                gaps.add("STATIC_PORT_SCHEMA_CONFLICT:" + id);
            }
            if (other.containsKey(id)) {
                gaps.add("STATIC_PORT_DIRECTION_CONFLICT:" + id);
            }
        }

        private boolean isInput(String port) {
            return inputs.containsKey(port);
        }

        private boolean isOutput(String port) {
            return outputs.containsKey(port);
        }

        private List<PortInfo> sortedInputs() {
            List<PortInfo> result = new ArrayList<>(inputs.values());
            Collections.sort(result, Comparator.comparing(value -> value.id));
            return result;
        }
    }

    private static final class PortInfo {
        private final String id;
        private final String regionId;
        private final String cell;
        private final String javaType;
        private final String descriptor;
        private final boolean input;
        private final boolean javaBoolean;

        private PortInfo(String id, String regionId, String cell,
                         String javaType, boolean input) {
            this.id = firstNonBlank(id);
            this.regionId = firstNonBlank(regionId);
            this.cell = firstNonBlank(cell);
            this.javaType = firstNonBlank(javaType);
            this.descriptor = javaTypeDescriptor(javaType);
            this.input = input;
            this.javaBoolean = "Z".equals(descriptor)
                    || "Ljava/lang/Boolean;".equals(descriptor);
        }

        private boolean sameSchema(PortInfo other) {
            return other != null && id.equals(other.id)
                    && regionId.equals(other.regionId)
                    && cell.equals(other.cell)
                    && descriptor.equals(other.descriptor)
                    && input == other.input;
        }
    }

    private static final class Arguments {
        private Path smt;
        private Path manifest;
        private Path regions;
        private Path relationships;
        private Path output;
        private String z3 = "z3";
        private long timeoutMillis = 20_000L;
        private int maxInputs = 12;
        private int maxValuations = 4096;
        private Mode mode = Mode.FINAL_REPORT;

        private static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; argv != null && index < argv.length; index++) {
                String argument = argv[index];
                if (!argument.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException(
                            "Expected --key value, got: " + argument);
                }
                values.put(argument.substring(2), argv[++index]);
            }
            Arguments result = new Arguments();
            result.smt = required(values, "smt");
            result.manifest = required(values, "manifest");
            result.regions = required(values, "regions");
            if (values.containsKey("relationships")) {
                result.relationships = Paths.get(values.get("relationships"));
            }
            result.output = values.containsKey("output")
                    ? Paths.get(values.get("output"))
                    : sibling(result.manifest,
                    "boolean_reach_condition.json");
            result.z3 = firstNonBlank(values.get("z3"), "z3");
            result.timeoutMillis = positiveLong(values.get("timeout-ms"),
                    20_000L);
            result.maxInputs = positiveInt(values.get("max-inputs"), 12);
            result.maxValuations = positiveInt(values.get(
                    "max-valuations"), 4096);
            result.mode = Mode.parse(values.get("mode"));
            return result;
        }

        private static Path required(Map<String, String> values,
                                     String key) {
            String value = values.get(key);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return Paths.get(value);
        }
    }

    enum Mode {
        FINAL_REPORT,
        BOOTSTRAP_REPLAY_MODEL;

        private static Mode parse(String value) {
            String normalized = firstNonBlank(value, FINAL_REPORT.name())
                    .toUpperCase(Locale.ROOT).replace('-', '_');
            try {
                return Mode.valueOf(normalized);
            } catch (IllegalArgumentException exception) {
                throw new IllegalArgumentException(
                        "Unsupported reach extraction mode: " + value,
                        exception);
            }
        }
    }

    static JsonObject artifact(Path path) throws IOException {
        byte[] bytes = Files.readAllBytes(path);
        JsonObject result = new JsonObject();
        result.addProperty("path", path.toAbsolutePath().normalize()
                .toString());
        result.addProperty("sha256", sha256(bytes));
        result.addProperty("sizeBytes", bytes.length);
        return result;
    }

    /**
     * Rejects cross-wired CLI artifacts before any solver process starts.
     * The composer manifest is the trust root: it fingerprints the exact SMT,
     * static-region ledger, and relationship-candidate bytes.  The candidate
     * catalog then independently binds itself back to the same composition
     * and SMT digest.
     */
    static void validateArtifactBindings(Path smtPath, Path regionsPath,
                                         Path relationshipsPath,
                                         JsonObject manifest,
                                         JsonObject relationships)
            throws IOException {
        if (!"COMPOSER_EXACT_CLI_INPUT_AND_OUTPUT_SHA256_V1".equals(
                string(manifest, "artifactBindingAuthority"))) {
            throw new IOException("Composition manifest has no exact "
                    + "artifact binding authority");
        }
        JsonObject actualSmt = artifact(smtPath);
        JsonObject actualRegions = artifact(regionsPath);
        JsonObject actualRelationships = artifact(relationshipsPath);
        requireExactArtifact("composed SMT", object(manifest,
                "composedSmtArtifact"), actualSmt);
        requireExactArtifact("static regions", object(manifest,
                "staticRegionsArtifact"), actualRegions);
        requireExactArtifact("relationship candidates", object(manifest,
                "relationshipCandidatesArtifact"), actualRelationships);

        String bindingId = string(manifest, "compositionBindingId");
        if (bindingId.isEmpty() || !bindingId.matches("[0-9a-f]{64}")
                || !bindingId.equals(string(relationships,
                "compositionBindingId"))) {
            throw new IOException("Composition binding id mismatch");
        }
        if (!bindingId.equals(compositionBindingId(manifest))) {
            throw new IOException("Composition binding id is not derived "
                    + "from its exact fatal identity and artifacts");
        }
        if (!"COMPOSER_EXACT_CLI_INPUT_AND_OUTPUT_SHA256_V1".equals(
                string(relationships, "artifactBindingAuthority"))) {
            throw new IOException("Relationship catalog has no exact "
                    + "artifact binding authority");
        }
        requireExactArtifact("relationship base SMT", object(relationships,
                "composedSmtArtifact"), actualSmt);
        requireExactArtifact("relationship static regions",
                object(relationships, "staticRegionsArtifact"),
                actualRegions);
        if (!object(manifest, "fatalQueriesArtifact").equals(
                object(relationships, "fatalQueriesArtifact"))
                || !object(manifest, "symbolicMergePlanArtifact").equals(
                object(relationships, "symbolicMergePlanArtifact"))
                || !object(manifest, "runtimeBindingCatalogArtifact").equals(
                object(relationships, "runtimeBindingCatalogArtifact"))
                || !object(manifest,
                "configuredTransportBindingsArtifact").equals(object(
                relationships, "configuredTransportBindingsArtifact"))
                || !array(manifest, "summaryInputArtifacts").equals(
                array(relationships, "summaryInputArtifacts"))) {
            throw new IOException("Composition source artifact binding "
                    + "mismatch");
        }
        String actualSmtPath = string(actualSmt, "path");
        if (!actualSmtPath.equals(normalizedPath(string(relationships,
                "baseSmt")))
                || !string(actualSmt, "sha256").equals(
                string(relationships, "baseSmtSha256"))
                || longInteger(actualSmt, "sizeBytes", -1L)
                != longInteger(relationships, "baseSmtSizeBytes", -2L)) {
            throw new IOException("Relationship base SMT fingerprint "
                    + "mismatch");
        }
        for (String field : new String[]{"fatalRegion", "fatalActivation",
                "fatalRegionInstanceId", "fatalOccurrence",
                "fatalDesiredOutcome", "validatedSummaryId"}) {
            JsonElement left = manifest == null ? null : manifest.get(field);
            JsonElement right = relationships == null
                    ? null : relationships.get(field);
            if (left == null || right == null || !left.equals(right)) {
                throw new IOException("Fatal identity binding mismatch: "
                        + field);
            }
        }
    }

    private static void requireExactArtifact(String label,
                                             JsonObject expected,
                                             JsonObject actual)
            throws IOException {
        if (expected.size() == 0
                || !string(actual, "path").equals(normalizedPath(
                string(expected, "path")))
                || !string(actual, "sha256").equals(string(expected,
                "sha256"))
                || longInteger(actual, "sizeBytes", -1L)
                != longInteger(expected, "sizeBytes", -2L)) {
            throw new IOException(label + " artifact fingerprint mismatch");
        }
    }

    private static String normalizedPath(String value) {
        if (firstNonBlank(value).isEmpty()) return "";
        return Paths.get(value).toAbsolutePath().normalize().toString();
    }

    static String compositionBindingId(JsonObject manifest) {
        JsonObject material = new JsonObject();
        material.addProperty("schemaVersion", 1);
        for (String field : new String[]{"fatalRegion", "fatalActivation",
                "fatalRegionInstanceId"}) {
            material.addProperty(field, string(manifest, field));
        }
        for (String field : new String[]{"fatalOccurrence",
                "fatalDesiredOutcome"}) {
            JsonElement value = manifest == null ? null : manifest.get(field);
            if (value == null) return "";
            material.add(field, value.deepCopy());
        }
        material.addProperty("validatedSummaryId",
                string(manifest, "validatedSummaryId"));
        material.add("composedSmtArtifact", object(manifest,
                "composedSmtArtifact").deepCopy());
        material.add("staticRegionsArtifact", object(manifest,
                "staticRegionsArtifact").deepCopy());
        material.add("fatalQueriesArtifact", object(manifest,
                "fatalQueriesArtifact").deepCopy());
        material.add("symbolicMergePlanArtifact", object(manifest,
                "symbolicMergePlanArtifact").deepCopy());
        material.add("runtimeBindingCatalogArtifact", object(manifest,
                "runtimeBindingCatalogArtifact").deepCopy());
        if (manifest != null
                && manifest.has("configuredTransportBindingsArtifact")) {
            material.add("configuredTransportBindingsArtifact",
                    object(manifest,
                            "configuredTransportBindingsArtifact")
                            .deepCopy());
        }
        material.add("summaryInputArtifacts", array(manifest,
                "summaryInputArtifacts").deepCopy());
        return sha256(BINDING_GSON.toJson(material));
    }

    private static Path referencedPath(JsonObject source, String field,
                                       Path sourcePath) throws IOException {
        String value = string(source, field);
        if (value.isEmpty()) {
            throw new IOException("Missing " + field + " in " + sourcePath);
        }
        Path result = Paths.get(value);
        if (!result.isAbsolute()) {
            Path parent = sourcePath.toAbsolutePath().getParent();
            result = parent == null ? result : parent.resolve(result);
        }
        return result.normalize();
    }

    private static String readText(Path path) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException("Input not found: " + path);
        }
        return new String(Files.readAllBytes(path), StandardCharsets.UTF_8);
    }

    private static JsonObject readJson(Path path) throws IOException {
        JsonElement value = JsonParser.parseString(readText(path));
        if (!value.isJsonObject()) {
            throw new IOException("Expected JSON object: " + path);
        }
        return value.getAsJsonObject();
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        List<JsonObject> result = new ArrayList<>();
        int lineNumber = 0;
        for (String line : Files.readAllLines(path, StandardCharsets.UTF_8)) {
            lineNumber++;
            if (line.trim().isEmpty()) continue;
            JsonElement value = JsonParser.parseString(line);
            if (!value.isJsonObject()) {
                throw new IOException("Expected JSON object at " + path
                        + ":" + lineNumber);
            }
            result.add(value.getAsJsonObject());
        }
        return result;
    }

    private static void write(Path path, String value) throws IOException {
        Path parent = path.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                path.getFileName().toString(), ".tmp");
        try {
            Files.write(temporary, value.getBytes(StandardCharsets.UTF_8));
            try {
                Files.move(temporary, path,
                        StandardCopyOption.REPLACE_EXISTING,
                        StandardCopyOption.ATOMIC_MOVE);
            } catch (java.nio.file.AtomicMoveNotSupportedException ignored) {
                Files.move(temporary, path,
                        StandardCopyOption.REPLACE_EXISTING);
            }
        } finally {
            Files.deleteIfExists(temporary);
        }
    }

    private static String cellJavaType(String cell) {
        String value = firstNonBlank(cell).trim();
        Matcher parameter = PARAMETER_CELL.matcher(value);
        if (parameter.find()) return parameter.group(1).trim();
        Matcher field = FIELD_CELL.matcher(value);
        if (field.matches()) return field.group(1).trim();
        Matcher returned = RETURN_CELL.matcher(value);
        return returned.matches() ? returned.group(1).trim() : "";
    }

    private static String javaTypeDescriptor(String type) {
        String value = firstNonBlank(type).trim().replace('.', '/');
        if (value.isEmpty()) return "";
        if (value.startsWith("[")) return value;
        if ("boolean".equals(value)) return "Z";
        if (value.length() == 1 && "ZBCSIJFDV".contains(value)) return value;
        if (value.startsWith("L") && value.endsWith(";")) return value;
        return "L" + value + ";";
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

    private static long positiveLong(String value, long fallback) {
        try {
            return Math.max(1L, Long.parseLong(firstNonBlank(value,
                    String.valueOf(fallback))));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int positiveInt(String value, int fallback) {
        try {
            return Math.max(1, Integer.parseInt(firstNonBlank(value,
                    String.valueOf(fallback))));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static Path sibling(Path path, String name) {
        Path parent = path.toAbsolutePath().getParent();
        return parent == null ? Paths.get(name) : parent.resolve(name);
    }

    private static String sha256(String value) {
        return sha256((value == null ? "" : value).getBytes(
                StandardCharsets.UTF_8));
    }

    private static String sha256(byte[] value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(value == null ? new byte[0] : value);
            StringBuilder result = new StringBuilder(bytes.length * 2);
            for (byte current : bytes) {
                result.append(String.format(Locale.ROOT, "%02x",
                        current & 0xff));
            }
            return result.toString();
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException(impossible);
        }
    }

    private static JsonArray array(JsonObject object, String key) {
        JsonElement value = object == null ? null : object.get(key);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static JsonObject object(JsonObject object, String key) {
        JsonElement value = object == null ? null : object.get(key);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static String string(JsonObject object, String key) {
        JsonElement value = object == null ? null : object.get(key);
        return value != null && value.isJsonPrimitive()
                ? value.getAsString() : "";
    }

    private static int integer(JsonObject object, String key,
                               int fallback) {
        try {
            JsonElement value = object == null ? null : object.get(key);
            return value != null && value.isJsonPrimitive()
                    ? value.getAsInt() : fallback;
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longInteger(JsonObject object, String key,
                                    long fallback) {
        try {
            JsonElement value = object == null ? null : object.get(key);
            return value != null && value.isJsonPrimitive()
                    ? value.getAsLong() : fallback;
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static boolean bool(JsonObject object, String key,
                                boolean fallback) {
        try {
            JsonElement value = object == null ? null : object.get(key);
            return value != null && value.isJsonPrimitive()
                    ? value.getAsBoolean() : fallback;
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

    private static <T> List<T> safe(List<T> values) {
        return values == null ? Collections.<T>emptyList() : values;
    }
}
