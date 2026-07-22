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
 * Projects a structurally complete candidate bug-path SMT formula onto its
 * finite Boolean root-input domain.
 *
 * <p>The extractor never accepts caller-authored reachability formulas.  It
 * discovers Java Boolean input ports from the static region IR, joins them to
 * the exact canonical terms already emitted by {@link ConcolicSmtComposer},
 * removes inputs supplied by composed producer-output relationships, and asks
 * Z3 about every remaining Boolean valuation.  The resulting truth table and
 * canonical DNF are therefore derived candidate artifacts of the composed
 * SMT. This class never promotes them to a trusted final result.</p>
 */
public final class BooleanReachConditionExtractor {
    private static final String NULLABLE_STRING_ENCODING_AUTHORITY =
            "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1";
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();
    private static final Pattern FIELD_CELL = Pattern.compile(
            "^<[^:]+:\\s+([^()<>\\s]+)\\s+[^()<>\\s]+>(?:#.*)?$");
    private static final Pattern RETURN_CELL = Pattern.compile(
            "^<[^:]+:\\s+([^<>\\s]+)\\s+[^<>\\s(]+\\([^>]*\\)>"
                    + "\\.return(?:#.*)?$");
    private static final Pattern PARAMETER_CELL = Pattern.compile(
            ">\\.param[0-9]+:([^#]+)(?:#.*)?$");
    private static final Pattern SAFE_SMT_ATOM = Pattern.compile(
            "[A-Za-z_~!@$%^&*+=<>.?/][A-Za-z0-9_~!@$%^&*+\\-=<>.?/]*");
    private BooleanReachConditionExtractor() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        JsonObject manifest = readJson(arguments.manifest);
        Path relationshipsPath = arguments.relationships;
        String smt = readText(arguments.smt);
        JsonObject relationships = readJson(relationshipsPath);
        List<JsonObject> regions = readJsonl(arguments.regions);
        validateArtifactBindings(arguments.smt, arguments.regions,
                relationshipsPath, manifest);
        Z3Solver solver = new Z3Solver(arguments.z3,
                arguments.timeoutMillis);
        Extraction extraction = extract(smt, manifest, regions,
                relationships, solver,
                arguments.maxInputs, arguments.maxValuations);
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
        report.addProperty("extractionMode", "CANDIDATE_MODEL");
        report.addProperty("candidateOnly", true);
        report.addProperty("candidateModelAvailable", false);
        report.addProperty("reportableFinalReachCondition", false);
        report.addProperty("fatalReplayValidated",
                bool(manifest, "fatalReplayValidated", false));
        report.addProperty("fatalReplaySkippedBecauseUnreachable", false);

        List<String> gaps = new ArrayList<>();
        validateCompositionAuthority(manifest, relationships, gaps);
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
        report.addProperty("staticNonBooleanScalarInputCount",
                discovery.staticNonBooleanScalarInputCount);
        report.addProperty("usedNonBooleanScalarInputCount",
                discovery.usedNonBooleanScalarInputCount);
        report.addProperty("upstreamSuppliedNonBooleanScalarInputCount",
                discovery.upstreamSuppliedNonBooleanScalarInputCount);
        report.addProperty("existentialNonBooleanRootInputCount",
                discovery.existentialNonBooleanRootInputs.size());
        report.add("existentialNonBooleanRootInputs",
                scalarInputCatalog(
                        discovery.existentialNonBooleanRootInputs));
        report.addProperty("nullableJavaStringModeled",
                discovery.nullableJavaStringInputCount > 0);
        report.addProperty("nullableJavaStringInputCount",
                discovery.nullableJavaStringInputCount);
        if (discovery.nullableJavaStringInputCount > 0) {
            report.addProperty("nullableStringEncodingAuthority",
                    NULLABLE_STRING_ENCODING_AUTHORITY);
        }
        report.addProperty(
                "existentialNonBooleanRootInputDiscoveryAuthority",
                "STATIC_JAVA_SCALAR_PORT_TYPE_PLUS_COMPOSER_CANONICAL_"
                        + "TERM_AND_RUNTIME_RELATIONSHIP_DIRECTION_V1");
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

        String base = SmtLibQueries.stripSolverCommands(
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
        boolean truthTableDecided = solverErrors == 0
                && satisfying + unsatisfying == valuationCount;
        report.addProperty("candidateModelAvailable",
                truthTableDecided && satisfying > 0);
        report.addProperty("reachabilityStatus", !truthTableDecided
                ? "UNKNOWN" : satisfying > 0
                ? "REACHABLE" : "UNREACHABLE");
        report.addProperty("fatalReplaySkippedBecauseUnreachable", false);
        report.add("discoveryGaps", new JsonArray());
        report.addProperty("complete", complete);
        String status = "BOOLEAN_REACH_CONDITION_WITH_SOLVER_GAPS";
        if (complete) {
            status = satisfying > 0
                    ? "COMPLETE_CANDIDATE_MODEL"
                    : "COMPLETE_CANDIDATE_UNREACHABLE";
        }
        report.addProperty("status", status);
        return new Extraction(report);
    }

    private static void validateCompositionAuthority(
            JsonObject manifest, JsonObject relationships,
            List<String> gaps) {
        boolean commonManifest = manifest != null
                && integer(manifest, "schemaVersion", -1) == 1
                && "CONCOLIC_COMPOSED_SMT".equals(string(manifest, "kind"))
                && bool(manifest, "caseProjectionCatalogComplete", false);
        boolean commonRelationships = relationships != null
                && integer(relationships, "schemaVersion", -1) == 1
                && "SYMBOLIC_RELATIONSHIP_CANDIDATES".equals(string(
                relationships, "kind"));
        if (!commonManifest
                || !"CANDIDATE".equals(string(manifest,
                "compositionStage"))
                || !bool(manifest, "structurallyComplete", false)
                || bool(manifest, "fatalReplayValidated", true)
                || bool(manifest, "complete", true)
                || !bool(manifest, "eligibleForCandidateModel", false)
                || bool(manifest,
                "eligibleToReportAutomaticRelationship", true)) {
            gaps.add("COMPOSITION_MANIFEST_NOT_CANDIDATE_MODEL_ELIGIBLE");
        }
        if (!commonRelationships
                || bool(relationships,
                "eligibleForAutomaticVerification", true)) {
            gaps.add("RELATIONSHIP_CATALOG_NOT_CANDIDATE_MODEL_ELIGIBLE");
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
                evidence.addProperty("selectorSolverSymbol", string(pathCase,
                        "selectorSolverSymbol"));
                evidence.add("caseDynamicFieldBindings", array(pathCase,
                        "dynamicFieldBindings").deepCopy());
                values.add(evidence);
            }
        }

        Set<String> upstreamSupplied = suppliedInputs(relationships, ports,
                gaps);
        List<BooleanInput> roots = new ArrayList<>();
        List<BooleanInput> domainInputs = new ArrayList<>();
        List<ScalarInput> scalarRoots = new ArrayList<>();
        int staticBoolean = 0;
        int usedBoolean = 0;
        int suppliedBoolean = 0;
        int staticScalar = 0;
        int usedScalar = 0;
        int suppliedScalar = 0;
        int nullableStrings = 0;
        for (PortInfo port : ports.sortedInputs()) {
            ScalarEncoding encoding = ScalarEncoding.of(port.descriptor);
            if (!port.javaBoolean && encoding == null) continue;
            if (port.javaBoolean) {
                staticBoolean++;
                encoding = ScalarEncoding.INT;
            } else {
                staticScalar++;
            }
            String solverTerm = encoding.solverTerm(port.id);
            String portTerm = "port__" + smtName(port.id);
            List<JsonObject> evidence = scalarEvidence(
                    mappingsByPort.get(port.id), encoding);
            String nullnessSolverTerm = encoding == ScalarEncoding.STRING
                    ? exactCanonicalStringNullnessTerm(evidence, port,
                    gaps) : "";
            boolean declared = canonicalScalarBindingDeclared(smt, portTerm,
                    solverTerm, nullnessSolverTerm, encoding);
            if (!declared && (evidence == null || evidence.isEmpty())) {
                continue;
            }
            if (port.javaBoolean) usedBoolean++;
            else usedScalar++;
            if (!declared) {
                gaps.add((port.javaBoolean
                        ? "BOOLEAN_PORT_WITHOUT_CANONICAL_SMT_BINDING:"
                        : "NON_BOOLEAN_SCALAR_PORT_WITHOUT_CANONICAL_"
                        + "SMT_BINDING:") + port.id);
                continue;
            }
            if (!atMostOneMappingPerUsedCase(evidence)) {
                gaps.add((port.javaBoolean
                        ? "BOOLEAN_CASE_MAPPING_AMBIGUOUS:"
                        : "NON_BOOLEAN_SCALAR_CASE_MAPPING_AMBIGUOUS:")
                        + port.id);
            }
            if (evidence != null) {
                for (JsonObject mapping : evidence) {
                    boolean direct = solverTerm.equals(string(mapping,
                            "solverTerm"));
                    boolean bridged = !direct
                            && exactDynamicCanonicalBridge(smt, mapping,
                            port.id, solverTerm, nullnessSolverTerm,
                            encoding);
                    boolean stringNullnessMatches = encoding
                            != ScalarEncoding.STRING
                            || direct && nullnessSolverTerm.equals(string(
                            mapping, "nullnessSolverTerm"))
                            || !direct && nullnessSolverTerm.equals(string(
                            mapping, "canonicalNullnessSolverTerm"));
                    if ((!direct && !bridged)
                            || direct && hasDynamicBridgeMetadata(mapping)
                            || !stringNullnessMatches
                            || encoding == ScalarEncoding.STRING
                            && !NULLABLE_STRING_ENCODING_AUTHORITY.equals(
                            string(mapping,
                                    "nullableStringEncodingAuthority"))
                            || !encoding.solverSort.equals(string(mapping,
                            "solverSort"))
                            || !"EMITTER_ACTUAL_TERM".equals(string(mapping,
                            "authority"))) {
                        gaps.add((port.javaBoolean
                                ? "BOOLEAN_CASE_TERM_MISMATCH:"
                                : "NON_BOOLEAN_SCALAR_CASE_TERM_MISMATCH:")
                                + port.id);
                        break;
                    }
                }
            }
            if (port.javaBoolean) {
                BooleanInput input = new BooleanInput(port, solverTerm,
                        encoding.solverSort, evidence);
                domainInputs.add(input);
                if (upstreamSupplied.contains(port.id)) {
                    suppliedBoolean++;
                    continue;
                }
                roots.add(input);
            } else if (upstreamSupplied.contains(port.id)) {
                suppliedScalar++;
                continue;
            } else {
                scalarRoots.add(new ScalarInput(port, solverTerm,
                        nullnessSolverTerm, encoding, evidence));
                if (encoding == ScalarEncoding.STRING) nullableStrings++;
            }
        }
        Collections.sort(roots, Comparator.comparing(value -> value.port.id));
        Collections.sort(domainInputs, Comparator.comparing(
                value -> value.port.id));
        Collections.sort(scalarRoots, Comparator.comparing(
                value -> value.port.id));
        return new Discovery(roots, domainInputs, staticBoolean,
                usedBoolean, suppliedBoolean, scalarRoots, staticScalar,
                usedScalar, suppliedScalar, nullableStrings);
    }

    private static String exactCanonicalStringNullnessTerm(
            List<JsonObject> evidence, PortInfo port, List<String> gaps) {
        if (evidence == null || evidence.isEmpty()) return "";
        String selected = "";
        for (JsonObject mapping : evidence) {
            if (!NULLABLE_STRING_ENCODING_AUTHORITY.equals(string(mapping,
                    "nullableStringEncodingAuthority"))) {
                gaps.add("STRING_CASE_NULLNESS_AUTHORITY_MISSING:"
                        + port.id);
                return "";
            }
            String candidate = firstNonBlank(string(mapping,
                    "canonicalNullnessSolverTerm"), string(mapping,
                    "nullnessSolverTerm"));
            if (!safeSmtAtom(candidate)) {
                gaps.add("STRING_CASE_NULLNESS_TERM_MISSING:" + port.id);
                return "";
            }
            if (!selected.isEmpty() && !selected.equals(candidate)) {
                gaps.add("STRING_CASE_NULLNESS_TERM_CONFLICT:" + port.id);
                return "";
            }
            selected = candidate;
        }
        return selected;
    }

    private static boolean canonicalScalarBindingDeclared(
            String smt, String portTerm, String solverTerm,
            String nullnessSolverTerm, ScalarEncoding encoding) {
        if (!smt.contains("(declare-const " + solverTerm + " "
                + encoding.solverSort + ")")
                || !smt.contains("(declare-const " + portTerm + " Value)")) {
            return false;
        }
        if (encoding == ScalarEncoding.STRING) {
            if (!safeSmtAtom(nullnessSolverTerm)
                    || !smt.contains("(declare-const " + nullnessSolverTerm
                    + " Bool)")) {
                return false;
            }
            String boxed = "(ite " + nullnessSolverTerm
                    + " (VRef nullRef) (VString " + solverTerm + "))";
            return smt.contains("(= " + portTerm + " " + boxed + ")")
                    || smt.contains("(= " + boxed + " " + portTerm + ")");
        }
        return smt.contains("(= " + portTerm + " ("
                + encoding.valueConstructor + " " + solverTerm + "))")
                || smt.contains("(= (" + encoding.valueConstructor + " "
                + solverTerm + ") " + portTerm + ")");
    }

    private static List<JsonObject> scalarEvidence(
            List<JsonObject> evidence, ScalarEncoding encoding) {
        if (evidence == null || evidence.isEmpty()) {
            return Collections.emptyList();
        }
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject mapping : evidence) {
            if (encoding.solverSort.equals(string(mapping, "solverSort"))) {
                result.add(mapping);
            }
        }
        return result;
    }

    /**
     * A short-circuit case need not read every root.  Evidence is authoritative
     * where the input is used; requiring it to be redundantly repeated in
     * every case rejects valid null and early-return paths.  Multiple
     * projections for one used case remain ambiguous and fail closed.
     */
    private static boolean atMostOneMappingPerUsedCase(
            List<JsonObject> evidence) {
        Set<String> cases = new LinkedHashSet<>();
        for (JsonObject mapping : evidence) {
            String caseId = string(mapping, "caseId");
            if (caseId.isEmpty() || !cases.add(caseId)) return false;
        }
        return true;
    }

    /**
     * Attests the composer's explicit dynamic-leaf/canonical-port bridge.
     * Every identity is reconstructed from the catalog and the exact named
     * assertion must occur as one complete SMT line; no symbol-prefix or
     * formula-shape inference is accepted here.
     */
    private static boolean exactDynamicCanonicalBridge(
            String smt, JsonObject mapping, String port,
            String canonicalSolverTerm,
            String canonicalNullnessSolverTerm,
            ScalarEncoding encoding) {
        String actual = string(mapping, "solverTerm");
        String actualNullness = string(mapping, "nullnessSolverTerm");
        String guard = string(mapping, "canonicalBridgeGuard");
        String expression = encoding == ScalarEncoding.STRING
                ? "(and (= " + actual + " " + canonicalSolverTerm
                + ") (= " + actualNullness + " "
                + canonicalNullnessSolverTerm + "))"
                : "(= " + actual + " " + canonicalSolverTerm + ")";
        String formula = "(=> " + guard + " " + expression + ")";
        String assertionName = string(mapping,
                "canonicalBridgeAssertionName");
        String assertion = "(assert (! " + formula + " :named "
                + assertionName + "))";
        JsonArray ids = array(mapping, "dynamicBindingIds");
        if (!port.equals(string(mapping, "canonicalPort"))
                || actual.isEmpty() || actual.equals(canonicalSolverTerm)
                || !safeSmtAtom(actual)
                || !safeSmtAtom(canonicalSolverTerm)
                || encoding == ScalarEncoding.STRING
                && (!safeSmtAtom(actualNullness)
                || !safeSmtAtom(canonicalNullnessSolverTerm)
                || !canonicalNullnessSolverTerm.equals(string(mapping,
                "canonicalNullnessSolverTerm"))
                || !NULLABLE_STRING_ENCODING_AUTHORITY.equals(string(
                mapping, "nullableStringEncodingAuthority")))
                || !canonicalSolverTerm.equals("sym__port__"
                + smtName(port) + "__" + encoding.suffix)
                || !port.startsWith(string(mapping, "regionId") + ".in.")
                || !encoding.name().equals(string(mapping, "sort"))
                || !canonicalSolverTerm.equals(string(mapping,
                "canonicalSolverTerm"))
                || !guard.equals(string(mapping, "selectorSolverSymbol"))
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
        String bindingId = ids.get(0).getAsString();
        JsonObject selected = null;
        for (JsonElement element : array(mapping,
                "caseDynamicFieldBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!bindingId.equals(string(binding,
                    "dynamicBindingId"))) continue;
            if (selected != null) return false;
            selected = binding;
        }
        return selected != null
                && port.equals(string(selected, "baseInputSymbol"))
                && actual.equals(string(selected, "solverTerm"))
                && (encoding != ScalarEncoding.STRING
                || actualNullness.equals(string(selected,
                "nullnessSolverTerm")))
                && string(mapping, "rawEngineSymbol").equals(string(selected,
                "fieldExpressionRawEngineSymbol"))
                && bool(selected, "complete", false)
                && bool(selected, "observationMatched", false)
                && (encoding != ScalarEncoding.STRING
                || NULLABLE_STRING_ENCODING_AUTHORITY.equals(string(
                selected, "nullableStringEncodingAuthority")))
                && "EMITTER_ACTUAL_DYNAMIC_FIELD_TERM".equals(string(
                selected, "termBindingAuthority"));
    }

    private static boolean hasDynamicBridgeMetadata(JsonObject mapping) {
        for (String member : new String[]{"canonicalSolverTerm",
                "canonicalBridgeGuard", "canonicalBridgeExpression",
                "canonicalBridgeFormula", "canonicalBridgeAssertionName",
                "canonicalBridgeAssertion",
                "canonicalBridgeAssertionSha256",
                "canonicalBridgeAuthority"}) {
            if (mapping.has(member)) return true;
        }
        return false;
    }

    private static boolean safeSmtAtom(String value) {
        return value != null && SAFE_SMT_ATOM.matcher(value).matches();
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

    private static Set<String> suppliedInputs(JsonObject relationships,
                                              PortCatalog ports,
                                              List<String> gaps) {
        Set<String> result = new LinkedHashSet<>();
        JsonArray rows = array(relationships, "relationships");
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

    private static JsonArray scalarInputCatalog(List<ScalarInput> inputs) {
        JsonArray result = new JsonArray();
        for (int index = 0; index < inputs.size(); index++) {
            JsonObject row = inputs.get(index).toJson();
            row.addProperty("ordinal", index);
            result.add(row);
        }
        return result;
    }

    private static JsonArray caseProjectionEvidence(
            List<JsonObject> evidenceRows) {
        JsonArray cases = new JsonArray();
        Set<String> seen = new LinkedHashSet<>();
        for (JsonObject evidence : evidenceRows) {
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
            for (String member : new String[]{"solverTerm",
                    "nullnessSolverTerm",
                    "canonicalSolverTerm", "canonicalBridgeGuard",
                    "canonicalNullnessSolverTerm",
                    "canonicalBridgeAssertionName",
                    "canonicalBridgeAssertionSha256",
                    "canonicalBridgeAuthority",
                    "nullableStringEncodingAuthority"}) {
                JsonElement value = evidence.get(member);
                if (value != null) row.add(member, value.deepCopy());
            }
            row.add("dynamicBindingIds", array(evidence,
                    "dynamicBindingIds").deepCopy());
            cases.add(row);
        }
        return cases;
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
        private final List<ScalarInput> existentialNonBooleanRootInputs;
        private final int staticNonBooleanScalarInputCount;
        private final int usedNonBooleanScalarInputCount;
        private final int upstreamSuppliedNonBooleanScalarInputCount;
        private final int nullableJavaStringInputCount;

        private Discovery(List<BooleanInput> rootInputs,
                          List<BooleanInput> booleanDomainInputs,
                          int staticBooleanInputCount,
                          int usedBooleanInputCount,
                          int upstreamSuppliedBooleanInputCount,
                          List<ScalarInput> existentialNonBooleanRootInputs,
                          int staticNonBooleanScalarInputCount,
                          int usedNonBooleanScalarInputCount,
                          int upstreamSuppliedNonBooleanScalarInputCount,
                          int nullableJavaStringInputCount) {
            this.rootInputs = rootInputs;
            this.booleanDomainInputs = booleanDomainInputs;
            this.staticBooleanInputCount = staticBooleanInputCount;
            this.usedBooleanInputCount = usedBooleanInputCount;
            this.upstreamSuppliedBooleanInputCount =
                    upstreamSuppliedBooleanInputCount;
            this.existentialNonBooleanRootInputs =
                    existentialNonBooleanRootInputs;
            this.staticNonBooleanScalarInputCount =
                    staticNonBooleanScalarInputCount;
            this.usedNonBooleanScalarInputCount =
                    usedNonBooleanScalarInputCount;
            this.upstreamSuppliedNonBooleanScalarInputCount =
                    upstreamSuppliedNonBooleanScalarInputCount;
            this.nullableJavaStringInputCount = nullableJavaStringInputCount;
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
            result.add("caseProjectionEvidence",
                    caseProjectionEvidence(caseEvidence));
            result.addProperty("authority",
                    "STATIC_BOOLEAN_PORT_PLUS_COMPOSED_SMT_CANONICAL_"
                            + "BINDING");
            return result;
        }
    }

    private static final class ScalarInput {
        private final PortInfo port;
        private final String solverTerm;
        private final String nullnessSolverTerm;
        private final ScalarEncoding encoding;
        private final List<JsonObject> caseEvidence;

        private ScalarInput(PortInfo port, String solverTerm,
                            String nullnessSolverTerm,
                            ScalarEncoding encoding,
                            List<JsonObject> caseEvidence) {
            this.port = port;
            this.solverTerm = solverTerm;
            this.nullnessSolverTerm = firstNonBlank(nullnessSolverTerm);
            this.encoding = encoding;
            this.caseEvidence = caseEvidence == null
                    ? Collections.<JsonObject>emptyList()
                    : new ArrayList<>(caseEvidence);
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("portId", port.id);
            result.addProperty("regionId", port.regionId);
            result.addProperty("cell", port.cell);
            result.addProperty("javaType", port.javaType);
            result.addProperty("javaTypeDescriptor", port.descriptor);
            result.addProperty("solverTerm", solverTerm);
            result.addProperty("solverSort", encoding.solverSort);
            if (encoding == ScalarEncoding.STRING) {
                result.addProperty("nullnessSolverTerm",
                        nullnessSolverTerm);
                result.addProperty("nullnessSolverSort", "Bool");
                result.addProperty("nullableStringEncodingAuthority",
                        NULLABLE_STRING_ENCODING_AUTHORITY);
            }
            result.addProperty("root", true);
            result.addProperty("upstreamSupplied", false);
            result.addProperty("projectionRole",
                    "EXISTENTIALLY_QUANTIFIED_IN_BOOLEAN_PROJECTION");
            result.add("caseProjectionEvidence",
                    caseProjectionEvidence(caseEvidence));
            result.addProperty("authority",
                    "STATIC_JAVA_SCALAR_PORT_PLUS_COMPOSED_SMT_CANONICAL_"
                            + "BINDING_AND_RUNTIME_RELATIONSHIP_DIRECTION_V1");
            return result;
        }
    }

    private enum ScalarEncoding {
        INT("Int", "int", "VInt"),
        FLOAT32("(_ FloatingPoint 8 24)", "float32", "VFloat"),
        FLOAT64("(_ FloatingPoint 11 53)", "float64", "VDouble"),
        STRING("String", "string", "VString");

        private final String solverSort;
        private final String suffix;
        private final String valueConstructor;

        ScalarEncoding(String solverSort, String suffix,
                       String valueConstructor) {
            this.solverSort = solverSort;
            this.suffix = suffix;
            this.valueConstructor = valueConstructor;
        }

        private String solverTerm(String port) {
            return "sym__port__" + smtName(port) + "__" + suffix;
        }

        private static ScalarEncoding of(String descriptor) {
            String value = firstNonBlank(descriptor);
            if ("B".equals(value) || "C".equals(value)
                    || "S".equals(value) || "I".equals(value)
                    || "J".equals(value)
                    || "Ljava/lang/Byte;".equals(value)
                    || "Ljava/lang/Character;".equals(value)
                    || "Ljava/lang/Short;".equals(value)
                    || "Ljava/lang/Integer;".equals(value)
                    || "Ljava/lang/Long;".equals(value)) {
                return INT;
            }
            if ("F".equals(value)
                    || "Ljava/lang/Float;".equals(value)) return FLOAT32;
            if ("D".equals(value)
                    || "Ljava/lang/Double;".equals(value)) return FLOAT64;
            if ("Ljava/lang/String;".equals(value)) return STRING;
            return null;
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

        private static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; argv != null && index < argv.length; index++) {
                String argument = argv[index];
                if (!argument.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException(
                            "Expected --key value, got: " + argument);
                }
                String key = argument.substring(2);
                if (!option(key)) {
                    throw new IllegalArgumentException(
                            "Unknown reach option: --" + key);
                }
                if (values.put(key, argv[++index]) != null) {
                    throw new IllegalArgumentException(
                            "Duplicate reach option: --" + key);
                }
            }
            Arguments result = new Arguments();
            result.smt = required(values, "smt");
            result.manifest = required(values, "manifest");
            result.regions = required(values, "regions");
            result.relationships = required(values, "relationships");
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
            return result;
        }

        private static boolean option(String key) {
            return "smt".equals(key) || "manifest".equals(key)
                    || "regions".equals(key)
                    || "relationships".equals(key)
                    || "output".equals(key) || "z3".equals(key)
                    || "timeout-ms".equals(key)
                    || "max-inputs".equals(key)
                    || "max-valuations".equals(key);
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
     * static-region ledger, and relationship-candidate bytes.
     */
    static void validateArtifactBindings(Path smtPath, Path regionsPath,
                                         Path relationshipsPath,
                                         JsonObject manifest)
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
