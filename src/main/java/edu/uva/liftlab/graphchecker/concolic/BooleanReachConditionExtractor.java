package edu.uva.liftlab.graphchecker.concolic;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.artifact;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sibling;
import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;

import java.io.File;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

/**
 * Projects a structurally complete candidate bug-path SMT formula onto its
 * free Boolean roots, and reports the reach condition as a DNF over them.
 */
public final class BooleanReachConditionExtractor {
    private static final int MAX_EXISTENTIAL_PERTURBATIONS = 32;
    static final String SYMBOLIC_VARIABLE_MODELS =
            "symbolicVariableModels";
    private static final String SYMBOLIC_VARIABLE_MODEL_KIND =
            "SYMBOLIC_VARIABLE_MODEL";
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();
    private BooleanReachConditionExtractor() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        JsonObject manifest = ArtifactIO.readObject(arguments.manifest);
        String smt = ArtifactIO.readText(arguments.smt);
        List<JsonObject> regions = RuntimePlanArtifact.read(
                arguments.runtimePlan).regions();
        validateArtifactBindings(arguments.smt, arguments.runtimePlan,
                manifest);
        Z3Solver solver = new Z3Solver(arguments.z3,
                arguments.timeoutMillis);
        JsonObject report = extract(smt, manifest, regions, solver,
                arguments.maxInputs, arguments.maxValuations);
        report.add("solverAttempts", solver.attempts());
        report.add("compositionManifestArtifact",
                artifact(arguments.manifest));
        report.add("solverArtifact", solver.artifact());
        ArtifactIO.replace(arguments.output, GSON.toJson(report)
                + System.lineSeparator());
        System.out.println(GSON.toJson(report));
        if (!"CANDIDATE_READY".equals(string(report, "state"))) {
            System.exit(2);
        }
    }

    static JsonObject extract(String composedSmt, JsonObject manifest,
                              List<JsonObject> regions, Z3Solver solver,
                              int maxInputs, int maxValuations)
            throws IOException, InterruptedException {
        JsonObject report = new JsonObject();
        report.addProperty("schemaVersion", 3);
        report.addProperty("kind", "BOOLEAN_REACH_CONDITION_REPORT");
        boolean recordedModelComplete =
                bool(manifest, "recordedModelComplete", false);
        report.addProperty("recordedModelComplete", recordedModelComplete);
        boolean unsatClosureComplete = unsatClosureComplete(manifest);
        report.addProperty(ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE,
                unsatClosureComplete);
        JsonObject unsatClosureEvidence = object(manifest,
                ConcolicSmtComposer.UNSAT_CLOSURE_EVIDENCE);
        if (unsatClosureEvidence.size() > 0) {
            report.add(ConcolicSmtComposer.UNSAT_CLOSURE_EVIDENCE,
                    unsatClosureEvidence.deepCopy());
        }

        List<String> gaps = new ArrayList<>();
        validateCompositionAuthority(manifest, gaps);
        if (firstNonBlank(composedSmt).isEmpty()) {
            gaps.add("COMPOSED_SMT_EMPTY");
        }

        PortCatalog ports = PortCatalog.from(regions);
        ConfiguredSourceCatalog configuredSources =
                ConfiguredSourceCatalog.from(manifest, gaps);
        Discovery discovery = discover(composedSmt, ports,
                PortOccurrenceCatalog.from(manifest), configuredSources,
                gaps);
        List<RootInput> inputs = discovery.rootInputs;
        JsonObject roots = new JsonObject();
        roots.add("booleanInputs", inputCatalog(inputs));
        roots.add("existentialInputs", inputCatalog(
                discovery.existentialNonBooleanRootInputs));
        report.add("roots", roots);
        JsonArray symbolicVariableModels = new JsonArray();
        report.add(SYMBOLIC_VARIABLE_MODELS, symbolicVariableModels);

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
        if (!gaps.isEmpty()) {
            return incomplete(report, gaps);
        }

        String base = SmtLibQueries.stripSolverCommands(
                composedSmt);
        List<boolean[]> satisfyingValuations = new ArrayList<>();
        JsonArray valuationRows = new JsonArray();
        JsonArray existentialPerturbations = new JsonArray();
        boolean rejectedExistentialPerturbation = false;
        boolean existentialProbeAttempted = false;
        int solverErrors = 0;
        int count = (int) valuationCount;
        for (int ordinal = 0; ordinal < count; ordinal++) {
            boolean[] values = valuation(ordinal, inputs.size());
            String query = valuationQuery(base, inputs, values,
                    discovery.existentialNonBooleanRootInputs);
            ConcolicConstraintSolver.SolverOutput result =
                    solver.check(query);
            String status = result.status();
            JsonObject row = valuationRow(values, status);
            if ("sat".equals(status)) {
                satisfyingValuations.add(values.clone());
                JsonArray witness = existentialWitness(result,
                        discovery.existentialNonBooleanRootInputs);
                if (witness.size() > 0) {
                    row.add("existentialWitness", witness);
                    if (!existentialProbeAttempted) {
                        existentialProbeAttempted = true;
                        JsonArray perturbations = existentialPerturbations(
                                solver, query,
                                discovery.existentialNonBooleanRootInputs,
                                witness);
                        for (JsonElement perturbation : perturbations) {
                            existentialPerturbations.add(perturbation);
                            if ("unsat".equals(string(
                                    perturbation.getAsJsonObject(),
                                    "status"))) {
                                rejectedExistentialPerturbation = true;
                            }
                        }
                    }
                }
                JsonArray configuredWitness = configuredSourceWitness(
                        inputs, values, witness);
                if (configuredWitness.size() > 0) {
                    row.add("configuredSourceWitness",
                            configuredWitness);
                    JsonObject symbolicModel = new JsonObject();
                    symbolicModel.addProperty("schemaVersion", 1);
                    symbolicModel.addProperty("kind",
                            SYMBOLIC_VARIABLE_MODEL_KIND);
                    symbolicModel.addProperty("valuationOrdinal", ordinal);
                    symbolicModel.add("variables",
                            configuredWitness.deepCopy());
                    symbolicVariableModels.add(symbolicModel);
                }
            } else if (!"unsat".equals(status)) {
                row.addProperty("solverOutput", result.diagnostic());
                solverErrors++;
            }
            valuationRows.add(row);
        }

        report.add("valuations", valuationRows);
        if (existentialPerturbations.size() > 0) {
            JsonObject probe = new JsonObject();
            probe.addProperty("authority",
                    "SOLVER_WITNESS_NEIGHBOR_PERTURBATION_V1");
            probe.addProperty("constrainsRootSpace",
                    rejectedExistentialPerturbation);
            probe.add("perturbations", existentialPerturbations);
            report.add("existentialRootProbe", probe);
        }

        // Every Boolean assignment was queried above and the DNF is built
        // from exactly the SAT rows, so no confirming solver call is needed.
        boolean complete = solverErrors == 0;
        // Best-effort branch replay never proves every program path was
        // explored, so an empty SAT set is UNKNOWN and not UNREACHABLE.
        boolean observedUnderapproximation = !unsatClosureComplete;
        String reachability = !complete
                ? "UNKNOWN" : !satisfyingValuations.isEmpty()
                ? "REACHABLE" : observedUnderapproximation
                ? "UNKNOWN" : "UNREACHABLE";
        JsonObject reachCondition = new JsonObject();
        String formula = dnf(inputs, satisfyingValuations, count);
        reachCondition.addProperty("formula", formula);
        if (!discovery.existentialNonBooleanRootInputs.isEmpty()) {
            reachCondition.addProperty("formulaDomain",
                    "BOOLEAN_PROJECTION_EXISTS_NON_BOOLEAN_ROOTS");
        }
        reachCondition.addProperty("reachability", reachability);
        if (observedUnderapproximation
                && satisfyingValuations.isEmpty() && complete) {
            reachCondition.addProperty("coverageConclusion",
                    recordedModelComplete
                            ? "INCONCLUSIVE_OPEN_PATH_CLOSURE"
                            : "INCONCLUSIVE_UNDERAPPROXIMATION");
        }
        reachCondition.addProperty("degeneracyCheck", degeneracyCheck(
                formula, reachability, inputs.size(),
                discovery.existentialNonBooleanRootInputs.size(),
                discovery.undecodedFreeInputCount,
                rejectedExistentialPerturbation));
        report.add("reachCondition", reachCondition);
        JsonArray resultGaps = new JsonArray();
        if (solverErrors > 0) {
            resultGaps.add("UNDECIDED_SOLVER_VALUATIONS:"
                    + solverErrors);
        }
        report.add("gaps", resultGaps);
        report.addProperty("state", complete
                ? "CANDIDATE_READY" : "CANDIDATE_WITH_GAPS");
        return report;
    }

    /** States whether the degeneracy question was decided, and on what. */
    private static String degeneracyCheck(String formula,
                                          String reachability,
                                          int booleanRootCount,
                                          int existentialRootCount,
                                          int undecodedFreeInputCount,
                                          boolean rejectedExistentialProbe) {
        if (!"REACHABLE".equals(reachability)) {
            return "NOT_APPLICABLE_NO_MODEL";
        }
        if (!"true".equals(formula)) {
            return "CONSTRAINED_ROOT_SPACE";
        }
        if (rejectedExistentialProbe) {
            return "CONSTRAINED_ROOT_SPACE";
        }
        if (existentialRootCount > 0) {
            return "UNDECIDED_UNENUMERATED_EXISTENTIAL_ROOTS:"
                    + existentialRootCount;
        }
        if (undecodedFreeInputCount > 0) {
            return "UNDECIDED_UNMODELLED_INPUT_FREEDOMS:"
                    + undecodedFreeInputCount;
        }
        return booleanRootCount == 0 ? "NOT_APPLICABLE_NO_FREE_ROOTS"
                : "DEGENERATE_UNCONSTRAINED_ROOT_SPACE";
    }

    private static void validateCompositionAuthority(
            JsonObject manifest, List<String> gaps) {
        // This stage needs a composition that already declared itself
        // candidate-ready; re-deriving that verdict from its members would
        // be the second gate README forbids.
        boolean commonManifest = manifest != null
                && integer(manifest, "schemaVersion", -1) == 2
                && "CONCOLIC_COMPOSED_SMT".equals(string(manifest, "kind"));
        if (!commonManifest
                || !"CANDIDATE_READY".equals(string(manifest, "state"))) {
            gaps.add("COMPOSITION_MANIFEST_NOT_CANDIDATE_MODEL_ELIGIBLE");
        }
        JsonElement occurrences = manifest == null ? null
                : manifest.get("portOccurrences");
        if (occurrences == null || !occurrences.isJsonArray()) {
            gaps.add("PORT_OCCURRENCES_MISSING");
        }
    }

    /** The Composer's single, internally consistent UNSAT closure claim. */
    private static boolean unsatClosureComplete(JsonObject manifest) {
        if (manifest == null
                || !bool(manifest,
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE, false)
                || !ConcolicSmtComposer.FINAL_READY.equals(
                string(manifest, ConcolicSmtComposer.FINAL_STATUS))) {
            return false;
        }
        JsonObject evidence = object(manifest,
                ConcolicSmtComposer.UNSAT_CLOSURE_EVIDENCE);
        JsonElement partial = evidence.get("partialProducerSummaryIds");
        return integer(evidence, "schemaVersion", -1) == 1
                && "UNSAT_CLOSURE_EVIDENCE".equals(
                string(evidence, "kind"))
                && ConcolicSmtComposer.UNSAT_CLOSURE_AUTHORITY.equals(
                string(evidence, "authority"))
                && bool(evidence, "recordedModelComplete", false)
                == bool(manifest, "recordedModelComplete", false)
                && bool(evidence, "recordedModelComplete", false)
                && bool(evidence, "producerPathsClosed", false)
                && bool(evidence, "targetPathsClosed", false)
                && bool(evidence, "compositionCoverageClosed", false)
                && bool(evidence, "finalStatusReady", false)
                && integer(evidence, "targetCoverageGapCount", -1) == 0
                && integer(evidence,
                "compositionCoverageGapCount", -1) == 0
                && partial != null && partial.isJsonArray()
                && partial.getAsJsonArray().size() == 0
                && bool(evidence,
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE, false);
    }

    private static Discovery discover(String smt, PortCatalog ports,
                                      PortOccurrenceCatalog occurrences,
                                      ConfiguredSourceCatalog sources,
                                      List<String> gaps) {
        List<RootInput> roots = new ArrayList<>();
        List<RootInput> scalarRoots = new ArrayList<>();
        // An unsupplied input this extractor cannot decode is still a freedom
        // of the model, only one this report cannot name, so it is counted
        // and surfaced through degeneracyCheck rather than dropped.
        Set<String> undecoded = new LinkedHashSet<>();
        for (PortOccurrenceInfo occurrence : occurrences.sorted()) {
            PortInfo port = ports.input(occurrence.portId);
            if (port == null) continue;
            ScalarEncoding encoding = ScalarEncoding.of(port.descriptor);
            if (encoding == null
                    || !encoding.occurrenceSort.equals(occurrence.sort)) {
                if (!occurrence.supplied) {
                    undecoded.add(port.id);
                }
                continue;
            }
            boolean declared = canonicalScalarBindingDeclared(smt,
                    occurrence.portTerm, occurrence.solverTerm,
                    occurrence.nullnessSolverTerm, encoding);
            if (!declared) {
                if (!occurrence.supplied) {
                    undecoded.add(port.id);
                }
                continue;
            }
            if (port.javaBoolean) {
                if (!occurrence.supplied) {
                    roots.add(new RootInput(port, occurrence.occurrenceId,
                            occurrence.solverTerm, ""));
                }
            } else if (occurrence.supplied) {
                continue;
            } else {
                scalarRoots.add(new RootInput(port,
                        occurrence.occurrenceId, occurrence.solverTerm,
                        occurrence.nullnessSolverTerm));
            }
        }
        for (ConfiguredSourceInfo source : sources.sorted()) {
            ScalarEncoding encoding = ScalarEncoding.of(source.descriptor);
            if (encoding == null
                    || !encoding.occurrenceSort.equals(source.sort)
                    || !encoding.solverSort.equals(source.smtSort)
                    || !configuredSourceBindingDeclared(smt, source,
                    encoding)) {
                String subject = "configured-source:" + source.sourceId
                        + "@" + source.sourcePhaseId;
                undecoded.add(subject);
                gaps.add("CONFIGURED_SOURCE_TERM_NOT_DECLARED_OR_SORT_MISMATCH:"
                        + subject);
                continue;
            }
            RootInput input = new RootInput(source.asPortInfo(),
                    source.sourceOccurrenceId, source.solverTerm,
                    source.nullnessSolverTerm, source.sourcePhaseId,
                    source.sourceKey);
            if (input.port.javaBoolean) {
                roots.add(input);
            } else {
                scalarRoots.add(input);
            }
        }
        // The solver term is the tiebreaker one mint site now needs: two
        // entries of one site share id, occurrence and phase and differ only
        // in the root they minted.
        Comparator<RootInput> byOccurrence = Comparator
                .comparing((RootInput value) -> value.port.id)
                .thenComparing(value -> value.occurrenceId)
                .thenComparing(value -> value.sourcePhaseId)
                .thenComparing(value -> value.solverTerm);
        Collections.sort(roots, byOccurrence);
        Collections.sort(scalarRoots, byOccurrence);
        return new Discovery(roots, scalarRoots, undecoded.size());
    }

    /** Whether the formula really declares the source term claimed. */
    private static boolean configuredSourceBindingDeclared(
            String smt, ConfiguredSourceInfo source,
            ScalarEncoding encoding) {
        if (!smt.contains("(declare-const " + source.solverTerm + " "
                + encoding.solverSort + ")")) {
            return false;
        }
        return encoding != ScalarEncoding.STRING
                || !source.nullnessSolverTerm.isEmpty()
                && smt.contains("(declare-const "
                + source.nullnessSolverTerm + " Bool)");
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
            if (!smt.contains("(declare-const " + nullnessSolverTerm
                    + " Bool)")) {
                return false;
            }
            String boxed = "(ite " + nullnessSolverTerm
                    + " (VRef nullRef) (VString " + solverTerm + "))";
            return smt.contains("(= " + portTerm + " " + boxed + ")")
                    || smt.contains("(= " + boxed + " " + portTerm + ")");
        }
        String valueConstructor = ContainerSmtCodec.valueKind(
                encoding.javaDescriptor);
        return smt.contains("(= " + portTerm + " ("
                + valueConstructor + " " + solverTerm + "))")
                || smt.contains("(= (" + valueConstructor + " "
                + solverTerm + ") " + portTerm + ")");
    }

    private static String valuationQuery(String base,
                                         List<RootInput> inputs,
                                         boolean[] values,
                                         List<RootInput> witnessRoots) {
        StringBuilder query = new StringBuilder(base);
        for (int index = 0; index < inputs.size(); index++) {
            query.append("(assert ")
                    .append(inputs.get(index).literal(values[index]))
                    .append(")").append(System.lineSeparator());
        }
        query.append("(check-sat)").append(System.lineSeparator());
        if (witnessRoots != null && !witnessRoots.isEmpty()) {
            query.append("(get-value (");
            for (RootInput root : witnessRoots) {
                query.append(' ').append(root.solverTerm);
                if (!root.nullnessSolverTerm.isEmpty()) {
                    query.append(' ').append(root.nullnessSolverTerm);
                }
            }
            query.append("))").append(System.lineSeparator());
        }
        return query.toString();
    }

    private static boolean[] valuation(int ordinal, int width) {
        boolean[] result = new boolean[width];
        for (int index = 0; index < width; index++) {
            int shift = width - index - 1;
            result[index] = ((ordinal >>> shift) & 1) != 0;
        }
        return result;
    }

    private static JsonArray inputCatalog(List<RootInput> inputs) {
        JsonArray result = new JsonArray();
        for (RootInput input : inputs) {
            result.add(input.toJson());
        }
        return result;
    }

    private static JsonObject incomplete(JsonObject report,
                                         List<String> gaps) {
        report.add("valuations", new JsonArray());
        JsonObject reachCondition = new JsonObject();
        reachCondition.addProperty("formula", "");
        reachCondition.addProperty("reachability", "UNKNOWN");
        reachCondition.addProperty("degeneracyCheck",
                "UNDECIDED_REPORT_INCOMPLETE");
        report.add("reachCondition", reachCondition);
        report.add("gaps", GSON.toJsonTree(gaps));
        report.addProperty("state", "CANDIDATE_WITH_GAPS");
        return report;
    }

    static final class Z3Solver {
        private final Path executable;
        private final long timeoutMillis;
        private final JsonObject artifact;
        private final JsonArray attempts = new JsonArray();
        private int queryOrdinal;

        Z3Solver(String executable, long timeoutMillis) throws IOException {
            this.timeoutMillis = Math.max(1L, timeoutMillis);
            this.executable = resolveExecutable(firstNonBlank(executable,
                    "z3"));
            this.artifact = ArtifactIO.artifact(this.executable);
        }

        JsonObject artifact() {
            return artifact.deepCopy();
        }

        JsonArray attempts() {
            return attempts.deepCopy();
        }

        ConcolicConstraintSolver.SolverOutput check(String smt)
                throws IOException,
                InterruptedException {
            return attempt(queryOrdinal++, 0, "Z3", smt, "",
                    timeoutMillis);
        }

        private ConcolicConstraintSolver.SolverOutput attempt(
                int currentQuery, int ordinal, String strategy,
                String baseQuery, String options, long attemptTimeout)
                throws IOException, InterruptedException {
            String query = options + baseQuery;
            long started = System.nanoTime();
            ConcolicConstraintSolver.SolverOutput result =
                    ConcolicConstraintSolver.run(executable, query,
                            attemptTimeout);
            long elapsedMillis = Math.max(0L,
                    (System.nanoTime() - started) / 1_000_000L);
            JsonObject row = new JsonObject();
            row.addProperty("queryOrdinal", currentQuery);
            row.addProperty("attemptOrdinal", ordinal);
            row.addProperty("strategy", strategy);
            row.addProperty("baseQuerySha256",
                    ArtifactIO.sha256(baseQuery));
            row.addProperty("solverQuerySha256", ArtifactIO.sha256(query));
            row.addProperty("timeoutMillis", attemptTimeout);
            row.addProperty("elapsedMillis", elapsedMillis);
            row.addProperty("status", result.status());
            row.addProperty("options", options.trim());
            attempts.add(row);
            return result;
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
                if (candidate.toFile().isFile()
                        && candidate.toFile().canExecute()) {
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
            if (!resolved.toFile().isFile()
                    || !resolved.toFile().canExecute()) {
                throw new IOException("Z3 executable is not an executable "
                        + "regular file: " + resolved);
            }
            return resolved;
        }

    }

    private static final class Discovery {
        private final List<RootInput> rootInputs;
        private final List<RootInput> existentialNonBooleanRootInputs;
        private final int undecodedFreeInputCount;

        private Discovery(List<RootInput> rootInputs,
                          List<RootInput> existentialNonBooleanRootInputs,
                          int undecodedFreeInputCount) {
            this.rootInputs = rootInputs;
            this.existentialNonBooleanRootInputs =
                    existentialNonBooleanRootInputs;
            this.undecodedFreeInputCount = undecodedFreeInputCount;
        }
    }

    private static final class RootInput {
        private final PortInfo port;
        private final String occurrenceId;
        private final String solverTerm;
        private final String nullnessSolverTerm;
        private final String sourcePhaseId;
        private final String sourceKey;

        private RootInput(PortInfo port, String occurrenceId,
                          String solverTerm,
                          String nullnessSolverTerm) {
            this(port, occurrenceId, solverTerm, nullnessSolverTerm,
                    "", "");
        }

        private RootInput(PortInfo port, String occurrenceId,
                          String solverTerm,
                          String nullnessSolverTerm,
                          String sourcePhaseId, String sourceKey) {
            this.port = port;
            this.occurrenceId = firstNonBlank(occurrenceId);
            this.solverTerm = solverTerm;
            this.nullnessSolverTerm = firstNonBlank(nullnessSolverTerm);
            this.sourcePhaseId = firstNonBlank(sourcePhaseId);
            this.sourceKey = firstNonBlank(sourceKey);
        }

        private String literal(boolean value) {
            return "(= " + solverTerm + " "
                    + (value ? "true" : "false") + ")";
        }

        private List<String> neighboringLiterals(String value) {
            ScalarEncoding encoding = ScalarEncoding.of(port.descriptor);
            return encoding == null ? Collections.<String>emptyList()
                    : encoding.neighboringLiterals(value);
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            if (port.configuredSource) {
                result.addProperty("inputKind", "CONFIGURED_SOURCE_FIELD");
                result.addProperty("sourceKey", sourceKey);
                result.addProperty("sourceId", port.id);
                result.addProperty("sourceOccurrenceId", occurrenceId);
                result.addProperty("sourcePhaseId", sourcePhaseId);
                result.addProperty("fieldSignature", port.fieldSignature);
                // Named by the entry, not by the site: two entries of one
                // site (the NameNode's key expiry and the DataNode's) share
                // every other component of this name.
                result.addProperty("displayName", sourceKey + "::"
                        + port.id + "::" + occurrenceId + "::"
                        + sourcePhaseId);
            } else {
                result.addProperty("inputKind", "REGION_INPUT_PORT");
                result.addProperty("portId", port.id);
                result.addProperty("occurrenceId", occurrenceId);
            }
            result.addProperty("javaTypeDescriptor", port.descriptor);
            result.addProperty("solverTerm", solverTerm);
            if (!nullnessSolverTerm.isEmpty()) {
                result.addProperty("nullnessSolverTerm",
                        nullnessSolverTerm);
            }
            return result;
        }
    }

    private enum ScalarEncoding {
        BOOL("BOOL", "Bool", "Z"),
        BYTE("INT", "Int", "B"),
        CHAR("INT", "Int", "C"),
        SHORT("INT", "Int", "S"),
        INT("INT", "Int", "I"),
        LONG("INT", "Int", "J"),
        FLOAT32("FLOAT32", "(_ FloatingPoint 8 24)", "F"),
        FLOAT64("FLOAT64", "(_ FloatingPoint 11 53)", "D"),
        STRING("STRING", "String", "Ljava/lang/String;");

        private final String occurrenceSort;
        private final String solverSort;
        private final String javaDescriptor;

        ScalarEncoding(String occurrenceSort, String solverSort,
                       String javaDescriptor) {
            this.occurrenceSort = occurrenceSort;
            this.solverSort = solverSort;
            this.javaDescriptor = javaDescriptor;
        }

        private static ScalarEncoding of(String descriptor) {
            String declared = firstNonBlank(descriptor);
            String value = JavaPrimitiveBoxing.primitiveDescriptor(declared);
            if (value.isEmpty()) value = javaTypeDescriptor(declared);
            if ("Z".equals(value)
                    || "Ljava/lang/Boolean;".equals(value)) return BOOL;
            if ("B".equals(value)) return BYTE;
            if ("C".equals(value)) return CHAR;
            if ("S".equals(value)) return SHORT;
            if ("I".equals(value)) return INT;
            if ("J".equals(value)) return LONG;
            if ("F".equals(value)) return FLOAT32;
            if ("D".equals(value)) return FLOAT64;
            if ("Ljava/lang/String;".equals(value)) return STRING;
            return null;
        }

        private List<String> neighboringLiterals(String literal) {
            BigInteger value = parseSmtInteger(literal);
            if (value == null) return Collections.emptyList();
            BigInteger minimum;
            BigInteger maximum;
            switch (this) {
                case BYTE:
                    minimum = BigInteger.valueOf(Byte.MIN_VALUE);
                    maximum = BigInteger.valueOf(Byte.MAX_VALUE);
                    break;
                case CHAR:
                    minimum = BigInteger.ZERO;
                    maximum = BigInteger.valueOf(Character.MAX_VALUE);
                    break;
                case SHORT:
                    minimum = BigInteger.valueOf(Short.MIN_VALUE);
                    maximum = BigInteger.valueOf(Short.MAX_VALUE);
                    break;
                case INT:
                    minimum = BigInteger.valueOf(Integer.MIN_VALUE);
                    maximum = BigInteger.valueOf(Integer.MAX_VALUE);
                    break;
                case LONG:
                    minimum = BigInteger.valueOf(Long.MIN_VALUE);
                    maximum = BigInteger.valueOf(Long.MAX_VALUE);
                    break;
                default:
                    return Collections.emptyList();
            }
            List<String> result = new ArrayList<>();
            if (value.compareTo(minimum) > 0) {
                result.add(formatSmtInteger(
                        value.subtract(BigInteger.ONE)));
            }
            if (value.compareTo(maximum) < 0) {
                result.add(formatSmtInteger(
                        value.add(BigInteger.ONE)));
            }
            return result;
        }

        private static BigInteger parseSmtInteger(String literal) {
            String value = firstNonBlank(literal);
            try {
                if (value.startsWith("(- ") && value.endsWith(")")) {
                    return new BigInteger(value.substring(3,
                            value.length() - 1).trim()).negate();
                }
                return new BigInteger(value);
            } catch (NumberFormatException invalid) {
                return null;
            }
        }

        private static String formatSmtInteger(BigInteger value) {
            return value.signum() < 0
                    ? "(- " + value.negate() + ")" : value.toString();
        }
    }

    /** The values that make this valuation satisfiable. */
    private static JsonArray existentialWitness(
            ConcolicConstraintSolver.SolverOutput answer,
            List<RootInput> roots) {
        JsonArray witness = new JsonArray();
        if (roots.isEmpty() || answer == null
                || !"sat".equals(answer.status())) return witness;
        Map<String, String> assigned =
                ConcolicConstraintSolver.parseGetValues(answer.stdout);
        for (RootInput root : roots) {
            String value = assigned.get(root.solverTerm);
            if (value == null) continue;
            JsonObject row = root.toJson();
            row.addProperty("value", value);
            if (!root.nullnessSolverTerm.isEmpty()) {
                String nullness = assigned.get(
                        root.nullnessSolverTerm);
                if (nullness != null) {
                    row.addProperty("nullnessValue", nullness);
                }
            }
            witness.add(row);
        }
        return witness;
    }

    /** Materializable configured fields, separated from anonymous ports. */
    private static JsonArray configuredSourceWitness(
            List<RootInput> booleanRoots, boolean[] booleanValues,
            JsonArray existentialWitness) {
        JsonArray result = new JsonArray();
        for (int index = 0; index < booleanRoots.size(); index++) {
            RootInput root = booleanRoots.get(index);
            if (!root.port.configuredSource) continue;
            JsonObject row = root.toJson();
            row.addProperty("value", booleanValues[index]);
            result.add(row);
        }
        for (JsonElement element : existentialWitness) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if ("CONFIGURED_SOURCE_FIELD".equals(
                    string(row, "inputKind"))) {
                result.add(row.deepCopy());
            }
        }
        return result;
    }

    /**
     * Looks for a rejected point adjacent to an already satisfying scalar
     * witness: one unsat neighbour proves the root space is constrained.
     */
    private static JsonArray existentialPerturbations(
            Z3Solver solver, String query, List<RootInput> roots,
            JsonArray witness) {
        JsonArray result = new JsonArray();
        Map<String, String> values = new LinkedHashMap<>();
        for (JsonElement element : witness) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            String solverTerm = string(row, "solverTerm");
            String value = string(row, "value");
            if (!solverTerm.isEmpty() && !value.isEmpty()) {
                values.put(solverTerm, value);
            }
        }
        if (values.size() != roots.size()) return result;

        String base = SmtLibQueries.stripSolverCommands(query);
        for (RootInput changed : roots) {
            for (String alternative : changed.neighboringLiterals(
                    values.get(changed.solverTerm))) {
                if (result.size() >= MAX_EXISTENTIAL_PERTURBATIONS) {
                    return result;
                }
                StringBuilder candidate = new StringBuilder(base);
                for (RootInput root : roots) {
                    String value = root == changed ? alternative
                            : values.get(root.solverTerm);
                    candidate.append("(assert (= ")
                            .append(root.solverTerm).append(' ')
                            .append(value).append("))")
                            .append(System.lineSeparator());
                }
                candidate.append("(check-sat)")
                        .append(System.lineSeparator());
                JsonObject row = changed.toJson();
                row.addProperty("witnessValue",
                        values.get(changed.solverTerm));
                row.addProperty("perturbedValue", alternative);
                boolean rejected = false;
                try {
                    ConcolicConstraintSolver.SolverOutput answer =
                            solver.check(candidate.toString());
                    row.addProperty("status", answer.status());
                    rejected = "unsat".equals(answer.status());
                    if (!"sat".equals(answer.status())
                            && !"unsat".equals(answer.status())) {
                        row.addProperty("solverOutput",
                                answer.diagnostic());
                    }
                } catch (IOException | InterruptedException unanswered) {
                    if (unanswered instanceof InterruptedException) {
                        Thread.currentThread().interrupt();
                        row.addProperty("status", "unknown");
                        row.addProperty("solverOutput",
                                unanswered.getClass().getSimpleName());
                        result.add(row);
                        return result;
                    }
                    row.addProperty("status", "unknown");
                    row.addProperty("solverOutput",
                            unanswered.getClass().getSimpleName());
                }
                result.add(row);
                if (rejected) return result;
            }
        }
        return result;
    }

    private static JsonObject valuationRow(boolean[] values, String status) {
        JsonObject result = new JsonObject();
        result.add("values", GSON.toJsonTree(values));
        result.addProperty("status", status);
        return result;
    }

    private static String dnf(List<RootInput> inputs,
                              List<boolean[]> satisfying, int valuationCount) {
        List<String> terms = new ArrayList<>();
        for (boolean[] valuation : satisfying) {
            List<String> literals = new ArrayList<>();
            for (int index = 0; index < inputs.size(); index++) {
                literals.add(inputs.get(index).literal(
                        valuation[index]));
            }
            terms.add(join("and", literals, "true"));
        }
        if (terms.isEmpty()) return "false";
        return terms.size() == valuationCount
                ? "true" : join("or", terms, "false");
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

        private static PortCatalog from(List<JsonObject> regions) {
            PortCatalog result = new PortCatalog();
            for (JsonObject region : regions) {
                for (JsonElement element : array(region,
                        "symbolicInputs")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject row = element.getAsJsonObject();
                    String id = string(row, "portId");
                    if (!id.isEmpty()) {
                        result.inputs.put(id, new PortInfo(id,
                                MaterializationSpec.logicalJavaType(row)));
                    }
                }
            }
            return result;
        }

        private PortInfo input(String id) {
            return inputs.get(firstNonBlank(id));
        }
    }

    /** Exact writable source terms published by the Composer. */
    private static final class ConfiguredSourceCatalog {
        private final List<ConfiguredSourceInfo> sources = new ArrayList<>();

        private static ConfiguredSourceCatalog from(
                JsonObject manifest, List<String> gaps) {
            ConfiguredSourceCatalog result = new ConfiguredSourceCatalog();
            JsonElement encoded = manifest == null ? null : manifest.get(
                    ConcolicSmtComposer
                            .CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
            if (encoded == null || !encoded.isJsonArray()) {
                gaps.add("CONFIGURED_SOURCE_MATERIALIZATIONS_MISSING");
                return result;
            }
            // Wave 3 C1: one mint site mints once per entry, so the same
            // (sourceKey, sourcePhaseId, sourceId) legitimately materialises
            // several roots - the NameNode's key expiry and the DataNode's
            // are two of them.  The root itself is the identity: the Composer
            // keeps the map from VM symbol to root name injective, so one
            // solver term names exactly one mint.
            Map<String, ConfiguredSourceInfo> byIdentity =
                    new LinkedHashMap<>();
            int ordinal = 0;
            for (JsonElement element : encoded.getAsJsonArray()) {
                if (!element.isJsonObject()) {
                    gaps.add("CONFIGURED_SOURCE_MATERIALIZATION_MALFORMED:"
                            + ordinal++);
                    continue;
                }
                ConfiguredSourceInfo source = ConfiguredSourceInfo.decode(
                        element.getAsJsonObject());
                if (source == null) {
                    gaps.add("CONFIGURED_SOURCE_MATERIALIZATION_MALFORMED:"
                            + ordinal++);
                    continue;
                }
                ConfiguredSourceInfo held = byIdentity.putIfAbsent(
                        source.solverTerm, source);
                if (held != null) {
                    gaps.add("CONFIGURED_SOURCE_MATERIALIZATION_CONFLICT:"
                            + ordinal);
                } else {
                    result.sources.add(source);
                }
                ordinal++;
            }
            return result;
        }

        private List<ConfiguredSourceInfo> sorted() {
            List<ConfiguredSourceInfo> result = new ArrayList<>(sources);
            result.sort(Comparator
                    .comparing((ConfiguredSourceInfo value) ->
                            value.sourceKey)
                    .thenComparing(value -> value.sourceId)
                    .thenComparing(value -> value.sourcePhaseId)
                    .thenComparing(value -> value.sourceOccurrenceId)
                    .thenComparing(value -> value.fieldSignature)
                    // The root name is what separates two entries of one
                    // site; without it this order is not total.
                    .thenComparing(value -> value.solverTerm));
            return result;
        }
    }

    private static final class ConfiguredSourceInfo {
        private final String sourceKey;
        private final String sourceId;
        private final String sourcePhaseId;
        private final String sourceOccurrenceId;
        private final String fieldSignature;
        private final String descriptor;
        private final String sort;
        private final String smtSort;
        private final String solverTerm;
        private final String nullnessSolverTerm;

        private ConfiguredSourceInfo(String sourceKey, String sourceId,
                                     String sourcePhaseId,
                                     String sourceOccurrenceId,
                                     String fieldSignature,
                                     String descriptor, String sort,
                                     String smtSort, String solverTerm,
                                     String nullnessSolverTerm) {
            this.sourceKey = firstNonBlank(sourceKey);
            this.sourceId = firstNonBlank(sourceId);
            this.sourcePhaseId = firstNonBlank(sourcePhaseId);
            this.sourceOccurrenceId = firstNonBlank(sourceOccurrenceId);
            this.fieldSignature = firstNonBlank(fieldSignature);
            this.descriptor = firstNonBlank(descriptor);
            this.sort = firstNonBlank(sort);
            this.smtSort = firstNonBlank(smtSort);
            this.solverTerm = firstNonBlank(solverTerm);
            this.nullnessSolverTerm = firstNonBlank(nullnessSolverTerm);
        }

        private static ConfiguredSourceInfo decode(JsonObject row) {
            if (row == null || integer(row, "schemaVersion", -1) != 3
                    || !ConcolicSmtComposer
                    .CONFIGURED_SOURCE_MATERIALIZATION_KIND.equals(
                    string(row, "kind"))
                    || !ConcolicSmtComposer
                    .CONFIGURED_SOURCE_MATERIALIZATION_AUTHORITY.equals(
                    string(row, "authority"))) {
                return null;
            }
            ConfiguredSourceInfo result = new ConfiguredSourceInfo(
                    string(row, "sourceKey"),
                    string(row, "sourceId"),
                    string(row, "sourcePhaseId"),
                    string(row, "sourceOccurrenceId"),
                    string(row, "fieldSignature"),
                    string(row, "javaTypeDescriptor"),
                    string(row, "sort"), string(row, "smtSort"),
                    string(row, "solverTerm"),
                    string(row, "nullnessSolverTerm"));
            return result.sourceKey.isEmpty() || result.sourceId.isEmpty()
                    || result.sourcePhaseId.isEmpty()
                    || !result.sourcePhaseId.startsWith("SOURCE_PHASE.")
                    || result.sourceOccurrenceId.isEmpty()
                    || result.fieldSignature.isEmpty()
                    || result.descriptor.isEmpty()
                    || result.sort.isEmpty() || result.smtSort.isEmpty()
                    || result.solverTerm.isEmpty() ? null : result;
        }

        private PortInfo asPortInfo() {
            return new PortInfo(sourceId, descriptor, true,
                    fieldSignature);
        }
    }

    private static final class PortOccurrenceCatalog {
        private final List<PortOccurrenceInfo> occurrences =
                new ArrayList<>();

        private static PortOccurrenceCatalog from(JsonObject manifest) {
            PortOccurrenceCatalog result = new PortOccurrenceCatalog();
            for (JsonElement element : array(manifest,
                    "portOccurrences")) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                PortOccurrenceInfo occurrence = new PortOccurrenceInfo(
                        string(row, "portId"),
                        string(row, "occurrenceId"),
                        string(row, "sort"),
                        string(row, "portTerm"),
                        string(row, "solverTerm"),
                        string(row, "nullnessSolverTerm"),
                        bool(row, "supplied", false));
                if (occurrence.complete()) {
                    result.occurrences.add(occurrence);
                }
            }
            return result;
        }

        private List<PortOccurrenceInfo> sorted() {
            List<PortOccurrenceInfo> result = new ArrayList<>(occurrences);
            result.sort(Comparator
                    .comparing((PortOccurrenceInfo value) -> value.portId)
                    .thenComparing(value -> value.occurrenceId)
                    .thenComparing(value -> value.sort));
            return result;
        }
    }

    private static final class PortOccurrenceInfo {
        private final String portId;
        private final String occurrenceId;
        private final String sort;
        private final String portTerm;
        private final String solverTerm;
        private final String nullnessSolverTerm;
        private final boolean supplied;

        private PortOccurrenceInfo(String portId, String occurrenceId,
                                   String sort, String portTerm,
                                   String solverTerm,
                                   String nullnessSolverTerm,
                                   boolean supplied) {
            this.portId = firstNonBlank(portId);
            this.occurrenceId = firstNonBlank(occurrenceId);
            this.sort = firstNonBlank(sort);
            this.portTerm = firstNonBlank(portTerm);
            this.solverTerm = firstNonBlank(solverTerm);
            this.nullnessSolverTerm =
                    firstNonBlank(nullnessSolverTerm);
            this.supplied = supplied;
        }

        private boolean complete() {
            return !portId.isEmpty() && !occurrenceId.isEmpty()
                    && !sort.isEmpty() && !portTerm.isEmpty()
                    && !solverTerm.isEmpty();
        }
    }

    private static final class PortInfo {
        private final String id;
        private final String descriptor;
        private final boolean javaBoolean;
        private final boolean configuredSource;
        private final String fieldSignature;

        private PortInfo(String id, String javaType) {
            this(id, javaTypeDescriptor(javaType), false, "");
        }

        private PortInfo(String id, String descriptor,
                         boolean configuredSource,
                         String fieldSignature) {
            this.id = firstNonBlank(id);
            this.descriptor = javaTypeDescriptor(descriptor);
            this.javaBoolean = "Z".equals(descriptor)
                    || "Ljava/lang/Boolean;".equals(descriptor);
            this.configuredSource = configuredSource;
            this.fieldSignature = firstNonBlank(fieldSignature);
        }
    }

    private static final class Arguments {
        private Path smt;
        private Path manifest;
        private Path runtimePlan;
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
            result.runtimePlan = required(values, "runtime-plan");
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
                    || "runtime-plan".equals(key)
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

    static void validateArtifactBindings(Path smtPath, Path runtimePlanPath,
                                         JsonObject manifest)
            throws IOException {
        JsonObject actualSmt = artifact(smtPath);
        JsonObject actualRuntimePlan = artifact(runtimePlanPath);
        requireExactArtifact("composed SMT", object(manifest,
                "composedSmtArtifact"), actualSmt);
        requireExactArtifact("runtime plan", object(manifest,
                "runtimePlanArtifact"), actualRuntimePlan);
    }

    private static void requireExactArtifact(String label,
                                             JsonObject expected,
                                             JsonObject actual)
            throws IOException {
        if (expected.size() == 0
                || !string(actual, "path").equals(normalizedPath(
                string(expected, "path")))
                || !string(actual, "sha256").equals(string(expected,
                "sha256"))) {
            throw new IOException(label + " artifact fingerprint mismatch");
        }
    }

    private static String normalizedPath(String value) {
        if (firstNonBlank(value).isEmpty()) return "";
        return Paths.get(value).toAbsolutePath().normalize().toString();
    }

    private static long positiveLong(String value, long fallback) {
        return value == null ? fallback
                : Math.max(1L, Long.parseLong(value));
    }

    private static int positiveInt(String value, int fallback) {
        return value == null ? fallback
                : Math.max(1, Integer.parseInt(value));
    }

}
