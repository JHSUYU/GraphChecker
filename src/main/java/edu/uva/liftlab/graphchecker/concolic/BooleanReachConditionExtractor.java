package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.artifact;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sibling;
import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;

import java.io.File;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Projects a structurally complete candidate bug-path SMT formula onto its
 * free Boolean roots, and reports the reach condition as a DNF over them.
 */
public final class BooleanReachConditionExtractor {
    private static final int MAX_EXISTENTIAL_PERTURBATIONS = 32;
    /** Which guarded-read arm the model chose for the fatal predicate. */
    static final String FATAL_STATE_SELECTION = "fatalStateSelection";
    private static final String FATAL_STATE_SELECTION_KIND =
            "FATAL_READ_STATE_SELECTION";
    /**
     * An unsat every probed attempt owed to the driver's own frontier.
     *
     * <p>Not a solver status: z3 said {@code unsat} to each attempt, but
     * each refutation used a case selector this driver pinned, so the
     * valuation is undecided rather than refuted.</p>
     */
    static final String FRONTIER_PINNED_UNSAT = "FRONTIER_PINNED_UNSAT";

    /** A perturbation the root's own declared physics forbids. */
    static final String WINDOW_BOUNDARY = "WINDOW_BOUNDARY";
    /** Whether a witness's named mechanism is needed, or only decoration. */
    static final String MECHANISM_NECESSITY = "mechanismNecessity";
    /** Solved to be read, never to be believed: the Composer refused. */
    static final String EVIDENCE_ONLY = "evidenceOnly";
    /** How the Composer spells "this formula must not be satisfiable". */
    private static final String FAIL_CLOSED_MARKER = "; fail closed";
    private static final String COMPOSITION_NOT_ELIGIBLE =
            "COMPOSITION_MANIFEST_NOT_CANDIDATE_MODEL_ELIGIBLE";
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
        validateArtifactBindings(arguments.smt, arguments.runtimePlan,
                manifest);
        Z3Solver solver = new Z3Solver(arguments.z3,
                arguments.timeoutMillis,
                array(manifest, "caseSelectorPartitions"),
                array(manifest,
                        ComposedManifest.CONDITIONAL_CASE_PARTITIONS),
                arguments.workers);
        JsonObject report = extract(smt, manifest, solver,
                arguments.maxInputs, arguments.maxValuations,
                ClaimPolicy.WireFlowEvidence.read(arguments.mappings,
                        arguments.runtimePlan.toString()));
        report.add("solverAttempts", solver.attempts());
        ArtifactIO.replace(arguments.output, GSON.toJson(report)
                + System.lineSeparator());
        System.out.println(GSON.toJson(report));
        if (!"CANDIDATE_READY".equals(optionalString(report, "state"))) {
            System.exit(2);
        }
    }

    static JsonObject extract(String composedSmt, JsonObject manifest,
                              Z3Solver solver,
                              int maxInputs, int maxValuations)
            throws IOException, InterruptedException {
        return extract(composedSmt, manifest, solver, maxInputs,
                maxValuations, ClaimPolicy.WireFlowEvidence.none());
    }

    /**
     * The report, with the campaign claim decided from it.  Every exit from
     * {@link #reachReport} publishes a reach condition, so the one gate that
     * reads one runs here rather than in each caller: the report and the
     * claim it justifies are published together or not at all.
     */
    static JsonObject extract(String composedSmt, JsonObject manifest,
                              Z3Solver solver,
                              int maxInputs, int maxValuations,
                              ClaimPolicy.WireFlowEvidence flows)
            throws IOException, InterruptedException {
        JsonObject report = reachReport(composedSmt, manifest, solver,
                maxInputs, maxValuations);
        report.add(ClaimPolicy.CLAIM,
                ClaimPolicy.decide(manifest, report, flows));
        return report;
    }

    private static JsonObject reachReport(String composedSmt,
                                          JsonObject manifest,
                                          Z3Solver solver,
                                          int maxInputs, int maxValuations)
            throws IOException, InterruptedException {
        JsonObject report = new JsonObject();
        report.addProperty("schemaVersion", 4);
        report.addProperty("kind", "BOOLEAN_REACH_CONDITION_REPORT");
        boolean unsatClosureComplete = unsatClosureComplete(manifest);
        report.addProperty(ComposedManifest.UNSAT_CLOSURE_COMPLETE,
                unsatClosureComplete);
        JsonObject unsatClosureEvidence = object(manifest,
                ComposedManifest.UNSAT_CLOSURE_EVIDENCE);
        if (unsatClosureEvidence.size() > 0) {
            report.add(ComposedManifest.UNSAT_CLOSURE_EVIDENCE,
                    unsatClosureEvidence.deepCopy());
        }

        List<String> gaps = new ArrayList<>();
        validateCompositionAuthority(composedSmt, manifest, gaps);
        if (firstNonBlank(composedSmt).isEmpty()) {
            gaps.add("COMPOSED_SMT_EMPTY");
        }

        ConfiguredSourceCatalog configuredSources =
                ConfiguredSourceCatalog.from(manifest, gaps);
        ManualSymbolicRootCatalog manualRoots =
                ManualSymbolicRootCatalog.from(manifest, gaps);
        Discovery discovery = discover(composedSmt, configuredSources,
                manualRoots, gaps);
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
        // A composition the Composer refused is still worth solving: the
        // valuations, the arm the witness picks and the probes are how anyone
        // finds out *why* it was refused, and refusing to look is how a
        // refusal becomes a dead end. What must not happen is the answer
        // being mistaken for a verdict, so it is solved, marked, and can
        // never reach candidate authority.
        boolean evidenceOnly = onlyRefusedCompositionGap(gaps);
        if (!gaps.isEmpty() && !evidenceOnly) {
            return incomplete(report, gaps);
        }
        report.addProperty(EVIDENCE_ONLY, evidenceOnly);

        String base = SmtLibQueries.stripSolverCommands(
                composedSmt);
        // A refused composition fails its formula closed, so every valuation
        // of it is unsat by construction and answers nothing. Evidence-only
        // solving lifts that one marker -- and only that one -- so the
        // valuations, the arm the model picks and the probes can be read;
        // the verdict is already pinned below candidate authority, so what
        // comes back can inform a reader and can never accept a run.
        int failClosed = 0;
        if (evidenceOnly) {
            StringBuilder lifted = new StringBuilder(base.length());
            for (String line : base.split("\\R", -1)) {
                if (line.contains(FAIL_CLOSED_MARKER)) {
                    failClosed++;
                    continue;
                }
                lifted.append(line).append(System.lineSeparator());
            }
            base = lifted.toString();
        }
        report.addProperty("failClosedMarkersLifted", failClosed);
        // The one shape a witness can rest on that no root move names: an
        // associative read whose key nothing ever put.  The other used to be
        // a merged wire boundary none of whose arms the model satisfied --
        // there are no arms and no merge node now, and a wire value is the
        // producer's own expression.
        List<JsonObject> fatalArms = Collections.<JsonObject>emptyList();
        Set<String> fatalAbsentKeyTerms = fatalAbsentKeyTerms(manifest,
                fatalArms);
        List<String> witnessFreedomSymbols =
                new ArrayList<>(fatalAbsentKeyTerms);
        List<String> modelSymbols = new ArrayList<>(witnessFreedomSymbols);
        report.add(FATAL_STATE_SELECTION, asEvidence(fatalStateSelection(
                fatalArms, Collections.<String, String>emptyMap()),
                evidenceOnly));
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
                    discovery.existentialNonBooleanRootInputs,
                    modelSymbols);
            ConcolicConstraintSolver.SolverOutput result =
                    solver.check(query);
            String status = solver.lastStatus();
            JsonObject row = asEvidence(valuationRow(values, status),
                    evidenceOnly);
            // A reader has to be able to tell a causal verdict from one the
            // case frontier decided: these are the selectors this valuation
            // was solved under.
            row.add("pinnedCaseSelectors",
                    GSON.toJsonTree(solver.lastPinnedSelectors()));
            List<String> frontierPins = solver.lastFrontierPins();
            if (!frontierPins.isEmpty()) {
                row.add("frontierPinnedCore",
                        GSON.toJsonTree(frontierPins));
            }
            if ("sat".equals(status)) {
                satisfyingValuations.add(values.clone());
                Map<String, String> model =
                        ConcolicConstraintSolver.parseGetValues(result.stdout);
                if (!fatalArms.isEmpty() && satisfyingValuations.size() == 1) {
                    report.add(FATAL_STATE_SELECTION, asEvidence(
                            fatalStateSelection(fatalArms, model),
                            evidenceOnly));
                }
                JsonArray witness = existentialWitness(result,
                        discovery.existentialNonBooleanRootInputs);
                if (witness.size() > 0) {
                    row.add("existentialWitness", witness);
                }
                JsonArray mechanisms = witnessMechanisms(manifest, inputs,
                        values, witness);
                // The recorded write order is a mechanism too, and this
                // valuation's own model is what says whether it holds: the
                // fatal read took the program's last writer while the same
                // location is written again afterwards.
                JsonObject race = RecordedOrderRace.of(manifest, fatalArms,
                        model);
                if (race != null) {
                    mechanisms.add(race);
                }
                if (mechanisms.size() > 0) {
                    row.add("witnessMechanisms", mechanisms);
                }
                JsonArray witnessFreedoms = witnessFreedoms(manifest, model,
                        fatalAbsentKeyTerms);
                if (witnessFreedoms.size() > 0) {
                    row.add(WITNESS_FREEDOMS, witnessFreedoms);
                }
                if (witness.size() > 0) {
                    if (!existentialProbeAttempted) {
                        existentialProbeAttempted = true;
                        JsonArray perturbations = existentialPerturbations(
                                solver, query,
                                discovery.existentialNonBooleanRootInputs,
                                witness, clockWindows(manifest));
                        for (JsonElement perturbation : perturbations) {
                            existentialPerturbations.add(perturbation);
                            if ("unsat".equals(optionalString(
                                    perturbation.getAsJsonObject(),
                                    "status"))) {
                                rejectedExistentialPerturbation = true;
                            }
                        }
                    }
                }
                JsonArray modelWitness = symbolicWitness(
                        inputs, values, witness);
                if (modelWitness.size() > 0) {
                    JsonObject symbolicModel = new JsonObject();
                    symbolicModel.addProperty("schemaVersion", 1);
                    symbolicModel.addProperty("kind",
                            SYMBOLIC_VARIABLE_MODEL_KIND);
                    symbolicModel.addProperty("valuationOrdinal", ordinal);
                    symbolicModel.add("variables", modelWitness);
                    symbolicVariableModels.add(symbolicModel);
                }
            } else if (!"unsat".equals(status)) {
                row.addProperty("solverOutput", result.diagnostic());
                solverErrors++;
            }
            valuationRows.add(row);
        }

        report.add("valuations", valuationRows);
        JsonObject necessity = mechanismNecessity(solver, base, manifest,
                inputs, valuationRows);
        report.add(MECHANISM_NECESSITY, asEvidence(necessity, evidenceOnly));
        report.add(CLOCK_DECISIONS, asEvidence(clockDecisionWindow(solver,
                base, manifest, clockNecessary(necessity)), evidenceOnly));
        if (existentialPerturbations.size() > 0) {
            JsonObject probe = new JsonObject();
            probe.addProperty("authority",
                    "SOLVER_WITNESS_NEIGHBOR_PERTURBATION_V1");
            probe.addProperty("constrainsRootSpace",
                    rejectedExistentialPerturbation);
            probe.add("perturbations", existentialPerturbations);
            report.add("existentialRootProbe", asEvidence(probe,
                    evidenceOnly));
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
                    "INCONCLUSIVE_OPEN_PATH_CLOSURE");
        }
        String degeneracy = degeneracyCheck(formula, reachability,
                inputs.size(),
                discovery.existentialNonBooleanRootInputs.size(),
                rejectedExistentialPerturbation);
        reachCondition.addProperty("degeneracyCheck", degeneracy);
        report.add("reachCondition", reachCondition);
        JsonArray resultGaps = new JsonArray();
        for (String gap : gaps) {
            resultGaps.add(gap);
        }
        if (solverErrors > 0) {
            resultGaps.add("UNDECIDED_SOLVER_VALUATIONS:"
                    + solverErrors);
        }
        // A free symbolic root that never changes target reachability is not
        // a causal witness.  Preserve the solver's exact valuation table and
        // reachability finding, but refuse candidate authority so callers
        // cannot turn a disconnected root/target formula into SAT evidence.
        boolean unconstrainedRootSpace =
                "DEGENERATE_UNCONSTRAINED_ROOT_SPACE".equals(degeneracy);
        if (unconstrainedRootSpace) {
            resultGaps.add(degeneracy);
        }
        report.add("gaps", resultGaps);
        report.addProperty("state",
                complete && !unconstrainedRootSpace && !evidenceOnly
                        ? "CANDIDATE_READY" : "CANDIDATE_WITH_GAPS");
        return report;
    }

    /**
     * Whether the only thing wrong is that the Composer refused.
     *
     * <p>Every other gap says this stage cannot answer -- an empty formula, a
     * root catalog it could not read, a valuation space too large to
     * enumerate. That one says the answer may not be believed, which is a
     * different thing and leaves the answer worth having.</p>
     */
    private static boolean onlyRefusedCompositionGap(List<String> gaps) {
        if (gaps.isEmpty()) {
            return false;
        }
        for (String gap : gaps) {
            if (!COMPOSITION_NOT_ELIGIBLE.equals(gap)) {
                return false;
            }
        }
        return true;
    }

    /** Stamps one published row as read-only evidence. */
    private static JsonObject asEvidence(JsonObject row,
                                         boolean evidenceOnly) {
        if (evidenceOnly && row != null) {
            row.addProperty(EVIDENCE_ONLY, true);
        }
        return row;
    }

    /** States whether the degeneracy question was decided, and on what. */
    private static String degeneracyCheck(String formula,
                                          String reachability,
                                          int booleanRootCount,
                                          int existentialRootCount,
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
        return booleanRootCount == 0 ? "NOT_APPLICABLE_NO_FREE_ROOTS"
                : "DEGENERATE_UNCONSTRAINED_ROOT_SPACE";
    }

    private static void validateCompositionAuthority(
            String composedSmt, JsonObject manifest, List<String> gaps) {
        // This stage needs a composition that already declared itself
        // candidate-ready; re-deriving that verdict from its members would
        // be the second gate README forbids.
        boolean commonManifest = manifest != null
                && optionalInteger(manifest, "schemaVersion", -1) == 2
                && "CONCOLIC_COMPOSED_SMT".equals(optionalString(manifest, "kind"));
        if (!commonManifest
                || !"CANDIDATE_READY".equals(optionalString(manifest, "state"))) {
            gaps.add(COMPOSITION_NOT_ELIGIBLE);
        }
    }


    /** The Composer's single, internally consistent UNSAT closure claim. */
    private static boolean unsatClosureComplete(JsonObject manifest) {
        if (manifest == null
                || !optionalBool(manifest,
                ComposedManifest.UNSAT_CLOSURE_COMPLETE, false)
                || !ComposedManifest.FINAL_READY.equals(
                optionalString(manifest, ComposedManifest.FINAL_STATUS))) {
            return false;
        }
        JsonObject evidence = object(manifest,
                ComposedManifest.UNSAT_CLOSURE_EVIDENCE);
        JsonElement partial = evidence.get("partialProducerSummaryIds");
        return optionalInteger(evidence, "schemaVersion", -1) == 1
                && "UNSAT_CLOSURE_EVIDENCE".equals(
                optionalString(evidence, "kind"))
                && ComposedManifest.UNSAT_CLOSURE_AUTHORITY.equals(
                optionalString(evidence, "authority"))
                && optionalBool(evidence, "targetPathsClosed", false)
                && optionalBool(evidence, "finalStatusReady", false)
                && optionalInteger(evidence, "targetCoverageGapCount", -1) == 0
                && optionalInteger(evidence,
                "compositionCoverageGapCount", -1) == 0
                && partial != null && partial.isJsonArray()
                && partial.getAsJsonArray().size() == 0;
    }

    private static Discovery discover(String smt,
                                      ConfiguredSourceCatalog sources,
                                      ManualSymbolicRootCatalog manualRoots,
                                      List<String> gaps) {
        List<RootInput> roots = new ArrayList<>();
        List<RootInput> scalarRoots = new ArrayList<>();
        Map<String, String> claimedTerms = new LinkedHashMap<>();
        for (ConfiguredSourceInfo source : sources.sorted()) {
            ScalarEncoding encoding = ScalarEncoding.of(source.descriptor);
            if (encoding == null
                    || !encoding.occurrenceSort.equals(source.sort)
                    || !encoding.solverSort.equals(source.smtSort)
                    || !configuredSourceBindingDeclared(smt, source,
                    encoding)) {
                String subject = "configured-source:" + source.sourceId
                        + "@" + source.sourcePhaseId;
                gaps.add("CONFIGURED_SOURCE_TERM_NOT_DECLARED_OR_SORT_MISMATCH:"
                        + subject);
                continue;
            }
            claimedTerms.put(source.solverTerm, "CONFIGURED_SOURCE_FIELD");
            RootInput input = new RootInput(source);
            if (input.javaBoolean) {
                roots.add(input);
            } else {
                scalarRoots.add(input);
            }
        }
        for (ManualSymbolicRootGroup manualRoot : manualRoots.sorted()) {
            ManualSymbolicRootInfo local = manualRoot.canonical();
            ScalarEncoding encoding = ScalarEncoding.of(local.descriptor);
            String subject = "region-input:" + local.portId + "@"
                    + local.occurrenceId;
            if (encoding == null
                    || !encoding.occurrenceSort.equals(local.sort)
                    || !encoding.solverSort.equals(local.smtSort)
                    || !scalarBindingDeclared(smt, local.solverTerm,
                    local.nullnessSolverTerm, encoding)) {
                gaps.add("MANUAL_SYMBOLIC_ROOT_TERM_NOT_DECLARED_OR_SORT_MISMATCH:"
                        + subject);
                continue;
            }
            String held = claimedTerms.putIfAbsent(local.solverTerm,
                    "REGION_SYMBOLIC_INPUT");
            if (held != null) {
                gaps.add("SYMBOLIC_ROOT_TERM_AUTHORITY_CONFLICT:"
                        + local.solverTerm + ":" + held
                        + ":REGION_SYMBOLIC_INPUT");
                continue;
            }
            RootInput input = new RootInput(manualRoot);
            if (input.javaBoolean) {
                roots.add(input);
            } else {
                scalarRoots.add(input);
            }
        }
        // The solver term is the tiebreaker one mint site now needs: two
        // entries of one site share id, occurrence and phase and differ only
        // in the root they minted.
        Comparator<RootInput> byOccurrence = Comparator
                .comparing((RootInput value) -> value.inputKind)
                .thenComparing(value -> value.inputId())
                .thenComparing(value -> value.occurrenceId)
                .thenComparing(value -> value.sourcePhaseId)
                .thenComparing(value -> value.solverTerm);
        Collections.sort(roots, byOccurrence);
        Collections.sort(scalarRoots, byOccurrence);
        return new Discovery(roots, scalarRoots);
    }

    /** Whether the formula really declares the source term claimed. */
    private static boolean configuredSourceBindingDeclared(
            String smt, ConfiguredSourceInfo source,
            ScalarEncoding encoding) {
        return scalarBindingDeclared(smt, source.solverTerm,
                source.nullnessSolverTerm, encoding);
    }

    /** Whether the formula declares the exact scalar term in one root row. */
    private static boolean scalarBindingDeclared(
            String smt, String solverTerm, String nullnessSolverTerm,
            ScalarEncoding encoding) {
        if (!smt.contains("(declare-const " + solverTerm + " "
                + encoding.solverSort + ")")) {
            return false;
        }
        return encoding != ScalarEncoding.STRING
                || !nullnessSolverTerm.isEmpty()
                && smt.contains("(declare-const "
                + nullnessSolverTerm + " Bool)");
    }

    private static String valuationQuery(String base,
                                         List<RootInput> inputs,
                                         boolean[] values,
                                         List<RootInput> witnessRoots,
                                         List<String> modelSymbols) {
        StringBuilder query = new StringBuilder(base);
        for (int index = 0; index < inputs.size(); index++) {
            query.append("(assert ")
                    .append(inputs.get(index).literal(values[index]))
                    .append(")").append(System.lineSeparator());
        }
        query.append("(check-sat)").append(System.lineSeparator());
        List<String> wanted = new ArrayList<>();
        if (witnessRoots != null) {
            for (RootInput root : witnessRoots) {
                wanted.add(root.solverTerm);
                if (!root.nullnessSolverTerm.isEmpty()) {
                    wanted.add(root.nullnessSolverTerm);
                }
            }
        }
        if (modelSymbols != null) {
            wanted.addAll(modelSymbols);
        }
        if (!wanted.isEmpty()) {
            query.append("(get-value (");
            for (String symbol : wanted) {
                query.append(' ').append(symbol);
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
        private final JsonArray attempts = new JsonArray();
        private final List<List<String>> casePartitions = new ArrayList<>();
        /**
         * Selectors whose partition the formula only asserts conditionally.
         *
         * <p>An exactly-one the formula states unconditionally is already
         * true in every model, so fixing one of its members and enumerating
         * the alternatives decides nothing the formula had left open: an
         * unsat over that enumeration is the program's.  A conditional
         * partition is the opposite -- the formula leaves it to a marker, and
         * pinning a member answers for the marker.</p>
         */
        private final Set<String> conditionalSelectors =
                new LinkedHashSet<>();
        /** Whether any pinned partition is one the formula leaves open. */
        private final boolean frontierUnderReview;
        private final int workers;
        private int queryOrdinal;

        Z3Solver(String executable, long timeoutMillis,
                 JsonArray partitions, int workers) throws IOException {
            this(executable, timeoutMillis, partitions, new JsonArray(),
                    workers);
        }

        /**
         * @param conditional the partitions the formula does <em>not</em>
         *                    assert unconditionally.  Pinning a member of one
         *                    of those decides the condition that governs it,
         *                    so an unsat reached under such a pin is this
         *                    driver's and not the program's.  They are passed
         *                    in only so that an unsat can be checked against
         *                    them; they are never pinned.
         */
        Z3Solver(String executable, long timeoutMillis,
                 JsonArray partitions, JsonArray conditional, int workers)
                throws IOException {
            this.timeoutMillis = Math.max(1L, timeoutMillis);
            this.executable = resolveExecutable(firstNonBlank(executable,
                    "z3"));
            this.workers = Math.max(1, workers);
            for (JsonElement element : partitions) {
                if (!element.isJsonArray()) continue;
                List<String> partition = new ArrayList<>();
                for (JsonElement selector : element.getAsJsonArray()) {
                    if (selector.isJsonPrimitive()) {
                        partition.add(selector.getAsString());
                    }
                }
                if (!partition.isEmpty()
                        && partition.size() <= this.workers) {
                    casePartitions.add(partition);
                }
            }
            for (JsonElement element : conditional) {
                if (!element.isJsonArray()) continue;
                for (JsonElement selector : element.getAsJsonArray()) {
                    if (selector.isJsonPrimitive()) {
                        conditionalSelectors.add(selector.getAsString());
                    }
                }
            }
            boolean pinsCondition = false;
            for (List<String> partition : casePartitions) {
                for (String selector : partition) {
                    if (conditionalSelectors.contains(selector)) {
                        pinsCondition = true;
                        break;
                    }
                }
                if (pinsCondition) break;
            }
            this.frontierUnderReview = pinsCondition;
        }

        private volatile List<String> lastPinned = Collections.emptyList();
        /** The status of the last {@link #check}, frontier probes included. */
        private volatile String lastStatus = "";
        /** Pins the last all-unsat fan-out could not be exonerated from. */
        private volatile List<String> lastFrontierPins =
                Collections.emptyList();

        synchronized JsonArray attempts() {
            return attempts.deepCopy();
        }

        /** Case selectors the attempt that decided the last check pinned. */
        List<String> lastPinnedSelectors() {
            return new ArrayList<>(lastPinned);
        }

        /**
         * The verdict of the last {@link #check}, which is not the raw
         * solver status: an all-unsat fan-out whose every probed core rests
         * on this driver's own pins reports {@link #FRONTIER_PINNED_UNSAT}.
         */
        String lastStatus() {
            return lastStatus;
        }

        /** The pins a {@link #FRONTIER_PINNED_UNSAT} verdict rests on. */
        List<String> lastFrontierPins() {
            return new ArrayList<>(lastFrontierPins);
        }

        ConcolicConstraintSolver.SolverOutput check(String smt)
                throws IOException,
                InterruptedException {
            int currentQuery = queryOrdinal++;
            PartitionPlan plan = splitPartitions();
            lastStatus = "";
            lastFrontierPins = Collections.emptyList();
            if (plan.primary.isEmpty()) {
                lastPinned = Collections.emptyList();
                ConcolicConstraintSolver.SolverOutput single = attempt(
                        currentQuery, 0, "Z3", smt, timeoutMillis,
                        Collections.emptyList());
                lastStatus = single.status();
                return single;
            }
            lastPinned = Collections.emptyList();
            List<PartitionQuery> queries = conditionedQueries(smt,
                    plan.primary);
            if (!plan.refinement.isEmpty()) {
                queries.addAll(refinementQueries(queries,
                        plan.refinement));
                queries.sort(Comparator.comparingInt(
                        query -> query.smt.length()));
            }
            ExecutorService pool = Executors.newFixedThreadPool(
                    Math.min(workers, queries.size()));
            CompletionService<ConcolicConstraintSolver.SolverOutput>
                    completed = new ExecutorCompletionService<>(pool);
            long waves = (queries.size() + workers - 1L) / workers;
            long attemptTimeout = Math.max(1L, timeoutMillis / waves);
            for (int index = 0; index < queries.size(); index++) {
                final int ordinal = index;
                PartitionQuery query = queries.get(index);
                completed.submit(() -> attempt(currentQuery, ordinal,
                        "CASE_FRONTIER_" + ordinal, query.smt,
                        attemptTimeout, query.selectors));
            }
            ConcolicConstraintSolver.SolverOutput unsat = null;
            ConcolicConstraintSolver.SolverOutput undecided = null;
            ConcolicConstraintSolver.SolverOutput any = null;
            try {
                for (int index = 0; index < queries.size(); index++) {
                    ConcolicConstraintSolver.SolverOutput result;
                    try {
                        result = completed.take().get();
                    } catch (ExecutionException failed) {
                        Throwable cause = failed.getCause();
                        if (cause instanceof IOException) {
                            throw (IOException) cause;
                        }
                        if (cause instanceof InterruptedException) {
                            throw (InterruptedException) cause;
                        }
                        throw new IOException("partition solver failed", cause);
                    }
                    any = result;
                    if ("sat".equals(result.status())) {
                        lastStatus = "sat";
                        return result;
                    }
                    if ("unsat".equals(result.status())) unsat = result;
                    else undecided = result;
                }
            } finally {
                pool.shutdownNow();
                pool.awaitTermination(10, TimeUnit.SECONDS);
            }
            if (undecided != null) {
                lastStatus = undecided.status();
                return undecided;
            }
            if (unsat == null) {
                lastStatus = any == null ? "unknown" : any.status();
                return any;
            }
            // Every attempt refused this valuation.  An attempt that
            // refused it only because of the selectors this driver pinned
            // has said nothing about the program, so an unsat is published
            // only once one attempt's core is shown to be independent of
            // its own frontier.
            lastStatus = !frontierUnderReview ? "unsat"
                    : frontierVerdict(currentQuery, smt, queries,
                    attemptTimeout);
            return unsat;
        }

        /**
         * {@code unsat}, or {@code FRONTIER_PINNED_UNSAT} and the pins.
         *
         * <p>Probing stops at the first attempt whose core names none of its
         * pins: that one attempt already proves the refutation is the
         * program's.  Probes are bounded because the pinned case is the one
         * this exists to catch and it is also the one where no probe will
         * ever exonerate; an unexonerated valuation is reported undecided,
         * never unsat, so the bound can only withhold a verdict and never
         * manufacture one.</p>
         */
        private String frontierVerdict(int currentQuery, String smt,
                                       List<PartitionQuery> queries,
                                       long attemptTimeout)
                throws IOException, InterruptedException {
            List<String> pins = new ArrayList<>();
            int probes = 0;
            for (PartitionQuery query : queries) {
                if (query.pinLiterals.isEmpty()) return "unsat";
                if (probes >= frontierProbeLimit()) break;
                probes++;
                FrontierProbe probe = probeFrontier(currentQuery, probes - 1,
                        smt, query, attemptTimeout);
                List<String> decided = new ArrayList<>();
                for (String pin : probe.pins) {
                    if (conditionalSelectors.contains(pin)) decided.add(pin);
                }
                if (probe.decided && decided.isEmpty()) return "unsat";
                for (String pin : decided) {
                    if (!pins.contains(pin)) pins.add(pin);
                }
            }
            lastFrontierPins = pins;
            return FRONTIER_PINNED_UNSAT;
        }

        private int frontierProbeLimit() {
            return Math.max(4, workers);
        }

        private FrontierProbe probeFrontier(int currentQuery, int ordinal,
                                            String smt, PartitionQuery query,
                                            long attemptTimeout)
                throws IOException, InterruptedException {
            // The probe is built from the query before its pins were
            // asserted: an assumption competes with an identical assertion
            // for a place in the core, and only the assumption is named.
            String core = pinCoreQuery(smt, query.pinLiterals);
            long started = System.nanoTime();
            ConcolicConstraintSolver.SolverOutput result =
                    ConcolicConstraintSolver.run(executable, core,
                            attemptTimeout);
            long elapsedMillis = Math.max(0L,
                    (System.nanoTime() - started) / 1_000_000L);
            List<String> pins = "unsat".equals(result.status())
                    ? pinnedCoreSelectors(result.stdout, query.pinLiterals)
                    : Collections.<String>emptyList();
            JsonObject row = new JsonObject();
            row.addProperty("queryOrdinal", currentQuery);
            row.addProperty("attemptOrdinal", ordinal);
            row.addProperty("strategy", "FRONTIER_CORE_" + ordinal);
            row.addProperty("solverQuerySha256", ArtifactIO.sha256(core));
            row.add("selectedCaseSelectors",
                    GSON.toJsonTree(query.selectors));
            row.addProperty("timeoutMillis", attemptTimeout);
            row.addProperty("elapsedMillis", elapsedMillis);
            row.addProperty("status", result.status());
            row.add("unsatCorePinnedSelectors", GSON.toJsonTree(pins));
            synchronized (this) {
                attempts.add(row);
            }
            return new FrontierProbe("unsat".equals(result.status()), pins);
        }

        private ConcolicConstraintSolver.SolverOutput attempt(
                int currentQuery, int ordinal, String strategy,
                String query, long attemptTimeout,
                List<String> selectedCaseSelectors)
                throws IOException, InterruptedException {
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
            row.addProperty("solverQuerySha256", ArtifactIO.sha256(query));
            if (!selectedCaseSelectors.isEmpty()) {
                row.add("selectedCaseSelectors",
                        GSON.toJsonTree(selectedCaseSelectors));
            }
            row.addProperty("timeoutMillis", attemptTimeout);
            row.addProperty("elapsedMillis", elapsedMillis);
            row.addProperty("status", result.status());
            // The attempt that finds a model is the one whose pin the verdict
            // rests on; an unsat over every attempt rests on none of them.
            if ("sat".equals(result.status())) {
                lastPinned = new ArrayList<>(selectedCaseSelectors);
            }
            synchronized (this) {
                attempts.add(row);
            }
            return result;
        }

        private PartitionPlan splitPartitions() {
            List<List<String>> selected = new ArrayList<>();
            long combinations = 1L;
            long limit = (long) workers * workers;
            List<String> refinement = Collections.emptyList();
            for (List<String> partition : casePartitions) {
                if (partition.size() == 1) {
                    selected.add(partition);
                    continue;
                }
                if (combinations > limit / partition.size()) {
                    if (refinement.isEmpty()) refinement = partition;
                    continue;
                }
                selected.add(partition);
                combinations *= partition.size();
            }
            return new PartitionPlan(selected, refinement);
        }

        private static String condition(String smt, List<String> partition,
                                        int chosen) {
            return constrainSelectors(smt,
                    Collections.singletonList(partition),
                    Collections.singletonList(chosen));
        }

        /** Fixes case selectors without rewriting the composed SMT. */
        private static String constrainSelectors(
                String smt, List<List<String>> partitions,
                List<Integer> chosen) {
            StringBuilder constraints = new StringBuilder();
            for (int partitionIndex = 0;
                 partitionIndex < partitions.size(); partitionIndex++) {
                List<String> partition = partitions.get(partitionIndex);
                int selected = chosen.get(partitionIndex);
                for (int selectorIndex = 0;
                     selectorIndex < partition.size(); selectorIndex++) {
                    String selector = partition.get(selectorIndex);
                    constraints.append("(assert ");
                    if (selectorIndex != selected) constraints.append("(not ");
                    constraints.append(selector);
                    if (selectorIndex != selected) constraints.append(')');
                    constraints.append(")").append(System.lineSeparator());
                }
            }
            int solverCommand = smt.indexOf("(check-sat");
            if (solverCommand < 0) solverCommand = smt.length();
            return new StringBuilder(smt.length() + constraints.length())
                    .append(smt, 0, solverCommand)
                    .append(constraints)
                    .append(smt, solverCommand, smt.length())
                    .toString();
        }

        /** The pin literals one assignment fixes, in partition order. */
        private static List<String> pinLiterals(
                List<List<String>> partitions, List<Integer> chosen) {
            List<String> literals = new ArrayList<>();
            for (int partitionIndex = 0;
                 partitionIndex < partitions.size(); partitionIndex++) {
                List<String> partition = partitions.get(partitionIndex);
                int selected = chosen.get(partitionIndex);
                for (int index = 0; index < partition.size(); index++) {
                    literals.add(index == selected ? partition.get(index)
                            : "(not " + partition.get(index) + ")");
                }
            }
            return literals;
        }

        /**
         * The same query, with the pins assumed instead of asserted.
         *
         * <p>Everything from the composed formula onwards is unchanged; only
         * the frontier moves from {@code assert} into the {@code check-sat}
         * assumption list, where z3 will name in the core exactly those
         * assumptions the refutation used.  A core that names none of them is
         * the only evidence that an unsat is the program's and not the
         * driver's.</p>
         */
        private static String pinCoreQuery(String smt,
                                           List<String> literals) {
            int solverCommand = smt.indexOf("(check-sat");
            if (solverCommand < 0) solverCommand = smt.length();
            StringBuilder query = new StringBuilder(smt.length() + 256);
            query.append("(set-option :produce-unsat-cores true)")
                    .append(System.lineSeparator());
            query.append(smt, 0, solverCommand);
            query.append("(check-sat");
            for (String literal : literals) {
                query.append(' ').append(literal);
            }
            query.append(')').append(System.lineSeparator());
            query.append("(get-unsat-core)").append(System.lineSeparator());
            return query.toString();
        }

        /** The pinned selectors an unsat core named, in pin order. */
        static List<String> pinnedCoreSelectors(String stdout,
                                                List<String> literals) {
            Set<String> names = new LinkedHashSet<>();
            for (String literal : literals) {
                String trimmed = literal.trim();
                if (trimmed.startsWith("(not ") && trimmed.endsWith(")")) {
                    trimmed = trimmed.substring(5, trimmed.length() - 1)
                            .trim();
                }
                if (!trimmed.isEmpty()) names.add(trimmed);
            }
            List<String> found = new ArrayList<>();
            if (stdout == null) return found;
            int newline = stdout.indexOf('\n');
            String body = newline < 0 ? "" : stdout.substring(newline + 1);
            for (String token : body.split("[^A-Za-z0-9_.$~^?/+=<>*&%!@-]+")) {
                if (names.contains(token) && !found.contains(token)) {
                    found.add(token);
                }
            }
            return found;
        }

        private static List<PartitionQuery> conditionedQueries(
                String smt, List<List<String>> partitions) {
            List<List<Integer>> assignments = new ArrayList<>();
            assignments.add(Collections.emptyList());
            for (List<String> partition : partitions) {
                List<List<Integer>> expanded = new ArrayList<>();
                for (List<Integer> assignment : assignments) {
                    for (int chosen = 0; chosen < partition.size(); chosen++) {
                        List<Integer> next = new ArrayList<>(assignment);
                        next.add(chosen);
                        expanded.add(next);
                    }
                }
                assignments = expanded;
            }
            List<PartitionQuery> result = new ArrayList<>();
            for (List<Integer> assignment : assignments) {
                List<String> selectors = new ArrayList<>();
                for (int index = 0; index < partitions.size(); index++) {
                    List<String> partition = partitions.get(index);
                    int chosen = assignment.get(index);
                    selectors.add(partition.get(chosen));
                }
                result.add(new PartitionQuery(constrainSelectors(
                        smt, partitions, assignment), selectors,
                        pinLiterals(partitions, assignment)));
            }
            result.sort(Comparator.comparingInt(query -> query.smt.length()));
            return result;
        }

        private List<PartitionQuery> refinementQueries(
                List<PartitionQuery> parents, List<String> partition) {
            List<PartitionQuery> result = new ArrayList<>();
            for (int parentIndex = 0;
                 parentIndex < Math.min(workers, parents.size());
                 parentIndex++) {
                PartitionQuery parent = parents.get(parentIndex);
                for (int chosen = 0; chosen < partition.size(); chosen++) {
                    List<String> selectors = new ArrayList<>(
                            parent.selectors);
                    selectors.add(partition.get(chosen));
                    List<String> literals = new ArrayList<>(
                            parent.pinLiterals);
                    literals.addAll(pinLiterals(
                            Collections.singletonList(partition),
                            Collections.singletonList(chosen)));
                    result.add(new PartitionQuery(
                            condition(parent.smt, partition, chosen),
                            selectors, literals));
                }
            }
            return result;
        }

        private static final class PartitionPlan {
            private final List<List<String>> primary;
            private final List<String> refinement;

            private PartitionPlan(List<List<String>> primary,
                                  List<String> refinement) {
                this.primary = primary;
                this.refinement = refinement;
            }
        }

        private static final class PartitionQuery {
            private final String smt;
            private final List<String> selectors;
            /**
             * The same pins as {@code check-sat} assumptions.
             *
             * <p>Asserting a pin and assuming it constrain the same models,
             * but only an assumption comes back named in the unsat core.
             * That is the whole question this class has to be able to answer:
             * whether an unsat rests on the program or on the frontier this
             * driver chose.</p>
             */
            private final List<String> pinLiterals;

            private PartitionQuery(String smt, List<String> selectors,
                                   List<String> pinLiterals) {
                this.smt = smt;
                this.selectors = selectors;
                this.pinLiterals = pinLiterals;
            }
        }

        /** One unsat attempt, and what its core says the unsat rests on. */
        private static final class FrontierProbe {
            private final boolean decided;
            private final List<String> pins;

            private FrontierProbe(boolean decided, List<String> pins) {
                this.decided = decided;
                this.pins = pins;
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

        private Discovery(List<RootInput> rootInputs,
                          List<RootInput> existentialNonBooleanRootInputs) {
            this.rootInputs = rootInputs;
            this.existentialNonBooleanRootInputs =
                    existentialNonBooleanRootInputs;
        }
    }

    private static final class RootInput {
        private final String inputKind;
        private final String sourceId;
        private final String portId;
        private final String descriptor;
        private final boolean javaBoolean;
        private final String fieldSignature;
        private final String occurrenceId;
        private final String solverTerm;
        private final String nullnessSolverTerm;
        private final String sourcePhaseId;
        private final String sourceKey;
        private final String sourceIdentity;
        private final String sourceIdentityAuthority;
        private final List<ManualSymbolicRootInfo> manualAliases;

        private RootInput(ConfiguredSourceInfo source) {
            this.inputKind = "CONFIGURED_SOURCE_FIELD";
            this.sourceId = source.sourceId;
            this.portId = "";
            this.descriptor = source.descriptor;
            this.javaBoolean = ScalarEncoding.of(descriptor)
                    == ScalarEncoding.BOOL;
            this.fieldSignature = source.fieldSignature;
            this.occurrenceId = source.sourceOccurrenceId;
            this.solverTerm = source.solverTerm;
            this.nullnessSolverTerm = source.nullnessSolverTerm;
            this.sourcePhaseId = source.sourcePhaseId;
            this.sourceKey = source.sourceKey;
            this.sourceIdentity = "";
            this.sourceIdentityAuthority = "";
            this.manualAliases = Collections.emptyList();
        }

        private RootInput(ManualSymbolicRootGroup root) {
            ManualSymbolicRootInfo local = root.canonical();
            this.inputKind = "REGION_SYMBOLIC_INPUT";
            this.sourceId = "";
            this.portId = local.portId;
            this.descriptor = local.descriptor;
            this.javaBoolean = ScalarEncoding.of(descriptor)
                    == ScalarEncoding.BOOL;
            this.fieldSignature = local.fieldSignature;
            this.occurrenceId = local.occurrenceId;
            this.solverTerm = local.solverTerm;
            this.nullnessSolverTerm = local.nullnessSolverTerm;
            this.sourcePhaseId = "";
            this.sourceKey = "";
            this.sourceIdentity = local.sourceIdentity;
            this.sourceIdentityAuthority = local.sourceIdentityAuthority;
            this.manualAliases = root.sortedAliases();
        }

        private String inputId() {
            return "REGION_SYMBOLIC_INPUT".equals(inputKind)
                    ? portId : sourceId;
        }

        private String literal(boolean value) {
            return "(= " + solverTerm + " "
                    + (value ? "true" : "false") + ")";
        }

        private List<String> neighboringLiterals(String value) {
            ScalarEncoding encoding = ScalarEncoding.of(descriptor);
            return encoding == null ? Collections.<String>emptyList()
                    : encoding.neighboringLiterals(value);
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("inputKind", inputKind);
            if ("REGION_SYMBOLIC_INPUT".equals(inputKind)) {
                result.addProperty("portId", portId);
                result.addProperty("occurrenceId", occurrenceId);
                if (!fieldSignature.isEmpty()) {
                    result.addProperty("fieldSignature", fieldSignature);
                }
                result.addProperty("sourceIdentity", sourceIdentity);
                result.addProperty("sourceIdentityAuthority",
                        sourceIdentityAuthority);
                JsonArray aliases = new JsonArray();
                for (ManualSymbolicRootInfo alias : manualAliases) {
                    JsonObject row = new JsonObject();
                    row.addProperty("portId", alias.portId);
                    row.addProperty("occurrenceId", alias.occurrenceId);
                    if (!alias.fieldSignature.isEmpty()) {
                        row.addProperty("fieldSignature",
                                alias.fieldSignature);
                    }
                    aliases.add(row);
                }
                result.add("aliases", aliases);
            } else {
                result.addProperty("sourceKey", sourceKey);
                result.addProperty("sourceId", sourceId);
                result.addProperty("sourceOccurrenceId", occurrenceId);
                result.addProperty("sourcePhaseId", sourcePhaseId);
                result.addProperty("fieldSignature", fieldSignature);
            }
            result.addProperty("javaTypeDescriptor", descriptor);
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
        private final String descriptor;

        ScalarEncoding(String occurrenceSort, String solverSort,
                       String descriptor) {
            this.occurrenceSort = occurrenceSort;
            this.solverSort = solverSort;
            this.descriptor = descriptor;
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

        /**
         * The two integer values either side of this valuation, as SMT
         * literals: what a perturbation may try next without leaving the
         * type.  The range belongs to the Java type, so it is read from the
         * primitive semantics rather than restated here.
         */
        private List<String> neighboringLiterals(String literal) {
            BigInteger value = parseSmtInteger(literal);
            BigInteger[] range =
                    JavaPrimitiveSmtSemantics.integralRange(descriptor);
            if (value == null || range == null) {
                return Collections.emptyList();
            }
            List<String> result = new ArrayList<>();
            if (value.compareTo(range[0]) > 0) {
                result.add(formatSmtInteger(
                        value.subtract(BigInteger.ONE)));
            }
            if (value.compareTo(range[1]) < 0) {
                result.add(formatSmtInteger(
                        value.add(BigInteger.ONE)));
            }
            return result;
        }

        static BigInteger parseSmtInteger(String literal) {
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
    /**
     * What this witness changed about the world, in mechanism terms.
     *
     * <p>A model is a list of numbers until it is read next to what those
     * roots actually returned.  Each root the witness moved off its recorded
     * value is reported as the mechanism it is: a Boolean marker flipped is
     * an injected fault, a wall clock moved is clock skew of that many
     * milliseconds on that node, anything else is a plain root move.  A root
     * the witness left at its recorded value contributes nothing, so a reader
     * sees "RPC fault" or "clock skew of X ms on node Y" rather than a wall
     * of assignments.</p>
     */
    private static JsonArray witnessMechanisms(
            JsonObject manifest, List<RootInput> booleanInputs,
            boolean[] booleanValues, JsonArray existentialWitness) {
        JsonArray mechanisms = new JsonArray();
        Map<String, JsonObject> recorded = new LinkedHashMap<>();
        for (JsonElement element : array(manifest,
                ComposedManifest.RECORDED_ROOT_VALUES)) {
            if (!element.isJsonObject()) continue;
            JsonObject ledger = element.getAsJsonObject();
            String term = optionalString(ledger, "solverTerm");
            if (!term.isEmpty()) recorded.put(term, ledger);
        }
        if (recorded.isEmpty()) return mechanisms;
        Map<String, String> witnessValues = new LinkedHashMap<>();
        for (int index = 0; index < booleanInputs.size()
                && index < booleanValues.length; index++) {
            witnessValues.put(booleanInputs.get(index).solverTerm,
                    Boolean.toString(booleanValues[index]));
        }
        for (JsonElement element : existentialWitness) {
            if (!element.isJsonObject()) continue;
            JsonObject root = element.getAsJsonObject();
            witnessValues.put(optionalString(root, "solverTerm"),
                    optionalString(root, "value"));
        }
        for (Map.Entry<String, String> assigned : witnessValues.entrySet()) {
            JsonObject ledger = recorded.get(assigned.getKey());
            if (ledger == null) continue;
            String was = optionalString(ledger, "recordedValue");
            String now = normalizeIntegral(assigned.getValue());
            if (was.isEmpty() || now.isEmpty() || was.equals(now)) continue;
            JsonObject mechanism = new JsonObject();
            mechanism.addProperty("sourceKey",
                    optionalString(ledger, "sourceKey"));
            mechanism.addProperty("siteId", optionalString(ledger, "siteId"));
            mechanism.addProperty("solverTerm", assigned.getKey());
            mechanism.addProperty("recordedValue", was);
            mechanism.addProperty("witnessValue", now);
            boolean clock = optionalBool(ledger, "wallClock", false);
            if (clock) {
                mechanism.addProperty("kind", "CLOCK_SKEW");
                Long delta = skewMillis(was, now);
                if (delta != null) {
                    mechanism.addProperty("skewMillis", delta);
                }
            } else if ("true".equals(was) || "false".equals(was)) {
                mechanism.addProperty("kind", "MARKER_FLIPPED");
            } else {
                mechanism.addProperty("kind", "ROOT_MOVED");
            }
            mechanisms.add(mechanism);
        }
        return mechanisms;
    }

    /** {@code (- 5)} is how a model spells -5; the ledger spells it "-5". */
    private static String normalizeIntegral(String value) {
        String text = value == null ? "" : value.trim();
        if (text.startsWith("(-") && text.endsWith(")")) {
            return "-" + text.substring(2, text.length() - 1).trim();
        }
        return text;
    }

    private static Long skewMillis(String recorded, String witness) {
        try {
            return Long.parseLong(normalizeIntegral(witness))
                    - Long.parseLong(recorded.trim());
        } catch (NumberFormatException notIntegral) {
            return null;
        }
    }

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

    /** Every materializable symbolic root in one satisfying model. */
    private static JsonArray symbolicWitness(
            List<RootInput> booleanRoots, boolean[] booleanValues,
            JsonArray existentialWitness) {
        JsonArray result = new JsonArray();
        for (int index = 0; index < booleanRoots.size(); index++) {
            RootInput root = booleanRoots.get(index);
            JsonObject row = root.toJson();
            row.addProperty("value", booleanValues[index]);
            result.add(row);
        }
        for (JsonElement element : existentialWitness) {
            if (element.isJsonObject()) result.add(element.deepCopy());
        }
        return result;
    }

    /**
     * Looks for a rejected point adjacent to an already satisfying scalar
     * witness: one unsat neighbour proves the root space is constrained.
     */
    /**
     * Whether the mechanism a witness names is needed, or only decoration.
     *
     * <p>An experiment that injects a fault marker and finds both polarities
     * satisfiable can still be a real finding, if the composition can say what
     * else reached the target in the polarity that has no fault. A witness
     * always names something -- a model assigns every free root, so a clock
     * that was free to move will have moved -- and the question is whether the
     * target needed it to. One query answers that: put the mechanism's roots
     * back to what they actually recorded, keep the marker at the polarity
     * being explained, and ask again. Still satisfiable means the mechanism
     * was decoration and the polarity is explained by nothing.</p>
     *
     * <p>Clock rows are pinned as one group. A wall clock is not a mechanism
     * by itself -- "these nodes' clocks disagreed" is the mechanism -- so
     * pinning them one at a time would ask about a skew nobody claimed.</p>
     */
    /** Where the model-decided freedom of one valuation is published. */
    public static final String WITNESS_FREEDOMS = "witnessFreedoms";

    /**
     * What this model was free to choose that no mechanism accounts for.
     *
     * <p>Neither shape is visible in the root witness, because neither moves
     * a root.  A merged consumer boundary whose dispatch no partition makes
     * total takes its unbound fall-through whenever the model satisfies none
     * of its arms: the value the wire carried is then whatever the solver
     * liked.  An associative read whose key matched no {@code PUT} of its
     * mutation chain, over a state reconstructed from a snapshot, answers
     * null because the map never held that key -- a statement about the
     * query, not about the program.</p>
     */
    private static JsonArray witnessFreedoms(
            JsonObject manifest, Map<String, String> model,
            Set<String> fatalAbsentKeyTerms) {
        JsonArray rows = new JsonArray();
        for (JsonElement element
                : array(manifest, ComposedManifest.ABSENT_KEY_DEFAULTS)) {
            if (!element.isJsonObject()) continue;
            JsonObject absent = element.getAsJsonObject();
            String term = optionalString(absent, "solverTerm");
            // Only the reads whose value the target predicate tests were
            // asked for above; anything else has no value in this model.
            if (!fatalAbsentKeyTerms.contains(term)
                    || !"true".equals(model.get(term))) {
                continue;
            }
            JsonObject row = new JsonObject();
            row.addProperty("code", WitnessLegitimacy.ABSENT_KEY_DEFAULT);
            row.addProperty("subject", term);
            row.addProperty("detail",
                    "an associative read the target predicate tests answered"
                            + " out of the absent-key default: its key "
                            + optionalString(absent, "keyTerm")
                            + " matched no PUT of the chain and the"
                            + " reconstructed initial state does not hold"
                            + " it, so the null is the empty map's answer"
                            + " rather than anything the program did");
            rows.add(row);
        }
        return rows;
    }

    /**
     * The absent-key terms that belong to the read the target predicate
     * tests.
     *
     * <p>A row is the fatal read's when it names that read's identity, or
     * when the guard it was lowered under carries one of the fatal read's
     * arm selectors -- the container chain of a state read is lowered inside
     * the arm that selects the state, so the arm is what the row records
     * when the read identity itself was not in scope.</p>
     */
    private static Set<String> fatalAbsentKeyTerms(JsonObject manifest,
                                                   List<JsonObject> fatalArms) {
        Set<String> identities = new LinkedHashSet<>();
        Set<String> selectors = new LinkedHashSet<>();
        for (JsonObject arm : fatalArms) {
            String identity = optionalString(arm, "readIdentity");
            if (!identity.isEmpty()) identities.add(identity);
            String selector = optionalString(arm, "selector");
            if (!selector.isEmpty()) selectors.add(selector);
        }
        Set<String> terms = new LinkedHashSet<>();
        for (JsonElement element
                : array(manifest, ComposedManifest.ABSENT_KEY_DEFAULTS)) {
            if (!element.isJsonObject()) continue;
            JsonObject absent = element.getAsJsonObject();
            String term = optionalString(absent, "solverTerm");
            if (term.isEmpty()) continue;
            boolean fatal = identities.contains(optionalString(absent,
                    "readIdentity"));
            String guard = optionalString(absent, "guard");
            for (String selector : selectors) {
                if (fatal) break;
                fatal = guard.contains(selector);
            }
            if (fatal) terms.add(term);
        }
        return terms;
    }


    private static boolean boundedSymbolAt(String line, int at, int length) {
        int end = at + length;
        return (at == 0 || !Character.isLetterOrDigit(line.charAt(at - 1))
                && line.charAt(at - 1) != '_')
                && (end >= line.length()
                || !Character.isLetterOrDigit(line.charAt(end))
                && line.charAt(end) != '_');
    }


    /** Where the clock-decision window probe is published. */
    static final String CLOCK_DECISIONS = "clockDecisions";
    /**
     * A comparison on the fatal slice that involves a wall-clock root and
     * takes one polarity only within the window the composition anchors the
     * clock in, while the other polarity becomes satisfiable once the window
     * is widened: the mechanism this clock could decide lies outside the
     * window, and no witness can show it at the configured skew.
     */
    public static final String CLOCK_DECISION_OUTSIDE_WINDOW =
            "CLOCK_DECISION_OUTSIDE_WINDOW";
    /**
     * A comparison on the fatal slice that involves a wall-clock root and
     * still refuses one polarity when the clock is left unbounded: no window
     * admits it, so the window is not what refuses it.  What refuses it is
     * the rest of the composition -- in practice the recorded case path
     * condition, which replays the observed outcome of the very branch the
     * clock decides, so the region can only take a path some replay
     * observed.  Widening the window cannot help; a flipped case for that
     * branch is what is missing.
     */
    public static final String CLOCK_DECISION_REFUSED_WITHOUT_WINDOW =
            "CLOCK_DECISION_REFUSED_WITHOUT_WINDOW";
    /**
     * Comparison atoms probed per run; a slice rarely has more, and never
     * fewer than one per declared clock, so a two-node mechanism cannot have
     * the node that decides it fall off the end of the list.
     */
    private static final int MAX_CLOCK_DECISION_ATOMS = 8;
    /** Window doublings tried: 5 min becomes 5 h 20 min at the sixth. */
    private static final int MAX_CLOCK_WINDOW_DOUBLINGS = 6;
    /** Solver checks the probe may spend in total. */
    private static final int MAX_CLOCK_DECISION_CHECKS = 64;

    /** Whether the necessity ledger holds a necessary clock group. */
    private static boolean clockNecessary(JsonObject necessity) {
        for (JsonElement element : array(necessity, "mechanisms")) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if ("CLOCK_SKEW".equals(optionalString(row, "mechanism"))
                    && optionalBool(row, "necessary", false)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Which comparisons a clock root takes part in, and whether the window
     * lets each be decided either way.
     *
     * <p>The clock window is a physical bound, not a pin: a clock may move
     * five minutes off its recording and no further.  A mechanism whose time
     * scale is longer -- a key that expires twenty hours out -- is then
     * unreachable by construction, and until now nothing said so: the
     * formula was simply unsat, or sat through something else.  This probe
     * names the comparisons the window decides.  For each comparison atom
     * over a clock term it asks the solver for both polarities inside the
     * window; when one polarity is unsat it widens every clock's window by
     * doublings until that polarity is sat, and reports the first width that
     * admits it as the advance the decision needs.</p>
     *
     * <p>Skipped when the necessity ledger already shows a clock decision
     * to be necessary: the window then admitted the mechanism, and the
     * probe would only spend solver time confirming it.  An atom is asserted
     * on its own, without the guards it sits under, so a comparison whose
     * operands are free where it is not evaluated may read as decidable
     * either way; that loses a gap, never invents one.</p>
     */
    private static JsonObject clockDecisionWindow(
            Z3Solver solver, String base, JsonObject manifest,
            boolean clockNecessary)
            throws IOException, InterruptedException {
        JsonObject result = new JsonObject();
        result.addProperty("authority", "CLOCK_DECISION_WINDOW_PROBE_V1");
        JsonObject physics = object(manifest, ClockRootPhysics.MANIFEST_FIELD);
        long skew = Math.max(0L, optionalLongInteger(physics,
                "clockSkewMillis", ClockRootPhysics.DEFAULT_SKEW_MILLIS));
        result.addProperty("windowMillis", skew);
        JsonArray rows = new JsonArray();
        result.add("decisions", rows);
        result.addProperty("outsideWindow", 0);
        Map<String, JsonObject> clocks = new LinkedHashMap<>();
        for (JsonElement element : array(physics, "clockReads")) {
            if (!element.isJsonObject()) continue;
            JsonObject read = element.getAsJsonObject();
            String term = optionalString(read, "solverTerm");
            if (!term.isEmpty() && read.has("recordedValue")) {
                clocks.put(term, read);
            }
        }
        if (clocks.isEmpty()) {
            result.addProperty("probed", false);
            result.addProperty("reason", "NO_CLOCK_ROOT");
            return result;
        }
        if (clockNecessary) {
            result.addProperty("probed", false);
            result.addProperty("reason", "CLOCK_DECISION_NECESSARY");
            return result;
        }
        List<String> atoms = clockComparisonAtoms(base, clocks.keySet(),
                Math.max(MAX_CLOCK_DECISION_ATOMS, 2 * clocks.size()));
        result.addProperty("probed", true);
        result.addProperty("atoms", atoms.size());
        int checks = 0;
        int outside = 0;
        int refused = 0;
        for (String atom : atoms) {
            if (checks + 2 > MAX_CLOCK_DECISION_CHECKS) {
                result.addProperty("budgetExhausted", true);
                break;
            }
            JsonObject row = new JsonObject();
            row.addProperty("atom", atom);
            JsonArray terms = new JsonArray();
            JsonArray sites = new JsonArray();
            for (Map.Entry<String, JsonObject> clock : clocks.entrySet()) {
                if (!containsSymbol(atom, clock.getKey())) continue;
                terms.add(clock.getKey());
                sites.add(firstNonBlank(optionalString(clock.getValue(),
                        "sourceKey")) + " " + optionalString(
                        clock.getValue(), "siteId"));
            }
            row.add("clockTerms", terms);
            row.add("sites", sites);
            String holds = probeStatus(solver, base, atom);
            String fails = probeStatus(solver, base, "(not " + atom + ")");
            checks += 2;
            row.addProperty("holdsWithinWindow", holds);
            row.addProperty("failsWithinWindow", fails);
            String blocked = "unsat".equals(holds) && "sat".equals(fails)
                    ? atom : "unsat".equals(fails) && "sat".equals(holds)
                    ? "(not " + atom + ")" : "";
            if (blocked.isEmpty()) {
                row.addProperty("decidedByWindow", false);
                rows.add(row);
                continue;
            }
            row.addProperty("decidedByWindow", true);
            row.addProperty("blockedPolarity", blocked);
            // Before blaming the window, ask the same polarity with no window
            // at all.  A polarity the unbounded clock cannot take is refused
            // by the rest of the composition -- in practice by a region case
            // path condition replaying the branch this clock decides -- and
            // no widening would ever admit it, so the ladder below would burn
            // six checks to arrive at a number that means nothing.
            String unbounded = "";
            if (checks + 1 <= MAX_CLOCK_DECISION_CHECKS) {
                unbounded = probeStatus(solver,
                        dropClockWindows(base, clocks, skew), blocked);
                checks++;
            } else {
                result.addProperty("budgetExhausted", true);
            }
            row.addProperty("unboundedClockStatus", unbounded);
            if ("unsat".equals(unbounded)) {
                row.addProperty("code",
                        CLOCK_DECISION_REFUSED_WITHOUT_WINDOW);
                row.add("pinnedBy", casePathConditionsOver(base, atom));
                refused++;
                rows.add(row);
                continue;
            }
            long admitted = -1L;
            long widest = skew;
            for (int doubling = 1; doubling <= MAX_CLOCK_WINDOW_DOUBLINGS;
                    doubling++) {
                if (checks + 1 > MAX_CLOCK_DECISION_CHECKS) {
                    result.addProperty("budgetExhausted", true);
                    break;
                }
                long wider = Math.max(1L, skew) << doubling;
                String status = probeStatus(solver,
                        widenClockWindows(base, clocks, skew, wider), blocked);
                checks++;
                widest = wider;
                if ("sat".equals(status)) {
                    admitted = wider;
                    break;
                }
                if (!"unsat".equals(status)) {
                    row.addProperty("wideningStatus", status);
                    break;
                }
            }
            row.addProperty("code", CLOCK_DECISION_OUTSIDE_WINDOW);
            outside++;
            if (admitted > 0L) {
                row.addProperty("requiredWindowMillisAtMost", admitted);
                row.addProperty("requiredWindowMillisAbove", admitted / 2);
            } else {
                row.addProperty("requiredWindowMillisAbove", widest);
            }
            rows.add(row);
        }
        result.addProperty("checks", checks);
        result.addProperty("outsideWindow", outside);
        result.addProperty("refusedWithoutWindow", refused);
        return result;
    }

    private static String probeStatus(Z3Solver solver, String base,
                                      String assertion)
            throws IOException, InterruptedException {
        solver.check(base + "(assert " + assertion + ")"
                + System.lineSeparator() + "(check-sat)"
                + System.lineSeparator());
        return solver.lastStatus();
    }

    /**
     * The region case path conditions that carry this comparison.
     *
     * <p>A case's path condition replays the branch outcomes the recording
     * observed, so a comparison inside one is pinned to the polarity some
     * replay took.  When a clock decision is refused with the clock
     * unbounded, these are the assertions that refuse it, and naming them
     * says which region has no observed case taking the other branch.</p>
     */
    private static JsonArray casePathConditionsOver(String base, String atom) {
        JsonArray names = new JsonArray();
        for (String line : base.split("\n")) {
            if (names.size() >= MAX_PINNING_CASES) break;
            if (!line.contains(atom)) continue;
            int at = line.indexOf(":named " + CASE_PATH_CONDITION_PREFIX);
            if (at < 0) continue;
            int from = at + ":named ".length();
            int to = from;
            while (to < line.length()
                    && "() \t".indexOf(line.charAt(to)) < 0) {
                to++;
            }
            names.add(line.substring(from, to));
        }
        return names;
    }

    /** How the Composer names a region case's path-condition assertion. */
    private static final String CASE_PATH_CONDITION_PREFIX =
            "case_selector_definition_";
    /** Pinning assertions named per refused decision; one is usually all. */
    private static final int MAX_PINNING_CASES = 4;

    /** The base text with every clock window assertion removed. */
    static String dropClockWindows(String base,
                                   Map<String, JsonObject> clocks,
                                   long skew) {
        String text = base;
        for (Map.Entry<String, JsonObject> clock : clocks.entrySet()) {
            long recorded = optionalLongInteger(clock.getValue(),
                    "recordedValue", 0L);
            text = text.replace(
                    ClockRootPhysics.window(clock.getKey(), recorded, skew),
                    "true");
        }
        return text;
    }

    /** The base text with every clock window widened to the given skew. */
    static String widenClockWindows(String base,
                                    Map<String, JsonObject> clocks,
                                    long skew, long wider) {
        String text = base;
        for (Map.Entry<String, JsonObject> clock : clocks.entrySet()) {
            long recorded = optionalLongInteger(clock.getValue(),
                    "recordedValue", 0L);
            text = text.replace(
                    ClockRootPhysics.window(clock.getKey(), recorded, skew),
                    ClockRootPhysics.window(clock.getKey(), recorded, wider));
        }
        return text;
    }

    /**
     * The comparison atoms of the formula that mention a clock term: the
     * innermost {@code (< a b)}, {@code (> a b)}, {@code (<= a b)} or
     * {@code (>= a b)} around each occurrence, one per operand pair, so the
     * two halves of Java's {@code lcmp} idiom count once.
     */
    static List<String> clockComparisonAtoms(String text,
                                             Collection<String> clockTerms,
                                             int limit) {
        List<String> atoms = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        // One clock's comparisons must not spend the whole budget: a
        // two-node mechanism needs a decision on each node, and the reads of
        // the first node alone can easily fill the limit. Take the clocks in
        // rounds, so every declared clock is asked about before any clock is
        // asked about twice.
        Map<String, Integer> cursor = new LinkedHashMap<>();
        for (String term : clockTerms) cursor.put(term, 0);
        boolean progress = true;
        while (atoms.size() < limit && progress) {
            progress = false;
            for (String term : clockTerms) {
                if (atoms.size() >= limit) break;
                int from = cursor.get(term);
                while (true) {
                    int at = text.indexOf(term, from);
                    if (at < 0) {
                        from = text.length();
                        break;
                    }
                    from = at + term.length();
                    if (!boundedSymbolAt(text, at, term.length())) continue;
                    if (clockPhysicsAssertion(text, at)) continue;
                    int open = enclosingComparison(text, at);
                    if (open < 0) continue;
                    int close = balancedEnd(text, open);
                    if (close < 0) continue;
                    String atom = text.substring(open, close + 1);
                    String key = comparisonKey(atom);
                    if (key.isEmpty() || !seen.add(key)) continue;
                    atoms.add(atom);
                    progress = true;
                    break;
                }
                cursor.put(term, from);
            }
        }
        return atoms;
    }

    /**
     * Whether this occurrence sits in an assertion the composition emitted
     * about the clock itself rather than about the program.
     *
     * <p>A clock's Java domain bound, its recorded window and its
     * monotonic order are comparisons over the clock term, and asking the
     * solver for both polarities of one of them asks whether a long can
     * leave its range: the answer is always "no", which then reads as a
     * decision the composition refuses.  The decisions worth naming are the
     * program's own.</p>
     */
    private static boolean clockPhysicsAssertion(String text, int at) {
        int start = text.lastIndexOf('\n', at) + 1;
        int end = text.indexOf('\n', at);
        String line = text.substring(start, end < 0 ? text.length() : end);
        return line.contains(":named java_integral_domain_")
                || line.contains(":named clock_window__")
                || line.contains(":named clock_monotonic__");
    }

    private static boolean containsSymbol(String text, String symbol) {
        int at = text.indexOf(symbol);
        while (at >= 0) {
            if (boundedSymbolAt(text, at, symbol.length())) return true;
            at = text.indexOf(symbol, at + 1);
        }
        return false;
    }

    /** The innermost enclosing s-expression headed by a comparison. */
    private static int enclosingComparison(String text, int at) {
        int depth = 0;
        for (int index = at - 1; index >= 0; index--) {
            char c = text.charAt(index);
            if (c == ')') {
                depth++;
            } else if (c == '(') {
                if (depth > 0) {
                    depth--;
                    continue;
                }
                int end = index + 1;
                while (end < text.length()
                        && !Character.isWhitespace(text.charAt(end))
                        && text.charAt(end) != '(') {
                    end++;
                }
                String head = text.substring(index + 1, end);
                if ("<".equals(head) || ">".equals(head)
                        || "<=".equals(head) || ">=".equals(head)) {
                    return index;
                }
                if ("assert".equals(head) || "define-fun".equals(head)
                        || "declare-const".equals(head)) {
                    return -1;
                }
            }
        }
        return -1;
    }

    private static int balancedEnd(String text, int open) {
        int depth = 0;
        for (int index = open; index < text.length(); index++) {
            char c = text.charAt(index);
            if (c == '(') depth++;
            if (c == ')') {
                depth--;
                if (depth == 0) return index;
            }
        }
        return -1;
    }

    /** An operand-pair key so {@code (< a b)} and {@code (> a b)} agree. */
    private static String comparisonKey(String atom) {
        List<String> parts = topLevelTokens(atom);
        if (parts.size() != 3) return "";
        String left = parts.get(1);
        String right = parts.get(2);
        return left.compareTo(right) <= 0 ? left + "\n" + right
                : right + "\n" + left;
    }

    /** The head and top-level operands of one s-expression. */
    private static List<String> topLevelTokens(String atom) {
        List<String> tokens = new ArrayList<>();
        String inner = atom.substring(1, atom.length() - 1).trim();
        int depth = 0;
        int start = -1;
        for (int index = 0; index < inner.length(); index++) {
            char c = inner.charAt(index);
            if (c == '(') {
                if (depth == 0) start = index;
                depth++;
            } else if (c == ')') {
                depth--;
                if (depth == 0) {
                    tokens.add(inner.substring(start, index + 1));
                    start = -1;
                }
            } else if (depth == 0) {
                if (Character.isWhitespace(c)) {
                    if (start >= 0) {
                        tokens.add(inner.substring(start, index));
                        start = -1;
                    }
                } else if (start < 0) {
                    start = index;
                }
            }
        }
        if (start >= 0 && depth == 0) tokens.add(inner.substring(start));
        return tokens;
    }

    private static JsonObject mechanismNecessity(
            Z3Solver solver, String base, JsonObject manifest,
            List<RootInput> markers, JsonArray valuations)
            throws IOException, InterruptedException {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "WITNESS_MECHANISM_NECESSITY");
        result.addProperty("authority", "RECORDED_ROOT_PIN_V1");
        JsonArray rows = new JsonArray();
        result.add("mechanisms", rows);
        Map<String, String> recorded = new LinkedHashMap<>();
        Set<String> clocks = new LinkedHashSet<>();
        for (JsonElement element
                : array(manifest, ComposedManifest.RECORDED_ROOT_VALUES)) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject ledger = element.getAsJsonObject();
            String term = optionalString(ledger, "solverTerm");
            String value = optionalString(ledger, "recordedValue");
            if (term.isEmpty() || value.isEmpty()) {
                continue;
            }
            recorded.put(term, value);
            if (optionalBool(ledger, "wallClock", false)) {
                clocks.add(term);
            }
        }
        if (recorded.isEmpty()) {
            return result;
        }
        // Every row states which valuation it answered for.  It used to
        // state it on one path only: the marker path built its row inline
        // and left {@code valuationOrdinal} off, so every consumer keying by
        // ordinal -- ClaimPolicy's clock-necessity map above all -- saw
        // nothing, CLOCK_NOT_NECESSARY could not fire, and a witness's clock
        // moves were accepted as its mechanism with the probe's own "not
        // necessary" answer sitting unread in the report.
        Set<Integer> answered = new LinkedHashSet<>();
        for (int index = 0; index < markers.size(); index++) {
            RootInput marker = markers.get(index);
            String recordedValue = recorded.get(marker.solverTerm);
            if (recordedValue == null || recordedValue.isEmpty()) {
                // Nothing observed what this root recorded, so "the recorded
                // polarity" names no valuation to probe.  Assuming one is
                // what ClaimPolicy stopped doing; this asks no question
                // rather than asking the wrong one.
                continue;
            }
            boolean polarity = !"false".equals(recordedValue);
            int ordinal = valuationOrdinalAt(valuations, index, polarity);
            JsonObject valuation = valuationRow(valuations, ordinal);
            if (valuation == null || !"sat".equals(optionalString(valuation,
                    "status"))) {
                continue;
            }
            answered.add(ordinal);
            for (Map.Entry<String, Set<String>> group
                    : mechanismRoots(valuation, clocks).entrySet()) {
                rows.add(necessityRow(solver, base, recorded,
                        marker.solverTerm, marker.literal(polarity),
                        marker.sourceIdentity, polarity, ordinal, group));
            }
        }
        // Every other satisfying valuation is a witness too, and its own
        // mechanisms have to answer for themselves.  A run with no declared
        // marker -- the clock cases, whose whole claim is that a wall clock
        // decided the target -- is entirely this loop, with that valuation's
        // Boolean assignment (empty, there) as the literal to hold.
        for (int ordinal = 0; ordinal < valuations.size(); ordinal++) {
            if (answered.contains(ordinal)) {
                continue;
            }
            JsonObject valuation = valuationRow(valuations, ordinal);
            if (valuation == null || !"sat".equals(optionalString(
                    valuation, "status"))) {
                continue;
            }
            String held = assignmentLiteral(markers, valuation);
            for (Map.Entry<String, Set<String>> group
                    : mechanismRoots(valuation, clocks).entrySet()) {
                rows.add(necessityRow(solver, base, recorded, "", held, "",
                        true, ordinal, group));
            }
        }
        return result;
    }

    /**
     * This valuation's own Boolean assignment, as one literal to assert.
     *
     * <p>"Does the target still reach without the clock" is a question about
     * one witness, so the witness's own roots are what the probe holds while
     * it asks.  Holding one marker instead answers about whichever sibling
     * marker that row also moved.</p>
     */
    private static String assignmentLiteral(List<RootInput> markers,
                                            JsonObject valuation) {
        JsonArray values = array(valuation, "values");
        List<String> literals = new ArrayList<>();
        for (int index = 0; index < markers.size()
                && index < values.size(); index++) {
            if (!values.get(index).isJsonPrimitive()) {
                continue;
            }
            literals.add(markers.get(index).literal(
                    values.get(index).getAsBoolean()));
        }
        if (literals.isEmpty()) {
            return "";
        }
        return literals.size() == 1 ? literals.get(0)
                : "(and " + String.join(" ", literals) + ")";
    }

    /**
     * Asks one mechanism whether the target still reaches with its roots put
     * back to what they recorded.
     *
     * @param markerLiteral the marker assertion to hold, or "" when the run
     *                      declares no marker at all
     */
    private static JsonObject necessityRow(
            Z3Solver solver, String base, Map<String, String> recorded,
            String markerTerm, String markerLiteral, String sourceIdentity,
            boolean polarity, int ordinal,
            Map.Entry<String, Set<String>> group)
            throws IOException, InterruptedException {
        JsonObject row = new JsonObject();
        row.addProperty("marker", markerTerm);
        row.addProperty("sourceIdentity", sourceIdentity);
        row.addProperty("polarity", polarity);
        row.addProperty("valuationOrdinal", ordinal);
        row.addProperty("mechanism", group.getKey());
        row.addProperty("pinnedRoots", group.getValue().size());
        StringBuilder query = new StringBuilder(base);
        if (!markerLiteral.isEmpty()) {
            query.append("(assert ").append(markerLiteral).append(")")
                    .append(System.lineSeparator());
        }
        for (String term : group.getValue()) {
            query.append("(assert (= ").append(term).append(' ')
                    .append(smtLiteral(recorded.get(term)))
                    .append("))").append(System.lineSeparator());
        }
        query.append("(check-sat)").append(System.lineSeparator());
        solver.check(query.toString());
        String answerStatus = solver.lastStatus();
        row.addProperty("status", answerStatus);
        row.addProperty("necessary", "unsat".equals(answerStatus));
        return row;
    }

    /** The roots each named mechanism of this witness rests on. */
    private static Map<String, Set<String>> mechanismRoots(
            JsonObject valuation, Set<String> clocks) {
        Map<String, Set<String>> groups = new LinkedHashMap<>();
        for (JsonElement element : array(valuation, "witnessMechanisms")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject mechanism = element.getAsJsonObject();
            String kind = optionalString(mechanism, "kind");
            String term = optionalString(mechanism, "solverTerm");
            if (kind.isEmpty() || "MARKER_FLIPPED".equals(kind)
                    || term.isEmpty()) {
                continue;
            }
            Set<String> roots = groups.get(kind);
            if (roots == null) {
                roots = new LinkedHashSet<>();
                groups.put(kind, roots);
            }
            // "CLOCK_SKEW" is a claim about clocks disagreeing, so the whole
            // set answers for it; anything else answers for itself.
            roots.addAll("CLOCK_SKEW".equals(kind) && clocks.contains(term)
                    ? clocks : Collections.singleton(term));
        }
        return groups;
    }

    /** One valuation row, or null. */
    private static JsonObject valuationRow(JsonArray valuations,
                                           int ordinal) {
        if (valuations == null || ordinal < 0
                || ordinal >= valuations.size()) {
            return null;
        }
        JsonElement element = valuations.get(ordinal);
        return element.isJsonObject() ? element.getAsJsonObject() : null;
    }

    /**
     * Where the valuation giving this Boolean root that polarity sits.
     *
     * <p>The ordinal, not the row: every necessity answer is published
     * against the valuation it was asked of, and a row found by scanning had
     * no position to state.</p>
     */
    private static int valuationOrdinalAt(JsonArray valuations, int index,
                                          boolean polarity) {
        for (int ordinal = 0; ordinal < valuations.size(); ordinal++) {
            JsonElement element = valuations.get(ordinal);
            if (!element.isJsonObject()) {
                continue;
            }
            JsonArray values = array(element.getAsJsonObject(), "values");
            if (index < values.size() && values.get(index).isJsonPrimitive()
                    && values.get(index).getAsBoolean() == polarity) {
                return ordinal;
            }
        }
        return -1;
    }

    /** A ledger value spells -5 as "-5"; a query needs "(- 5)". */
    private static String smtLiteral(String recorded) {
        String value = firstNonBlank(recorded);
        return value.startsWith("-")
                ? "(- " + value.substring(1).trim() + ")" : value;
    }


    /** The published arms, with the model's choice marked on each. */
    private static JsonObject fatalStateSelection(List<JsonObject> arms,
                                                  Map<String, String> model) {
        JsonObject selection = new JsonObject();
        selection.addProperty("schemaVersion", 1);
        selection.addProperty("kind", FATAL_STATE_SELECTION_KIND);
        selection.addProperty("authority",
                "SOLVER_SELECTED_GUARDED_READ_ARM_V1");
        selection.addProperty("resolved", !arms.isEmpty());
        JsonArray rows = new JsonArray();
        for (JsonObject arm : arms) {
            JsonObject row = arm.deepCopy();
            String assigned = model.get(optionalString(arm, "selector"));
            row.addProperty("selected", "true".equals(assigned));
            row.addProperty("modelled", assigned != null);
            rows.add(row);
        }
        selection.add("arms", rows);
        return selection;
    }

    /**
     * The value range each clock root's own physics allows, by solver term.
     *
     * <p>{@link ClockRootPhysics} already asserts this window in the formula,
     * so a perturbation outside it is rejected by that assertion rather than
     * by anything the target predicate says.  Reading the window here lets the
     * probe stay inside it and stop mistaking its own boundary for evidence.
     */
    static Map<String, BigInteger[]> clockWindows(JsonObject manifest) {
        Map<String, BigInteger[]> windows = new LinkedHashMap<>();
        JsonObject physics = object(manifest, ClockRootPhysics.MANIFEST_FIELD);
        if (physics.size() == 0) {
            return windows;
        }
        BigInteger skew = BigInteger.valueOf(Math.max(0L,
                optionalLongInteger(physics, "clockSkewMillis",
                        ClockRootPhysics.DEFAULT_SKEW_MILLIS)));
        for (JsonElement element : array(physics, "clockReads")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject read = element.getAsJsonObject();
            String term = optionalString(read, "solverTerm");
            if (term.isEmpty() || !read.has("recordedValue")) {
                continue;
            }
            BigInteger recorded = BigInteger.valueOf(
                    optionalLongInteger(read, "recordedValue", 0L));
            windows.put(term, new BigInteger[] {
                    recorded.subtract(skew), recorded.add(skew) });
        }
        return windows;
    }

    /** Whether an SMT integer literal lies inside a declared window. */
    private static boolean insideWindow(BigInteger[] window, String literal) {
        if (window == null) {
            return true;
        }
        BigInteger value = ScalarEncoding.parseSmtInteger(literal);
        return value == null || (value.compareTo(window[0]) >= 0
                && value.compareTo(window[1]) <= 0);
    }

    private static JsonArray existentialPerturbations(
            Z3Solver solver, String query, List<RootInput> roots,
            JsonArray witness, Map<String, BigInteger[]> windows) {
        JsonArray result = new JsonArray();
        Map<String, String> values = new LinkedHashMap<>();
        for (JsonElement element : witness) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            String solverTerm = optionalString(row, "solverTerm");
            String value = optionalString(row, "value");
            if (!solverTerm.isEmpty() && !value.isEmpty()) {
                values.put(solverTerm, value);
            }
        }
        if (values.size() != roots.size()) return result;

        String base = SmtLibQueries.stripSolverCommands(query);
        for (RootInput changed : roots) {
            BigInteger[] window = windows.get(changed.solverTerm);
            for (String alternative : changed.neighboringLiterals(
                    values.get(changed.solverTerm))) {
                if (result.size() >= MAX_EXISTENTIAL_PERTURBATIONS) {
                    return result;
                }
                // A value the root's own declared physics forbids is refused
                // by that assertion, not by the target predicate, so trying
                // it would answer a question nobody asked. Name it and move
                // to the neighbour that is still a value the clock could have
                // returned.
                if (!insideWindow(window, alternative)) {
                    JsonObject refused = changed.toJson();
                    refused.addProperty("witnessValue",
                            values.get(changed.solverTerm));
                    refused.addProperty("perturbedValue", alternative);
                    refused.addProperty("status", "skipped");
                    refused.addProperty("rejectedBy", WINDOW_BOUNDARY);
                    result.add(refused);
                    continue;
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
                    String answerStatus = solver.lastStatus();
                    row.addProperty("status", answerStatus);
                    rejected = "unsat".equals(answerStatus);
                    if (!"sat".equals(answerStatus)
                            && !"unsat".equals(answerStatus)) {
                        row.addProperty("solverOutput",
                                answer == null ? answerStatus
                                        : answer.diagnostic());
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

    /** Exact region-local root terms published by the Composer. */
    private static final class ManualSymbolicRootCatalog {
        private final List<ManualSymbolicRootGroup> roots = new ArrayList<>();

        private static ManualSymbolicRootCatalog from(
                JsonObject manifest, List<String> gaps) {
            ManualSymbolicRootCatalog result = new ManualSymbolicRootCatalog();
            JsonElement encoded = manifest == null ? null : manifest.get(
                    ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_FIELD);
            if (encoded == null || !encoded.isJsonArray()) {
                gaps.add("MANUAL_SYMBOLIC_ROOT_LEDGER_MISSING");
                return result;
            }
            Map<String, ManualSymbolicRootGroup> byTerm =
                    new LinkedHashMap<>();
            Map<String, ManualSymbolicRootInfo> byInput = new LinkedHashMap<>();
            Map<String, ManualSymbolicRootInfo> bySource =
                    new LinkedHashMap<>();
            int ordinal = 0;
            for (JsonElement element : encoded.getAsJsonArray()) {
                if (!element.isJsonObject()) {
                    gaps.add("MANUAL_SYMBOLIC_ROOT_MALFORMED:" + ordinal++);
                    continue;
                }
                ManualSymbolicRootInfo root = ManualSymbolicRootInfo.decode(
                        element.getAsJsonObject());
                if (root == null) {
                    gaps.add("MANUAL_SYMBOLIC_ROOT_MALFORMED:" + ordinal++);
                    continue;
                }
                String input = root.occurrenceId + "\n" + root.portId;
                String source = root.sourceIdentityAuthority + "\n"
                        + root.sourceIdentity;
                ManualSymbolicRootInfo heldInput = byInput.get(input);
                ManualSymbolicRootInfo heldSource = bySource.get(source);
                ManualSymbolicRootGroup heldTerm = byTerm.get(
                        root.solverTerm);
                if ((heldInput != null && !heldInput.sameBinding(root))
                        || (heldSource != null
                        && (!heldSource.solverTerm.equals(root.solverTerm)
                        || !heldSource.sameEncoding(root)))
                        || (heldTerm != null
                        && (!heldTerm.canonical().sameEncoding(root)
                        || heldTerm.canonical().distinctMint(root)))) {
                    gaps.add("MANUAL_SYMBOLIC_ROOT_CONFLICT:" + ordinal);
                } else if (heldInput != null) {
                    // An identical duplicate row adds no second logical alias.
                } else {
                    byInput.put(input, root);
                    bySource.putIfAbsent(source, root);
                    if (heldTerm == null) {
                        heldTerm = new ManualSymbolicRootGroup(root);
                        byTerm.put(root.solverTerm, heldTerm);
                        result.roots.add(heldTerm);
                    } else {
                        heldTerm.addAlias(root);
                    }
                }
                ordinal++;
            }
            return result;
        }

        private List<ManualSymbolicRootGroup> sorted() {
            List<ManualSymbolicRootGroup> result = new ArrayList<>(roots);
            result.sort(Comparator
                    .comparing((ManualSymbolicRootGroup value) ->
                            value.canonical().portId)
                    .thenComparing(value ->
                            value.canonical().occurrenceId)
                    .thenComparing(value ->
                            value.canonical().solverTerm));
            return result;
        }
    }

    /** All declared occurrence/port aliases of one physical solver root. */
    private static final class ManualSymbolicRootGroup {
        private final List<ManualSymbolicRootInfo> aliases =
                new ArrayList<>();

        private ManualSymbolicRootGroup(ManualSymbolicRootInfo first) {
            aliases.add(first);
        }

        private void addAlias(ManualSymbolicRootInfo alias) {
            aliases.add(alias);
        }

        private ManualSymbolicRootInfo canonical() {
            return sortedAliases().get(0);
        }

        private List<ManualSymbolicRootInfo> sortedAliases() {
            List<ManualSymbolicRootInfo> result = new ArrayList<>(aliases);
            result.sort(Comparator
                    // Prefer a mint when the selected closure contains one;
                    // exact reused-action rows are aliases of the same term.
                    .comparing((ManualSymbolicRootInfo value) -> value.reused)
                    .thenComparing(value -> value.portId)
                    .thenComparing(value -> value.occurrenceId));
            return result;
        }
    }

    /** One declared region input and the exact SMT scalar it materialized. */
    private static final class ManualSymbolicRootInfo {
        private final String portId;
        private final String occurrenceId;
        private final String fieldSignature;
        private final String descriptor;
        private final String sort;
        private final String smtSort;
        private final String solverTerm;
        private final String nullnessSolverTerm;
        private final String sourceIdentity;
        private final String sourceIdentityAuthority;
        private final boolean reused;

        private ManualSymbolicRootInfo(String portId, String occurrenceId,
                                      String fieldSignature,
                                      String descriptor, String sort,
                                      String smtSort, String solverTerm,
                                      String nullnessSolverTerm,
                                      String sourceIdentity,
                                      String sourceIdentityAuthority,
                                      boolean reused) {
            this.portId = firstNonBlank(portId);
            this.occurrenceId = firstNonBlank(occurrenceId);
            this.fieldSignature = firstNonBlank(fieldSignature);
            this.descriptor = firstNonBlank(descriptor);
            this.sort = firstNonBlank(sort);
            this.smtSort = firstNonBlank(smtSort);
            this.solverTerm = firstNonBlank(solverTerm);
            this.nullnessSolverTerm = firstNonBlank(nullnessSolverTerm);
            this.sourceIdentity = firstNonBlank(sourceIdentity);
            this.sourceIdentityAuthority = firstNonBlank(
                    sourceIdentityAuthority);
            this.reused = reused;
        }

        private static ManualSymbolicRootInfo decode(JsonObject row) {
            if (row == null || optionalInteger(row, "schemaVersion", -1) != 1
                    || !ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_KIND.equals(
                    optionalString(row, "kind"))
                    || !ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_AUTHORITY
                    .equals(optionalString(row, "authority"))) {
                return null;
            }
            ManualSymbolicRootInfo result = new ManualSymbolicRootInfo(
                    optionalString(row, "portId"), optionalString(row, "occurrenceId"),
                    optionalString(row, "fieldSignature"),
                    optionalString(row, "javaTypeDescriptor"),
                    optionalString(row, "sort"), optionalString(row, "smtSort"),
                    optionalString(row, "solverTerm"),
                    optionalString(row, "nullnessSolverTerm"),
                    optionalString(row, "sourceIdentity"),
                    optionalString(row, "sourceIdentityAuthority"),
                    optionalBool(row, SymbolicSourceEvidence.REUSED, false));
            return result.portId.isEmpty() || result.occurrenceId.isEmpty()
                    || result.descriptor.isEmpty() || result.sort.isEmpty()
                    || result.smtSort.isEmpty() || result.solverTerm.isEmpty()
                    || result.sourceIdentity.isEmpty()
                    || !validSourceIdentityAuthority(
                    result.sourceIdentityAuthority, result.reused)
                    ? null : result;
        }

        /** Two independently minted roots may never share one SMT term. */
        private boolean distinctMint(ManualSymbolicRootInfo other) {
            return !reused && !other.reused && !sameSource(other);
        }

        private boolean sameSource(ManualSymbolicRootInfo other) {
            return sourceIdentity.equals(other.sourceIdentity)
                    && sourceIdentityAuthority.equals(
                    other.sourceIdentityAuthority);
        }

        private boolean sameEncoding(ManualSymbolicRootInfo other) {
            return descriptor.equals(other.descriptor)
                    && sort.equals(other.sort)
                    && smtSort.equals(other.smtSort)
                    && nullnessSolverTerm.equals(
                    other.nullnessSolverTerm);
        }

        private boolean sameBinding(ManualSymbolicRootInfo other) {
            return solverTerm.equals(other.solverTerm)
                    && sameSource(other) && sameEncoding(other);
        }

        private static boolean validSourceIdentityAuthority(
                String authority, boolean reused) {
            return "EXACT_SEED_FIELD_VERSION_V1".equals(authority)
                    || "SOURCE_EPOCH_HEAP_FIELD_VERSION_V1".equals(
                    authority)
                    || "EXACT_RUNTIME_LOCAL_SOURCE_EVENT_V1".equals(
                    authority)
                    || SymbolicSourceEvidence.MANUAL_AUTHORITY.equals(
                    authority)
                    || reused && ConcolicSummaryImporter
                    .MANUAL_INPUT_OBSERVATION_AUTHORITY.equals(authority);
        }
    }

    /** Exact writable source terms published by the Composer. */
    private static final class ConfiguredSourceCatalog {
        private final List<ConfiguredSourceInfo> sources = new ArrayList<>();

        private static ConfiguredSourceCatalog from(
                JsonObject manifest, List<String> gaps) {
            ConfiguredSourceCatalog result = new ConfiguredSourceCatalog();
            JsonElement encoded = manifest == null ? null : manifest.get(
                    ComposedManifest
                            .CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
            if (encoded == null || !encoded.isJsonArray()) {
                gaps.add("CONFIGURED_SOURCE_MATERIALIZATIONS_MISSING");
                return result;
            }
            // One mint site may materialize several roots for the same source
            // metadata. The root is the identity: the Composer keeps VM
            // symbols and root names injective.
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
            if (row == null || optionalInteger(row, "schemaVersion", -1) != 3
                    || !ComposedManifest
                    .CONFIGURED_SOURCE_MATERIALIZATION_KIND.equals(
                    optionalString(row, "kind"))
                    || !ComposedManifest
                    .CONFIGURED_SOURCE_MATERIALIZATION_AUTHORITY.equals(
                    optionalString(row, "authority"))) {
                return null;
            }
            ConfiguredSourceInfo result = new ConfiguredSourceInfo(
                    optionalString(row, "sourceKey"),
                    optionalString(row, "sourceId"),
                    optionalString(row, "sourcePhaseId"),
                    optionalString(row, "sourceOccurrenceId"),
                    optionalString(row, "fieldSignature"),
                    optionalString(row, "javaTypeDescriptor"),
                    optionalString(row, "sort"), optionalString(row, "smtSort"),
                    optionalString(row, "solverTerm"),
                    optionalString(row, "nullnessSolverTerm"));
            return result.sourceKey.isEmpty() || result.sourceId.isEmpty()
                    || result.sourcePhaseId.isEmpty()
                    || !result.sourcePhaseId.startsWith("SOURCE_PHASE.")
                    || result.sourceOccurrenceId.isEmpty()
                    || result.fieldSignature.isEmpty()
                    || result.descriptor.isEmpty()
                    || result.sort.isEmpty() || result.smtSort.isEmpty()
                    || result.solverTerm.isEmpty() ? null : result;
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
        private int workers = 8;
        private String mappings = "";

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
            result.workers = positiveInt(values.get("workers"), 8);
            result.mappings = firstNonBlank(values.get("mappings"));
            return result;
        }

        private static boolean option(String key) {
            return "smt".equals(key) || "manifest".equals(key)
                    || "runtime-plan".equals(key)
                    || "output".equals(key) || "z3".equals(key)
                    || "timeout-ms".equals(key)
                    || "max-inputs".equals(key)
                    || "max-valuations".equals(key)
                    || "workers".equals(key)
                    || "mappings".equals(key);
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
                || !optionalString(actual, "path").equals(normalizedPath(
                optionalString(expected, "path")))
                || !optionalString(actual, "sha256").equals(optionalString(expected,
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
