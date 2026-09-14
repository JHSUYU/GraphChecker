package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
import edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract;
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
 * SOLVE: z3 over {@code Fatal_T}, and what a satisfying assignment means.
 *
 * <p>The composition publishes one formula per anchored occurrence of the
 * target.  This enumerates that formula's free Boolean roots, solves each
 * valuation, probes whether the marker and clock roots a satisfying witness
 * moved were needed for it, and reads every witness against the mechanisms
 * the recording allows.  What it publishes is the valuations and the
 * mechanisms; {@link ClaimPolicy} decides from them.</p>
 *
 * <p>It used to publish a "reach condition" as well: the satisfying
 * valuations rendered again as a DNF, the domain that rendering was a
 * projection of, a coverage conclusion and a degeneracy verdict.
 * Reachability is Fatal_T's satisfiability and is one field; a second
 * rendering of the valuations is a second artifact to keep true, and whether
 * the target is unconstrained by every root is decided where the formula is
 * built, not by reading the shape of a disjunction afterwards.</p>
 */
public final class RootValuationSolver {
    private static final int MAX_EXISTENTIAL_PERTURBATIONS = 32;

    /** A perturbation the root's own declared physics forbids. */
    static final String WINDOW_BOUNDARY = "WINDOW_BOUNDARY";
    /** Whether a witness's named mechanism is needed, or only decoration. */
    static final String MECHANISM_NECESSITY = "mechanismNecessity";
    /** Solved to be read, never to be believed: the Composer refused. */
    static final String EVIDENCE_ONLY = "evidenceOnly";
    /** How the Composer spells "this formula must not be satisfiable". */
    private static final String FAIL_CLOSED_MARKER = "; fail closed";
    static final String SYMBOLIC_VARIABLE_MODELS =
            "symbolicVariableModels";
    private static final String SYMBOLIC_VARIABLE_MODEL_KIND =
            "SYMBOLIC_VARIABLE_MODEL";
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();
    private RootValuationSolver() {
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
                ClaimPolicy.PlannedSymbolicRoots.read(
                        arguments.runtimePlan.toString()));
        report.add("solverAttempts", solver.attempts());
        // One artifact per anchored occurrence.  The valuations and the
        // mechanisms are about the formula the manifest describes, and a
        // second file beside it was a second thing to keep in step -- the
        // campaign copied it, digested it, required it and named it in every
        // report row.  They are published into the manifest, under the
        // member the readers ask for.
        manifest.add(ComposedManifest.SOLVER, report);
        ArtifactIO.replace(arguments.manifest, GSON.toJson(manifest)
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
                maxValuations, ClaimPolicy.PlannedSymbolicRoots.none());
    }

    /**
     * The report, with the campaign claim decided from it.  Every exit from
     * {@link #solverReport} states a reachability, so the one gate that reads
     * one runs here rather than in each caller: the report and the claim it
     * justifies are published together or not at all.
     */
    static JsonObject extract(String composedSmt, JsonObject manifest,
                              Z3Solver solver,
                              int maxInputs, int maxValuations,
                              ClaimPolicy.PlannedSymbolicRoots flows)
            throws IOException, InterruptedException {
        JsonObject report = solverReport(composedSmt, manifest, solver,
                maxInputs, maxValuations);
        report.add(ClaimPolicy.CLAIM,
                ClaimPolicy.decide(manifest, report, flows));
        return report;
    }

    private static JsonObject solverReport(String composedSmt,
                                           JsonObject manifest,
                                           Z3Solver solver,
                                           int maxInputs, int maxValuations)
            throws IOException, InterruptedException {
        JsonObject report = new JsonObject();
        report.addProperty("schemaVersion", 4);
        report.addProperty("kind", "ROOT_VALUATION_REPORT");
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
        boolean composerRefused = composerRefused(manifest);
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

        // One question for every declared root: the Boolean markers over
        // {recorded, flipped} and the roots the case gave a domain over that
        // domain, recorded value first.  The two used to be different kinds
        // of thing -- the markers enumerated, an integral root left
        // existential with a preference for what it recorded -- so no
        // valuation ever moved a serial number and no witness could name the
        // rotation the case is about.
        List<Map<String, String>> rootAssignments = rootAssignments(manifest,
                discovery.existentialNonBooleanRootInputs,
                Math.max(1, maxValuations));
        long booleanCount = inputs.size() >= 63
                ? Long.MAX_VALUE : 1L << inputs.size();
        long valuationCount = booleanCount == Long.MAX_VALUE
                ? Long.MAX_VALUE : booleanCount * rootAssignments.size();
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
        boolean evidenceOnly = composerRefused;
        if (!gaps.isEmpty()) {
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
        // Nothing is asked of the model beyond the roots.  Membership in a
        // container is decided by the assoc model over the whole mutation
        // chain, so there is no separate "did this read take a default"
        // symbol to fetch and no freedom to report about one.
        List<String> modelSymbols = new ArrayList<>();
        List<boolean[]> satisfyingValuations = new ArrayList<>();
        JsonArray valuationRows = new JsonArray();
        JsonArray existentialPerturbations = new JsonArray();
        boolean rejectedExistentialPerturbation = false;
        boolean existentialProbeAttempted = false;
        int solverErrors = 0;
        int count = (int) valuationCount;
        int booleans = (int) booleanCount;
        for (int ordinal = 0; ordinal < count; ordinal++) {
            // Assignment-major, so ordinal 0 is the run as it happened and a
            // composition with no declared domain enumerates exactly what it
            // enumerated before.
            Map<String, String> assignment =
                    rootAssignments.get(ordinal / booleans);
            boolean[] values = valuation(ordinal % booleans, inputs.size());
            String query = valuationQuery(base, inputs, values, assignment,
                    discovery.existentialNonBooleanRootInputs,
                    modelSymbols);
            ConcolicConstraintSolver.SolverOutput result =
                    solver.check(query);
            String status = solver.lastStatus();
            JsonObject row = asEvidence(valuationRow(values, status),
                    evidenceOnly);
            if (!assignment.isEmpty()) {
                row.add("rootAssignment", GSON.toJsonTree(assignment));
            }
            // A reader has to be able to tell a causal verdict from one the
            // these are the selectors this valuation
            // was solved under.
            row.add("pinnedCaseSelectors",
                    GSON.toJsonTree(solver.lastPinnedSelectors()));
            if ("sat".equals(status)) {
                satisfyingValuations.add(values.clone());
                Map<String, String> model =
                        ConcolicConstraintSolver.parseGetValues(result.stdout);
                JsonArray witness = existentialWitness(result,
                        discovery.existentialNonBooleanRootInputs);
                if (witness.size() > 0) {
                    row.add("existentialWitness", witness);
                }
                JsonArray mechanisms = witnessMechanisms(manifest, inputs,
                        values, witness);
                if (mechanisms.size() > 0) {
                    row.add("witnessMechanisms", mechanisms);
                }
                if (witness.size() > 0) {
                    if (!existentialProbeAttempted) {
                        existentialProbeAttempted = true;
                        JsonArray perturbations = existentialPerturbations(
                                solver, query,
                                discovery.existentialNonBooleanRootInputs,
                                witness, declaredWindows(manifest));
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
        // Reachability is Fatal_T's satisfiability at this anchor, and that
        // is all it is.  It used to travel inside a "reach condition" that
        // also carried a DNF rendering of the satisfying valuations, the
        // domain that rendering was a projection of, a coverage conclusion
        // and a degeneracy verdict.  The valuations are published below and
        // are the evidence; a second rendering of them is a second artifact
        // to keep true.  And whether the target is unconstrained by every
        // root is decided where the formula is built -- the composition
        // refuses ROOT_NOT_ON_ANY_PATH -- not by reading the shape of a
        // disjunction afterwards.
        report.addProperty("reachability", reachability);
        JsonArray resultGaps = new JsonArray();
        for (String gap : gaps) {
            resultGaps.add(gap);
        }
        if (solverErrors > 0) {
            resultGaps.add("UNDECIDED_SOLVER_VALUATIONS:"
                    + solverErrors);
        }
        report.add("gaps", resultGaps);
        report.addProperty("state",
                complete && !evidenceOnly
                        ? "CANDIDATE_READY" : "CANDIDATE_WITH_GAPS");
        return report;
    }

    /** Stamps one published row as read-only evidence. */
    private static JsonObject asEvidence(JsonObject row,
                                         boolean evidenceOnly) {
        if (evidenceOnly && row != null) {
            row.addProperty(EVIDENCE_ONLY, true);
        }
        return row;
    }


    /**
     * Whether the composition this stage was handed refused itself.
     *
     * <p>This stage needs a composition that already declared itself
     * candidate-ready; re-deriving that verdict from its members would be the
     * second gate README forbids, so the manifest's own {@code state} is
     * read and nothing else is.  A refusal is not a gap of this stage's own:
     * the composition published its refusal, with the code that names it,
     * and repeating "so the solver's answer is not about a candidate model"
     * as a second row is that one refusal counted twice.  It is a fact about
     * this report -- the answer may be read and may not be believed -- and it
     * is published as {@code evidenceOnly}.</p>
     */
    private static boolean composerRefused(JsonObject manifest) {
        boolean commonManifest = manifest != null
                && optionalInteger(manifest, "schemaVersion", -1) == 2
                && "CONCOLIC_COMPOSED_SMT".equals(optionalString(manifest, "kind"));
        return !commonManifest
                || !"CANDIDATE_READY".equals(optionalString(manifest, "state"));
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
                                         Map<String, String> assignment,
                                         List<RootInput> witnessRoots,
                                         List<String> modelSymbols) {
        StringBuilder query = new StringBuilder(base);
        for (int index = 0; index < inputs.size(); index++) {
            query.append("(assert ")
                    .append(inputs.get(index).literal(values[index]))
                    .append(")").append(System.lineSeparator());
        }
        for (Map.Entry<String, String> root : assignment.entrySet()) {
            query.append("(assert (= ").append(root.getKey()).append(' ')
                    .append(root.getValue()).append("))")
                    .append(System.lineSeparator());
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

    /**
     * The values each declared root is enumerated over, recorded first.
     *
     * <p>A declared root is asked the same question a declared marker is:
     * what does the target do at each value the case says the root may have
     * had?  For a Boolean marker that is {recorded, flipped}, which is the
     * two-value case of this; for the block-key serial it is the recording's
     * value and the rotations past it.  The recorded value leads, so the
     * first assignment is the run as it happened, and the rest follow it by
     * distance -- one rotation before three, so the smallest departure that
     * reaches the target is the one a reader sees first.</p>
     */
    private static List<Map<String, String>> rootAssignments(
            JsonObject manifest, List<RootInput> roots, int budget) {
        Map<String, BigInteger[]> domains = declaredDomains(manifest);
        Map<String, String> recorded = recordedRootValues(manifest);
        List<String> terms = new ArrayList<>();
        Map<String, List<BigInteger>> moves = new LinkedHashMap<>();
        for (RootInput root : roots == null
                ? Collections.<RootInput>emptyList() : roots) {
            BigInteger[] domain = domains.get(root.solverTerm);
            BigInteger at = integral(firstNonBlank(
                    recorded.get(root.solverTerm)));
            if (domain == null || at == null) continue;
            List<BigInteger> alternatives = new ArrayList<>();
            for (BigInteger value = domain[0];
                    value.compareTo(domain[1]) <= 0;
                    value = value.add(BigInteger.ONE)) {
                if (value.equals(at)) continue;
                alternatives.add(value);
                if (alternatives.size() >= Math.max(1, budget)) break;
            }
            if (alternatives.isEmpty()) continue;
            Collections.sort(alternatives, byDistanceFrom(at));
            terms.add(root.solverTerm);
            moves.put(root.solverTerm, alternatives);
        }
        List<Map<String, String>> assignments = new ArrayList<>();
        assignments.add(Collections.<String, String>emptyMap());
        if (terms.isEmpty()) return assignments;
        // One root moved, then two, then three: a witness that needs fewer
        // departures from the recording is the smaller claim, so it is asked
        // for first.  The budget is the caller's valuation cap, which is the
        // one bound on how much of the product is asked at all.
        List<Map<String, String>> level = new ArrayList<>(assignments);
        for (int moved = 1; moved <= terms.size(); moved++) {
            List<Map<String, String>> next = new ArrayList<>();
            for (Map<String, String> previous : level) {
                for (String term : terms) {
                    if (previous.containsKey(term)) continue;
                    if (!previous.isEmpty() && terms.indexOf(term)
                            <= lastIndex(terms, previous)) {
                        continue;
                    }
                    for (BigInteger value : moves.get(term)) {
                        Map<String, String> assignment =
                                new LinkedHashMap<>(previous);
                        assignment.put(term,
                                ScalarEncoding.formatSmtInteger(value));
                        next.add(assignment);
                    }
                }
            }
            if (next.isEmpty()) break;
            assignments.addAll(next);
            level = next;
            if (assignments.size() >= Math.max(1, budget)) break;
        }
        return assignments;
    }

    /** The last term of {@code terms} this assignment already moved. */
    private static int lastIndex(List<String> terms,
                                 Map<String, String> assignment) {
        int last = -1;
        for (String term : assignment.keySet()) {
            last = Math.max(last, terms.indexOf(term));
        }
        return last;
    }

    /** Nearest to the recorded value first; ties by value, for stability. */
    private static Comparator<BigInteger> byDistanceFrom(
            final BigInteger recorded) {
        return new Comparator<BigInteger>() {
            @Override
            public int compare(BigInteger left, BigInteger right) {
                int distance = left.subtract(recorded).abs().compareTo(
                        right.subtract(recorded).abs());
                return distance != 0 ? distance : left.compareTo(right);
            }
        };
    }

    /** What the recording read for each declared root, by solver term. */
    private static Map<String, String> recordedRootValues(
            JsonObject manifest) {
        Map<String, String> recorded = new LinkedHashMap<>();
        for (JsonElement element : array(manifest,
                ComposedManifest.RECORDED_ROOT_VALUES)) {
            if (!element.isJsonObject()) continue;
            JsonObject ledger = element.getAsJsonObject();
            String term = optionalString(ledger, "solverTerm");
            String value = optionalString(ledger,
                    ComposedManifest.RECORDED_SOURCE_VALUE);
            if (!term.isEmpty() && !value.isEmpty()) {
                recorded.put(term, value);
            }
        }
        return recorded;
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
        report.addProperty("reachability", "UNKNOWN");
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
        }

        private volatile List<String> lastPinned = Collections.emptyList();
        /** The status of the last {@link #check}. */
        private volatile String lastStatus = "";

        synchronized JsonArray attempts() {
            return attempts.deepCopy();
        }

        /** Case selectors the attempt that decided the last check pinned. */
        List<String> lastPinnedSelectors() {
            return new ArrayList<>(lastPinned);
        }

        /** The solver status of the last {@link #check}. */
        String lastStatus() {
            return lastStatus;
        }

        ConcolicConstraintSolver.SolverOutput check(String smt)
                throws IOException,
                InterruptedException {
            int currentQuery = queryOrdinal++;
            PartitionPlan plan = splitPartitions();
            lastStatus = "";
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
            // Every attempt refused this valuation, and every selector this
            // driver pins comes from a case partition the composition
            // published, so an unsat here is the formula's answer.
            lastStatus = "unsat";
            return unsat;
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
             * A pin that shows up in the core says the refusal rests on a
             * case this driver chose to fix, which is worth reading back.</p>
             */
            private final List<String> pinLiterals;

            private PartitionQuery(String smt, List<String> selectors,
                                   List<String> pinLiterals) {
                this.smt = smt;
                this.selectors = selectors;
                this.pinLiterals = pinLiterals;
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
    /**
     * Whether this root's witnessed value is inside the domain the case
     * declared for it.  A root with no declared domain has none, so the
     * answer is no and the move stays an unexplained one.
     */
    private static boolean insideDeclaredDomain(JsonObject ledger,
                                                String witnessed) {
        String min = optionalString(ledger,
                PathMergeComposer.DECLARED_DOMAIN_MIN);
        String max = optionalString(ledger,
                PathMergeComposer.DECLARED_DOMAIN_MAX);
        if (min.isEmpty() || max.isEmpty()) return false;
        try {
            BigInteger value = new BigInteger(
                    normalizeIntegral(witnessed).trim());
            return value.compareTo(new BigInteger(min.trim())) >= 0
                    && value.compareTo(new BigInteger(max.trim())) <= 0;
        } catch (NumberFormatException notIntegral) {
            return false;
        }
    }

    /**
     * How far a witnessed clock is from the nearest instant this root was
     * actually read at, or from the seed's reading when the composition
     * published no others.
     */
    private static Long nearestSkew(List<Long> readings, String recorded,
                                    String witnessed) {
        Long direct = skewMillis(recorded, witnessed);
        if (readings == null || readings.isEmpty()) return direct;
        final long value;
        try {
            value = Long.parseLong(normalizeIntegral(witnessed).trim());
        } catch (NumberFormatException notAnInstant) {
            return direct;
        }
        Long nearest = null;
        for (Long reading : readings) {
            long distance = Math.abs(value - reading);
            if (nearest == null || distance < nearest) nearest = distance;
        }
        return nearest == null ? direct : nearest;
    }

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
        // Every instant each clock root was read at, as the composition
        // published them: a witness inside one execution's window is that
        // execution's clock, and the skew is measured against the reading
        // it is nearest to rather than against the seed's alone.
        Map<String, List<Long>> clockReadings = new LinkedHashMap<>();
        for (JsonElement element : array(object(manifest,
                ClockRootPhysics.MANIFEST_FIELD), "clockReads")) {
            if (!element.isJsonObject()) continue;
            JsonObject read = element.getAsJsonObject();
            List<Long> readings = new ArrayList<>();
            for (JsonElement reading : array(read, "readings")) {
                try {
                    readings.add(Long.parseLong(
                            reading.getAsString().trim()));
                } catch (RuntimeException notAnInstant) {
                    continue;
                }
            }
            if (!readings.isEmpty()) {
                clockReadings.put(optionalString(read, "solverTerm"),
                        readings);
            }
        }
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
            // A handoff variable is not a root and has no recorded value of
            // its own: what the ledger carries for it is whichever replay's
            // delivery the inventory saw first, and calling the difference
            // "a root moved" reported twelve unexplained moves on bug3 for
            // a formula in which no root had moved at all.  What may be
            // said about a delivery is said through its family, below.
            if (!optionalString(ledger,
                    InSessionReadResolver.HANDOFF_PHASE_ID).isEmpty()) {
                continue;
            }
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
                Long delta = nearestSkew(clockReadings.get(
                        assigned.getKey()), was, now);
                if (delta != null) {
                    mechanism.addProperty("skewMillis", delta);
                }
            } else if ("true".equals(was) || "false".equals(was)
                    || insideDeclaredDomain(ledger, now)) {
                // A declared root moved off the value it recorded: a Boolean
                // to its other polarity, an integral root to another value
                // of the domain the case declares.  Which of the two it is
                // says nothing about the mechanism -- the case declared the
                // root and the witness moved it within what the case allows.
                mechanism.addProperty("kind", "MARKER_FLIPPED");
            } else {
                mechanism.addProperty("kind", WitnessLegitimacy.ROOT_MOVED);
            }
            mechanisms.add(mechanism);
        }
        for (JsonElement element : familyMechanisms(manifest, witnessValues,
                recorded)) {
            mechanisms.add(element);
        }
        return mechanisms;
    }

    /**
     * The mechanism behind each delivery the witness took, via its family.
     *
     * <p>A handoff variable is free and its family says what it may be: one
     * arm per replay that delivered there, each guarded by the valuation
     * that replay ran under.  So the model's value at {@code v_H} names an
     * arm, the arm names the delivering replay, and that replay's own
     * assignment is the mechanism -- a marker it flipped, a clock it read
     * later, a configured root its obligation moved.  An arm whose replay
     * ran at everything the recording read states no mechanism at all: the
     * delivery is one the recorded topology made under the recorded roots,
     * and nothing here claims otherwise.</p>
     */
    private static JsonArray familyMechanisms(
            JsonObject manifest, Map<String, String> witnessValues,
            Map<String, JsonObject> recorded) {
        JsonArray mechanisms = new JsonArray();
        JsonObject merge = object(manifest, "pathMerge");
        Set<String> stated = new LinkedHashSet<>();
        for (JsonElement element : array(merge, "handoffFamilies")) {
            if (!element.isJsonObject()) continue;
            JsonObject family = element.getAsJsonObject();
            String term = optionalString(family, "handoffSolverTerm");
            String delivered = normalizeIntegral(witnessValues.get(term));
            if (term.isEmpty() || delivered.isEmpty()) continue;
            for (JsonElement encoded : array(family, "arms")) {
                if (!encoded.isJsonObject()) continue;
                JsonObject arm = encoded.getAsJsonObject();
                if (!delivered.equals(normalizeIntegral(
                        optionalString(arm, "deliveredValue")))) {
                    continue;
                }
                for (JsonElement stated_element
                        : array(arm, "valuation")) {
                    if (!stated_element.isJsonObject()) continue;
                    JsonObject ran = stated_element.getAsJsonObject();
                    String rootTerm = optionalString(ran, "solverTerm");
                    JsonObject ledger = recorded.get(rootTerm);
                    if (ledger == null) continue;
                    String was = optionalString(ledger, "recordedValue");
                    String now = normalizeIntegral(optionalString(ran,
                            "value"));
                    if (was.isEmpty() || now.isEmpty() || was.equals(now)
                            || !stated.add(term + "\n" + rootTerm)) {
                        continue;
                    }
                    JsonObject mechanism = new JsonObject();
                    mechanism.addProperty("sourceKey",
                            optionalString(ledger, "sourceKey"));
                    mechanism.addProperty("siteId",
                            optionalString(ledger, "siteId"));
                    mechanism.addProperty("solverTerm", rootTerm);
                    mechanism.addProperty("recordedValue", was);
                    mechanism.addProperty("witnessValue", now);
                    mechanism.addProperty("deliveredAt",
                            optionalString(family,
                                    InSessionReadResolver
                                            .HANDOFF_PHASE_ID));
                    mechanism.addProperty("deliveredBy",
                            optionalString(arm, "replayGroupId"));
                    if (optionalBool(ran, "wallClock", false)) {
                        mechanism.addProperty("kind", "CLOCK_SKEW");
                        Long delta = skewMillis(was, now);
                        if (delta != null) {
                            mechanism.addProperty("skewMillis", delta);
                        }
                    } else if ("true".equals(was) || "false".equals(was)) {
                        mechanism.addProperty("kind", "MARKER_FLIPPED");
                    } else {
                        mechanism.addProperty("kind",
                                WitnessLegitimacy.ROOT_MOVED);
                    }
                    mechanisms.add(mechanism);
                }
                break;
            }
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

    /**
     * The base text with every clock window assertion removed.
     *
     * <p>An unbounded case asserted none, so there is nothing to remove and
     * the text is already the question this asks: what does the target do
     * with the clocks free?</p>
     */
    static String dropClockWindows(String base,
                                   Map<String, JsonObject> clocks,
                                   long skew) {
        String text = base;
        for (Map.Entry<String, JsonObject> clock : clocks.entrySet()) {
            long recorded = optionalLongInteger(clock.getValue(),
                    "recordedValue", 0L);
            String window = ClockRootPhysics.window(clock.getKey(),
                    recorded, skew);
            if (window.isEmpty()) continue;
            text = text.replace(window, "true");
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
            String window = ClockRootPhysics.window(clock.getKey(),
                    recorded, skew);
            // Nothing to widen where the case asserted no window: the cell
            // is already free and a wider one would say less than nothing.
            if (window.isEmpty()) continue;
            text = text.replace(window, ClockRootPhysics.window(
                    clock.getKey(), recorded, wider));
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

    /**
     * The value range each root's own declaration allows, by solver term.
     *
     * <p>Two declarations, one meaning.  {@link ClockRootPhysics} states the
     * window a wall clock may have returned, and the case states the domain
     * any other declared root may take; the composition asserts both in the
     * formula, so a perturbation outside either is rejected by that
     * assertion rather than by anything the target predicate says.  Reading
     * the range here lets the probe stay inside it and stop mistaking its
     * own boundary for evidence -- bug3's serial number is declared
     * {@code [recorded, recorded+3]} and the probe tried {@code recorded-1},
     * which the domain refused, and reported the refusal as though the
     * target had decided it.</p>
     */
    /**
     * The domain the case declared for each root, by solver term.
     *
     * <p>Only these roots are enumerated: the domain is what the case says
     * the root may have been, so the values in it are the ones a witness may
     * rest on.  A root with no domain is pinned to its recording by the
     * composition and is not a question this solver asks.</p>
     */
    static Map<String, BigInteger[]> declaredDomains(JsonObject manifest) {
        Map<String, BigInteger[]> domains = new LinkedHashMap<>();
        for (JsonElement element : array(object(manifest,
                PathMergeComposer.MANIFEST_FIELD), "roots")) {
            if (!element.isJsonObject()) continue;
            JsonObject root = element.getAsJsonObject();
            String term = optionalString(root, "solverTerm");
            BigInteger low = integral(optionalString(root,
                    PathMergeComposer.DECLARED_DOMAIN_MIN));
            BigInteger high = integral(optionalString(root,
                    PathMergeComposer.DECLARED_DOMAIN_MAX));
            if (!term.isEmpty() && low != null && high != null) {
                domains.put(term, new BigInteger[] {low, high});
            }
        }
        return domains;
    }

    static Map<String, BigInteger[]> declaredWindows(JsonObject manifest) {
        Map<String, BigInteger[]> windows =
                new LinkedHashMap<>(declaredDomains(manifest));
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

    /** One declared bound as an integer, or null when it states none. */
    private static BigInteger integral(String stated) {
        try {
            return stated.trim().isEmpty() ? null
                    : new BigInteger(stated.trim());
        } catch (NumberFormatException notIntegral) {
            return null;
        }
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
            // A composition that refused publishes no ledgers at all.  An
            // absent ledger is that refusal restated, not a second finding:
            // no manual root was materialized, which is what an empty
            // catalog says.
            if (encoded == null || !encoded.isJsonArray()) {
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
            // As above: a refused composition materialized no source, and an
            // empty catalog says so without raising a gap the refusal
            // already raised.
            if (encoded == null || !encoded.isJsonArray()) {
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
                    // Three spellings, one shape.  A configured source
                    // names a SOURCE_PHASE., a wire value a HANDOFF_PHASE.,
                    // and a manual input its own id REGION.<r>.in.<uuid> --
                    // and all three are roots the campaign can vary through
                    // one runtime mechanism.  Requiring a prefix refused
                    // first every handoff materialization and then every
                    // manual one, in both cases after COMPOSE had accepted
                    // them.  What matters is that the identity is stated.
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
        private String z3 = "z3";
        private long timeoutMillis = 20_000L;
        private int maxInputs = 12;
        private int maxValuations = 4096;
        private int workers = 8;

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
            result.z3 = firstNonBlank(values.get("z3"), "z3");
            result.timeoutMillis = positiveLong(values.get("timeout-ms"),
                    20_000L);
            result.maxInputs = positiveInt(values.get("max-inputs"), 12);
            result.maxValuations = positiveInt(values.get(
                    "max-valuations"), 4096);
            result.workers = positiveInt(values.get("workers"), 8);
            return result;
        }

        private static boolean option(String key) {
            return "smt".equals(key) || "manifest".equals(key)
                    || "runtime-plan".equals(key)
                    || "z3".equals(key)
                    || "timeout-ms".equals(key)
                    || "max-inputs".equals(key)
                    || "max-valuations".equals(key)
                    || "workers".equals(key);
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
