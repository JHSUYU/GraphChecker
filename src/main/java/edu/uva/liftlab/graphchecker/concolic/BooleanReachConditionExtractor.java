package edu.uva.liftlab.graphchecker.concolic;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.artifact;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sibling;
import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
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
        validateArtifactBindings(arguments.smt, arguments.runtimePlan,
                manifest);
        Z3Solver solver = new Z3Solver(arguments.z3,
                arguments.timeoutMillis,
                array(manifest, "caseSelectorPartitions"),
                arguments.workers);
        JsonObject report = extract(smt, manifest, solver,
                arguments.maxInputs, arguments.maxValuations);
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
        JsonObject report = new JsonObject();
        report.addProperty("schemaVersion", 3);
        report.addProperty("kind", "BOOLEAN_REACH_CONDITION_REPORT");
        boolean guardedReadModelComplete =
                optionalBool(manifest, "guardedReadModelComplete", false);
        report.addProperty("guardedReadModelComplete",
                guardedReadModelComplete);
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
                    guardedReadModelComplete
                            ? "INCONCLUSIVE_OPEN_PATH_CLOSURE"
                            : "INCONCLUSIVE_UNDERAPPROXIMATION");
        }
        String degeneracy = degeneracyCheck(formula, reachability,
                inputs.size(),
                discovery.existentialNonBooleanRootInputs.size(),
                rejectedExistentialPerturbation);
        reachCondition.addProperty("degeneracyCheck", degeneracy);
        report.add("reachCondition", reachCondition);
        JsonArray resultGaps = new JsonArray();
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
        report.addProperty("state", complete && !unconstrainedRootSpace
                ? "CANDIDATE_READY" : "CANDIDATE_WITH_GAPS");
        return report;
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
            gaps.add("COMPOSITION_MANIFEST_NOT_CANDIDATE_MODEL_ELIGIBLE");
        }
        validatePropagationContract(composedSmt, manifest, gaps);
    }

    /** Checks the selector-to-PC definitions used by the emitted formula. */
    private static void validatePropagationContract(
            String composedSmt, JsonObject manifest, List<String> gaps) {
        JsonElement caseDependencies = manifest == null ? null
                : manifest.get("casePathConditionDependencies");
        if (caseDependencies == null || !caseDependencies.isJsonArray()) {
            gaps.add("CASE_PATH_CONDITION_DEPENDENCIES_MISSING");
        } else {
            validateCasePathConditionDependencies(composedSmt, manifest,
                    caseDependencies.getAsJsonArray(), gaps);
        }
    }

    /**
     * Proves that every propagated output arm still carries its own PC.
     *
     * <p>The propagation ledger may name an expression arm only when its
     * base selector belongs to one occurrence-local exactly-one partition,
     * the arm's owner deterministically names that base selector, and the
     * emitted SMT contains the Composer's named {@code selector => PC}
     * definition. Replay-specific arms may share the same owner only when
     * they carry distinct observation selectors linked back to that base
     * case. A selector with no definition would turn a guarded value into a
     * free solver choice, so it remains a hard composition gap.</p>
     */
    private static void validateCasePathConditionDependencies(
            String smt, JsonObject manifest, JsonArray dependencies,
            List<String> gaps) {
        JsonElement encodedPartitions = manifest == null ? null
                : manifest.get("caseSelectorPartitions");
        if (encodedPartitions == null
                || !encodedPartitions.isJsonArray()) {
            gaps.add("CASE_SELECTOR_PARTITIONS_MISSING");
            return;
        }

        Map<String, List<Integer>> partitionsBySelector =
                new LinkedHashMap<>();
        JsonArray partitions = encodedPartitions.getAsJsonArray();
        for (int partitionIndex = 0;
             partitionIndex < partitions.size(); partitionIndex++) {
            JsonElement encodedPartition = partitions.get(partitionIndex);
            if (!encodedPartition.isJsonArray()) {
                gaps.add("CASE_SELECTOR_PARTITION_MALFORMED:"
                        + partitionIndex);
                continue;
            }
            Set<String> local = new LinkedHashSet<>();
            JsonArray partition = encodedPartition.getAsJsonArray();
            for (JsonElement encodedSelector : partition) {
                if (!encodedSelector.isJsonPrimitive()
                        || !encodedSelector.getAsJsonPrimitive().isString()
                        || firstNonBlank(encodedSelector.getAsString())
                        .isEmpty()) {
                    gaps.add("CASE_SELECTOR_PARTITION_MALFORMED:"
                            + partitionIndex);
                    continue;
                }
                String selector = encodedSelector.getAsString();
                if (!local.add(selector)) {
                    gaps.add("CASE_SELECTOR_PARTITION_DUPLICATE:"
                            + selector);
                    continue;
                }
                partitionsBySelector.computeIfAbsent(selector,
                        ignored -> new ArrayList<>()).add(partitionIndex);
            }
        }

        Map<String, Integer> targetReachGuards = new LinkedHashMap<>();
        for (JsonElement encodedTarget : array(manifest,
                "targetReachLedger")) {
            if (!encodedTarget.isJsonObject()) continue;
            String guard = optionalString(encodedTarget.getAsJsonObject(),
                    "caseGuard");
            if (!guard.isEmpty()) {
                targetReachGuards.merge(guard, 1, Integer::sum);
            }
        }

        Set<String> dependencyIdentities = new LinkedHashSet<>();
        for (int dependencyIndex = 0;
             dependencyIndex < dependencies.size(); dependencyIndex++) {
            JsonElement encodedDependency = dependencies.get(dependencyIndex);
            if (!encodedDependency.isJsonObject()) {
                gaps.add("CASE_PATH_CONDITION_DEPENDENCY_MALFORMED:"
                        + dependencyIndex);
                continue;
            }
            JsonObject dependency = encodedDependency.getAsJsonObject();
            String family = optionalString(dependency, VmExpressionIr.FAMILY_KEY);
            String boundaryKind = optionalString(dependency, "boundaryKind");
            String epoch = optionalString(dependency, VmExpressionIr.TOPOLOGY_EPOCH);
            JsonElement encodedArms = dependency.get("arms");
            if (optionalInteger(dependency, "schemaVersion", -1)
                    != SymbolicPropagationClosure.SCHEMA_VERSION
                    || !SymbolicPropagationClosure.DEPENDENCY_KIND.equals(
                    optionalString(dependency, "kind"))
                    || !"REGION_CASE_PC_V1".equals(
                    optionalString(dependency, "authority"))
                    || family.isEmpty() || epoch.isEmpty()
                    || !(VmExpressionIr.RPC_ATTACH.equals(boundaryKind)
                    || VmExpressionIr.FIELD_READ.equals(boundaryKind))
                    || encodedArms == null || !encodedArms.isJsonArray()
                    || encodedArms.getAsJsonArray().size() == 0
                    || !dependencyIdentities.add(family)) {
                gaps.add("CASE_PATH_CONDITION_DEPENDENCY_MALFORMED:"
                        + dependencyIndex);
                continue;
            }

            Set<String> armIdentities = new LinkedHashSet<>();
            JsonArray arms = encodedArms.getAsJsonArray();
            for (int armIndex = 0; armIndex < arms.size(); armIndex++) {
                JsonElement encodedArm = arms.get(armIndex);
                if (!encodedArm.isJsonObject()) {
                    gaps.add("CASE_PATH_CONDITION_ARM_MALFORMED:"
                            + dependencyIndex + ":" + armIndex);
                    continue;
                }
                JsonObject arm = encodedArm.getAsJsonObject();
                String owner = optionalString(arm, "caseOwner");
                String baseSelector = optionalString(arm, "caseSelector");
                String encodedSelector = optionalString(arm, "selector");
                String observationSelector = optionalString(arm,
                        SymbolicPropagationClosure.OBSERVATION_SELECTOR);
                String selector = firstNonBlank(observationSelector,
                        encodedSelector);
                String region = optionalString(arm, "regionId");
                String occurrence = optionalString(arm, "occurrenceId");
                String armIdentity = owner + "\u0000" + selector;
                boolean selectorShapeMatches = observationSelector.isEmpty()
                        ? encodedSelector.equals(baseSelector)
                        : encodedSelector.equals(observationSelector);
                if (owner.isEmpty() || baseSelector.isEmpty()
                        || selector.isEmpty()
                        || region.isEmpty() || occurrence.isEmpty()
                        || !armIdentities.add(armIdentity)
                        || !selectorShapeMatches
                        || !caseOwnerMatchesOccurrence(owner, region,
                        occurrence)
                        || !baseSelector.equals(
                        LocalCaseIdentity.selector(owner))) {
                    gaps.add("CASE_PATH_CONDITION_ARM_MALFORMED:"
                            + dependencyIndex + ":" + armIndex);
                    continue;
                }

                boolean initialSource =
                        SymbolicPropagationClosure.isInitialSourceCase(
                                owner, region, occurrence);
                if (initialSource
                        && !(VmExpressionIr.FIELD_READ.equals(boundaryKind)
                        && SymbolicPropagationClosure
                        .READ_FROM_DEPENDENCY_POLICY.equals(
                                optionalString(dependency, "selectionPolicy"))
                        && observationSelector.isEmpty()
                        && selector.equals(baseSelector)
                        && arm.has("pathCondition")
                        && arm.get("pathCondition").isJsonArray()
                        && arm.getAsJsonArray("pathCondition").size() == 0)) {
                    gaps.add("INITIAL_SOURCE_DEPENDENCY_MALFORMED:"
                            + selector);
                    continue;
                }

                int targetReachGuardCount = targetReachGuards.getOrDefault(
                        baseSelector, 0);
                boolean targetOwned = targetReachGuardCount > 0;
                if (initialSource) {
                    // INITIAL is the value present when a location first
                    // becomes symbolic.  Its empty PC is true; it has no
                    // producer region, case partition, or case-PC assertion.
                } else if (targetOwned) {
                    if (targetReachGuardCount != 1) {
                        gaps.add("CASE_DEPENDENCY_TARGET_GUARD_NOT_UNIQUE:"
                                + baseSelector);
                    }
                } else {
                    List<Integer> memberships = partitionsBySelector.get(
                            baseSelector);
                    if (memberships == null || memberships.size() != 1) {
                        gaps.add(
                                "CASE_DEPENDENCY_SELECTOR_PARTITION_NOT_UNIQUE:"
                                        + baseSelector);
                    }
                }
                // INITIAL_SOURCE is a provenance record for the value that
                // existed when a location first became symbolic.  Its empty
                // PC contributes true, so the synthetic case selector is not
                // emitted unless the SMT actually uses it as a guard.  An
                // absent selector is therefore no solver freedom to validate.
                boolean selectorDeclared = smt.contains(
                        "(declare-const " + selector + " Bool)");
                if (initialSource && !selectorDeclared) {
                    continue;
                }
                if (!selectorDeclared) {
                    gaps.add("CASE_DEPENDENCY_SELECTOR_DECLARATION_MISSING:"
                            + selector);
                }
                if (!selector.equals(baseSelector)
                        && !smt.contains("(declare-const " + baseSelector
                        + " Bool)")) {
                    gaps.add(
                            "CASE_DEPENDENCY_BASE_SELECTOR_DECLARATION_MISSING:"
                                    + baseSelector);
                }
                if (initialSource) {
                    // The guarded-read selector activates this source.  There
                    // is no independent producer path to define.
                } else if (targetOwned
                        && !targetPathDefinitionDeclared(smt,
                        baseSelector)) {
                    gaps.add(
                            "CASE_DEPENDENCY_TARGET_DEFINITION_MISSING:"
                                    + baseSelector);
                } else if (!targetOwned
                        && !casePcDefinitionDeclared(smt, selector)) {
                    gaps.add("CASE_DEPENDENCY_PC_DEFINITION_MISSING:"
                            + selector);
                }
                if (!observationSelector.isEmpty()
                        && !caseObservationPartitionDeclared(smt,
                        baseSelector, observationSelector)) {
                    gaps.add("CASE_DEPENDENCY_BASE_DEFINITION_MISSING:"
                            + baseSelector + ":" + observationSelector);
                }
            }
        }
    }

    /** Matches either an activation owner or its stable planned address. */
    static boolean caseOwnerMatchesOccurrence(String owner, String region,
                                               String occurrence) {
        if (SymbolicPropagationClosure.isInitialSourceCase(owner, region,
                occurrence)) return true;
        String prefix = "region:" + region + "/instance:";
        if (owner.startsWith(prefix + occurrence + "/case:")) return true;
        String planned = OccurrenceId.parse(occurrence).planned();
        return owner.startsWith(prefix + planned + "/case:");
    }

    /** Exact assertion shape emitted by the Composer's case-PC authority. */
    private static boolean casePcDefinitionDeclared(String smt,
                                                     String selector) {
        String implication = "(=> " + selector + " ";
        for (String line : firstNonBlank(smt).split("\\R")) {
            if (line.contains(implication)
                    && line.contains(":named case_selector_definition_")) {
                return true;
            }
        }
        return false;
    }

    /** Observation PCs refine, rather than replace, their base case. */
    private static boolean caseObservationPartitionDeclared(
            String smt, String baseSelector, String observationSelector) {
        String baseTerm = "(ite " + baseSelector + " 1 0)";
        String observationTerm = "(ite " + observationSelector + " 1 0)";
        for (String line : firstNonBlank(smt).split("\\R")) {
            if (line.contains(baseTerm) && line.contains(observationTerm)
                    && line.contains(
                    ":named region_case_observation_partition_")) {
                return true;
            }
        }
        return false;
    }

    /** Target cases are owned by the target ledger, not producer partitions. */
    private static boolean targetPathDefinitionDeclared(String smt,
                                                        String selector) {
        String implication = "(=> " + selector + " ";
        for (String line : firstNonBlank(smt).split("\\R")) {
            if (line.contains(implication)
                    && line.contains(
                    ":named target_path_selector_definition_")) {
                return true;
            }
        }
        return false;
    }

    /** The Composer's single, internally consistent UNSAT closure claim. */
    private static boolean unsatClosureComplete(JsonObject manifest) {
        if (manifest == null
                || !optionalBool(manifest,
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE, false)
                || !ConcolicSmtComposer.FINAL_READY.equals(
                optionalString(manifest, ConcolicSmtComposer.FINAL_STATUS))) {
            return false;
        }
        JsonObject evidence = object(manifest,
                ConcolicSmtComposer.UNSAT_CLOSURE_EVIDENCE);
        JsonElement partial = evidence.get("partialProducerSummaryIds");
        return optionalInteger(evidence, "schemaVersion", -1) == 1
                && "UNSAT_CLOSURE_EVIDENCE".equals(
                optionalString(evidence, "kind"))
                && ConcolicSmtComposer.UNSAT_CLOSURE_AUTHORITY.equals(
                optionalString(evidence, "authority"))
                // The manifest states the guarded-read verdict once; the
                // remaining components are the closure itself, and their
                // conjunction is what the evidence used to restate.
                && optionalBool(manifest, "guardedReadModelComplete", false)
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
        private final JsonArray attempts = new JsonArray();
        private final List<List<String>> casePartitions = new ArrayList<>();
        private final int workers;
        private int queryOrdinal;

        Z3Solver(String executable, long timeoutMillis,
                 JsonArray partitions, int workers) throws IOException {
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

        synchronized JsonArray attempts() {
            return attempts.deepCopy();
        }

        ConcolicConstraintSolver.SolverOutput check(String smt)
                throws IOException,
                InterruptedException {
            int currentQuery = queryOrdinal++;
            PartitionPlan plan = splitPartitions();
            if (plan.primary.isEmpty()) {
                return attempt(currentQuery, 0, "Z3", smt,
                        timeoutMillis, Collections.emptyList());
            }
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
                    if ("sat".equals(result.status())) return result;
                    if ("unsat".equals(result.status())) unsat = result;
                    else undecided = result;
                }
                return undecided == null ? unsat : undecided;
            } finally {
                pool.shutdownNow();
                pool.awaitTermination(10, TimeUnit.SECONDS);
            }
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
                        smt, partitions, assignment), selectors));
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
                    result.add(new PartitionQuery(
                            condition(parent.smt, partition, chosen),
                            selectors));
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

            private PartitionQuery(String smt, List<String> selectors) {
                this.smt = smt;
                this.selectors = selectors;
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
                result.addProperty("displayName", occurrenceId + "::"
                        + portId);
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
                // Name each entry independently because one site may
                // materialize multiple roots with otherwise equal metadata.
                result.addProperty("displayName", sourceKey + "::"
                        + sourceId + "::" + occurrenceId + "::"
                        + sourcePhaseId);
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
        BOOL("BOOL", "Bool"),
        BYTE("INT", "Int"),
        CHAR("INT", "Int"),
        SHORT("INT", "Int"),
        INT("INT", "Int"),
        LONG("INT", "Int"),
        FLOAT32("FLOAT32", "(_ FloatingPoint 8 24)"),
        FLOAT64("FLOAT64", "(_ FloatingPoint 11 53)"),
        STRING("STRING", "String");

        private final String occurrenceSort;
        private final String solverSort;

        ScalarEncoding(String occurrenceSort, String solverSort) {
            this.occurrenceSort = occurrenceSort;
            this.solverSort = solverSort;
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
    private static JsonArray existentialPerturbations(
            Z3Solver solver, String query, List<RootInput> roots,
            JsonArray witness) {
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

    /** Exact region-local root terms published by the Composer. */
    private static final class ManualSymbolicRootCatalog {
        private final List<ManualSymbolicRootGroup> roots = new ArrayList<>();

        private static ManualSymbolicRootCatalog from(
                JsonObject manifest, List<String> gaps) {
            ManualSymbolicRootCatalog result = new ManualSymbolicRootCatalog();
            JsonElement encoded = manifest == null ? null : manifest.get(
                    ConcolicSmtComposer.MANUAL_SOURCE_MATERIALIZATION_FIELD);
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
                    || !ConcolicSmtComposer.MANUAL_SOURCE_MATERIALIZATION_KIND.equals(
                    optionalString(row, "kind"))
                    || !ConcolicSmtComposer.MANUAL_SOURCE_MATERIALIZATION_AUTHORITY
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
                    ConcolicSmtComposer
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
                    || !ConcolicSmtComposer
                    .CONFIGURED_SOURCE_MATERIALIZATION_KIND.equals(
                    optionalString(row, "kind"))
                    || !ConcolicSmtComposer
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
            return result;
        }

        private static boolean option(String key) {
            return "smt".equals(key) || "manifest".equals(key)
                    || "runtime-plan".equals(key)
                    || "output".equals(key) || "z3".equals(key)
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
