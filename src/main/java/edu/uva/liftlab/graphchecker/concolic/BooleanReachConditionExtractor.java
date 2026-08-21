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
 * finite Boolean root-input domain.
 *
 * <p>The extractor never accepts caller-authored reachability formulas.  It
 * discovers Java Boolean input ports from the static region IR, joins them to
 * the exact canonical terms already emitted by {@link ConcolicSmtComposer},
 * removes inputs supplied by composed producer outputs, and asks
 * Z3 about every remaining Boolean valuation.  The resulting truth table and
 * canonical DNF are therefore derived candidate artifacts of the composed
 * SMT. For integral non-Boolean roots it may additionally perturb one value
 * in a satisfying witness; a rejected neighboring tuple proves the complete
 * root space is constrained without pretending to enumerate it. This class
 * never promotes either result to a trusted final result.</p>
 */
public final class BooleanReachConditionExtractor {
    private static final int MAX_EXISTENTIAL_PERTURBATIONS = 32;
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

        List<String> gaps = new ArrayList<>();
        validateCompositionAuthority(manifest, gaps);
        if (firstNonBlank(composedSmt).isEmpty()) {
            gaps.add("COMPOSED_SMT_EMPTY");
        }

        PortCatalog ports = PortCatalog.from(regions);
        Discovery discovery = discover(composedSmt, ports,
                PortOccurrenceCatalog.from(manifest));
        List<RootInput> inputs = discovery.rootInputs;
        JsonObject roots = new JsonObject();
        roots.add("booleanInputs", inputCatalog(inputs));
        roots.add("existentialInputs", inputCatalog(
                discovery.existentialNonBooleanRootInputs));
        report.add("roots", roots);

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
        String domainBase = appendBooleanDomain(base,
                discovery.booleanDomainInputs);
        List<boolean[]> satisfyingValuations = new ArrayList<>();
        JsonArray valuationRows = new JsonArray();
        JsonArray existentialPerturbations = new JsonArray();
        boolean rejectedExistentialPerturbation = false;
        boolean existentialProbeAttempted = false;
        int solverErrors = 0;
        int count = (int) valuationCount;
        for (int ordinal = 0; ordinal < count; ordinal++) {
            boolean[] values = valuation(ordinal, inputs.size());
            String query = valuationQuery(domainBase, inputs, values);
            ConcolicConstraintSolver.SolverOutput result =
                    solver.check(query);
            String status = result.status();
            JsonObject row = valuationRow(values, status);
            if ("sat".equals(status)) {
                satisfyingValuations.add(values.clone());
                JsonArray witness = existentialWitness(solver, query,
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

        // Every Boolean assignment was queried above; the DNF is built from
        // exactly the SAT rows.  A second "base implies DNF" solver call only
        // rechecks that exhaustive table and adds no admission evidence.
        boolean complete = solverErrors == 0;
        // Best-effort branch replay never proves that all program paths were
        // explored.  A satisfying selected case is still a bounded witness;
        // only an open recorded read-from model makes an unsatisfiable answer
        // inconclusive.
        boolean observedUnderapproximation = !recordedModelComplete;
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
                    "INCONCLUSIVE_UNDERAPPROXIMATION");
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

    /**
     * States whether the degeneracy question was decided, and on what.
     *
     * <p>A satisfying model is worth nothing when the reach condition admits
     * the whole root space: it then says only that the target's method runs,
     * which the recording already showed.  The formula alone cannot be read
     * for that.  It is a DNF over the Boolean roots only, so it collapses to
     * the constant {@code "true"} both when every enumerated valuation is
     * admitted - the degenerate case - and when there was no Boolean root to
     * enumerate at all, where {@code "true"} is the DNF's arity and not a
     * measurement.  An empty {@code values} vector is the same arity restated
     * and is likewise not evidence.  So the verdict is published, not left to
     * be inferred from a constant that has two meanings.</p>
     *
     * <p>Only two verdicts are provable from an exhaustive Boolean table:
     * some enumerated valuation is refused, so the condition demonstrably
     * cuts the root space; or that space is non-empty, was enumerated whole,
     * and every point of it reaches.  A surviving existential root makes the
     * space infinite and unenumerated, so an exhaustive verdict is not
     * available.  A rejected scalar tuple adjacent to a satisfying witness is
     * nevertheless a complete counterexample to the claim that every root
     * assignment reaches, and therefore proves the space is constrained.  If
     * no such counterexample is found, the check remains undecided rather
     * than treating a finite probe as an exhaustive pass.</p>
     *
     * <p>A root is an input no composed producer supplies - a freedom.  Where
     * there is none the condition has nothing it could be a tautology over,
     * and satisfiability of the whole composed system is the strongest answer
     * available rather than the weakest.  That is not degeneracy either, and
     * it is named too, so it can never be mistaken for a check that ran.  An
     * unsupplied input whose encoding this report cannot decode is a freedom
     * it never enumerated, so it blocks the same claim: the space was not
     * covered whole and the exhaustive reading of it would be a fiction.</p>
     */
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
        // What this stage needs is a composition that produced a usable
        // model: the Composer's own artifact, and its own "CANDIDATE_READY".
        // An under-approximate model is still one - its formula is the run's
        // evidence, and the only thing its openness forbids is reading UNSAT
        // as unreachability, which the reach condition states.  Whether the
        // model may be accepted as the milestone artifact is finalStatus, and
        // it is decided by the Composer alone; re-deriving an eligibility of
        // our own out of its members is the second gate README forbids.
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

    private static Discovery discover(String smt, PortCatalog ports,
                                      PortOccurrenceCatalog occurrences) {
        List<RootInput> roots = new ArrayList<>();
        List<RootInput> domainInputs = new ArrayList<>();
        List<RootInput> scalarRoots = new ArrayList<>();
        // An unsupplied input this extractor cannot decode is still a freedom
        // of the model; it is only one this report cannot name.  Counting it
        // is what keeps "the root space was enumerated whole" honest, because
        // a silently dropped freedom would make that claim of an
        // under-counted space.
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
                RootInput input = new RootInput(port,
                        occurrence.occurrenceId, occurrence.solverTerm,
                        "");
                domainInputs.add(input);
                if (occurrence.supplied) {
                    continue;
                }
                roots.add(input);
            } else if (occurrence.supplied) {
                continue;
            } else {
                scalarRoots.add(new RootInput(port,
                        occurrence.occurrenceId, occurrence.solverTerm,
                        occurrence.nullnessSolverTerm));
            }
        }
        Comparator<RootInput> byOccurrence = Comparator
                .comparing((RootInput value) -> value.port.id)
                .thenComparing(value -> value.occurrenceId);
        Collections.sort(roots, byOccurrence);
        Collections.sort(domainInputs, Comparator.comparing(
                (RootInput value) -> value.port.id).thenComparing(
                value -> value.occurrenceId));
        Collections.sort(scalarRoots, byOccurrence);
        return new Discovery(roots, domainInputs, scalarRoots,
                undecoded.size());
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
                                              List<RootInput> inputs) {
        StringBuilder result = new StringBuilder(base);
        for (RootInput input : inputs) {
            result.append("(assert ").append(input.domainFormula())
                    .append(")").append(System.lineSeparator());
        }
        return result.toString();
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

        Z3Solver(String executable, long timeoutMillis) throws IOException {
            this.timeoutMillis = Math.max(1L, timeoutMillis);
            this.executable = resolveExecutable(firstNonBlank(executable,
                    "z3"));
            this.artifact = ArtifactIO.artifact(this.executable);
        }

        JsonObject artifact() {
            return artifact.deepCopy();
        }

        ConcolicConstraintSolver.SolverOutput check(String smt)
                throws IOException,
                InterruptedException {
            String query = smt;
            if (SmtArrayExtensionalityAudit
                    .provesExtensionalityRedundant(smt)) {
                query = "(set-option :smt.array.extensional false)\n"
                        + "(set-option :smt.random_seed 7)\n"
                        + "(set-option :sat.random_seed 7)\n" + smt;
            }
            return ConcolicConstraintSolver.run(executable, query,
                    timeoutMillis);
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
        private final List<RootInput> booleanDomainInputs;
        private final List<RootInput> existentialNonBooleanRootInputs;
        private final int undecodedFreeInputCount;

        private Discovery(List<RootInput> rootInputs,
                          List<RootInput> booleanDomainInputs,
                          List<RootInput> existentialNonBooleanRootInputs,
                          int undecodedFreeInputCount) {
            this.rootInputs = rootInputs;
            this.booleanDomainInputs = booleanDomainInputs;
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

        private RootInput(PortInfo port, String occurrenceId,
                          String solverTerm,
                          String nullnessSolverTerm) {
            this.port = port;
            this.occurrenceId = firstNonBlank(occurrenceId);
            this.solverTerm = solverTerm;
            this.nullnessSolverTerm = firstNonBlank(nullnessSolverTerm);
        }

        private String literal(boolean value) {
            return "(= " + solverTerm + " "
                    + (value ? "true" : "false") + ")";
        }

        private String domainFormula() {
            return "true";
        }

        private List<String> neighboringLiterals(String value) {
            ScalarEncoding encoding = ScalarEncoding.of(port.descriptor);
            return encoding == null ? Collections.<String>emptyList()
                    : encoding.neighboringLiterals(value);
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("portId", port.id);
            result.addProperty("occurrenceId", occurrenceId);
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

    /**
     * The values that make this valuation satisfiable.
     *
     * <p>Reachability is stated existentially over the non-boolean roots, so
     * the verdict is complete without them — but a report that says a failure
     * is reachable and cannot say on what is a claim the reader has to take on
     * trust. Ask the solver, once, for the assignment it already found.</p>
     *
     * <p>The witness is evidence, never a premise: it is read off a query that
     * was already answered, and nothing downstream constrains anything by it.
     * A solver that will not answer leaves the row as it was.</p>
     */
    private static JsonArray existentialWitness(
            Z3Solver solver, String query, List<RootInput> roots) {
        JsonArray witness = new JsonArray();
        if (roots.isEmpty()) return witness;
        StringBuilder terms = new StringBuilder();
        for (RootInput root : roots) {
            terms.append(' ').append(root.solverTerm);
        }
        try {
            ConcolicConstraintSolver.SolverOutput answer = solver.check(
                    query + "\n(get-value (" + terms.toString().trim()
                            + "))");
            if (!"sat".equals(answer.status())) return witness;
            Map<String, String> assigned =
                    ConcolicConstraintSolver.getValues(answer.stdout);
            for (RootInput root : roots) {
                String value = assigned.get(root.solverTerm);
                if (value == null) continue;
                JsonObject row = new JsonObject();
                row.addProperty("portId", root.port.id);
                row.addProperty("occurrenceId", root.occurrenceId);
                row.addProperty("solverTerm", root.solverTerm);
                row.addProperty("value", value);
                witness.add(row);
            }
        } catch (IOException | InterruptedException unanswered) {
            if (unanswered instanceof InterruptedException) {
                Thread.currentThread().interrupt();
            }
            return new JsonArray();
        }
        return witness;
    }

    /**
     * Looks for a rejected point adjacent to an already satisfying scalar
     * root assignment.
     *
     * <p>This does not pretend to enumerate an infinite Java scalar domain.
     * Each query fixes the complete non-boolean root tuple to the solver's
     * witnessed values and changes exactly one integral root by one.  One
     * UNSAT result is enough to disprove that the composed candidate admits
     * the whole root space.  SAT results prove nothing about the rest of the
     * domain and are never treated as exhaustive.</p>
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

        private PortInfo(String id, String javaType) {
            this.id = firstNonBlank(id);
            this.descriptor = javaTypeDescriptor(javaType);
            this.javaBoolean = "Z".equals(descriptor)
                    || "Ljava/lang/Boolean;".equals(descriptor);
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

    /**
     * Rejects cross-wired CLI artifacts before any solver process starts.
     * The composer manifest is the trust root: it fingerprints the exact SMT,
     * and static-region ledger.
     */
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
