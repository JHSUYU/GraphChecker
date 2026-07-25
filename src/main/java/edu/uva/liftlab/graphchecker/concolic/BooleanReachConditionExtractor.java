package edu.uva.liftlab.graphchecker.concolic;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.artifact;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sibling;
import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
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
import java.util.concurrent.TimeUnit;
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
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();
    private BooleanReachConditionExtractor() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        JsonObject manifest = ArtifactIO.readObject(arguments.manifest);
        Path relationshipsPath = arguments.relationships;
        String smt = ArtifactIO.readText(arguments.smt);
        JsonObject relationships = ArtifactIO.readObject(relationshipsPath);
        List<JsonObject> regions = ArtifactIO.readJsonl(arguments.regions);
        validateArtifactBindings(arguments.smt, arguments.regions,
                relationshipsPath, manifest);
        Z3Solver solver = new Z3Solver(arguments.z3,
                arguments.timeoutMillis);
        JsonObject report = extract(smt, manifest, regions,
                relationships, solver,
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
                              List<JsonObject> regions,
                              JsonObject relationships, Solver solver,
                              int maxInputs, int maxValuations)
            throws IOException, InterruptedException {
        JsonObject report = new JsonObject();
        report.addProperty("schemaVersion", 3);
        report.addProperty("kind", "BOOLEAN_REACH_CONDITION_REPORT");
        report.addProperty("trustState", "CANDIDATE_ONLY");

        List<String> gaps = new ArrayList<>();
        validateCompositionAuthority(manifest, relationships, gaps);
        if (firstNonBlank(composedSmt).isEmpty()) {
            gaps.add("COMPOSED_SMT_EMPTY");
        }

        PortCatalog ports = PortCatalog.from(regions);
        Discovery discovery = discover(composedSmt, relationships, ports);
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
        List<Valuation> valuations = new ArrayList<>();
        JsonArray valuationRows = new JsonArray();
        int satisfying = 0;
        int solverErrors = 0;
        int count = (int) valuationCount;
        for (int ordinal = 0; ordinal < count; ordinal++) {
            boolean[] values = valuation(ordinal, inputs.size());
            String query = valuationQuery(domainBase, inputs, values);
            SolverResult result = solver.check(query);
            Valuation valuation = new Valuation(values, result.status);
            valuations.add(valuation);
            JsonObject row = valuation.toJson(inputs);
            if ("sat".equals(result.status)) {
                satisfying++;
            } else if (!"unsat".equals(result.status)) {
                row.addProperty("solverOutput", result.output);
                solverErrors++;
            }
            valuationRows.add(row);
        }

        report.add("valuations", valuationRows);

        // Every Boolean assignment was queried above; the DNF is built from
        // exactly the SAT rows.  A second "base implies DNF" solver call only
        // rechecks that exhaustive table and adds no admission evidence.
        boolean complete = solverErrors == 0;
        String reachability = !complete
                ? "UNKNOWN" : satisfying > 0
                ? "REACHABLE" : "UNREACHABLE";
        JsonObject reachCondition = new JsonObject();
        reachCondition.addProperty("formula", dnf(inputs, valuations));
        reachCondition.addProperty("reachability", reachability);
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

    private static void validateCompositionAuthority(
            JsonObject manifest, JsonObject relationships,
            List<String> gaps) {
        boolean commonManifest = manifest != null
                && integer(manifest, "schemaVersion", -1) == 2
                && "CONCOLIC_COMPOSED_SMT".equals(string(manifest, "kind"));
        boolean commonRelationships = relationships != null
                && integer(relationships, "schemaVersion", -1) == 2
                && "SYMBOLIC_RELATIONSHIP_CANDIDATES".equals(string(
                relationships, "kind"));
        if (!commonManifest
                || !"CANDIDATE_READY".equals(string(manifest, "state"))
                || !"CANDIDATE_ONLY".equals(string(manifest,
                "trustState"))) {
            gaps.add("COMPOSITION_MANIFEST_NOT_CANDIDATE_MODEL_ELIGIBLE");
        }
        if (!commonRelationships
                || !"CANDIDATE_ONLY".equals(string(relationships,
                "trustState"))) {
            gaps.add("RELATIONSHIP_CATALOG_NOT_CANDIDATE_MODEL_ELIGIBLE");
        }
    }

    private static Discovery discover(String smt,
                                      JsonObject relationships,
                                      PortCatalog ports) {
        Set<String> upstreamSupplied = suppliedInputs(relationships, ports);
        List<RootInput> roots = new ArrayList<>();
        List<RootInput> domainInputs = new ArrayList<>();
        List<RootInput> scalarRoots = new ArrayList<>();
        for (PortInfo port : ports.sortedInputs()) {
            ScalarEncoding encoding = ScalarEncoding.of(port.descriptor);
            if (!port.javaBoolean && encoding == null) continue;
            if (port.javaBoolean) {
                encoding = ScalarEncoding.INT;
            }
            String solverTerm = encoding.solverTerm(port.id);
            String portTerm = "port__" + smtName(port.id);
            String nullnessSolverTerm = encoding == ScalarEncoding.STRING
                    ? "sym__port__" + smtName(port.id)
                    + "__string_is_null" : "";
            boolean declared = canonicalScalarBindingDeclared(smt, portTerm,
                    solverTerm, nullnessSolverTerm, encoding);
            if (!declared) continue;
            if (port.javaBoolean) {
                RootInput input = new RootInput(port, solverTerm, "");
                domainInputs.add(input);
                if (upstreamSupplied.contains(port.id)) {
                    continue;
                }
                roots.add(input);
            } else if (upstreamSupplied.contains(port.id)) {
                continue;
            } else {
                scalarRoots.add(new RootInput(port, solverTerm,
                        nullnessSolverTerm));
            }
        }
        Collections.sort(roots, Comparator.comparing(value -> value.port.id));
        Collections.sort(domainInputs, Comparator.comparing(
                value -> value.port.id));
        Collections.sort(scalarRoots, Comparator.comparing(
                value -> value.port.id));
        return new Discovery(roots, domainInputs, scalarRoots);
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
        return smt.contains("(= " + portTerm + " ("
                + encoding.valueConstructor + " " + solverTerm + "))")
                || smt.contains("(= (" + encoding.valueConstructor + " "
                + solverTerm + ") " + portTerm + ")");
    }

    private static Set<String> suppliedInputs(JsonObject relationships,
                                              PortCatalog ports) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : array(relationships, "relationships")) {
            if (!element.isJsonObject()) continue;
            JsonObject roles = object(element.getAsJsonObject(), "roles");
            String left = string(roles, "left");
            String right = string(roles, "right");
            if (ports.inputs.containsKey(left)
                    && ports.outputs.contains(right)) {
                result.add(left);
            }
            if (ports.inputs.containsKey(right)
                    && ports.outputs.contains(left)) {
                result.add(right);
            }
        }
        return result;
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
        report.add("reachCondition", reachCondition);
        report.add("gaps", GSON.toJsonTree(gaps));
        report.addProperty("state", "CANDIDATE_WITH_GAPS");
        return report;
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
        private final JsonObject artifact;

        Z3Solver(String executable, long timeoutMillis)
                throws IOException, InterruptedException {
            this.timeoutMillis = Math.max(1L, timeoutMillis);
            this.executable = resolveExecutable(firstNonBlank(executable,
                    "z3"));
            this.artifact = ArtifactIO.artifact(this.executable);
            this.artifact.addProperty("version", validateVersion(
                    this.executable, this.timeoutMillis));
        }

        JsonObject artifact() {
            return artifact.deepCopy();
        }

        @Override
        public SolverResult check(String smt) throws IOException,
                InterruptedException {
            Process process = new ProcessBuilder(executable.toString(),
                    "-in", "-smt2").redirectErrorStream(true).start();
            try (OutputStream input = process.getOutputStream()) {
                input.write(smt.getBytes(StandardCharsets.UTF_8));
            }
            if (!process.waitFor(timeoutMillis, TimeUnit.MILLISECONDS)) {
                process.destroyForcibly();
                process.waitFor();
                return new SolverResult("timeout", "solver timeout");
            }
            String output = readAll(process.getInputStream());
            return new SolverResult(process.exitValue() == 0
                    ? solverStatus(output) : "error", output);
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

        private static String validateVersion(Path executable,
                                              long timeoutMillis)
                throws IOException, InterruptedException {
            Process process = new ProcessBuilder(executable.toString(),
                    "-version").redirectErrorStream(true).start();
            if (!process.waitFor(timeoutMillis, TimeUnit.MILLISECONDS)) {
                process.destroyForcibly();
                process.waitFor();
                throw new IOException("Z3 -version timed out");
            }
            String output = readAll(process.getInputStream()).trim();
            if (process.exitValue() != 0 || !output.contains("Z3")) {
                throw new IOException("Invalid Z3 executable identity: "
                        + output);
            }
            return output;
        }

        private static String readAll(InputStream input) throws IOException {
            ByteArrayOutputStream output = new ByteArrayOutputStream();
            byte[] buffer = new byte[4096];
            int count;
            while ((count = input.read(buffer)) >= 0) {
                output.write(buffer, 0, count);
            }
            return new String(output.toByteArray(),
                    StandardCharsets.UTF_8);
        }
    }

    static String solverStatus(String output) {
        String normalized = firstNonBlank(output);
        int newline = normalized.indexOf('\n');
        String value = (newline < 0
                ? normalized : normalized.substring(0, newline)).trim();
        return "sat".equals(value) || "unsat".equals(value)
                || "unknown".equals(value) ? value : "unknown";
    }

    private static final class Discovery {
        private final List<RootInput> rootInputs;
        private final List<RootInput> booleanDomainInputs;
        private final List<RootInput> existentialNonBooleanRootInputs;

        private Discovery(List<RootInput> rootInputs,
                          List<RootInput> booleanDomainInputs,
                          List<RootInput> existentialNonBooleanRootInputs) {
            this.rootInputs = rootInputs;
            this.booleanDomainInputs = booleanDomainInputs;
            this.existentialNonBooleanRootInputs =
                    existentialNonBooleanRootInputs;
        }
    }

    private static final class RootInput {
        private final PortInfo port;
        private final String solverTerm;
        private final String nullnessSolverTerm;

        private RootInput(PortInfo port, String solverTerm,
                          String nullnessSolverTerm) {
            this.port = port;
            this.solverTerm = solverTerm;
            this.nullnessSolverTerm = firstNonBlank(nullnessSolverTerm);
        }

        private String literal(boolean value) {
            return "(= " + solverTerm + " " + (value ? "1" : "0") + ")";
        }

        private String domainFormula() {
            return "(or (= " + solverTerm + " 0) (= " + solverTerm
                    + " 1))";
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("portId", port.id);
            result.addProperty("regionId", port.regionId);
            result.addProperty("cell", port.cell);
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
        private final boolean[] values;
        private final String status;

        private Valuation(boolean[] values, String status) {
            this.values = values.clone();
            this.status = firstNonBlank(status, "unknown");
        }

        private JsonObject toJson(List<RootInput> inputs) {
            JsonObject result = new JsonObject();
            JsonArray assignments = new JsonArray();
            for (int index = 0; index < inputs.size(); index++) {
                JsonObject assignment = new JsonObject();
                assignment.addProperty("portId", inputs.get(index).port.id);
                assignment.addProperty("value", values[index]);
                assignments.add(assignment);
            }
            result.add("assignments", assignments);
            result.addProperty("status", status);
            return result;
        }
    }

    private static String dnf(List<RootInput> inputs,
                              List<Valuation> valuations) {
        List<String> terms = new ArrayList<>();
        for (Valuation valuation : valuations) {
            if (!"sat".equals(valuation.status)) continue;
            List<String> literals = new ArrayList<>();
            for (int index = 0; index < inputs.size(); index++) {
                literals.add(inputs.get(index).literal(
                        valuation.values[index]));
            }
            terms.add(join("and", literals, "true"));
        }
        if (terms.isEmpty()) return "false";
        return terms.size() == valuations.size()
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
        private final Set<String> outputs = new LinkedHashSet<>();

        private static PortCatalog from(List<JsonObject> regions) {
            PortCatalog result = new PortCatalog();
            for (JsonObject region : regions) {
                String regionId = string(region, "regionId");
                for (JsonElement element : array(region,
                        "symbolicInputs")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject row = element.getAsJsonObject();
                    String id = string(row, "portId");
                    if (!id.isEmpty()) {
                        result.inputs.put(id, new PortInfo(id, regionId,
                                string(row, "cell"),
                                string(row, "javaType")));
                    }
                }
                for (JsonElement element : array(region, "outputs")) {
                    if (element.isJsonObject()) {
                        String id = string(element.getAsJsonObject(),
                                "portId");
                        if (!id.isEmpty()) result.outputs.add(id);
                    }
                }
            }
            return result;
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
        private final String descriptor;
        private final boolean javaBoolean;

        private PortInfo(String id, String regionId, String cell,
                         String javaType) {
            this.id = firstNonBlank(id);
            this.regionId = firstNonBlank(regionId);
            this.cell = firstNonBlank(cell);
            this.descriptor = javaTypeDescriptor(javaType);
            this.javaBoolean = "Z".equals(descriptor)
                    || "Ljava/lang/Boolean;".equals(descriptor);
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

    /**
     * Rejects cross-wired CLI artifacts before any solver process starts.
     * The composer manifest is the trust root: it fingerprints the exact SMT,
     * static-region ledger, and relationship-candidate bytes.
     */
    static void validateArtifactBindings(Path smtPath, Path regionsPath,
                                         Path relationshipsPath,
                                         JsonObject manifest)
            throws IOException {
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
                "sha256"))) {
            throw new IOException(label + " artifact fingerprint mismatch");
        }
    }

    private static String normalizedPath(String value) {
        if (firstNonBlank(value).isEmpty()) return "";
        return Paths.get(value).toAbsolutePath().normalize().toString();
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

}
