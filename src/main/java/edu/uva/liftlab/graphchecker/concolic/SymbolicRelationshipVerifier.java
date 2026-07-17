package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

/**
 * Proves generated symbolic relationships by checking the base constraints
 * and then checking {@code base AND NOT(relationship)}.
 *
 * <p>A relationship is labelled DERIVED only when the base formula is
 * satisfiable and the negated relationship is unsatisfiable.  This avoids both
 * concrete-model interpretation and vacuous proofs from an inconsistent base
 * formula.</p>
 */
public final class SymbolicRelationshipVerifier {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private SymbolicRelationshipVerifier() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        JsonObject candidates = readJson(arguments.candidates);
        String smt = new String(Files.readAllBytes(arguments.smt),
                StandardCharsets.UTF_8);
        Verification result = verify(smt, candidates,
                new Z3Solver(arguments.z3, arguments.timeoutMillis));
        write(arguments.output, GSON.toJson(result.report)
                + System.lineSeparator());
        System.out.println(GSON.toJson(result.report));
        if (!bool(result.report, "complete", false)) {
            System.exit(2);
        }
    }

    static Verification verify(String baseSmt, JsonObject candidates,
                               Solver solver) throws IOException,
            InterruptedException {
        if (!bool(candidates, "eligibleForAutomaticVerification", false)) {
            return ineligible(candidates);
        }
        String base = stripSolverCommands(baseSmt);
        SolverResult baseResult = solver.check(base + System.lineSeparator()
                + "(check-sat)" + System.lineSeparator());

        JsonObject report = new JsonObject();
        report.addProperty("schemaVersion", 1);
        report.addProperty("kind", "SYMBOLIC_RELATIONSHIP_PROOF_REPORT");
        report.addProperty("proofMethod",
                "BASE_AND_NEGATED_RELATION_UNSAT");
        report.addProperty("automaticVerificationEligible", true);
        report.addProperty("automaticVerificationAttempted", true);
        report.addProperty("baseStatus", baseResult.status);
        report.addProperty("baseSatisfiable",
                "sat".equals(baseResult.status));

        JsonArray verified = new JsonArray();
        int proved = 0;
        int notEntailed = 0;
        int errors = 0;
        int required = 0;
        int requiredProved = 0;
        for (JsonElement element : array(candidates, "relationships")) {
            if (!element.isJsonObject()) continue;
            JsonObject candidate = element.getAsJsonObject();
            JsonObject row = candidate.deepCopy();
            boolean isRequired = bool(candidate, "required", false);
            if (isRequired) required++;
            String formula = string(candidate, "formula");
            if (!"sat".equals(baseResult.status)) {
                row.addProperty("status", "NOT_CHECKED_BASE_NOT_SAT");
                row.addProperty("classification", "UNVERIFIED");
                errors++;
            } else if (formula.isEmpty()) {
                row.addProperty("status", "MALFORMED_EMPTY_FORMULA");
                row.addProperty("classification", "UNVERIFIED");
                errors++;
            } else {
                String query = base + System.lineSeparator()
                        + "(assert (not " + formula + "))"
                        + System.lineSeparator() + "(check-sat)"
                        + System.lineSeparator();
                SolverResult check = solver.check(query);
                row.addProperty("negatedRelationshipStatus", check.status);
                if ("unsat".equals(check.status)) {
                    row.addProperty("status",
                            "PROVED_BY_UNSAT_NEGATION");
                    row.addProperty("classification", "DERIVED");
                    row.addProperty("proofObligation",
                            "ComposedConstraints AND NOT(Relationship)");
                    row.addProperty("concreteModelUsed", false);
                    proved++;
                    if (isRequired) requiredProved++;
                } else if ("sat".equals(check.status)) {
                    row.addProperty("status", "NOT_ENTAILED");
                    row.addProperty("classification",
                            "CANDIDATE_NOT_DERIVED");
                    row.addProperty("counterexampleExists", true);
                    notEntailed++;
                } else {
                    row.addProperty("status", "SOLVER_"
                            + check.status.toUpperCase());
                    row.addProperty("classification", "UNVERIFIED");
                    row.addProperty("solverOutput", check.output);
                    errors++;
                }
            }
            verified.add(row);
        }
        report.addProperty("relationshipCount", verified.size());
        report.addProperty("provedRelationshipCount", proved);
        report.addProperty("notEntailedRelationshipCount", notEntailed);
        report.addProperty("verificationErrorCount", errors);
        report.addProperty("requiredRelationshipCount", required);
        report.addProperty("requiredRelationshipProvedCount",
                requiredProved);
        boolean complete = "sat".equals(baseResult.status)
                && errors == 0 && required == requiredProved;
        report.addProperty("complete", complete);
        report.addProperty("status", complete
                ? "COMPLETE_RELATIONSHIP_PROOF"
                : "RELATIONSHIP_PROOF_WITH_GAPS");
        report.add("relationships", verified);
        return new Verification(report);
    }

    private static Verification ineligible(JsonObject candidates) {
        JsonObject report = new JsonObject();
        report.addProperty("schemaVersion", 1);
        report.addProperty("kind", "SYMBOLIC_RELATIONSHIP_PROOF_REPORT");
        report.addProperty("proofMethod",
                "BASE_AND_NEGATED_RELATION_UNSAT");
        report.addProperty("automaticVerificationEligible", false);
        report.addProperty("automaticVerificationAttempted", false);
        report.addProperty("baseStatus", "not_checked");
        report.addProperty("baseSatisfiable", false);

        JsonArray rows = new JsonArray();
        int required = 0;
        for (JsonElement element : array(candidates, "relationships")) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject().deepCopy();
            if (bool(row, "required", false)) required++;
            row.addProperty("status",
                    "NOT_ELIGIBLE_INCOMPLETE_COMPOSITION");
            row.addProperty("classification", "UNVERIFIED");
            row.addProperty("reason",
                    "CANDIDATE_SET_NOT_ELIGIBLE_FOR_AUTOMATIC_VERIFICATION");
            rows.add(row);
        }
        report.addProperty("relationshipCount", rows.size());
        report.addProperty("provedRelationshipCount", 0);
        report.addProperty("notEntailedRelationshipCount", 0);
        report.addProperty("verificationErrorCount", rows.size());
        report.addProperty("requiredRelationshipCount", required);
        report.addProperty("requiredRelationshipProvedCount", 0);
        report.addProperty("complete", false);
        report.addProperty("status",
                "RELATIONSHIP_PROOF_BLOCKED_BY_COMPOSITION_GAPS");
        report.add("relationships", rows);
        return new Verification(report);
    }

    static String stripSolverCommands(String input) {
        StringBuilder result = new StringBuilder();
        String[] lines = (input == null ? "" : input)
                .split("\\r?\\n", -1);
        for (String line : lines) {
            String trimmed = line.trim();
            if (trimmed.startsWith("(check-sat")
                    || trimmed.startsWith("(get-model")
                    || trimmed.startsWith("(get-value")
                    || trimmed.startsWith("(get-unsat-core")
                    || trimmed.startsWith("(exit")) {
                continue;
            }
            result.append(line).append(System.lineSeparator());
        }
        return result.toString();
    }

    interface Solver {
        SolverResult check(String smt) throws IOException,
                InterruptedException;
    }

    static final class SolverResult {
        private final String status;
        private final String output;

        SolverResult(String status, String output) {
            this.status = status;
            this.output = output;
        }
    }

    private static final class Z3Solver implements Solver {
        private final String executable;
        private final long timeoutMillis;

        private Z3Solver(String executable, long timeoutMillis) {
            this.executable = executable;
            this.timeoutMillis = timeoutMillis;
        }

        @Override
        public SolverResult check(String smt) throws IOException,
                InterruptedException {
            Path directory = Files.createTempDirectory(
                    "graphchecker-relationship-z3-");
            Path query = directory.resolve("query.smt2");
            Path output = directory.resolve("output.txt");
            try {
                Files.write(query, smt.getBytes(StandardCharsets.UTF_8));
                Process process = new ProcessBuilder(executable, "-smt2",
                        query.toString())
                        .redirectErrorStream(true)
                        .redirectOutput(output.toFile())
                        .start();
                boolean finished = process.waitFor(timeoutMillis,
                        TimeUnit.MILLISECONDS);
                if (!finished) {
                    process.destroyForcibly();
                    process.waitFor();
                    return new SolverResult("timeout", "solver timeout");
                }
                String text = Files.isRegularFile(output)
                        ? new String(Files.readAllBytes(output),
                        StandardCharsets.UTF_8) : "";
                String status = solverStatus(text);
                if (process.exitValue() != 0 && "unknown".equals(status)) {
                    status = "error";
                }
                return new SolverResult(status, text.trim());
            } finally {
                Files.deleteIfExists(query);
                Files.deleteIfExists(output);
                Files.deleteIfExists(directory);
            }
        }
    }

    static String solverStatus(String output) {
        String[] lines = (output == null ? "" : output).split("\\r?\\n");
        for (String line : lines) {
            String value = line.trim();
            if ("sat".equals(value) || "unsat".equals(value)
                    || "unknown".equals(value)) {
                return value;
            }
        }
        return "unknown";
    }

    static final class Verification {
        final JsonObject report;

        Verification(JsonObject report) {
            this.report = report;
        }
    }

    private static final class Arguments {
        private Path smt;
        private Path candidates;
        private Path output;
        private String z3 = "z3";
        private long timeoutMillis = 20_000L;

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
            result.candidates = required(values, "candidates");
            result.output = values.containsKey("output")
                    ? Paths.get(values.get("output"))
                    : sibling(result.candidates,
                    "symbolic_relationship_proofs.json");
            result.z3 = firstNonBlank(values.get("z3"), "z3");
            try {
                result.timeoutMillis = Long.parseLong(firstNonBlank(
                        values.get("timeout-ms"), "20000"));
            } catch (RuntimeException ignored) {
                result.timeoutMillis = 20_000L;
            }
            result.timeoutMillis = Math.max(1L, result.timeoutMillis);
            return result;
        }

        private static Path required(Map<String, String> values, String key) {
            String value = values.get(key);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return Paths.get(value);
        }
    }

    private static JsonObject readJson(Path path) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException("JSON input not found: " + path);
        }
        JsonElement value = JsonParser.parseString(new String(
                Files.readAllBytes(path), StandardCharsets.UTF_8));
        if (!value.isJsonObject()) {
            throw new IOException("Expected JSON object: " + path);
        }
        return value.getAsJsonObject();
    }

    private static void write(Path path, String value) throws IOException {
        Path parent = path.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                path.getFileName().toString(), ".tmp");
        Files.write(temporary, value.getBytes(StandardCharsets.UTF_8));
        try {
            Files.move(temporary, path, StandardCopyOption.ATOMIC_MOVE,
                    StandardCopyOption.REPLACE_EXISTING);
        } catch (IOException ignored) {
            Files.move(temporary, path, StandardCopyOption.REPLACE_EXISTING);
        }
    }

    private static Path sibling(Path path, String name) {
        Path parent = path.toAbsolutePath().getParent();
        return (parent == null ? Paths.get(".") : parent).resolve(name);
    }

    private static JsonArray array(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
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
}
