package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sha256;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Converts one VM execution row into one semantic path row.
 *
 * <p>The VM expression graph is the authority for scalars, fields and
 * containers.  Import therefore performs one decode and one admission pass;
 * it does not reconstruct Map entries, array elements or dynamic field
 * selectors from concrete runtime snapshots.</p>
 */
public final class ConcolicSummaryImporter {
    private ConcolicSummaryImporter() {
    }

    public static void main(String[] args) throws Exception {
        Map<String, String> options = parseArgs(args);
        Path results = required(options, "results");
        Path tasks = required(options, "task-plan");
        Path regions = required(options, "regions");
        Path output = Paths.get(firstNonBlank(options.get("output"),
                sibling(results,
                        "concolic_region_summaries.jsonl").toString()));
        Path diagnostics = Paths.get(firstNonBlank(
                options.get("diagnostics"),
                sibling(results,
                        "concolic_import_diagnostics.jsonl").toString()));
        ImportResult imported = importSummaries(results, tasks, regions,
                output, diagnostics);
        if (imported.diagnosticCount > 0) {
            try (BufferedReader reader = Files.newBufferedReader(diagnostics,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    System.err.println("[concolic-import] " + line);
                }
            }
        }
        if (imported.validSummaryCount == 0
                && imported.rawResultCount > 0) {
            System.exit(2);
        }
    }

    public static ImportResult importSummaries(
            Path resultsFile, Path taskPlanFile, Path regionFile,
            Path outputFile, Path diagnosticFile) throws IOException {
        Map<String, ExecutionTask> tasks = taskIndex(
                ArtifactIO.readJsonl(taskPlanFile));
        Set<String> regions = regionIds(ArtifactIO.readJsonl(regionFile));
        List<JsonObject> rawResults = ArtifactIO.readJsonl(resultsFile);
        List<JsonObject> summaries = new ArrayList<>();
        List<JsonObject> diagnostics = new ArrayList<>();
        Set<String> hashes = new LinkedHashSet<>();

        for (int index = 0; index < rawResults.size(); index++) {
            JsonObject raw = rawResults.get(index);
            String taskId = string(raw, "taskId");
            if (!"CONCOLIC_REGION_RESULT".equals(string(raw, "event"))) {
                diagnostics.add(diagnostic(raw, index,
                        "SKIPPED_RUNTIME_EVENT",
                        string(raw, "event")));
                continue;
            }
            ExecutionTask task = tasks.get(taskId);
            if (task == null) {
                diagnostics.add(diagnostic(raw, index,
                        "UNKNOWN_EXECUTION_TASK", taskId));
                continue;
            }
            if (!regions.contains(task.regionId())) {
                diagnostics.add(diagnostic(raw, index,
                        "UNKNOWN_REGION", task.regionId()));
                continue;
            }

            List<String> issues = new ArrayList<>();
            JsonObject engine = object(raw, "engineSummary");
            if (!bool(engine, "complete", false)
                    || bool(engine, "aborted", false)) {
                issues.add("VM_SUMMARY_INCOMPLETE:"
                        + string(engine, "abortReason"));
            }
            for (JsonElement unresolved : array(raw,
                    "unresolvedInputs")) {
                issues.add("UNRESOLVED_INPUT:" + unresolved);
            }

            SemanticPath path = SemanticPath.from(
                    array(engine, "pathCondition"),
                    array(raw, "branchMappings"));
            JsonArray mappings = branchMappings(raw, task, path, issues);
            JsonObject outputs = outputExpressions(raw, task, issues);
            JsonArray symbolicInputs = symbolicInputs(raw);
            // The flip contract is a worklist hint, not output semantics.
            // A replay may diverge before the requested branch; its actual PC
            // and normal-exit output relation remain a valid newly found path.
            JsonElement replayContract = task.replayContract();

            JsonObject summary = new JsonObject();
            summary.addProperty("goalId", task.goalId());
            summary.addProperty("taskId", task.taskId());
            summary.addProperty("regionId", task.regionId());
            summary.addProperty("regionInstanceId",
                    task.regionInstanceId());
            task.goalKind().writeToTask(summary);
            if (task.outputClosure() != null) {
                summary.add(OutputClosureContract.FIELD,
                        task.outputClosure().toJson());
            }
            summary.add("symbolicInputs", symbolicInputs);
            summary.add("edgeBindings", task.edgeBindings());
            summary.add("pathCondition", path.expressions);
            summary.add("branchMappings", mappings);
            summary.add("outputExpressions", outputs);
            summary.addProperty("normalExit",
                    "NORMAL".equals(string(raw, "exitKind")));
            summary.addProperty("exceptionType",
                    string(raw, "exceptionType"));
            summary.addProperty("relationallyComplete", issues.isEmpty());

            if (replayContract != null && !issues.isEmpty()) {
                diagnostics.add(diagnostic(raw, index,
                        "PATH_REPLAY_ADMISSION_REJECTED",
                        String.join(";", issues)));
                continue;
            }

            JsonObject semantic = summary.deepCopy();
            semantic.remove("taskId");
            String hash = sha256(CanonicalJson.render(semantic));
            if (!hashes.add(hash)) {
                diagnostics.add(diagnostic(raw, index,
                        "DUPLICATE_SUMMARY", hash));
                continue;
            }
            summary.addProperty("summaryId",
                    "SUMMARY." + task.regionId() + "." + hash);
            summaries.add(summary);
            if (!issues.isEmpty()) {
                diagnostics.add(diagnostic(raw, index,
                        "INCOMPLETE_RELATION",
                        String.join(";", issues)));
            }
        }

        ArtifactIO.replaceJsonl(outputFile, summaries);
        ArtifactIO.replaceJsonl(diagnosticFile, diagnostics);
        return new ImportResult(rawResults.size(), summaries.size(),
                diagnostics.size());
    }

    private static JsonArray branchMappings(
            JsonObject raw, ExecutionTask task, SemanticPath path,
            List<String> issues) {
        Map<String, SummaryBranchMapping.Policy> policies =
                branchPolicies(task);
        JsonArray result = new JsonArray();
        Set<String> events = new LinkedHashSet<>();
        Set<Integer> decisionPositions = new LinkedHashSet<>();
        for (JsonElement element : array(raw, "branchMappings")) {
            if (!element.isJsonObject()) {
                issues.add("MALFORMED_BRANCH_MAPPING");
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            String site = string(row, "siteId");
            int occurrence = integer(row, "occurrence", -1);
            if (site.isEmpty() || occurrence < 1
                    || !events.add(site + "\u0000" + occurrence)) {
                issues.add("AMBIGUOUS_BRANCH_EVENT:" + site);
                continue;
            }
            SummaryBranchMapping.Policy policy = policies.get(site);
            if (policy == null) {
                policy = SummaryBranchMapping.Policy.PATH_ASSUMPTION;
            }
            try {
                BranchWitness direct = null;
                ExactConcreteBranchObservation concrete = null;
                if (row.has("witness")
                        && row.get("witness").isJsonObject()) {
                    direct = BranchWitness.fromJson(
                            row.getAsJsonObject("witness"));
                    int pcIndex = direct.vmPcIndex();
                    if (pcIndex < 0 || pcIndex >= path.original.size()
                            || !BranchPredicateAlgebra.equivalent(
                            direct.sourceSatisfiedPredicate(),
                            path.original.get(pcIndex))) {
                        issues.add("BRANCH_PC_MISMATCH:" + site);
                        continue;
                    }
                } else if (row.has("concreteObservation")
                        && row.get("concreteObservation").isJsonObject()) {
                    concrete = ExactConcreteBranchObservation.fromJson(
                            row.getAsJsonObject("concreteObservation"));
                } else {
                    issues.add("BRANCH_WITHOUT_AUTHORITY:" + site);
                    continue;
                }

                int baseline = integer(row,
                        "rawPathConditionBaseline", -1);
                int limit = integer(row, "rawPathConditionSize", -1);
                if (baseline < 0 || limit < baseline
                        || limit > path.original.size()
                        || direct != null
                        && (direct.vmPcIndex() < baseline
                        || direct.vmPcIndex() >= limit)) {
                    issues.add("INVALID_BRANCH_PC_WINDOW:" + site);
                    continue;
                }

                int derivedOrdinal = 0;
                boolean emittedDecision = false;
                for (int pcIndex = baseline; pcIndex < limit; pcIndex++) {
                    int summaryPcIndex = path.summaryIndex(pcIndex);
                    if (summaryPcIndex < 0) {
                        continue;
                    }
                    SummaryBranchMapping decision = null;
                    if (direct != null
                            && direct.vmPcIndex() == pcIndex) {
                        decision = SummaryBranchMapping.witnessed(
                                direct.atPcIndex(summaryPcIndex),
                                summaryPcIndex, policy);
                    } else if (pcPredicate(path.original.get(pcIndex))) {
                        derivedOrdinal++;
                        decision = SummaryBranchMapping.witnessed(
                                BranchWitness.pcPredicate(site,
                                        string(row, "method"),
                                        integer(row, "unitIndex", -1),
                                        occurrence, derivedOrdinal,
                                        path.original.get(pcIndex),
                                        summaryPcIndex),
                                summaryPcIndex, policy);
                    }
                    if (decision == null) continue;
                    if (!decisionPositions.add(summaryPcIndex)) {
                        issues.add("AMBIGUOUS_BRANCH_PC:"
                                + summaryPcIndex);
                        continue;
                    }
                    result.add(decision.toJson());
                    emittedDecision = true;
                }
                if (!emittedDecision && concrete != null) {
                    result.add(SummaryBranchMapping.concrete(concrete,
                            policy).toJson());
                }
            } catch (IllegalArgumentException malformed) {
                issues.add("MALFORMED_BRANCH_MAPPING:" + site + ":"
                        + malformed.getMessage());
            }
        }
        return result;
    }

    /**
     * The raw branch window may contain several primitive predicates used to
     * compute one synthetic Jimple boolean. Explicit VM relations remain
     * prefix context; every other complementable binary predicate is a path
     * decision.
     */
    private static boolean pcPredicate(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        if (!"BinaryExpression".equals(string(object, "_type"))
                || ContainerSmtCodec.handlesFieldBinding(expression)
                || ContainerSmtCodec.handlesAccessConstraint(expression)) {
            return false;
        }
        try {
            BranchPredicateAlgebra.complementOperator(
                    string(object, "_op"));
            return true;
        } catch (IllegalArgumentException unsupported) {
            return false;
        }
    }

    private static Map<String, SummaryBranchMapping.Policy> branchPolicies(
            ExecutionTask task) {
        Map<String, SummaryBranchMapping.Policy> result =
                new LinkedHashMap<>();
        for (JsonElement element : task.branches()) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            String site = string(branch, "siteId");
            try {
                result.put(site, SummaryBranchMapping.Policy.fromWire(
                        string(branch, "policy")));
            } catch (IllegalArgumentException unsupported) {
                result.put(site, SummaryBranchMapping.Policy.EXPLORE);
            }
        }
        return result;
    }

    private static JsonObject outputExpressions(
            JsonObject raw, ExecutionTask task, List<String> issues) {
        JsonObject result = new JsonObject();
        OutputClosureContract closure = task.outputClosure();
        if (closure == null) return result;

        Map<String, List<JsonElement>> captures = new LinkedHashMap<>();
        for (JsonElement element : array(raw, "outputCaptures")) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            JsonElement expression = row.get("expression");
            if (expression != null && !expression.isJsonNull()) {
                captures.computeIfAbsent(string(row, "captureBindingId"),
                        ignored -> new ArrayList<>())
                        .add(expression.deepCopy());
            }
        }

        Map<String, List<OutputCaptureSpec>> specsByPort =
                new LinkedHashMap<>();
        for (OutputCaptureSpec spec : task.outputCaptures()) {
            specsByPort.computeIfAbsent(spec.outputPort(),
                    ignored -> new ArrayList<>()).add(spec);
        }
        for (String port : closure.outputPorts()) {
            List<OutputCaptureSpec> specs = specsByPort.get(port);
            List<JsonElement> expressions = new ArrayList<>();
            if (specs != null) {
                for (OutputCaptureSpec spec : specs) {
                    List<JsonElement> values = captures.get(
                            spec.captureBindingId());
                    if (values != null) expressions.addAll(values);
                }
            }
            if (expressions.size() == 1) {
                result.add(port, expressions.get(0));
                continue;
            }
            JsonElement root = rootOutputExpression(raw);
            if ((specs == null || specs.isEmpty())
                    && closure.outputPorts().size() == 1
                    && root != null) {
                result.add(port, root);
                continue;
            }
            issues.add("OUTPUT_CAPTURE_COUNT:" + port + ":"
                    + expressions.size());
        }
        return result;
    }

    private static JsonElement rootOutputExpression(JsonObject raw) {
        JsonElement encoded = raw.get("rootOutputExpression");
        if (encoded == null || !encoded.isJsonObject()) return null;
        JsonObject wrapper = encoded.getAsJsonObject();
        JsonElement expression = wrapper.get("expression");
        return expression != null && !expression.isJsonNull()
                ? expression.deepCopy() : null;
    }

    private static JsonArray symbolicInputs(JsonObject raw) {
        JsonArray result = new JsonArray();
        Set<String> unique = new LinkedHashSet<>();
        for (JsonElement element : array(raw, "symbolizedInputs")) {
            if (element.isJsonPrimitive()) {
                String symbol = element.getAsString();
                if (!symbol.isEmpty() && unique.add(symbol)) {
                    result.add(symbol);
                }
            }
        }
        return result;
    }

    private static Map<String, ExecutionTask> taskIndex(
            List<JsonObject> rows) throws IOException {
        Map<String, ExecutionTask> result = new LinkedHashMap<>();
        for (JsonObject row : rows) {
            final ExecutionTask task;
            try {
                task = ExecutionTask.decode(row);
            } catch (IllegalArgumentException malformed) {
                throw new IOException("Malformed execution task: "
                        + malformed.getMessage(), malformed);
            }
            if (result.put(task.taskId(), task) != null) {
                throw new IOException("Duplicate taskId " + task.taskId());
            }
        }
        return result;
    }

    private static Set<String> regionIds(List<JsonObject> rows)
            throws IOException {
        Set<String> result = new LinkedHashSet<>();
        for (JsonObject row : rows) {
            String id = string(row, "regionId");
            if (id.isEmpty() || !result.add(id)) {
                throw new IOException("Missing or duplicate regionId " + id);
            }
        }
        return result;
    }

    private static JsonObject diagnostic(
            JsonObject raw, int index, String code, String detail) {
        JsonObject result = new JsonObject();
        result.addProperty("kind", "CONCOLIC_IMPORT_DIAGNOSTIC");
        result.addProperty("code", code);
        result.addProperty("detail", firstNonBlank(detail, "UNKNOWN"));
        result.addProperty("taskId", string(raw, "taskId"));
        result.addProperty("line", index + 1);
        return result;
    }

    /** Removes replay-only container observations and remaps PC ownership. */
    private static final class SemanticPath {
        private final JsonArray original;
        private final JsonArray expressions;
        private final int[] summaryIndices;

        private SemanticPath(JsonArray original, JsonArray expressions,
                             int[] summaryIndices) {
            this.original = original;
            this.expressions = expressions;
            this.summaryIndices = summaryIndices;
        }

        private static SemanticPath from(JsonArray raw,
                                         JsonArray branchMappings) {
            JsonArray original = raw == null
                    ? new JsonArray() : raw.deepCopy();
            JsonArray expressions = new JsonArray();
            int[] indices = new int[original.size()];
            Set<Integer> branchDecisions =
                    witnessedVmPcIndices(branchMappings);
            Set<Integer> branchEvaluation =
                    branchEvaluationIndices(branchMappings, original.size());
            for (int index = 0; index < original.size(); index++) {
                JsonElement expression = original.get(index);
                boolean witnessed = branchDecisions.contains(index);
                if (!witnessed
                        && (InitialContainerObservation.isConcreteEquality(
                        expression)
                        || !branchEvaluation.contains(index)
                        && pcPredicate(expression))) {
                    indices[index] = -1;
                } else {
                    indices[index] = expressions.size();
                    expressions.add(expression.deepCopy());
                }
            }
            return new SemanticPath(original, expressions, indices);
        }

        private static Set<Integer> witnessedVmPcIndices(
                JsonArray branchMappings) {
            Set<Integer> result = new LinkedHashSet<>();
            for (JsonElement element : branchMappings) {
                if (!element.isJsonObject()) continue;
                JsonObject witness = object(
                        element.getAsJsonObject(), "witness");
                int index = integer(witness, "vmPcIndex", -1);
                if (index >= 0) result.add(index);
            }
            return result;
        }

        private static Set<Integer> branchEvaluationIndices(
                JsonArray branchMappings, int pathSize) {
            Set<Integer> result = new LinkedHashSet<>();
            for (JsonElement element : branchMappings) {
                if (!element.isJsonObject()) continue;
                JsonObject mapping = element.getAsJsonObject();
                int start = integer(mapping,
                        "rawPathConditionBaseline", -1);
                int limit = integer(mapping,
                        "rawPathConditionSize", -1);
                if (start < 0 || limit < start || limit > pathSize) {
                    continue;
                }
                for (int index = start; index < limit; index++) {
                    result.add(index);
                }
            }
            return result;
        }

        private int summaryIndex(int vmIndex) {
            return vmIndex < 0 || vmIndex >= summaryIndices.length
                    ? -1 : summaryIndices[vmIndex];
        }
    }

    private static Map<String, String> parseArgs(String[] args) {
        Map<String, String> result = new LinkedHashMap<>();
        for (int index = 0; index < args.length; index++) {
            String argument = args[index];
            if (!argument.startsWith("--")) {
                throw new IllegalArgumentException(
                        "expected --name value, got " + argument);
            }
            String name = argument.substring(2);
            int equals = name.indexOf('=');
            if (equals >= 0) {
                result.put(name.substring(0, equals),
                        name.substring(equals + 1));
            } else if (index + 1 < args.length) {
                result.put(name, args[++index]);
            } else {
                throw new IllegalArgumentException(
                        "missing value for " + argument);
            }
        }
        return result;
    }

    private static Path required(
            Map<String, String> options, String name) {
        String value = options.get(name);
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException(
                    "missing required --" + name);
        }
        return Paths.get(value);
    }

    private static Path sibling(Path input, String name) {
        Path parent = input.toAbsolutePath().normalize().getParent();
        return parent == null ? Paths.get(name) : parent.resolve(name);
    }

    public static final class ImportResult {
        public final int rawResultCount;
        public final int validSummaryCount;
        public final int diagnosticCount;

        private ImportResult(int rawResultCount, int validSummaryCount,
                             int diagnosticCount) {
            this.rawResultCount = rawResultCount;
            this.validSummaryCount = validSummaryCount;
            this.diagnosticCount = diagnosticCount;
        }
    }
}
