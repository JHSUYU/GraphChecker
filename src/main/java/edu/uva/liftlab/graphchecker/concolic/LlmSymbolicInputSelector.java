package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.math.BigDecimal;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.TimeUnit;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Lets an external LLM choose a subset of scheduler-approved symbolic inputs.
 *
 * <p>The deterministic scheduler remains the authority for materialization:
 * the selector can only turn an existing {@code SYMBOLIC} action into
 * {@code CONCRETE}.  It cannot add an input, rewrite an action, or introduce
 * an edge or constraint.</p>
 */
final class LlmSymbolicInputSelector {
    private static final int SCHEMA_VERSION = 1;
    private static final String REQUEST_KIND =
            "GRAPH_CHECKER_SYMBOLIC_INPUT_SELECTION_REQUEST";
    private static final String RESPONSE_KIND =
            "GRAPH_CHECKER_SYMBOLIC_INPUT_SELECTION_RESPONSE";
    private static final int MAX_CONTEXT_BYTES = 64 * 1024;
    private static final int MAX_STDOUT_BYTES = 1024 * 1024;
    private static final int MAX_STDERR_BYTES = 64 * 1024;

    private static final String[] ACTION_FIELDS = {
            "symbol", "portId", "location", "bindingMode", "cell",
            "javaType", "sourceKind", "dependencyRole", "symbolicDemand",
            "method", "local", "index", "argumentIndex", "siteId",
            "unitIndex", "definitionMethod", "definitionUnitIndex",
            "accessorCallerMethod", "accessorCallUnitIndex",
            "accessorDeclaredCallee", "accessorImplementationMethod",
            "declaredFieldSignature", "accessFieldSignature",
            "leafFieldSignature", "fieldPath", "fieldPaths",
            "fieldPathDeclarations", "definitionSites", "accessSites",
            "materialization", "authority", "primitiveValue",
            "replayOccurrence"
    };

    private static final String[] BRANCH_FIELDS = {
            "siteId", "method", "unitIndex", "policy", "policyReason",
            "failureTarget", "requiredOutcome", "observedOutcome",
            "operandCells", "loopControlGuard"
    };

    private final Path command;
    private final Path contextFile;
    private final boolean required;
    private final long timeoutMillis;
    private final Map<String, Decision> cache = new LinkedHashMap<>();
    private final Map<String, JsonObject> audits = new LinkedHashMap<>();

    LlmSymbolicInputSelector(Path command, Path contextFile,
                             boolean required, long timeoutMillis) {
        this.command = command;
        this.contextFile = contextFile;
        this.required = required;
        this.timeoutMillis = Math.max(1L, timeoutMillis);
    }

    boolean enabled() {
        return command != null;
    }

    JsonArray select(JsonObject goalContext, JsonArray branches,
                     JsonArray inputActions) throws IOException {
        JsonArray baseline = inputActions.deepCopy();
        if (!enabled()) return baseline;

        CandidateCatalog catalog = CandidateCatalog.from(baseline);
        if (catalog.encoded.size() == 0) return baseline;

        JsonObject request = request(goalContext, branches, catalog);
        String decisionId = string(request, "decisionId");
        Decision decision = cache.get(decisionId);
        if (decision == null) {
            try {
                JsonObject response = invoke(request);
                decision = validate(request, catalog, response);
            } catch (Exception failure) {
                if (required) {
                    throw new IOException("LLM symbolic input selection "
                            + "failed for " + decisionId + ": "
                            + concise(failure), failure);
                }
                decision = Decision.fallback(catalog.ids(), failure);
            }
            cache.put(decisionId, decision);
            audits.put(decisionId, audit(request, catalog, decision));
        }
        return apply(baseline, catalog, decision.selectedIds);
    }

    List<JsonObject> auditRows() {
        List<JsonObject> result = new ArrayList<>();
        List<String> ids = new ArrayList<>(audits.keySet());
        Collections.sort(ids);
        for (String id : ids) result.add(audits.get(id).deepCopy());
        return result;
    }

    private JsonObject request(JsonObject goalContext, JsonArray branches,
                               CandidateCatalog catalog) throws IOException {
        JsonObject request = new JsonObject();
        request.addProperty("schemaVersion", SCHEMA_VERSION);
        request.addProperty("kind", REQUEST_KIND);
        request.add("goal", goalContext.deepCopy());
        request.add("demandedBranches", projectBranches(branches));
        request.add("candidates", catalog.encoded.deepCopy());
        String context = readContext();
        if (!context.isEmpty()) request.addProperty("analysisContext", context);
        String candidateHash = CanonicalJson.sha256(catalog.encoded);
        request.addProperty("candidateSetSha256", candidateHash);
        JsonObject identity = request.deepCopy();
        identity.remove("analysisContext");
        identity.addProperty("analysisContextSha256",
                ArtifactIO.sha256(context));
        request.addProperty("decisionId", "SYMBOL_SELECTION."
                + CanonicalJson.sha256(identity));
        return request;
    }

    private String readContext() throws IOException {
        if (contextFile == null) return "";
        if (!Files.isRegularFile(contextFile)) {
            throw new IOException("symbolic selector context not found: "
                    + contextFile);
        }
        long size = Files.size(contextFile);
        if (size > MAX_CONTEXT_BYTES) {
            throw new IOException("symbolic selector context exceeds "
                    + MAX_CONTEXT_BYTES + " bytes: " + contextFile);
        }
        return new String(Files.readAllBytes(contextFile),
                StandardCharsets.UTF_8);
    }

    private JsonObject invoke(JsonObject request) throws IOException {
        if (!Files.isRegularFile(command) || !Files.isExecutable(command)) {
            throw new IOException("symbolic selector command is not an "
                    + "executable file: " + command);
        }
        Process process = new ProcessBuilder(command.toString()).start();
        LimitedCollector stdout = new LimitedCollector(
                process.getInputStream(), MAX_STDOUT_BYTES);
        LimitedCollector stderr = new LimitedCollector(
                process.getErrorStream(), MAX_STDERR_BYTES);
        Thread stdoutThread = new Thread(stdout,
                "causynth-symbol-selector-stdout");
        Thread stderrThread = new Thread(stderr,
                "causynth-symbol-selector-stderr");
        stdoutThread.setDaemon(true);
        stderrThread.setDaemon(true);
        stdoutThread.start();
        stderrThread.start();
        try (OutputStream input = process.getOutputStream()) {
            input.write((CanonicalJson.render(request) + "\n")
                    .getBytes(StandardCharsets.UTF_8));
        }

        boolean finished;
        try {
            finished = process.waitFor(timeoutMillis,
                    TimeUnit.MILLISECONDS);
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            process.destroyForcibly();
            throw new IOException("symbolic selector interrupted",
                    interrupted);
        }
        if (!finished) {
            process.destroy();
            try {
                if (!process.waitFor(1000L, TimeUnit.MILLISECONDS)) {
                    process.destroyForcibly();
                }
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
                process.destroyForcibly();
            }
            throw new IOException("symbolic selector timed out after "
                    + timeoutMillis + " ms");
        }
        join(stdoutThread);
        join(stderrThread);
        if (stdout.overflow || stderr.overflow) {
            throw new IOException("symbolic selector output exceeded limit");
        }
        if (process.exitValue() != 0) {
            throw new IOException("symbolic selector exited "
                    + process.exitValue() + ": "
                    + conciseText(stderr.text()));
        }
        JsonElement parsed;
        try {
            parsed = JsonParser.parseString(stdout.text().trim());
        } catch (RuntimeException malformed) {
            throw new IOException("symbolic selector returned malformed JSON",
                    malformed);
        }
        if (!parsed.isJsonObject()) {
            throw new IOException("symbolic selector response is not an object");
        }
        return parsed.getAsJsonObject();
    }

    private static void join(Thread thread) throws IOException {
        try {
            thread.join(5000L);
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new IOException("interrupted while reading selector output",
                    interrupted);
        }
        if (thread.isAlive()) {
            throw new IOException("selector output stream did not close");
        }
    }

    private static Decision validate(JsonObject request,
                                     CandidateCatalog catalog,
                                     JsonObject response)
            throws IOException {
        Set<String> allowedFields = new LinkedHashSet<>();
        Collections.addAll(allowedFields, "schemaVersion", "kind",
                "decisionId", "candidateSetSha256",
                "selectedCandidateIds", "rationale");
        for (String field : response.keySet()) {
            if (!allowedFields.contains(field)) {
                throw new IOException("unknown selector response field: "
                        + field);
            }
        }
        JsonElement version = response.get("schemaVersion");
        if (version == null || !version.isJsonPrimitive()
                || !version.getAsJsonPrimitive().isNumber()
                || !exactSchemaVersion(version)
                || !RESPONSE_KIND.equals(string(response, "kind"))
                || !string(request, "decisionId").equals(
                string(response, "decisionId"))
                || !string(request, "candidateSetSha256").equals(
                string(response, "candidateSetSha256"))) {
            throw new IOException("selector response identity mismatch");
        }
        JsonElement rationale = response.get("rationale");
        if (rationale == null || !rationale.isJsonPrimitive()
                || !rationale.getAsJsonPrimitive().isString()) {
            throw new IOException("selector response requires rationale");
        }
        JsonElement selectedValue = response.get("selectedCandidateIds");
        if (selectedValue == null || !selectedValue.isJsonArray()) {
            throw new IOException("selector response requires "
                    + "selectedCandidateIds array");
        }
        Set<String> selected = new LinkedHashSet<>();
        for (JsonElement element : selectedValue.getAsJsonArray()) {
            if (!element.isJsonPrimitive()
                    || !element.getAsJsonPrimitive().isString()) {
                throw new IOException("selected candidate id is not a string");
            }
            String id = element.getAsString();
            if (!catalog.byId.containsKey(id)) {
                throw new IOException("selector chose unknown candidate: "
                        + id);
            }
            if (!selected.add(id)) {
                throw new IOException("selector repeated candidate: " + id);
            }
        }
        if (selected.isEmpty()) {
            throw new IOException("selector chose no symbolic input");
        }
        if (!selected.containsAll(catalog.requiredIds)) {
            Set<String> missing = new LinkedHashSet<>(catalog.requiredIds);
            missing.removeAll(selected);
            throw new IOException("selector omitted required candidates: "
                    + missing);
        }
        return Decision.selected(selected, response);
    }

    private static boolean exactSchemaVersion(JsonElement value) {
        try {
            return value.getAsBigDecimal().compareTo(BigDecimal.ONE) == 0;
        } catch (NumberFormatException invalid) {
            return false;
        }
    }

    private static JsonArray apply(JsonArray actions,
                                   CandidateCatalog catalog,
                                   Set<String> selectedIds) {
        JsonArray result = new JsonArray();
        for (JsonElement element : actions) {
            JsonObject action = element.getAsJsonObject().deepCopy();
            if (InputActionCatalog.Mode.SYMBOLIC.name().equals(
                    string(action, "mode"))) {
                String id = catalog.idBySymbol.get(string(action, "symbol"));
                if (id != null && !selectedIds.contains(id)) {
                    action.addProperty("mode",
                            InputActionCatalog.Mode.CONCRETE.name());
                }
            }
            result.add(action);
        }
        return result;
    }

    private static JsonObject audit(JsonObject request,
                                    CandidateCatalog catalog,
                                    Decision decision) {
        JsonObject audit = new JsonObject();
        audit.addProperty("schemaVersion", SCHEMA_VERSION);
        audit.addProperty("kind", "LLM_SYMBOLIC_INPUT_SELECTION");
        audit.addProperty("decisionId", string(request, "decisionId"));
        audit.addProperty("candidateSetSha256",
                string(request, "candidateSetSha256"));
        audit.addProperty("status", decision.fallback
                ? "ADVISORY_FALLBACK" : "SELECTED");
        audit.add("goal", request.get("goal").deepCopy());
        audit.add("request", request.deepCopy());
        JsonArray selected = new JsonArray();
        JsonArray deselected = new JsonArray();
        JsonArray selectedSymbols = new JsonArray();
        JsonArray deselectedSymbols = new JsonArray();
        for (String id : catalog.ids()) {
            boolean keep = decision.selectedIds.contains(id);
            (keep ? selected : deselected).add(id);
            (keep ? selectedSymbols : deselectedSymbols)
                    .add(catalog.byId.get(id).symbol);
        }
        audit.add("selectedCandidateIds", selected);
        audit.add("deselectedCandidateIds", deselected);
        audit.add("selectedSymbols", selectedSymbols);
        audit.add("deselectedSymbols", deselectedSymbols);
        if (decision.response != null) {
            audit.add("response", decision.response.deepCopy());
        }
        if (!decision.failure.isEmpty()) {
            audit.addProperty("fallbackReason", decision.failure);
        }
        return audit;
    }

    private static JsonArray projectBranches(JsonArray branches) {
        JsonArray result = new JsonArray();
        for (JsonElement element : branches) {
            if (!element.isJsonObject()) continue;
            JsonObject projected = project(element.getAsJsonObject(),
                    BRANCH_FIELDS);
            if (projected.size() > 0) result.add(projected);
        }
        return result;
    }

    private static JsonObject project(JsonObject source, String[] fields) {
        JsonObject result = new JsonObject();
        for (String field : fields) {
            JsonElement value = source.get(field);
            if (value != null && !value.isJsonNull()) {
                result.add(field, value.deepCopy());
            }
        }
        return result;
    }

    private static List<String> requiredReasons(List<JsonObject> actions) {
        Set<String> reasons = new LinkedHashSet<>();
        for (JsonObject action : actions) {
            String source = string(action, "sourceKind");
            String demand = string(action, "symbolicDemand");
            String location = string(action, "location");
            if ("EXPLICIT_SYMBOLIC_FAULT".equals(source)
                    || "EXPLICIT_SYMBOLIC_FAULT".equals(demand)) {
                reasons.add("EXPLICIT_SYMBOLIC_FAULT");
            }
            if ("EXACT_INCOMING_COMPOSITION".equals(demand)) {
                reasons.add("EXACT_INCOMING_COMPOSITION");
            }
            if ("PROTOCOL_ARGUMENT".equals(location)
                    || "PROTOCOL_RETURN".equals(location)) {
                reasons.add("TRUSTED_PROTOCOL_BINDING");
            }
            if ("BOUNDED_CONTAINER_STATE".equals(demand)
                    || "BOUNDED_STATE_FRONTIER".equals(demand)) {
                reasons.add(demand);
            }
            if ("EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1".equals(
                    string(action, "authority"))) {
                reasons.add("EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1");
            }
        }
        List<String> result = new ArrayList<>(reasons);
        Collections.sort(result);
        return result;
    }

    private static String concise(Throwable failure) {
        String message = failure == null ? "unknown failure"
                : failure.getClass().getSimpleName() + ": "
                + String.valueOf(failure.getMessage());
        return conciseText(message);
    }

    private static String conciseText(String value) {
        String message = String.valueOf(value);
        message = message.replace('\n', ' ').replace('\r', ' ').trim();
        return message.length() <= 512 ? message
                : message.substring(0, 512);
    }

    private static final class CandidateCatalog {
        private final JsonArray encoded;
        private final Map<String, Candidate> byId;
        private final Map<String, String> idBySymbol;
        private final Set<String> requiredIds;

        private CandidateCatalog(List<Candidate> candidates) {
            encoded = new JsonArray();
            byId = new LinkedHashMap<>();
            idBySymbol = new LinkedHashMap<>();
            requiredIds = new LinkedHashSet<>();
            for (Candidate candidate : candidates) {
                encoded.add(candidate.encoded.deepCopy());
                byId.put(candidate.id, candidate);
                idBySymbol.put(candidate.symbol, candidate.id);
                if (candidate.required) requiredIds.add(candidate.id);
            }
        }

        static CandidateCatalog from(JsonArray actions) {
            Map<String, List<JsonObject>> grouped = new TreeMap<>();
            for (JsonElement element : actions) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                if (!InputActionCatalog.Mode.SYMBOLIC.name().equals(
                        string(action, "mode"))) continue;
                String symbol = string(action, "symbol");
                if (symbol.isEmpty()) continue;
                grouped.computeIfAbsent(symbol,
                        ignored -> new ArrayList<>()).add(action);
            }
            List<Candidate> candidates = new ArrayList<>();
            for (Map.Entry<String, List<JsonObject>> entry
                    : grouped.entrySet()) {
                candidates.add(new Candidate(entry.getKey(),
                        entry.getValue()));
            }
            candidates.sort(Comparator.comparing(value -> value.id));
            return new CandidateCatalog(candidates);
        }

        Set<String> ids() {
            return new LinkedHashSet<>(byId.keySet());
        }
    }

    private static final class Candidate {
        private final String id;
        private final String symbol;
        private final boolean required;
        private final JsonObject encoded;

        private Candidate(String symbol, List<JsonObject> actions) {
            this.symbol = symbol;
            List<JsonObject> projected = new ArrayList<>();
            for (JsonObject action : actions) {
                projected.add(project(action, ACTION_FIELDS));
            }
            projected.sort(Comparator.comparing(CanonicalJson::render));
            JsonArray materializations = new JsonArray();
            for (JsonObject action : projected) {
                materializations.add(action);
            }
            List<String> reasons = requiredReasons(actions);
            required = !reasons.isEmpty();
            JsonObject identity = new JsonObject();
            identity.addProperty("symbol", symbol);
            identity.add("materializations", materializations.deepCopy());
            id = "SYMBOL_CANDIDATE." + CanonicalJson.sha256(identity);
            encoded = identity;
            encoded.addProperty("candidateId", id);
            encoded.addProperty("required", required);
            JsonArray requiredReasons = new JsonArray();
            for (String reason : reasons) requiredReasons.add(reason);
            encoded.add("requiredReasons", requiredReasons);
        }
    }

    private static final class Decision {
        private final Set<String> selectedIds;
        private final JsonObject response;
        private final boolean fallback;
        private final String failure;

        private Decision(Set<String> selectedIds, JsonObject response,
                         boolean fallback, String failure) {
            this.selectedIds = Collections.unmodifiableSet(
                    new LinkedHashSet<>(selectedIds));
            this.response = response == null ? null : response.deepCopy();
            this.fallback = fallback;
            this.failure = failure;
        }

        static Decision selected(Set<String> ids, JsonObject response) {
            return new Decision(ids, response, false, "");
        }

        static Decision fallback(Set<String> ids, Throwable failure) {
            return new Decision(ids, null, true, concise(failure));
        }
    }

    private static final class LimitedCollector implements Runnable {
        private final InputStream input;
        private final int limit;
        private final ByteArrayOutputStream bytes =
                new ByteArrayOutputStream();
        private volatile boolean overflow;

        private LimitedCollector(InputStream input, int limit) {
            this.input = input;
            this.limit = limit;
        }

        @Override
        public void run() {
            byte[] buffer = new byte[4096];
            try (InputStream stream = input) {
                int read;
                while ((read = stream.read(buffer)) >= 0) {
                    if (read == 0) continue;
                    int remaining = limit - bytes.size();
                    if (remaining > 0) {
                        bytes.write(buffer, 0, Math.min(read, remaining));
                    }
                    if (read > remaining) overflow = true;
                }
            } catch (IOException failure) {
                overflow = true;
            }
        }

        private String text() {
            return new String(bytes.toByteArray(), StandardCharsets.UTF_8);
        }
    }
}
