package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.concolic.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.concolic.SummaryBranchMapping;

import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Immutable, once-decoded view of one imported concolic path summary.
 *
 * <p>The original summary is retained only as the attested replay payload.
 * Worklist and relation consumers use the typed and canonical fields below.</p>
 */
public final class PathObservation {
    private static final String[] RELATION_EVIDENCE_FIELDS = {
            "heapStateInitializers", "heapObservations",
            "finiteMapSnapshots", "dynamicFieldBindings",
            "engineArrayInputBindings", "vmIntrinsicPlaceholderBindings",
            "unforcedEnvironmentValidationRequirements", "heapEffects"
    };
    private static final String[] STABLE_CASE_FIELDS = {
            "heapStateInitializers", "heapObservations",
            "finiteMapSnapshots", "vmIntrinsicPlaceholderBindings",
            "unforcedEnvironmentValidationRequirements"
    };
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private final JsonObject raw;
    private final Scope scope;
    private final String regionId, summaryId, sourceTaskId;
    private final boolean relationallyComplete;
    private final JsonArray pathCondition;
    private final JsonObject outputExpressions;
    private final JsonArray edgeBindings;
    private final List<SummaryBranchMapping> branchMappings;
    private final String branchMappingIssue;
    private final AlphaNormalizer alpha;
    private final String runtimeBindingIdentity;
    private final String pathKey;
    private final String stableCasePayload;

    private PathObservation(JsonObject summary, JsonObject task) {
        this.raw = summary.deepCopy();
        this.scope = Scope.decode(raw, task);
        this.regionId = string(raw, "regionId");
        this.summaryId = string(raw, "summaryId");
        this.sourceTaskId = string(raw, "taskId");
        this.relationallyComplete = bool(raw, "relationallyComplete", false);
        this.pathCondition = array(raw, "pathCondition").deepCopy();
        this.outputExpressions = object(raw,
                "outputExpressions").deepCopy();
        this.edgeBindings = array(raw, "edgeBindings").deepCopy();
        JsonObject stableCase = new JsonObject();
        for (String field : STABLE_CASE_FIELDS) {
            stableCase.add(field, array(raw, field).deepCopy());
        }
        this.stableCasePayload = CanonicalJson.render(stableCase);
        List<SummaryBranchMapping> decoded = Collections.emptyList();
        String issue = "";
        try {
            decoded = SummaryBranchMapping.fromSummary(raw);
        } catch (IllegalArgumentException malformed) {
            issue = firstNonBlank(malformed.getMessage(), "UNKNOWN");
        }
        this.branchMappings = Collections.unmodifiableList(decoded);
        this.branchMappingIssue = issue;
        this.alpha = new AlphaNormalizer(raw);
        this.runtimeBindingIdentity = stableRuntimeBindings(raw, alpha);
        this.pathKey = stablePathKey(raw, scope, alpha,
                runtimeBindingIdentity);
    }

    public static PathObservation decode(JsonObject summary, JsonObject task) {
        if (summary == null) {
            throw new IllegalArgumentException("summary is required");
        }
        return new PathObservation(summary, task);
    }

    public static String stablePathKey(JsonObject summary) {
        return decode(summary, null).pathKey;
    }

    public String regionId() { return regionId; }
    public String summaryId() { return summaryId; }
    public String sourceTaskId() { return sourceTaskId; }
    public boolean relationallyComplete() { return relationallyComplete; }
    public Scope scope() { return scope; }
    public String pathKey() { return pathKey; }
    public List<SummaryBranchMapping> branchMappings() {
        return branchMappings;
    }
    public String branchMappingIssue() { return branchMappingIssue; }
    public JsonArray pathCondition() { return pathCondition.deepCopy(); }
    public JsonObject outputExpressions() {
        return outputExpressions.deepCopy();
    }
    public JsonArray edgeBindings() { return edgeBindings.deepCopy(); }

    void copyRelationEvidenceTo(JsonObject target) {
        for (String field : RELATION_EVIDENCE_FIELDS) {
            target.add(field, array(raw, field).deepCopy());
        }
    }

    public String stableCasePayload() { return stableCasePayload; }

    public boolean hasExactOutputSet(Set<String> outputPorts) {
        return new TreeSet<>(outputExpressions.keySet())
                .equals(new TreeSet<>(outputPorts));
    }

    public JsonArray prefixBefore(int conditionIndex) {
        JsonArray prefix = new JsonArray();
        for (int index = 0; index < conditionIndex; index++) {
            prefix.add(pathCondition.get(index).deepCopy());
        }
        return prefix;
    }

    public String flipKey(SummaryBranchMapping mapping,
                          boolean desiredOutcome) {
        StringBuilder value = new StringBuilder();
        component(value, regionId);
        component(value, scope.identity);
        component(value, alphaCanonical(
                prefixBefore(mapping.summaryPcIndex()), alpha));
        component(value, mapping.siteId());
        component(value, String.valueOf(mapping.occurrence()));
        component(value, String.valueOf(desiredOutcome));
        component(value, runtimeBindingIdentity);
        return sha256(value.toString());
    }

    public JsonObject replayPayload() { return raw.deepCopy(); }
    public JsonArray dynamicFieldBindings() {
        return array(raw, "dynamicFieldBindings").deepCopy();
    }

    public static final class Scope {
        private final ClosureGoalKind goalKind;
        private final String goalId;
        private final OutputClosureContract outputClosure;
        private final Set<String> branchSites;
        private final String identity;
        private final String outputClosureIdentity;

        private Scope(ClosureGoalKind goalKind, String goalId,
                      OutputClosureContract outputClosure,
                      Set<String> branchSites, String identity) {
            this.goalKind = goalKind;
            this.goalId = goalId;
            this.outputClosure = outputClosure;
            this.branchSites = Collections.unmodifiableSet(branchSites);
            this.identity = identity;
            this.outputClosureIdentity = outputClosure == null ? ""
                    : CanonicalJson.render(outputClosure.toJson());
        }

        public static Scope decode(JsonObject summary, JsonObject task) {
            JsonObject canonical = summary != null ? summary : task;
            if (canonical == null) {
                throw new IllegalArgumentException(
                        "closure goal is required");
            }
            ClosureGoalKind goalKind = ClosureGoalKind.fromTask(canonical);
            String goalId = string(canonical, "goalId");
            if (goalId.isEmpty()) {
                throw new IllegalArgumentException(
                        "closure goal is required");
            }
            if (goalKind.capturesTargetReach()) {
                JsonObject source = task != null ? task : canonical;
                Set<String> sites = new LinkedHashSet<>();
                String targetMethod = string(source, "targetMethod");
                for (JsonElement element : array(source, "branches")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject branch = element.getAsJsonObject();
                    if (!"EXPLORE".equals(string(branch, "policy"))) continue;
                    String site = string(branch, "siteId");
                    if (!site.isEmpty() && (targetMethod.isEmpty()
                            || site.startsWith(targetMethod + "#"))) {
                        sites.add(site);
                    }
                }
                String region = firstNonBlank(string(source, "regionId"),
                        string(canonical, "regionId"));
                String instance = firstNonBlank(string(source,
                        "regionInstanceId"), string(canonical,
                        "regionInstanceId"));
                return new Scope(goalKind, goalId, null, sites,
                        "TARGET_REACH_CLOSURE_V1\n" + goalId + "\n"
                                + region + "\n" + instance + "\n"
                                + targetMethod);
            }
            OutputClosureContract contract = OutputClosureCodec.decode(
                    canonical);
            return new Scope(goalKind, goalId, contract,
                    new LinkedHashSet<>(
                            contract.executionScope().branchSites()),
                    "OUTPUT_RELATION_CLOSURE_V1\n" + goalId + "\n"
                            + contract.demandKey() + "\n"
                            + contract.closureFingerprint());
        }

        public ClosureGoalKind goalKind() { return goalKind; }
        public String goalId() { return goalId; }
        public OutputClosureContract outputClosure() {
            return outputClosure;
        }
        public Set<String> branchSites() { return branchSites; }
        public String identity() { return identity; }
        public String outputClosureIdentity() {
            return outputClosureIdentity;
        }
    }

    private static String stablePathKey(
            JsonObject summary, Scope scope, AlphaNormalizer alpha,
            String runtimeBindings) {
        StringBuilder value = new StringBuilder();
        component(value, string(summary, "regionId"));
        component(value, scope.identity);
        component(value, alphaCanonical(summary.get("pathCondition"), alpha));
        component(value, alphaCanonical(summary.get("outputExpressions"),
                alpha));
        component(value, alphaCanonical(summary.get("heapEffects"), alpha));
        component(value, runtimeBindings);
        component(value, string(summary, "normalExit"));
        component(value, string(summary, "exceptionType"));
        return sha256(value.toString());
    }

    private static String stableDynamicBindings(
            JsonObject summary, AlphaNormalizer alpha) {
        List<String> bindings = new ArrayList<>();
        for (JsonElement element : array(summary, "dynamicFieldBindings")) {
            if (!element.isJsonObject()) {
                bindings.add(alphaCanonical(element, alpha));
                continue;
            }
            JsonObject source = element.getAsJsonObject();
            JsonObject stable = new JsonObject();
            stable.addProperty("kind", string(source, "kind"));
            stable.addProperty("baseInputSymbol", string(source,
                    "baseInputSymbol"));
            stable.addProperty("dynamicFieldSymbol", string(source,
                    "dynamicFieldSymbol"));
            stable.addProperty("materializationSiteId", string(source,
                    "materializationSiteId"));
            stable.addProperty("materializationOccurrence", integer(source,
                    "materializationOccurrence", -1));
            for (String field : new String[]{"fieldSignature", "fieldPath",
                    "keyExpression", "keyExpressionAuthority",
                    "mapProjectionSelector", "runtimeSymbolizationAuthority",
                    "projectionEvidenceAuthority", "outputValidationMode"}) {
                JsonElement value = source.get(field);
                if (value != null) stable.add(field, value.deepCopy());
            }
            stable.addProperty("complete", bool(source, "complete", false));
            bindings.add(alphaCanonical(stripVolatileIdentity(stable),
                    alpha));
        }
        Collections.sort(bindings);
        return CanonicalJson.render(GSON.toJsonTree(bindings));
    }

    private static String stableRuntimeBindings(
            JsonObject summary, AlphaNormalizer alpha) {
        return stableDynamicBindings(summary, alpha) + "\n"
                + stableEngineArrayBindings(summary, alpha);
    }

    private static String stableEngineArrayBindings(
            JsonObject summary, AlphaNormalizer alpha) {
        List<JsonElement> ordered = new ArrayList<>();
        for (JsonElement element : array(summary,
                "engineArrayInputBindings")) {
            ordered.add(element);
        }
        Collections.sort(ordered, (left, right) -> {
            if (!left.isJsonObject() || !right.isJsonObject()) {
                return CanonicalJson.render(left).compareTo(
                        CanonicalJson.render(right));
            }
            JsonObject l = left.getAsJsonObject();
            JsonObject r = right.getAsJsonObject();
            int port = string(l, "inputPort").compareTo(
                    string(r, "inputPort"));
            return port != 0 ? port : string(l, "inputCell").compareTo(
                    string(r, "inputCell"));
        });
        List<String> bindings = new ArrayList<>();
        for (JsonElement element : ordered) {
            if (!element.isJsonObject()) {
                bindings.add(alphaCanonical(element, alpha));
                continue;
            }
            JsonObject source = element.getAsJsonObject();
            JsonObject stable = new JsonObject();
            stable.addProperty("schemaVersion", integer(source,
                    "schemaVersion", -1));
            stable.addProperty("kind", string(source, "kind"));
            stable.addProperty("inputPort", string(source, "inputPort"));
            stable.addProperty("inputCell", string(source, "inputCell"));
            stable.addProperty("inputJavaTypeDescriptor", string(source,
                    "inputJavaTypeDescriptor"));
            stable.addProperty("engineArrayId", alpha.arrayId(string(source,
                    "engineArrayId")));
            bindings.add(alphaCanonical(stable, alpha));
        }
        Collections.sort(bindings);
        return CanonicalJson.render(GSON.toJsonTree(bindings));
    }

    private static JsonElement stripVolatileIdentity(JsonElement value) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()) {
            return value == null ? JsonNull.INSTANCE : value.deepCopy();
        }
        if (value.isJsonArray()) {
            JsonArray result = new JsonArray();
            for (JsonElement element : value.getAsJsonArray()) {
                result.add(stripVolatileIdentity(element));
            }
            return result;
        }
        JsonObject result = new JsonObject();
        for (Map.Entry<String, JsonElement> entry
                : value.getAsJsonObject().entrySet()) {
            String key = entry.getKey().toLowerCase();
            if (key.contains("objecttoken")
                    || "entryreadobservationid".equals(key)) continue;
            result.add(entry.getKey(), stripVolatileIdentity(
                    entry.getValue()));
        }
        return result;
    }

    private static String alphaCanonical(
            JsonElement value, AlphaNormalizer alpha) {
        if (value == null || value.isJsonNull()) return "null";
        if (value.isJsonPrimitive()) {
            return GSON.toJson(value.getAsJsonPrimitive());
        }
        if (value.isJsonArray()) {
            StringBuilder result = new StringBuilder("[");
            boolean first = true;
            for (JsonElement element : value.getAsJsonArray()) {
                if (!first) result.append(',');
                first = false;
                result.append(alphaCanonical(element, alpha));
            }
            return result.append(']').toString();
        }
        JsonObject object = value.getAsJsonObject();
        String type = string(object, "_type");
        StringBuilder result = new StringBuilder("{");
        boolean first = true;
        for (String key : new TreeSet<>(object.keySet())) {
            if (!first) result.append(',');
            first = false;
            result.append(GSON.toJson(key)).append(':');
            JsonElement field = object.get(key);
            if ("_exp".equals(key)
                    && ("SymbolExpression".equals(type)
                    || "ConSymbolExp".equals(type))
                    && field != null && field.isJsonPrimitive()) {
                result.append(GSON.toJson(alpha.symbol(
                        field.getAsString())));
            } else if ("_count".equals(key)
                    && "PlaceholderExpression".equals(type)
                    && field != null && field.isJsonPrimitive()) {
                result.append(GSON.toJson(alpha.placeholder(
                        string(object, "_place_holder_func"),
                        field.getAsString())));
            } else if ("_arr_str".equals(key)
                    && "_array_expr".equals(type)
                    && field != null && field.isJsonPrimitive()) {
                result.append(GSON.toJson(alpha.arrayId(
                        field.getAsString())));
            } else {
                result.append(alphaCanonical(field, alpha));
            }
        }
        return result.append('}').toString();
    }

    private static final class AlphaNormalizer {
        private final Set<String> canonicalPorts = new LinkedHashSet<>();
        private final Map<String, String> symbols = new LinkedHashMap<>();
        private final Map<String, String> placeholders = new LinkedHashMap<>();
        private final Map<String, String> arrays = new LinkedHashMap<>();

        private AlphaNormalizer(JsonObject summary) {
            collectPortArray(summary.get("symbolicInputs"));
            JsonElement outputs = summary.get("outputExpressions");
            if (outputs != null && outputs.isJsonObject()) {
                for (String port : outputs.getAsJsonObject().keySet()) {
                    addPort(port);
                }
            }
            for (JsonElement element : array(summary, "heapEffects")) {
                if (!element.isJsonObject()) continue;
                JsonObject effect = element.getAsJsonObject();
                addPort(string(effect, "inputPort"));
                addPort(string(effect, "outputPort"));
            }
            for (JsonElement element : array(summary,
                    "heapStateInitializers")) {
                if (!element.isJsonObject()) continue;
                JsonObject initializer = element.getAsJsonObject();
                addPort(string(initializer, "statePort"));
                addPort(string(initializer, "requestedOutputPort"));
            }
            for (JsonElement element : array(summary,
                    "engineArrayInputBindings")) {
                if (element.isJsonObject()) {
                    addPort(string(element.getAsJsonObject(), "inputPort"));
                }
            }
            for (JsonElement element : array(summary,
                    "dynamicFieldBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject selector = object(element.getAsJsonObject(),
                        "mapProjectionSelector");
                addPort(string(selector, "mapInputPort"));
                addPort(string(selector, "outputPort"));
            }
        }

        private void collectPortArray(JsonElement value) {
            if (value == null || !value.isJsonArray()) return;
            for (JsonElement element : value.getAsJsonArray()) {
                if (element.isJsonPrimitive()) {
                    addPort(element.getAsString());
                } else if (element.isJsonObject()) {
                    collectPortObject(element);
                }
            }
        }

        private void collectPortObject(JsonElement value) {
            JsonObject object = value.getAsJsonObject();
            addPort(string(object, "portId"));
            addPort(string(object, "inputPort"));
            addPort(string(object, "outputPort"));
        }

        private void addPort(String candidate) {
            if (looksLikeCanonicalPort(candidate)) {
                canonicalPorts.add(candidate);
            }
        }

        private String symbol(String raw) {
            if (containsCanonicalPort(raw)) return raw;
            return alpha(symbols, raw, "@symbol.");
        }

        private String placeholder(String function, String count) {
            return alpha(placeholders, firstNonBlank(function, "unknown")
                    + "\u0000" + firstNonBlank(count, "0"),
                    "@placeholder.");
        }

        private String arrayId(String raw) {
            return alpha(arrays, raw, "@array.");
        }

        private boolean containsCanonicalPort(String raw) {
            if (looksLikeCanonicalPort(raw)) return true;
            for (String port : canonicalPorts) {
                int start = raw.indexOf(port);
                while (start >= 0) {
                    int end = start + port.length();
                    boolean left = start == 0 || raw.charAt(start - 1) == '_';
                    boolean right = end == raw.length()
                            || raw.charAt(end) == '_';
                    if (left && right) return true;
                    start = raw.indexOf(port, start + 1);
                }
            }
            return false;
        }

        private static String alpha(
                Map<String, String> values, String raw, String prefix) {
            String existing = values.get(raw);
            if (existing != null) return existing;
            String normalized = prefix + values.size();
            values.put(raw, normalized);
            return normalized;
        }

        private static boolean looksLikeCanonicalPort(String value) {
            String candidate = firstNonBlank(value);
            return candidate.startsWith("REGION.")
                    && (candidate.contains(".in.")
                    || candidate.contains(".out."));
        }
    }

    private static void component(StringBuilder output, String value) {
        String safe = value == null ? "" : value;
        output.append(safe.length()).append(':').append(safe).append('|');
    }

    static String sha256(String value) {
        try {
            byte[] hash = MessageDigest.getInstance("SHA-256").digest(
                    value.getBytes(StandardCharsets.UTF_8));
            return String.format(Locale.ROOT, "%064x",
                    new BigInteger(1, hash));
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException(impossible);
        }
    }
}
