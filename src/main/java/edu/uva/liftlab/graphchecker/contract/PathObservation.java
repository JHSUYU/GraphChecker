package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.concolic.SummaryBranchMapping;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Immutable, once-decoded view of one imported concolic path summary.
 *
 * <p>The original summary is retained only as the attested replay payload.
 * Worklist and relation consumers use the typed and canonical fields below.</p>
 */
public final class PathObservation {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private final JsonObject raw;
    private final Scope scope;
    private final List<SummaryBranchMapping> branchMappings;
    private final String branchMappingIssue;
    private final AlphaNormalizer alpha;
    private final String pathKey;
    private final JsonArray relationPathCondition;
    private final String relationGuardKey;
    private final String relationKey;

    private PathObservation(JsonObject summary, JsonObject task) {
        this.raw = summary.deepCopy();
        this.scope = Scope.decode(raw, task);
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
        this.pathKey = stablePathKey(raw, scope,
                raw.get("pathCondition"), alpha);
        this.relationPathCondition = projectRelationPathCondition(
                raw, scope, branchMappings);
        this.relationGuardKey = CanonicalJson.sha256(alphaCanonical(
                relationPathCondition, new AlphaNormalizer(raw)));
        this.relationKey = stablePathKey(raw, scope,
                relationPathCondition, new AlphaNormalizer(raw));
    }

    public static PathObservation decode(JsonObject summary, JsonObject task) {
        if (summary == null) {
            throw new IllegalArgumentException("summary is required");
        }
        return new PathObservation(summary, task);
    }

    public String regionId() {
        return scope.outputClosure == null ? string(raw, "regionId")
                : scope.outputClosure.producer().regionId();
    }
    public String sourceTaskId() { return string(raw, "taskId"); }
    public boolean relationallyComplete() {
        return bool(raw, "relationallyComplete", false);
    }
    public Scope scope() { return scope; }
    public String pathKey() { return pathKey; }
    public List<SummaryBranchMapping> branchMappings() {
        return branchMappings;
    }
    public String branchMappingIssue() { return branchMappingIssue; }
    public JsonArray pathCondition() {
        return array(raw, "pathCondition").deepCopy();
    }
    public JsonObject outputExpressions() {
        return object(raw, "outputExpressions").deepCopy();
    }
    public JsonArray relationPathCondition() {
        return relationPathCondition.deepCopy();
    }
    public String relationGuardKey() { return relationGuardKey; }
    public String relationKey() { return relationKey; }
    public JsonArray edgeBindings() {
        return array(raw, "edgeBindings").deepCopy();
    }

    public boolean hasExactOutputSet(Set<String> outputPorts) {
        return new TreeSet<>(object(raw, "outputExpressions").keySet())
                .equals(new TreeSet<>(outputPorts));
    }

    public JsonArray prefixBefore(int conditionIndex) {
        JsonArray prefix = new JsonArray();
        JsonArray conditions = array(raw, "pathCondition");
        for (int index = 0; index < conditionIndex; index++) {
            prefix.add(conditions.get(index).deepCopy());
        }
        return prefix;
    }

    public String flipKey(SummaryBranchMapping mapping,
                          boolean desiredOutcome) {
        StringBuilder value = new StringBuilder();
        component(value, regionId());
        component(value, scope.identity);
        component(value, alphaCanonical(
                prefixBefore(mapping.summaryPcIndex()), alpha));
        component(value, mapping.siteId());
        component(value, String.valueOf(mapping.occurrence()));
        component(value, String.valueOf(mapping.decisionOrdinal()));
        component(value, String.valueOf(desiredOutcome));
        return CanonicalJson.sha256(value.toString());
    }

    public JsonObject replayPayload() { return raw.deepCopy(); }
    public static final class Scope {
        private final ClosureGoalKind goalKind;
        private final String goalId;
        private final OutputClosureContract outputClosure;
        private final Set<String> branchSites;
        private final String identity;

        private Scope(ClosureGoalKind goalKind, String goalId,
                      OutputClosureContract outputClosure,
                      Set<String> branchSites, String identity) {
            this.goalKind = goalKind;
            this.goalId = goalId;
            this.outputClosure = outputClosure;
            this.branchSites = Collections.unmodifiableSet(branchSites);
            this.identity = identity;
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
            return outputClosure == null ? ""
                    : outputClosure.closureFingerprint();
        }
    }

    private static String stablePathKey(
            JsonObject summary, Scope scope, JsonElement pathCondition,
            AlphaNormalizer alpha) {
        StringBuilder value = new StringBuilder();
        component(value, scope.outputClosure == null
                ? string(summary, "regionId")
                : scope.outputClosure.producer().regionId());
        component(value, scope.identity);
        component(value, alphaCanonical(pathCondition, alpha));
        component(value, alphaCanonical(summary.get("outputExpressions"),
                alpha));
        component(value, string(summary, "normalExit"));
        component(value, string(summary, "exceptionType"));
        return CanonicalJson.sha256(value.toString());
    }

    private static JsonArray projectRelationPathCondition(
            JsonObject summary, Scope scope,
            List<SummaryBranchMapping> mappings) {
        JsonArray full = array(summary, "pathCondition");
        if (!scope.goalKind.capturesOutputRelation()) {
            return full.deepCopy();
        }
        Map<Integer, SummaryBranchMapping> owners = new LinkedHashMap<>();
        for (SummaryBranchMapping mapping : mappings) {
            if (mapping.isWitnessed()) {
                owners.put(mapping.summaryPcIndex(), mapping);
            }
        }
        JsonArray projected = new JsonArray();
        for (int index = 0; index < full.size(); index++) {
            SummaryBranchMapping owner = owners.get(index);
            if (owner != null
                    && !scope.branchSites.contains(owner.siteId())) {
                continue;
            }
            // Unowned conditions are solver context, not proven branch noise.
            projected.add(full.get(index).deepCopy());
        }
        return projected;
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

        private AlphaNormalizer(JsonObject summary) {
            collectPortArray(summary.get("symbolicInputs"));
            JsonElement outputs = summary.get("outputExpressions");
            if (outputs != null && outputs.isJsonObject()) {
                for (String port : outputs.getAsJsonObject().keySet()) {
                    addPort(port);
                }
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

}
