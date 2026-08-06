package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.PathObservation;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Builds one solver query from all closed concolic paths which reached the
 * exact annotated exception type in the consumer target region.
 */
public final class TargetReachPathQueryBuilder {
    private static final Gson JSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private TargetReachPathQueryBuilder() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        JsonObject result = build(arguments);
        String encoded = JSON.toJson(result);
        ArtifactIO.replace(arguments.output,
                encoded + System.lineSeparator());
        System.out.println(encoded);
    }

    static JsonObject build(Arguments arguments) throws IOException {
        JsonObject manifest = ArtifactIO.readObject(arguments.pathManifest);
        if (!"CLOSED".equals(string(manifest, "state"))
                || array(manifest, "gaps").size() != 0
                || !ClosureGoalKind.TARGET_REACH_CLOSURE.name().equals(
                string(manifest, ClosureGoalKind.TASK_FIELD))) {
            throw new IOException(
                    "target path worklist is not completely closed");
        }

        List<JsonObject> seeds = ArtifactIO.readJsonl(arguments.seedQuery,
                "Malformed target seed query %1$s:%2$d",
                "Non-object target seed query %1$s:%2$d");
        if (seeds.size() != 1
                || !"TARGET_BRANCH_SOLVER_QUERY".equals(
                string(seeds.get(0), "kind"))
                || !bool(seeds.get(0), "readyForSolver", false)) {
            throw new IOException(
                    "exactly one solver-ready target seed query is required");
        }
        JsonObject seed = seeds.get(0);
        String region = string(seed, "regionId");
        String instance = string(seed, "regionInstanceId");
        String canonicalInstance = firstNonBlank(string(seed,
                "canonicalRegionInstanceId"), instance);
        String goalId = string(seed, "goalId");
        String targetSite = string(seed, "targetSiteId");
        if (!region.equals(string(manifest, "regionId"))
                || !goalId.equals(string(manifest, "goalId"))
                || !canonicalInstance.equals(string(manifest,
                "regionInstanceId"))
                || region.isEmpty() || instance.isEmpty()
                || goalId.isEmpty() || targetSite.isEmpty()) {
            throw new IOException(
                    "target seed and closed path scope do not match");
        }
        if (!arguments.targetInstance.isEmpty()
                && !arguments.targetInstance.equals(instance)) {
            throw new IOException("selected target instance does not match "
                    + "the exact seed query occurrence");
        }
        SelectedOccurrence selected = SelectedOccurrence.decode(
                object(seed, "selectedTargetOccurrence"), region,
                instance, "target seed query");
        final BranchReplayContract targetReplay;
        try {
            targetReplay = BranchReplayContract.fromJson(
                    object(seed, "replayContract"));
        } catch (IllegalArgumentException malformed) {
            throw new IOException("malformed target replay contract",
                    malformed);
        }
        if (!targetSite.equals(targetReplay.source().siteId())) {
            throw new IOException(
                    "target replay contract does not match target site");
        }
        int targetOccurrence = targetReplay.source().occurrence();
        boolean desiredOutcome = targetReplay.requiredTakenOutcome();

        Map<String, JsonObject> pathsByKey = new LinkedHashMap<>();
        List<JsonObject> summaries = ArtifactIO.readJsonl(arguments.summaries,
                "Malformed target summary %1$s:%2$d",
                "Non-object target summary %1$s:%2$d");
        for (JsonObject summary : summaries) {
            if (!region.equals(string(summary, "regionId"))
                    || !canonicalInstance.equals(string(summary,
                    "regionInstanceId"))
                    || !goalId.equals(string(summary, "goalId"))
                    || !ClosureGoalKind.fromTask(summary)
                    .capturesTargetReach()
                    || !bool(summary, "relationallyComplete", false)) {
                continue;
            }
            SelectedOccurrence summaryOccurrence =
                    selectedOccurrence(summary, region, instance,
                            canonicalInstance);
            selected.requireSameInstantiation(summaryOccurrence,
                    "target summary occurrence");
            selected.requireExactDemandLedger(summary);
            // Parsing is the schema/admission boundary for branch-owned
            // predicates. The importer already normalized the PC; this check
            // prevents a malformed mapping row from entering the path set.
            PathObservation observation = PathObservation.decode(
                    summary, null);
            if (!observation.branchMappingIssue().isEmpty()) {
                throw new IOException("Malformed target branch mapping: "
                        + observation.branchMappingIssue());
            }
            SummaryBranchMapping targetMapping = targetSiteMapping(
                    observation, targetSite, targetOccurrence);
            if (targetMapping == null) {
                continue;
            }

            JsonObject path = new JsonObject();
            final JsonArray constraints;
            if (targetMapping.witness().sourceTakenOutcome()
                    == desiredOutcome) {
                constraints = array(summary, "pathCondition").deepCopy();
                path.addProperty("fatalBranchConditionAuthority",
                        "WITNESSED_TARGET_OUTCOME_V1");
            } else {
                // The flip solver only proposes fresh paths; it is not a
                // semantic authority.  A path that witnessed the target
                // decision with the opposite outcome still proves the exact
                // decided prefix, and the fatal branch condition itself
                // stays symbolic: it is the complement of this path's own
                // witnessed predicate, decided at the reach stage.
                constraints = observation.prefixBefore(
                        targetMapping.summaryPcIndex());
                constraints.add(BranchPredicateAlgebra.complement(
                        targetMapping.witness()
                                .sourceSatisfiedPredicate()));
                path.addProperty("fatalBranchConditionAuthority",
                        "SYMBOLIC_COMPLEMENT_OF_WITNESSED_TARGET_V1");
            }
            String pathKey = observation.pathKey();
            path.add("constraints", remap(constraints,
                    selected.exactInputByCanonical));
            JsonObject previous = pathsByKey.put(pathKey, path);
            if (previous != null && !previous.equals(path)) {
                throw new IOException(
                        "conflicting reached target path: " + pathKey);
            }
        }

        List<String> pathKeys = new ArrayList<>(pathsByKey.keySet());
        Collections.sort(pathKeys);
        JsonArray encodedPaths = new JsonArray();
        for (String pathKey : pathKeys) {
            encodedPaths.add(pathsByKey.get(pathKey));
        }
        if (encodedPaths.size() == 0) {
            throw new IOException(
                    "closed target worklist contains no path reaching the "
                            + "required target branch outcome");
        }

        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        result.addProperty("regionId", region);
        result.addProperty("regionInstanceId", instance);
        result.addProperty("canonicalRegionInstanceId",
                canonicalInstance);
        result.addProperty("targetSiteId", targetSite);
        result.addProperty("targetOccurrence", targetOccurrence);
        result.addProperty("requiredTakenOutcome", desiredOutcome);
        result.addProperty("targetExceptionType", arguments.exceptionType);
        result.add("paths", encodedPaths);
        result.add("seedReplayContract", remap(
                object(seed, "replayContract"),
                selected.exactInputByCanonical));
        JsonObject symbolicContext = remap(
                object(seed, "symbolicContext"),
                selected.exactInputByCanonical).getAsJsonObject();
        selected.requireExactContext(symbolicContext);
        result.add("symbolicContext", symbolicContext);
        result.add("selectedTargetOccurrence", selected.encoded.deepCopy());
        result.addProperty("constraintAuthority",
                "CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1");
        return result;
    }

    /** The witnessed decision of the exact target site, or null. */
    private static SummaryBranchMapping targetSiteMapping(
            PathObservation observation, String siteId, int occurrence) {
        for (SummaryBranchMapping mapping
                : observation.branchMappings()) {
            if (mapping.isWitnessed()
                    && siteId.equals(mapping.siteId())
                    && occurrence == mapping.occurrence()) {
                return mapping;
            }
        }
        return null;
    }

    private static SelectedOccurrence selectedOccurrence(
            JsonObject summary, String region, String selectedInstance,
            String canonicalInstance) throws IOException {
        JsonObject catalog = object(summary,
                "occurrenceInstantiationCatalog");
        if (!"LOGICAL_SUMMARY_OCCURRENCE_CATALOG".equals(
                string(catalog, "kind"))
                || !canonicalInstance.equals(string(catalog,
                "canonicalRegionInstanceId"))
                || !string(summary, "logicalRegionId").equals(
                string(catalog, "logicalRegionId"))
                || !string(summary, "summaryReuseKey").equals(
                string(catalog, "summaryReuseKey"))) {
            throw new IOException("target summary has malformed logical "
                    + "occurrence catalog");
        }
        JsonObject selected = null;
        Set<String> instances = new LinkedHashSet<>();
        for (JsonElement element : array(catalog, "occurrences")) {
            if (!element.isJsonObject()) {
                throw new IOException("target summary occurrence catalog "
                        + "contains a non-object");
            }
            JsonObject occurrence = element.getAsJsonObject();
            String instance = string(occurrence, "regionInstanceId");
            if (instance.isEmpty() || !instances.add(instance)) {
                throw new IOException("target summary occurrence catalog "
                        + "contains an ambiguous instance " + instance);
            }
            if (selectedInstance.equals(instance)) selected = occurrence;
        }
        if (!instances.contains(canonicalInstance) || selected == null) {
            throw new IOException("target summary catalog does not contain "
                    + "the selected exact occurrence " + selectedInstance);
        }
        return SelectedOccurrence.decode(selected, region,
                selectedInstance, "target summary catalog");
    }

    private static JsonElement remap(JsonElement value,
                                     Map<String, String> ports) {
        if (value == null || value.isJsonNull()) return value;
        if (value.isJsonArray()) {
            JsonArray result = new JsonArray();
            for (JsonElement element : value.getAsJsonArray()) {
                result.add(remap(element, ports));
            }
            return result;
        }
        if (value.isJsonObject()) {
            JsonObject result = new JsonObject();
            for (Map.Entry<String, JsonElement> entry
                    : value.getAsJsonObject().entrySet()) {
                String key = ports.getOrDefault(entry.getKey(),
                        entry.getKey());
                if (result.has(key)) {
                    throw new IllegalArgumentException(
                            "target occurrence port remap collides at "
                                    + key);
                }
                result.add(key, remap(entry.getValue(), ports));
            }
            return result;
        }
        JsonPrimitive primitive = value.getAsJsonPrimitive();
        if (!primitive.isString()) return primitive.deepCopy();
        return new JsonPrimitive(remapPortTokens(
                primitive.getAsString(), ports));
    }

    private static String remapPortTokens(String value,
                                          Map<String, String> ports) {
        String exact = ports.get(value);
        if (exact != null) return exact;
        List<String> canonical = new ArrayList<>(ports.keySet());
        canonical.sort((left, right) -> Integer.compare(
                right.length(), left.length()));
        StringBuilder result = new StringBuilder();
        int cursor = 0;
        while (cursor < value.length()) {
            String match = "";
            for (String candidate : canonical) {
                if (!value.startsWith(candidate, cursor)) continue;
                int end = cursor + candidate.length();
                boolean leftBoundary = cursor == 0
                        || value.charAt(cursor - 1) == '_';
                boolean rightBoundary = end == value.length()
                        || value.charAt(end) == '_';
                if (leftBoundary && rightBoundary) {
                    match = candidate;
                    break;
                }
            }
            if (match.isEmpty()) {
                result.append(value.charAt(cursor++));
            } else {
                result.append(ports.get(match));
                cursor += match.length();
            }
        }
        return result.toString();
    }

    private static final class SelectedOccurrence {
        private final JsonObject encoded;
        private final String instance;
        private final long rootCallId;
        private final Map<String, String> exactInputByCanonical;
        private final Set<String> bindingIds;

        private SelectedOccurrence(JsonObject encoded, String instance,
                                   long rootCallId,
                                   Map<String, String> inputPorts,
                                   Set<String> bindingIds) {
            this.encoded = encoded.deepCopy();
            this.instance = instance;
            this.rootCallId = rootCallId;
            this.exactInputByCanonical = inputPorts;
            this.bindingIds = bindingIds;
        }

        private static SelectedOccurrence decode(
                JsonObject encoded, String region, String expectedInstance,
                String source) throws IOException {
            String instance = string(encoded, "regionInstanceId");
            long rootCallId = longInteger(encoded, "rootCallId", -1L);
            if (!expectedInstance.equals(instance)
                    || rootCallId >= 0L
                    && !instance.endsWith("#call" + rootCallId)) {
                throw new IOException(source + " has inconsistent selected "
                        + "target occurrence identity");
            }
            Map<String, String> inputPorts = new LinkedHashMap<>();
            Set<String> exactPorts = new LinkedHashSet<>();
            for (JsonElement element : array(encoded, "inputPortMap")) {
                if (!element.isJsonObject()) {
                    throw new IOException(source
                            + " has malformed inputPortMap");
                }
                JsonObject mapping = element.getAsJsonObject();
                String canonical = string(mapping, "canonicalPort");
                String exact = string(mapping, "exactPort");
                if (canonical.isEmpty() || exact.isEmpty()
                        || !exact.startsWith(region + ".in.")
                        || inputPorts.putIfAbsent(canonical, exact) != null
                        || !exactPorts.add(exact)) {
                    throw new IOException(source
                            + " has ambiguous target inputPortMap");
                }
            }
            if (array(encoded, "outputPortMap").size() != 0) {
                throw new IOException(source
                        + " target occurrence declares output ports");
            }
            Set<String> bindingIds = new LinkedHashSet<>();
            for (JsonElement element : array(encoded, "bindingIds")) {
                if (!element.isJsonPrimitive()
                        || !element.getAsJsonPrimitive().isString()) {
                    throw new IOException(source
                            + " has malformed binding ledger");
                }
                String id = element.getAsString().trim();
                if (id.isEmpty() || !bindingIds.add(id)) {
                    throw new IOException(source
                            + " has ambiguous binding ledger");
                }
            }
            return new SelectedOccurrence(encoded, instance, rootCallId,
                    inputPorts, bindingIds);
        }

        private void requireSameInstantiation(
                SelectedOccurrence other, String source) throws IOException {
            if (other == null || rootCallId != other.rootCallId
                    || !instance.equals(other.instance)
                    || !exactInputByCanonical.equals(
                    other.exactInputByCanonical)
                    || !other.bindingIds.containsAll(bindingIds)) {
                throw new IOException(source
                        + " does not match selected target evidence");
            }
        }

        private void requireExactDemandLedger(JsonObject summary)
                throws IOException {
            Set<String> exactInputs = new LinkedHashSet<>(
                    exactInputByCanonical.values());
            Set<String> demanded = new LinkedHashSet<>();
            for (JsonElement element : array(summary, "edgeBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if (!instance.equals(string(binding,
                        "toRegionInstance")) || !exactInputs.contains(
                        string(binding, "toInputPort"))) {
                    continue;
                }
                String id = string(binding, "edgeId");
                if (id.isEmpty()) {
                    throw new IOException("selected target demand binding "
                            + "has no edgeId");
                }
                demanded.add(id);
            }
            if (!bindingIds.equals(demanded)) {
                throw new IOException("selected target demand ledger does "
                        + "not exactly cover mapped input ports");
            }
        }

        private void requireExactContext(JsonObject context)
                throws IOException {
            if (!instance.equals(string(context, "regionInstanceId"))) {
                throw new IOException("selected target symbolic context has "
                        + "the wrong occurrence identity");
            }
            Set<String> exactInputs = new LinkedHashSet<>(
                    exactInputByCanonical.values());
            Set<String> contextBindings = new LinkedHashSet<>();
            collectContextBindings(array(context, "equalityRelations"),
                    exactInputs, contextBindings);
            collectContextBindings(array(context, "versionedStateMerges"),
                    exactInputs, contextBindings);
            for (JsonElement group : array(context,
                    "alternativeWriterGroups")) {
                if (group.isJsonObject()) {
                    collectContextBindings(array(group.getAsJsonObject(),
                            "alternatives"), exactInputs,
                            contextBindings);
                }
            }
            if (!bindingIds.equals(contextBindings)) {
                throw new IOException("selected target symbolic context "
                        + "does not exactly match demanded binding ledger");
            }
        }

        private void collectContextBindings(
                JsonArray relations, Set<String> exactInputs,
                Set<String> result) throws IOException {
            for (JsonElement element : relations) {
                if (!element.isJsonObject()) continue;
                JsonObject relation = element.getAsJsonObject();
                for (JsonElement selected : array(relation,
                        "selectedBindings")) {
                    if (!selected.isJsonObject()) continue;
                    JsonObject binding = selected.getAsJsonObject();
                    if (!instance.equals(string(binding,
                            "toRegionInstance")) || !exactInputs.contains(
                            string(binding, "toInputPort"))) {
                        throw new IOException("selected target symbolic "
                                + "context contains an unrelated binding");
                    }
                    String id = string(binding, "edgeId");
                    if (id.isEmpty()) {
                        throw new IOException("selected target symbolic "
                                + "context binding has no edgeId");
                    }
                    result.add(id);
                }
            }
        }
    }

    static final class Arguments {
        private final Path summaries;
        private final Path pathManifest;
        private final Path seedQuery;
        private final String exceptionType;
        private final String targetInstance;
        private final Path output;

        private Arguments(Path summaries, Path pathManifest,
                          Path seedQuery, String exceptionType,
                          String targetInstance,
                          Path output) {
            this.summaries = summaries;
            this.pathManifest = pathManifest;
            this.seedQuery = seedQuery;
            this.exceptionType = exceptionType;
            this.targetInstance = targetInstance;
            this.output = output;
        }

        static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; index < argv.length; index++) {
                String option = argv[index];
                if (!option.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException(
                            "Expected --name value, got " + option);
                }
                values.put(option.substring(2), argv[++index]);
            }
            return new Arguments(requiredPath(values, "summaries"),
                    requiredPath(values, "path-manifest"),
                    requiredPath(values, "seed-query"),
                    required(values, "exception-type"),
                    optional(values, "target-instance"),
                    requiredPath(values, "output"));
        }

        private static Path requiredPath(Map<String, String> values,
                                         String name) {
            return Paths.get(required(values, name));
        }

        private static String required(Map<String, String> values,
                                       String name) {
            String value = values.get(name);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + name);
            }
            return value.trim();
        }

        private static String optional(Map<String, String> values,
                                       String name) {
            String value = values.get(name);
            return value == null ? "" : value.trim();
        }
    }
}
