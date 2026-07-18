package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Derives the schema-2 producer-group catalog consumed by
 * {@link ConcolicComposedModelProjector}.
 *
 * <p>Roles are outputs, never configuration.  A target-state producer is
 * identified by an exact runtime read-from into the selected fatal map
 * receiver.  A lookup-key producer is identified by (1) one exact MAP_PUT
 * key in the selected summary case, (2) an UNSAT counterexample query proving
 * that the composer's emitted key term equals the fatal lookup term in that
 * case, and (3) one unambiguous path of individually runtime-confirmed edges
 * from the producer instance to the fatal instance.  Value fingerprints are
 * checked only on the equality edge that declares their endpoints; they are
 * never used to invent transitive edges.</p>
 *
 * <p>The planner emits a witness sidecar and an enriched immutable copy of
 * the input summaries.  The catalog records SHA-256 digests of every source
 * artifact.  The projector independently reopens and verifies those sources;
 * the embedded witness is therefore an index, not self-authenticating
 * evidence.</p>
 */
public final class ConcolicProducerGroupPlanner {
    static final String TARGET_MAP_STATE = "TARGET_MAP_STATE";
    static final String LOOKUP_KEY_PRODUCER = "LOOKUP_KEY_PRODUCER";
    static final String CATALOG_KIND = "CONCOLIC_PRODUCER_GROUP_CATALOG";
    static final String WITNESS_KIND = "CONCOLIC_PRODUCER_GROUP_WITNESSES";
    static final String LOOKUP_WITNESS_KIND =
            "RUNTIME_CONFIRMED_LOOKUP_KEY_PRODUCER";
    static final String TARGET_WITNESS_KIND =
            "RUNTIME_CONFIRMED_TARGET_MAP_STATE_PRODUCER";
    static final String LOOKUP_AUTHORITY =
            "COMPOSER_EXACT_TERM_IMPLICATION_AND_RUNTIME_CONFIRMED_EDGE_PATH";
    static final String TARGET_AUTHORITY =
            "EXACT_FATAL_MAP_RECEIVER_RUNTIME_CONFIRMED_READ_FROM";

    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();
    private static final Gson PRETTY = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();
    private static final Pattern REGION_INPUT = Pattern.compile(
            "REGION\\.[0-9]+\\.in\\.[0-9]+");
    private static final Pattern DECLARED_FIELD = Pattern.compile(
            "^<([^:]+):\\s+(.+)\\s+([^\\s>]+)>(?:#.*)?$");

    private ConcolicProducerGroupPlanner() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        Result result = plan(arguments);
        System.out.println(PRETTY.toJson(result.catalog));
    }

    static Result plan(Arguments arguments) throws Exception {
        require(arguments.compositionManifest, "composition manifest");
        require(arguments.smt, "composed SMT");
        require(arguments.summaries, "raw summaries");
        require(arguments.activations, "producer activations");
        require(arguments.targetActivations, "target activations");
        require(arguments.fatalQueries, "fatal queries");
        require(arguments.runtimeEdges, "runtime edge validation");
        require(arguments.z3, "Z3 executable");
        requireFreshOutputs(arguments.catalog, arguments.witnesses,
                arguments.enrichedSummaries);

        JsonObject composition = readJson(arguments.compositionManifest);
        if (!bool(composition, "complete", false)
                || !bool(composition, "boundedComposition", false)
                || !bool(composition, "fatalReplayValidated", false)
                || !bool(composition, "caseProjectionCatalogComplete",
                false)) {
            throw gap("COMPOSITION_NOT_COMPLETE_AND_BOUNDED");
        }
        List<String> bounded = strings(array(composition,
                "boundedUpstreamRegions"));
        if (bounded.isEmpty()) throw gap("NO_BOUNDED_UPSTREAM_REGIONS");

        List<JsonObject> originalSummaries = readJsonl(arguments.summaries);
        List<JsonObject> activations = readJsonl(arguments.activations);
        List<JsonObject> targetActivations = readJsonl(
                arguments.targetActivations);
        List<JsonObject> fatalQueries = readJsonl(arguments.fatalQueries);
        List<JsonObject> runtimeRows = readJsonl(arguments.runtimeEdges);
        String smt = new String(Files.readAllBytes(arguments.smt),
                StandardCharsets.UTF_8);

        String fatalRegion = string(composition, "fatalRegion");
        String fatalActivationId = firstNonBlank(
                arguments.targetActivationId,
                string(composition, "fatalActivation"));
        JsonObject targetActivation = selectActivation(targetActivations,
                fatalRegion, fatalActivationId, "target");
        JsonObject fatal = selectFatal(fatalQueries, targetActivation,
                fatalRegion);
        FatalLookup lookup = FatalLookup.resolve(fatal, targetActivation,
                smt);

        Map<String, JsonObject> summaryById = new LinkedHashMap<>();
        for (JsonObject summary : originalSummaries) {
            String id = string(summary, "summaryId");
            if (id.isEmpty() || summaryById.put(id, summary) != null) {
                throw gap("MISSING_OR_DUPLICATE_SUMMARY_ID:" + id);
            }
        }
        Map<String, List<JsonObject>> casesByRegion = casesByRegion(
                composition, bounded, summaryById);
        ExecutionScope executionScope = ExecutionScope.from(
                targetActivation, runtimeRows, sha256(arguments.runtimeEdges));
        RuntimeEdgeIndex runtime = RuntimeEdgeIndex.build(runtimeRows,
                sha256(arguments.runtimeEdges), executionScope);
        List<AdmittedEdge> admitted = admittedEdges(casesByRegion,
                summaryById, fatal, runtime);

        List<Group> groups = new ArrayList<>();
        List<JsonObject> allWitnesses = new ArrayList<>();
        for (String region : bounded) {
            List<JsonObject> cases = casesByRegion.get(region);
            if (cases == null || cases.isEmpty()) continue;
            Group group = deriveGroup(region, cases, summaryById,
                    activations, targetActivation, lookup, admitted, runtime,
                    smt, arguments);
            if (group != null) {
                groups.add(group);
                allWitnesses.addAll(group.witnesses);
            }
        }
        Collections.sort(groups, new Comparator<Group>() {
            @Override
            public int compare(Group left, Group right) {
                int role = Integer.compare(
                        TARGET_MAP_STATE.equals(left.role) ? 0 : 1,
                        TARGET_MAP_STATE.equals(right.role) ? 0 : 1);
                return role != 0 ? role : left.region.compareTo(right.region);
            }
        });
        int targetCount = 0;
        int lookupCount = 0;
        for (Group group : groups) {
            if (TARGET_MAP_STATE.equals(group.role)) targetCount++;
            if (LOOKUP_KEY_PRODUCER.equals(group.role)) lookupCount++;
        }
        if (targetCount != 1 || lookupCount < 1) {
            throw gap("PRODUCER_GROUP_ROLE_CARDINALITY:target="
                    + targetCount + ":lookup=" + lookupCount);
        }

        JsonObject witnesses = witnessSidecar(arguments, composition,
                targetActivation, fatal, lookup, allWitnesses);
        List<JsonObject> enriched = enrichSummaries(originalSummaries,
                allWitnesses, arguments);
        // The sidecar intentionally hashes only immutable source artifacts.
        // Output artifact hashes are placed in the catalog after they exist.
        writeJsonl(arguments.enrichedSummaries, enriched);
        write(arguments.witnesses, PRETTY.toJson(witnesses)
                + System.lineSeparator());
        JsonObject catalog = catalog(arguments, groups, witnesses,
                enriched.size());
        write(arguments.catalog, PRETTY.toJson(catalog)
                + System.lineSeparator());
        return new Result(catalog, witnesses, enriched);
    }

    private static Group deriveGroup(String region, List<JsonObject> cases,
                                     Map<String, JsonObject> summaryById,
                                     List<JsonObject> activations,
                                     JsonObject targetActivation,
                                     FatalLookup lookup,
                                     List<AdmittedEdge> admitted,
                                     RuntimeEdgeIndex runtime, String smt,
                                     Arguments arguments) throws Exception {
        List<JsonObject> targetWitnesses = new ArrayList<>();
        List<JsonObject> lookupWitnesses = new ArrayList<>();
        Integer expectedBound = null;
        for (JsonObject pathCase : cases) {
            String summaryId = string(pathCase, "sourceSummaryId");
            JsonObject summary = summaryById.get(summaryId);
            requireCompleteSummary(summary, region, summaryId);
            JsonObject activation = selectSummaryActivation(activations,
                    summary, region);
            int bound = boundedCandidateCount(activations, activation,
                    targetActivation, region);
            if (expectedBound != null && expectedBound != bound) {
                throw gap("CASE_BROADCAST_BOUND_CHANGED:" + region);
            }
            expectedBound = bound;

            List<AdmittedEdge> targetEdges = exactTargetStateEdges(pathCase,
                    summary, lookup, string(targetActivation,
                    "regionInstanceId"), runtime);
            if (targetEdges.size() == 1) {
                targetWitnesses.add(targetWitness(pathCase, summary,
                        activation, lookup, targetEdges.get(0), arguments));
            } else if (targetEdges.size() > 1) {
                throw gap("AMBIGUOUS_TARGET_STATE_EDGE:" + summaryId);
            }

            List<EffectTerm> keyTerms = effectTerms(pathCase, summary);
            List<EffectTerm> proven = new ArrayList<>();
            for (EffectTerm candidate : keyTerms) {
                EqualityProof proof = proveEquality(smt,
                        string(pathCase, "selectorSolverSymbol"),
                        candidate.solverTerm, lookup.solverTerm,
                        arguments.z3, arguments.timeoutMillis);
                if (proof.feasible && proof.implied) {
                    candidate.proof = proof;
                    proven.add(candidate);
                }
            }
            if (proven.size() > 1) {
                throw gap("AMBIGUOUS_LOOKUP_KEY_MAP_PUT:" + summaryId);
            }
            if (proven.size() == 1) {
                List<List<AdmittedEdge>> paths = paths(admitted,
                        string(summary, "regionInstanceId"),
                        string(targetActivation, "regionInstanceId"), 8,
                        string(pathCase, "caseId"));
                if (paths.size() != 1) {
                    throw gap("LOOKUP_RUNTIME_PATH_COUNT:" + summaryId
                            + ":" + paths.size());
                }
                lookupWitnesses.add(lookupWitness(pathCase, summary,
                        activation, lookup, proven.get(0), paths.get(0),
                        arguments));
            }
        }
        if (targetWitnesses.size() == cases.size()
                && lookupWitnesses.isEmpty()) {
            return new Group(region, TARGET_MAP_STATE, expectedBound,
                    targetWitnesses);
        }
        if (lookupWitnesses.size() == cases.size()
                && targetWitnesses.isEmpty()) {
            return new Group(region, LOOKUP_KEY_PRODUCER, expectedBound,
                    lookupWitnesses);
        }
        boolean hasMapEffects = false;
        for (JsonObject pathCase : cases) {
            JsonObject summary = summaryById.get(string(pathCase,
                    "sourceSummaryId"));
            if (!effectTerms(pathCase, summary).isEmpty()) {
                hasMapEffects = true;
                break;
            }
        }
        if (hasMapEffects || !targetWitnesses.isEmpty()
                || !lookupWitnesses.isEmpty()) {
            throw gap("ROLE_NOT_CASE_INVARIANT:" + region + ":target="
                    + targetWitnesses.size() + ":lookup="
                    + lookupWitnesses.size() + ":cases=" + cases.size());
        }
        // A bounded intermediate relation region is not a replay producer
        // group when it has no finite-map effect to materialize.
        return null;
    }

    private static List<AdmittedEdge> exactTargetStateEdges(
            JsonObject pathCase, JsonObject summary, FatalLookup lookup,
            String target,
            RuntimeEdgeIndex idx)
            throws IOException {
        List<AdmittedEdge> result = new ArrayList<>();
        for (JsonElement element : array(summary, "edgeBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!"READ_FROM".equals(string(binding, "relation"))
                    || !AutomaticRegionEdge
                    .trustedRuntimeReadFromBinding(binding)
                    || !target.equals(string(binding, "toRegionInstance"))
                    || !lookup.receiverPort.equals(string(binding,
                    "toInputPort"))
                    || !lookup.receiverCell.equals(string(binding,
                    "toInputCell"))) continue;
            AdmittedEdge validated = idx.validateSummaryBinding(binding);
            validated.admitSummary(pathCase, summary, binding);
            result.add(validated);
        }
        return result;
    }

    private static JsonObject targetWitness(JsonObject pathCase,
                                            JsonObject summary,
                                            JsonObject activation,
                                            FatalLookup lookup,
                                            AdmittedEdge edge,
                                            Arguments arguments)
            throws IOException {
        JsonObject witness = baseWitness(TARGET_WITNESS_KIND, pathCase,
                summary, activation, lookup, arguments);
        witness.addProperty("authority", TARGET_AUTHORITY);
        JsonArray path = new JsonArray();
        path.add(edge.json.deepCopy());
        witness.add("runtimeProvenancePath", path);
        witness.addProperty("runtimeProvenancePathLength", 1);
        witness.addProperty("targetMapReceiverReadFromConfirmed", true);
        finishWitnessId(witness);
        return witness;
    }

    private static JsonObject lookupWitness(JsonObject pathCase,
                                            JsonObject summary,
                                            JsonObject activation,
                                            FatalLookup lookup,
                                            EffectTerm effect,
                                            List<AdmittedEdge> path,
                                            Arguments arguments)
            throws IOException {
        JsonObject witness = baseWitness(LOOKUP_WITNESS_KIND, pathCase,
                summary, activation, lookup, arguments);
        witness.addProperty("authority", LOOKUP_AUTHORITY);
        witness.addProperty("runtimeConfirmed", true);
        witness.addProperty("valueEqualityConfirmed", true);
        witness.addProperty("rawEngineSymbol", effect.raw);
        witness.addProperty("summaryEffectId", effect.effectId);
        witness.addProperty("producerSolverTerm", effect.solverTerm);
        witness.addProperty("targetLookupSolverTerm", lookup.solverTerm);
        witness.add("symbolicEqualityProof", effect.proof.toJson());
        JsonArray runtimePath = new JsonArray();
        String execution = "";
        for (AdmittedEdge edge : path) {
            String current = string(edge.json, "executionIdentity");
            if (execution.isEmpty()) execution = current;
            if (!execution.equals(current)) {
                throw gap("CROSS_EXECUTION_RUNTIME_PATH:"
                        + string(summary, "summaryId"));
            }
            runtimePath.add(edge.json.deepCopy());
        }
        witness.add("runtimeProvenancePath", runtimePath);
        witness.addProperty("runtimeProvenancePathLength",
                runtimePath.size());
        witness.addProperty("executionIdentity", execution);
        witness.addProperty("crossSerializationPolicy",
                "EACH_EQUALITY_EDGE_CONNECTS_ONLY_ITS_DECLARED_ENDPOINTS");
        witness.addProperty("fingerprintTransitiveJoinForbidden", true);
        long writer = firstSequence(path, true);
        long reader = firstSequence(path, false);
        witness.addProperty("writerEventSeq", writer);
        witness.addProperty("readerEventSeq", reader);
        finishWitnessId(witness);
        return witness;
    }

    private static JsonObject baseWitness(String kind, JsonObject pathCase,
                                          JsonObject summary,
                                          JsonObject activation,
                                          FatalLookup lookup,
                                          Arguments arguments)
            throws IOException {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 2);
        result.addProperty("kind", kind);
        result.addProperty("complete", true);
        result.addProperty("producerRegion", string(summary, "regionId"));
        result.addProperty("producerRegionInstanceId",
                string(summary, "regionInstanceId"));
        result.addProperty("producerActivationId",
                string(activation, "activationId"));
        result.addProperty("sourceSummaryId",
                string(summary, "summaryId"));
        result.addProperty("sourceSummaryObjectSha256",
                sha256(GSON.toJson(summary)));
        result.addProperty("compositionCaseId", string(pathCase, "caseId"));
        result.addProperty("compositionCaseObjectSha256",
                sha256(GSON.toJson(pathCase)));
        result.addProperty("targetRegion", lookup.region);
        result.addProperty("targetRegionInstanceId", lookup.instance);
        result.addProperty("targetActivationId", lookup.activationId);
        result.addProperty("targetMapInput", lookup.receiverPort);
        result.addProperty("targetMapCell", lookup.receiverCell);
        result.addProperty("targetLookupRawEngineSymbol", lookup.rawKey);
        result.addProperty("runtimeEdgeArtifactSha256",
                sha256(arguments.runtimeEdges));
        result.addProperty("compositionManifestSha256",
                sha256(arguments.compositionManifest));
        result.addProperty("composedSmtSha256", sha256(arguments.smt));
        return result;
    }

    private static void finishWitnessId(JsonObject witness) {
        JsonObject stable = witness.deepCopy();
        stable.remove("witnessId");
        witness.addProperty("witnessId", "PRODUCER.WITNESS."
                + sha256(GSON.toJson(stable)).substring(0, 20));
    }

    private static long firstSequence(List<AdmittedEdge> path,
                                      boolean writer) {
        if (path.isEmpty()) return -1L;
        JsonObject first = writer ? path.get(0).json
                : path.get(path.size() - 1).json;
        return longInteger(first, writer ? "fromEventSeq" : "toEventSeq",
                -1L);
    }

    private static List<EffectTerm> effectTerms(JsonObject pathCase,
                                                JsonObject summary)
            throws IOException {
        Map<String, JsonObject> mappings = new LinkedHashMap<>();
        for (JsonElement element : array(pathCase,
                "rawEngineSymbolMappings")) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            String raw = string(mapping, "rawEngineSymbol");
            if (!raw.isEmpty() && mappings.put(raw, mapping) != null) {
                throw gap("DUPLICATE_CASE_RAW_SYMBOL:" + raw);
            }
        }
        List<EffectTerm> result = new ArrayList<>();
        Set<String> ids = new LinkedHashSet<>();
        for (JsonElement element : array(summary, "heapEffects")) {
            if (!element.isJsonObject()) continue;
            JsonObject effect = element.getAsJsonObject();
            if (!"MAP_PUT".equals(string(effect, "kind"))) continue;
            String id = string(effect, "effectId");
            String raw = expressionSymbol(effect.get("keyExpression"));
            JsonObject mapping = mappings.get(raw);
            if (id.isEmpty() || raw.isEmpty() || !ids.add(id)
                    || mapping == null
                    || !"Int".equals(string(mapping, "solverSort"))
                    || !"EMITTER_ACTUAL_TERM".equals(string(mapping,
                    "authority"))
                    || string(mapping, "solverTerm").isEmpty()) {
                throw gap("MAP_PUT_CASE_TERM_NOT_EXACT:" + id + ":" + raw);
            }
            result.add(new EffectTerm(id, raw,
                    string(mapping, "solverTerm")));
        }
        return result;
    }

    private static EqualityProof proveEquality(String smt, String selector,
                                               String producer,
                                               String target, Path z3,
                                               long timeoutMillis)
            throws IOException, InterruptedException {
        if (selector.isEmpty() || producer.isEmpty() || target.isEmpty()) {
            throw gap("INCOMPLETE_SYMBOLIC_EQUALITY_PROOF_TERMS");
        }
        String base = stripSolverCommands(smt);
        String feasibleInput = base + "\n(assert " + selector
                + ")\n(check-sat)\n";
        SolverOutput feasible = run(z3, feasibleInput, timeoutMillis);
        requireSolver(feasible, "producer case feasibility");
        String feasibleStatus = firstLine(feasible.stdout);
        if (!"sat".equals(feasibleStatus)) {
            return new EqualityProof(false, false, selector, producer,
                    target, feasibleStatus, "not-run", feasibleInput, "");
        }
        String proofInput = base + "\n(assert " + selector + ")\n"
                + "(assert (not (= " + producer + " " + target
                + ")))\n(check-sat)\n";
        SolverOutput proof = run(z3, proofInput, timeoutMillis);
        requireSolver(proof, "producer key equality implication");
        String status = firstLine(proof.stdout);
        return new EqualityProof(true, "unsat".equals(status), selector,
                producer, target, feasibleStatus, status, feasibleInput,
                proofInput);
    }

    private static String stripSolverCommands(String smt) {
        StringBuilder result = new StringBuilder();
        for (String line : firstNonBlank(smt).split("\\r?\\n")) {
            String trimmed = line.trim();
            if (trimmed.startsWith("(check-sat")
                    || trimmed.startsWith("(get-value")
                    || trimmed.startsWith("(get-model")
                    || trimmed.startsWith("(exit")) continue;
            result.append(line).append('\n');
        }
        return result.toString();
    }

    private static List<AdmittedEdge> admittedEdges(
            Map<String, List<JsonObject>> casesByRegion,
            Map<String, JsonObject> summaries, JsonObject fatal,
            RuntimeEdgeIndex runtime) throws IOException {
        Map<String, AdmittedEdge> result = new LinkedHashMap<>();
        for (List<JsonObject> cases : casesByRegion.values()) {
            for (JsonObject pathCase : cases) {
                JsonObject summary = summaries.get(string(pathCase,
                        "sourceSummaryId"));
                for (JsonElement element : array(summary, "edgeBindings")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject binding = element.getAsJsonObject();
                    if (!AutomaticRegionEdge
                            .trustedRuntimeReadFromBinding(binding)) continue;
                    AdmittedEdge edge = runtime.validateSummaryBinding(
                            binding);
                    edge.admitSummary(pathCase, summary, binding);
                    putUniqueEdge(result, edge);
                }
            }
        }
        JsonObject context = object(fatal, "symbolicContext");
        for (JsonElement element : array(context, "equalityRelations")) {
            if (!element.isJsonObject()) continue;
            addContextRelation(element.getAsJsonObject(), runtime, result);
        }
        for (JsonElement element : array(context, "versionedStateMerges")) {
            if (!element.isJsonObject()) continue;
            addContextRelation(element.getAsJsonObject(), runtime, result);
        }
        for (JsonElement element : array(context,
                "alternativeWriterGroups")) {
            if (!element.isJsonObject()) continue;
            for (JsonElement alternative : array(element.getAsJsonObject(),
                    "alternatives")) {
                if (alternative.isJsonObject()) addContextRelation(
                        alternative.getAsJsonObject(), runtime, result);
            }
        }
        return new ArrayList<>(result.values());
    }

    private static void addContextRelation(JsonObject relation,
                                           RuntimeEdgeIndex runtime,
                                           Map<String, AdmittedEdge> result)
            throws IOException {
        for (JsonElement element : array(relation, "selectedBindings")) {
            if (!element.isJsonObject()) continue;
            AdmittedEdge edge = runtime.validateContextBinding(relation,
                    element.getAsJsonObject());
            edge.admitFatalContext(relation, element.getAsJsonObject());
            putUniqueEdge(result, edge);
        }
    }

    private static void putUniqueEdge(Map<String, AdmittedEdge> result,
                                      AdmittedEdge edge) throws IOException {
        String key = edge.identity();
        AdmittedEdge old = result.get(key);
        if (old == null) {
            result.put(key, edge);
        } else {
            old.mergeAdmissions(edge);
        }
    }

    private static List<List<AdmittedEdge>> paths(List<AdmittedEdge> edges,
                                                   String source,
                                                   String target,
                                                   int maxDepth,
                                                   String selectedCaseId) {
        Map<String, List<AdmittedEdge>> outgoing = new LinkedHashMap<>();
        for (AdmittedEdge edge : edges) {
            if (!edge.admittedForCase(selectedCaseId)) continue;
            List<AdmittedEdge> list = outgoing.get(edge.fromInstance());
            if (list == null) {
                list = new ArrayList<>();
                outgoing.put(edge.fromInstance(), list);
            }
            list.add(edge);
        }
        List<List<AdmittedEdge>> result = new ArrayList<>();
        Deque<AdmittedEdge> path = new ArrayDeque<>();
        Set<String> visited = new LinkedHashSet<>();
        visited.add(source);
        dfsPaths(source, target, maxDepth, outgoing, path, visited, result);
        return result;
    }

    private static void dfsPaths(String current, String target, int depth,
                                 Map<String, List<AdmittedEdge>> outgoing,
                                 Deque<AdmittedEdge> path,
                                 Set<String> visited,
                                 List<List<AdmittedEdge>> result) {
        if (result.size() > 1 || depth < 1) return;
        List<AdmittedEdge> next = outgoing.get(current);
        if (next == null) return;
        for (AdmittedEdge edge : next) {
            String node = edge.toInstance();
            if (!visited.add(node)) continue;
            path.addLast(edge);
            if (target.equals(node)) {
                result.add(new ArrayList<>(path));
            } else {
                dfsPaths(node, target, depth - 1, outgoing, path, visited,
                        result);
            }
            path.removeLast();
            visited.remove(node);
            if (result.size() > 1) return;
        }
    }

    private static Map<String, List<JsonObject>> casesByRegion(
            JsonObject composition, List<String> bounded,
            Map<String, JsonObject> summaries) throws IOException {
        Set<String> allowed = new LinkedHashSet<>(bounded);
        Map<String, List<JsonObject>> result = new LinkedHashMap<>();
        Set<String> caseIds = new LinkedHashSet<>();
        for (JsonElement element : array(composition,
                "caseProjectionCatalog")) {
            if (!element.isJsonObject()) continue;
            JsonObject pathCase = element.getAsJsonObject();
            String region = string(pathCase, "regionId");
            if (!allowed.contains(region)) continue;
            String caseId = string(pathCase, "caseId");
            String summaryId = string(pathCase, "sourceSummaryId");
            if (integer(pathCase, "schemaVersion", -1) != 1
                    || !"GUARDED_CASE_PROJECTION_CATALOG".equals(string(
                    pathCase, "kind"))
                    || !bool(pathCase, "complete", false)
                    || caseId.isEmpty() || !caseIds.add(caseId)
                    || summaryId.isEmpty() || summaries.get(summaryId) == null
                    || !"EMITTER_ACTUAL_TERM_CAPTURE_IN_CASE_SCOPE".equals(
                    string(pathCase, "rawEngineSymbolMappingAuthority"))) {
                throw gap("INCOMPLETE_OR_DUPLICATE_COMPOSITION_CASE:"
                        + caseId);
            }
            List<JsonObject> rows = result.get(region);
            if (rows == null) {
                rows = new ArrayList<>();
                result.put(region, rows);
            }
            rows.add(pathCase);
        }
        return result;
    }

    private static JsonObject witnessSidecar(Arguments arguments,
                                             JsonObject composition,
                                             JsonObject targetActivation,
                                             JsonObject fatal,
                                             FatalLookup lookup,
                                             List<JsonObject> witnesses)
            throws IOException {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 2);
        result.addProperty("kind", WITNESS_KIND);
        result.addProperty("complete", true);
        result.add("sourceArtifacts", sourceArtifacts(arguments));
        result.addProperty("fatalRegion", string(composition, "fatalRegion"));
        result.addProperty("fatalActivationId",
                string(targetActivation, "activationId"));
        result.addProperty("fatalRegionInstanceId",
                string(targetActivation, "regionInstanceId"));
        result.addProperty("fatalQueryObjectSha256",
                sha256(GSON.toJson(fatal)));
        result.add("fatalLookup", lookup.toJson());
        JsonArray rows = new JsonArray();
        Set<String> ids = new LinkedHashSet<>();
        for (JsonObject witness : witnesses) {
            String id = string(witness, "witnessId");
            if (id.isEmpty() || !ids.add(id)) {
                throw gap("DUPLICATE_WITNESS_ID:" + id);
            }
            rows.add(witness.deepCopy());
        }
        result.add("witnesses", rows);
        result.addProperty("witnessCount", rows.size());
        return result;
    }

    private static JsonArray sourceArtifacts(Arguments arguments)
            throws IOException {
        JsonArray result = new JsonArray();
        result.add(artifact("COMPOSITION_MANIFEST",
                arguments.compositionManifest));
        result.add(artifact("COMPOSED_SMT", arguments.smt));
        result.add(artifact("ORIGINAL_SUMMARIES", arguments.summaries));
        result.add(artifact("PRODUCER_ACTIVATIONS", arguments.activations));
        result.add(artifact("TARGET_ACTIVATIONS",
                arguments.targetActivations));
        result.add(artifact("FATAL_QUERIES", arguments.fatalQueries));
        result.add(artifact("RUNTIME_EDGE_VALIDATION",
                arguments.runtimeEdges));
        return result;
    }

    private static JsonObject artifact(String role, Path path)
            throws IOException {
        JsonObject result = new JsonObject();
        result.addProperty("role", role);
        result.addProperty("path", path.toAbsolutePath().normalize()
                .toString());
        result.addProperty("sha256", sha256(path));
        return result;
    }

    private static List<JsonObject> enrichSummaries(
            List<JsonObject> summaries, List<JsonObject> witnesses,
            Arguments arguments) throws IOException {
        Map<String, List<JsonObject>> bySummary = new LinkedHashMap<>();
        for (JsonObject witness : witnesses) {
            if (!LOOKUP_WITNESS_KIND.equals(string(witness, "kind"))) {
                continue;
            }
            String id = string(witness, "sourceSummaryId");
            List<JsonObject> rows = bySummary.get(id);
            if (rows == null) {
                rows = new ArrayList<>();
                bySummary.put(id, rows);
            }
            rows.add(witness);
        }
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject source : summaries) {
            JsonObject copy = source.deepCopy();
            List<JsonObject> rows = bySummary.get(string(source,
                    "summaryId"));
            if (rows != null) {
                JsonArray embedded = new JsonArray();
                for (JsonObject witness : rows) embedded.add(
                        witness.deepCopy());
                copy.add("lookupKeyProducerWitnesses", embedded);
                copy.addProperty("producerWitnessSourceArtifactSha256",
                        sha256(arguments.runtimeEdges));
            }
            result.add(copy);
        }
        return result;
    }

    private static JsonObject catalog(Arguments arguments,
                                      List<Group> groups,
                                      JsonObject witnesses,
                                      int summaryCount) throws IOException {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 2);
        result.addProperty("kind", CATALOG_KIND);
        result.addProperty("complete", true);
        result.addProperty("roleSelectionIsDerived", true);
        result.addProperty("roleSelectionAuthority",
                "FATAL_RECEIVER_AND_COMPOSER_TERM_PROOF_WITH_RUNTIME_PATH");
        result.add("sourceArtifacts", sourceArtifacts(arguments));
        result.add("witnessSidecar", artifact("PRODUCER_WITNESSES",
                arguments.witnesses));
        result.add("enrichedSummaries", artifact("ENRICHED_SUMMARIES",
                arguments.enrichedSummaries));
        result.addProperty("enrichedSummaryCount", summaryCount);
        JsonArray rows = new JsonArray();
        for (Group group : groups) {
            JsonObject row = new JsonObject();
            row.addProperty("producerGroupId", "PRODUCER.GROUP."
                    + sha256(group.region + "\n" + group.role).substring(0,
                    16));
            row.addProperty("upstreamRegion", group.region);
            row.addProperty("upstreamActivations",
                    arguments.activations.toAbsolutePath().normalize()
                            .toString());
            row.addProperty("broadcastActivations",
                    arguments.activations.toAbsolutePath().normalize()
                            .toString());
            row.addProperty("expectedBroadcastCandidates",
                    group.expectedBound);
            row.addProperty("projectionRole", group.role);
            row.addProperty("projectionRoleDerived", true);
            row.addProperty("projectionRoleAuthority",
                    TARGET_MAP_STATE.equals(group.role)
                            ? TARGET_AUTHORITY : LOOKUP_AUTHORITY);
            JsonArray ids = new JsonArray();
            for (JsonObject witness : group.witnesses) {
                ids.add(string(witness, "witnessId"));
            }
            row.add("witnessIds", ids);
            row.addProperty("witnessCount", ids.size());
            // The projector selects the case-specific witness after the
            // selector model is known; no manually selected raw symbol lives
            // in the catalog row.
            rows.add(row);
        }
        result.add("producerGroups", rows);
        result.addProperty("producerGroupCount", rows.size());
        return result;
    }

    private static int boundedCandidateCount(List<JsonObject> rows,
                                             JsonObject source,
                                             JsonObject target,
                                             String region)
            throws IOException {
        int targetCall = integer(target, "rootCallId", -1);
        String root = firstNonBlank(string(source, "rootMethod"),
                string(source, "observedRootMethod"));
        String test = string(source, "test");
        JsonObject output = object(source, "requestedOutput");
        String port = string(output, "portId");
        String cell = string(output, "cell");
        if (targetCall < 1 || root.isEmpty() || test.isEmpty()
                || port.isEmpty() || cell.isEmpty()) {
            throw gap("ACTIVATION_BOUND_IDENTITY_INCOMPLETE:" + region);
        }
        Set<Integer> ordinals = new LinkedHashSet<>();
        boolean sourceIncluded = false;
        for (JsonObject row : rows) {
            if (!region.equals(string(row, "regionId"))
                    || !test.equals(string(row, "test"))
                    || !root.equals(firstNonBlank(string(row, "rootMethod"),
                    string(row, "observedRootMethod")))
                    || !bool(row, "upstreamEventObserved", false)
                    || !port.equals(string(object(row,
                    "requestedOutput"), "portId"))
                    || !cell.equals(string(object(row,
                    "requestedOutput"), "cell"))) continue;
            int call = integer(row, "rootCallId", -1);
            int ordinal = integer(row, "invocationOrdinal", -1);
            JsonObject event = object(row, "selectedUpstreamEvent");
            if (call < 1 || call >= targetCall || ordinal < 1
                    || integer(event, "rootCallId", -1) != call
                    || integer(event, "writerCallId", -1) != call) continue;
            if (!ordinals.add(ordinal)) {
                throw gap("AMBIGUOUS_BROADCAST_ORDINAL:" + region + ":"
                        + ordinal);
            }
            if (string(source, "regionInstanceId").equals(string(row,
                    "regionInstanceId"))) sourceIncluded = true;
        }
        if (ordinals.isEmpty() || !sourceIncluded) {
            throw gap("INCOMPLETE_BROADCAST_BOUND:" + region);
        }
        return ordinals.size();
    }

    private static JsonObject selectSummaryActivation(List<JsonObject> rows,
                                                       JsonObject summary,
                                                       String region)
            throws IOException {
        JsonObject selected = null;
        for (JsonObject row : rows) {
            if (!region.equals(string(row, "regionId"))) continue;
            boolean id = string(summary, "activationId").equals(string(row,
                    "activationId"));
            boolean instance = string(summary, "regionInstanceId").equals(
                    string(row, "regionInstanceId"));
            if (!id && !instance) continue;
            if (selected != null) throw gap("AMBIGUOUS_SUMMARY_ACTIVATION:"
                    + string(summary, "summaryId"));
            selected = row;
        }
        if (selected == null) throw gap("MISSING_SUMMARY_ACTIVATION:"
                + string(summary, "summaryId"));
        if (!string(summary, "activationId").equals(string(selected,
                "activationId")) || !string(summary,
                "regionInstanceId").equals(string(selected,
                "regionInstanceId"))) {
            throw gap("SUMMARY_ACTIVATION_NOT_EXACT:"
                    + string(summary, "summaryId"));
        }
        return selected;
    }

    private static JsonObject selectActivation(List<JsonObject> rows,
                                               String region, String id,
                                               String label)
            throws IOException {
        JsonObject selected = null;
        for (JsonObject row : rows) {
            if (!region.equals(string(row, "regionId"))) continue;
            if (!id.isEmpty() && !id.equals(string(row,
                    "activationId"))) continue;
            if (selected != null) throw gap("AMBIGUOUS_" + label
                    .toUpperCase() + "_ACTIVATION");
            selected = row;
        }
        if (selected == null) throw gap("MISSING_" + label.toUpperCase()
                + "_ACTIVATION:" + region + ":" + id);
        if (string(selected, "regionInstanceId").isEmpty()) {
            throw gap("TARGET_ACTIVATION_INSTANCE_MISSING");
        }
        return selected;
    }

    private static JsonObject selectFatal(List<JsonObject> rows,
                                          JsonObject target, String region)
            throws IOException {
        JsonObject selected = null;
        for (JsonObject row : rows) {
            if (!region.equals(string(row, "regionId"))
                    || !string(target, "activationId").equals(string(row,
                    "activationId"))
                    || !string(target, "regionInstanceId").equals(string(row,
                    "regionInstanceId"))
                    || !bool(row, "readyForSolver", false)) continue;
            if (selected != null) throw gap("AMBIGUOUS_FATAL_QUERY");
            selected = row;
        }
        if (selected == null) throw gap("MISSING_EXACT_FATAL_QUERY");
        return selected;
    }

    private static void requireCompleteSummary(JsonObject summary,
                                               String region, String id)
            throws IOException {
        if (summary == null || !region.equals(string(summary, "regionId"))
                || !bool(summary, "valid", false)
                || !bool(summary, "relationallyComplete", false)
                || string(summary, "activationId").isEmpty()
                || string(summary, "regionInstanceId").isEmpty()) {
            throw gap("INCOMPLETE_SELECTED_SUMMARY:" + id);
        }
    }

    /** Revalidates a schema-2 catalog from original artifacts. */
    static VerifiedCatalog verifyCatalog(Path catalogPath,
                                         Path compositionPath,
                                         Path smtPath,
                                         Path summariesPath,
                                         Path targetActivationsPath,
                                         Path fatalQueriesPath,
                                         Path runtimeEdgesPath,
                                         Path z3,
                                         long timeoutMillis)
            throws Exception {
        JsonObject catalog = readJson(catalogPath);
        if (integer(catalog, "schemaVersion", -1) != 2
                || !CATALOG_KIND.equals(string(catalog, "kind"))
                || !bool(catalog, "complete", false)
                || !bool(catalog, "roleSelectionIsDerived", false)) {
            throw gap("INCOMPLETE_SCHEMA2_PRODUCER_CATALOG");
        }
        Map<String, JsonObject> artifacts = verifyArtifactCatalog(
                array(catalog, "sourceArtifacts"));
        requireArtifact(artifacts, "COMPOSITION_MANIFEST", compositionPath);
        requireArtifact(artifacts, "COMPOSED_SMT", smtPath);
        requireArtifact(artifacts, "TARGET_ACTIVATIONS",
                targetActivationsPath);
        requireArtifact(artifacts, "FATAL_QUERIES", fatalQueriesPath);
        requireArtifact(artifacts, "RUNTIME_EDGE_VALIDATION",
                runtimeEdgesPath);
        JsonObject enrichedArtifact = object(catalog,
                "enrichedSummaries");
        if (!"ENRICHED_SUMMARIES".equals(string(enrichedArtifact, "role"))
                || !samePath(summariesPath, Paths.get(string(
                enrichedArtifact, "path")))
                || !sha256(summariesPath).equals(string(enrichedArtifact,
                "sha256"))) {
            throw gap("ENRICHED_SUMMARIES_HASH_MISMATCH");
        }
        JsonObject sidecarArtifact = object(catalog, "witnessSidecar");
        Path sidecarPath = Paths.get(string(sidecarArtifact, "path"));
        if (!"PRODUCER_WITNESSES".equals(string(sidecarArtifact, "role"))
                || !Files.isRegularFile(sidecarPath)
                || !sha256(sidecarPath).equals(string(sidecarArtifact,
                "sha256"))) {
            throw gap("WITNESS_SIDECAR_HASH_MISMATCH");
        }
        JsonObject sidecar = readJson(sidecarPath);
        if (integer(sidecar, "schemaVersion", -1) != 2
                || !WITNESS_KIND.equals(string(sidecar, "kind"))
                || !bool(sidecar, "complete", false)
                || integer(sidecar, "witnessCount", -1)
                != array(sidecar, "witnesses").size()) {
            throw gap("INCOMPLETE_WITNESS_SIDECAR");
        }
        Map<String, JsonObject> sideArtifacts = verifyArtifactCatalog(
                array(sidecar, "sourceArtifacts"));
        if (!artifactMapsEqual(artifacts, sideArtifacts)) {
            throw gap("CATALOG_SIDECAR_SOURCE_ARTIFACT_MISMATCH");
        }
        JsonObject composition = readJson(compositionPath);
        String smt = new String(Files.readAllBytes(smtPath),
                StandardCharsets.UTF_8);
        List<JsonObject> summaries = readJsonl(summariesPath);
        Map<String, JsonObject> summariesById = new LinkedHashMap<>();
        for (JsonObject summary : summaries) {
            summariesById.put(string(summary, "summaryId"), summary);
        }
        List<JsonObject> verifiedRuntimeRows = readJsonl(runtimeEdgesPath);
        JsonObject verifiedTarget = selectActivation(readJsonl(
                targetActivationsPath), string(sidecar, "fatalRegion"),
                string(sidecar, "fatalActivationId"), "target");
        JsonObject verifiedFatal = selectFatal(readJsonl(fatalQueriesPath),
                verifiedTarget, string(sidecar, "fatalRegion"));
        RuntimeEdgeIndex runtime = RuntimeEdgeIndex.build(
                verifiedRuntimeRows, sha256(runtimeEdgesPath),
                ExecutionScope.from(verifiedTarget, verifiedRuntimeRows,
                        sha256(runtimeEdgesPath)));
        Map<String, JsonObject> cases = new LinkedHashMap<>();
        for (JsonElement element : array(composition,
                "caseProjectionCatalog")) {
            if (element.isJsonObject()) cases.put(string(
                    element.getAsJsonObject(), "caseId"),
                    element.getAsJsonObject());
        }
        Map<String, JsonObject> witnesses = new LinkedHashMap<>();
        for (JsonElement element : array(sidecar, "witnesses")) {
            if (!element.isJsonObject()) throw gap("NON_OBJECT_WITNESS");
            JsonObject witness = element.getAsJsonObject();
            verifyWitness(witness, cases, summariesById, runtime, smt, z3,
                    timeoutMillis, sidecar, verifiedFatal);
            String id = string(witness, "witnessId");
            if (id.isEmpty() || witnesses.put(id, witness) != null) {
                throw gap("DUPLICATE_WITNESS_ID:" + id);
            }
        }
        verifyGroupRows(catalog, witnesses);
        return new VerifiedCatalog(catalog, witnesses);
    }

    static List<String> validateExecutionBindingsForTests(
            JsonObject target, List<JsonObject> runtimeRows, String sha)
            throws IOException {
        ExecutionScope scope = ExecutionScope.from(target, runtimeRows, sha);
        List<String> result = new ArrayList<>();
        for (JsonObject edge : runtimeRows) {
            for (JsonElement element : array(edge, "validatedBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                result.add(scope.validate(edge, binding,
                        string(edge, "edgeId"), string(binding, "test")));
            }
        }
        return result;
    }

    private static void verifyWitness(JsonObject witness,
                                      Map<String, JsonObject> cases,
                                      Map<String, JsonObject> summaries,
                                      RuntimeEdgeIndex runtime, String smt,
                                      Path z3, long timeoutMillis,
                                      JsonObject sidecar, JsonObject fatal)
            throws Exception {
        String kind = string(witness, "kind");
        if (integer(witness, "schemaVersion", -1) != 2
                || !bool(witness, "complete", false)
                || !(LOOKUP_WITNESS_KIND.equals(kind)
                || TARGET_WITNESS_KIND.equals(kind))) {
            throw gap("INCOMPLETE_PRODUCER_WITNESS");
        }
        JsonObject pathCase = cases.get(string(witness,
                "compositionCaseId"));
        JsonObject summary = summaries.get(string(witness,
                "sourceSummaryId"));
        if (pathCase == null || summary == null
                || !sha256(GSON.toJson(pathCase)).equals(string(witness,
                "compositionCaseObjectSha256"))
                || !string(pathCase, "sourceSummaryId").equals(string(
                witness, "sourceSummaryId"))
                || !string(summary, "regionId").equals(string(witness,
                "producerRegion"))
                || !string(summary, "regionInstanceId").equals(string(
                witness, "producerRegionInstanceId"))
                || !string(summary, "activationId").equals(string(witness,
                "producerActivationId"))) {
            throw gap("WITNESS_CASE_SUMMARY_INSTANCE_MISMATCH");
        }
        JsonObject originalSummary = summary.deepCopy();
        originalSummary.remove("lookupKeyProducerWitnesses");
        originalSummary.remove("producerWitnessSourceArtifactSha256");
        if (!sha256(GSON.toJson(originalSummary)).equals(string(witness,
                "sourceSummaryObjectSha256"))) {
            throw gap("WITNESS_SUMMARY_OBJECT_HASH_MISMATCH");
        }
        JsonArray path = array(witness, "runtimeProvenancePath");
        if (path.isEmpty() || integer(witness,
                "runtimeProvenancePathLength", -1) != path.size()) {
            throw gap("INCOMPLETE_RUNTIME_PROVENANCE_PATH");
        }
        String expectedFrom = string(witness,
                "producerRegionInstanceId");
        String execution = "";
        for (JsonElement element : path) {
            if (!element.isJsonObject()) throw gap("NON_OBJECT_PATH_EDGE");
            JsonObject edge = element.getAsJsonObject();
            verifyComposerAdmission(edge, cases, summaries, fatal, runtime);
            if (!new AdmittedEdge(edge).admittedForCase(string(witness,
                    "compositionCaseId"))) {
                throw gap("EDGE_NOT_ADMITTED_FOR_WITNESSED_COMPOSER_CASE");
            }
            AdmittedEdge verified = runtime.revalidateNormalized(edge);
            if (!expectedFrom.equals(verified.fromInstance())) {
                throw gap("DISCONNECTED_RUNTIME_PROVENANCE_PATH");
            }
            expectedFrom = verified.toInstance();
            String current = string(verified.json, "executionIdentity");
            if (execution.isEmpty()) execution = current;
            if (!execution.equals(current)) {
                throw gap("CROSS_EXECUTION_RUNTIME_PROVENANCE_PATH");
            }
        }
        if (!string(witness, "targetRegionInstanceId").equals(expectedFrom)) {
            throw gap("RUNTIME_PATH_DOES_NOT_REACH_FATAL_INSTANCE");
        }
        if (TARGET_WITNESS_KIND.equals(kind)) {
            if (path.size() != 1 || !"READ_FROM".equals(string(
                    path.get(0).getAsJsonObject(), "relation"))
                    || !string(witness, "targetMapInput").equals(string(
                    path.get(0).getAsJsonObject(), "toPort"))
                    || !string(witness, "targetMapCell").equals(string(
                    path.get(0).getAsJsonObject(), "toCell"))) {
                throw gap("TARGET_STATE_WITNESS_NOT_EXACT_RECEIVER_READ_FROM");
            }
            return;
        }
        if (!LOOKUP_AUTHORITY.equals(string(witness, "authority"))
                || !bool(witness, "runtimeConfirmed", false)
                || !bool(witness, "valueEqualityConfirmed", false)
                || !bool(witness, "fingerprintTransitiveJoinForbidden",
                false)) {
            throw gap("LOOKUP_WITNESS_AUTHORITY_INCOMPLETE");
        }
        String raw = string(witness, "rawEngineSymbol");
        String effectId = string(witness, "summaryEffectId");
        int effectMatches = 0;
        for (EffectTerm term : effectTerms(pathCase, summary)) {
            if (raw.equals(term.raw) && effectId.equals(term.effectId)
                    && string(witness, "producerSolverTerm").equals(
                    term.solverTerm)) effectMatches++;
        }
        if (effectMatches != 1) {
            throw gap("LOOKUP_WITNESS_EFFECT_NOT_EXACT:" + effectMatches);
        }
        JsonObject proof = object(witness, "symbolicEqualityProof");
        EqualityProof rerun = proveEquality(smt,
                string(pathCase, "selectorSolverSymbol"),
                string(witness, "producerSolverTerm"),
                string(witness, "targetLookupSolverTerm"), z3,
                timeoutMillis);
        if (!rerun.feasible || !rerun.implied
                || !"unsat".equals(string(proof,
                "negatedEqualityStatus"))
                || !rerun.proofInputSha256.equals(string(proof,
                "proofInputSha256"))) {
            throw gap("LOOKUP_SYMBOLIC_EQUALITY_PROOF_NOT_REPRODUCIBLE");
        }
        JsonArray embedded = array(summary, "lookupKeyProducerWitnesses");
        int embeddedMatches = 0;
        for (JsonElement element : embedded) {
            if (element.isJsonObject() && string(witness,
                    "witnessId").equals(string(element.getAsJsonObject(),
                    "witnessId")) && GSON.toJson(witness).equals(
                    GSON.toJson(element))) embeddedMatches++;
        }
        if (embeddedMatches != 1) {
            throw gap("LOOKUP_WITNESS_NOT_EXACTLY_EMBEDDED");
        }
    }

    private static void verifyComposerAdmission(JsonObject edge,
                                                Map<String, JsonObject> cases,
                                                Map<String, JsonObject> summaries,
                                                JsonObject fatal,
                                                RuntimeEdgeIndex runtime)
            throws IOException {
        JsonArray admissions = array(edge, "composerAdmissions");
        if (admissions.isEmpty()) throw gap("MISSING_COMPOSER_ADMISSION");
        Set<String> unique = new LinkedHashSet<>();
        for (JsonElement element : admissions) {
            if (!element.isJsonObject()
                    || !unique.add(GSON.toJson(element))) {
                throw gap("NON_OBJECT_OR_DUPLICATE_COMPOSER_ADMISSION");
            }
            verifyOneComposerAdmission(element.getAsJsonObject(), cases,
                    summaries, fatal, runtime, edge);
        }
    }

    private static void verifyOneComposerAdmission(JsonObject admission,
            Map<String, JsonObject> cases,
            Map<String, JsonObject> summaries, JsonObject fatal,
            RuntimeEdgeIndex runtime, JsonObject normalizedEdge)
            throws IOException {
        String kind = string(admission, "kind");
        String objectSha = string(admission,
                "selectedBindingObjectSha256");
        int matches = 0;
        JsonObject matchedBinding = null;
        JsonObject matchedRelation = null;
        if ("SELECTED_CASE_SUMMARY_EDGE_BINDING".equals(kind)) {
            JsonObject pathCase = cases.get(string(admission, "caseId"));
            JsonObject summary = summaries.get(string(admission,
                    "sourceSummaryId"));
            if (pathCase == null || summary == null
                    || !string(pathCase, "sourceSummaryId").equals(string(
                    summary, "summaryId"))
                    || !string(pathCase, "selectorSolverSymbol").equals(
                    string(admission, "caseSelectorSolverTerm"))) {
                throw gap("COMPOSER_SUMMARY_ADMISSION_IDENTITY_MISMATCH");
            }
            for (JsonElement element : array(summary, "edgeBindings")) {
                if (element.isJsonObject()
                        && objectSha.equals(sha256(GSON.toJson(element)))) {
                    matches++;
                    matchedBinding = element.getAsJsonObject();
                }
            }
        } else if ("FATAL_SYMBOLIC_CONTEXT_SELECTED_BINDING".equals(kind)) {
            String relationSha = string(admission,
                    "relationObjectSha256");
            JsonObject context = object(fatal, "symbolicContext");
            List<JsonObject> relations = new ArrayList<>();
            for (String member : new String[]{"equalityRelations",
                    "versionedStateMerges"}) {
                for (JsonElement element : array(context, member)) {
                    if (element.isJsonObject()) relations.add(
                            element.getAsJsonObject());
                }
            }
            for (JsonElement groupElement : array(context,
                    "alternativeWriterGroups")) {
                if (!groupElement.isJsonObject()) continue;
                for (JsonElement alternative : array(
                        groupElement.getAsJsonObject(), "alternatives")) {
                    if (alternative.isJsonObject()) relations.add(
                            alternative.getAsJsonObject());
                }
            }
            for (JsonObject relation : relations) {
                if (!relationSha.equals(sha256(GSON.toJson(relation)))) {
                    continue;
                }
                for (JsonElement binding : array(relation,
                        "selectedBindings")) {
                    if (binding.isJsonObject() && objectSha.equals(
                            sha256(GSON.toJson(binding)))) {
                        matches++;
                        matchedBinding = binding.getAsJsonObject();
                        matchedRelation = relation;
                    }
                }
            }
        } else {
            throw gap("UNTRUSTED_COMPOSER_ADMISSION_KIND:" + kind);
        }
        if (matches != 1) {
            throw gap("COMPOSER_SELECTED_BINDING_MATCH_COUNT:" + matches);
        }
        AdmittedEdge rebound = "SELECTED_CASE_SUMMARY_EDGE_BINDING".equals(
                kind) ? runtime.validateSummaryBinding(matchedBinding)
                : runtime.validateContextBinding(matchedRelation,
                matchedBinding);
        JsonObject expectedCore = normalizedEdge.deepCopy();
        expectedCore.remove("composerAdmissions");
        if (!GSON.toJson(expectedCore).equals(GSON.toJson(rebound.json))) {
            throw gap("COMPOSER_SELECTED_BINDING_DOES_NOT_DESCRIBE_RUNTIME_"
                    + "EDGE:" + string(normalizedEdge, "edgeId"));
        }
    }

    private static void verifyGroupRows(JsonObject catalog,
                                        Map<String, JsonObject> witnesses)
            throws IOException {
        JsonArray groups = array(catalog, "producerGroups");
        if (groups.isEmpty() || integer(catalog, "producerGroupCount", -1)
                != groups.size()) throw gap("INCOMPLETE_PRODUCER_GROUP_ROWS");
        int target = 0;
        int lookup = 0;
        Set<String> regions = new LinkedHashSet<>();
        Set<String> usedWitnesses = new LinkedHashSet<>();
        for (JsonElement element : groups) {
            if (!element.isJsonObject()) throw gap("NON_OBJECT_GROUP_ROW");
            JsonObject group = element.getAsJsonObject();
            String role = string(group, "projectionRole");
            String region = string(group, "upstreamRegion");
            if (region.isEmpty() || !regions.add(region)
                    || !bool(group, "projectionRoleDerived", false)
                    || integer(group, "expectedBroadcastCandidates", -1) < 1
                    || integer(group, "witnessCount", -1)
                    != array(group, "witnessIds").size()) {
                throw gap("INCOMPLETE_OR_DUPLICATE_GROUP_ROW:" + region);
            }
            if (TARGET_MAP_STATE.equals(role)) target++;
            else if (LOOKUP_KEY_PRODUCER.equals(role)) lookup++;
            else throw gap("UNKNOWN_DERIVED_GROUP_ROLE:" + role);
            for (String id : strings(array(group, "witnessIds"))) {
                JsonObject witness = witnesses.get(id);
                String expectedKind = TARGET_MAP_STATE.equals(role)
                        ? TARGET_WITNESS_KIND : LOOKUP_WITNESS_KIND;
                if (witness == null || !expectedKind.equals(string(witness,
                        "kind")) || !region.equals(string(witness,
                        "producerRegion")) || !usedWitnesses.add(id)) {
                    throw gap("GROUP_WITNESS_ROLE_OR_REGION_MISMATCH:" + id);
                }
            }
        }
        if (target != 1 || lookup < 1
                || usedWitnesses.size() != witnesses.size()) {
            throw gap("VERIFIED_ROLE_CARDINALITY_OR_UNUSED_WITNESS:target="
                    + target + ":lookup=" + lookup);
        }
    }

    private static Map<String, JsonObject> verifyArtifactCatalog(
            JsonArray artifacts) throws IOException {
        Map<String, JsonObject> result = new LinkedHashMap<>();
        for (JsonElement element : artifacts) {
            if (!element.isJsonObject()) throw gap("NON_OBJECT_ARTIFACT");
            JsonObject artifact = element.getAsJsonObject();
            String role = string(artifact, "role");
            String path = string(artifact, "path");
            if (role.isEmpty() || path.isEmpty()
                    || result.put(role, artifact) != null
                    || !Files.isRegularFile(Paths.get(path))
                    || !sha256(Paths.get(path)).equals(string(artifact,
                    "sha256"))) {
                throw gap("ARTIFACT_HASH_OR_IDENTITY_MISMATCH:" + role);
            }
        }
        return result;
    }

    private static void requireArtifact(Map<String, JsonObject> artifacts,
                                        String role, Path actual)
            throws IOException {
        JsonObject artifact = artifacts.get(role);
        if (artifact == null || !samePath(actual, Paths.get(string(artifact,
                "path"))) || !sha256(actual).equals(string(artifact,
                "sha256"))) {
            throw gap("REQUIRED_ARTIFACT_MISMATCH:" + role);
        }
    }

    private static boolean artifactMapsEqual(Map<String, JsonObject> left,
                                             Map<String, JsonObject> right) {
        return left.keySet().equals(right.keySet())
                && GSON.toJson(left).equals(GSON.toJson(right));
    }

    private static boolean samePath(Path left, Path right) {
        return left.toAbsolutePath().normalize().equals(
                right.toAbsolutePath().normalize());
    }

    private static SolverOutput run(Path executable, String input,
                                    long timeoutMillis)
            throws IOException, InterruptedException {
        Process process = new ProcessBuilder(executable.toString(), "-in",
                "-smt2").start();
        try (OutputStream stream = process.getOutputStream()) {
            stream.write(input.getBytes(StandardCharsets.UTF_8));
        }
        boolean finished = process.waitFor(Math.max(1L, timeoutMillis),
                TimeUnit.MILLISECONDS);
        if (!finished) {
            process.destroyForcibly();
            process.waitFor();
        }
        return new SolverOutput(finished ? process.exitValue() : -1,
                !finished, readAll(process.getInputStream()),
                readAll(process.getErrorStream()));
    }

    private static void requireSolver(SolverOutput output, String phase)
            throws IOException {
        if (output.timedOut) throw gap("Z3_TIMEOUT:" + phase);
        String status = firstLine(output.stdout);
        if (output.exitCode != 0 && !("sat".equals(status)
                || "unsat".equals(status) || "unknown".equals(status))) {
            throw gap("Z3_FAILED:" + phase + ":" + output.stderr.trim());
        }
    }

    private static String readAll(InputStream input) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[4096];
        int count;
        while ((count = input.read(buffer)) >= 0) {
            output.write(buffer, 0, count);
        }
        return new String(output.toByteArray(), StandardCharsets.UTF_8);
    }

    private static String firstLine(String value) {
        String normalized = firstNonBlank(value);
        int newline = normalized.indexOf('\n');
        return newline < 0 ? normalized : normalized.substring(0, newline)
                .trim();
    }

    private static JsonObject readJson(Path path) throws IOException {
        JsonElement parsed = new JsonParser().parse(new String(
                Files.readAllBytes(path), StandardCharsets.UTF_8));
        if (!parsed.isJsonObject()) throw gap("EXPECTED_JSON_OBJECT:" + path);
        return parsed.getAsJsonObject();
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        List<JsonObject> result = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                JsonElement parsed = new JsonParser().parse(line);
                if (!parsed.isJsonObject()) throw gap(
                        "EXPECTED_JSONL_OBJECT:" + path);
                result.add(parsed.getAsJsonObject());
            }
        }
        return result;
    }

    private static void writeJsonl(Path path, List<JsonObject> rows)
            throws IOException {
        StringBuilder value = new StringBuilder();
        for (JsonObject row : rows) value.append(GSON.toJson(row)).append('\n');
        write(path, value.toString());
    }

    private static void write(Path path, String value) throws IOException {
        Path parent = path.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        Files.write(path, value.getBytes(StandardCharsets.UTF_8));
    }

    private static void require(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)
                || Files.size(path) == 0) {
            throw new IOException("Missing or empty " + label + ": " + path);
        }
    }

    private static void requireFreshOutputs(Path... outputs)
            throws IOException {
        Set<Path> unique = new LinkedHashSet<>();
        for (Path output : outputs) {
            if (output == null) throw gap("OUTPUT_PATH_MISSING");
            Path normalized = output.toAbsolutePath().normalize();
            if (!unique.add(normalized)) {
                throw gap("OUTPUT_PATHS_NOT_DISTINCT:" + normalized);
            }
            if (Files.exists(normalized)) {
                throw gap("OUTPUT_ALREADY_EXISTS:" + normalized);
            }
        }
    }

    private static String sha256(Path path) throws IOException {
        return sha256(Files.readAllBytes(path));
    }

    private static String sha256(String value) {
        return sha256(firstNonBlank(value).getBytes(StandardCharsets.UTF_8));
    }

    private static String sha256(byte[] bytes) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] hashed = digest.digest(bytes);
            StringBuilder result = new StringBuilder();
            for (byte item : hashed) result.append(String.format("%02x",
                    item & 0xff));
            return result.toString();
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException(impossible);
        }
    }

    private static IOException gap(String reason) {
        return new IOException("PRODUCER_GROUP_PLANNING_GAP: " + reason);
    }

    private static String expressionSymbol(JsonElement value) {
        return value != null && value.isJsonObject()
                ? string(value.getAsJsonObject(), "_exp") : "";
    }

    private static String string(JsonObject object, String member) {
        if (object == null || !object.has(member)
                || object.get(member).isJsonNull()
                || !object.get(member).isJsonPrimitive()) return "";
        try {
            return object.get(member).getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static int integer(JsonObject object, String member,
                               int fallback) {
        try {
            return object != null && object.has(member)
                    ? object.get(member).getAsInt() : fallback;
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longInteger(JsonObject object, String member,
                                    long fallback) {
        try {
            return object != null && object.has(member)
                    ? object.get(member).getAsLong() : fallback;
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static boolean bool(JsonObject object, String member,
                                boolean fallback) {
        try {
            return object != null && object.has(member)
                    ? object.get(member).getAsBoolean() : fallback;
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static JsonArray array(JsonObject object, String member) {
        return object != null && object.has(member)
                && object.get(member).isJsonArray()
                ? object.getAsJsonArray(member) : new JsonArray();
    }

    private static JsonObject object(JsonObject object, String member) {
        return object != null && object.has(member)
                && object.get(member).isJsonObject()
                ? object.getAsJsonObject(member) : new JsonObject();
    }

    private static List<String> strings(JsonArray values) {
        List<String> result = new ArrayList<>();
        for (JsonElement value : values) {
            if (value.isJsonPrimitive()) result.add(value.getAsString());
        }
        return result;
    }

    private static String firstNonBlank(String... values) {
        if (values == null) return "";
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) return value.trim();
        }
        return "";
    }

    static final class Arguments {
        private Path compositionManifest;
        private Path smt;
        private Path summaries;
        private Path activations;
        private Path targetActivations;
        private Path fatalQueries;
        private Path runtimeEdges;
        private Path z3 = Paths.get("z3");
        private Path catalog;
        private Path witnesses;
        private Path enrichedSummaries;
        private String targetActivationId = "";
        private long timeoutMillis = 30000L;

        static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; index < argv.length; index += 2) {
                if (!argv[index].startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException("Expected --key value");
                }
                String key = argv[index].substring(2);
                if (values.put(key, argv[index + 1]) != null) {
                    throw new IllegalArgumentException("Duplicate --" + key);
                }
            }
            Arguments result = new Arguments();
            result.compositionManifest = path(values,
                    "composition-manifest", true);
            result.smt = path(values, "smt", true);
            result.summaries = path(values, "summaries", true);
            result.activations = path(values, "activations", true);
            result.targetActivations = path(values,
                    "target-activations", true);
            result.fatalQueries = path(values, "fatal-query", true);
            result.runtimeEdges = path(values, "runtime-edges", true);
            if (values.containsKey("z3")) result.z3 = path(values, "z3",
                    true);
            result.catalog = path(values, "output-catalog", true);
            result.witnesses = path(values, "output-witnesses", true);
            result.enrichedSummaries = path(values,
                    "output-summaries", true);
            result.targetActivationId = firstNonBlank(values.get(
                    "target-activation-id"));
            if (values.containsKey("timeout-ms")) {
                result.timeoutMillis = Long.parseLong(values.get(
                        "timeout-ms"));
            }
            return result;
        }

        private static Path path(Map<String, String> values, String key,
                                 boolean required) {
            String value = values.get(key);
            if ((value == null || value.trim().isEmpty()) && required) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return value == null || value.trim().isEmpty()
                    ? null : Paths.get(value);
        }
    }

    static final class Result {
        final JsonObject catalog;
        final JsonObject witnesses;
        final List<JsonObject> enrichedSummaries;

        Result(JsonObject catalog, JsonObject witnesses,
               List<JsonObject> enrichedSummaries) {
            this.catalog = catalog;
            this.witnesses = witnesses;
            this.enrichedSummaries = enrichedSummaries;
        }
    }

    static final class VerifiedCatalog {
        final JsonObject catalog;
        final Map<String, JsonObject> witnesses;

        VerifiedCatalog(JsonObject catalog,
                        Map<String, JsonObject> witnesses) {
            this.catalog = catalog;
            this.witnesses = witnesses;
        }
    }

    private static final class Group {
        private final String region;
        private final String role;
        private final int expectedBound;
        private final List<JsonObject> witnesses;

        private Group(String region, String role, Integer expectedBound,
                      List<JsonObject> witnesses) {
            this.region = region;
            this.role = role;
            this.expectedBound = expectedBound == null ? -1 : expectedBound;
            this.witnesses = witnesses;
        }
    }

    private static final class EffectTerm {
        private final String effectId;
        private final String raw;
        private final String solverTerm;
        private EqualityProof proof;

        private EffectTerm(String effectId, String raw, String solverTerm) {
            this.effectId = effectId;
            this.raw = raw;
            this.solverTerm = solverTerm;
        }
    }

    private static final class EqualityProof {
        private final boolean feasible;
        private final boolean implied;
        private final String selector;
        private final String producer;
        private final String target;
        private final String feasibilityStatus;
        private final String proofStatus;
        private final String feasibilityInputSha256;
        private final String proofInputSha256;

        private EqualityProof(boolean feasible, boolean implied,
                              String selector, String producer, String target,
                              String feasibilityStatus, String proofStatus,
                              String feasibleInput, String proofInput) {
            this.feasible = feasible;
            this.implied = implied;
            this.selector = selector;
            this.producer = producer;
            this.target = target;
            this.feasibilityStatus = feasibilityStatus;
            this.proofStatus = proofStatus;
            this.feasibilityInputSha256 = sha256(feasibleInput);
            this.proofInputSha256 = sha256(proofInput);
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("kind",
                    "COMPOSER_EXACT_TERM_EQUALITY_IMPLICATION");
            result.addProperty("complete", feasible && implied);
            result.addProperty("caseSelectorSolverTerm", selector);
            result.addProperty("producerSolverTerm", producer);
            result.addProperty("targetLookupSolverTerm", target);
            result.addProperty("caseFeasibilityStatus", feasibilityStatus);
            result.addProperty("negatedEqualityStatus", proofStatus);
            result.addProperty("feasibilityInputSha256",
                    feasibilityInputSha256);
            result.addProperty("proofInputSha256", proofInputSha256);
            result.addProperty("authority",
                    "Z3_UNSAT_NEGATED_EQUALITY_OVER_EXACT_COMPOSED_SMT_CASE");
            return result;
        }
    }

    private static final class FatalLookup {
        private final String region;
        private final String instance;
        private final String activationId;
        private final String receiverPort;
        private final String receiverCell;
        private final String rawKey;
        private final String solverTerm;

        private FatalLookup(String region, String instance,
                            String activationId, String receiverPort,
                            String receiverCell, String rawKey,
                            String solverTerm) {
            this.region = region;
            this.instance = instance;
            this.activationId = activationId;
            this.receiverPort = receiverPort;
            this.receiverCell = receiverCell;
            this.rawKey = rawKey;
            this.solverTerm = solverTerm;
        }

        private static FatalLookup resolve(JsonObject fatal,
                                           JsonObject activation, String smt)
                throws IOException {
            Map<String, String> receiverToKey = new LinkedHashMap<>();
            collectLookups(fatal.get("constraints"), receiverToKey);
            if (receiverToKey.size() != 1) {
                throw gap("EXPECTED_ONE_FATAL_MAP_LOOKUP:"
                        + receiverToKey.keySet());
            }
            String receiver = receiverToKey.keySet().iterator().next();
            Set<String> cells = new LinkedHashSet<>();
            JsonArray actions = array(activation, "materializations");
            if (actions.isEmpty()) actions = array(activation, "symbolize");
            for (JsonElement element : actions) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                if (!receiver.equals(string(action, "symbol"))) continue;
                String cell = string(action, "cell");
                Matcher matcher = DECLARED_FIELD.matcher(cell);
                if (matcher.matches()
                        && "java.util.Map".equals(matcher.group(2).trim())) {
                    cells.add(cell);
                }
            }
            if (cells.size() != 1) {
                throw gap("EXPECTED_ONE_FATAL_MAP_RECEIVER_CELL:" + cells);
            }
            String solver = ConcolicComposedModelProjector
                    .actualTargetLookupTerm(smt, receiver);
            return new FatalLookup(string(fatal, "regionId"),
                    string(fatal, "regionInstanceId"),
                    string(fatal, "activationId"), receiver,
                    cells.iterator().next(), receiverToKey.get(receiver),
                    solver);
        }

        private static void collectLookups(JsonElement element,
                                           Map<String, String> result)
                throws IOException {
            if (element == null || element.isJsonNull()) return;
            if (element.isJsonArray()) {
                for (JsonElement child : element.getAsJsonArray()) {
                    collectLookups(child, result);
                }
                return;
            }
            if (!element.isJsonObject()) return;
            JsonObject object = element.getAsJsonObject();
            if ("MethodExpression".equals(string(object, "_type"))
                    && string(object, "_name").endsWith("HashMap get")) {
                JsonArray parameters = array(object, "_param_list");
                if (parameters.size() >= 2) {
                    Matcher matcher = REGION_INPUT.matcher(expressionSymbol(
                            parameters.get(0)));
                    Set<String> ports = new LinkedHashSet<>();
                    while (matcher.find()) ports.add(matcher.group());
                    if (ports.size() == 1) {
                        String port = ports.iterator().next();
                        String old = result.put(port, expressionSymbol(
                                parameters.get(1)));
                        if (old != null) throw gap(
                                "DUPLICATE_FATAL_LOOKUP_RECEIVER:" + port);
                    }
                }
            }
            for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
                collectLookups(entry.getValue(), result);
            }
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("regionId", region);
            result.addProperty("regionInstanceId", instance);
            result.addProperty("activationId", activationId);
            result.addProperty("receiverPort", receiverPort);
            result.addProperty("receiverCell", receiverCell);
            result.addProperty("lookupKeyRawEngineSymbol", rawKey);
            result.addProperty("lookupKeySolverTerm", solverTerm);
            result.addProperty("authority",
                    "EXACT_FATAL_HASHMAP_GET_RECEIVER_AND_EMITTED_MAP_TERM");
            return result;
        }
    }

    private static final class ExecutionScope {
        private final String kind;
        private final String expectedExecutionId;
        private final String artifactSha;

        private ExecutionScope(String kind, String expectedExecutionId,
                               String artifactSha) {
            this.kind = kind;
            this.expectedExecutionId = expectedExecutionId;
            this.artifactSha = artifactSha;
        }

        private static ExecutionScope from(JsonObject target,
                                           List<JsonObject> runtimeRows,
                                           String artifactSha)
                throws IOException {
            String targetExecution = firstNonBlank(string(target,
                    "postDiscoveryTargetExecutionId"), string(target,
                    "discoveredExecutionId"));
            boolean discovered = false;
            for (JsonObject edge : runtimeRows) {
                if (!string(edge, "discoveredExecutionId").isEmpty()
                        || !array(edge, "discoveredExecutionIds").isEmpty()) {
                    discovered = true;
                    break;
                }
                for (JsonElement element : array(edge,
                        "validatedBindings")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject binding = element.getAsJsonObject();
                    if (!bindingExecution(binding).isEmpty()) {
                        discovered = true;
                        break;
                    }
                }
            }
            if (!targetExecution.isEmpty()) {
                return new ExecutionScope("CAMPAIGN_DISCOVERED_EXECUTION",
                        targetExecution, artifactSha);
            }
            if (discovered) {
                throw gap("TARGET_EXECUTION_ID_MISSING_FOR_DISCOVERED_EDGE_"
                        + "ARTIFACT");
            }
            return new ExecutionScope("IMMUTABLE_BASELINE_ARTIFACT", "",
                    artifactSha);
        }

        private String validate(JsonObject edge, JsonObject binding,
                                String edgeId, String test)
                throws IOException {
            String bindingExecution = bindingExecution(binding);
            if ("CAMPAIGN_DISCOVERED_EXECUTION".equals(kind)) {
                if (!expectedExecutionId.equals(bindingExecution)) {
                    throw gap("CROSS_OR_MISSING_DISCOVERED_EXECUTION:"
                            + edgeId + ":expected=" + expectedExecutionId
                            + ":actual=" + bindingExecution);
                }
                Set<String> declared = new LinkedHashSet<>(strings(array(edge,
                        "discoveredExecutionIds")));
                String single = string(edge, "discoveredExecutionId");
                if (!single.isEmpty()) declared.add(single);
                if (!declared.contains(expectedExecutionId)) {
                    throw gap("EDGE_DOES_NOT_DECLARE_BINDING_EXECUTION:"
                            + edgeId);
                }
                return expectedExecutionId;
            }
            if (!bindingExecution.isEmpty()
                    || !string(edge, "discoveredExecutionId").isEmpty()
                    || !array(edge, "discoveredExecutionIds").isEmpty()) {
                throw gap("BASELINE_AND_DISCOVERED_EXECUTION_MIXED:"
                        + edgeId);
            }
            return "BASELINE:" + artifactSha + ":" + test;
        }

        private static String bindingExecution(JsonObject binding)
                throws IOException {
            String explicit = string(binding, "discoveredExecutionId");
            String from = instanceExecution(string(binding,
                    "fromRegionInstance"));
            String to = instanceExecution(string(binding,
                    "toRegionInstance"));
            Set<String> values = new LinkedHashSet<>();
            if (!explicit.isEmpty()) values.add(explicit);
            if (!from.isEmpty()) values.add(from);
            if (!to.isEmpty()) values.add(to);
            if (values.size() > 1) {
                throw gap("BINDING_CROSSES_DISCOVERED_EXECUTIONS:" + values);
            }
            return values.isEmpty() ? "" : values.iterator().next();
        }

        private static String instanceExecution(String instance) {
            int separator = firstNonBlank(instance).indexOf("::");
            return separator <= 0 ? "" : instance.substring(0, separator);
        }
    }

    private static final class RuntimeEdgeIndex {
        private final Map<String, JsonObject> byId;
        private final String artifactSha;
        private final ExecutionScope executionScope;

        private RuntimeEdgeIndex(Map<String, JsonObject> byId,
                                 String artifactSha,
                                 ExecutionScope executionScope) {
            this.byId = byId;
            this.artifactSha = artifactSha;
            this.executionScope = executionScope;
        }

        private static RuntimeEdgeIndex build(List<JsonObject> rows,
                                              String sha,
                                              ExecutionScope executionScope)
                throws IOException {
            Map<String, JsonObject> byId = new LinkedHashMap<>();
            for (JsonObject row : rows) {
                String id = string(row, "edgeId");
                if (id.isEmpty() || byId.put(id, row) != null) {
                    throw gap("DUPLICATE_RUNTIME_EDGE_ID:" + id);
                }
            }
            return new RuntimeEdgeIndex(byId, sha, executionScope);
        }

        private AdmittedEdge validateSummaryBinding(JsonObject binding)
                throws IOException {
            String relation = string(binding, "relation");
            if (!"READ_FROM".equals(relation)
                    || !AutomaticRegionEdge
                    .trustedRuntimeReadFromBinding(binding)) {
                throw gap("STATIC_OR_UNTRUSTED_SUMMARY_EDGE:"
                        + string(binding, "edgeId"));
            }
            return validate(string(binding, "edgeId"), relation,
                    string(binding, "fromRegion"),
                    string(binding, "toRegion"),
                    string(binding, "fromOutputCell"),
                    string(binding, "toInputCell"), binding,
                    string(binding, "fromOutputPort"),
                    string(binding, "toInputPort"));
        }

        private AdmittedEdge validateContextBinding(JsonObject relation,
                                                     JsonObject binding)
                throws IOException {
            String runtimeStatus = string(relation, "runtimeStatus");
            String kind;
            if ("CONFIRMED_READ_FROM".equals(runtimeStatus)) {
                kind = "READ_FROM";
            } else if ("CONFIRMED_RUNTIME_VALUE_EQUALITY".equals(
                    runtimeStatus)) {
                kind = "EQUALITY";
            } else {
                throw gap("STATIC_OR_UNTRUSTED_CONTEXT_EDGE:"
                        + string(relation, "edgeId"));
            }
            return validate(string(relation, "edgeId"), kind,
                    regionOf(string(relation, "fromEndpoint")),
                    regionOf(string(relation, "toEndpoint")),
                    string(relation, "fromCell"),
                    string(relation, "toCell"), binding,
                    string(relation, "fromEndpoint"),
                    string(relation, "toEndpoint"));
        }

        private AdmittedEdge validate(String edgeId, String relation,
                                      String fromRegion, String toRegion,
                                      String fromCell, String toCell,
                                      JsonObject admittedBinding,
                                      String fromPort, String toPort)
                throws IOException {
            JsonObject edge = byId.get(edgeId);
            if (edge == null || bool(edge, "mappingOnly", true)
                    || !bool(edge, "composable", false)
                    || !bool(edge, "eligibleForAutomaticSmt", false)
                    || !relation.equals(string(edge, "validatedRelation"))
                    || !fromRegion.equals(string(edge, "fromRegion"))
                    || !toRegion.equals(string(edge, "toRegion"))
                    || !fromCell.equals(string(edge, "fromPort"))
                    || !toCell.equals(string(edge, "toPort"))) {
                throw gap("RUNTIME_EDGE_METADATA_MISMATCH:" + edgeId);
            }
            List<JsonObject> matches = new ArrayList<>();
            for (JsonElement element : array(edge, "validatedBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject raw = element.getAsJsonObject();
                if (!string(admittedBinding, "fromRegionInstance").equals(
                        string(raw, "fromRegionInstance"))
                        || !string(admittedBinding,
                        "toRegionInstance").equals(string(raw,
                        "toRegionInstance"))) continue;
                if ("READ_FROM".equals(relation)) {
                    long writer = firstLong(admittedBinding,
                            "writerEventSeq", "writeSeq");
                    long reader = firstLong(admittedBinding,
                            "readerEventSeq", "readSeq");
                    if (writer != firstLong(raw, "writerEventSeq",
                            "writeSeq") || reader != firstLong(raw,
                            "readerEventSeq", "readSeq")
                            || writer < 0 || reader <= writer
                            || !bool(raw, "orderConfirmed", false)
                            || longInteger(admittedBinding,
                            "receiverObjectId", -1) != longInteger(raw,
                            "receiverObjectId", -2)
                            || longInteger(admittedBinding,
                            "valueObjectId", -1) != longInteger(raw,
                            "valueObjectId", -2)
                            || !AutomaticRegionEdge
                            .trustedReadFromEvidence(raw)) continue;
                } else {
                    long writer = firstLong(admittedBinding,
                            "fromEndpointSeq", "writerEventSeq");
                    long reader = firstLong(admittedBinding,
                            "toEndpointSeq", "readerEventSeq");
                    if (writer != longInteger(raw, "fromEndpointSeq", -2)
                            || reader != longInteger(raw, "toEndpointSeq", -2)
                            || writer < 0 || reader <= writer
                            || !bool(raw, "orderConfirmed", false)
                            || !bool(raw, "valueEqualityObserved", false)
                            || !"RUNTIME_COMPLETE_VALUE_FINGERPRINT".equals(
                            string(raw, "valueEqualityAuthority"))
                            || string(raw, "valueFingerprint").isEmpty()
                            || !string(raw, "valueFingerprint").equals(string(
                            admittedBinding, "valueFingerprint"))) continue;
                }
                matches.add(raw);
            }
            if (matches.size() != 1) {
                throw gap("RUNTIME_EDGE_BINDING_MATCH_COUNT:" + edgeId
                        + ":" + matches.size());
            }
            JsonObject raw = matches.get(0);
            String test = string(raw, "test");
            if (test.isEmpty()) throw gap("RUNTIME_EDGE_EXECUTION_MISSING:"
                    + edgeId);
            String executionIdentity = executionScope.validate(edge, raw,
                    edgeId, test);
            JsonObject normalized = new JsonObject();
            normalized.addProperty("schemaVersion", 1);
            normalized.addProperty("edgeId", edgeId);
            normalized.addProperty("relation", relation);
            normalized.addProperty("fromRegion", fromRegion);
            normalized.addProperty("toRegion", toRegion);
            normalized.addProperty("fromRegionInstance",
                    string(raw, "fromRegionInstance"));
            normalized.addProperty("toRegionInstance",
                    string(raw, "toRegionInstance"));
            normalized.addProperty("fromPort", fromPort);
            normalized.addProperty("toPort", toPort);
            normalized.addProperty("fromCell", fromCell);
            normalized.addProperty("toCell", toCell);
            normalized.addProperty("fromEventSeq", "READ_FROM".equals(
                    relation) ? firstLong(raw, "writerEventSeq", "writeSeq")
                    : longInteger(raw, "fromEndpointSeq", -1));
            normalized.addProperty("toEventSeq", "READ_FROM".equals(
                    relation) ? firstLong(raw, "readerEventSeq", "readSeq")
                    : longInteger(raw, "toEndpointSeq", -1));
            normalized.addProperty("orderConfirmed", true);
            normalized.addProperty("executionIdentity", executionIdentity);
            normalized.addProperty("executionScopeKind",
                    executionScope.kind);
            normalized.addProperty("runtimeEdgeArtifactSha256", artifactSha);
            normalized.addProperty("runtimeBindingObjectSha256",
                    sha256(GSON.toJson(raw)));
            normalized.addProperty("runtimeValidationAuthority",
                    "READ_FROM".equals(relation)
                            ? "RUNTIME_CONFIRMED_READ_FROM"
                            : "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
            if ("READ_FROM".equals(relation)) {
                normalized.addProperty("receiverObjectId", longInteger(raw,
                        "receiverObjectId", -1));
                normalized.addProperty("valueObjectId", longInteger(raw,
                        "valueObjectId", -1));
                normalized.addProperty("objectIdentityConfirmed", true);
            } else {
                normalized.addProperty("valueFingerprint",
                        string(raw, "valueFingerprint"));
                normalized.addProperty("valueEqualityObserved", true);
                normalized.addProperty("valueEqualityAuthority",
                        string(raw, "valueEqualityAuthority"));
                normalized.addProperty("fromFingerprintSource",
                        string(raw, "fromFingerprintSource"));
                normalized.addProperty("toFingerprintSource",
                        string(raw, "toFingerprintSource"));
            }
            return new AdmittedEdge(normalized);
        }

        private AdmittedEdge revalidateNormalized(JsonObject normalized)
                throws IOException {
            JsonObject admitted = new JsonObject();
            admitted.addProperty("fromRegionInstance", string(normalized,
                    "fromRegionInstance"));
            admitted.addProperty("toRegionInstance", string(normalized,
                    "toRegionInstance"));
            if ("READ_FROM".equals(string(normalized, "relation"))) {
                admitted.addProperty("writerEventSeq", longInteger(normalized,
                        "fromEventSeq", -1));
                admitted.addProperty("readerEventSeq", longInteger(normalized,
                        "toEventSeq", -1));
                admitted.addProperty("receiverObjectId", longInteger(
                        normalized, "receiverObjectId", -1));
                admitted.addProperty("valueObjectId", longInteger(normalized,
                        "valueObjectId", -1));
            } else {
                admitted.addProperty("fromEndpointSeq", longInteger(normalized,
                        "fromEventSeq", -1));
                admitted.addProperty("toEndpointSeq", longInteger(normalized,
                        "toEventSeq", -1));
                admitted.addProperty("valueFingerprint", string(normalized,
                        "valueFingerprint"));
            }
            AdmittedEdge verified = validate(string(normalized, "edgeId"),
                    string(normalized, "relation"), string(normalized,
                    "fromRegion"), string(normalized, "toRegion"),
                    string(normalized, "fromCell"), string(normalized,
                    "toCell"), admitted, string(normalized, "fromPort"),
                    string(normalized, "toPort"));
            JsonObject normalizedCore = normalized.deepCopy();
            normalizedCore.remove("composerAdmissions");
            if (!GSON.toJson(verified.json).equals(GSON.toJson(
                    normalizedCore))) {
                throw gap("NORMALIZED_RUNTIME_EDGE_WITNESS_MISMATCH:"
                        + string(normalized, "edgeId"));
            }
            return verified;
        }

        private static long firstLong(JsonObject object, String first,
                                      String second) {
            long value = longInteger(object, first, Long.MIN_VALUE);
            return value != Long.MIN_VALUE ? value
                    : longInteger(object, second, -1L);
        }
    }

    private static String regionOf(String endpoint) {
        Matcher matcher = Pattern.compile("REGION\\.[0-9]+").matcher(
                firstNonBlank(endpoint));
        return matcher.find() ? matcher.group() : "";
    }

    private static final class AdmittedEdge {
        private final JsonObject json;

        private AdmittedEdge(JsonObject json) {
            this.json = json;
        }

        private String fromInstance() {
            return string(json, "fromRegionInstance");
        }

        private String toInstance() {
            return string(json, "toRegionInstance");
        }

        private String identity() {
            return string(json, "edgeId") + "\n" + fromInstance() + "\n"
                    + toInstance() + "\n" + longInteger(json,
                    "fromEventSeq", -1) + "\n" + longInteger(json,
                    "toEventSeq", -1);
        }

        private void admitSummary(JsonObject pathCase, JsonObject summary,
                                  JsonObject binding) {
            JsonObject admission = new JsonObject();
            admission.addProperty("kind",
                    "SELECTED_CASE_SUMMARY_EDGE_BINDING");
            admission.addProperty("caseId", string(pathCase, "caseId"));
            admission.addProperty("caseSelectorSolverTerm", string(
                    pathCase, "selectorSolverSymbol"));
            admission.addProperty("sourceSummaryId", string(summary,
                    "summaryId"));
            admission.addProperty("selectedBindingObjectSha256",
                    sha256(GSON.toJson(binding)));
            addAdmission(admission);
        }

        private void admitFatalContext(JsonObject relation,
                                       JsonObject binding) {
            JsonObject admission = new JsonObject();
            admission.addProperty("kind",
                    "FATAL_SYMBOLIC_CONTEXT_SELECTED_BINDING");
            admission.addProperty("relationObjectSha256",
                    sha256(GSON.toJson(relation)));
            admission.addProperty("selectedBindingObjectSha256",
                    sha256(GSON.toJson(binding)));
            addAdmission(admission);
        }

        private boolean admittedForCase(String caseId) {
            for (JsonElement element : array(json, "composerAdmissions")) {
                if (!element.isJsonObject()) continue;
                JsonObject admission = element.getAsJsonObject();
                String kind = string(admission, "kind");
                if ("FATAL_SYMBOLIC_CONTEXT_SELECTED_BINDING".equals(kind)
                        || ("SELECTED_CASE_SUMMARY_EDGE_BINDING".equals(kind)
                        && caseId.equals(string(admission, "caseId")))) {
                    return true;
                }
            }
            return false;
        }

        private void addAdmission(JsonObject admission) {
            JsonArray admissions = array(json, "composerAdmissions")
                    .deepCopy();
            Map<String, JsonObject> canonical = new LinkedHashMap<>();
            for (JsonElement element : admissions) {
                if (element.isJsonObject()) canonical.put(
                        GSON.toJson(element), element.getAsJsonObject());
            }
            canonical.put(GSON.toJson(admission), admission);
            List<String> keys = new ArrayList<>(canonical.keySet());
            Collections.sort(keys);
            JsonArray sorted = new JsonArray();
            for (String key : keys) sorted.add(canonical.get(key).deepCopy());
            json.add("composerAdmissions", sorted);
        }

        private void mergeAdmissions(AdmittedEdge other) throws IOException {
            JsonObject leftCore = json.deepCopy();
            JsonObject rightCore = other.json.deepCopy();
            leftCore.remove("composerAdmissions");
            rightCore.remove("composerAdmissions");
            if (!GSON.toJson(leftCore).equals(GSON.toJson(rightCore))) {
                throw gap("CONFLICTING_ADMITTED_EDGE:" + identity());
            }
            for (JsonElement element : array(other.json,
                    "composerAdmissions")) {
                if (element.isJsonObject()) addAdmission(
                        element.getAsJsonObject());
            }
        }
    }

    private static final class SolverOutput {
        private final int exitCode;
        private final boolean timedOut;
        private final String stdout;
        private final String stderr;

        private SolverOutput(int exitCode, boolean timedOut, String stdout,
                             String stderr) {
            this.exitCode = exitCode;
            this.timedOut = timedOut;
            this.stdout = stdout;
            this.stderr = stderr;
        }
    }
}
