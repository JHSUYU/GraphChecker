package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.concolic.ConcolicSmtComposer;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Builds the explicitly approximate, one-DataNode bootstrap model used for
 * the pre-fix HDFS-11741 experiment.
 *
 * <p>This adapter deliberately does not weaken {@code ConcolicSmtComposer}'s
 * project-independent completeness rules.  It requires exact static evidence
 * for the target lookup, the expiry comparison, the map mutation, and the
 * array-element field projections.  Only the cross-iteration witness, the
 * pre-fix cache persistence, and configured transport round trips are allowed
 * to be approximate.  The resulting manifest therefore always says
 * {@code complete=false} and cannot be reported as a validated final model.</p>
 *
 * <p>The adapter requires one imported, relationally complete concolic
 * transformer for each configured semantic region (NameNode, balancer key
 * updater, DataNode heartbeat, dispatcher, and SASL target).  Their real
 * guards and output expressions are translated by {@link ConcolicSmtComposer}
 * and conjoined with the explicit bootstrap contracts; replay files are not
 * accepted as hash-only supplemental evidence.</p>
 *
 * <p>Every HDFS method and field selector comes from the policy JSON.  Region
 * ids, port ids, filesystem paths, and commands are discovered from the CLI
 * artifacts and never embedded here.</p>
 */
public final class Hdfs11741BootstrapComposer {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().serializeNulls().setPrettyPrinting()
            .create();
    private static final List<String> REGION_ROLES = Arrays.asList(
            "namenode", "keyUpdater", "datanode", "balancer", "target");
    private static final List<String> PORT_ROLES = Arrays.asList(
            "targetMap", "targetEncodedKey", "targetFailure",
            "namenodeMapPre", "namenodeMapPost", "namenodeExpiry",
            "namenodeNow", "datanodeMapPre", "datanodeMapPost",
            "datanodeSnapshot", "datanodeEntryKey",
            "datanodeEntryExpiry", "datanodeNow",
            "keyUpdaterCurrentKey", "balancerCachedKey",
            "balancerSaslUsername");

    private Hdfs11741BootstrapComposer() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        Result result = compose(arguments);
        write(arguments.output, result.smtLib);
        write(arguments.manifest, GSON.toJson(result.manifest)
                + System.lineSeparator());
        System.out.println(GSON.toJson(result.manifest));
    }

    public static Result compose(Arguments arguments) throws IOException {
        require(arguments.policy, "selector policy");
        require(arguments.regions, "symbolic regions");
        require(arguments.staticGraph, "static dataflow graph");
        require(arguments.regionEdges, "symbolic region edges");
        require(arguments.runtimeEdges, "runtime edge validations");
        require(arguments.runtimeSummary, "runtime summary");
        require(arguments.activationPlan, "activation plan");
        require(arguments.offlineProvenance, "offline provenance");
        require(arguments.targetQuery, "directed fatal branch query");
        if (arguments.replaySummaries.isEmpty()) {
            throw gap("FIVE_REPLAY_SUMMARIES_REQUIRED:0");
        }
        for (Path replaySummary : arguments.replaySummaries) {
            require(replaySummary, "required replay summary");
        }

        JsonObject policy = readJson(arguments.policy);
        validatePolicy(policy);
        Map<String, JsonObject> regions = selectRegions(arguments.regions,
                object(policy, "regions"));
        Map<String, JsonObject> ports = selectPorts(regions,
                object(policy, "ports"));

        JsonObject bindingsPolicy = object(policy, "containerBindings");
        JsonObject keyBinding = uniqueBinding(regions.get("datanode"),
                object(bindingsPolicy, "keyId"), "keyId");
        JsonObject expiryBinding = uniqueBinding(regions.get("datanode"),
                object(bindingsPolicy, "expiry"), "expiry");
        validateContainerBindings(keyBinding, expiryBinding, ports);

        StaticEvidence staticEvidence = scanStaticGraph(
                arguments.staticGraph, object(policy, "staticEvidence"),
                keyBinding, expiryBinding);
        JsonObject regionEdgeEvidence = scanRegionEdges(arguments.regionEdges,
                regions, object(policy, "runtimeEvidence"));
        RuntimeEvidence runtimeEvidence = scanRuntimeEdges(
                arguments.runtimeEdges, regions,
                object(policy, "runtimeEvidence"));
        JsonObject activationEvidence = scanActivations(
                arguments.activationPlan, regions,
                string(policy, "workload"));
        JsonObject runtimeSummary = readJson(arguments.runtimeSummary);
        JsonObject offlineProvenance = readJson(
                arguments.offlineProvenance);

        TargetQueryEvidence targetQuery = selectTargetQuery(
                arguments.targetQuery, regions.get("target"),
                object(policy, "targetGuard"));
        ReplayEvidence replayEvidence = selectReplaySummaries(
                arguments.replaySummaries, regions,
                object(policy, "approximationPolicy"), targetQuery);
        ConcolicSmtComposer.SummaryFormulaFragment replayFormulas =
                ConcolicSmtComposer.renderSummaryFormulaFragment(
                        new ArrayList<>(regions.values()),
                        replayEvidence.orderedSummaries);
        validateReplayFormulaFragment(replayFormulas,
                replayEvidence.orderedSummaries.size());

        JsonObject artifacts = inputArtifacts(arguments);
        validateRuntimeArtifacts(policy, runtimeSummary,
                offlineProvenance, artifacts);

        validateTargetGuard(regions.get("target"),
                object(policy, "targetGuard"));
        JsonArray approximations = approximationCatalog(policy,
                runtimeEvidence, regions, replayEvidence);

        String smt = renderSmt(regions, ports, keyBinding, expiryBinding,
                replayEvidence, replayFormulas, targetQuery);
        byte[] smtBytes = smt.getBytes(StandardCharsets.UTF_8);

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("kind",
                "HDFS_11741_APPROXIMATE_BOOTSTRAP_COMPOSITION");
        manifest.addProperty("profileId", string(policy, "profileId"));
        manifest.addProperty("workload", string(policy, "workload"));
        manifest.addProperty("compositionStage", "BOOTSTRAP");
        manifest.addProperty("complete", false);
        manifest.addProperty("relationallyComplete", false);
        manifest.addProperty("structurallyComplete", false);
        manifest.addProperty("domainSemanticAdapterUsed", true);
        manifest.addProperty("explicitContractsIncluded", true);
        manifest.addProperty("eligibleForApproximateBootstrapModel", true);
        manifest.addProperty("eligibleForBootstrapModel", false);
        manifest.addProperty("eligibleToReportAutomaticRelationship", false);
        manifest.addProperty("solverActuallyInvoked", false);
        manifest.addProperty("oneDataNodeModel", true);
        manifest.addProperty("innerMapExpirySymbolic", true);
        manifest.addProperty("outerLoopApproximationUsed", true);
        manifest.addProperty("status", "APPROXIMATE_BOOTSTRAP_SMT_READY");
        manifest.addProperty("soundnessScope",
                "ONE_RELEVANT_SYMBOLIC_MAP_ENTRY_PLUS_EXPLICIT_HDFS_"
                        + "TRANSPORT_AND_OUTER_LOOP_APPROXIMATIONS");
        manifest.addProperty("mapAbstraction",
                "SYMBOLIC_MEMBERSHIP_AND_EXPIRY_ARRAY_ONE_RELEVANT_ENTRY");
        manifest.addProperty("derivedCondition",
                "There exists a symbolic block-key entry whose expiry is "
                        + "earlier than the selected DataNode removal time; "
                        + "the pre-fix balancer keeps that entry's key id "
                        + "cached and SASL transports it after the DataNode "
                        + "removes the same entry, so allKeys.get(keyId) is "
                        + "null and InvalidEncryptionKeyException is reached.");
        manifest.addProperty("derivedConditionSmt",
                "entryExpiry < removeNow && cachedKeyId == entryKeyId && "
                        + "saslServerKeyId == cachedKeyId && "
                        + "!member(dnKeysAtTarget, saslServerKeyId)");
        manifest.add("selectedRegions", selectedRegionCatalog(regions));
        manifest.add("portMappings", selectedPortCatalog(ports));
        JsonObject bindings = new JsonObject();
        bindings.add("keyId", keyBinding.deepCopy());
        bindings.add("expiry", expiryBinding.deepCopy());
        manifest.add("containerBindings", bindings);
        manifest.add("staticEvidence", staticEvidence.catalog);
        manifest.add("regionEdgeEvidence", regionEdgeEvidence);
        manifest.add("runtimeEvidence", runtimeEvidence.catalog);
        manifest.add("activationEvidence", activationEvidence);
        manifest.add("runtimeSummary", selectedMetadata(runtimeSummary));
        manifest.add("offlineProvenance",
                selectedMetadata(offlineProvenance));
        manifest.add("approximations", approximations);
        JsonObject supplemental = new JsonObject();
        supplemental.addProperty("replaySummariesRequired", true);
        supplemental.addProperty("requiredSemanticRegionCount",
                REGION_ROLES.size());
        supplemental.addProperty("replaySummaryCount",
                replayEvidence.orderedSummaries.size());
        supplemental.add("selectedReplaySummaries",
                replayEvidence.catalog.deepCopy());
        supplemental.add("replayFormulaProjection",
                replayFormulas.catalog.deepCopy());
        supplemental.add("replaySummaryArtifacts",
                replayEvidence.artifacts.deepCopy());
        supplemental.add("directedFatalBranchQuery",
                targetQuery.catalog.deepCopy());
        supplemental.addProperty("directedFatalBranchQueryRequired", true);
        supplemental.addProperty("summaryContractBridgeAuthority",
                "POLICY_SELECTED_TYPED_PORTS_PLUS_EXACT_COMPOSER_"
                        + "EMITTED_SYMBOLS_PLUS_CONFIGURED_HDFS_FIELD_"
                        + "AND_CODEC_ADAPTER_V2");
        supplemental.addProperty("summaryContractBridgeCount", 12);
        supplemental.add("summaryContractBridges",
                summaryContractBridgeCatalog());
        manifest.add("supplementalEvidence", supplemental);
        manifest.add("blockers", new JsonArray());
        manifest.addProperty("assertionCount", countAssertions(smt));
        manifest.addProperty("output",
                arguments.output.toAbsolutePath().normalize().toString());

        manifest.add("inputArtifacts", artifacts);
        manifest.add("smtArtifact", artifact(arguments.output, smtBytes));
        manifest.add("researchScope", object(policy, "researchScope")
                .deepCopy());
        return new Result(smt, manifest);
    }

    private static void validatePolicy(JsonObject policy) throws IOException {
        if (integer(policy, "schemaVersion", -1) != 1) {
            throw gap("POLICY_SCHEMA_VERSION");
        }
        requireText(policy, "profileId", "policy profile id");
        requireText(policy, "workload", "policy workload");
        JsonObject regionPolicy = object(policy, "regions");
        for (String role : REGION_ROLES) {
            JsonObject selector = object(regionPolicy, role);
            if (selector.size() == 0) throw gap(
                    "MISSING_REGION_SELECTOR:" + role);
            requireText(selector, "rootMethod", role + " root method");
            requireText(selector, "anchorMethod", role + " anchor method");
        }
        JsonObject portPolicy = object(policy, "ports");
        for (String role : PORT_ROLES) {
            JsonObject selector = object(portPolicy, role);
            if (selector.size() == 0) throw gap(
                    "MISSING_PORT_SELECTOR:" + role);
            requireText(selector, "region", role + " region role");
            requireText(selector, "collection", role + " collection");
            requireText(selector, "cell", role + " exact cell");
        }
        JsonObject target = object(policy, "targetGuard");
        requireText(target, "siteId", "target guard site");
        if (!target.has("requiredOutcome")
                || bool(target, "requiredOutcome", true)) {
            throw gap("TARGET_GUARD_MUST_REQUIRE_FALSE_OUTCOME");
        }
        JsonObject bindings = object(policy, "containerBindings");
        requireBindingPolicy(object(bindings, "keyId"), "keyId");
        requireBindingPolicy(object(bindings, "expiry"), "expiry");
        JsonObject staticEvidence = object(policy, "staticEvidence");
        requireText(staticEvidence, "targetMethod",
                "static target method");
        requireText(staticEvidence, "removeMethod",
                "static remove method");
        requireText(staticEvidence, "structuredEncoding",
                "static structured encoding");
        requireStringArray(staticEvidence, "requiredTargetEdgeKinds");
        requireStringArray(staticEvidence, "requiredRemoveEdgeKinds");

        JsonObject runtimeEvidence = object(policy, "runtimeEvidence");
        requireStringArray(runtimeEvidence, "saslKinds");
        requireStringArray(runtimeEvidence, "sharedStateKinds");
        requireStringArray(runtimeEvidence, "regionEdgeMappingKinds");

        JsonObject approximation = object(policy,
                "approximationPolicy");
        for (String flag : Arrays.asList(
                "allowOuterLoopSingleWitness",
                "allowNnSnapshotFanout",
                "allowPreFixCachePersistence",
                "allowSaslCodecRoundTrip")) {
            if (!bool(approximation, flag, false)) {
                throw gap("APPROXIMATION_NOT_AUTHORIZED:" + flag);
            }
        }
        requireText(approximation, "outerLoopAuthority",
                "outer loop authority");
        requireStringArray(approximation,
                "allowedOuterLoopRootMethods");
        if (bool(approximation,
                "allowOperationallyAdmittedPartialReplaySummaries",
                false)) {
            requireStringArray(approximation,
                    "allowedPartialReplayRoles");
        }
    }

    private static void requireBindingPolicy(JsonObject policy,
                                             String label)
            throws IOException {
        if (policy.size() == 0) throw gap(
                "MISSING_CONTAINER_BINDING_SELECTOR:" + label);
        requireText(policy, "declaredFieldSignature",
                label + " declared field signature");
        requireText(policy, "materializationMode",
                label + " materialization mode");
        requireStringArray(policy, "fieldPath");
    }

    private static Map<String, JsonObject> selectRegions(Path path,
            JsonObject policy) throws IOException {
        final Map<String, List<JsonObject>> candidates =
                new LinkedHashMap<>();
        for (String role : REGION_ROLES) candidates.put(role,
                new ArrayList<JsonObject>());
        forEachJsonl(path, new JsonConsumer() {
            @Override
            public void accept(JsonObject row) {
                for (String role : REGION_ROLES) {
                    if (matchesRegion(row, object(policy, role))) {
                        candidates.get(role).add(row.deepCopy());
                    }
                }
            }
        });
        Map<String, JsonObject> result = new LinkedHashMap<>();
        Set<String> ids = new LinkedHashSet<>();
        for (String role : REGION_ROLES) {
            List<JsonObject> matches = candidates.get(role);
            if (matches.size() != 1) {
                throw gap("REGION_SELECTOR_CARDINALITY:" + role + ":"
                        + matches.size());
            }
            JsonObject selected = matches.get(0);
            String id = string(selected, "regionId");
            if (id.isEmpty() || !ids.add(id)) {
                throw gap("REGION_ID_MISSING_OR_REUSED:" + role + ":" + id);
            }
            result.put(role, selected);
        }
        return result;
    }

    private static boolean matchesRegion(JsonObject region,
                                         JsonObject selector) {
        if (!string(selector, "rootMethod").equals(
                string(region, "rootMethod"))) return false;
        if (!string(selector, "anchorMethod").equals(
                string(region, "anchorMethod"))) return false;
        Set<String> methods = stringSet(array(region, "methods"));
        for (JsonElement element : array(selector, "requiredMethods")) {
            if (!element.isJsonPrimitive()
                    || !methods.contains(element.getAsString())) return false;
        }
        return true;
    }

    private static Map<String, JsonObject> selectPorts(
            Map<String, JsonObject> regions, JsonObject policy)
            throws IOException {
        Map<String, JsonObject> result = new LinkedHashMap<>();
        for (String role : PORT_ROLES) {
            JsonObject selector = object(policy, role);
            String regionRole = string(selector, "region");
            JsonObject region = regions.get(regionRole);
            if (region == null) throw gap("UNKNOWN_PORT_REGION_ROLE:" + role
                    + ":" + regionRole);
            String collection = string(selector, "collection");
            String cell = string(selector, "cell");
            List<JsonObject> matches = new ArrayList<>();
            for (JsonElement element : array(region, collection)) {
                if (element.isJsonObject() && cell.equals(string(
                        element.getAsJsonObject(), "cell"))) {
                    matches.add(element.getAsJsonObject());
                }
            }
            if (matches.size() != 1) throw gap(
                    "PORT_SELECTOR_CARDINALITY:" + role + ":"
                            + matches.size());
            JsonObject selected = matches.get(0).deepCopy();
            selected.addProperty("regionRole", regionRole);
            selected.addProperty("regionId", string(region, "regionId"));
            selected.addProperty("collection", collection);
            result.put(role, selected);
        }
        return result;
    }

    private static JsonObject uniqueBinding(JsonObject region,
            JsonObject selector, String label) throws IOException {
        List<JsonObject> matches = new ArrayList<>();
        collectBindings(region, selector, matches);
        if (matches.size() != 1) throw gap(
                "CONTAINER_BINDING_CARDINALITY:" + label + ":"
                        + matches.size());
        return matches.get(0).deepCopy();
    }

    private static void collectBindings(JsonElement value,
            JsonObject selector, List<JsonObject> matches) {
        if (value == null || value.isJsonNull()) return;
        if (value.isJsonArray()) {
            for (JsonElement element : value.getAsJsonArray()) {
                collectBindings(element, selector, matches);
            }
            return;
        }
        if (!value.isJsonObject()) return;
        JsonObject object = value.getAsJsonObject();
        if ("ARRAY_ELEMENT_FIELD".equals(string(object, "kind"))
                && bool(object, "complete", false)
                && array(selector, "fieldPath").equals(
                array(object, "fieldPath"))
                && string(selector, "declaredFieldSignature").equals(
                string(object, "declaredFieldSignature"))
                && string(selector, "materializationMode").equals(
                string(object, "materializationMode"))
                && (!selector.has("schemaVersion")
                || integer(selector, "schemaVersion", -1) == integer(object,
                "schemaVersion", -2))) {
            matches.add(object);
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            collectBindings(entry.getValue(), selector, matches);
        }
    }

    private static void validateContainerBindings(JsonObject key,
            JsonObject expiry, Map<String, JsonObject> ports)
            throws IOException {
        if (!"ARRAY_ELEMENT_FIELD".equals(string(key, "kind"))
                || !bool(key, "complete", false)) {
            throw gap("KEY_ID_CONTAINER_BINDING_INCOMPLETE");
        }
        if (integer(expiry, "schemaVersion", -1) != 2
                || !"ARRAY_ELEMENT_FIELD".equals(string(expiry, "kind"))
                || !"CONTAINER_SNAPSHOT".equals(string(expiry,
                "materializationMode"))
                || !bool(expiry, "complete", false)
                || array(expiry, "proofCausalEdgeIds").size() != 5) {
            throw gap("EXPIRY_CONTAINER_SNAPSHOT_NOT_EXACT_SCHEMA2_FIVE_EDGE");
        }
        String container = portId(ports.get("datanodeSnapshot"));
        String keyPort = portId(ports.get("datanodeEntryKey"));
        String expiryPort = portId(ports.get("datanodeEntryExpiry"));
        if (!container.equals(string(key, "containerInputPort"))
                || !container.equals(string(expiry, "containerInputPort"))) {
            throw gap("CONTAINER_BINDINGS_DO_NOT_SHARE_SNAPSHOT_PORT");
        }
        if (!keyPort.equals(string(key, "baseInputSymbol"))
                || !expiryPort.equals(string(expiry, "baseInputSymbol"))) {
            throw gap("CONTAINER_BINDING_BASE_PORT_MISMATCH");
        }
    }

    private static StaticEvidence scanStaticGraph(Path path,
            JsonObject policy, JsonObject keyBinding,
            JsonObject expiryBinding) throws IOException {
        final String targetMethod = string(policy, "targetMethod");
        final String removeMethod = string(policy, "removeMethod");
        final String encoding = string(policy, "structuredEncoding");
        final Set<String> targetKinds = stringSet(array(policy,
                "requiredTargetEdgeKinds"));
        final Set<String> removeKinds = stringSet(array(policy,
                "requiredRemoveEdgeKinds"));
        final Map<String, String> targetMatches = new LinkedHashMap<>();
        final Map<String, String> removeMatches = new LinkedHashMap<>();
        final Set<String> proofRequired = new LinkedHashSet<>();
        proofRequired.addAll(stringSet(array(keyBinding,
                "proofCausalEdgeIds")));
        proofRequired.addAll(stringSet(array(expiryBinding,
                "proofCausalEdgeIds")));
        final Set<String> proofObserved = new LinkedHashSet<>();
        final JsonArray structured = new JsonArray();
        forEachJsonl(path, new JsonConsumer() {
            @Override
            public void accept(JsonObject edge) {
                String id = string(edge, "id");
                if (proofRequired.contains(id)) proofObserved.add(id);
                String method = string(edge, "method");
                String kind = string(edge, "kind");
                if (targetMethod.equals(method) && targetKinds.contains(kind)
                        && !targetMatches.containsKey(kind)) {
                    targetMatches.put(kind, id);
                }
                if (removeMethod.equals(method) && removeKinds.contains(kind)
                        && !removeMatches.containsKey(kind)) {
                    removeMatches.put(kind, id);
                }
                if (encoding.equals(string(edge, "structuredEncoding"))) {
                    JsonObject row = minimalEdge(edge);
                    if (structured.size() < 16) structured.add(row);
                }
            }
        });
        Set<String> missingTarget = difference(targetKinds,
                targetMatches.keySet());
        Set<String> missingRemove = difference(removeKinds,
                removeMatches.keySet());
        Set<String> missingProof = difference(proofRequired, proofObserved);
        if (!missingTarget.isEmpty()) throw gap(
                "MISSING_TARGET_STATIC_EDGE_KINDS:" + missingTarget);
        if (!missingRemove.isEmpty()) throw gap(
                "MISSING_REMOVE_STATIC_EDGE_KINDS:" + missingRemove);
        if (!missingProof.isEmpty()) throw gap(
                "MISSING_CONTAINER_PROOF_EDGES:" + missingProof);
        if (structured.size() == 0) throw gap(
                "MISSING_STRUCTURED_ENCODING_EDGE:" + encoding);

        JsonObject catalog = new JsonObject();
        catalog.addProperty("targetMethod", targetMethod);
        catalog.add("targetEdgeKinds", mapToJson(targetMatches));
        catalog.addProperty("removeMethod", removeMethod);
        catalog.add("removeEdgeKinds", mapToJson(removeMatches));
        catalog.add("containerProofEdgeIds",
                GSON.toJsonTree(proofObserved));
        catalog.addProperty("containerProofComplete", true);
        catalog.addProperty("structuredEncoding", encoding);
        catalog.add("structuredEncodingEdges", structured);
        catalog.addProperty("complete", true);
        return new StaticEvidence(catalog);
    }

    private static JsonObject scanRegionEdges(Path path,
            Map<String, JsonObject> regions, JsonObject policy)
            throws IOException {
        final Set<String> ids = regionIds(regions);
        final Set<String> configuredKinds = stringSet(array(policy,
                "regionEdgeMappingKinds"));
        final JsonArray samples = new JsonArray();
        final long[] counts = new long[2];
        forEachJsonl(path, new JsonConsumer() {
            @Override
            public void accept(JsonObject edge) {
                String from = string(edge, "fromRegion");
                String to = string(edge, "toRegion");
                if (!(ids.contains(from) || ids.contains(to)
                        || ("EXTERNAL".equals(from) && ids.contains(to)))) {
                    return;
                }
                counts[0]++;
                String mappingKind = string(edge, "mappingKind");
                if (!configuredKinds.isEmpty()
                        && !configuredKinds.contains(mappingKind)) return;
                counts[1]++;
                if (samples.size() < 64) samples.add(minimalRegionEdge(edge));
            }
        });
        JsonObject result = new JsonObject();
        result.addProperty("relevantEdgeCount", counts[0]);
        result.addProperty("configuredMappingEdgeCount", counts[1]);
        result.addProperty("sampleTruncated", counts[1] > samples.size());
        result.add("edges", samples);
        if (counts[1] == 0) throw gap(
                "MISSING_CONFIGURED_STATIC_TRANSPORT_MAPPING");
        return result;
    }

    private static RuntimeEvidence scanRuntimeEdges(Path path,
            Map<String, JsonObject> regions, JsonObject policy)
            throws IOException {
        final Set<String> ids = regionIds(regions);
        final Set<String> saslKinds = stringSet(array(policy, "saslKinds"));
        final Set<String> sharedKinds = stringSet(array(policy,
                "sharedStateKinds"));
        final String target = regionId(regions, "target");
        final String datanode = regionId(regions, "datanode");
        final String balancer = regionId(regions, "balancer");
        final JsonArray samples = new JsonArray();
        final long[] counts = new long[4];
        forEachJsonl(path, new JsonConsumer() {
            @Override
            public void accept(JsonObject edge) {
                String from = string(edge, "fromRegion");
                String to = string(edge, "toRegion");
                if (!ids.contains(from) && !ids.contains(to)) return;
                counts[0]++;
                boolean confirmed = integer(edge,
                        "confirmedReadFromPairCount", 0) > 0
                        || integer(edge, "confirmedValueEqualityPairCount",
                        0) > 0
                        || string(edge, "status").startsWith("CONFIRMED");
                if (!confirmed) return;
                counts[1]++;
                String kind = string(edge, "kind");
                String mapping = string(edge, "mappingKind");
                if (balancer.equals(from) && target.equals(to)
                        && (saslKinds.contains(kind)
                        || saslKinds.contains(mapping))) {
                    counts[2]++;
                }
                if (datanode.equals(from) && target.equals(to)
                        && (sharedKinds.contains(kind)
                        || sharedKinds.contains(mapping))) counts[3]++;
                if (samples.size() < 64) samples.add(
                        minimalRuntimeEdge(edge));
            }
        });
        JsonObject catalog = new JsonObject();
        catalog.addProperty("relevantEdgeCount", counts[0]);
        catalog.addProperty("confirmedEdgeCount", counts[1]);
        catalog.addProperty("confirmedSaslEdgeCount", counts[2]);
        catalog.addProperty("confirmedSharedStateEdgeCount", counts[3]);
        catalog.addProperty("sampleTruncated", counts[1] > samples.size());
        catalog.add("confirmedEdges", samples);
        catalog.addProperty("runtimeTransportEvidenceComplete",
                counts[2] > 0 && counts[3] > 0);
        return new RuntimeEvidence(catalog, counts[2] > 0,
                counts[3] > 0);
    }

    private static JsonObject scanActivations(Path path,
            Map<String, JsonObject> regions, final String workload)
            throws IOException {
        final Map<String, String> rolesById = new LinkedHashMap<>();
        for (Map.Entry<String, JsonObject> entry : regions.entrySet()) {
            rolesById.put(string(entry.getValue(), "regionId"),
                    entry.getKey());
        }
        final Map<String, Long> counts = new LinkedHashMap<>();
        final Map<String, JsonObject> selected = new LinkedHashMap<>();
        for (String role : REGION_ROLES) counts.put(role, 0L);
        forEachJsonl(path, new JsonConsumer() {
            @Override
            public void accept(JsonObject row) {
                String role = rolesById.get(string(row, "regionId"));
                if (role == null) return;
                String test = firstNonBlank(string(row, "test"),
                        string(row, "workload"));
                if (!workload.equals(test)) return;
                counts.put(role, counts.get(role) + 1L);
                JsonObject candidate = minimalActivation(row);
                JsonObject previous = selected.get(role);
                if (previous == null || activationOrder(candidate)
                        < activationOrder(previous)) selected.put(role,
                        candidate);
            }
        });
        JsonObject countJson = new JsonObject();
        JsonObject selectedJson = new JsonObject();
        for (String role : REGION_ROLES) {
            countJson.addProperty(role, counts.get(role));
            selectedJson.add(role, selected.containsKey(role)
                    ? selected.get(role) : new JsonObject());
        }
        JsonObject result = new JsonObject();
        result.add("activationCounts", countJson);
        result.add("deterministicWitnesses", selectedJson);
        boolean allObserved = counts.values().stream()
                .allMatch(value -> value > 0);
        result.addProperty("allRolesObserved", allObserved);
        if (!allObserved) throw gap("WORKLOAD_DID_NOT_OBSERVE_ALL_ROLES:"
                + countJson);
        return result;
    }

    private static JsonArray approximationCatalog(JsonObject policy,
            RuntimeEvidence runtime, Map<String, JsonObject> regions,
            ReplayEvidence replay)
            throws IOException {
        JsonObject allowed = object(policy, "approximationPolicy");
        JsonArray result = new JsonArray();
        result.add(approximation("OUTER_LONG_LOOP_SINGLE_ORDERED_WITNESS",
                "Heartbeat/updater repetitions are represented by one "
                        + "ordered cache, removal, and send witness."));
        result.add(approximation("CONFIGURED_NN_SNAPSHOT_FANOUT",
                "The selected NameNode snapshot key and expiry are projected "
                        + "to the Balancer and one DataNode."));
        result.add(approximation("PRE_FIX_BALANCER_CACHE_PERSISTS",
                "The pre-fix KeyManager cached DataEncryptionKey is retained "
                        + "across later block-key updates."));
        result.add(approximation(
                "STATIC_CODEC_TEMPLATE_REUSED_FOR_SELECTED_BALANCER_PORT",
                "A statically discovered HDFS decimal username codec "
                        + "template is applied to the selected PendingMove "
                        + "SASL port; this is not an exact runtime "
                        + "Balancer-to-DataNode equality edge."));
        List<String> boundedRoles = new ArrayList<>();
        for (String role : REGION_ROLES) {
            if (bool(regions.get(role), "truncated", false)) {
                boundedRoles.add(role);
            }
        }
        if (!boundedRoles.isEmpty()) {
            result.add(approximation("STATIC_REGION_CATALOG_BOUNDED",
                    "The selected static region catalog marks these roles "
                            + "as bounded/truncated: " + boundedRoles
                            + ". The model uses only the explicitly selected "
                            + "ports and evidence slices."));
        }
        if (!replay.partialRoles.isEmpty()) {
            result.add(approximation(
                    "OPERATIONALLY_ADMITTED_PARTIAL_REPLAY_SUMMARY",
                    "These replay summaries have complete input admission "
                            + "and an operational requested output slice, "
                            + "but intentionally retain unresolved relational "
                            + "heap details: " + replay.partialRoles + "."));
        }
        if (!runtime.confirmedSasl) {
            if (!bool(allowed, "allowMissingRuntimeEquality", false)) {
                throw gap("MISSING_RUNTIME_SASL_EQUALITY_NOT_AUTHORIZED");
            }
            result.add(approximation("MISSING_RUNTIME_SASL_EQUALITY",
                    "No confirmed SASL equality edge was available; the "
                            + "configured codec contract supplies bootstrap "
                            + "equality only."));
        }
        if (!runtime.confirmedShared) {
            if (!bool(allowed, "allowMissingRuntimeEquality", false)) {
                throw gap("MISSING_RUNTIME_SHARED_STATE_NOT_AUTHORIZED");
            }
            result.add(approximation("MISSING_RUNTIME_SHARED_STATE_EDGE",
                    "No exact selected shared-state edge was available; "
                            + "the one-witness ordering remains explicit."));
        }
        return result;
    }

    private static ReplayEvidence selectReplaySummaries(
            List<Path> paths, Map<String, JsonObject> regions,
            JsonObject approximationPolicy, TargetQueryEvidence targetQuery)
            throws IOException {
        final Map<String, List<ReplayCandidate>> candidates =
                new LinkedHashMap<>();
        final Map<String, String> roleByRegion = new LinkedHashMap<>();
        for (String role : REGION_ROLES) {
            candidates.put(role, new ArrayList<ReplayCandidate>());
            roleByRegion.put(string(regions.get(role), "regionId"), role);
        }

        JsonArray artifacts = new JsonArray();
        for (final Path path : paths) {
            final JsonObject sourceArtifact = artifact(path);
            artifacts.add(sourceArtifact.deepCopy());
            forEachJsonl(path, new JsonConsumer() {
                @Override
                public void accept(JsonObject row) {
                    String role = roleByRegion.get(string(row, "regionId"));
                    if (role != null) {
                        candidates.get(role).add(new ReplayCandidate(
                                row.deepCopy(), sourceArtifact.deepCopy()));
                    }
                }
            });
        }

        ReplayEvidence result = new ReplayEvidence(artifacts);
        for (String role : REGION_ROLES) {
            List<ReplayCandidate> matches = candidates.get(role);
            if (matches.size() != 1) {
                throw gap("REPLAY_SUMMARY_CARDINALITY:" + role + ":"
                        + matches.size());
            }
            ReplayCandidate candidate = matches.get(0);
            JsonObject summary = "target".equals(role)
                    ? applyTargetQuery(candidate.summary, targetQuery)
                    : candidate.summary;
            boolean guardedMerge = "GUARDED_PATH_MERGE".equals(string(
                    object(summary, "regionRelation"), "kind"));
            int guardCount = replayGuardExpressionCount(summary);
            int outputCount = replayOutputExpressionCount(summary);
            boolean relationallyComplete = bool(summary,
                    "relationallyComplete", false);
            boolean partialReplayAuthorized = !relationallyComplete
                    && bool(approximationPolicy,
                    "allowOperationallyAdmittedPartialReplaySummaries",
                    false)
                    && arrayContains(array(approximationPolicy,
                    "allowedPartialReplayRoles"), role)
                    && bool(summary,
                    "requestedOutputSliceOperationallyAdmitted", false)
                    && bool(object(summary,
                    "inputMaterializationAdmission"), "complete", false);
            if (string(summary, "summaryId").isEmpty()
                    || string(summary, "activationId").isEmpty()
                    || !string(regions.get(role), "rootMethod").equals(
                    string(summary, "rootMethod"))
                    || !bool(summary, "valid", false)
                    || (!relationallyComplete && !partialReplayAuthorized)
                    || !summary.has("pathCondition")
                    || !summary.get("pathCondition").isJsonArray()
                    || !summary.has("outputExpressions")
                    || !summary.get("outputExpressions").isJsonObject()
                    || outputCount == 0
                    || guardedMerge && !bool(object(summary,
                    "regionRelation"), "complete", false)
                    || summary.has("protocolModel")) {
                throw gap("REPLAY_SUMMARY_NOT_IMPORTED_RELATIONAL_"
                        + "TRANSFORMER:" + role);
            }
            JsonObject selected = new JsonObject();
            selected.addProperty("summaryId", string(summary,
                    "summaryId"));
            selected.addProperty("activationId", string(summary,
                    "activationId"));
            selected.addProperty("regionId", string(summary, "regionId"));
            selected.addProperty("rootMethod", string(summary,
                    "rootMethod"));
            selected.addProperty("engine", string(summary, "engine"));
            selected.addProperty("valid", true);
            selected.addProperty("relationallyComplete",
                    relationallyComplete);
            selected.addProperty("partialReplayAdmitted",
                    partialReplayAuthorized);
            if (partialReplayAuthorized) {
                selected.addProperty("partialReplayAuthority",
                        "CONFIGURED_OPERATIONAL_OUTPUT_SLICE_PLUS_COMPLETE_"
                                + "INPUT_ADMISSION_V1");
                result.partialRoles.add(role);
            }
            selected.addProperty("guardedPathMerge", guardedMerge);
            selected.addProperty("directedFatalBranchQueryApplied",
                    "target".equals(role));
            selected.addProperty("pathConditionCount", guardCount);
            selected.addProperty("outputExpressionCount", outputCount);
            selected.add("pathCondition",
                    array(summary, "pathCondition").deepCopy());
            selected.add("outputExpressions",
                    object(summary, "outputExpressions").deepCopy());
            if (summary.has("regionRelation")) {
                selected.add("regionRelation",
                        summary.get("regionRelation").deepCopy());
            }
            selected.add("sourceArtifact", candidate.artifact.deepCopy());
            result.catalog.add(role, selected);
            result.orderedSummaries.add(summary);
        }
        return result;
    }

    private static TargetQueryEvidence selectTargetQuery(Path path,
            JsonObject targetRegion, JsonObject targetGuard)
            throws IOException {
        final List<JsonObject> matches = new ArrayList<>();
        forEachJsonl(path, new JsonConsumer() {
            @Override
            public void accept(JsonObject row) {
                if (string(targetRegion, "regionId").equals(
                        string(row, "regionId"))
                        && string(targetGuard, "siteId").equals(
                        string(row, "siteId"))) {
                    matches.add(row.deepCopy());
                }
            }
        });
        if (matches.size() != 1) {
            throw gap("DIRECTED_TARGET_QUERY_CARDINALITY:"
                    + matches.size());
        }
        JsonObject query = matches.get(0);
        boolean desired = bool(targetGuard, "requiredOutcome", false);
        if (string(query, "activationId").isEmpty()
                || string(query, "regionInstanceId").isEmpty()
                || !query.has("observedOutcome")
                || !query.has("desiredOutcome")
                || bool(query, "observedOutcome", desired) == desired
                || bool(query, "desiredOutcome", !desired) != desired
                || !bool(query, "readyForSolver", false)
                || integer(query, "conditionIndex", -1) < 0
                || !"KEEP_CONDITIONS_BEFORE_TARGET".equals(string(query,
                "prefixPolicy"))
                || !"NEGATE_TARGET_CONDITION".equals(string(query,
                "targetPolicy"))
                || !"DROP_OLD_SUFFIX".equals(string(query,
                "suffixPolicy"))
                || !query.has("originalTargetCondition")
                || !query.has("negatedTargetCondition")
                || array(query, "constraints").size() == 0
                || !"MAP_LOOKUP_ABSENCE".equals(string(
                object(query, "semanticModel"), "theory"))
                || object(object(query, "semanticModel"),
                "keyExpression").size() == 0) {
            throw gap("DIRECTED_TARGET_QUERY_NOT_SOLVER_READY");
        }
        JsonObject catalog = selected(query, "activationId", "regionId",
                "regionInstanceId", "siteId", "occurrence",
                "observedOutcome", "desiredOutcome", "conditionIndex",
                "prefixPolicy", "targetPolicy", "suffixPolicy",
                "readyForSolver", "readyForReplay", "semanticModel");
        catalog.addProperty("targetReplayValidated",
                bool(query, "targetReplayValidated", false));
        catalog.addProperty("branchFlipAppliedToSmt", true);
        catalog.add("sourceArtifact", artifact(path));
        return new TargetQueryEvidence(query, catalog);
    }

    private static JsonObject applyTargetQuery(JsonObject source,
            TargetQueryEvidence evidence) throws IOException {
        JsonObject query = evidence.query;
        if (!string(source, "activationId").equals(
                string(query, "activationId"))
                || !string(source, "regionId").equals(
                string(query, "regionId"))) {
            throw gap("DIRECTED_TARGET_QUERY_SUMMARY_IDENTITY_MISMATCH");
        }
        JsonArray original = array(source, "pathCondition");
        JsonArray constraints = array(query, "constraints");
        int conditionIndex = integer(query, "conditionIndex", -1);
        if (conditionIndex >= original.size()
                || constraints.size() != conditionIndex + 1
                || !original.get(conditionIndex).equals(
                query.get("originalTargetCondition"))
                || !constraints.get(conditionIndex).equals(
                query.get("negatedTargetCondition"))) {
            throw gap("DIRECTED_TARGET_QUERY_CONDITION_MISMATCH");
        }
        for (int index = 0; index < conditionIndex; index++) {
            if (!original.get(index).equals(constraints.get(index))) {
                throw gap("DIRECTED_TARGET_QUERY_PREFIX_MISMATCH:" + index);
            }
        }
        JsonObject result = source.deepCopy();
        result.add("pathCondition", constraints.deepCopy());
        result.add("directedTargetQuery", query.deepCopy());
        result.addProperty("directedFatalBranchQueryApplied", true);
        result.addProperty("targetReplayValidated",
                bool(query, "targetReplayValidated", false));
        return result;
    }

    private static int replayGuardExpressionCount(JsonObject summary) {
        JsonObject relation = object(summary, "regionRelation");
        if (!"GUARDED_PATH_MERGE".equals(string(relation, "kind"))) {
            return array(summary, "pathCondition").size();
        }
        int result = 0;
        for (JsonElement element : array(relation, "cases")) {
            if (element.isJsonObject()) {
                result += array(object(element.getAsJsonObject(), "guard"),
                        "conditions").size();
            }
        }
        return result;
    }

    private static boolean arrayContains(JsonArray values, String expected) {
        for (JsonElement value : values) {
            if (value.isJsonPrimitive()
                    && expected.equals(value.getAsString())) {
                return true;
            }
        }
        return false;
    }

    private static int replayOutputExpressionCount(JsonObject summary) {
        JsonObject relation = object(summary, "regionRelation");
        if (!"GUARDED_PATH_MERGE".equals(string(relation, "kind"))) {
            return object(summary, "outputExpressions").size();
        }
        int result = 0;
        for (JsonElement element : array(relation, "cases")) {
            if (element.isJsonObject()) {
                result += object(element.getAsJsonObject(),
                        "outputExpressions").size();
            }
        }
        return result;
    }

    private static void validateReplayFormulaFragment(
            ConcolicSmtComposer.SummaryFormulaFragment fragment,
            int expectedSummaryCount) throws IOException {
        JsonObject catalog = fragment.catalog;
        if (integer(catalog, "summaryCount", -1) != expectedSummaryCount
                || integer(catalog, "guardExpressionCount", 0) <= 0
                || integer(catalog, "outputExpressionCount", 0)
                < expectedSummaryCount
                || integer(catalog, "assertionCount", 0) <= 0
                || bool(catalog, "containsSolverCommand", true)
                || fragment.smtLib.contains("(check-sat)")) {
            throw gap("REPLAY_FORMULA_FRAGMENT_INCOMPLETE");
        }
        for (JsonElement element : array(catalog,
                "summaryProjections")) {
            if (!element.isJsonObject()
                    || integer(element.getAsJsonObject(),
                    "emittedAssertionCount", 0) <= 0) {
                throw gap("REPLAY_SUMMARY_EMITTED_NO_SMT_ASSERTION");
            }
        }
    }

    private static String renderSmt(Map<String, JsonObject> regions,
            Map<String, JsonObject> ports, JsonObject keyBinding,
            JsonObject expiryBinding,
            ReplayEvidence replayEvidence,
            ConcolicSmtComposer.SummaryFormulaFragment replayFormulas,
            TargetQueryEvidence targetQuery) throws IOException {
        JsonObject namenodeSummary = replaySummary(replayEvidence,
                regionId(regions, "namenode"));
        String namenodeKeyRaw = uniqueHeapEffectExpression(
                namenodeSummary, "MAP_PUT", "keyExpression", "Int");
        String namenodeKeyTerm = summarySolverSymbol(replayFormulas,
                regionId(regions, "namenode"), namenodeKeyRaw,
                "NAMENODE_MAP_PUT_KEY");
        String targetKeyRaw = string(object(object(targetQuery.query,
                "semanticModel"), "keyExpression"), "_exp");
        String targetKeyTerm = summarySolverSymbol(replayFormulas,
                string(regions.get("target"), "regionId"), targetKeyRaw,
                "TARGET_LOOKUP_KEY");
        String targetMapPort = smtPort(ports.get("targetMap"));
        String targetEncodedKeyPort = smtPort(
                ports.get("targetEncodedKey"));
        String targetFailurePort = smtPort(ports.get("targetFailure"));
        String namenodeExpiryPort = smtPort(ports.get("namenodeExpiry"));
        String datanodeMapPostPort = smtPort(
                ports.get("datanodeMapPost"));
        String datanodeEntryKeyPort = smtPort(
                ports.get("datanodeEntryKey"));
        String datanodeEntryExpiryPort = smtPort(
                ports.get("datanodeEntryExpiry"));
        String keyUpdaterCurrentKeyPort = smtPort(
                ports.get("keyUpdaterCurrentKey"));
        String balancerCachedKeyPort = smtPort(
                ports.get("balancerCachedKey"));
        String balancerUsernamePort = smtPort(
                ports.get("balancerSaslUsername"));
        StringBuilder out = new StringBuilder();
        out.append("; Auto-generated approximate HDFS-11741 bootstrap model\n");
        out.append("; target region: ").append(regionId(regions, "target"))
                .append(" map port: ").append(portId(ports.get("targetMap")))
                .append('\n');
        out.append("; NameNode region: ").append(regionId(regions,
                "namenode")).append("; DataNode region: ").append(
                regionId(regions, "datanode")).append("; Balancer region: ")
                .append(regionId(regions, "balancer")).append('\n');
        out.append("; key binding: ").append(string(keyBinding,
                "bindingId")).append("; expiry binding: ").append(
                string(expiryBinding, "bindingId")).append('\n');
        out.append("(set-option :produce-models true)\n");
        out.append("; Imported concolic guards and output transformers follow.\n");
        out.append(replayFormulas.smtLib);
        if (!replayFormulas.smtLib.endsWith("\n")) out.append('\n');
        out.append("; Explicit one-DN HDFS transport/outer-loop contracts follow.\n");
        ensureDeclaration(out, targetMapPort, "MapState");
        ensureDeclaration(out, datanodeMapPostPort, "MapState");
        ensureDeclaration(out, targetEncodedKeyPort, "Value");
        ensureDeclaration(out, balancerUsernamePort, "Value");
        ensureDeclaration(out, targetFailurePort, "Value");
        ensureDeclaration(out, keyUpdaterCurrentKeyPort, "Value");
        ensureScalarPort(out, replayFormulas.smtLib, namenodeExpiryPort);
        ensureScalarPort(out, replayFormulas.smtLib,
                datanodeEntryKeyPort);
        ensureScalarPort(out, replayFormulas.smtLib,
                datanodeEntryExpiryPort);
        ensureScalarPort(out, replayFormulas.smtLib,
                balancerCachedKeyPort);
        out.append("(declare-const nn_snapshot_keys (Array Int Bool))\n");
        out.append("(declare-const nn_snapshot_expiry (Array Int Int))\n");
        out.append("(declare-const nn_snapshot_key_id Int)\n");
        out.append("(declare-const nn_snapshot_key_expiry Int)\n");
        out.append("(declare-const nn_later_current_key_id Int)\n");
        out.append("(declare-const cache_time Int)\n");
        out.append("(declare-const remove_now Int)\n");
        out.append("(declare-const send_time Int)\n");
        out.append("(declare-const observation_time Int)\n");
        out.append("(declare-const old_block_key_expiry Int)\n");
        out.append("(declare-const cached_dek_expiry Int)\n");
        out.append("(declare-const balancer_cached_key_id Int)\n");
        out.append("(declare-const balancer_cached_key_after_update Int)\n");
        out.append("(declare-const dn_received_key_id Int)\n");
        out.append("(declare-const dn_received_key_expiry Int)\n");
        out.append("(declare-const dn_iterator_key_id Int)\n");
        out.append("(declare-const dn_keys_before_add (Array Int Bool))\n");
        out.append("(declare-const dn_keys_after_add (Array Int Bool))\n");
        out.append("(declare-const dn_keys_after_remove (Array Int Bool))\n");
        out.append("(declare-const dn_keys_at_target (Array Int Bool))\n");
        out.append("(declare-const dn_expiry_before_add (Array Int Int))\n");
        out.append("(declare-const dn_expiry_after_add (Array Int Int))\n");
        out.append("(declare-const sasl_client_key_id Int)\n");
        out.append("(declare-const sasl_server_key_id Int)\n");
        out.append("(declare-const lookup_key_id Int)\n");
        out.append("(declare-const exception_reached Bool)\n");
        out.append("(declare-fun hdfs_block_key_id (Value) Int)\n");
        out.append("(declare-fun hdfs_username_key_id (Value) Int)\n");

        named(out, "summary_nn_map_put_key_to_hdfs_contract",
                "(= nn_snapshot_key_id " + namenodeKeyTerm + ")");
        named(out, "summary_nn_expiry_to_hdfs_contract",
                "(= nn_snapshot_key_expiry "
                        + scalarWitness(namenodeExpiryPort) + ")");
        named(out, "summary_key_updater_output_to_hdfs_contract",
                "(= (hdfs_block_key_id " + keyUpdaterCurrentKeyPort
                        + ") nn_snapshot_key_id)");
        named(out, "summary_dn_key_to_hdfs_contract",
                "(= dn_received_key_id "
                        + scalarWitness(datanodeEntryKeyPort) + ")");
        named(out, "summary_dn_expiry_to_hdfs_contract",
                "(= dn_received_key_expiry "
                        + scalarWitness(datanodeEntryExpiryPort) + ")");
        named(out, "summary_balancer_cache_to_hdfs_contract",
                "(= balancer_cached_key_id "
                        + scalarWitness(balancerCachedKeyPort) + ")");
        named(out, "summary_dispatcher_username_to_target_input",
                "(= " + balancerUsernamePort + " "
                        + targetEncodedKeyPort + ")");
        named(out, "summary_dispatcher_username_codec_bridge",
                "(= (hdfs_username_key_id " + balancerUsernamePort
                        + ") balancer_cached_key_id)");
        named(out, "summary_target_username_codec_bridge",
                "(= (hdfs_username_key_id " + targetEncodedKeyPort
                        + ") " + targetKeyTerm + ")");
        named(out, "summary_target_lookup_key_to_hdfs_contract",
                "(= lookup_key_id " + targetKeyTerm + ")");
        // The original replay exited normally.  This port is therefore an
        // adapter projection of the directed fatal query, not a replay-
        // emitted exception observation.
        named(out, "directed_fatal_query_synthetic_output",
                "(= " + targetFailurePort
                        + " (VBool exception_reached))");

        named(out, "nn_snapshot_contains_symbolic_entry",
                "(select nn_snapshot_keys nn_snapshot_key_id)");
        named(out, "nn_snapshot_expiry_projection",
                "(= nn_snapshot_key_expiry (select nn_snapshot_expiry "
                        + "nn_snapshot_key_id))");
        named(out, "old_block_key_expiry_projection",
                "(= old_block_key_expiry nn_snapshot_key_expiry)");
        named(out, "cache_created_before_expiry",
                "(and (< cache_time old_block_key_expiry) "
                        + "(< cache_time cached_dek_expiry))");
        named(out, "nn_rotates_to_different_key",
                "(distinct nn_later_current_key_id nn_snapshot_key_id)");
        named(out, "nn_to_balancer_snapshot_key",
                "(= balancer_cached_key_id nn_snapshot_key_id)");
        named(out, "pre_fix_cache_survives_block_key_update",
                "(= balancer_cached_key_after_update "
                        + "balancer_cached_key_id)");
        named(out, "nn_to_datanode_snapshot_key",
                "(= dn_received_key_id nn_snapshot_key_id)");
        named(out, "nn_to_datanode_snapshot_expiry",
                "(= dn_received_key_expiry nn_snapshot_key_expiry)");
        named(out, "datanode_adds_snapshot_entry",
                "(= dn_keys_after_add (store dn_keys_before_add "
                        + "dn_received_key_id true))");
        named(out, "datanode_adds_snapshot_expiry",
                "(= dn_expiry_after_add (store dn_expiry_before_add "
                        + "dn_received_key_id dn_received_key_expiry))");
        named(out, "summary_dn_post_map_membership_bridge",
                "(= (select dn_keys_after_add dn_received_key_id) "
                        + "(map_has " + datanodeMapPostPort
                        + " (VMapInteger dn_received_key_id)))");

        // One iterator entry is bounded, but its key and expiry remain fully
        // symbolic.  This is the inner loop semantics that must not collapse
        // to a concrete workload value.
        named(out, "iterator_selects_relevant_symbolic_entry",
                "(= dn_iterator_key_id dn_received_key_id)");
        named(out, "iterator_entry_is_present_before_remove",
                "(select dn_keys_after_add dn_iterator_key_id)");
        named(out, "iterator_entry_expired",
                "(< (select dn_expiry_after_add dn_iterator_key_id) "
                        + "remove_now)");
        named(out, "datanode_removes_expired_symbolic_entry",
                "(= dn_keys_after_remove (store dn_keys_after_add "
                        + "dn_iterator_key_id false))");
        named(out, "outer_loop_order_cache_remove_send",
                "(and (< cache_time remove_now) (< remove_now send_time) "
                        + "(= observation_time send_time))");
        named(out, "old_block_key_expired_at_observation",
                "(< old_block_key_expiry observation_time)");
        named(out, "cached_dek_expired_but_still_reused",
                "(< cached_dek_expiry observation_time)");
        named(out, "no_readd_in_selected_outer_loop_witness",
                "(= dn_keys_at_target dn_keys_after_remove)");
        named(out, "balancer_cache_to_sasl_client",
                "(= sasl_client_key_id balancer_cached_key_after_update)");
        named(out, "sasl_codec_round_trip_to_server",
                "(= sasl_server_key_id sasl_client_key_id)");
        named(out, "sasl_server_to_lookup_key",
                "(= lookup_key_id sasl_server_key_id)");
        named(out, "target_map_lookup_miss_definition",
                "(= exception_reached (not (select dn_keys_at_target "
                        + "lookup_key_id)))");
        named(out, "summary_target_map_membership_bridge",
                "(= (select dn_keys_at_target lookup_key_id) "
                        + "(map_has " + targetMapPort
                        + " (VMapInteger lookup_key_id)))");
        named(out, "reach_invalid_encryption_key_exception",
                "exception_reached");
        out.append("(check-sat)\n");
        out.append("(get-model)\n");
        out.append("(get-value (exception_reached nn_snapshot_key_id "
                + "old_block_key_expiry cached_dek_expiry observation_time "
                + "remove_now balancer_cached_key_id sasl_server_key_id "
                + "lookup_key_id))\n");
        return out.toString();
    }

    private static String summarySolverSymbol(
            ConcolicSmtComposer.SummaryFormulaFragment fragment,
            String regionId, String rawSymbol, String label)
            throws IOException {
        List<String> matches = new ArrayList<>();
        for (JsonElement projectionElement : array(fragment.catalog,
                "summaryProjections")) {
            if (!projectionElement.isJsonObject()) continue;
            JsonObject projection = projectionElement.getAsJsonObject();
            if (!regionId.equals(string(projection, "regionId"))) continue;
            for (JsonElement bindingElement : array(projection,
                    "emittedSymbolBindings")) {
                if (!bindingElement.isJsonObject()) continue;
                JsonObject binding = bindingElement.getAsJsonObject();
                if (rawSymbol.equals(string(binding, "rawSymbol"))
                        && "Int".equals(string(binding, "sort"))) {
                    matches.add(string(binding, "solverSymbol"));
                }
            }
        }
        if (rawSymbol.isEmpty() || matches.size() != 1
                || matches.get(0).isEmpty()) {
            throw gap(label + "_SOLVER_SYMBOL_CARDINALITY:"
                    + matches.size());
        }
        return matches.get(0);
    }

    private static JsonObject replaySummary(ReplayEvidence evidence,
            String regionId) throws IOException {
        List<JsonObject> matches = new ArrayList<>();
        for (JsonObject summary : evidence.orderedSummaries) {
            if (regionId.equals(string(summary, "regionId"))) {
                matches.add(summary);
            }
        }
        if (matches.size() != 1) {
            throw gap("REPLAY_SUMMARY_REGION_CARDINALITY:" + regionId
                    + ":" + matches.size());
        }
        return matches.get(0);
    }

    /**
     * Selects a unique raw symbolic leaf from the real heap transformer.  The
     * HDFS adapter knows that the snapshot entry is introduced by MAP_PUT,
     * but deliberately does not know an engine-generated symbol name.
     */
    private static String uniqueHeapEffectExpression(JsonObject summary,
            String effectKind, String expressionField, String solverSort)
            throws IOException {
        Set<String> rawSymbols = new LinkedHashSet<>();
        for (JsonElement element : array(summary, "heapEffects")) {
            if (!element.isJsonObject()) continue;
            JsonObject effect = element.getAsJsonObject();
            if (!effectKind.equals(string(effect, "kind"))) continue;
            JsonObject expression = object(effect, expressionField);
            String raw = string(expression, "_exp");
            if (!raw.isEmpty() && expressionSort(expression).equals(
                    solverSort)) {
                rawSymbols.add(raw);
            }
        }
        if (rawSymbols.size() != 1) {
            throw gap("HEAP_EFFECT_" + effectKind + "_"
                    + expressionField.toUpperCase() + "_CARDINALITY:"
                    + rawSymbols.size());
        }
        return rawSymbols.iterator().next();
    }

    private static String expressionSort(JsonObject expression) {
        String javaType = firstNonBlank(string(expression, "_java_type"),
                string(expression, "javaType"));
        if ("I".equals(javaType) || "J".equals(javaType)
                || "S".equals(javaType) || "B".equals(javaType)
                || "C".equals(javaType)
                || "java/lang/Integer".equals(javaType)
                || "java.lang.Integer".equals(javaType)
                || "java/lang/Long".equals(javaType)
                || "java.lang.Long".equals(javaType)) {
            return "Int";
        }
        return "Ref";
    }

    private static String smtPort(JsonObject port) {
        return "port__" + smtName(portId(port));
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

    private static String scalarWitness(String portTerm) {
        return "sym__port__" + portTerm.substring("port__".length())
                + "__int";
    }

    private static void ensureDeclaration(StringBuilder out, String name,
                                          String sort) {
        String declaration = "(declare-const " + name + " " + sort + ")";
        if (out.indexOf(declaration) < 0) out.append(declaration)
                .append('\n');
    }

    private static void ensureScalarPort(StringBuilder out,
            String replaySmt, String portTerm) {
        ensureDeclaration(out, portTerm, "Value");
        String witness = scalarWitness(portTerm);
        ensureDeclaration(out, witness, "Int");
        String binding = "(= " + portTerm + " (VInt " + witness + "))";
        if (!replaySmt.contains(binding)) {
            named(out, "hdfs_scalar_port_bridge_" + smtName(portTerm),
                    binding);
        }
    }

    private static void named(StringBuilder out, String name,
                              String formula) {
        out.append("(assert (! ").append(formula).append(" :named ")
                .append(name).append("))\n");
    }

    private static JsonObject selectedRegionCatalog(
            Map<String, JsonObject> regions) {
        JsonObject result = new JsonObject();
        for (String role : REGION_ROLES) {
            JsonObject region = regions.get(role);
            JsonObject selected = new JsonObject();
            selected.addProperty("regionId", string(region, "regionId"));
            selected.addProperty("rootMethod", string(region,
                    "rootMethod"));
            selected.addProperty("anchorMethod", string(region,
                    "anchorMethod"));
            selected.addProperty("truncated", bool(region, "truncated",
                    false));
            result.add(role, selected);
        }
        return result;
    }

    private static JsonObject selectedPortCatalog(
            Map<String, JsonObject> ports) {
        JsonObject result = new JsonObject();
        for (String role : PORT_ROLES) {
            JsonObject port = ports.get(role);
            JsonObject selected = new JsonObject();
            selected.addProperty("regionRole", string(port, "regionRole"));
            selected.addProperty("regionId", string(port, "regionId"));
            selected.addProperty("collection", string(port, "collection"));
            selected.addProperty("portId", portId(port));
            selected.addProperty("cell", string(port, "cell"));
            result.add(role, selected);
        }
        return result;
    }

    private static JsonArray summaryContractBridgeCatalog() {
        JsonArray result = new JsonArray();
        bridge(result, "summary_nn_map_put_key_to_hdfs_contract",
                "EMITTED_HEAP_EFFECT_SYMBOL");
        bridge(result, "summary_nn_expiry_to_hdfs_contract",
                "EMITTED_SCALAR_INPUT_PORT");
        bridge(result, "summary_key_updater_output_to_hdfs_contract",
                "EMITTED_OUTPUT_PORT_PLUS_CONFIGURED_HDFS_FIELD_PROJECTION");
        bridge(result, "summary_dn_key_to_hdfs_contract",
                "EMITTED_SCALAR_INPUT_PORT");
        bridge(result, "summary_dn_expiry_to_hdfs_contract",
                "STATIC_PORT_OUTER_LOOP_APPROXIMATION");
        bridge(result, "summary_balancer_cache_to_hdfs_contract",
                "STATIC_PORT_HDFS_ADAPTER");
        bridge(result, "summary_dispatcher_username_to_target_input",
                "POLICY_SELECTED_TRANSPORT_ENDPOINT_EQUALITY");
        bridge(result, "summary_dispatcher_username_codec_bridge",
                "CONFIGURED_HDFS_CODEC_ADAPTER");
        bridge(result, "summary_target_username_codec_bridge",
                "CONFIGURED_HDFS_CODEC_ADAPTER_PLUS_EMITTED_TARGET_KEY");
        bridge(result, "summary_target_lookup_key_to_hdfs_contract",
                "EMITTED_TARGET_LOOKUP_KEY_SYMBOL");
        bridge(result, "summary_dn_post_map_membership_bridge",
                "EMITTED_HEAP_STATE_OUTPUT_PORT");
        bridge(result, "summary_target_map_membership_bridge",
                "EMITTED_TARGET_MAP_INPUT_PORT");
        return result;
    }

    private static void bridge(JsonArray catalog, String assertion,
            String authority) {
        JsonObject item = new JsonObject();
        item.addProperty("assertion", assertion);
        item.addProperty("authority", authority);
        catalog.add(item);
    }

    private static JsonObject inputArtifacts(Arguments arguments)
            throws IOException {
        JsonObject artifacts = new JsonObject();
        artifacts.add("policy", artifact(arguments.policy));
        artifacts.add("regions", artifact(arguments.regions));
        artifacts.add("staticGraph", artifact(arguments.staticGraph));
        artifacts.add("regionEdges", artifact(arguments.regionEdges));
        artifacts.add("runtimeEdgeValidations",
                artifact(arguments.runtimeEdges));
        artifacts.add("runtimeSummary", artifact(arguments.runtimeSummary));
        artifacts.add("activationPlan", artifact(arguments.activationPlan));
        artifacts.add("offlineProvenance",
                artifact(arguments.offlineProvenance));
        artifacts.add("directedFatalBranchQuery",
                artifact(arguments.targetQuery));
        JsonArray replay = new JsonArray();
        for (Path path : arguments.replaySummaries) {
            replay.add(artifact(path));
        }
        artifacts.add("replaySummaries", replay);
        return artifacts;
    }

    private static void validateRuntimeArtifacts(JsonObject policy,
            JsonObject summary, JsonObject provenance,
            JsonObject artifacts) throws IOException {
        if (integer(summary, "staticRegionCount", 0) <= 0
                || integer(summary, "staticRegionEdgeCount", 0) <= 0
                || integer(summary, "runtimeRegionInstanceCount", 0) <= 0
                || integer(summary, "runtimeRegionEdgeValidationCount", 0)
                <= 0
                || integer(summary, "activationCount", 0) <= 0) {
            throw gap("RUNTIME_SUMMARY_COUNTS_MISSING");
        }
        if (integer(summary, "truncatedCallTreeInstanceCount", -1) != 0
                || integer(summary, "skippedContainedCallCount", -1) != 0) {
            throw gap("RUNTIME_CALL_TREE_TRUNCATED");
        }
        boolean pathPrefixApproximation = bool(summary, "truncated", true);
        if (pathPrefixApproximation) {
            if (integer(summary, "truncatedPathSignatureInstanceCount", 0)
                    <= 0
                    || integer(summary, "skippedPathSignatureEventCount", 0)
                    <= 0) {
                throw gap("RUNTIME_TRUNCATION_IS_NOT_BOUNDED_PATH_PREFIX");
            }
        } else if (integer(summary,
                "truncatedPathSignatureInstanceCount", -1) != 0
                || integer(summary, "skippedPathSignatureEventCount", -1)
                != 0) {
            throw gap("EXACT_RUNTIME_SUMMARY_HAS_SKIPPED_PATH_EVENTS");
        }

        if (integer(provenance, "schemaVersion", -1) != 2
                || !bool(provenance, "complete", false)
                || !bool(provenance, "aggregationComplete", false)
                || bool(provenance, "replayJvmAggregation", true)
                || !string(policy, "workload").equals(
                string(provenance, "test"))) {
            throw gap("OFFLINE_PROVENANCE_NOT_FROZEN_FOR_WORKLOAD");
        }
        requireArtifactHash(provenance, "staticGraphSha256", artifacts,
                "staticGraph");
        requireArtifactHash(provenance, "symbolicRegionsSha256", artifacts,
                "regions");
        requireArtifactHash(provenance, "symbolicRegionEdgesSha256",
                artifacts, "regionEdges");
        requireArtifactHash(provenance, "runtimeRegionSummarySha256",
                artifacts, "runtimeSummary");

        if (bool(provenance, "runtimePathEvidenceComplete", false)
                == pathPrefixApproximation) {
            throw gap("RUNTIME_PATH_COMPLETENESS_DISAGREES_WITH_SUMMARY");
        }
        JsonObject recordedApproximation = object(provenance,
                "outerLoopPathSignatureApproximation");
        if (bool(recordedApproximation, "applied", false)
                != pathPrefixApproximation) {
            throw gap("OUTER_LOOP_APPROXIMATION_DISAGREES_WITH_SUMMARY");
        }
        if (pathPrefixApproximation) {
            JsonObject allowed = object(policy, "approximationPolicy");
            if (!string(allowed, "outerLoopAuthority").equals(
                    string(recordedApproximation, "authority"))) {
                throw gap("OUTER_LOOP_APPROXIMATION_AUTHORITY_MISMATCH");
            }
            Set<String> expectedRoots = stringSet(array(allowed,
                    "allowedOuterLoopRootMethods"));
            Set<String> recordedRoots = stringSet(array(
                    recordedApproximation, "allowedRootMethods"));
            if (!expectedRoots.equals(recordedRoots)) {
                throw gap("OUTER_LOOP_APPROXIMATION_ROOTS_MISMATCH");
            }
            if (integer(recordedApproximation, "truncatedInstanceCount", 0)
                    != integer(summary,
                    "truncatedPathSignatureInstanceCount", -1)
                    || integer(recordedApproximation,
                    "skippedPathEventCount", 0) != integer(summary,
                    "skippedPathSignatureEventCount", -1)) {
                throw gap("OUTER_LOOP_APPROXIMATION_COUNTS_MISMATCH");
            }
        }
    }

    private static void requireArtifactHash(JsonObject provenance,
            String provenanceField, JsonObject artifacts,
            String artifactRole) throws IOException {
        String expected = string(object(artifacts, artifactRole), "sha256");
        String recorded = string(provenance, provenanceField);
        if (expected.isEmpty() || !expected.equals(recorded)) {
            throw gap("PROVENANCE_HASH_MISMATCH:" + artifactRole);
        }
    }

    private static JsonObject selectedMetadata(JsonObject source) {
        JsonObject result = new JsonObject();
        for (String field : Arrays.asList("schemaVersion", "kind", "mode",
                "complete", "truncated", "contextPairTruncated",
                "aggregationComplete", "runtimePathEvidenceComplete",
                "runtimeRegionInstanceCount", "runtimeRegionEdgeValidationCount",
                "activationCount", "test", "workload")) {
            if (source.has(field)) result.add(field,
                    source.get(field).deepCopy());
        }
        if (source.has("outerLoopPathSignatureApproximation")) {
            result.add("outerLoopPathSignatureApproximation", source.get(
                    "outerLoopPathSignatureApproximation").deepCopy());
        }
        return result;
    }

    private static JsonObject minimalEdge(JsonObject edge) {
        return selected(edge, "id", "method", "kind", "transferKind",
                "relation", "fromCell", "toCell", "siteId",
                "structuredEncoding", "dependencyAuthority");
    }

    private static JsonObject minimalRegionEdge(JsonObject edge) {
        return selected(edge, "edgeId", "fromRegion", "fromPort",
                "fromOutputPort", "toRegion", "toPort", "kind",
                "mappingKind", "candidateRelation", "mappingAuthority");
    }

    private static JsonObject minimalRuntimeEdge(JsonObject edge) {
        return selected(edge, "edgeId", "fromRegion", "fromPort",
                "toRegion", "toPort", "kind", "mappingKind", "status",
                "confirmedReadFromPairCount",
                "confirmedValueEqualityPairCount", "validatedBindingCount",
                "valueEqualityAuthority", "endpointOrderAuthority");
    }

    private static JsonObject minimalActivation(JsonObject row) {
        return selected(row, "activationId", "regionId",
                "regionInstanceId", "rootCallId", "invocationOrdinal",
                "process", "threadId", "test", "replayable",
                "fullyObserved", "validationStatus");
    }

    private static JsonObject selected(JsonObject source,
                                       String... fields) {
        JsonObject result = new JsonObject();
        for (String field : fields) {
            if (source.has(field)) result.add(field,
                    source.get(field).deepCopy());
        }
        return result;
    }

    private static long activationOrder(JsonObject row) {
        long root = longInteger(row, "rootCallId", Long.MAX_VALUE);
        return root == Long.MAX_VALUE
                ? longInteger(row, "invocationOrdinal", Long.MAX_VALUE)
                : root;
    }

    private static JsonObject approximation(String id, String reason) {
        JsonObject result = new JsonObject();
        result.addProperty("id", id);
        result.addProperty("kind", "EXPLICIT_BOOTSTRAP_APPROXIMATION");
        result.addProperty("reason", reason);
        result.addProperty("includedInSmt", true);
        result.addProperty("eligibleForAutomaticDerivation", false);
        return result;
    }

    private static JsonObject mapToJson(Map<String, String> values) {
        JsonObject result = new JsonObject();
        for (Map.Entry<String, String> entry : values.entrySet()) {
            result.addProperty(entry.getKey(), entry.getValue());
        }
        return result;
    }

    private static Set<String> regionIds(Map<String, JsonObject> regions) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonObject region : regions.values()) result.add(string(region,
                "regionId"));
        return result;
    }

    private static String regionId(Map<String, JsonObject> regions,
                                   String role) {
        return string(regions.get(role), "regionId");
    }

    private static String portId(JsonObject port) {
        return firstNonBlank(string(port, "portId"), string(port, "symbol"));
    }

    private static int countAssertions(String smt) {
        int count = 0;
        int offset = 0;
        while ((offset = smt.indexOf("(assert ", offset)) >= 0) {
            count++;
            offset += 8;
        }
        return count;
    }

    private static Set<String> difference(Set<String> expected,
                                          Set<String> actual) {
        Set<String> result = new LinkedHashSet<>(expected);
        result.removeAll(actual);
        return result;
    }

    private static Set<String> stringSet(JsonArray values) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : values) {
            if (element.isJsonPrimitive()) result.add(element.getAsString());
        }
        return result;
    }

    private static void validateTargetGuard(JsonObject region,
            JsonObject selector) throws IOException {
        String site = string(selector, "siteId");
        int count = 0;
        for (JsonElement element : array(region, "branchPolicies")) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (site.equals(string(branch, "siteId"))
                    && !bool(branch, "requiredOutcome", true)) count++;
        }
        if (count != 1) throw gap("TARGET_FALSE_GUARD_CARDINALITY:" + count);
    }

    private static void requireStringArray(JsonObject owner, String field)
            throws IOException {
        JsonArray values = array(owner, field);
        if (values.size() == 0) throw gap("EMPTY_POLICY_ARRAY:" + field);
        for (JsonElement element : values) {
            if (!element.isJsonPrimitive()
                    || element.getAsString().trim().isEmpty()) {
                throw gap("MALFORMED_POLICY_ARRAY:" + field);
            }
        }
    }

    private static void requireText(JsonObject owner, String field,
                                    String label) throws IOException {
        if (string(owner, field).isEmpty()) throw gap(
                "MISSING_" + label.toUpperCase().replace(' ', '_'));
    }

    private static void require(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)
                || !Files.isReadable(path)) {
            throw new IOException(label + " not found: " + path);
        }
    }

    private static JsonObject readJson(Path path) throws IOException {
        JsonElement value = JsonParser.parseString(new String(
                Files.readAllBytes(path), StandardCharsets.UTF_8));
        if (!value.isJsonObject()) throw new IOException(
                "Expected JSON object: " + path);
        return value.getAsJsonObject();
    }

    private static void forEachJsonl(Path path, JsonConsumer consumer)
            throws IOException {
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            long lineNumber = 0;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                if (line.trim().isEmpty()) continue;
                JsonElement value;
                try {
                    value = JsonParser.parseString(line);
                } catch (RuntimeException exception) {
                    throw new IOException("Malformed JSONL " + path + ":"
                            + lineNumber, exception);
                }
                if (!value.isJsonObject()) throw new IOException(
                        "Expected JSON object at " + path + ":" + lineNumber);
                consumer.accept(value.getAsJsonObject());
            }
        }
    }

    private static void write(Path path, String value) throws IOException {
        Path parent = path.toAbsolutePath().normalize().getParent();
        if (parent != null) Files.createDirectories(parent);
        Files.write(path, value.getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING,
                StandardOpenOption.WRITE);
    }

    private static JsonObject artifact(Path path) throws IOException {
        MessageDigest digest;
        try {
            digest = MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException exception) {
            throw new IllegalStateException(exception);
        }
        long size = 0L;
        byte[] buffer = new byte[64 * 1024];
        try (InputStream input = Files.newInputStream(path)) {
            int read;
            while ((read = input.read(buffer)) >= 0) {
                if (read == 0) continue;
                digest.update(buffer, 0, read);
                size += read;
            }
        }
        JsonObject result = new JsonObject();
        result.addProperty("path",
                path.toAbsolutePath().normalize().toString());
        result.addProperty("sha256", hex(digest.digest()));
        result.addProperty("sizeBytes", size);
        return result;
    }

    private static JsonObject artifact(Path path, byte[] bytes) {
        JsonObject result = new JsonObject();
        result.addProperty("path",
                path.toAbsolutePath().normalize().toString());
        result.addProperty("sha256", sha256(bytes));
        result.addProperty("sizeBytes", bytes.length);
        return result;
    }

    private static String sha256(byte[] bytes) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] hash = digest.digest(bytes);
            return hex(hash);
        } catch (NoSuchAlgorithmException exception) {
            throw new IllegalStateException(exception);
        }
    }

    private static String hex(byte[] hash) {
        StringBuilder result = new StringBuilder();
        for (byte value : hash) result.append(String.format("%02x",
                value & 0xff));
        return result.toString();
    }

    private static JsonObject object(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static JsonArray array(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static String string(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull() ? ""
                    : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static boolean bool(JsonObject owner, String field,
                                boolean fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull() ? fallback
                    : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int integer(JsonObject owner, String field, int fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull() ? fallback
                    : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longInteger(JsonObject owner, String field,
                                    long fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull() ? fallback
                    : value.getAsLong();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) return value;
        }
        return "";
    }

    private static IOException gap(String reason) {
        return new IOException("HDFS_11741_BOOTSTRAP_GAP:" + reason);
    }

    private interface JsonConsumer {
        void accept(JsonObject object) throws IOException;
    }

    private static final class StaticEvidence {
        private final JsonObject catalog;

        private StaticEvidence(JsonObject catalog) {
            this.catalog = catalog;
        }
    }

    private static final class RuntimeEvidence {
        private final JsonObject catalog;
        private final boolean confirmedSasl;
        private final boolean confirmedShared;

        private RuntimeEvidence(JsonObject catalog, boolean confirmedSasl,
                                boolean confirmedShared) {
            this.catalog = catalog;
            this.confirmedSasl = confirmedSasl;
            this.confirmedShared = confirmedShared;
        }
    }

    private static final class ReplayCandidate {
        private final JsonObject summary;
        private final JsonObject artifact;

        private ReplayCandidate(JsonObject summary, JsonObject artifact) {
            this.summary = summary;
            this.artifact = artifact;
        }
    }

    private static final class ReplayEvidence {
        private final List<JsonObject> orderedSummaries = new ArrayList<>();
        private final List<String> partialRoles = new ArrayList<>();
        private final JsonObject catalog = new JsonObject();
        private final JsonArray artifacts;

        private ReplayEvidence(JsonArray artifacts) {
            this.artifacts = artifacts;
        }
    }

    private static final class TargetQueryEvidence {
        private final JsonObject query;
        private final JsonObject catalog;

        private TargetQueryEvidence(JsonObject query, JsonObject catalog) {
            this.query = query;
            this.catalog = catalog;
        }
    }

    public static final class Result {
        public final String smtLib;
        public final JsonObject manifest;

        private Result(String smtLib, JsonObject manifest) {
            this.smtLib = smtLib;
            this.manifest = manifest;
        }
    }

    public static final class Arguments {
        private Path policy;
        private Path regions;
        private Path staticGraph;
        private Path regionEdges;
        private Path runtimeEdges;
        private Path runtimeSummary;
        private Path activationPlan;
        private Path offlineProvenance;
        private Path targetQuery;
        private final List<Path> replaySummaries = new ArrayList<>();
        private Path output;
        private Path manifest;

        public static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            List<String> replayValues = new ArrayList<>();
            for (int index = 0; argv != null && index < argv.length; index++) {
                String key = argv[index];
                if (!key.startsWith("--") || index + 1 >= argv.length
                        || argv[index + 1].startsWith("--")) {
                    throw new IllegalArgumentException(
                            "Expected --key value, got " + key);
                }
                String name = key.substring(2);
                String value = argv[++index];
                if ("replay-summary".equals(name)) {
                    replayValues.add(value);
                } else {
                    values.put(name, value);
                }
            }
            Arguments result = new Arguments();
            result.policy = required(values, "policy");
            result.regions = required(values, "regions");
            result.staticGraph = required(values, "static-graph");
            result.regionEdges = required(values, "region-edges");
            result.runtimeEdges = required(values,
                    "runtime-edge-validations");
            result.runtimeSummary = required(values, "runtime-summary");
            result.activationPlan = required(values, "activation-plan");
            result.offlineProvenance = required(values,
                    "offline-provenance");
            result.targetQuery = required(values, "target-query");
            for (String value : replayValues) {
                if (value != null && !value.trim().isEmpty()) {
                    result.replaySummaries.add(Paths.get(value));
                }
            }
            result.output = required(values, "output");
            result.manifest = values.containsKey("manifest")
                    ? Paths.get(values.get("manifest"))
                    : sibling(result.output,
                    "hdfs_11741_bootstrap_manifest.json");
            return result;
        }

        private static Path required(Map<String, String> values, String key) {
            String value = values.get(key);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return Paths.get(value);
        }

        private static Path sibling(Path path, String name) {
            Path parent = path.toAbsolutePath().normalize().getParent();
            return parent == null ? Paths.get(name) : parent.resolve(name);
        }
    }
}
