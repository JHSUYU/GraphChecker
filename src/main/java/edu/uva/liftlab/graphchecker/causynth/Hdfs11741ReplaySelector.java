package edu.uva.liftlab.graphchecker.causynth;

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
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Selects the five temporally related base activations used by the bounded
 * HDFS-11741 replay. Generated ACT/REGION ids are outputs, never selectors.
 */
public final class Hdfs11741ReplaySelector {
    static final String AUTHORITY =
            "POLICY_REGION_SIGNATURE_TIMELINE_AND_RUNTIME_SASL_BINDING_V2";
    private static final String COMPLETE_EQUALITY_VALIDATION =
            "COMPLETE_ENDPOINT_VALUE_FINGERPRINT_EQUALITY";
    private static final String COMPLETE_FINGERPRINT_AUTHORITY =
            "RUNTIME_COMPLETE_VALUE_FINGERPRINT";
    private static final String GLOBAL_ORDER_AUTHORITY =
            "GLOBAL_TRACE_ENDPOINT_SEQUENCE";
    private static final String ENDPOINT_CORRELATION_AUTHORITY =
            "NEAREST_PRECEDING_SOURCE_ROOT_THEN_ENDPOINT";
    private static final String MANIFEST_KIND =
            "HDFS_11741_SEMANTIC_REPLAY_SELECTION_MANIFEST";
    private static final String ROW_KIND =
            "HDFS_11741_SEMANTIC_REPLAY_SELECTION";
    private static final String TRANSPORT_BINDING_KIND =
            "CONFIGURED_TRANSPORT_BINDINGS";
    private static final String TRANSPORT_BINDING_RESOLUTION_AUTHORITY =
            "POLICY_ROLE_PORT_ALIAS_TO_SELECTED_REGION_INSTANCE_V1";
    private static final List<String> ROLES = Arrays.asList(
            "namenode", "datanode", "keyUpdater", "balancer", "target");
    private static final Set<String> PRODUCERS = new LinkedHashSet<>(
            Arrays.asList("namenode", "datanode", "keyUpdater", "balancer"));
    private static final Gson JSON = new GsonBuilder()
            .disableHtmlEscaping().create();
    private static final Gson PRETTY = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private Hdfs11741ReplaySelector() {
    }

    public static void main(String[] argv) throws Exception {
        Result result = select(Arguments.parse(argv));
        System.out.println(PRETTY.toJson(result.manifest));
    }

    /** Writes the selected full activation rows and a hash-bound manifest. */
    public static Result select(Arguments arguments) throws IOException {
        require(arguments.policy, "bootstrap policy");
        require(arguments.regions, "frozen symbolic regions");
        require(arguments.activationPlan, "frozen activation plan");

        JsonObject policy = readJson(arguments.policy);
        boolean runtimeEvidenceDeclared = policy.has("runtimeEvidence")
                && policy.get("runtimeEvidence").isJsonObject();
        if (runtimeEvidenceDeclared) {
            require(arguments.runtimeEdges,
                    "frozen runtime region edge validations");
        }
        validateOutputPaths(arguments);
        if (integer(policy, "schemaVersion", -1) != 1) {
            throw gap("POLICY_SCHEMA_VERSION");
        }
        String profile = requiredText(policy, "profileId",
                "POLICY_PROFILE_ID");
        String workload = requiredText(policy, "workload",
                "POLICY_WORKLOAD");
        if (integer(object(policy, "replaySelection"), "schemaVersion", -1)
                != 1) throw gap("REPLAY_SELECTION_POLICY_SCHEMA_VERSION");
        JsonObject targetGuard = object(policy, "targetGuard");
        requiredText(targetGuard, "siteId", "TARGET_GUARD_SITE");
        requiredBoolean(targetGuard, "requiredOutcome",
                "TARGET_GUARD_REQUIRED_OUTCOME");

        Map<String, RegionSpec> regions = selectRegions(policy,
                readJsonl(arguments.regions));
        Map<String, List<JsonObject>> candidates = candidates(
                readJsonl(arguments.activationPlan), regions, workload,
                targetGuard);

        JsonObject updater = unique(candidates.get("keyUpdater"),
                "keyUpdater");
        long updaterCall = call(updater);
        JsonObject dn = latestBefore(candidates.get("datanode"), updaterCall,
                "datanode", "keyUpdater");
        long datanodeCall = call(dn);
        JsonObject nn = latestBefore(candidates.get("namenode"), datanodeCall,
                "namenode", "datanode");
        JsonObject dispatcher;
        JsonObject target;
        RuntimeSaslSelection runtimeSasl = null;
        if (runtimeEvidenceDeclared) {
            // Pick the fatal consumer without first guessing which concurrent
            // transfer produced its username.  The confirmed endpoint binding
            // below then identifies that exact Dispatcher instance.
            target = earliestAfter(candidates.get("target"), updaterCall,
                    "target", "keyUpdater");
            runtimeSasl = selectRuntimeSaslProducer(
                    readJsonl(arguments.runtimeEdges),
                    object(policy, "runtimeEvidence"), regions,
                    candidates.get("balancer"), target, workload);
            dispatcher = runtimeSasl.producerActivation;
        } else {
            dispatcher = earliestAfter(candidates.get("balancer"),
                    updaterCall, "balancer", "keyUpdater");
            target = earliestAfter(candidates.get("target"), call(dispatcher),
                    "target", "balancer");
        }
        long dispatcherCall = call(dispatcher);

        Map<String, Choice> selected = new LinkedHashMap<>();
        selected.put("namenode", choice("namenode", nn,
                "LATEST_BEFORE_DATANODE", "datanode", datanodeCall,
                bounded(candidates.get("namenode"), datanodeCall, true).size()));
        selected.put("datanode", choice("datanode", dn,
                "LATEST_BEFORE_KEY_UPDATER", "keyUpdater", updaterCall,
                bounded(candidates.get("datanode"), updaterCall, true).size()));
        selected.put("keyUpdater", choice("keyUpdater", updater,
                "UNIQUE_SEMANTIC_ACTIVATION", "", -1L, 1));
        selected.put("balancer", choice("balancer", dispatcher,
                runtimeSasl == null ? "EARLIEST_AFTER_KEY_UPDATER"
                        : "CONFIRMED_SASL_PRODUCER_FOR_TARGET",
                runtimeSasl == null ? "keyUpdater" : "target",
                runtimeSasl == null ? updaterCall : call(target),
                runtimeSasl == null
                        ? bounded(candidates.get("balancer"), updaterCall,
                        false).size() : 1));
        selected.put("target", choice("target", target,
                runtimeSasl == null ? "EARLIEST_AFTER_DISPATCHER"
                        : "EARLIEST_AFTER_KEY_UPDATER",
                runtimeSasl == null ? "balancer" : "keyUpdater",
                runtimeSasl == null ? dispatcherCall : updaterCall,
                bounded(candidates.get("target"), runtimeSasl == null
                        ? dispatcherCall : updaterCall, false).size()));
        validateTimeline(selected);

        List<Choice> timeline = new ArrayList<>(selected.values());
        Collections.sort(timeline, Comparator.comparingLong(value ->
                call(value.activation)));
        List<JsonObject> outputRows = new ArrayList<>();
        JsonObject selectedCatalog = new JsonObject();
        for (int index = 0; index < timeline.size(); index++) {
            Choice choice = timeline.get(index);
            RegionSpec region = regions.get(choice.role);
            JsonObject evidence = evidence(choice, region, targetGuard,
                    index + 1, candidates.get(choice.role).size());
            JsonObject outputRow = choice.activation.deepCopy();
            outputRow.add("hdfs11741ReplaySelection", evidence.deepCopy());
            outputRows.add(outputRow);
            JsonObject compact = compact(choice.activation);
            compact.add("selection", evidence);
            selectedCatalog.add(choice.role, compact);
        }
        JsonObject configuredTransportBindings =
                resolveConfiguredTransportBindings(policy, regions, selected);
        writeJsonl(arguments.output, outputRows);

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("kind", MANIFEST_KIND);
        manifest.addProperty("profileId", profile);
        manifest.addProperty("workload", workload);
        manifest.addProperty("complete", true);
        manifest.addProperty("selectionAuthority", AUTHORITY);
        manifest.addProperty("selectedRoleCount", selected.size());
        manifest.addProperty("configuredGeneratedRegionIds", false);
        manifest.addProperty("configuredGeneratedActivationIds", false);
        manifest.addProperty("datanodeRootCallId", datanodeCall);
        manifest.addProperty("keyUpdaterRootCallId", updaterCall);
        manifest.addProperty("dispatcherRootCallId", dispatcherCall);
        manifest.addProperty("targetRootCallId", call(target));
        manifest.addProperty("causalBoundsVerified", true);
        if (runtimeSasl != null) manifest.add(
                "dispatcherTargetRuntimeEvidence", runtimeSasl.evidence());
        manifest.add("causalBounds", causalBounds(selected));
        manifest.add("roleCapturePolicies", capturePolicies(regions,
                targetGuard));
        manifest.add("candidateCounts", candidateCounts(candidates,
                datanodeCall, updaterCall, dispatcherCall));
        manifest.add("selectedActivations", selectedCatalog);
        manifest.add("configuredTransportBindings",
                configuredTransportBindings);
        JsonObject inputs = new JsonObject();
        inputs.add("policy", artifact(arguments.policy));
        inputs.add("regions", artifact(arguments.regions));
        inputs.add("activationPlan", artifact(arguments.activationPlan));
        if (arguments.runtimeEdges != null) inputs.add("runtimeEdges",
                artifact(arguments.runtimeEdges));
        manifest.add("inputArtifacts", inputs);
        manifest.add("replaySelectionArtifact", artifact(arguments.output));
        manifest.addProperty("manifestPath", arguments.manifest
                .toAbsolutePath().normalize().toString());
        ConcolicStaticCatalogReuse.writeManifest(arguments.manifest, manifest);
        return new Result(outputRows, manifest);
    }

    /**
     * Resolves policy role/port aliases against the frozen static catalog and
     * the selected runtime instances.  Expression-valued sources deliberately
     * remain selectors: replay summaries are validated by the composer, not
     * read by this selection stage.
     */
    private static JsonObject resolveConfiguredTransportBindings(
            JsonObject policy, Map<String, RegionSpec> regions,
            Map<String, Choice> selected) throws IOException {
        JsonObject configured = requiredObject(policy, "transportBindings",
                "TRANSPORT_BINDINGS_POLICY");
        if (integer(configured, "schemaVersion", -1) != 1) throw gap(
                "TRANSPORT_BINDINGS_SCHEMA_VERSION");
        String authority = requiredText(configured, "authority",
                "TRANSPORT_BINDINGS_AUTHORITY");
        JsonArray bindings = requiredArray(configured, "bindings",
                "TRANSPORT_BINDINGS");
        if (bindings.size() == 0) throw gap("TRANSPORT_BINDINGS_EMPTY");

        JsonArray resolvedBindings = new JsonArray();
        Set<String> bindingIds = new LinkedHashSet<>();
        for (JsonElement value : bindings) {
            if (!value.isJsonObject()) throw gap(
                    "TRANSPORT_BINDING_NOT_OBJECT");
            JsonObject binding = value.getAsJsonObject();
            String bindingId = requiredText(binding, "bindingId",
                    "TRANSPORT_BINDING_ID");
            if (!bindingIds.add(bindingId)) throw gap(
                    "TRANSPORT_BINDING_ID_DUPLICATE:" + bindingId);
            boolean includeGuards = requiredBoolean(binding,
                    "includeSourcePathGuards",
                    "TRANSPORT_BINDING_SOURCE_PATH_GUARDS:" + bindingId);
            if (!includeGuards) throw gap(
                    "TRANSPORT_BINDING_SOURCE_PATH_GUARDS_DISABLED:"
                            + bindingId);
            String approximation = requiredText(binding, "approximation",
                    "TRANSPORT_BINDING_APPROXIMATION:" + bindingId);

            JsonObject resolved = new JsonObject();
            resolved.addProperty("bindingId", bindingId);
            resolved.addProperty("authority", authority);
            resolved.addProperty("policyDerived", true);
            resolved.addProperty("configuredGeneratedRegionIds", false);
            resolved.addProperty("configuredGeneratedActivationIds", false);
            resolved.add("source", resolveTransportSource(
                    requiredObject(binding, "source",
                            "TRANSPORT_BINDING_SOURCE:" + bindingId),
                    policy, regions, selected, bindingId));

            JsonArray targets = requiredArray(binding, "targets",
                    "TRANSPORT_BINDING_TARGETS:" + bindingId);
            if (targets.size() == 0) throw gap(
                    "TRANSPORT_BINDING_TARGETS_EMPTY:" + bindingId);
            JsonArray resolvedTargets = new JsonArray();
            Set<String> targetAliases = new LinkedHashSet<>();
            for (JsonElement targetValue : targets) {
                if (!targetValue.isJsonObject()) throw gap(
                        "TRANSPORT_BINDING_TARGET_NOT_OBJECT:"
                                + bindingId);
                JsonObject target = targetValue.getAsJsonObject();
                String alias = requiredText(target, "portAlias",
                        "TRANSPORT_BINDING_TARGET_PORT_ALIAS:"
                                + bindingId);
                if (!targetAliases.add(alias)) throw gap(
                        "TRANSPORT_BINDING_TARGET_ALIAS_DUPLICATE:"
                                + bindingId + ":" + alias);
                resolvedTargets.add(resolvePortEndpoint(target, policy,
                        regions, selected, bindingId, "TARGET"));
            }
            resolved.add("targets", resolvedTargets);
            resolved.addProperty("includeSourcePathGuards", true);
            resolved.addProperty("approximation", approximation);
            resolvedBindings.add(resolved);
        }

        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", TRANSPORT_BINDING_KIND);
        result.addProperty("authority", authority);
        result.addProperty("resolutionAuthority",
                TRANSPORT_BINDING_RESOLUTION_AUTHORITY);
        result.addProperty("policyDerived", true);
        result.addProperty("configuredGeneratedRegionIds", false);
        result.addProperty("configuredGeneratedActivationIds", false);
        result.addProperty("bindingCount", resolvedBindings.size());
        result.add("bindings", resolvedBindings);
        return result;
    }

    private static JsonObject resolveTransportSource(JsonObject source,
            JsonObject policy, Map<String, RegionSpec> regions,
            Map<String, Choice> selected, String bindingId)
            throws IOException {
        String kind = requiredText(source, "kind",
                "TRANSPORT_BINDING_SOURCE_KIND:" + bindingId);
        if ("PORT_ALIAS".equals(kind)) {
            return resolvePortEndpoint(source, policy, regions, selected,
                    bindingId, "SOURCE");
        }
        if (!"UNIFORM_HEAP_EFFECT_EXPRESSION".equals(kind)) throw gap(
                "TRANSPORT_BINDING_SOURCE_KIND_UNSUPPORTED:" + bindingId
                        + ":" + kind);
        String role = requiredText(source, "role",
                "TRANSPORT_BINDING_SOURCE_ROLE:" + bindingId);
        RoleResolution roleResolution = resolveRole(role, regions, selected,
                "SOURCE:" + bindingId);
        requiredSort(source, bindingId + ":SOURCE");
        requiredText(source, "effectKind",
                "TRANSPORT_BINDING_EFFECT_KIND:" + bindingId);
        requiredText(source, "expressionField",
                "TRANSPORT_BINDING_EXPRESSION_FIELD:" + bindingId);

        JsonObject result = source.deepCopy();
        addRoleResolution(result, roleResolution);
        result.addProperty("selectorPreserved", true);
        return result;
    }

    private static JsonObject resolvePortEndpoint(JsonObject endpoint,
            JsonObject policy, Map<String, RegionSpec> regions,
            Map<String, Choice> selected, String bindingId, String endpointKind)
            throws IOException {
        String role = requiredText(endpoint, "role",
                "TRANSPORT_BINDING_" + endpointKind + "_ROLE:"
                        + bindingId);
        String alias = requiredText(endpoint, "portAlias",
                "TRANSPORT_BINDING_" + endpointKind + "_PORT_ALIAS:"
                        + bindingId);
        requiredSort(endpoint, bindingId + ":" + endpointKind + ":"
                + alias);
        JsonObject ports = requiredObject(policy, "ports",
                "TRANSPORT_BINDING_PORT_CATALOG");
        JsonObject portSelector = requiredObject(ports, alias,
                "TRANSPORT_BINDING_PORT_ALIAS_UNKNOWN:" + alias);
        String configuredRole = requiredText(portSelector, "region",
                "TRANSPORT_BINDING_PORT_ROLE:" + alias);
        if (!role.equals(configuredRole)) throw gap(
                "TRANSPORT_BINDING_PORT_ROLE_MISMATCH:" + alias + ":"
                        + role + ":" + configuredRole);
        String collection = requiredText(portSelector, "collection",
                "TRANSPORT_BINDING_PORT_COLLECTION:" + alias);
        String cell = requiredText(portSelector, "cell",
                "TRANSPORT_BINDING_PORT_CELL:" + alias);
        RoleResolution roleResolution = resolveRole(role, regions, selected,
                endpointKind + ":" + bindingId + ":" + alias);
        JsonArray portsInRegion = requiredArray(roleResolution.region.region,
                collection, "TRANSPORT_BINDING_REGION_COLLECTION:" + alias
                        + ":" + collection);
        List<JsonObject> matches = new ArrayList<>();
        for (JsonElement candidate : portsInRegion) {
            if (candidate.isJsonObject() && cell.equals(string(
                    candidate.getAsJsonObject(), "cell"))) {
                matches.add(candidate.getAsJsonObject());
            }
        }
        if (matches.size() != 1) throw gap(
                "TRANSPORT_BINDING_PORT_CARDINALITY:" + alias + ":"
                        + matches.size());
        String portId = requiredText(matches.get(0), "portId",
                "TRANSPORT_BINDING_PORT_ID:" + alias);
        validateFieldProjection(endpoint, bindingId, endpointKind, alias);

        JsonObject result = endpoint.deepCopy();
        result.addProperty("kind", "PORT");
        result.addProperty("configuredEndpointKind",
                string(endpoint, "kind").isEmpty()
                        ? "PORT_ALIAS" : string(endpoint, "kind"));
        addRoleResolution(result, roleResolution);
        result.addProperty("collection", collection);
        result.addProperty("portId", portId);
        result.addProperty("cell", cell);
        result.addProperty("portResolutionAuthority",
                TRANSPORT_BINDING_RESOLUTION_AUTHORITY);
        return result;
    }

    private static void validateFieldProjection(JsonObject endpoint,
            String bindingId, String endpointKind, String alias)
            throws IOException {
        if (!endpoint.has("fieldPath")) return;
        JsonArray path = requiredArray(endpoint, "fieldPath",
                "TRANSPORT_BINDING_FIELD_PATH:" + bindingId + ":"
                        + endpointKind + ":" + alias);
        if (path.size() == 0) throw gap(
                "TRANSPORT_BINDING_FIELD_PATH_EMPTY:" + bindingId + ":"
                        + alias);
        for (JsonElement component : path) {
            if (!component.isJsonPrimitive()
                    || component.getAsString().trim().isEmpty()) throw gap(
                    "TRANSPORT_BINDING_FIELD_PATH_COMPONENT:" + bindingId
                            + ":" + alias);
        }
        requiredText(endpoint, "declaredFieldSignature",
                "TRANSPORT_BINDING_DECLARED_FIELD_SIGNATURE:" + bindingId
                        + ":" + alias);
    }

    private static String requiredSort(JsonObject endpoint, String context)
            throws IOException {
        String sort = requiredText(endpoint, "expectedSort",
                "TRANSPORT_BINDING_EXPECTED_SORT:" + context);
        if (!Arrays.asList("Int", "Bool", "Real", "String")
                .contains(sort)) throw gap(
                "TRANSPORT_BINDING_EXPECTED_SORT_UNSUPPORTED:" + context
                        + ":" + sort);
        return sort;
    }

    private static RoleResolution resolveRole(String role,
            Map<String, RegionSpec> regions, Map<String, Choice> selected,
            String context) throws IOException {
        if (!ROLES.contains(role) || !regions.containsKey(role)
                || !selected.containsKey(role)) throw gap(
                "TRANSPORT_BINDING_ROLE_UNKNOWN:" + context + ":" + role);
        RegionSpec region = regions.get(role);
        Choice choice = selected.get(role);
        String regionId = requiredText(region.region, "regionId",
                "TRANSPORT_BINDING_REGION_ID:" + context);
        if (!regionId.equals(string(choice.activation, "regionId"))) {
            throw gap("TRANSPORT_BINDING_SELECTED_ROLE_MISMATCH:" + context
                    + ":" + role);
        }
        String instanceId = requiredText(choice.activation,
                "regionInstanceId",
                "TRANSPORT_BINDING_REGION_INSTANCE_ID:" + context);
        String activationId = requiredText(choice.activation,
                "activationId",
                "TRANSPORT_BINDING_ACTIVATION_ID:" + context);
        return new RoleResolution(role, region, regionId, instanceId,
                activationId);
    }

    private static void addRoleResolution(JsonObject endpoint,
            RoleResolution resolution) {
        endpoint.addProperty("role", resolution.role);
        endpoint.addProperty("regionId", resolution.regionId);
        endpoint.addProperty("regionInstanceId", resolution.instanceId);
        endpoint.addProperty("activationId", resolution.activationId);
    }

    private static Map<String, RegionSpec> selectRegions(JsonObject policy,
            List<JsonObject> rows) throws IOException {
        JsonObject selectors = object(policy, "regions");
        JsonObject outputs = object(object(policy, "replaySelection"),
                "producerOutputs");
        Map<String, RegionSpec> result = new LinkedHashMap<>();
        Set<String> ids = new LinkedHashSet<>();
        for (String role : ROLES) {
            JsonObject selector = object(selectors, role);
            String root = requiredText(selector, "rootMethod",
                    "REGION_ROOT:" + role);
            String anchor = requiredText(selector, "anchorMethod",
                    "REGION_ANCHOR:" + role);
            if (!selector.has("requiredMethods")
                    || !selector.get("requiredMethods").isJsonArray()) {
                throw gap("REGION_REQUIRED_METHODS:" + role);
            }
            Set<String> required = strings(array(selector,
                    "requiredMethods"));
            List<JsonObject> matches = new ArrayList<>();
            for (JsonObject row : rows) {
                if (root.equals(string(row, "rootMethod"))
                        && anchor.equals(string(row, "anchorMethod"))
                        && strings(array(row, "methods"))
                        .containsAll(required)) {
                    matches.add(row);
                }
            }
            if (matches.size() != 1) throw gap(
                    "REGION_SELECTOR_CARDINALITY:" + role + ":"
                            + matches.size());
            JsonObject region = matches.get(0);
            String id = string(region, "regionId");
            if (id.isEmpty() || !ids.add(id)) throw gap(
                    "REGION_ID_MISSING_OR_REUSED:" + role + ":" + id);

            JsonObject output = null;
            JsonObject outputSlice = null;
            if (PRODUCERS.contains(role)) {
                String cell = requiredText(object(outputs, role), "cell",
                        "PRODUCER_OUTPUT_CELL:" + role);
                List<JsonObject> outputMatches = new ArrayList<>();
                for (JsonElement value : array(region, "outputs")) {
                    if (value.isJsonObject() && cell.equals(string(
                            value.getAsJsonObject(), "cell"))) {
                        outputMatches.add(value.getAsJsonObject());
                    }
                }
                if (outputMatches.size() != 1) throw gap(
                        "PRODUCER_OUTPUT_CARDINALITY:" + role + ":"
                                + outputMatches.size());
                output = outputMatches.get(0);
                if (string(output, "portId").isEmpty()) throw gap(
                        "PRODUCER_OUTPUT_PORT_MISSING:" + role);
                List<JsonObject> sliceMatches = new ArrayList<>();
                for (JsonElement value : array(region, "outputSlices")) {
                    if (!value.isJsonObject()) continue;
                    JsonObject slice = value.getAsJsonObject();
                    if (string(output, "portId").equals(string(slice,
                            "outputPort")) && cell.equals(string(slice,
                            "outputCell"))) sliceMatches.add(slice);
                }
                if (sliceMatches.size() != 1) throw gap(
                        "PRODUCER_OUTPUT_SLICE_CARDINALITY:" + role + ":"
                                + sliceMatches.size());
                outputSlice = sliceMatches.get(0);
                if (!bool(outputSlice, "structuralComplete", false)
                        || bool(outputSlice, "truncated", true)) throw gap(
                        "PRODUCER_OUTPUT_SLICE_NOT_STRUCTURAL:" + role);
            }
            result.put(role, new RegionSpec(selector, region, output,
                    outputSlice));
        }
        return result;
    }

    private static Map<String, List<JsonObject>> candidates(
            List<JsonObject> rows, Map<String, RegionSpec> regions,
            String workload, JsonObject targetGuard) throws IOException {
        Map<String, List<JsonObject>> result = new LinkedHashMap<>();
        Map<String, String> rolesByRegion = new LinkedHashMap<>();
        for (String role : ROLES) {
            result.put(role, new ArrayList<>());
            rolesByRegion.put(string(regions.get(role).region, "regionId"),
                    role);
        }
        Set<String> ids = new LinkedHashSet<>();
        Set<String> instances = new LinkedHashSet<>();
        for (JsonObject row : rows) {
            String role = rolesByRegion.get(string(row, "regionId"));
            // Derived output closures share a rootCallId with their base row;
            // the selector emits the base and lets Scheduler rebuild closure.
            if (role == null || !string(row,
                    "derivedFromActivationId").isEmpty()) continue;
            String rowWorkload = first(string(row, "test"),
                    string(row, "workload"));
            String expectedRoot = string(regions.get(role).selector,
                    "rootMethod");
            if (!workload.equals(rowWorkload)
                    || !rootsMatch(row, expectedRoot)
                    || row.has("anchorObserved")
                    && !bool(row, "anchorObserved", false)
                    || "target".equals(role)
                    && !matchesTargetBranch(row, targetGuard)) continue;
            if (call(row) <= 0L) throw gap(
                    "ACTIVATION_ROOT_CALL_ID:" + role);
            String id = string(row, "activationId");
            if (id.isEmpty() || !ids.add(id)) throw gap(
                    "ACTIVATION_ID_MISSING_OR_DUPLICATE:" + id);
            String instance = string(row, "regionInstanceId");
            if (instance.isEmpty() || !instances.add(instance)) throw gap(
                    "REGION_INSTANCE_ID_MISSING_OR_DUPLICATE:" + instance);
            result.get(role).add(row.deepCopy());
        }
        for (String role : ROLES) {
            if (result.get(role).isEmpty()) throw gap(
                    "NO_SEMANTIC_ACTIVATION:" + role);
        }
        return result;
    }

    private static boolean rootsMatch(JsonObject row, String expected) {
        boolean observed = false;
        for (String field : Arrays.asList("rootMethod", "observedRootMethod",
                "staticRootMethod")) {
            String value = string(row, field);
            if (value.isEmpty()) continue;
            observed = true;
            if (!expected.equals(value)) return false;
        }
        return observed;
    }

    private static boolean matchesTargetBranch(JsonObject row,
            JsonObject targetGuard) {
        String site = string(targetGuard, "siteId");
        boolean outcome = bool(targetGuard, "requiredOutcome", false);
        int matches = 0;
        for (JsonElement value : array(row, "branches")) {
            if (!value.isJsonObject()) continue;
            JsonObject branch = value.getAsJsonObject();
            if (site.equals(string(branch, "siteId"))
                    && bool(branch, "observed", false)
                    && branch.has("requiredOutcome")
                    && bool(branch, "requiredOutcome", !outcome)
                    == outcome) matches++;
        }
        return matches == 1;
    }

    private static RuntimeSaslSelection selectRuntimeSaslProducer(
            List<JsonObject> runtimeEdges, JsonObject runtimePolicy,
            Map<String, RegionSpec> regions,
            List<JsonObject> balancerCandidates, JsonObject target,
            String workload) throws IOException {
        Set<String> saslKinds = strings(array(runtimePolicy, "saslKinds"));
        if (saslKinds.isEmpty()) throw gap(
                "RUNTIME_SASL_MAPPING_KINDS_MISSING");
        String balancerRegion = string(regions.get("balancer").region,
                "regionId");
        String targetRegion = string(regions.get("target").region,
                "regionId");
        String targetInstance = string(target, "regionInstanceId");
        long targetRoot = call(target);
        if (!instanceMatches(targetInstance, targetRegion, targetRoot)) {
            throw gap("TARGET_INSTANCE_ROOT_MISMATCH:" + targetInstance);
        }

        List<RuntimeSaslSelection> matches = new ArrayList<>();
        for (JsonObject edge : runtimeEdges) {
            if (!"CONFIRMED_RUNTIME_VALUE_EQUALITY".equals(string(edge,
                    "status"))
                    || !saslKinds.contains(string(edge, "mappingKind"))
                    || !balancerRegion.equals(string(edge, "fromRegion"))
                    || !targetRegion.equals(string(edge, "toRegion"))
                    || !optionalTrue(edge,
                    "producerRegionUniquelyConfirmed")
                    || !COMPLETE_EQUALITY_VALIDATION.equals(string(edge,
                    "validation"))
                    || !COMPLETE_FINGERPRINT_AUTHORITY.equals(string(edge,
                    "valueEqualityAuthority"))
                    || !GLOBAL_ORDER_AUTHORITY.equals(string(edge,
                    "endpointOrderAuthority"))) continue;
            for (JsonElement value : array(edge, "validatedBindings")) {
                if (!value.isJsonObject()) continue;
                JsonObject binding = value.getAsJsonObject();
                String fromInstance = string(binding,
                        "fromRegionInstance");
                if (!targetInstance.equals(string(binding,
                        "toRegionInstance"))
                        || !workload.equals(string(binding, "test"))
                        || !optionalTrue(binding,
                        "producerRegionUniquelyConfirmed")
                        || !instanceMatches(string(binding,
                        "toRegionInstance"), targetRegion, targetRoot)
                        || !fromInstance.startsWith(balancerRegion + "@")
                        || !completeEndpointEquality(binding)) continue;

                List<JsonObject> producers = new ArrayList<>();
                for (JsonObject candidate : balancerCandidates) {
                    if (fromInstance.equals(string(candidate,
                            "regionInstanceId"))
                            && workload.equals(first(string(candidate, "test"),
                            string(candidate, "workload")))
                            && instanceMatches(fromInstance, balancerRegion,
                            call(candidate))) producers.add(candidate);
                }
                if (producers.size() != 1) throw gap(
                        "RUNTIME_SASL_PRODUCER_ACTIVATION_CARDINALITY:"
                                + producers.size() + ":" + fromInstance);
                matches.add(new RuntimeSaslSelection(producers.get(0),
                        target, edge, binding));
            }
        }
        if (matches.size() != 1) throw gap(
                "RUNTIME_SASL_BINDING_CARDINALITY:" + matches.size()
                        + ":" + targetInstance);
        return matches.get(0);
    }

    private static boolean completeEndpointEquality(JsonObject binding) {
        String fingerprint = string(binding, "valueFingerprint");
        if (!bool(binding, "valueEqualityObserved", false)
                || !bool(binding, "orderConfirmed", false)
                || !COMPLETE_FINGERPRINT_AUTHORITY.equals(string(binding,
                "valueEqualityAuthority"))
                || !GLOBAL_ORDER_AUTHORITY.equals(string(binding,
                "endpointOrderAuthority"))
                || !ENDPOINT_CORRELATION_AUTHORITY.equals(string(binding,
                "endpointCorrelationAuthority"))
                || !fingerprint.matches("sha256:[0-9a-fA-F]{64}")) {
            return false;
        }
        long fromSequence = longValue(binding, "fromEndpointSeq", -1L);
        long toSequence = longValue(binding, "toEndpointSeq", -1L);
        return fromSequence > 0L && fromSequence < toSequence;
    }

    private static boolean optionalTrue(JsonObject value, String field) {
        return !value.has(field) || bool(value, field, false);
    }

    private static boolean instanceMatches(String instance, String region,
            long rootCallId) {
        if (instance == null || !instance.startsWith(region + "@")
                || rootCallId <= 0L) return false;
        int marker = instance.lastIndexOf("#call");
        if (marker < 0 || marker + 5 >= instance.length()) return false;
        try {
            return Long.parseLong(instance.substring(marker + 5))
                    == rootCallId;
        } catch (NumberFormatException ignored) {
            return false;
        }
    }

    private static Choice choice(String role, JsonObject activation,
            String rule, String boundaryRole, long boundary, int eligible) {
        return new Choice(role, activation, rule, boundaryRole, boundary,
                eligible);
    }

    private static JsonObject unique(List<JsonObject> rows, String role)
            throws IOException {
        if (rows == null || rows.size() != 1) throw gap(
                "UNIQUE_ACTIVATION_CARDINALITY:" + role + ":"
                        + (rows == null ? 0 : rows.size()));
        return rows.get(0);
    }

    private static JsonObject latestBefore(List<JsonObject> rows,
            long boundary, String role, String boundaryRole)
            throws IOException {
        List<JsonObject> eligible = bounded(rows, boundary, true);
        long selected = Long.MIN_VALUE;
        for (JsonObject row : eligible) selected = Math.max(selected,
                call(row));
        return uniqueAt(eligible, selected, role,
                "LATEST_BEFORE_" + boundaryRole);
    }

    private static JsonObject earliestAfter(List<JsonObject> rows,
            long boundary, String role, String boundaryRole)
            throws IOException {
        List<JsonObject> eligible = bounded(rows, boundary, false);
        long selected = Long.MAX_VALUE;
        for (JsonObject row : eligible) selected = Math.min(selected,
                call(row));
        return uniqueAt(eligible, selected, role,
                "EARLIEST_AFTER_" + boundaryRole);
    }

    private static List<JsonObject> bounded(List<JsonObject> rows,
            long boundary, boolean before) {
        List<JsonObject> result = new ArrayList<>();
        if (rows == null) return result;
        for (JsonObject row : rows) {
            if (before ? call(row) < boundary : call(row) > boundary) {
                result.add(row);
            }
        }
        return result;
    }

    private static JsonObject uniqueAt(List<JsonObject> rows, long selected,
            String role, String rule) throws IOException {
        JsonObject result = null;
        int count = 0;
        for (JsonObject row : rows) {
            if (call(row) == selected) {
                result = row;
                count++;
            }
        }
        if (count != 1) throw gap("TEMPORAL_SELECTION_CARDINALITY:" + role
                + ":" + rule + ":" + count);
        return result;
    }

    private static void validateTimeline(Map<String, Choice> selected)
            throws IOException {
        long nn = call(selected.get("namenode").activation);
        long dn = call(selected.get("datanode").activation);
        long updater = call(selected.get("keyUpdater").activation);
        long dispatcher = call(selected.get("balancer").activation);
        long target = call(selected.get("target").activation);
        if (!(nn < dn && dn < updater && updater < dispatcher
                && dispatcher < target)) throw gap(
                "SELECTED_TIMELINE_NOT_CAUSALLY_BOUNDED");
        Set<String> ids = new LinkedHashSet<>();
        for (Choice choice : selected.values()) {
            String id = string(choice.activation, "activationId");
            if (!ids.add(id)) throw gap("SELECTED_ACTIVATION_REUSED:" + id);
        }
    }

    private static JsonObject evidence(Choice choice, RegionSpec region,
            JsonObject targetGuard, int order, int candidateCount) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", ROW_KIND);
        result.addProperty("policyRole", choice.role);
        result.addProperty("semanticRole", semanticRole(choice.role));
        result.addProperty("replayOrder", order);
        result.addProperty("selectionRule", choice.rule);
        result.addProperty("selectionAuthority", AUTHORITY);
        result.addProperty("rootCallId", call(choice.activation));
        result.addProperty("semanticCandidateCount", candidateCount);
        result.addProperty("eligibleTemporalCandidateCount", choice.eligible);
        if (!choice.boundaryRole.isEmpty()) {
            result.addProperty("boundaryPolicyRole", choice.boundaryRole);
            result.addProperty("boundaryRootCallId", choice.boundary);
        }
        JsonObject selector = new JsonObject();
        selector.addProperty("rootMethod", string(region.selector,
                "rootMethod"));
        selector.addProperty("anchorMethod", string(region.selector,
                "anchorMethod"));
        selector.add("requiredMethods", array(region.selector,
                "requiredMethods").deepCopy());
        result.add("regionSelector", selector);
        result.addProperty("selectedRegionId", string(region.region,
                "regionId"));
        JsonObject captureGoal = capture(region, targetGuard);
        if ("target".equals(choice.role)) {
            captureGoal.addProperty("selectedActivationBranchObserved",
                    true);
        }
        result.add("captureGoal", captureGoal);
        return result;
    }

    private static JsonObject capture(RegionSpec region,
            JsonObject targetGuard) {
        JsonObject result = new JsonObject();
        if (region.output != null) {
            result.addProperty("kind", "OUTPUT_CLOSURE");
            result.addProperty("scope", "BOUNDED_OUTPUT_RELEVANT_PATHS");
            result.addProperty("requestedOutputCell", string(region.output,
                    "cell"));
            result.addProperty("requestedOutputPort", string(region.output,
                    "portId"));
            result.addProperty("requestedOutputSliceStructuralComplete",
                    bool(region.outputSlice, "structuralComplete", false));
            result.addProperty("requestedOutputSliceTruncated",
                    bool(region.outputSlice, "truncated", true));
            result.addProperty("selectionAuthority",
                    "POLICY_CELL_AND_UNIQUE_STATIC_REGION_OUTPUT_V1");
        } else {
            result.addProperty("kind", "TARGET_BRANCH");
            result.addProperty("scope", "ONE_DIRECTED_BRANCH");
            result.addProperty("targetSiteId", string(targetGuard,
                    "siteId"));
            result.addProperty("requiredOutcome", bool(targetGuard,
                    "requiredOutcome", false));
            result.addProperty("selectionAuthority",
                    "BOOTSTRAP_POLICY_TARGET_GUARD_V1");
        }
        return result;
    }

    private static JsonObject capturePolicies(Map<String, RegionSpec> regions,
            JsonObject targetGuard) {
        JsonObject result = new JsonObject();
        for (String role : ROLES) result.add(role,
                capture(regions.get(role), targetGuard));
        return result;
    }

    private static JsonObject causalBounds(Map<String, Choice> selected) {
        JsonObject result = new JsonObject();
        addBound(result, "namenodeToDatanode", selected.get("namenode"),
                selected.get("datanode"));
        addBound(result, "datanodeToKeyUpdater", selected.get("datanode"),
                selected.get("keyUpdater"));
        addBound(result, "keyUpdaterToDispatcher",
                selected.get("keyUpdater"), selected.get("balancer"));
        addBound(result, "dispatcherToTarget", selected.get("balancer"),
                selected.get("target"));
        return result;
    }

    private static void addBound(JsonObject owner, String name, Choice from,
            Choice to) {
        JsonObject bound = new JsonObject();
        bound.addProperty("fromRole", from.role);
        bound.addProperty("fromRootCallId", call(from.activation));
        bound.addProperty("toRole", to.role);
        bound.addProperty("toRootCallId", call(to.activation));
        bound.addProperty("strictlyBefore",
                call(from.activation) < call(to.activation));
        owner.add(name, bound);
    }

    private static JsonObject candidateCounts(
            Map<String, List<JsonObject>> values, long datanode,
            long updater, long dispatcher) {
        JsonObject result = new JsonObject();
        for (String role : ROLES) {
            JsonObject count = new JsonObject();
            count.addProperty("semanticActivationCount",
                    values.get(role).size());
            if ("namenode".equals(role)) {
                count.addProperty("eligibleBeforeDatanodeCount",
                        bounded(values.get(role), datanode, true).size());
            } else if ("datanode".equals(role)) {
                count.addProperty("eligibleBeforeKeyUpdaterCount",
                        bounded(values.get(role), updater, true).size());
            } else if ("balancer".equals(role)) {
                count.addProperty("eligibleAfterKeyUpdaterCount",
                        bounded(values.get(role), updater, false).size());
            } else if ("target".equals(role)) {
                count.addProperty("eligibleAfterDispatcherCount",
                        bounded(values.get(role), dispatcher, false).size());
            }
            result.add(role, count);
        }
        return result;
    }

    private static JsonObject compact(JsonObject row) {
        JsonObject result = new JsonObject();
        for (String field : Arrays.asList("activationId", "regionId",
                "regionInstanceId", "rootMethod", "observedRootMethod",
                "rootCallId", "invocationOrdinal", "test", "replayable",
                "replayMode")) {
            if (row.has(field)) result.add(field, row.get(field).deepCopy());
        }
        return result;
    }

    private static String semanticRole(String role) {
        if ("namenode".equals(role)) return "NN";
        if ("datanode".equals(role)) return "DN";
        if ("keyUpdater".equals(role)) return "KeyUpdater";
        if ("balancer".equals(role)) return "Dispatcher";
        return "target";
    }

    private static void validateOutputPaths(Arguments arguments)
            throws IOException {
        Set<Path> inputs = new LinkedHashSet<>(Arrays.asList(
                absolute(arguments.policy), absolute(arguments.regions),
                absolute(arguments.activationPlan)));
        if (arguments.runtimeEdges != null) inputs.add(absolute(
                arguments.runtimeEdges));
        Path output = absolute(arguments.output);
        Path manifest = absolute(arguments.manifest);
        if (output.equals(manifest) || inputs.contains(output)
                || inputs.contains(manifest)) throw gap(
                "OUTPUT_PATH_OVERLAPS_INPUT_OR_MANIFEST");
    }

    private static Path absolute(Path path) {
        return path.toAbsolutePath().normalize();
    }

    private static void require(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)
                || Files.size(path) == 0L) throw new IOException(
                "Missing or empty " + label + ": " + path);
    }

    private static JsonObject readJson(Path path) throws IOException {
        JsonElement value;
        try {
            value = JsonParser.parseString(new String(Files.readAllBytes(path),
                    StandardCharsets.UTF_8));
        } catch (RuntimeException exception) {
            throw new IOException("Malformed JSON: " + path, exception);
        }
        if (!value.isJsonObject()) throw new IOException(
                "Expected JSON object: " + path);
        return value.getAsJsonObject();
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        List<JsonObject> result = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            long lineNumber = 0L;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                if (line.trim().isEmpty()) continue;
                try {
                    JsonElement value = JsonParser.parseString(line);
                    if (!value.isJsonObject()) throw new IOException(
                            "Expected JSON object at " + path + ":"
                                    + lineNumber);
                    result.add(value.getAsJsonObject());
                } catch (RuntimeException exception) {
                    throw new IOException("Malformed JSONL " + path + ":"
                            + lineNumber, exception);
                }
            }
        }
        if (result.isEmpty()) throw new IOException(
                "Missing JSONL rows: " + path);
        return result;
    }

    private static void writeJsonl(Path path, List<JsonObject> rows)
            throws IOException {
        StringBuilder value = new StringBuilder();
        for (JsonObject row : rows) value.append(JSON.toJson(row)).append('\n');
        writeAtomic(path, value.toString());
    }

    private static void writeAtomic(Path path, String value)
            throws IOException {
        Path absolute = absolute(path);
        Path parent = absolute.getParent();
        if (parent != null) Files.createDirectories(parent);
        Path temporary = Files.createTempFile(parent,
                ".hdfs-11741-replay-selection-", ".jsonl.tmp");
        try {
            Files.write(temporary, value.getBytes(StandardCharsets.UTF_8));
            try {
                Files.move(temporary, absolute, StandardCopyOption.ATOMIC_MOVE,
                        StandardCopyOption.REPLACE_EXISTING);
            } catch (AtomicMoveNotSupportedException ignored) {
                Files.move(temporary, absolute,
                        StandardCopyOption.REPLACE_EXISTING);
            }
        } finally {
            Files.deleteIfExists(temporary);
        }
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
        result.addProperty("path", absolute(path).toString());
        result.addProperty("sha256", hex(digest.digest()));
        result.addProperty("sizeBytes", size);
        return result;
    }

    private static String hex(byte[] bytes) {
        StringBuilder result = new StringBuilder();
        for (byte value : bytes) result.append(String.format("%02x",
                value & 0xff));
        return result.toString();
    }

    private static JsonObject object(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static JsonObject requiredObject(JsonObject owner, String field,
            String reason) throws IOException {
        JsonElement value = owner == null ? null : owner.get(field);
        if (value == null || !value.isJsonObject()) throw gap(reason);
        return value.getAsJsonObject();
    }

    private static JsonArray array(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static JsonArray requiredArray(JsonObject owner, String field,
            String reason) throws IOException {
        JsonElement value = owner == null ? null : owner.get(field);
        if (value == null || !value.isJsonArray()) throw gap(reason);
        return value.getAsJsonArray();
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

    private static String requiredText(JsonObject owner, String field,
            String reason) throws IOException {
        String result = string(owner, field);
        if (result.isEmpty()) throw gap(reason);
        return result;
    }

    private static boolean requiredBoolean(JsonObject owner, String field,
            String reason) throws IOException {
        JsonElement value = owner == null ? null : owner.get(field);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isBoolean()) throw gap(reason);
        return value.getAsBoolean();
    }

    private static boolean bool(JsonObject owner, String field,
            boolean fallback) {
        try {
            JsonElement value = owner == null ? null : owner.get(field);
            return value == null || value.isJsonNull() ? fallback
                    : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int integer(JsonObject owner, String field, int fallback) {
        try {
            JsonElement value = owner == null ? null : owner.get(field);
            return value == null || value.isJsonNull() ? fallback
                    : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longValue(JsonObject owner, String field,
            long fallback) {
        try {
            JsonElement value = owner == null ? null : owner.get(field);
            return value == null || value.isJsonNull() ? fallback
                    : value.getAsLong();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long call(JsonObject row) {
        try {
            JsonElement value = row == null ? null : row.get("rootCallId");
            return value == null || value.isJsonNull() ? -1L
                    : value.getAsLong();
        } catch (RuntimeException ignored) {
            return -1L;
        }
    }

    private static Set<String> strings(JsonArray values) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement value : values) {
            if (value.isJsonPrimitive()) result.add(value.getAsString());
        }
        return result;
    }

    private static String first(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) return value;
        }
        return "";
    }

    private static IOException gap(String reason) {
        return new IOException("HDFS_11741_REPLAY_SELECTION_GAP:" + reason);
    }

    private static final class RegionSpec {
        private final JsonObject selector;
        private final JsonObject region;
        private final JsonObject output;
        private final JsonObject outputSlice;

        private RegionSpec(JsonObject selector, JsonObject region,
                JsonObject output, JsonObject outputSlice) {
            this.selector = selector.deepCopy();
            this.region = region.deepCopy();
            this.output = output == null ? null : output.deepCopy();
            this.outputSlice = outputSlice == null ? null
                    : outputSlice.deepCopy();
        }
    }

    private static final class RoleResolution {
        private final String role;
        private final RegionSpec region;
        private final String regionId;
        private final String instanceId;
        private final String activationId;

        private RoleResolution(String role, RegionSpec region,
                String regionId, String instanceId, String activationId) {
            this.role = role;
            this.region = region;
            this.regionId = regionId;
            this.instanceId = instanceId;
            this.activationId = activationId;
        }
    }

    private static final class Choice {
        private final String role;
        private final JsonObject activation;
        private final String rule;
        private final String boundaryRole;
        private final long boundary;
        private final int eligible;

        private Choice(String role, JsonObject activation, String rule,
                String boundaryRole, long boundary, int eligible) {
            this.role = role;
            this.activation = activation.deepCopy();
            this.rule = rule;
            this.boundaryRole = boundaryRole;
            this.boundary = boundary;
            this.eligible = eligible;
        }
    }

    private static final class RuntimeSaslSelection {
        private final JsonObject producerActivation;
        private final JsonObject targetActivation;
        private final JsonObject edge;
        private final JsonObject binding;

        private RuntimeSaslSelection(JsonObject producerActivation,
                JsonObject targetActivation, JsonObject edge,
                JsonObject binding) {
            this.producerActivation = producerActivation.deepCopy();
            this.targetActivation = targetActivation.deepCopy();
            this.edge = edge.deepCopy();
            this.binding = binding.deepCopy();
        }

        private JsonObject evidence() {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 1);
            result.addProperty("kind",
                    "HDFS_11741_DISPATCHER_TARGET_RUNTIME_BINDING");
            result.addProperty("selectionAuthority", AUTHORITY);
            result.addProperty("edgeId", string(edge, "edgeId"));
            result.addProperty("mappingKind", string(edge,
                    "mappingKind"));
            result.addProperty("status", string(edge, "status"));
            result.addProperty("validation", string(edge, "validation"));
            result.addProperty("fromRegion", string(edge, "fromRegion"));
            result.addProperty("toRegion", string(edge, "toRegion"));
            result.addProperty("fromRegionInstance", string(binding,
                    "fromRegionInstance"));
            result.addProperty("toRegionInstance", string(binding,
                    "toRegionInstance"));
            result.addProperty("workload", string(binding, "test"));
            result.addProperty("producerRootCallId",
                    call(producerActivation));
            result.addProperty("targetRootCallId", call(targetActivation));
            result.addProperty("valueFingerprint", string(binding,
                    "valueFingerprint"));
            result.addProperty("valueEqualityAuthority", string(binding,
                    "valueEqualityAuthority"));
            result.addProperty("endpointOrderAuthority", string(binding,
                    "endpointOrderAuthority"));
            result.addProperty("endpointCorrelationAuthority", string(binding,
                    "endpointCorrelationAuthority"));
            result.addProperty("fromEndpointSeq", longValue(binding,
                    "fromEndpointSeq", -1L));
            result.addProperty("toEndpointSeq", longValue(binding,
                    "toEndpointSeq", -1L));
            result.addProperty("uniqueValidatedBinding", true);
            return result;
        }
    }

    public static final class Result {
        public final List<JsonObject> selections;
        public final JsonObject manifest;

        private Result(List<JsonObject> selections, JsonObject manifest) {
            this.selections = Collections.unmodifiableList(
                    new ArrayList<>(selections));
            this.manifest = manifest;
        }
    }

    public static final class Arguments {
        private Path policy;
        private Path regions;
        private Path activationPlan;
        private Path runtimeEdges;
        private Path output;
        private Path manifest;

        public static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            Set<String> allowed = new LinkedHashSet<>(Arrays.asList("policy",
                    "regions", "activation-plan", "runtime-edges", "output",
                    "manifest"));
            for (int index = 0; argv != null && index < argv.length; index++) {
                String key = argv[index];
                if (!key.startsWith("--") || index + 1 >= argv.length
                        || argv[index + 1].startsWith("--")) {
                    throw new IllegalArgumentException(
                            "Expected --key value, got " + key);
                }
                String name = key.substring(2);
                if (!allowed.contains(name)) throw new IllegalArgumentException(
                        "Unknown --" + name);
                if (values.put(name, argv[++index]) != null) {
                    throw new IllegalArgumentException("Duplicate --" + name);
                }
            }
            Arguments result = new Arguments();
            result.policy = required(values, "policy");
            result.regions = required(values, "regions");
            result.activationPlan = required(values, "activation-plan");
            result.runtimeEdges = optional(values, "runtime-edges");
            result.output = required(values, "output");
            result.manifest = required(values, "manifest");
            return result;
        }

        private static Path required(Map<String, String> values, String key) {
            String value = values.get(key);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return Paths.get(value);
        }

        private static Path optional(Map<String, String> values, String key) {
            String value = values.get(key);
            return value == null || value.trim().isEmpty()
                    ? null : Paths.get(value);
        }
    }
}
