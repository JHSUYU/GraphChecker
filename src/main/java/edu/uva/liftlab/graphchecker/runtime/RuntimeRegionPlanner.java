package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.ToNumberPolicy;
import com.google.gson.reflect.TypeToken;
import edu.uva.liftlab.graphchecker.causynth.ProtocolCarrierReconstruction;
import edu.uva.liftlab.graphchecker.concolic.AutomaticRegionEdge;
import edu.uva.liftlab.graphchecker.concolic.JsonFields;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.reflect.Type;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.function.ToLongFunction;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.GZIPInputStream;

/** Binds region skeletons and refined region state to concrete activations. */
final class RuntimeRegionPlanner {
    private static final Type ROW =
            new TypeToken<Map<String, Object>>() { }.getType();
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();
    private static final Pattern FIELD = Pattern.compile(
            "^<[^:]+:\\s+([^()<>]+)\\s+[^\\s()>]+>$");
    private static final Pattern STATIC_SITE = Pattern.compile(
            "^(<.*>)#u([0-9]+)$");

    private RuntimeRegionPlanner() {
    }

    static Result planSkeletonGraph(File skeletonFile,
                                    List<MethodEvent> methods) {
        List<Map<String, Object>> skeletons = read(skeletonFile);
        for (Map<String, Object> row : skeletons) {
            require(row, 3, "REGION_SKELETON", skeletonFile);
        }
        TraceIndex trace = new TraceIndex(methods, Collections.emptyList(),
                Collections.emptyList());
        Result result = new Result();
        result.staticRegionCount = skeletons.size();
        Set<String> skeletonRoots = new LinkedHashSet<>();
        Map<String, Map<String, Object>> authoritativeByRoot =
                new LinkedHashMap<>();
        for (Map<String, Object> skeleton : skeletons) {
            String root = text(skeleton.get("rootMethod"));
            String authority = text(skeleton.get("rootAuthority"));
            if ((!validRootAuthority(authority)
                    && !"NESTED_CALL".equals(authority))
                    || constructor(root)) {
                throw new IllegalArgumentException(
                        "region skeleton has no authoritative execution "
                                + "context root: " + root);
            }
            if (!skeletonRoots.add(root)) {
                throw new IllegalArgumentException(
                        "duplicate region skeleton root: " + root);
            }
            if (validRootAuthority(authority)) {
                authoritativeByRoot.put(root, skeleton);
            }
        }
        Map<Long, Map<String, Object>> activationByCall =
                new LinkedHashMap<>();
        for (Map<String, Object> skeleton : skeletons) {
            if ("NESTED_CALL".equals(text(skeleton.get("rootAuthority")))) {
                continue;
            }
            if ("AUTHORITY_ENVELOPE".equals(text(skeleton.get(
                    "selection")))) {
                continue;
            }
            String rootMethod = text(skeleton.get("rootMethod"));
            List<String> anchors = strings(skeleton.get("anchorMethods"));
            if (anchors.isEmpty()) {
                anchors.add(text(skeleton.get("anchorMethod")));
            }
            for (MethodEvent root : trace.methods(rootMethod)) {
                Set<String> observed = trace.methodNames(
                        trace.subtree(root.callId));
                if (Collections.disjoint(observed, anchors)) {
                    continue;
                }
                addSkeletonActivation(activationByCall, skeleton,
                        root, trace);
            }
        }
        for (Map<String, Object> fragment : skeletons) {
            if (!"NESTED_CALL".equals(text(fragment.get(
                    "rootAuthority")))) {
                continue;
            }
            String endpoint = text(fragment.get("rootMethod"));
            List<String> anchors = anchors(fragment);
            for (MethodEvent nested : trace.methods(endpoint)) {
                Set<String> observed = trace.methodNames(
                        trace.subtree(nested.callId));
                if (Collections.disjoint(observed, anchors)) {
                    continue;
                }
                MethodEvent owner = trace.nearestAuthoritativeAncestor(
                        nested, authoritativeByRoot.keySet());
                if (owner == null) {
                    throw new IllegalStateException("nested protocol "
                            + "endpoint has no authoritative owner: "
                            + endpoint + "#call" + nested.callId);
                }
                mergeNestedFragment(activationByCall,
                        authoritativeByRoot.get(owner.method), fragment,
                        owner, nested, trace);
            }
        }
        result.runtimeInstances.addAll(activationByCall.values());
        for (Map.Entry<Long, Map<String, Object>> entry
                : activationByCall.entrySet()) {
            long parent = trace.nearestAncestor(entry.getKey(),
                    activationByCall.keySet());
            if (parent == 0L) {
                continue;
            }
            Map<String, Object> edge = new LinkedHashMap<>();
            edge.put("schemaVersion", 3);
            edge.put("kind", "RUNTIME_ACTIVATION_EDGE");
            edge.put("fromActivation", activationByCall.get(parent).get(
                    "activationId"));
            edge.put("toActivation", entry.getValue().get("activationId"));
            result.runtimeGraphEdges.add(edge);
        }
        return result;
    }

    private static void addSkeletonActivation(
            Map<Long, Map<String, Object>> activationByCall,
            Map<String, Object> skeleton, MethodEvent root,
            TraceIndex trace) {
        Set<Long> calls = trace.subtree(root.callId);
        Set<String> allowed = new LinkedHashSet<>(
                strings(skeleton.get("methods")));
        calls.removeIf(call -> {
            MethodEvent event = trace.methodByCall.get(call);
            return event == null || !allowed.contains(event.method);
        });
        Set<String> observed = trace.methodNames(calls);
        List<String> observedAnchors = new ArrayList<>();
        for (String anchor : anchors(skeleton)) {
            if (observed.contains(anchor)) {
                observedAnchors.add(anchor);
            }
        }
        if (observedAnchors.isEmpty()) {
            throw new IllegalStateException("selected activation has no "
                    + "observed anchor: " + root.method);
        }
        Map<String, Object> activation = activationByCall.get(root.callId);
        if (activation != null) {
            throw new IllegalStateException("multiple region definitions "
                    + "claimed one execution-context activation: "
                    + root.callId);
        }
        activation = new LinkedHashMap<>();
        activation.put("schemaVersion", 3);
        activation.put("kind", "RUNTIME_REGION_ACTIVATION");
        activation.put("activationId", activationId(root));
        activation.put("regionId", skeleton.get("regionId"));
        activation.put("logicalRegionId", logicalRegionId(
                text(skeleton.get("regionId")), root.ownerId));
        activation.put("regionIds", new ArrayList<>(Collections.singletonList(
                skeleton.get("regionId"))));
        activation.put("rootCallId", root.callId);
        activation.put("rootMethod", root.method);
        activation.put("rootAuthority", skeleton.get("rootAuthority"));
        activation.put("anchorMethod", observedAnchors.get(0));
        activation.put("anchorMethods", observedAnchors);
        activation.put("selection", skeleton.get("selection"));
        activation.put("test", root.test);
        activation.put("process", root.process);
        activation.put("thread", root.threadName);
        activation.put("threadId", root.tid);
        putTraceContext(activation, root);
        activation.put("callIds", new ArrayList<>(calls));
        activation.put("observedMethods", new ArrayList<>(observed));
        activationByCall.put(root.callId, activation);
    }

    private static void mergeNestedFragment(
            Map<Long, Map<String, Object>> activationByCall,
            Map<String, Object> ownerSkeleton,
            Map<String, Object> fragment, MethodEvent owner,
            MethodEvent nested, TraceIndex trace) {
        Set<Long> calls = selectedSubtree(owner, ownerSkeleton, trace);
        calls.addAll(trace.path(owner.callId, nested.callId));
        calls.addAll(selectedSubtree(nested, fragment, trace));
        Set<String> observed = trace.methodNames(calls);
        List<String> observedAnchors = new ArrayList<>();
        for (String anchor : anchors(fragment)) {
            if (observed.contains(anchor)) {
                observedAnchors.add(anchor);
            }
        }
        if (observedAnchors.isEmpty()) {
            throw new IllegalStateException("nested endpoint has no observed "
                    + "semantic anchor: " + nested.method);
        }
        Map<String, Object> activation = activationByCall.get(owner.callId);
        if (activation == null) {
            activation = new LinkedHashMap<>();
            activation.put("schemaVersion", 3);
            activation.put("kind", "RUNTIME_REGION_ACTIVATION");
            activation.put("activationId", activationId(owner));
            activation.put("regionId", ownerSkeleton.get("regionId"));
            activation.put("logicalRegionId", logicalRegionId(
                    text(ownerSkeleton.get("regionId")), owner.ownerId));
            activation.put("regionIds", new ArrayList<>(
                    Collections.singletonList(ownerSkeleton.get("regionId"))));
            activation.put("rootCallId", owner.callId);
            activation.put("rootMethod", owner.method);
            activation.put("rootAuthority",
                    ownerSkeleton.get("rootAuthority"));
            activation.put("selection", fragment.get("selection"));
            activation.put("anchorMethod", observedAnchors.get(0));
            activation.put("anchorMethods", new ArrayList<>(observedAnchors));
            activation.put("test", owner.test);
            activation.put("process", owner.process);
            activation.put("thread", owner.threadName);
            activation.put("threadId", owner.tid);
            putTraceContext(activation, owner);
            activation.put("callIds", new ArrayList<>(calls));
            activation.put("observedMethods", new ArrayList<>(observed));
            activationByCall.put(owner.callId, activation);
        } else {
            mergeList(activation, "callIds", calls);
            mergeList(activation, "observedMethods", observed);
            mergeList(activation, "anchorMethods", observedAnchors);
            if (selectionRank(text(fragment.get("selection")))
                    > selectionRank(text(activation.get("selection")))) {
                activation.put("selection", fragment.get("selection"));
                activation.put("anchorMethod", observedAnchors.get(0));
            }
        }
        mergeList(activation, "regionIds", Collections.singletonList(
                fragment.get("regionId")));
    }

    private static Set<Long> selectedSubtree(
            MethodEvent root, Map<String, Object> skeleton,
            TraceIndex trace) {
        Set<Long> calls = trace.subtree(root.callId);
        Set<String> allowed = new LinkedHashSet<>(
                strings(skeleton.get("methods")));
        calls.removeIf(call -> {
            MethodEvent event = trace.methodByCall.get(call);
            return event == null || !allowed.contains(event.method);
        });
        return calls;
    }

    private static void mergeList(Map<String, Object> row, String field,
                                  Collection<?> additions) {
        Set<Object> merged = new LinkedHashSet<>();
        Object existing = row.get(field);
        if (existing instanceof Collection<?>) {
            merged.addAll((Collection<?>) existing);
        }
        if (additions != null) {
            merged.addAll(additions);
        }
        row.put(field, new ArrayList<>(merged));
    }

    private static int selectionRank(String selection) {
        if (selection != null && selection.startsWith("EXCEPTION")) {
            return 3;
        }
        if (selection != null && selection.startsWith("PROTOCOL")) {
            return 2;
        }
        return 1;
    }

    private static List<String> anchors(Map<String, Object> skeleton) {
        List<String> result = strings(skeleton.get("anchorMethods"));
        if (result.isEmpty() && !text(skeleton.get("anchorMethod")).isEmpty()) {
            result.add(text(skeleton.get("anchorMethod")));
        }
        return result;
    }

    private static boolean constructor(String method) {
        return method != null && (method.contains(" <init>(")
                || method.contains(" <clinit>("));
    }

    private static boolean validRootAuthority(String authority) {
        return "THREAD_ENTRY".equals(authority)
                || "TASK_ENTRY".equals(authority)
                || "MAIN_ENTRY".equals(authority)
                || "RPC_HANDLER".equals(authority);
    }

    static Result plan(File regionFile, File regionEdgeFile,
                       File refinedGraphFile,
                       Collection<Map<String, Object>> runtimeSeeds,
                       List<MethodEvent> methods,
                       List<RuntimeEvent> runtimeEvents,
                       List<FieldAccessEvent> fieldEvents) {
        return plan(read(regionFile), read(regionEdgeFile),
                RefinedFlowIndex.read(refinedGraphFile), regionFile,
                regionEdgeFile, runtimeSeeds, methods, runtimeEvents,
                fieldEvents);
    }

    /** Builds the refined-flow index once from already parsed rows. */
    static RefinedFlowIndex buildFlowIndex(
            List<Map<String, Object>> rows, File source) {
        return RefinedFlowIndex.build(rows, source);
    }

    /**
     * In-memory planning entry point.  {@code regionFile} and
     * {@code regionEdgeFile} only label diagnostics; rows must already be in
     * the exact JSONL value domain the file readers would produce.
     */
    static Result plan(List<Map<String, Object>> regions,
                       List<Map<String, Object>> regionEdges,
                       RefinedFlowIndex refinedFlow,
                       File regionFile, File regionEdgeFile,
                       Collection<Map<String, Object>> runtimeSeeds,
                       List<MethodEvent> methods,
                       List<RuntimeEvent> runtimeEvents,
                       List<FieldAccessEvent> fieldEvents) {
        TraceIndex trace = new TraceIndex(methods, runtimeEvents, fieldEvents);
        Result result = new Result();
        result.staticRegionCount = regions.size();
        Map<String, Map<String, Object>> regionById = new LinkedHashMap<>();
        for (Map<String, Object> region : regions) {
            require(region, 3, "SYMBOLIC_REGION", regionFile);
            if (!"RUNTIME_REFINED_DATAFLOW".equals(
                    text(region.get("graphKind")))) {
                throw new IllegalArgumentException(
                        "region was not planned from the refined graph: "
                                + regionFile);
            }
            regionById.put(text(region.get("regionId")), region);
        }
        Map<String, String> instanceByRegionAndCall = new LinkedHashMap<>();
        Map<String, Map<String, Object>> goalByInstance =
                new LinkedHashMap<>();
        Map<String, Map<String, Object>> planByInstance =
                new LinkedHashMap<>();
        Map<String, String> exactPorts = new LinkedHashMap<>();
        for (Map<String, Object> seed : runtimeSeeds == null
                ? Collections.<Map<String, Object>>emptyList()
                : runtimeSeeds) {
            if (!"RUNTIME_REGION_ACTIVATION".equals(
                    text(seed.get("kind")))) {
                throw new IllegalArgumentException(
                        "concolic planning requires runtime activation seeds");
            }
            String regionId = text(seed.get("regionId"));
            Map<String, Object> region = regionById.get(regionId);
            if (region == null) continue;
            long rootCallId = longNumber(seed.get("rootCallId"), -1L);
            Set<Long> retainedRootCalls = longNumbers(
                    region.get("runtimeRootCallIds"));
            if (retainedRootCalls.isEmpty()) {
                throw new IllegalArgumentException("runtime-refined region "
                        + "has no retained activation seeds: " + regionId);
            }
            if (!retainedRootCalls.contains(rootCallId)) {
                continue;
            }
            Set<String> allowedMethods = new LinkedHashSet<>(
                    strings(region.get("methods")));
            MethodEvent root = trace.methodByCall.get(rootCallId);
            if (root == null) {
                throw new IllegalArgumentException("runtime activation seed "
                        + "references an unknown root call: " + regionId
                        + "#call" + rootCallId);
            }
            Set<Long> calls = longNumbers(seed.get("callIds"));
            if (calls.isEmpty()) calls = trace.subtree(rootCallId);
            Set<String> observedMethods = new LinkedHashSet<>(
                    strings(seed.get("observedMethods")));
            if (observedMethods.isEmpty()) {
                observedMethods.addAll(trace.methodNames(calls));
            }
            observedMethods.retainAll(allowedMethods);
            // Runtime fixes the activation and the concrete sink.  Keep the
            // static region only as a candidate universe: the backward
            // data/control slice may prove that an alternate, baseline-
            // unobserved callee defines that sink.  The completed slice is
            // narrowed again before it becomes executable instrumentation.
            Map<String, Object> activation = new LinkedHashMap<>();
            activation.put("schemaVersion", 3);
            activation.put("kind", "RUNTIME_REGION_ACTIVATION");
            activation.put("activationId", activationId(root));
            activation.put("regionId", region.get("regionId"));
            activation.put("logicalRegionId", logicalRegionId(regionId,
                    root.ownerId));
            activation.put("rootCallId", root.callId);
            activation.put("rootMethod", root.method);
            activation.put("selection", region.get("selection"));
            activation.put("test", root.test);
            activation.put("process", root.process);
            activation.put("thread", root.threadName);
            activation.put("threadId", root.tid);
            putTraceContext(activation, root);
            activation.put("callIds", new ArrayList<>(calls));
            activation.put("observedMethods",
                    new ArrayList<>(observedMethods));
            result.runtimeInstances.add(activation);

            String instanceId = regionId + "@"
                    + safe(root.test) + "#call" + rootCallId;
            boolean target = text(region.get("selection"))
                    .startsWith("EXCEPTION");
            List<Map<String, Object>> symbolize = symbolize(
                    rows(region.get("symbolicInputs")), rootCallId);
            List<Map<String, Object>> branches = branches(
                    rows(region.get("branchPolicies")),
                    trace.runtime(calls));
            ReturnSlice targetSlice = target
                    ? refinedFlow.targetReachSlice(regionId, rootCallId,
                    allowedMethods, rows(region.get("symbolicInputs")),
                    rows(region.get("outputs")),
                    rows(region.get("branchPolicies")), root.method)
                    : null;
            if (targetSlice != null) {
                symbolize = filterByText(symbolize, "symbol",
                        targetSlice.inputPorts);
                branches = filterByText(branches, "siteId",
                        targetSlice.branchSites);
                addMaterializationMethods(targetSlice.methods, symbolize,
                        allowedMethods);
                observedMethods.retainAll(targetSlice.methods);
                allowedMethods = new LinkedHashSet<>(targetSlice.methods);
            }
                Map<String, Object> goal = new LinkedHashMap<>();
                goal.put("goalId", target ? "GOAL.TARGET_REACH."
                        + UUID.nameUUIDFromBytes(instanceId.getBytes(
                        StandardCharsets.UTF_8))
                        : "GOAL.OUTPUT_RELATION."
                        + UUID.nameUUIDFromBytes(instanceId.getBytes(
                        StandardCharsets.UTF_8)));
                goal.put("kind", target ? "TARGET_REACH_CLOSURE"
                        : "OUTPUT_RELATION_CLOSURE");
                goal.put("runtimeDefinitionMethods",
                        new ArrayList<>(allowedMethods));
                goal.put("baselineObservedMethods",
                        new ArrayList<>(observedMethods));
                goal.put("admission", object("state", target
                                ? "READY" : "DISCOVERED",
                        "mode", "RUNTIME_FAILURE_CLOSURE", "blockers",
                        target ? Collections.emptyList()
                                : Collections.singletonList(
                                "OUTPUT_CLOSURE_PENDING")));
                goal.put("symbolize", symbolize);
                goal.put("branches", branches);
                goal.put("edgeBindings", new ArrayList<>());

                Map<String, Object> plan = new LinkedHashMap<>();
                plan.put("schemaVersion", 3);
                plan.put("kind", "CONCOLIC_REGION_PLAN");
                plan.put("regionInstanceId", instanceId);
                plan.put("regionId", region.get("regionId"));
                plan.put("logicalRegionId", logicalRegionId(regionId,
                        root.ownerId));
                putTraceContext(plan, root);
                plan.put("rootCallId", root.callId);
                plan.put("logicalRootCallIds", new ArrayList<>(
                        Collections.singletonList(rootCallId)));
                plan.put("logicalActivationIds", new ArrayList<>(
                        Collections.singletonList(activation.get(
                                "activationId"))));
                plan.put("logicalInstanceCount", 1);
                plan.put("rootSelector", rootSelector(root));
                plan.put("targetMethod", region.get("anchorMethod"));
                plan.put("closureGoals", Collections.singletonList(goal));
                result.regionPlans.add(plan);
                String exactInstance = instanceKey(regionId, rootCallId);
                if (instanceByRegionAndCall.putIfAbsent(exactInstance,
                        instanceId) != null
                        || goalByInstance.putIfAbsent(instanceId,
                        goal) != null) {
                    throw new IllegalArgumentException(
                            "duplicate runtime activation: " + regionId
                                    + "#call" + rootCallId);
                }
                planByInstance.put(instanceId, plan);
                registerExactPorts(region, regionId, rootCallId,
                        exactPorts);
        }
        for (Map<String, Object> edge : regionEdges) {
            String edgeKind = text(edge.get("kind"));
            if (!"RUNTIME_FIELD_FLOW".equals(edgeKind)
                    && !"RUNTIME_PROTOCOL_FLOW".equals(edgeKind)
                    && !"RUNTIME_COORDINATED_STATE_FLOW".equals(edgeKind)) {
                throw new IllegalArgumentException("invalid runtime region "
                        + "flow row in " + regionEdgeFile);
            }
            String fromInstance = instanceByRegionAndCall.get(instanceKey(
                    text(edge.get("fromRegion")),
                    longNumber(edge.get("fromRootCallId"), -1L)));
            String toInstance = instanceByRegionAndCall.get(instanceKey(
                    text(edge.get("toRegion")),
                    longNumber(edge.get("toRootCallId"), -1L)));
            if (fromInstance == null || toInstance == null) {
                throw new IllegalArgumentException(
                        "runtime field flow has no selected activation: "
                                + text(edge.get("edgeId")));
            }
            boolean protocol = "RUNTIME_PROTOCOL_FLOW".equals(edgeKind);
            boolean coordinated =
                    "RUNTIME_COORDINATED_STATE_FLOW".equals(edgeKind);
            boolean containerMutation = "CONTAINER_MUTATION".equals(
                    text(edge.get("bindingKind")));
            if (protocol) {
                long callerSeq = longNumber(edge.get(
                        "callerSiteEventSeq"), -1L);
                long sendSeq = longNumber(edge.get("sendEventSeq"), -1L);
                long receiveSeq = longNumber(edge.get(
                        "receiveEventSeq"), -1L);
                if (!"TRUSTED_CONFIGURED_RPC_MAPPING_V1".equals(
                        text(edge.get("authority")))
                        || text(edge.get("mappingId")).isEmpty()
                        || callerSeq < 0L || callerSeq >= sendSeq
                        || sendSeq >= receiveSeq) {
                    throw new IllegalArgumentException(
                            "runtime protocol flow lacks trusted configured "
                                    + "mapping and ordered call/send/receive: "
                                    + text(edge.get("edgeId")));
                }
            }
            String fromPort = exactPort(exactPorts,
                    text(edge.get("fromRegion")),
                    longNumber(edge.get("fromRootCallId"), -1L),
                    "OUT", text(edge.get("fromPort")), edge);
            String toPort = exactPort(exactPorts,
                    text(edge.get("toRegion")),
                    longNumber(edge.get("toRootCallId"), -1L),
                    "IN", text(edge.get("toPort")), edge);
            Map<String, Object> binding = object(
                    "schemaVersion", 3,
                    "edgeId", edge.get("edgeId"),
                    "fromRegion", edge.get("fromRegion"),
                    "toRegion", edge.get("toRegion"),
                    "transportKind", edge.get("transportKind"),
                    "evidenceKind", protocol
                            ? "TRUSTED_CONFIGURED_RPC_MAPPING_V1"
                            : coordinated
                            ? "DECLARED_FIELD_COORDINATION_CANDIDATE_V1"
                            : containerMutation
                            ? "CONTAINER_MUTATION_READ_FROM_V1"
                            : "FIELD_ASSIGNMENT_READ_FROM_V1",
                    "fromRegionInstance", fromInstance,
                    "toRegionInstance", toInstance,
                    "fromRootCallId", edge.get("fromRootCallId"),
                    "toRootCallId", edge.get("toRootCallId"),
                    "fromOutputPort", fromPort,
                    "toInputPort", toPort,
                    "dependencyRole", edge.get("dependencyRole"),
                    "receiverObjectId", edge.get("receiverObjectId"),
                    "valueObjectId", edge.get("valueObjectId"),
                    "writerReceiverObjectId",
                    edge.get("writerReceiverObjectId"),
                    "readerReceiverObjectId",
                    edge.get("readerReceiverObjectId"),
                    "writerEventSeq", edge.get("writerEventSeq"),
                    "readerEventSeq", edge.get("readerEventSeq"),
                    "writerFieldReadSeq", edge.get("writerFieldReadSeq"),
                    "mutatorEnterSeq", edge.get("mutatorEnterSeq"),
                    "mutationCompletionSeq",
                    edge.get("mutationCompletionSeq"),
                    "mutationInvocationId",
                    edge.get("mutationInvocationId"),
                    "mutatorDeclaredCallee",
                    edge.get("mutatorDeclaredCallee"),
                    "readerValueObjectId",
                    edge.get("readerValueObjectId"),
                    "mappingId", edge.get("mappingId"),
                    "callerMethod", edge.get("callerMethod"),
                    "callerSiteId", edge.get("callerSiteId"),
                    "callerUnitIndex", edge.get("callerUnitIndex"),
                    "callerInvocationId", edge.get("callerInvocationId"),
                    "callerDeclaredCallee",
                    edge.get("callerDeclaredCallee"),
                    "clientArgumentIndex",
                    edge.get("clientArgumentIndex"),
                    "serverParameterIndex",
                    edge.get("serverParameterIndex"),
                    "callerSiteEventSeq",
                    edge.get("callerSiteEventSeq"),
                    "sendEventSeq", edge.get("sendEventSeq"),
                    "receiveEventSeq", edge.get("receiveEventSeq"),
                    "protocolDirection", edge.get("direction"),
                    "protocolPort", edge.get("port"),
                    "fieldPathDeclarations",
                    edge.get("fieldPathDeclarations"),
                    "correlationAuthority",
                    protocol ? "TRUSTED_CONFIGURED_RPC_MAPPING_V1"
                            : coordinated
                            ? "FAILURE_SLICED_DECLARED_FIELD_FAMILY_V1"
                            : "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
            // Preserve the generic static-selection witness for an RPC
            // descendant value.  The RPC mapping proves the cross-region
            // equality; these fields tell the producer planner which exact
            // local container definition implements that projected output.
            for (String field : new String[]{
                    "projectionKind", "rpcDescendantProjection",
                    "projectionSelectionAuthority", "projectionOfEdgeId",
                    "projectionOfFromPort", "projectionOfToPort",
                    "producerProjectionSiteId", "consumerProjectionSiteId",
                    "javaType"}) {
                copyIfPresent(binding, edge, field);
            }
            copyBindingContext(binding, edge,
                    planByInstance.get(fromInstance),
                    planByInstance.get(toInstance));
            Map<String, Object> evidence = new LinkedHashMap<>(edge);
            evidence.put("fromPort", fromPort);
            evidence.put("toPort", toPort);
            evidence.put("state", protocol
                    ? "CONFIRMED_TRUSTED_CONFIGURED_RPC"
                    : coordinated
                    ? "CANDIDATE_COORDINATED_STATE"
                    : "CONFIRMED_RUNTIME_IDENTITY");
            evidence.put("bindings", Collections.singletonList(binding));
            result.edgeValidations.add(evidence);
            Map<String, Object> producerGoal = goalByInstance.get(
                    fromInstance);
            if (producerGoal != null && "OUTPUT_RELATION_CLOSURE".equals(
                    text(producerGoal.get("kind")))) {
                appendGoalBinding(producerGoal, binding);
            }
            Map<String, Object> consumerGoal = goalByInstance.get(
                    toInstance);
            if (consumerGoal != null && consumerGoal != producerGoal) {
                // Consumer protocol arguments are symbolic expressions only
                // when this exact trusted incoming edge is present.  They are
                // not fresh independent leaves.
                appendGoalBinding(consumerGoal, binding);
            }
        }
        finalizeProducerGoals(result.regionPlans, regionById, refinedFlow,
                trace);
        assignPathSeedKeys(result.regionPlans);
        aggregateLogicalPlans(result.regionPlans);
        return result;
    }

    private static void appendGoalBinding(
            Map<String, Object> goal, Map<String, Object> binding) {
        List<Map<String, Object>> bindings = rows(goal.get("edgeBindings"));
        String edgeId = text(binding.get("edgeId"));
        for (Map<String, Object> prior : bindings) {
            if (!edgeId.isEmpty()
                    && edgeId.equals(text(prior.get("edgeId")))
                    && text(binding.get("fromRegionInstance")).equals(
                    text(prior.get("fromRegionInstance")))
                    && text(binding.get("toRegionInstance")).equals(
                    text(prior.get("toRegionInstance")))) {
                return;
            }
        }
        bindings.add(binding);
        goal.put("edgeBindings", bindings);
    }

    /**
     * Names the bounded concrete path observed for each exact activation.
     * Trace call ids deliberately do not participate: repeated activations
     * with the same relevant branch outcomes are interchangeable replay
     * seeds, while distinct outcome combinations remain parallel seeds.
     */
    private static void assignPathSeedKeys(
            List<Map<String, Object>> plans) {
        for (Map<String, Object> plan : plans) {
            for (Map<String, Object> goal
                    : rows(plan.get("closureGoals"))) {
                goal.put("pathSeedKey", pathSeedKey(
                        rows(goal.get("branches"))));
            }
        }
    }

    private static String pathSeedKey(
            List<Map<String, Object>> branches) {
        List<String> decisions = new ArrayList<>();
        for (Map<String, Object> branch : branches) {
            String site = text(branch.get("siteId"));
            if (site.isEmpty()) continue;
            StringBuilder decision = new StringBuilder(site);
            List<Map<String, Object>> occurrences = rows(
                    branch.get("occurrences"));
            if (occurrences.isEmpty()) {
                decision.append("\nUNOBSERVED");
            } else {
                occurrences.sort(Comparator.comparingInt(value ->
                        integer(value.get("occurrence"), Integer.MAX_VALUE)));
                for (Map<String, Object> occurrence : occurrences) {
                    decision.append('\n')
                            .append(integer(occurrence.get("occurrence"), -1))
                            .append('=')
                            .append(String.valueOf(
                                    occurrence.get("outcome")));
                }
            }
            decisions.add(decision.toString());
        }
        Collections.sort(decisions);
        String identity = decisions.isEmpty()
                ? "EMPTY_BOUNDED_PATH" : String.join("\n--\n", decisions);
        return "PATH.SEED." + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    /**
     * Reuses one VM summary plan for repeated activations of the same
     * template/owner pair without weakening the exact runtime evidence.
     *
     * <p>All causal edges are bound before this method runs.  The original
     * invocation plans are therefore copied into {@code occurrences} before
     * executable goals are coalesced.  A retained goal records the exact
     * invocation that must be replayed in {@code executionOccurrence}; the
     * remaining invocations are consumers of that summary, not additional VM
     * jobs.</p>
     */
    private static void aggregateLogicalPlans(
            List<Map<String, Object>> plans) {
        Map<String, List<Map<String, Object>>> byLogicalRegion =
                new LinkedHashMap<>();
        for (Map<String, Object> plan : plans) {
            String logical = text(plan.get("logicalRegionId"));
            if (logical.isEmpty()) {
                logical = text(plan.get("regionInstanceId"));
            }
            byLogicalRegion.computeIfAbsent(logical,
                    ignored -> new ArrayList<>()).add(plan);
        }

        List<Map<String, Object>> aggregated = new ArrayList<>();
        for (Map.Entry<String, List<Map<String, Object>>> entry
                : byLogicalRegion.entrySet()) {
            List<Map<String, Object>> occurrences = entry.getValue();
            occurrences.sort(Comparator
                    .comparingLong((Map<String, Object> value) ->
                            longNumber(value.get("rootCallId"), Long.MAX_VALUE))
                    .thenComparing(value -> text(value.get(
                            "regionInstanceId"))));
            Map<String, Object> representative = occurrences.get(0);
            List<Long> rootCalls = new ArrayList<>();
            List<String> activationIds = new ArrayList<>();
            List<Map<String, Object>> ledger = new ArrayList<>();
            for (Map<String, Object> occurrence : occurrences) {
                rootCalls.add(longNumber(occurrence.get("rootCallId"), -1L));
                activationIds.addAll(strings(occurrence.get(
                        "logicalActivationIds")));
                ledger.add(occurrenceLedger(occurrence));
            }

            representative.put("logicalRegionId", entry.getKey());
            representative.put("logicalRootCallIds", rootCalls);
            representative.put("logicalActivationIds", activationIds);
            representative.put("logicalInstanceCount", occurrences.size());
            representative.put("summaryReuseKey", entry.getKey());
            representative.put("occurrences", ledger);
            representative.put("closureGoals", aggregateLogicalGoals(
                    entry.getKey(), occurrences));
            aggregated.add(representative);
        }
        plans.clear();
        plans.addAll(aggregated);
    }

    private static Map<String, Object> occurrenceLedger(
            Map<String, Object> plan) {
        Map<String, Object> occurrence = deepCopy(plan);
        occurrence.remove("schemaVersion");
        occurrence.remove("kind");
        occurrence.remove("logicalRootCallIds");
        occurrence.remove("logicalActivationIds");
        occurrence.remove("logicalInstanceCount");
        occurrence.remove("summaryReuseKey");
        occurrence.remove("occurrences");
        List<String> activationIds = strings(plan.get(
                "logicalActivationIds"));
        if (!activationIds.isEmpty()) {
            occurrence.put("activationId", activationIds.get(0));
        }
        return occurrence;
    }

    private static List<Map<String, Object>> aggregateLogicalGoals(
            String logicalRegionId,
            List<Map<String, Object>> occurrencePlans) {
        Map<String, Map<String, Object>> bySemanticGoal =
                new LinkedHashMap<>();
        for (Map<String, Object> plan : occurrencePlans) {
            for (Map<String, Object> encoded
                    : rows(plan.get("closureGoals"))) {
                Map<String, Object> goal = deepCopy(encoded);
                goal.put("executionOccurrence", executionOccurrence(plan));
                String semanticKey = semanticGoalKey(goal, plan);
                Map<String, Object> retained = bySemanticGoal.get(
                        semanticKey);
                if (retained == null) {
                    bySemanticGoal.put(semanticKey, goal);
                    continue;
                }
                List<Map<String, Object>> bindings = rows(
                        retained.get("edgeBindings"));
                bindings.addAll(rows(goal.get("edgeBindings")));
                retained.put("edgeBindings", bindings);
            }
        }

        List<Map<String, Object>> result = new ArrayList<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : bySemanticGoal.entrySet()) {
            Map<String, Object> goal = entry.getValue();
            String kind = text(goal.get("kind"));
            String prefix = "TARGET_REACH_CLOSURE".equals(kind)
                    ? "GOAL.TARGET_REACH." : "GOAL.OUTPUT_RELATION.";
            goal.put("goalId", prefix + UUID.nameUUIDFromBytes(
                    (logicalRegionId + "\n" + entry.getKey()).getBytes(
                            StandardCharsets.UTF_8)));
            result.add(goal);
        }
        return result;
    }

    private static Map<String, Object> executionOccurrence(
            Map<String, Object> plan) {
        Map<String, Object> result = new LinkedHashMap<>();
        copyIfPresent(result, plan, "regionInstanceId");
        copyIfPresent(result, plan, "rootCallId");
        copyIfPresent(result, plan, "rootSelector");
        copyIfPresent(result, plan, "targetMethod");
        copyIfPresent(result, plan, "ownerId");
        copyIfPresent(result, plan, "laneId");
        copyIfPresent(result, plan, "spanId");
        copyIfPresent(result, plan, "parentSpanId");
        copyIfPresent(result, plan, "remoteParentSpanId");
        copyIfPresent(result, plan, "process");
        copyIfPresent(result, plan, "thread");
        copyIfPresent(result, plan, "threadId");
        return result;
    }

    private static String semanticGoalKey(Map<String, Object> goal,
                                          Map<String, Object> plan) {
        String kind = text(goal.get("kind"));
        String pathSeed = text(goal.get("pathSeedKey"));
        if ("TARGET_REACH_CLOSURE".equals(kind)) {
            return kind + "\n" + text(plan.get("regionId")) + "\n"
                    + pathSeed;
        }
        Map<String, Object> closure = row(goal.get("outputClosure"));
        if (closure.isEmpty()) {
            // Pending goals are diagnostics and never become VM jobs.  Keep
            // them exact until a structural output closure exists.
            return kind + "\nPENDING\n"
                    + text(plan.get("regionInstanceId")) + "\n"
                    + text(goal.get("goalId"));
        }
        List<String> members = new ArrayList<>();
        for (Map<String, Object> member : rows(closure.get("members"))) {
            Map<String, Object> output = row(member.get("output"));
            Map<String, Object> slice = row(member.get("slice"));
            List<String> structural = new ArrayList<>();
            structural.addAll(strings(slice.get("methods")));
            structural.addAll(strings(slice.get("sites")));
            structural.addAll(strings(slice.get("staticSites")));
            Collections.sort(structural);
            members.add(text(output.get("cell")) + "\n"
                    + text(output.get("kind")) + "\n"
                    + text(output.get("javaTypeDescriptor")) + "\n"
                    + text(output.get("outputSiteId")) + "\n"
                    + integer(output.get("outputOccurrence"), -1) + "\n"
                    + integer(output.get("replayOccurrence"), -1) + "\n"
                    + structural);
        }
        Collections.sort(members);
        // Keep the complete demanded member set in the key.  Path seeding
        // must never collapse distinct multi-output relation contracts.
        return kind + "\n" + pathSeed + "\n" + members;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> row(Object value) {
        return value instanceof Map<?, ?>
                ? (Map<String, Object>) value
                : Collections.emptyMap();
    }

    /**
     * Structural replacement for the previous Gson round-trip copy with the
     * identical value domain: null-valued map entries are dropped, integral
     * numbers become Long, list nulls survive.
     */
    private static Map<String, Object> deepCopy(Map<String, Object> value) {
        return (Map<String, Object>) deepCopyValue(value);
    }

    @SuppressWarnings("unchecked")
    private static Object deepCopyValue(Object value) {
        if (value instanceof Map<?, ?>) {
            Map<String, Object> result = new LinkedHashMap<>();
            for (Map.Entry<?, ?> entry : ((Map<?, ?>) value).entrySet()) {
                if (entry.getValue() == null) continue;
                result.put(String.valueOf(entry.getKey()),
                        deepCopyValue(entry.getValue()));
            }
            return result;
        }
        if (value instanceof Collection<?>) {
            List<Object> result = new ArrayList<>(
                    ((Collection<?>) value).size());
            for (Object item : (Collection<?>) value) {
                result.add(item == null ? null : deepCopyValue(item));
            }
            return result;
        }
        if (value instanceof Integer || value instanceof Short
                || value instanceof Byte) {
            return ((Number) value).longValue();
        }
        if (value instanceof Float) {
            return ((Number) value).doubleValue();
        }
        return value;
    }

    /**
     * Structural replacement for {@code GSON.toJsonTree} over the plain
     * Map/List/scalar rows this planner manipulates; mirrors Gson exactly,
     * including dropped null map entries and JsonNull list members.
     */
    private static JsonElement toJsonTreeFast(Object value) {
        if (value == null) {
            return com.google.gson.JsonNull.INSTANCE;
        }
        if (value instanceof String) {
            return new com.google.gson.JsonPrimitive((String) value);
        }
        if (value instanceof Boolean) {
            return new com.google.gson.JsonPrimitive((Boolean) value);
        }
        if (value instanceof Number) {
            return new com.google.gson.JsonPrimitive((Number) value);
        }
        if (value instanceof Map<?, ?>) {
            JsonObject result = new JsonObject();
            for (Map.Entry<?, ?> entry : ((Map<?, ?>) value).entrySet()) {
                if (entry.getValue() == null) continue;
                result.add(String.valueOf(entry.getKey()),
                        toJsonTreeFast(entry.getValue()));
            }
            return result;
        }
        if (value instanceof Collection<?>) {
            JsonArray result = new JsonArray();
            for (Object item : (Collection<?>) value) {
                result.add(toJsonTreeFast(item));
            }
            return result;
        }
        return GSON.toJsonTree(value);
    }

    private static void copyIfPresent(Map<String, Object> target,
                                      Map<String, Object> source,
                                      String field) {
        if (source.containsKey(field)) target.put(field, source.get(field));
    }

    /**
     * Freezes the complete demanded producer relation.  Repeated writes of
     * one static output are alternate bounded seeds; they are never conjoined
     * as if one VM summary simultaneously represented several loop epochs.
     */
    /**
     * Producer-goal completion is independent per plan over shared
     * read-only inputs (region catalog, refined-flow index, trace index),
     * so plans are processed on a bounded pool; every plan's goals are
     * computed exactly as in the sequential order and written back only to
     * that plan, which keeps results and artifact order byte-identical.
     */
    private static void finalizeProducerGoals(
            List<Map<String, Object>> plans,
            Map<String, Map<String, Object>> regionById,
            RefinedFlowIndex refinedFlow, TraceIndex trace) {
        int configured = Integer.getInteger(
                "causynth.aggregate.threads", 0);
        int threads = configured > 0 ? Math.min(configured, 32)
                : Math.max(1, Math.min(8,
                Runtime.getRuntime().availableProcessors() - 2));
        if (threads <= 1 || plans.size() <= 1) {
            for (Map<String, Object> plan : plans) {
                finalizeProducerGoalsForPlan(plan, regionById, refinedFlow,
                        trace);
            }
            return;
        }
        java.util.concurrent.ExecutorService executor =
                java.util.concurrent.Executors.newFixedThreadPool(threads,
                        runnable -> {
                            Thread thread = new Thread(runnable,
                                    "causynth-producer-goals");
                            thread.setDaemon(true);
                            return thread;
                        });
        try {
            List<java.util.concurrent.Future<?>> pending =
                    new ArrayList<>();
            for (Map<String, Object> plan : plans) {
                pending.add(executor.submit(() ->
                        finalizeProducerGoalsForPlan(plan, regionById,
                                refinedFlow, trace)));
            }
            for (java.util.concurrent.Future<?> future : pending) {
                future.get();
            }
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new IllegalStateException(
                    "producer goal planning interrupted", interrupted);
        } catch (java.util.concurrent.ExecutionException failure) {
            Throwable cause = failure.getCause();
            if (cause instanceof RuntimeException) {
                throw (RuntimeException) cause;
            }
            if (cause instanceof Error) {
                throw (Error) cause;
            }
            throw new IllegalStateException(cause);
        } finally {
            executor.shutdownNow();
        }
    }

    private static void finalizeProducerGoalsForPlan(
            Map<String, Object> plan,
            Map<String, Map<String, Object>> regionById,
            RefinedFlowIndex refinedFlow, TraceIndex trace) {
        {
            List<Map<String, Object>> goals = rows(plan.get("closureGoals"));
            if (goals.size() != 1 || !"OUTPUT_RELATION_CLOSURE".equals(
                    text(goals.get(0).get("kind")))) {
                return;
            }
            Map<String, Object> base = goals.get(0);
            Map<String, Object> producerRegion = regionById.get(
                    text(plan.get("regionId")));
            long producerRootCallId = longNumber(
                    plan.get("rootCallId"), -1L);
            Map<String, List<Map<String, Object>>> byEndpoint =
                    new LinkedHashMap<>();
            List<Map<String, Object>> incomingBindings = new ArrayList<>();
            String producerInstance = text(plan.get("regionInstanceId"));
            for (Map<String, Object> binding
                    : rows(base.get("edgeBindings"))) {
                boolean outgoing = producerInstance.equals(
                        text(binding.get("fromRegionInstance")));
                boolean incoming = producerInstance.equals(
                        text(binding.get("toRegionInstance")));
                String output = outgoing
                        ? text(binding.get("fromOutputPort")) : "";
                if (outgoing && !output.isEmpty()) {
                    String endpoint = semanticOutputEndpoint(binding,
                            producerRegion, producerRootCallId);
                    // Missing endpoint metadata must not merge unrelated
                    // ports. The later closure construction will fail this
                    // unresolved endpoint closed.
                    if (endpoint.isEmpty()) endpoint = "UNRESOLVED:" + output;
                    byEndpoint.computeIfAbsent(endpoint,
                            ignored -> new ArrayList<>()).add(binding);
                }
                if (incoming && !outgoing) incomingBindings.add(binding);
            }
            List<String> demandedEndpoints = new ArrayList<>(
                    byEndpoint.keySet());
            Collections.sort(demandedEndpoints);
            List<Map<String, List<Map<String, Object>>>> alternatives =
                    demandedBindingAlternatives(demandedEndpoints,
                            byEndpoint);
            if (alternatives.isEmpty()) {
                alternatives = Collections.singletonList(
                        Collections.emptyMap());
            }
            List<Map<String, Object>> completeSet = new ArrayList<>();
            int alternative = 0;
            for (Map<String, List<Map<String, Object>>> selected
                    : alternatives) {
                Map<String, Object> goal = deepCopy(base);
                List<Map<String, Object>> selectedBindings =
                        new ArrayList<>(incomingBindings);
                for (String endpoint : demandedEndpoints) {
                    selectedBindings.addAll(selected.getOrDefault(endpoint,
                            Collections.emptyList()));
                }
                goal.put("edgeBindings", selectedBindings);
                String identity = text(plan.get("regionInstanceId"))
                        + "\n" + demandedEndpoints + "\n" + alternative
                        + "\n" + bindingAlternativeIdentity(selected);
                goal.put("goalId", "GOAL.OUTPUT_RELATION."
                        + UUID.nameUUIDFromBytes(identity.getBytes(
                        StandardCharsets.UTF_8)));

                List<OutputClosureContract> members = new ArrayList<>();
                List<String> blockers = new ArrayList<>();
                List<Map<String, Object>> successfulOutgoingBindings =
                        new ArrayList<>();
                if (demandedEndpoints.isEmpty()) {
                    blockers.add("OUTPUT_DEMAND_SET_EMPTY");
                }
                for (String endpoint : demandedEndpoints) {
                    List<Map<String, Object>> outputBindings =
                            selected.getOrDefault(endpoint,
                                    Collections.emptyList());
                    String output = selectedOutputPort(outputBindings);
                    if (output.isEmpty()) {
                        blockers.add("OUTPUT_ENDPOINT_AMBIGUOUS:"
                                + endpoint);
                        continue;
                    }
                    List<String> heapBlockers = new ArrayList<>();
                    OutputClosureContract closure = directHeapOutputClosure(
                            plan, goal,
                            producerRegion,
                            output, outputBindings, refinedFlow, trace,
                            heapBlockers);
                    if (closure == null && heapBlockers.isEmpty()) {
                        closure = directProtocolOutputClosure(
                                plan, goal,
                                producerRegion,
                                output, outputBindings, refinedFlow,
                                bindingOccurrenceRank(outputBindings,
                                        byEndpoint.get(endpoint)));
                    }
                    if (closure == null) {
                        if (heapBlockers.isEmpty()) {
                            blockers.add("OUTPUT_CLOSURE_PENDING:" + output);
                        } else {
                            blockers.addAll(heapBlockers);
                        }
                    } else {
                        members.add(closure);
                        successfulOutgoingBindings.addAll(outputBindings);
                    }
                }

                if (members.isEmpty()) {
                    goal.put("admission", object("state", "DISCOVERED",
                            "mode", "RUNTIME_FAILURE_CLOSURE", "blockers",
                            blockers));
                    goal.put("excludedOutputBlockers", blockers);
                    goal.remove("outputClosure");
                    goal.put("runtimeDefinitionMethods",
                            Collections.emptyList());
                    goal.put("baselineObservedMethods",
                            Collections.emptyList());
                    goal.put("symbolize", Collections.emptyList());
                    goal.put("branches", Collections.emptyList());
                } else {
                    // A demanded endpoint is independently materializable.
                    // An unrelated pending endpoint must not poison the
                    // exact producer relation that the VM can execute.  The
                    // surviving distinct endpoints are still summarized in
                    // one multi-output relation.
                    OutputClosureContract closure =
                            OutputClosureCodec.merge(members);
                    Set<String> inputs = new LinkedHashSet<>(
                            closure.executionScope().inputPorts());
                    List<Map<String, Object>> executableBindings =
                            new ArrayList<>();
                    for (Map<String, Object> incoming : incomingBindings) {
                        if (inputs.contains(text(
                                incoming.get("toInputPort")))) {
                            executableBindings.add(incoming);
                        }
                    }
                    executableBindings.addAll(successfulOutgoingBindings);
                    goal.put("edgeBindings", executableBindings);
                    goal.put("excludedOutputBlockers", blockers);
                    goal.put("admission", object("state", "READY",
                            "mode", "RUNTIME_FAILURE_CLOSURE", "blockers",
                            Collections.emptyList()));
                    goal.put("outputClosure", GSON.fromJson(
                            closure.toJson(), ROW));
                    Set<String> sites = new LinkedHashSet<>(
                            closure.executionScope().branchSites());
                    Set<String> methods = new LinkedHashSet<>(
                            closure.executionScope().methods());
                    goal.put("runtimeDefinitionMethods",
                            new ArrayList<>(methods));
                    Set<String> baseline = new LinkedHashSet<>(strings(
                            goal.get("baselineObservedMethods")));
                    baseline.retainAll(methods);
                    goal.put("baselineObservedMethods",
                            new ArrayList<>(baseline));
                    goal.put("symbolize", filterByText(
                            rows(goal.get("symbolize")), "symbol", inputs));
                    goal.put("branches", filterByText(
                            rows(goal.get("branches")), "siteId", sites));
                }
                completeSet.add(goal);
                alternative++;
            }
            assignOutputOccurrenceIdentity(completeSet);
            plan.put("closureGoals", completeSet);
        }
    }


    /**
     * Identifies a semantic output endpoint independently of the runtime
     * port id. Repeated ports at this endpoint are bounded occurrences, while
     * different endpoint keys are members of one producer relation.
     */
    private static String semanticOutputEndpoint(
            Map<String, Object> binding, Map<String, Object> region,
            long rootCallId) {
        if (region == null) return "";
        String portId = text(binding.get("fromOutputPort"));
        Map<String, Object> port = uniquePort(rows(region.get("outputs")),
                portId, rootCallId);
        if (port == null) return "";
        String cell = text(port.get("cell"));
        if ("PROTOCOL_INPUT".equals(text(port.get("sourceKind")))) {
            return "PROTOCOL\n" + text(binding.get("callerMethod"))
                    + "#u" + integer(binding.get("callerUnitIndex"), -1)
                    + "\n" + text(binding.get("callerDeclaredCallee"))
                    + "\narg" + integer(binding.get(
                    "clientArgumentIndex"), -1)
                    + "\n" + text(binding.get("protocolDirection"))
                    + "\n" + cell;
        }
        Map<String, Object> access = exactDemandedHeapOutput(port,
                Collections.singletonList(binding), rootCallId);
        if (access == null) return "";
        List<String> declarations = strings(
                access.get("fieldPathDeclarations"));
        String declaration = declarations.isEmpty() ? cell
                : declarations.get(declarations.size() - 1);
        String kind = text(access.get("bindingKind"));
        String site = text(access.get("staticAccessSiteId"));
        if (kind.isEmpty() || site.isEmpty() || declaration.isEmpty()) {
            return "";
        }
        return "HEAP\n" + kind + "\n" + site + "\n"
                + text(access.get("mutatorDeclaredCallee")) + "\n"
                + declaration;
    }

    private static String selectedOutputPort(
            List<Map<String, Object>> bindings) {
        String selected = "";
        for (Map<String, Object> binding : bindings) {
            String candidate = text(binding.get("fromOutputPort"));
            if (candidate.isEmpty()) return "";
            if (selected.isEmpty()) selected = candidate;
            else if (!selected.equals(candidate)) return "";
        }
        return selected;
    }

    private static List<Map<String, List<Map<String, Object>>>>
            demandedBindingAlternatives(
            List<String> outputs,
            Map<String, List<Map<String, Object>>> byOutput) {
        Map<String, List<List<Map<String, Object>>>> choicesByOutput =
                new LinkedHashMap<>();
        int alternativeCount = 1;
        for (String output : outputs) {
            Map<Long, List<Map<String, Object>>> grouped =
                    new LinkedHashMap<>();
            List<Map<String, Object>> ordered = new ArrayList<>(
                    byOutput.getOrDefault(output, Collections.emptyList()));
            ordered.sort(Comparator.comparingLong(
                    RuntimeRegionPlanner::bindingOccurrenceSeq));
            for (Map<String, Object> binding : ordered) {
                grouped.computeIfAbsent(bindingOccurrenceSeq(binding),
                        ignored -> new ArrayList<>()).add(binding);
            }
            List<List<Map<String, Object>>> choices = new ArrayList<>(
                    grouped.values());
            if (choices.isEmpty()) choices.add(Collections.emptyList());
            choicesByOutput.put(output, choices);
            alternativeCount = Math.max(alternativeCount,
                    Math.min(choices.size(),
                            LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS));
        }
        List<Map<String, List<Map<String, Object>>>> result =
                new ArrayList<>();
        for (int alternative = 0; alternative < alternativeCount;
             alternative++) {
            Map<String, List<Map<String, Object>>> selected =
                    new LinkedHashMap<>();
            for (String output : outputs) {
                List<List<Map<String, Object>>> choices =
                        choicesByOutput.get(output);
                // Outputs observed once belong to every epoch.  Repeated
                // outputs are aligned by activation-local occurrence instead
                // of forming an artificial Cartesian history.
                selected.put(output, choices.get(Math.min(alternative,
                        choices.size() - 1)));
            }
            result.add(selected);
        }
        return result;
    }

    private static long bindingOccurrenceSeq(Map<String, Object> binding) {
        long writer = longNumber(binding.get("writerEventSeq"), -1L);
        if (writer >= 0L) return writer;
        long caller = longNumber(binding.get("callerSiteEventSeq"), -1L);
        if (caller >= 0L) return caller;
        long send = longNumber(binding.get("sendEventSeq"), -1L);
        if (send >= 0L) return send;
        long receive = longNumber(binding.get("receiveEventSeq"), -1L);
        return receive >= 0L ? receive : Long.MIN_VALUE;
    }

    private static String bindingAlternativeIdentity(
            Map<String, List<Map<String, Object>>> selected) {
        List<String> identity = new ArrayList<>();
        for (Map.Entry<String, List<Map<String, Object>>> entry
                : selected.entrySet()) {
            List<String> edges = new ArrayList<>();
            for (Map<String, Object> binding : entry.getValue()) {
                edges.add(text(binding.get("edgeId")) + "@"
                        + bindingOccurrenceSeq(binding));
            }
            Collections.sort(edges);
            identity.add(entry.getKey() + "=" + edges);
        }
        Collections.sort(identity);
        return identity.toString();
    }

    private static int bindingOccurrenceRank(
            List<Map<String, Object>> selected,
            List<Map<String, Object>> all) {
        if (selected == null || selected.isEmpty()) return 1;
        long target = bindingOccurrenceSeq(selected.get(0));
        Set<Long> ordered = new java.util.TreeSet<>();
        if (all != null) {
            for (Map<String, Object> binding : all) {
                ordered.add(bindingOccurrenceSeq(binding));
            }
        }
        int rank = 1;
        for (Long occurrence : ordered) {
            if (occurrence == target) return rank;
            rank++;
        }
        return 1;
    }

    /**
     * Numbers repeated outputs at one static capture endpoint within the
     * bounded producer activation.  The encounter order is already the
     * causal output order retained by the refined graph.  Only the resulting
     * local ordinal and static endpoint are exported; trace event ids,
     * remote identities and payload/object fingerprints are not identities.
     */
    private static void assignOutputOccurrenceIdentity(
            List<Map<String, Object>> goals) {
        Map<String, Integer> nextByStaticOutput = new LinkedHashMap<>();
        for (Map<String, Object> goal : goals) {
            Map<String, Object> closure = row(goal.get("outputClosure"));
            if (closure.isEmpty()) continue;
            List<Map<String, Object>> members = rows(closure.get("members"));
            for (Map<String, Object> member : members) {
                Map<String, Object> output = row(member.get("output"));
                Map<String, Object> slice = row(member.get("slice"));
                String siteId = staticOutputSiteId(output, slice);
                String shape = text(output.get("cell")) + "\n"
                        + text(output.get("kind")) + "\n"
                        + text(output.get("javaTypeDescriptor")) + "\n"
                        + siteId;
                int explicit = integer(
                        slice.get("activationLocalOccurrence"), -1);
                int occurrence;
                if (explicit > 0) {
                    occurrence = explicit;
                    nextByStaticOutput.merge(shape, occurrence, Math::max);
                } else {
                    occurrence = nextByStaticOutput.compute(shape,
                            (ignored, prior) -> prior == null
                                    ? 1 : prior + 1);
                }
                putOutputOccurrence(output, siteId, occurrence);
                for (Map<String, Object> capture
                        : rows(slice.get("captureBindings"))) {
                    putOutputOccurrence(capture, siteId, occurrence);
                }
            }
        }
    }

    private static String staticOutputSiteId(
            Map<String, Object> output, Map<String, Object> slice) {
        List<String> endpoints = new ArrayList<>();
        for (Map<String, Object> capture
                : rows(slice.get("captureBindings"))) {
            String captureKind = text(capture.get("captureKind"));
            if (OutputCaptureSpec.CALL_ARGUMENT.equals(captureKind)) {
                endpoints.add("CALL_ARGUMENT:"
                        + text(capture.get("definitionMethod")) + "#u"
                        + integer(capture.get("definitionUnitIndex"), -1)
                        + ":" + text(capture.get("declaredCallee"))
                        + "#arg"
                        + integer(capture.get("argumentIndex"), -1));
            } else if (OutputCaptureSpec.MUTATION_STATE.equals(
                    captureKind)) {
                endpoints.add("MUTATION_STATE:"
                        + text(capture.get("definitionMethod")) + "#u"
                        + integer(capture.get("definitionUnitIndex"), -1)
                        + ":" + text(capture.get("declaredCallee"))
                        + ":" + text(capture.get("fieldSignature")));
            } else if (OutputCaptureSpec.FIELD_WRITE_STATE.equals(
                    captureKind)) {
                endpoints.add("FIELD_WRITE_STATE:"
                        + text(capture.get("definitionMethod")) + "#u"
                        + integer(capture.get("definitionUnitIndex"), -1)
                        + ":" + text(capture.get("fieldSignature")));
            } else {
                List<String> path = strings(capture.get("fieldPath"));
                endpoints.add("REGION_EXIT_FIELD:"
                        + text(capture.get("fieldSignature")) + ":"
                        + path);
            }
        }
        if (endpoints.isEmpty()) {
            endpoints.add("REGION_EXIT:" + text(output.get("cell")));
        }
        Collections.sort(endpoints);
        return String.join("|", endpoints);
    }

    private static void putOutputOccurrence(
            Map<String, Object> target, String siteId, int occurrence) {
        target.put("outputSiteId", siteId);
        target.put("outputOccurrence", occurrence);
        target.put("replayOccurrence", occurrence);
    }

    private static OutputClosureContract directHeapOutputClosure(
            Map<String, Object> plan, Map<String, Object> goal,
            Map<String, Object> region, String outputPort,
            List<Map<String, Object>> bindings,
            RefinedFlowIndex refinedFlow, TraceIndex trace,
            List<String> rejectionReasons) {
        if (region == null) return null;
        List<Map<String, Object>> trusted = new ArrayList<>();
        boolean allReadFrom = true;
        boolean allRpcContainerProjection = true;
        for (Map<String, Object> binding : bindings) {
            JsonObject encoded = toJsonTreeFast(binding).getAsJsonObject();
            allReadFrom &= AutomaticRegionEdge
                    .trustedRuntimeReadFromBinding(encoded);
            allRpcContainerProjection &=
                    trustedRpcContainerProjectionBinding(encoded);
            trusted.add(binding);
        }
        if (trusted.isEmpty()
                || !allReadFrom && !allRpcContainerProjection) {
            return null;
        }

        long rootCallId = longNumber(plan.get("rootCallId"), -1L);
        Map<String, Object> outputPortRow = uniquePort(
                rows(region.get("outputs")), outputPort, rootCallId);
        Map<String, Object> output = exactDemandedHeapOutput(
                outputPortRow, trusted, rootCallId);
        if (output == null) return null;
        if (allRpcContainerProjection
                && !trustedRpcContainerProjectionOutput(
                outputPortRow, output, trusted)) {
            return null;
        }
        String staticAccessSiteId = text(output.get("staticAccessSiteId"));
        Matcher staticSite = STATIC_SITE.matcher(staticAccessSiteId);
        int outputOccurrence = integer(output.get(
                "activationLocalStaticSiteOccurrence"), -1);
        String bindingKind = text(output.get("bindingKind"));
        // The recorded ordinal counts every activation-local execution of the
        // site, nested calls included, and the replay no longer has to hit it
        // exactly.  Dropping an output because the recording reached its site
        // often would discard a relation the trace proves.
        if (!staticSite.matches() || outputOccurrence < 1) {
            return null;
        }
        String definitionMethod = staticSite.group(1);
        int definitionUnitIndex = Integer.parseInt(staticSite.group(2));
        boolean mutation = "CONTAINER_MUTATION".equals(bindingKind);
        boolean exactFieldAssignment = true;
        for (Map<String, Object> binding : trusted) {
            exactFieldAssignment &= "FIELD_ASSIGNMENT_READ_FROM_V1".equals(
                    text(binding.get("evidenceKind")));
        }
        boolean directFieldWrite = "DECLARED_FIELD_ACCESS".equals(
                bindingKind) || exactFieldAssignment
                || allRpcContainerProjection;
        String declaredCallee = text(output.get("mutatorDeclaredCallee"));
        if (!mutation && !directFieldWrite
                || mutation && declaredCallee.isEmpty()) {
            return null;
        }
        List<String> path = strings(output.get("fieldPath"));
        List<String> declarations = strings(
                output.get("fieldPathDeclarations"));
        if (path.isEmpty() || path.size() != declarations.size()) return null;
        String declaration = declarations.get(declarations.size() - 1);

        List<Map<String, Object>> regionInputs = rows(
                region.get("symbolicInputs"));
        List<Map<String, Object>> regionOutputs = rows(
                region.get("outputs"));
        Map<String, Object> priorStateInput = null;
        ExactContainerPreState exactPreState = null;
        String javaType = leafType(declarations);
        String owner = fieldOwner(declaration);
        if ("java.lang.Object".equals(javaType) || owner.isEmpty()) {
            return null;
        }

        Set<String> allowed = new LinkedHashSet<>(
                strings(goal.get("runtimeDefinitionMethods")));
        long outputEventSeq = longNumber(output.get("eventSeq"), -1L);
        Set<Long> invocationCalls = trace.exactOutputInvocationCalls(
                rootCallId, outputEventSeq);
        ExactMutationFold mutationFold = null;
        long relationBoundarySeq = Math.max(outputEventSeq,
                longNumber(output.get("mutationCompletionSeq"), -1L));
        if (mutation && invocationCalls != null) {
            mutationFold = trace.exactMutationFold(outputEventSeq,
                    definitionMethod, staticAccessSiteId, declaredCallee,
                    integer(output.get("valueObjectId"), 0));
            // A mutation relation denotes the state at the definition
            // invocation's normal exit.  An anchor in the middle of a loop
            // is not a complete output relation: every later mutation of the
            // same receiver at the statically selected mutator must be
            // observed and stay within the configured bound.
            if (mutationFold == null || mutationFold.completions.isEmpty()
                    || mutationFold.completions.size()
                    > LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS) {
                if (mutationFold != null && mutationFold.completions.size()
                        > LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS) {
                    addBoundInsufficient(rejectionReasons,
                            "MUTATION_FOLD", outputPort,
                            mutationFold.completions.size(),
                            LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS);
                }
                return null;
            }
            relationBoundarySeq = mutationFold.normalExitSeq;
        }
        boolean boundedMutation = mutation
                && "BOUNDED_CONTAINER_STATE".equals(
                text(outputPortRow.get("symbolicDemand")))
                && JavaContainerTypes.shape(javaType)
                != JavaContainerTypes.Shape.NONE;
        if (boundedMutation) {
            if (invocationCalls == null || mutationFold == null) {
                rejectionReasons.add("MISSING_EXACT_CONTAINER_MUTATION_"
                        + "INVOCATION:" + outputPort);
                return null;
            }
            exactPreState = exactContainerPreStateInput(regionInputs,
                    outputPortRow, rootCallId, output, path, declarations,
                    invocationCalls, mutationFold.firstMutationEnterSeq);
            if (exactPreState == null) {
                rejectionReasons.add("MISSING_OR_AMBIGUOUS_EXACT_"
                        + "CONTAINER_PRE_STATE:" + outputPort);
                return null;
            }
            priorStateInput = exactPreState.port;
            if (!refineExactContainerPreStateAction(goal, exactPreState,
                    javaType)) {
                rejectionReasons.add("MISSING_EXACT_CONTAINER_PRE_STATE_"
                        + "ACTION:" + outputPort);
                return null;
            }
        } else {
            priorStateInput = matchingFieldInputBeforeOutput(regionInputs,
                    rootCallId, output, path, declarations);
        }
        if (invocationCalls != null) {
            Set<String> corridorMethods = trace.methodNames(invocationCalls);
            allowed.retainAll(corridorMethods);
            // runtimeDefinitionMethods is a candidate universe, not an
            // authority to cut an exact observed call corridor.  Admit an
            // observed intermediary as a traversal permission; backwardSlice
            // still requires a region-labelled refined-flow edge before the
            // method can enter the emitted relation.  Thus unrelated methods
            // on the long-lived root never leak into the task.
            allowed.addAll(corridorMethods);
        }
        if (!allowed.contains(definitionMethod)) return null;
        Set<String> seedMethods = new LinkedHashSet<>();
        seedMethods.add(text(plan.get("rootMethod")));
        seedMethods.add(text(output.get("rootMethod")));
        Map<String, Object> sliceOutput = output;
        if (!mutation) {
            // Runtime heap ports are rooted at the enclosing activation and
            // may not repeat the defining helper/site on the aggregate port.
            // The selected access does: force the backward slice through that
            // exact HEAP_WRITE so constructor/helper arguments become real VM
            // inputs rather than disappearing at the field boundary.
            sliceOutput = deepCopy(output);
            sliceOutput.put("rootMethod", definitionMethod);
            sliceOutput.put("siteId", staticAccessSiteId);
        }
        ProtocolCarrierReconstruction decode =
                ProtocolCarrierReconstruction.of(regionInputs);
        String carrierPort = decode.responsePortFor(rootCallId,
                outputEventSeq);
        ReturnSlice stateSlice = carrierPort.isEmpty()
                ? refinedFlow.dependencySlice(
                text(plan.get("regionId")), rootCallId, declaration,
                sliceOutput, allowed, regionInputs, regionOutputs,
                rows(region.get("branchPolicies")), seedMethods)
                // A write recorded inside a configured response decode window
                // rebuilds the transferred carrier.  Its operands belong to
                // the serialization implementation, not to this relation, so
                // the demand penetrates to the declared response port.
                : carrierSlice(carrierPort, definitionMethod, allowed,
                text(plan.get("rootMethod")));
        if (stateSlice == null) return null;

        List<String> inputPorts = new ArrayList<>(stateSlice.inputPorts);
        addProtocolCarrierPorts(inputPorts, regionInputs, rootCallId);
        if (priorStateInput != null) {
            String priorStatePort = text(priorStateInput.get("portId"));
            // Mutating an existing container depends on its prior bounded
            // state even when the static def-use graph only records the
            // mutator arguments.  This is a semantic live-in, unlike an
            // owner reference invented solely to find the output object.
            if (!priorStatePort.isEmpty()
                    && !inputPorts.contains(priorStatePort)) {
                inputPorts.add(0, priorStatePort);
            }
        }
        List<String> methods = new ArrayList<>(stateSlice.methods);
        if (methods.isEmpty()) {
            addIfAllowed(methods, allowed, text(output.get("rootMethod")));
            addIfAllowed(methods, allowed, text(plan.get("rootMethod")));
        }
        if (methods.isEmpty()) return null;
        Set<String> methodSet = new LinkedHashSet<>(methods);
        methodSet.add(definitionMethod);
        if (!addReachingAccessorMaterializations(inputPorts, regionInputs,
                rootCallId, methodSet, relationBoundarySeq,
                invocationCalls, rejectionReasons, outputPort)) {
            return null;
        }

        List<String> staticSites = new ArrayList<>(stateSlice.staticSites);
        if (!staticSites.contains(staticAccessSiteId)) {
            staticSites.add(staticAccessSiteId);
        }
        List<String> sites = new ArrayList<>(stateSlice.branchSites);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", outputPort);
        slice.addProperty("outputCell", declaration);
        slice.add("inputPorts", stringsJson(inputPorts));
        slice.add("sites", stringsJson(sites));
        slice.add("staticSites", stringsJson(staticSites));
        slice.add("methods", stringsJson(methods));
        int replayOccurrence = mutationFold == null ? outputOccurrence
                : mutationFold.anchorOccurrence;
        slice.addProperty("activationLocalOccurrence", replayOccurrence);
        slice.addProperty("selectedRuntimeEventSeq", longNumber(
                output.get("eventSeq"), -1L));
        if (mutationFold != null) {
            slice.addProperty("outputBoundaryKind",
                    "DEFINITION_INVOCATION_NORMAL_EXIT");
            slice.addProperty("observedDefinitionCallId",
                    mutationFold.definitionCallId);
            slice.addProperty("definitionCompletionSeq",
                    mutationFold.normalExitSeq);
            slice.addProperty("lastMutationCompletionSeq",
                    mutationFold.completions.get(
                            mutationFold.completions.size() - 1));
            slice.addProperty("foldedMutationCount",
                    mutationFold.completions.size());
            slice.add("foldedMutationCompletionSeqs",
                    toJsonTreeFast(mutationFold.completions));
            if (exactPreState != null) {
                slice.addProperty("containerPreStatePort",
                        text(exactPreState.port.get("portId")));
                slice.addProperty("containerPreStateEventSeq",
                        longNumber(exactPreState.access.get("eventSeq"),
                                -1L));
                slice.addProperty("containerPreStateStaticSiteId",
                        text(exactPreState.access.get(
                                "staticAccessSiteId")));
                slice.addProperty("containerPreStateAuthority",
                        "EARLIEST_READ_IN_EXACT_DEFINITION_INVOCATION_V1");
            }
        } else {
            slice.addProperty("outputBoundaryKind",
                    "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT");
        }
        JsonArray exactBranches = exactBranchReplay(
                rows(region.get("branchPolicies")), stateSlice.branchSites,
                trace, invocationCalls, relationBoundarySeq,
                rejectionReasons, outputPort);
        if (exactBranches == null) return null;
        if (exactBranches.size() > 0) {
            slice.add("branchReplay", exactBranches);
        }
        addConcretePrimitiveCallReturns(slice, trace, invocationCalls,
                stateSlice.staticSites, inputPorts, regionInputs,
                relationBoundarySeq);

        JsonArray edgeIds = new JsonArray();
        JsonArray causalEdges = new JsonArray();
        Set<String> seenEdges = new LinkedHashSet<>();
        for (Map<String, Object> binding : trusted) {
            String edgeId = text(binding.get("edgeId"));
            if (edgeId.isEmpty() || !seenEdges.add(edgeId)) continue;
            edgeIds.add(edgeId);
            causalEdges.add(toJsonTreeFast(binding).getAsJsonObject());
        }
        if (edgeIds.size() == 0) return null;
        slice.add("causalEdgeIds", edgeIds);
        slice.add("causalEdges", causalEdges);

        JsonObject capture = new JsonObject();
        String captureId = "CAPTURE." + UUID.nameUUIDFromBytes((
                text(plan.get("regionInstanceId")) + "\n" + outputPort
                        + "\n" + staticAccessSiteId)
                .getBytes(StandardCharsets.UTF_8));
        capture.addProperty("captureBindingId", captureId);
        capture.addProperty("captureKind", mutation
                ? OutputCaptureSpec.MUTATION_STATE
                : OutputCaptureSpec.FIELD_WRITE_STATE);
        capture.addProperty("outputPort", outputPort);
        capture.addProperty("outputCell", declaration);
        capture.add("fieldPath", stringsJson(Collections.singletonList(
                path.get(path.size() - 1))));
        capture.addProperty("fieldSignature", declaration);
        capture.addProperty("javaType", javaType);
        capture.addProperty("definitionMethod", definitionMethod);
        capture.addProperty("definitionUnitIndex", definitionUnitIndex);
        if (mutation) {
            capture.addProperty("declaredCallee", declaredCallee);
        }
        String captureSiteId = mutation
                ? OutputCaptureSpec.MUTATION_STATE + ":"
                + staticAccessSiteId + ":"
                + declaredCallee + ":" + declaration
                : OutputCaptureSpec.FIELD_WRITE_STATE + ":"
                + staticAccessSiteId + ":"
                + declaration;
        capture.addProperty("outputSiteId", captureSiteId);
        capture.addProperty("outputOccurrence", replayOccurrence);
        capture.addProperty("replayOccurrence", replayOccurrence);
        if (mutationFold != null) {
            capture.addProperty("occurrenceScope",
                    "DEFINITION_INVOCATION");
            capture.addProperty("outputBoundaryKind",
                    "DEFINITION_INVOCATION_NORMAL_EXIT");
            capture.addProperty("definitionCompletionSeq",
                    mutationFold.normalExitSeq);
            capture.addProperty("foldedMutationCount",
                    mutationFold.completions.size());
        } else {
            capture.addProperty("occurrenceScope",
                    OutputCaptureSpec.REGION_ACTIVATION_SCOPE);
            capture.addProperty("outputBoundaryKind",
                    "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT");
        }
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());

        return OutputClosureCodec.singleton(
                text(plan.get("regionId")),
                text(plan.get("regionInstanceId")), rootCallId,
                outputPort, declaration, "HEAP_STATE", javaType, slice);
    }

    /**
     * A configured RPC mapping can project one failure-relevant descendant
     * without turning the complete wire object into a symbolic value.  The
     * descendant is either a bounded container or a semantic scalar leaf.
     * This remains an equality witness; it is accepted by the heap closure
     * only because the finalizer also selected one exact local HEAP_WRITE
     * that the VM can capture.
     */
    private static boolean trustedRpcContainerProjectionBinding(
            JsonObject binding) {
        String kind = JsonFields.string(binding, "projectionKind");
        String selection = JsonFields.string(binding,
                "projectionSelectionAuthority");
        boolean declaredKind =
                "BOUNDED_CONTAINER_STATE".equals(kind)
                        && "STATIC_DEF_USE_CONTAINER_PROJECTION_V1".equals(
                        selection)
                        || "SCALAR_LEAF_VALUE".equals(kind)
                        && "STATIC_DEF_USE_SCALAR_LEAF_PROJECTION_V1".equals(
                        selection);
        return AutomaticRegionEdge.trustedRuntimeValueEqualityBinding(binding)
                && JsonFields.bool(binding, "rpcDescendantProjection", false)
                && declaredKind
                && !JsonFields.string(binding,
                "producerProjectionSiteId").isEmpty();
    }

    private static boolean trustedRpcContainerProjectionOutput(
            Map<String, Object> port, Map<String, Object> exact,
            List<Map<String, Object>> bindings) {
        String selection = text(port.get("rpcProjectionSelectionAuthority"));
        String demand = text(port.get("symbolicDemand"));
        boolean declaredKind =
                "STATIC_DEF_USE_CONTAINER_PROJECTION_V1".equals(selection)
                        && "BOUNDED_CONTAINER_STATE".equals(demand)
                        || "STATIC_DEF_USE_SCALAR_LEAF_PROJECTION_V1".equals(
                        selection) && demand.isEmpty();
        if (!Boolean.TRUE.equals(port.get("rpcDescendantProjectionOutput"))
                || !declaredKind
                || !"TRUSTED_CONFIGURED_RPC_MAPPING_V1".equals(
                text(port.get("rpcProjectionAuthority")))) {
            return false;
        }
        String mapping = text(port.get("rpcProjectionMappingId"));
        String declaration = text(port.get(
                "rpcProjectionFieldDeclaration"));
        String site = text(port.get("rpcProjectionStaticAccessSiteId"));
        List<String> declarations = strings(
                exact.get("fieldPathDeclarations"));
        if (mapping.isEmpty() || declaration.isEmpty() || site.isEmpty()
                || declarations.isEmpty()
                || !declaration.equals(declarations.get(
                declarations.size() - 1))
                || !site.equals(text(exact.get("staticAccessSiteId")))) {
            return false;
        }
        for (Map<String, Object> binding : bindings) {
            if (!mapping.equals(text(binding.get("mappingId")))
                    || !site.equals(text(binding.get(
                    "producerProjectionSiteId")))) {
                return false;
            }
        }
        return true;
    }

    /**
     * Adds only accessor observations that can reach the selected exact
     * output. A long-lived activation may execute one accessor in several
     * loop epochs, including after the demanded mutation. Those observations
     * are alternatives rather than simultaneous relation inputs, so each
     * static accessor endpoint contributes its latest preceding occurrence.
     */
    static void addReachingAccessorMaterializations(
            List<String> inputPorts,
            List<Map<String, Object>> regionInputs,
            long rootCallId, Set<String> selectedMethods,
            long outputBoundarySeq) {
        addReachingAccessorMaterializations(inputPorts, regionInputs,
                rootCallId, selectedMethods, outputBoundarySeq, null,
                null, "");
    }

    private static boolean addReachingAccessorMaterializations(
            List<String> inputPorts,
            List<Map<String, Object>> regionInputs,
            long rootCallId, Set<String> selectedMethods,
            long outputBoundarySeq, Set<Long> invocationCalls,
            List<String> rejectionReasons, String outputPort) {
        if (outputBoundarySeq < 0L) return true;
        if (invocationCalls != null) {
            Map<String, List<Map<String, Object>>> byActivationEndpoint =
                    new LinkedHashMap<>();
            for (Map<String, Object> candidate : regionInputs) {
                if (longNumber(candidate.get("rootCallId"), -1L)
                        != rootCallId
                        || !"ACCESSOR_RETURN".equals(
                        text(candidate.get("sourceKind")))) {
                    continue;
                }
                MaterializationSpec materialization =
                        MaterializationSpec.decode(
                                toJsonTreeFast(candidate)
                                        .getAsJsonObject());
                long callId = longNumber(candidate.get("callId"), -1L);
                long eventSeq = longNumber(candidate.get("eventSeq"), -1L);
                if (materialization.kind()
                        != MaterializationSpec.Kind.ACCESSOR_RETURN
                        || !selectedMethods.contains(
                        materialization.method())
                        || !invocationCalls.contains(callId)
                        || eventSeq < 0L || eventSeq > outputBoundarySeq) {
                    continue;
                }
                String endpoint = callId + "\n"
                        + materialization.siteId() + "\n"
                        + materialization.declaredCallee() + "\n"
                        + materialization.implementationMethod() + "\n"
                        + materialization.leafField() + "\n"
                        + materialization.path();
                byActivationEndpoint.computeIfAbsent(endpoint,
                        ignored -> new ArrayList<>()).add(candidate);
            }
            List<Map<String, Object>> selected = new ArrayList<>();
            for (List<Map<String, Object>> candidates
                    : byActivationEndpoint.values()) {
                candidates.sort(Comparator.comparingLong(value ->
                        longNumber(value.get("eventSeq"), Long.MAX_VALUE)));
                if (candidates.size() > LoopBoundPolicy
                        .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY) {
                    addBoundInsufficient(rejectionReasons,
                            "ACCESSOR_MATERIALIZATION", outputPort,
                            candidates.size(), LoopBoundPolicy
                                    .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY);
                    return false;
                }
                selected.addAll(candidates);
            }
            selected.sort(Comparator.comparingLong(value ->
                    longNumber(value.get("eventSeq"), Long.MAX_VALUE)));
            for (Map<String, Object> candidate : selected) {
                String port = text(candidate.get("portId"));
                if (!port.isEmpty() && !inputPorts.contains(port)) {
                    inputPorts.add(port);
                }
            }
            return true;
        }

        Map<String, Map<String, Object>> latestByEndpoint =
                new LinkedHashMap<>();
        Set<String> ambiguousEndpoints = new LinkedHashSet<>();
        for (Map<String, Object> candidate : regionInputs) {
            if (longNumber(candidate.get("rootCallId"), -1L) != rootCallId
                    || !"ACCESSOR_RETURN".equals(
                    text(candidate.get("sourceKind")))) {
                continue;
            }
            MaterializationSpec materialization = MaterializationSpec.decode(
                    toJsonTreeFast(candidate).getAsJsonObject());
            long eventSeq = longNumber(candidate.get("eventSeq"), -1L);
            if (materialization.kind()
                    != MaterializationSpec.Kind.ACCESSOR_RETURN
                    || !selectedMethods.contains(materialization.method())
                    || eventSeq < 0L || eventSeq > outputBoundarySeq) {
                continue;
            }
            String endpoint = materialization.siteId() + "\n"
                    + materialization.declaredCallee() + "\n"
                    + materialization.implementationMethod() + "\n"
                    + materialization.leafField() + "\n"
                    + materialization.path();
            Map<String, Object> prior = latestByEndpoint.get(endpoint);
            long priorSeq = prior == null ? -1L
                    : longNumber(prior.get("eventSeq"), -1L);
            if (eventSeq > priorSeq) {
                latestByEndpoint.put(endpoint, candidate);
                ambiguousEndpoints.remove(endpoint);
            } else if (eventSeq == priorSeq && prior != null
                    && !text(prior.get("portId")).equals(
                    text(candidate.get("portId")))) {
                ambiguousEndpoints.add(endpoint);
            }
        }
        for (Map.Entry<String, Map<String, Object>> selected
                : latestByEndpoint.entrySet()) {
            if (ambiguousEndpoints.contains(selected.getKey())) continue;
            String port = text(selected.getValue().get("portId"));
            if (!port.isEmpty() && !inputPorts.contains(port)) {
                inputPorts.add(port);
            }
        }
        return true;
    }

    /** Exact, invocation-local replay ordinals for a projected output. */
    private static JsonArray exactBranchReplay(
            List<Map<String, Object>> policies, Set<String> selectedSites,
            TraceIndex trace, Set<Long> invocationCalls,
            long outputBoundarySeq, List<String> rejectionReasons,
            String outputPort) {
        JsonArray result = new JsonArray();
        if (invocationCalls == null || selectedSites.isEmpty()
                || outputBoundarySeq < 0L) {
            return result;
        }
        Map<String, Map<Long, List<RuntimeEvent>>> bySiteAndCall =
                new LinkedHashMap<>();
        for (RuntimeEvent event : trace.runtime(invocationCalls)) {
            if (!"BRANCH".equals(event.kind)
                    || event.seq > outputBoundarySeq
                    || !selectedSites.contains(event.siteId)) {
                continue;
            }
            bySiteAndCall.computeIfAbsent(event.siteId,
                    ignored -> new LinkedHashMap<>())
                    .computeIfAbsent(event.callId,
                            ignored -> new ArrayList<>()).add(event);
        }
        for (Map<String, Object> policy : policies) {
            String site = text(policy.get("siteId"));
            if (!selectedSites.contains(site)) continue;
            Map<Long, List<RuntimeEvent>> byCall = bySiteAndCall.get(site);
            if (byCall == null || byCall.isEmpty()) continue;
            List<RuntimeEvent> selected = null;
            for (List<RuntimeEvent> events : byCall.values()) {
                events.sort(Comparator.comparingLong(value -> value.seq));
                if (selected == null || events.get(events.size() - 1).seq
                        > selected.get(selected.size() - 1).seq) {
                    selected = events;
                }
            }
            if (selected == null || selected.isEmpty()) continue;
            if (selected.size()
                    > LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS) {
                // Truncating an exact demanded branch stream changes the
                // state relation.  Let the caller reject this closure so the
                // configured bound can be raised explicitly.
                addBoundInsufficient(rejectionReasons, "BRANCH_REPLAY",
                        outputPort, selected.size(),
                        LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS);
                return null;
            }
            RuntimeEvent last = selected.get(selected.size() - 1);
            Map<String, Object> replay = new LinkedHashMap<>(policy);
            replay.put("observed", true);
            replay.put("observedOutcome", last.outcome);
            replay.put("selectedOccurrence", selected.size());
            replay.put("selectedRuntimeEventSeq", last.seq);
            replay.put("selectedCallId", last.callId);
            List<Map<String, Object>> occurrences = new ArrayList<>();
            for (int index = 0; index < selected.size(); index++) {
                RuntimeEvent event = selected.get(index);
                occurrences.add(object("occurrence", index + 1,
                        "outcome", event.outcome,
                        "eventSeq", event.seq,
                        "callId", event.callId));
            }
            replay.put("occurrences", occurrences);
            result.add(toJsonTreeFast(replay));
        }
        return result;
    }

    private static void addBoundInsufficient(
            List<String> rejectionReasons, String kind, String outputPort,
            int required, int configured) {
        if (rejectionReasons == null) return;
        rejectionReasons.add("BOUND_INSUFFICIENT:" + safe(kind) + ":"
                + safe(outputPort) + ":required=" + required
                + ":configured=" + configured);
    }

    /**
     * Records selected primitive call returns that intentionally remain
     * concrete.  They are evidence for selective execution, never input
     * actions, so a missing environment model cannot silently become a free
     * SMT variable.
     */
    private static void addConcretePrimitiveCallReturns(
            JsonObject slice, TraceIndex trace, Set<Long> invocationCalls,
            Set<String> selectedSites, List<String> symbolicInputPorts,
            List<Map<String, Object>> regionInputs, long boundarySeq) {
        if (invocationCalls == null || selectedSites.isEmpty()
                || boundarySeq < 0L) {
            return;
        }
        Set<String> symbolicAccessorSites = new LinkedHashSet<>();
        Set<String> selectedPorts = new LinkedHashSet<>(symbolicInputPorts);
        for (Map<String, Object> input : regionInputs) {
            if (!selectedPorts.contains(text(input.get("portId")))) continue;
            MaterializationSpec materialization = MaterializationSpec.decode(
                    toJsonTreeFast(input).getAsJsonObject());
            if (materialization.kind()
                    == MaterializationSpec.Kind.ACCESSOR_RETURN) {
                symbolicAccessorSites.add(materialization.siteId());
            }
        }
        List<RuntimeEvent> events = trace.runtime(invocationCalls);
        JsonArray concrete = new JsonArray();
        Set<String> seen = new LinkedHashSet<>();
        for (RuntimeEvent event : events) {
            if (!"CALL_SITE_RETURN".equals(event.kind)
                    || event.seq > boundarySeq
                    || event.primitiveValue.isEmpty()
                    || !selectedSites.contains(event.siteId)
                    || symbolicAccessorSites.contains(event.siteId)) {
                continue;
            }
            String identity = event.callId + "\n" + event.siteId;
            if (!seen.add(identity)) continue;
            JsonObject value = new JsonObject();
            value.addProperty("policy", "CONCRETE_REPLAY_VALUE");
            value.addProperty("authority",
                    "EXACT_RUNTIME_PRIMITIVE_CALL_RETURN_V1");
            value.addProperty("method", event.method);
            value.addProperty("siteId", event.siteId);
            value.addProperty("declaredCallee", event.declaredCallee);
            value.addProperty("eventSeq", event.seq);
            value.addProperty("primitiveValue", event.primitiveValue);
            concrete.add(value);
        }
        if (concrete.size() > 0) {
            slice.add("concreteCallReturns", concrete);
        }
    }

    /**
     * Materializes the concrete write selected by the demanded causal edge.
     * A region port can aggregate many writes from one long-lived root; its
     * first top-level access is therefore not an adequate replay seed.
     */
    private static Map<String, Object> exactDemandedHeapOutput(
            Map<String, Object> port,
            List<Map<String, Object>> bindings,
            long rootCallId) {
        if (port == null || bindings.isEmpty()) return null;
        Set<Long> writerSeqs = new LinkedHashSet<>();
        Set<Long> completionSeqs = new LinkedHashSet<>();
        for (Map<String, Object> binding : bindings) {
            long writer = longNumber(binding.get("writerEventSeq"), -1L);
            long completion = longNumber(
                    binding.get("mutationCompletionSeq"), -1L);
            if (writer >= 0L) writerSeqs.add(writer);
            if (completion >= 0L) completionSeqs.add(completion);
        }
        if (writerSeqs.size() > 1 || completionSeqs.size() > 1) {
            return null;
        }
        long writer = writerSeqs.isEmpty() ? -1L
                : writerSeqs.iterator().next();
        long completion = completionSeqs.isEmpty() ? -1L
                : completionSeqs.iterator().next();

        List<Map<String, Object>> accesses = new ArrayList<>(
                rows(port.get("runtimeAccesses")));
        if (accesses.isEmpty()) return null;
        accesses.sort(Comparator.comparingLong(value ->
                longNumber(value.get("eventSeq"), Long.MAX_VALUE)));
        Map<String, Object> selected = null;
        for (Map<String, Object> access : accesses) {
            if (longNumber(access.get("rootCallId"), rootCallId)
                    != rootCallId) {
                continue;
            }
            long event = longNumber(access.get("eventSeq"), -1L);
            long accessCompletion = longNumber(
                    access.get("mutationCompletionSeq"), -1L);
            if ((writer >= 0L && event != writer)
                    || (completion >= 0L
                    && accessCompletion != completion)) {
                continue;
            }
            if (selected != null) return null;
            selected = access;
        }
        if (selected == null) return null;
        String site = text(selected.get("staticAccessSiteId"));
        int occurrence = integer(selected.get(
                "activationLocalStaticSiteOccurrence"), -1);
        // The recorded ordinal counts every activation-local execution of the
        // site, nested calls included, and the replay no longer has to hit it
        // exactly (the same rule directHeapOutputClosure already applies).
        // Capping it here silently dropped the only mutation writer of a
        // demanded container input, leaving that input without a producer in
        // the demanded closure.  The mutation fold still bounds how many
        // mutations one definition invocation may perform.
        if (!STATIC_SITE.matcher(site).matches() || occurrence < 1) {
            return null;
        }
        Map<String, Object> exact = deepCopy(port);
        for (Map.Entry<String, Object> entry : selected.entrySet()) {
            exact.put(entry.getKey(), entry.getValue());
        }
        return exact;
    }

    /** Freezes an exact request argument or server return protocol value. */
    private static OutputClosureContract directProtocolOutputClosure(
            Map<String, Object> plan, Map<String, Object> goal,
            Map<String, Object> region, String outputPort,
            List<Map<String, Object>> bindings,
            RefinedFlowIndex refinedFlow,
            int activationLocalOccurrence) {
        if (region == null) return null;
        List<Map<String, Object>> trusted = new ArrayList<>();
        for (Map<String, Object> binding : bindings) {
            JsonObject encoded = toJsonTreeFast(binding).getAsJsonObject();
            if (AutomaticRegionEdge.trustedRuntimeValueEqualityBinding(
                    encoded)) {
                trusted.add(binding);
            }
        }
        if (trusted.size() != bindings.size() || trusted.isEmpty()) {
            return null;
        }

        long rootCallId = longNumber(plan.get("rootCallId"), -1L);
        Map<String, Object> output = uniquePort(
                rows(region.get("outputs")), outputPort, rootCallId);
        if (output == null
                || !"PROTOCOL_INPUT".equals(text(output.get("sourceKind")))) {
            return null;
        }
        String direction = text(output.get("protocolDirection"));
        if (!"REQUEST".equals(direction) && !"RESPONSE".equals(direction)) {
            return null;
        }
        String outputCell = text(output.get("cell"));
        String rootMethod = text(plan.get("rootMethod"));
        if (rootMethod.isEmpty()) rootMethod = text(region.get("rootMethod"));
        if ("RESPONSE".equals(direction)
                && !outputCell.equals(rootMethod + ".return")) return null;

        String captureMethod = "";
        String captureSite = "";
        String captureCallee = "";
        int captureUnit = -1;
        int captureArgument = -1;
        if ("REQUEST".equals(direction)) {
            for (Map<String, Object> binding : trusted) {
                String method = text(binding.get("callerMethod"));
                String site = text(binding.get("callerSiteId"));
                String callee = text(binding.get("callerDeclaredCallee"));
                int unit = integer(binding.get("callerUnitIndex"), -1);
                int argument = integer(binding.get("clientArgumentIndex"),
                        -1);
                if (method.isEmpty() || site.isEmpty() || callee.isEmpty()
                        || unit < 0 || argument < 0
                        || !site.equals(method + "#u" + unit)) {
                    return null;
                }
                if (captureMethod.isEmpty()) {
                    captureMethod = method;
                    captureSite = site;
                    captureCallee = callee;
                    captureUnit = unit;
                    captureArgument = argument;
                } else if (!captureMethod.equals(method)
                        || !captureSite.equals(site)
                        || !captureCallee.equals(callee)
                        || captureUnit != unit
                        || captureArgument != argument) {
                    return null;
                }
            }
        }

        Set<String> allowed = new LinkedHashSet<>(
                strings(goal.get("runtimeDefinitionMethods")));
        Set<String> seedMethods = new LinkedHashSet<>();
        seedMethods.add(rootMethod);
        seedMethods.add(captureMethod);
        long protocolOccurrenceSeq = bindingOccurrenceSeq(trusted.get(0));
        Map<String, Object> exactProtocolOutput = protocolOccurrenceSeq >= 0L
                ? object("eventSeq", protocolOccurrenceSeq)
                : null;
        ReturnSlice returnSlice = refinedFlow.dependencySlice(
                text(plan.get("regionId")), rootCallId, outputCell,
                exactProtocolOutput, allowed,
                rows(region.get("symbolicInputs")),
                rows(region.get("outputs")),
                rows(region.get("branchPolicies")), seedMethods);
        if (returnSlice == null) return null;

        Set<String> methodSet = new LinkedHashSet<>(returnSlice.methods);
        methodSet.add(rootMethod);
        if (!captureMethod.isEmpty()) methodSet.add(captureMethod);
        List<String> methods = new ArrayList<>(methodSet);
        List<String> sites = new ArrayList<>(returnSlice.branchSites);
        List<String> inputPorts = new ArrayList<>(returnSlice.inputPorts);
        addProtocolCarrierPorts(inputPorts,
                rows(region.get("symbolicInputs")), rootCallId);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", outputPort);
        slice.addProperty("outputCell", outputCell);
        slice.add("inputPorts", stringsJson(inputPorts));
        slice.add("sites", stringsJson(sites));
        slice.add("staticSites", stringsJson(returnSlice.staticSites));
        if (!captureSite.isEmpty()
                && !returnSlice.staticSites.contains(captureSite)) {
            JsonArray staticSites = slice.getAsJsonArray("staticSites");
            staticSites.add(captureSite);
        }
        slice.add("methods", stringsJson(methods));
        slice.addProperty("activationLocalOccurrence",
                Math.max(1, activationLocalOccurrence));
        slice.addProperty("selectedRuntimeEventSeq",
                protocolOccurrenceSeq);

        JsonArray edgeIds = new JsonArray();
        JsonArray causalEdges = new JsonArray();
        Set<String> seenEdges = new LinkedHashSet<>();
        for (Map<String, Object> binding : trusted) {
            String edgeId = text(binding.get("edgeId"));
            if (edgeId.isEmpty() || !seenEdges.add(edgeId)) continue;
            edgeIds.add(edgeId);
            causalEdges.add(toJsonTreeFast(binding).getAsJsonObject());
        }
        if (edgeIds.size() == 0) return null;
        slice.add("causalEdgeIds", edgeIds);
        slice.add("causalEdges", causalEdges);
        JsonArray captures = new JsonArray();
        String javaType;
        String outputKind;
        if ("REQUEST".equals(direction)) {
            javaType = methodParameterType(captureCallee, captureArgument);
            if (javaType.isEmpty()) return null;
            JsonObject capture = new JsonObject();
            capture.addProperty("captureBindingId", "CAPTURE."
                    + UUID.nameUUIDFromBytes((text(plan.get(
                    "regionInstanceId")) + "\n" + outputPort + "\n"
                    + captureSite + "\n" + captureArgument).getBytes(
                    StandardCharsets.UTF_8)));
            capture.addProperty("captureKind", "CALL_ARGUMENT");
            capture.addProperty("outputPort", outputPort);
            capture.addProperty("outputCell", outputCell);
            capture.addProperty("definitionMethod", captureMethod);
            capture.addProperty("definitionUnitIndex", captureUnit);
            capture.addProperty("declaredCallee", captureCallee);
            capture.addProperty("argumentIndex", captureArgument);
            capture.addProperty("javaType", javaType);
            captures.add(capture);
            outputKind = "REGION_OUTPUT";
        } else {
            javaType = methodReturnType(rootMethod);
            if (javaType.isEmpty() || "void".equals(javaType)) return null;
            outputKind = "RETURN";
        }
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());
        return OutputClosureCodec.singleton(
                text(plan.get("regionId")),
                text(plan.get("regionInstanceId")), rootCallId,
                outputPort, outputCell, outputKind, javaType, slice);
    }

    private static Map<String, Object> uniquePort(
            List<Map<String, Object>> ports, String portId, long rootCallId) {
        Map<String, Object> match = null;
        for (Map<String, Object> port : ports) {
            long boundRoot = "PROTOCOL_INPUT".equals(
                    text(port.get("sourceKind")))
                    ? longNumber(port.get("fromRootCallId"), -1L)
                    : longNumber(port.get("rootCallId"), -1L);
            if (!portId.equals(text(port.get("portId")))
                    || boundRoot != rootCallId) {
                continue;
            }
            if (match != null) return null;
            match = port;
        }
        return match;
    }

    /**
     * Selects the container live-in at the first exact field read in the
     * mutation definition invocation.  Trace call ids are evidence for this
     * selection only; replay is constrained by the static access site and
     * does not depend on the discovery run's root call id.
     */
    private static ExactContainerPreState exactContainerPreStateInput(
            List<Map<String, Object>> inputs,
            Map<String, Object> outputPort, long rootCallId,
            Map<String, Object> output, List<String> path,
            List<String> declarations, Set<Long> invocationCalls,
            long firstMutationEnterSeq) {
        if (firstMutationEnterSeq < 0L || invocationCalls == null
                || invocationCalls.isEmpty()
                || !"PROVED".equals(text(outputPort.get(
                "boundedContainerStateAdmission")))) {
            return null;
        }
        Set<String> admittedPorts = new LinkedHashSet<>(strings(
                outputPort.get("boundedContainerPreStatePorts")));
        if (admittedPorts.isEmpty()) return null;
        long owner = longNumber(output.get("fieldReceiverObjectId"),
                longNumber(output.get("rootObjectId"), 0L));
        int container = integer(output.get("valueObjectId"), 0);
        ExactContainerPreState selected = null;
        long selectedSeq = Long.MAX_VALUE;
        for (Map<String, Object> input : inputs) {
            String portId = text(input.get("portId"));
            long inputOwner = longNumber(input.get(
                            "fieldReceiverObjectId"),
                    longNumber(input.get("rootObjectId"), 0L));
            if (!admittedPorts.contains(portId)
                    || longNumber(input.get("rootCallId"), -1L)
                    != rootCallId
                    || owner <= 0L || owner != inputOwner
                    || !path.equals(strings(input.get("fieldPath")))
                    || !declarations.equals(strings(
                    input.get("fieldPathDeclarations")))
                    || !"BOUNDED_CONTAINER_STATE".equals(
                    text(input.get("symbolicDemand")))
                    || !"EXACT_RUNTIME_CONTAINER_MUTATION_STATE_CHAIN_V1"
                    .equals(text(input.get(
                            "boundedContainerStateAuthority")))) {
                continue;
            }
            for (Map<String, Object> access
                    : rows(input.get("runtimeAccesses"))) {
                long callId = longNumber(access.get("callId"), -1L);
                long seq = longNumber(access.get("eventSeq"), -1L);
                int observedContainer = integer(
                        access.get("valueObjectId"), 0);
                String site = text(access.get("staticAccessSiteId"));
                if (!invocationCalls.contains(callId)
                        || seq < 0L || seq >= firstMutationEnterSeq
                        || integer(access.get("fieldReceiverObjectId"), 0)
                        != owner
                        || container > 0 && observedContainer != container
                        || !declarations.equals(strings(access.get(
                        "fieldPathDeclarations")))
                        || !STATIC_SITE.matcher(site).matches()) {
                    continue;
                }
                if (seq < selectedSeq) {
                    selected = new ExactContainerPreState(input, access);
                    selectedSeq = seq;
                } else if (seq == selectedSeq
                        && (selected == null
                        || !portId.equals(text(
                        selected.port.get("portId"))))) {
                    return null;
                }
            }
        }
        return selected;
    }

    /** Applies the exact discovery access to the already-created action. */
    private static boolean refineExactContainerPreStateAction(
            Map<String, Object> goal, ExactContainerPreState selected,
            String javaType) {
        String portId = text(selected.port.get("portId"));
        Map<String, Object> action = null;
        for (Map<String, Object> candidate : rows(goal.get("symbolize"))) {
            if (!portId.equals(text(candidate.get("symbol")))) continue;
            if (action != null) return false;
            action = candidate;
        }
        if (action == null) return false;
        String site = text(selected.access.get("staticAccessSiteId"));
        if (!STATIC_SITE.matcher(site).matches()) return false;
        action.put("javaType", javaType);
        action.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        action.put("dependencyRole", "VALUE_FRONTIER");
        action.put("containerCapacity", LoopBoundPolicy
                .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY);
        action.put("boundedContainerStateRole", "MUTATION_PRE_STATE");
        action.put("boundedContainerStateAuthority",
                "EXACT_RUNTIME_CONTAINER_MUTATION_STATE_CHAIN_V1");
        action.put("accessSites", Collections.singletonList(site));
        action.put("siteId", site);
        action.put("selectedRuntimeEventSeq",
                selected.access.get("eventSeq"));
        action.put("selectedRuntimeCallId", selected.access.get("callId"));
        action.put("preStateSelectionAuthority",
                "EARLIEST_READ_IN_EXACT_DEFINITION_INVOCATION_V1");
        return true;
    }

    private static Map<String, Object> matchingFieldInputBeforeOutput(
            List<Map<String, Object>> inputs, long rootCallId,
            Map<String, Object> output, List<String> path,
            List<String> declarations) {
        long owner = longNumber(output.get("fieldReceiverObjectId"),
                longNumber(output.get("rootObjectId"), 0L));
        long writeSeq = longNumber(output.get("eventSeq"), Long.MAX_VALUE);
        Map<String, Object> match = null;
        for (Map<String, Object> input : inputs) {
            long inputOwner = longNumber(input.get("fieldReceiverObjectId"),
                    longNumber(input.get("rootObjectId"), 0L));
            long readSeq = longNumber(input.get("eventSeq"), -1L);
            if (longNumber(input.get("rootCallId"), -1L) != rootCallId
                    || owner == 0L || owner != inputOwner
                    || readSeq > writeSeq
                    || !path.equals(strings(input.get("fieldPath")))
                    || !declarations.equals(strings(
                    input.get("fieldPathDeclarations")))) {
                continue;
            }
            if (match == null || readSeq > longNumber(
                    match.get("eventSeq"), -1L)) {
                match = input;
            } else if (readSeq == longNumber(match.get("eventSeq"), -1L)
                    && !text(match.get("portId")).equals(
                    text(input.get("portId")))) {
                return null;
            }
        }
        return match;
    }

    /**
     * Frontier of a value the caller only rebuilt from a decoded reply.  The
     * declared response port is the whole relation; the serialization code
     * that materialized the carrier stays outside the replay envelope.
     */
    private static ReturnSlice carrierSlice(String carrierPort,
                                            String definitionMethod,
                                            Set<String> allowed,
                                            String rootMethod) {
        ReturnSlice result = new ReturnSlice();
        result.inputPorts.add(carrierPort);
        addIfAllowed(result.methods, allowed, definitionMethod);
        addIfAllowed(result.methods, allowed, rootMethod);
        return result;
    }

    /**
     * Adds the response port every selected carrier leaf penetrates to, so a
     * value read back out of a rebuilt carrier keeps demanding the server
     * region that produced it.
     */
    private static void addProtocolCarrierPorts(
            List<String> inputPorts, List<Map<String, Object>> regionInputs,
            long rootCallId) {
        if (inputPorts.isEmpty()) return;
        Set<String> selected = new LinkedHashSet<>(inputPorts);
        for (Map<String, Object> input : regionInputs) {
            String carrier =
                    ProtocolCarrierReconstruction.responsePort(input);
            if (carrier.isEmpty()
                    || longNumber(input.get("rootCallId"), -1L) != rootCallId
                    || !selected.contains(text(input.get("portId")))
                    || !selected.add(carrier)) {
                continue;
            }
            inputPorts.add(carrier);
        }
    }

    private static void addIfAllowed(List<String> methods,
                                     Set<String> allowed, String method) {
        if (!method.isEmpty() && allowed.contains(method)
                && !constructor(method) && !methods.contains(method)) {
            methods.add(method);
        }
    }

    private static void addIfAllowed(Set<String> methods,
                                     Set<String> allowed, String method) {
        if (!method.isEmpty() && allowed.contains(method)
                && !constructor(method)) {
            methods.add(method);
        }
    }

    private static String fieldOwner(String declaration) {
        int colon = declaration.indexOf(':');
        return declaration.startsWith("<") && colon > 1
                ? declaration.substring(1, colon).trim() : "";
    }

    private static String methodReturnType(String method) {
        int colon = method.indexOf(':');
        int open = method.indexOf('(', colon + 1);
        if (!method.startsWith("<") || colon < 1 || open < 0) return "";
        String prefix = method.substring(colon + 1, open).trim();
        int separator = prefix.lastIndexOf(' ');
        return separator > 0 ? prefix.substring(0, separator).trim() : "";
    }

    private static String methodParameterType(String method, int index) {
        int colon = method.indexOf(':');
        int open = method.indexOf('(', colon + 1);
        int close = method.lastIndexOf(')');
        if (!method.startsWith("<") || colon < 1 || open < 0
                || close < open || index < 0) return "";
        String parameters = method.substring(open + 1, close).trim();
        if (parameters.isEmpty()) return "";
        String[] types = parameters.split(",", -1);
        return index < types.length ? types[index].trim() : "";
    }

    private static JsonArray stringsJson(Collection<String> values) {
        JsonArray result = new JsonArray();
        Set<String> seen = new LinkedHashSet<>();
        for (String value : values) {
            if (!safe(value).isEmpty() && seen.add(value)) result.add(value);
        }
        return result;
    }

    private static List<Map<String, Object>> filterByText(
            List<Map<String, Object>> rows, String field,
            Set<String> accepted) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> row : rows) {
            if (accepted.contains(text(row.get(field)))) result.add(row);
        }
        return result;
    }

    private static String instanceKey(String region, long rootCallId) {
        return region + "\n" + rootCallId;
    }

    private static String logicalRegionId(String regionId, long ownerId) {
        return ownerId > 0L ? regionId + "@owner" + ownerId : regionId;
    }

    private static void copyBindingContext(Map<String, Object> binding,
                                           Map<String, Object> edge,
                                           Map<String, Object> fromPlan,
                                           Map<String, Object> toPlan) {
        copyContextLong(binding, "fromOwnerId", edge, fromPlan, "ownerId");
        copyContextLong(binding, "fromLaneId", edge, fromPlan, "laneId");
        copyContextLong(binding, "fromSpanId", edge, fromPlan, "spanId");
        copyContextLong(binding, "toOwnerId", edge, toPlan, "ownerId");
        copyContextLong(binding, "toLaneId", edge, toPlan, "laneId");
        copyContextLong(binding, "toSpanId", edge, toPlan, "spanId");
        copyContextLong(binding, "receiveRemoteParentSpanId", edge, null,
                "");
        long writerLane = longNumber(binding.get("fromLaneId"), -1L);
        long readerLane = longNumber(binding.get("toLaneId"), -1L);
        if (writerLane > 0L) binding.put("writerLaneId", writerLane);
        if (readerLane > 0L) binding.put("readerLaneId", readerLane);
        binding.put("programOrderRequired",
                writerLane > 0L && writerLane == readerLane);
    }

    private static void copyContextLong(Map<String, Object> target,
                                        String targetKey,
                                        Map<String, Object> edge,
                                        Map<String, Object> fallback,
                                        String fallbackKey) {
        long value = longNumber(edge.get(targetKey), -1L);
        if (value <= 0L && fallback != null && !fallbackKey.isEmpty()) {
            value = longNumber(fallback.get(fallbackKey), -1L);
        }
        if (value > 0L) target.put(targetKey, value);
    }

    private static void putTraceContext(Map<String, Object> target,
                                        MethodEvent event) {
        if (event.ownerId > 0L) target.put("ownerId", event.ownerId);
        if (event.laneId > 0L) target.put("laneId", event.laneId);
        if (event.spanId > 0L) target.put("spanId", event.spanId);
        if (event.parentSpanId > 0L) {
            target.put("parentSpanId", event.parentSpanId);
        }
        if (event.remoteParentSpanId > 0L) {
            target.put("remoteParentSpanId", event.remoteParentSpanId);
        }
    }

    private static List<Map<String, Object>> symbolize(
            List<Map<String, Object>> ports, long rootCallId) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> port : ports) {
            long boundRootCallId = "PROTOCOL_INPUT".equals(
                    text(port.get("sourceKind")))
                    ? longNumber(port.get("toRootCallId"), -1L)
                    : longNumber(port.get("rootCallId"), -1L);
            if (boundRootCallId != rootCallId) {
                continue;
            }
            List<String> path = strings(port.get("fieldPath"));
            Map<String, Object> action = new LinkedHashMap<>(port);
            MaterializationSpec materialization = MaterializationSpec.decode(
                    toJsonTreeFast(port).getAsJsonObject());
            action.put("symbol", port.get("portId"));
            action.put("observed", true);
            action.put("objectId", port.get("rootObjectId"));
            String javaType = leafType(
                    strings(port.get("fieldPathDeclarations")));
            // A projected container carries the exact static transport type.
            // Prefer it over a lossy boundary declaration (for example an
            // Object-typed helper parameter), while all ordinary inputs keep
            // the declaration-derived type used before this projection.
            if ("BOUNDED_CONTAINER_STATE".equals(
                    text(port.get("symbolicDemand")))
                    && !text(port.get("javaType")).isEmpty()) {
                javaType = text(port.get("javaType"));
            }
            action.put("javaType", javaType);
            if ("PROTOCOL_INPUT".equals(text(port.get("sourceKind")))) {
                if (port.containsKey("argumentIndex")) {
                    action.put("argumentIndex", port.get("argumentIndex"));
                }
                action.put("location", "REQUEST".equals(
                        text(port.get("protocolDirection")))
                        ? "PROTOCOL_ARGUMENT" : "PROTOCOL_RETURN");
            } else if ("PARAMETER".equals(text(port.get("rootKind")))) {
                action.put("argumentIndex", port.get("rootParameterIndex"));
                action.put("location", path.isEmpty()
                        ? "ARGUMENT" : "ARGUMENT_FIELD_PATH");
            } else if ("OBSERVED_FIELD_RECEIVER".equals(
                    text(port.get("rootKind")))) {
                action.put("location", "HEAP_OBJECT_FIELD");
                addFieldAccessIdentity(action, port, path);
            } else {
                action.put("location", "RECEIVER_FIELD");
            }
            if (!path.isEmpty()) {
                action.put("fieldPaths",
                        Collections.singletonList(path));
            }
            action.putAll(materialization.actionFields());
            result.add(action);
        }
        return result;
    }

    private static void addMaterializationMethods(
            Set<String> methods, List<Map<String, Object>> actions,
            Set<String> allowedMethods) {
        for (Map<String, Object> action : actions) {
            addIfAllowed(methods, allowedMethods,
                    text(action.get("rootMethod")));
            addIfAllowed(methods, allowedMethods,
                    text(action.get("accessorCallerMethod")));
            addIfAllowed(methods, allowedMethods,
                    text(action.get("accessorImplementationMethod")));
        }
    }

    private static void addFieldAccessIdentity(
            Map<String, Object> action, Map<String, Object> port,
            List<String> path) {
        List<String> declarations = strings(
                port.get("fieldPathDeclarations"));
        if (!declarations.isEmpty()) {
            action.put("accessFieldSignature", declarations.get(0));
            action.put("leafFieldSignature",
                    declarations.get(declarations.size() - 1));
        }
        String site = text(port.get("siteId"));
        if (!site.isEmpty()) {
            action.put("accessSites", Collections.singletonList(site));
        }
        action.put("fieldPath", path);
    }

    private static void registerExactPorts(
            Map<String, Object> region, String regionId, long rootCallId,
            Map<String, String> exactPorts) {
        registerExactPorts(rows(region.get("symbolicInputs")), regionId,
                rootCallId, "IN", exactPorts);
        registerExactPorts(rows(region.get("outputs")), regionId,
                rootCallId, "OUT", exactPorts);
    }

    private static void registerExactPorts(
            List<Map<String, Object>> ports, String regionId,
            long rootCallId, String direction,
            Map<String, String> exactPorts) {
        for (Map<String, Object> port : ports) {
            long boundRoot = "PROTOCOL_INPUT".equals(
                    text(port.get("sourceKind")))
                    ? longNumber(port.get("IN".equals(direction)
                    ? "toRootCallId" : "fromRootCallId"), -1L)
                    : longNumber(port.get("rootCallId"), -1L);
            if (boundRoot != rootCallId) continue;
            String id = text(port.get("portId"));
            if (id.isEmpty()) continue;
            String key = exactPortKey(regionId, rootCallId, direction, id);
            String previous = exactPorts.putIfAbsent(key, id);
            if (previous != null && !previous.equals(id)) {
                throw new IllegalArgumentException(
                        "conflicting exact runtime port binding: " + key);
            }
        }
    }

    private static String exactPort(
            Map<String, String> exactPorts, String regionId, long rootCallId,
            String direction, String portId, Map<String, Object> edge) {
        String selected = exactPorts.get(exactPortKey(regionId, rootCallId,
                direction, portId));
        if (selected == null) {
            throw new IllegalArgumentException("runtime flow "
                    + text(edge.get("edgeId")) + " has no exact "
                    + direction.toLowerCase() + " port for " + regionId
                    + "#call" + rootCallId + ": " + portId);
        }
        return selected;
    }

    private static String exactPortKey(String regionId, long rootCallId,
                                       String direction, String portId) {
        return regionId + "\n" + rootCallId + "\n" + direction + "\n"
                + portId;
    }

    private static List<Map<String, Object>> branches(
            List<Map<String, Object>> policies,
            List<RuntimeEvent> events) {
        Map<String, List<RuntimeEvent>> bySite = new LinkedHashMap<>();
        for (RuntimeEvent event : events) {
            if ("BRANCH".equals(event.kind)) {
                bySite.computeIfAbsent(event.siteId,
                        ignored -> new ArrayList<>()).add(event);
            }
        }
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> policy : policies) {
            String site = text(policy.get("siteId"));
            List<RuntimeEvent> occurrences = bySite.getOrDefault(site,
                    Collections.emptyList());
            List<Map<String, Object>> encoded = new ArrayList<>();
            for (int index = 0; index < occurrences.size(); index++) {
                encoded.add(object("occurrence", index + 1, "outcome",
                        occurrences.get(index).outcome));
            }
            RuntimeEvent selected = occurrences.isEmpty() ? null
                    : occurrences.get(occurrences.size() - 1);
            Map<String, Object> branch = new LinkedHashMap<>(policy);
            branch.put("observed", selected != null);
            branch.put("observedOutcome",
                    selected == null ? null : selected.outcome);
            branch.put("selectedOccurrence", occurrences.size());
            branch.put("occurrences", encoded);
            result.add(branch);
        }
        return result;
    }

    private static Map<String, Object> rootSelector(MethodEvent root) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("method", root.method);
        if (root.receiverType.isEmpty()) {
            result.put("kind", "GLOBAL_INVOCATION");
        } else {
            result.put("kind", "RECEIVER_CONTEXT");
            result.put("receiverClass", root.receiverType);
        }
        return result;
    }

    static final class RefinedFlowIndex {
        private final Map<String, List<FlowEdge>> incoming =
                new LinkedHashMap<>();
        /** region\nmethod\nsite -> cells guarded by that exact branch. */
        private final Map<String, Set<String>> guardedCellsBySite =
                new LinkedHashMap<>();
        /** declaration\nmethod\nsite -> regions with that HEAP_WRITE. */
        private final Map<String, Set<String>> heapWriteRegionsBySite =
                new LinkedHashMap<>();

        private void addEdge(FlowEdge edge) {
            incoming.computeIfAbsent(edge.toCell,
                    ignored -> new ArrayList<>()).add(edge);
            if ("GUARD".equals(edge.transferKind)
                    && !edge.method.isEmpty() && !edge.siteId.isEmpty()) {
                for (String region : edge.regions) {
                    guardedCellsBySite.computeIfAbsent(region + "\n"
                            + edge.method + "\n" + edge.siteId,
                            ignored -> new LinkedHashSet<>())
                            .add(edge.toCell);
                }
            }
            if ("HEAP_WRITE".equals(edge.transferKind)
                    && !edge.method.isEmpty() && !edge.siteId.isEmpty()) {
                for (String region : edge.regions) {
                    heapWriteRegionsBySite.computeIfAbsent(edge.toCell
                            + "\n" + edge.method + "\n" + edge.siteId,
                            ignored -> new LinkedHashSet<>()).add(region);
                }
            }
        }

        private static RefinedFlowIndex build(
                List<Map<String, Object>> rows, File graph) {
            RefinedFlowIndex result = new RefinedFlowIndex();
            int count = 0;
            for (Map<String, Object> row : rows == null
                    ? Collections.<Map<String, Object>>emptyList() : rows) {
                count++;
                if (row == null
                        || integer(row.get("schemaVersion"), -1) != 3
                        || integer(row.get("refinementSchemaVersion"), -1)
                        != 1
                        || !"RUNTIME_REFINED_DATAFLOW".equals(
                        text(row.get("graphKind")))) {
                    throw new IllegalArgumentException(
                            "concolic planning requires the "
                                    + "runtime-refined graph: " + graph);
                }
                FlowEdge edge = FlowEdge.decode(row);
                if (edge != null) {
                    result.addEdge(edge);
                }
            }
            if (count == 0) {
                throw new IllegalArgumentException(
                        "refined graph is empty: " + graph);
            }
            return result;
        }

        private static RefinedFlowIndex read(File graph) {
            if (graph == null || !graph.isFile()) {
                throw new IllegalArgumentException(
                        "artifact is missing: " + graph);
            }
            RefinedFlowIndex result = new RefinedFlowIndex();
            int rows = 0;
            try (BufferedReader input = reader(graph)) {
                String line;
                while ((line = input.readLine()) != null) {
                    if (line.trim().isEmpty()) continue;
                    Map<String, Object> row = GSON.fromJson(line, ROW);
                    rows++;
                    if (row == null
                            || integer(row.get("schemaVersion"), -1) != 3
                            || integer(row.get("refinementSchemaVersion"), -1)
                            != 1
                            || !"RUNTIME_REFINED_DATAFLOW".equals(
                            text(row.get("graphKind")))) {
                        throw new IllegalArgumentException(
                                "concolic planning requires the "
                                        + "runtime-refined graph: " + graph);
                    }
                    FlowEdge edge = FlowEdge.decode(row);
                    if (edge != null) {
                        result.addEdge(edge);
                    }
                }
            } catch (IOException exception) {
                throw new IllegalArgumentException(
                        "cannot read runtime-refined graph: " + graph,
                        exception);
            }
            if (rows == 0) {
                throw new IllegalArgumentException(
                        "refined graph is empty: " + graph);
            }
            return result;
        }

        /**
         * Builds one failure-sliced relation frontier.  Runtime fixes the
         * activation and the concrete heap access sites; static value/control
         * flow may then prove an alternate callee relevant even when the
         * baseline did not execute it.  Methods not reached by this backward
         * slice remain outside the transition fragment.  A heap read is a
         * live-in only when no exact earlier write to the same receiver/field
         * exists in the activation.
         */
        private ReturnSlice dependencySlice(
                String regionId, long rootCallId, String outputCell,
                Map<String, Object> exactHeapOutput,
                Set<String> allowedMethods,
                List<Map<String, Object>> inputs,
                List<Map<String, Object>> outputs,
                List<Map<String, Object>> branchPolicies,
                Set<String> seedMethods) {
            return dependencySlice(regionId, rootCallId, outputCell,
                    exactHeapOutput, allowedMethods, inputs, outputs,
                    branchPolicies, seedMethods, false);
        }

        private ReturnSlice dependencySlice(
                String regionId, long rootCallId, String outputCell,
                Map<String, Object> exactHeapOutput,
                Set<String> allowedMethods,
                List<Map<String, Object>> inputs,
                List<Map<String, Object>> outputs,
                List<Map<String, Object>> branchPolicies,
                Set<String> seedMethods, boolean requireGuardProof) {
            long boundaryUpperSeq = outputBoundarySeq(exactHeapOutput);
            ReturnSlice result = backwardSlice(regionId, rootCallId,
                    outputCell, exactHeapOutput, allowedMethods, inputs,
                    outputs, boundaryUpperSeq);
            for (String method : seedMethods) {
                if (!method.isEmpty() && allowedMethods.contains(method)) {
                    result.methods.add(method);
                }
            }

            boolean changed;
            do {
                changed = false;
                Set<String> selectedMethods = new LinkedHashSet<>(
                        result.methods);
                for (Map<String, Object> branch : branchPolicies) {
                    String method = text(branch.get("method"));
                    String site = text(branch.get("siteId"));
                    List<String> operands = strings(
                            branch.get("operandCells"));
                    boolean legacySiteOnly = !requireGuardProof
                            && operands.isEmpty()
                            && selectedMethods.contains(method);
                    if ((!selectedMethods.contains(method)
                            && !allowedMethods.contains(method))
                            || !"EXPLORE".equals(text(branch.get("policy")))
                            || Boolean.TRUE.equals(
                            branch.get("loopControlGuard"))
                            || site.isEmpty()
                            || !legacySiteOnly
                            && !controlsSelectedCell(regionId, method, site,
                            result.cells)
                            || !result.branchSites.add(site)) {
                        continue;
                    }
                    // A retained guard executes in its helper method even if
                    // all value-flow predecessors terminate at an input
                    // boundary.  Omitting the method leaves a branch site in
                    // the task that Soot is not allowed to instrument.
                    result.methods.add(method);
                    int before = result.cells.size();
                    for (String operand : operands) {
                        result.merge(backwardSlice(regionId, rootCallId,
                                operand, null, allowedMethods, inputs,
                                outputs, boundaryUpperSeq));
                    }
                    changed |= result.cells.size() != before;
                }
            } while (changed);
            return result;
        }

        /**
         * Uses the exact exception guard as a sink instead of inheriting the
         * whole execution-context region.  The target guard is retained even
         * when it is a path assumption; all other branches still require a
         * static GUARD edge into the selected value slice.
         */
        private ReturnSlice targetReachSlice(
                String regionId, long rootCallId,
                Set<String> allowedMethods,
                List<Map<String, Object>> inputs,
                List<Map<String, Object>> outputs,
                List<Map<String, Object>> branchPolicies,
                String rootMethod) {
            ReturnSlice result = new ReturnSlice();
            boolean targetFound = false;
            for (Map<String, Object> branch : branchPolicies) {
                if (!Boolean.TRUE.equals(branch.get("failureTarget"))) {
                    continue;
                }
                String site = text(branch.get("siteId"));
                String method = text(branch.get("method"));
                if (site.isEmpty() || method.isEmpty()
                        || !allowedMethods.contains(method)) {
                    continue;
                }
                targetFound = true;
                result.branchSites.add(site);
                result.methods.add(method);
                for (String operand : strings(branch.get("operandCells"))) {
                    result.merge(dependencySlice(regionId, rootCallId,
                            operand, null, allowedMethods, inputs, outputs,
                            branchPolicies, Collections.<String>emptySet(),
                            true));
                }
            }
            if (!targetFound) return null;
            addIfAllowed(result.methods, allowedMethods, rootMethod);
            return result;
        }

        private boolean controlsSelectedCell(String regionId, String method,
                                             String site,
                                             Set<String> selectedCells) {
            // Index form of: exists GUARD edge at (regionId, method, site)
            // whose guarded cell is currently selected.
            Set<String> guarded = guardedCellsBySite.get(regionId + "\n"
                    + method + "\n" + site);
            if (guarded == null) return false;
            if (guarded.size() <= selectedCells.size()) {
                for (String cell : guarded) {
                    if (selectedCells.contains(cell)) return true;
                }
                return false;
            }
            for (String cell : selectedCells) {
                if (guarded.contains(cell)) return true;
            }
            return false;
        }

        /**
         * Input boundary maps depend only on the (immutable) region input
         * list and the bound root call; they were previously rebuilt on
         * every backward slice, which dominated planning time.  The cache
         * preserves construction order exactly.
         */
        private final Map<List<Map<String, Object>>, Map<Long, Boundaries>>
                boundariesByInputs = new java.util.IdentityHashMap<>();

        private static final class Boundaries {
            private final Map<String, List<Map<String, Object>>> direct =
                    new LinkedHashMap<>();
            private final Map<String, List<Map<String, Object>>> heap =
                    new LinkedHashMap<>();
        }

        /** Synchronized: plans are finalized on a pool sharing this index. */
        private synchronized Boundaries boundaries(
                List<Map<String, Object>> inputs, long rootCallId) {
            Map<Long, Boundaries> byRoot = boundariesByInputs
                    .computeIfAbsent(inputs,
                            ignored -> new LinkedHashMap<>());
            Boundaries cached = byRoot.get(rootCallId);
            if (cached != null) return cached;
            Boundaries result = new Boundaries();
            for (Map<String, Object> input : inputs) {
                long boundRoot = "PROTOCOL_INPUT".equals(
                        text(input.get("sourceKind")))
                        ? longNumber(input.get("toRootCallId"), -1L)
                        : longNumber(input.get("rootCallId"), -1L);
                String port = text(input.get("portId"));
                if (boundRoot != rootCallId || port.isEmpty()) continue;
                registerBoundary(result.direct, text(input.get("cell")),
                        input);
                List<String> declarations = strings(
                        input.get("fieldPathDeclarations"));
                if (!declarations.isEmpty()) {
                    registerBoundary(result.heap,
                            text(input.get("siteId")) + "\n"
                                    + declarations.get(
                                    declarations.size() - 1), input);
                }
            }
            byRoot.put(rootCallId, result);
            return result;
        }

        private ReturnSlice backwardSlice(
                String regionId, long rootCallId, String sinkCell,
                Map<String, Object> exactHeapOutput,
                Set<String> allowedMethods,
                List<Map<String, Object>> inputs,
                List<Map<String, Object>> outputs,
                long boundaryUpperSeq) {
            ReturnSlice result = new ReturnSlice();
            if (sinkCell.isEmpty()) return result;
            result.cells.add(sinkCell);

            Boundaries bounds = boundaries(inputs, rootCallId);
            Map<String, List<Map<String, Object>>> directInputs =
                    bounds.direct;
            Map<String, List<Map<String, Object>>> heapInputs =
                    bounds.heap;

            String forcedMethod = exactHeapOutput == null ? ""
                    : text(exactHeapOutput.get("rootMethod"));
            String forcedSite = exactHeapOutput == null ? ""
                    : text(exactHeapOutput.get("siteId"));
            SliceNode sink = new SliceNode(sinkCell, forcedMethod,
                    forcedSite);
            Map<SliceNode, SliceStep> towardSink = new LinkedHashMap<>();
            Set<SliceNode> visited = new LinkedHashSet<>();
            Deque<SliceNode> queue = new ArrayDeque<>();
            visited.add(sink);
            queue.add(sink);
            while (!queue.isEmpty()) {
                SliceNode current = queue.removeFirst();
                Map<String, Object> direct = current.forcedWrite()
                        ? null : selectBoundary(
                        directInputs.get(current.cell), boundaryUpperSeq,
                        true);
                if (direct != null) {
                    result.inputPorts.add(text(direct.get("portId")));
                    addSlicePath(result, current, sink, towardSink, null);
                    continue;
                }

                for (FlowEdge edge : incoming.getOrDefault(current.cell,
                        Collections.<FlowEdge>emptyList())) {
                    if (!edge.regions.contains(regionId)
                            || edge.method.isEmpty()
                            || !allowedMethods.contains(edge.method)
                            || "PROTOCOL_TRANSFER".equals(
                            edge.transferKind)) {
                        continue;
                    }
                    if (current.forcedWrite()) {
                        if (!"HEAP_WRITE".equals(edge.transferKind)
                                || !current.writeMethod.equals(edge.method)
                                || !current.writeSite.equals(edge.siteId)) {
                            continue;
                        }
                        SliceNode predecessor = new SliceNode(
                                edge.fromCell, "", "");
                        enqueueSlice(predecessor, current, edge, visited,
                                queue, towardSink);
                        continue;
                    }
                    if ("HEAP_READ".equals(edge.transferKind)) {
                        String key = edge.siteId + "\n" + edge.fromCell;
                        Map<String, Object> input = selectBoundary(
                                heapInputs.get(key), boundaryUpperSeq,
                                false);
                        if (input == null) continue;
                        Map<String, Object> writer = precedingWrite(
                                regionId, rootCallId, input, edge.fromCell,
                                outputs, allowedMethods);
                        if (writer != null) {
                            SliceNode predecessor = new SliceNode(
                                    edge.fromCell,
                                    text(writer.get("rootMethod")),
                                    text(writer.get("siteId")));
                            enqueueSlice(predecessor, current, edge, visited,
                                    queue, towardSink);
                        } else {
                            result.inputPorts.add(text(input.get("portId")));
                            addSlicePath(result, current, sink, towardSink,
                                    edge);
                        }
                        continue;
                    }
                    if ("HEAP_WRITE".equals(edge.transferKind)
                            || !returnValueTransfer(edge.transferKind)) {
                        continue;
                    }
                    SliceNode predecessor = new SliceNode(edge.fromCell,
                            "", "");
                    enqueueSlice(predecessor, current, edge, visited, queue,
                            towardSink);
                }
            }
            return result;
        }

        private Map<String, Object> precedingWrite(
                String regionId, long rootCallId,
                Map<String, Object> read, String declaration,
                List<Map<String, Object>> outputs,
                Set<String> allowedMethods) {
            long receiver = longNumber(read.get("fieldReceiverObjectId"),
                    longNumber(read.get("rootObjectId"), 0L));
            long readSeq = longNumber(read.get("eventSeq"), -1L);
            if (receiver == 0L || readSeq < 0L) return null;
            Map<String, Object> selected = null;
            for (Map<String, Object> output : outputs) {
                List<String> declarations = strings(
                        output.get("fieldPathDeclarations"));
                long writerReceiver = longNumber(
                        output.get("fieldReceiverObjectId"),
                        longNumber(output.get("rootObjectId"), 0L));
                long writeSeq = longNumber(output.get("eventSeq"), -1L);
                String method = text(output.get("rootMethod"));
                String site = text(output.get("siteId"));
                if (longNumber(output.get("rootCallId"), -1L) != rootCallId
                        || declarations.isEmpty()
                        || !declaration.equals(declarations.get(
                        declarations.size() - 1))
                        || receiver != writerReceiver
                        || writeSeq < 0L || writeSeq >= readSeq
                        || method.isEmpty() || site.isEmpty()
                        || !allowedMethods.contains(method)
                        || !hasExactWrite(regionId, declaration, method,
                        site)) {
                    continue;
                }
                if (selected == null || writeSeq > longNumber(
                        selected.get("eventSeq"), -1L)) {
                    selected = output;
                } else if (writeSeq == longNumber(
                        selected.get("eventSeq"), -1L)
                        && (!method.equals(text(selected.get("rootMethod")))
                        || !site.equals(text(selected.get("siteId"))))) {
                    return null;
                }
            }
            return selected;
        }

        private boolean hasExactWrite(String regionId, String declaration,
                                      String method, String site) {
            Set<String> regions = heapWriteRegionsBySite.get(declaration
                    + "\n" + method + "\n" + site);
            return regions != null && regions.contains(regionId);
        }

        private static void enqueueSlice(
                SliceNode predecessor, SliceNode current, FlowEdge edge,
                Set<SliceNode> visited, Deque<SliceNode> queue,
                Map<SliceNode, SliceStep> towardSink) {
            if (!visited.add(predecessor)) return;
            towardSink.put(predecessor, new SliceStep(edge, current));
            queue.addLast(predecessor);
        }

        private static void addSlicePath(
                ReturnSlice result, SliceNode start, SliceNode sink,
                Map<SliceNode, SliceStep> towardSink, FlowEdge first) {
            if (first != null) result.add(first);
            SliceNode cursor = start;
            while (!cursor.equals(sink)) {
                SliceStep step = towardSink.get(cursor);
                if (step == null) return;
                result.add(step.edge);
                cursor = step.towardSink;
            }
        }

        private static void registerBoundary(
                Map<String, List<Map<String, Object>>> boundaries,
                String key, Map<String, Object> input) {
            if (key.isEmpty()) return;
            boundaries.computeIfAbsent(key,
                    ignored -> new ArrayList<>()).add(input);
        }

        /**
         * A repeated RPC receive into the same local is an activation-local
         * reaching definition, not ambiguous aliasing.  Select the latest
         * receive preceding the exact demanded producer write.  Other
         * repeated boundaries remain fail-closed.
         */
        private static Map<String, Object> selectBoundary(
                List<Map<String, Object>> candidates, long upperSeq,
                boolean allowProtocolOccurrence) {
            if (candidates == null || candidates.isEmpty()) return null;
            Map<String, Object> first = candidates.get(0);
            boolean onePort = true;
            boolean allProtocol = true;
            String port = text(first.get("portId"));
            for (Map<String, Object> candidate : candidates) {
                onePort &= port.equals(text(candidate.get("portId")));
                allProtocol &= "PROTOCOL_INPUT".equals(
                        text(candidate.get("sourceKind")));
            }
            if (onePort) return first;
            if (!allowProtocolOccurrence || !allProtocol || upperSeq < 0L) {
                return null;
            }

            List<Map<String, Object>> preceding = new ArrayList<>();
            for (Map<String, Object> candidate : candidates) {
                long receive = longNumber(candidate.get("receiveEventSeq"),
                        -1L);
                if (receive >= 0L && receive <= upperSeq) {
                    preceding.add(candidate);
                }
            }
            preceding.sort(Comparator.comparingLong(
                    (Map<String, Object> value) -> longNumber(
                            value.get("receiveEventSeq"), -1L)).reversed());
            if (preceding.size()
                    > LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS) {
                preceding = new ArrayList<>(preceding.subList(0,
                        LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS));
            }
            if (preceding.isEmpty()) return null;
            long latest = longNumber(preceding.get(0).get(
                    "receiveEventSeq"), -1L);
            Map<String, Object> selected = preceding.get(0);
            for (int index = 1; index < preceding.size(); index++) {
                Map<String, Object> candidate = preceding.get(index);
                if (longNumber(candidate.get("receiveEventSeq"), -1L)
                        != latest) break;
                if (!text(selected.get("portId")).equals(
                        text(candidate.get("portId")))) {
                    return null;
                }
            }
            return selected;
        }

        private static long outputBoundarySeq(
                Map<String, Object> exactOutput) {
            if (exactOutput == null || exactOutput.isEmpty()) return -1L;
            long event = longNumber(exactOutput.get("eventSeq"), -1L);
            long completion = longNumber(
                    exactOutput.get("mutationCompletionSeq"), -1L);
            return Math.max(event, completion);
        }

        private static boolean returnValueTransfer(String transferKind) {
            return "VALUE_PASS".equals(transferKind)
                    || "IDENTITY_BINDING".equals(transferKind)
                    || "FUNCTION_RETURN".equals(transferKind)
                    || "CONSTRUCT".equals(transferKind)
                    || "MODEL_TRANSFORM".equals(transferKind)
                    || "COMPUTE".equals(transferKind)
                    || "HEAP_LOOKUP".equals(transferKind)
                    || "DYNAMIC_DISPATCH".equals(transferKind);
        }

    }

    private static final class FlowEdge {
        private final String id;
        private final String fromCell;
        private final String toCell;
        private final String method;
        private final String siteId;
        private final String transferKind;
        private final Set<String> regions;

        private FlowEdge(String id, String fromCell, String toCell,
                         String method,
                         String siteId, String transferKind,
                         Set<String> regions) {
            this.id = id;
            this.fromCell = fromCell;
            this.toCell = toCell;
            this.method = method;
            this.siteId = siteId;
            this.transferKind = transferKind;
            this.regions = regions;
        }

        private static FlowEdge decode(Map<String, Object> row) {
            String from = text(row.get("fromCell"));
            String to = text(row.get("toCell"));
            String transfer = text(row.get("transferKind"));
            if (from.isEmpty() || to.isEmpty()) {
                return null;
            }
            return new FlowEdge(text(row.get("id")), from, to,
                    text(row.get("method")),
                    text(row.get("siteId")), transfer,
                    new LinkedHashSet<>(strings(row.get("regionIds"))));
        }
    }

    private static final class ReturnSlice {
        private final Set<String> inputPorts = new LinkedHashSet<>();
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<String> staticSites = new LinkedHashSet<>();
        private final Set<String> branchSites = new LinkedHashSet<>();
        private final Set<String> edges = new LinkedHashSet<>();
        private final Set<String> cells = new LinkedHashSet<>();

        private void add(FlowEdge edge) {
            String identity = edge.id.isEmpty()
                    ? edge.fromCell + "\n" + edge.toCell + "\n"
                    + edge.transferKind : edge.id;
            if (!edges.add(identity)) return;
            methods.add(edge.method);
            if (!edge.siteId.isEmpty()) staticSites.add(edge.siteId);
            cells.add(edge.fromCell);
            cells.add(edge.toCell);
        }

        private void merge(ReturnSlice other) {
            inputPorts.addAll(other.inputPorts);
            methods.addAll(other.methods);
            staticSites.addAll(other.staticSites);
            branchSites.addAll(other.branchSites);
            edges.addAll(other.edges);
            cells.addAll(other.cells);
        }
    }

    private static final class SliceNode {
        private final String cell;
        private final String writeMethod;
        private final String writeSite;

        private SliceNode(String cell, String writeMethod,
                          String writeSite) {
            this.cell = safe(cell);
            this.writeMethod = safe(writeMethod);
            this.writeSite = safe(writeSite);
        }

        private boolean forcedWrite() {
            return !writeMethod.isEmpty() && !writeSite.isEmpty();
        }

        @Override
        public boolean equals(Object value) {
            if (this == value) return true;
            if (!(value instanceof SliceNode)) return false;
            SliceNode other = (SliceNode) value;
            return cell.equals(other.cell)
                    && writeMethod.equals(other.writeMethod)
                    && writeSite.equals(other.writeSite);
        }

        @Override
        public int hashCode() {
            int result = cell.hashCode();
            result = 31 * result + writeMethod.hashCode();
            return 31 * result + writeSite.hashCode();
        }
    }

    private static final class SliceStep {
        private final FlowEdge edge;
        private final SliceNode towardSink;

        private SliceStep(FlowEdge edge, SliceNode towardSink) {
            this.edge = edge;
            this.towardSink = towardSink;
        }
    }

    private static void require(Map<String, Object> row, int schema,
                                String kind, File source) {
        if (integer(row.get("schemaVersion"), -1) != schema
                || !kind.equals(text(row.get("kind")))) {
            throw new IllegalArgumentException("invalid " + kind
                    + " row in " + source);
        }
    }

    private static List<Map<String, Object>> read(File file) {
        if (file == null || !file.isFile()) {
            throw new IllegalArgumentException("artifact is missing: " + file);
        }
        List<Map<String, Object>> result = new ArrayList<>();
        try (BufferedReader reader = reader(file)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (!line.trim().isEmpty()) {
                    Map<String, Object> row = GSON.fromJson(line, ROW);
                    if (row == null) {
                        throw new IllegalArgumentException(
                                "null artifact row: " + file);
                    }
                    result.add(row);
                }
            }
        } catch (IOException failure) {
            throw new IllegalArgumentException("cannot read " + file,
                    failure);
        }
        return result;
    }

    private static BufferedReader reader(File file) throws IOException {
        InputStream input = Files.newInputStream(file.toPath());
        if (file.getName().endsWith(".gz")) {
            input = new GZIPInputStream(input);
        }
        return new BufferedReader(new InputStreamReader(input,
                StandardCharsets.UTF_8));
    }

    private static String activationId(MethodEvent root) {
        return "ACT." + UUID.nameUUIDFromBytes((root.test + "\n"
                + root.process + "\n" + root.tid + "\n" + root.callId)
                .getBytes(StandardCharsets.UTF_8));
    }

    private static String leafType(List<String> declarations) {
        if (declarations.isEmpty()) {
            return "java.lang.Object";
        }
        Matcher matcher = FIELD.matcher(
                declarations.get(declarations.size() - 1));
        return matcher.matches() ? matcher.group(1) : "java.lang.Object";
    }

    private static Map<String, Object> object(Object... fields) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index + 1 < fields.length; index += 2) {
            result.put(String.valueOf(fields[index]), fields[index + 1]);
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> rows(Object value) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (item instanceof Map<?, ?>) {
                    result.add((Map<String, Object>) item);
                }
            }
        }
        return result;
    }

    private static List<String> strings(Object value) {
        List<String> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (!text(item).isEmpty()) {
                    result.add(text(item));
                }
            }
        }
        return result;
    }

    private static Set<Long> longNumbers(Object value) {
        Set<Long> result = new LinkedHashSet<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (item instanceof Number) {
                    result.add(((Number) item).longValue());
                }
            }
        }
        return result;
    }

    private static int integer(Object value, int fallback) {
        return value instanceof Number ? ((Number) value).intValue()
                : fallback;
    }

    private static long longNumber(Object value, long fallback) {
        return value instanceof Number ? ((Number) value).longValue()
                : fallback;
    }

    private static String text(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }

    private static <T> List<T> sorted(Collection<T> source,
                                      ToLongFunction<T> sequence) {
        List<T> result = new ArrayList<>(source == null
                ? Collections.emptyList() : source);
        result.sort(Comparator.comparingLong(sequence));
        return result;
    }

    static final class Result {
        final List<Map<String, Object>> regionPlans = new ArrayList<>();
        final List<Map<String, Object>> edgeValidations = new ArrayList<>();
        final List<Map<String, Object>> runtimeInstances = new ArrayList<>();
        final List<Map<String, Object>> runtimeGraphEdges = new ArrayList<>();
        int staticRegionCount;

        String regionPlansJsonl() {
            return jsonl(regionPlans);
        }

        String edgeValidationsJsonl() {
            return jsonl(edgeValidations);
        }

        String runtimeInstancesJsonl() {
            return jsonl(runtimeInstances);
        }

        String runtimeGraphEdgesJsonl() {
            return jsonl(runtimeGraphEdges);
        }

        private static String jsonl(List<Map<String, Object>> rows) {
            StringBuilder result = new StringBuilder();
            for (Map<String, Object> row : rows) {
                result.append(GSON.toJson(row)).append('\n');
            }
            return result.toString();
        }
    }

    static final class MethodEvent {
        final long seq;
        final String test;
        final String process;
        final String threadName;
        final long tid;
        final String method;
        final int objectId;
        final String receiverType;
        final long callId;
        final long parentCallId;
        final long parentSiteId;
        final long ownerId;
        final long laneId;
        final long spanId;
        final long parentSpanId;
        final long remoteParentSpanId;

        MethodEvent(long seq, String test, String process, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId) {
            this(seq, test, process, threadName, tid, method, objectId,
                    receiverType, callId, parentCallId, parentSiteId,
                    0L, 0L, 0L, 0L, 0L);
        }

        MethodEvent(long seq, String test, String process, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId,
                    long ownerId, long laneId, long spanId,
                    long parentSpanId, long remoteParentSpanId) {
            this.seq = seq;
            this.test = safe(test);
            this.process = safe(process);
            this.threadName = safe(threadName);
            this.tid = tid;
            this.method = safe(method);
            this.objectId = objectId;
            this.receiverType = safe(receiverType);
            this.callId = callId;
            this.parentCallId = parentCallId;
            this.parentSiteId = parentSiteId;
            this.ownerId = ownerId;
            this.laneId = laneId;
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
        }
    }

    static final class ProtocolEvent {
        final long seq;
        final String direction;
        final String transport;
        final String correlationId;
        final String process;
        final String threadName;
        final long tid;
        final String method;
        final long callId;
        final long invocationId;
        final String declaredCallee;
        final long ownerId;
        final long laneId;
        final long spanId;
        final long parentSpanId;
        final long remoteParentSpanId;

        ProtocolEvent(long seq, String direction, String transport,
                      String correlationId, String process,
                      String threadName, long tid, String method, long callId,
                      long invocationId, String declaredCallee) {
            this(seq, direction, transport, correlationId, process,
                    threadName, tid, method, callId, invocationId,
                    declaredCallee, 0L, 0L, 0L, 0L, 0L);
        }

        ProtocolEvent(long seq, String direction, String transport,
                      String correlationId, String process,
                      String threadName, long tid, String method, long callId,
                      long invocationId, String declaredCallee,
                      long ownerId, long laneId, long spanId,
                      long parentSpanId, long remoteParentSpanId) {
            this.seq = seq;
            this.direction = safe(direction);
            this.transport = safe(transport);
            this.correlationId = safe(correlationId);
            this.process = safe(process);
            this.threadName = safe(threadName);
            this.tid = tid;
            this.method = safe(method);
            this.callId = callId;
            this.invocationId = invocationId;
            this.declaredCallee = safe(declaredCallee);
            this.ownerId = ownerId;
            this.laneId = laneId;
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
        }
    }

    static final class RuntimeEvent {
        final long seq;
        final String kind;
        final String method;
        final long callId;
        final long invocationId;
        final long parentSiteId;
        final String siteId;
        final String declaredCallee;
        final int argumentIndex;
        final String runtimeType;
        final int objectId;
        final String primitiveValue;
        final Boolean outcome;
        final Integer successorIndex;
        final String branchKind;
        final String switchCaseKeys;

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     int argumentIndex, String runtimeType, int objectId,
                     String primitiveValue, boolean hasOutcome,
                     boolean outcome) {
            this(seq, kind, method, callId, invocationId, parentSiteId,
                    siteId, "", argumentIndex, runtimeType, objectId,
                    primitiveValue, hasOutcome ? outcome : null, null,
                    "", "");
        }

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     String declaredCallee, int argumentIndex,
                     String runtimeType, int objectId, String primitiveValue,
                     boolean hasOutcome, boolean outcome) {
            this(seq, kind, method, callId, invocationId, parentSiteId,
                    siteId, declaredCallee, argumentIndex, runtimeType,
                    objectId, primitiveValue, hasOutcome ? outcome : null,
                    null, "", "");
        }

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     String declaredCallee, int argumentIndex,
                     String runtimeType, int objectId, String primitiveValue,
                     Boolean outcome, Integer successorIndex, String branchKind,
                     String switchCaseKeys) {
            this.seq = seq;
            this.kind = safe(kind);
            this.method = safe(method);
            this.callId = callId;
            this.invocationId = invocationId;
            this.parentSiteId = parentSiteId;
            this.siteId = safe(siteId);
            this.declaredCallee = safe(declaredCallee);
            this.argumentIndex = argumentIndex;
            this.runtimeType = safe(runtimeType);
            this.objectId = objectId;
            this.primitiveValue = safe(primitiveValue);
            this.outcome = outcome;
            this.successorIndex = successorIndex;
            this.branchKind = safe(branchKind);
            this.switchCaseKeys = safe(switchCaseKeys);
        }
    }

    static final class FieldAccessEvent {
        final long seq;
        final String kind;
        final String method;
        final long callId;
        final int unitIndex;
        final String siteId;
        final String field;
        final int receiverObjectId;
        final int valueObjectId;
        final String primitiveValue;

        FieldAccessEvent(long seq, String kind, String method, long callId,
                         String field, int receiverObjectId,
                         int valueObjectId, String primitiveValue) {
            this(seq, kind, method, callId, -1, "", field,
                    receiverObjectId, valueObjectId, primitiveValue);
        }

        FieldAccessEvent(long seq, String kind, String method, long callId,
                         int unitIndex, String siteId, String field,
                         int receiverObjectId, int valueObjectId,
                         String primitiveValue) {
            this.seq = seq;
            this.kind = safe(kind);
            this.method = safe(method);
            this.callId = callId;
            this.unitIndex = unitIndex;
            this.siteId = unitIndex >= 0 && !this.method.isEmpty()
                    ? this.method + "#u" + unitIndex : safe(siteId);
            this.field = safe(field);
            this.receiverObjectId = receiverObjectId;
            this.valueObjectId = valueObjectId;
            this.primitiveValue = safe(primitiveValue);
        }
    }

    private static final class ExactContainerPreState {
        private final Map<String, Object> port;
        private final Map<String, Object> access;

        private ExactContainerPreState(Map<String, Object> port,
                                       Map<String, Object> access) {
            this.port = port;
            this.access = access;
        }
    }

    /** Runtime proof that one mutation anchor belongs to a complete normal
     * definition invocation.  Completion sequences are local evidence only;
     * replay uses the bounded occurrence within that invocation. */
    private static final class ExactMutationFold {
        private final long definitionCallId;
        private final long normalExitSeq;
        private final long firstMutationEnterSeq;
        private final int anchorOccurrence;
        private final List<Long> completions;

        private ExactMutationFold(long definitionCallId,
                                  long normalExitSeq,
                                  long firstMutationEnterSeq,
                                  int anchorOccurrence,
                                  List<Long> completions) {
            this.definitionCallId = definitionCallId;
            this.normalExitSeq = normalExitSeq;
            this.firstMutationEnterSeq = firstMutationEnterSeq;
            this.anchorOccurrence = anchorOccurrence;
            this.completions = Collections.unmodifiableList(
                    new ArrayList<>(completions));
        }
    }

    /** Open-addressed long->long map with an ambiguity sentinel. */
    private static final class LongLongMap {
        private static final long AMBIGUOUS = Long.MIN_VALUE;
        private long[] keys = new long[1 << 16];
        private long[] values = new long[1 << 16];
        private int size;

        /** Keys are event sequence numbers >= 0; values are call ids > 0. */
        private void register(long seq, long callId) {
            int mask = keys.length - 1;
            int index = mix(seq) & mask;
            while (true) {
                long existingValue = values[index];
                if (existingValue == 0L) {
                    keys[index] = seq;
                    values[index] = callId;
                    size++;
                    if (size * 4 > keys.length * 3) {
                        grow();
                    }
                    return;
                }
                if (keys[index] == seq) {
                    if (existingValue != callId) {
                        values[index] = AMBIGUOUS;
                    }
                    return;
                }
                index = (index + 1) & mask;
            }
        }

        /** Unique call id for seq, or -1 when absent or ambiguous. */
        private long uniqueValue(long seq) {
            int mask = keys.length - 1;
            int index = mix(seq) & mask;
            while (true) {
                long value = values[index];
                if (value == 0L) return -1L;
                if (keys[index] == seq) {
                    return value == AMBIGUOUS ? -1L : value;
                }
                index = (index + 1) & mask;
            }
        }

        private void grow() {
            long[] oldKeys = keys;
            long[] oldValues = values;
            keys = new long[oldKeys.length * 2];
            values = new long[oldValues.length * 2];
            int mask = keys.length - 1;
            for (int from = 0; from < oldKeys.length; from++) {
                long value = oldValues[from];
                if (value == 0L) continue;
                int index = mix(oldKeys[from]) & mask;
                while (values[index] != 0L) {
                    index = (index + 1) & mask;
                }
                keys[index] = oldKeys[from];
                values[index] = value;
            }
        }

        private static int mix(long key) {
            long h = key * 0x9E3779B97F4A7C15L;
            return (int) (h ^ (h >>> 32));
        }
    }

    private static final class TraceIndex {
        private final List<MethodEvent> methods;
        private final Map<Long, MethodEvent> methodByCall =
                new LinkedHashMap<>();
        private final Map<String, List<MethodEvent>> methodsByName =
                new LinkedHashMap<>();
        private final Map<Long, List<Long>> children = new LinkedHashMap<>();
        private final Map<Long, List<RuntimeEvent>> runtimeByCall =
                new LinkedHashMap<>();
        /**
         * seq -> unique owning callId, or the ambiguity sentinel when two
         * events registered different call ids for one sequence number.
         * Behaviorally identical to the previous Map&lt;Long, Set&lt;Long&gt;&gt;
         * whose readers only accepted singleton sets, at a fraction of the
         * footprint for multi-million-event traces.
         */
        private final LongLongMap eventCallIdBySeq = new LongLongMap();

        private TraceIndex(Collection<MethodEvent> methodEvents,
                           Collection<RuntimeEvent> runtimeEvents,
                           Collection<FieldAccessEvent> fieldEvents) {
            methods = sorted(methodEvents, value -> value.seq);
            for (MethodEvent event : methods) {
                methodByCall.put(event.callId, event);
                methodsByName.computeIfAbsent(event.method,
                        ignored -> new ArrayList<>()).add(event);
                children.computeIfAbsent(event.parentCallId,
                        ignored -> new ArrayList<>()).add(event.callId);
            }
            for (RuntimeEvent event : sorted(runtimeEvents,
                    value -> value.seq)) {
                runtimeByCall.computeIfAbsent(event.callId,
                        ignored -> new ArrayList<>()).add(event);
                registerEventCall(event.seq, event.callId);
            }
            for (FieldAccessEvent event : sorted(fieldEvents,
                    value -> value.seq)) {
                registerEventCall(event.seq, event.callId);
            }
        }

        private void registerEventCall(long seq, long callId) {
            if (seq < 0L || callId <= 0L) return;
            eventCallIdBySeq.register(seq, callId);
        }

        private List<MethodEvent> methods(String signature) {
            return methodsByName.getOrDefault(signature,
                    Collections.emptyList());
        }

        private Set<Long> subtree(long root) {
            Set<Long> result = new LinkedHashSet<>();
            Deque<Long> work = new ArrayDeque<>();
            work.add(root);
            while (!work.isEmpty()) {
                long call = work.removeFirst();
                if (result.add(call)) {
                    work.addAll(children.getOrDefault(call,
                            Collections.emptyList()));
                }
            }
            return result;
        }

        private Set<String> methodNames(Set<Long> calls) {
            Set<String> result = new LinkedHashSet<>();
            for (Long call : calls) {
                MethodEvent method = methodByCall.get(call);
                if (method != null) {
                    result.add(method.method);
                }
            }
            return result;
        }

        private List<RuntimeEvent> runtime(Set<Long> calls) {
            List<RuntimeEvent> result = new ArrayList<>();
            for (Long call : calls) {
                result.addAll(runtimeByCall.getOrDefault(call,
                        Collections.emptyList()));
            }
            result.sort(Comparator.comparingLong(value -> value.seq));
            return result;
        }

        private long nearestAncestor(long call, Set<Long> candidates) {
            MethodEvent current = methodByCall.get(call);
            while (current != null && current.parentCallId != 0L) {
                if (candidates.contains(current.parentCallId)) {
                    return current.parentCallId;
                }
                current = methodByCall.get(current.parentCallId);
            }
            return 0L;
        }

        private MethodEvent nearestAuthoritativeAncestor(
                MethodEvent start, Set<String> authoritativeMethods) {
            MethodEvent current = start;
            while (current != null && current.parentCallId != 0L) {
                current = methodByCall.get(current.parentCallId);
                if (current != null
                        && authoritativeMethods.contains(current.method)) {
                    return current;
                }
            }
            return null;
        }

        private Set<Long> path(long ancestor, long descendant) {
            Deque<Long> reversed = new ArrayDeque<>();
            MethodEvent current = methodByCall.get(descendant);
            while (current != null) {
                reversed.addFirst(current.callId);
                if (current.callId == ancestor) {
                    return new LinkedHashSet<>(reversed);
                }
                current = methodByCall.get(current.parentCallId);
            }
            throw new IllegalArgumentException("call " + descendant
                    + " is not below authoritative owner " + ancestor);
        }

        /**
         * Narrows a long-lived root to the invocation that produced one
         * exact runtime output.  The root-to-caller chain preserves the
         * execution context, while the caller subtree preserves helpers that
         * participate in the selected transition.  Earlier sibling
         * invocations under the same service loop are deliberately absent.
         * A missing or ambiguous event mapping returns {@code null}, leaving
         * legacy fixtures on the conservative static method universe.
         */
        private Set<Long> exactOutputInvocationCalls(
                long rootCallId, long outputEventSeq) {
            long caller = eventCallIdBySeq.uniqueValue(outputEventSeq);
            if (caller <= 0L || !methodByCall.containsKey(rootCallId)) {
                return null;
            }
            if (!methodByCall.containsKey(caller)) return null;
            Set<Long> corridor;
            try {
                corridor = path(rootCallId, caller);
            } catch (IllegalArgumentException ignored) {
                return null;
            }
            corridor.addAll(subtree(caller));
            return corridor;
        }

        /**
         * Finds every completed execution of the selected mutator on the
         * same concrete container in the exact definition invocation and
         * extends its relation boundary to that invocation's normal exit.
         * Missing enter/return pairs, a non-normal exit, or an anchor that is
         * not one of those completions fail closed.
         */
        private ExactMutationFold exactMutationFold(
                long anchorCompletionSeq, String definitionMethod,
                String siteId, String declaredCallee,
                int containerObjectId) {
            long definitionCallId = eventCallIdBySeq.uniqueValue(
                    anchorCompletionSeq);
            if (definitionCallId <= 0L
                    || definitionMethod.isEmpty() || siteId.isEmpty()
                    || declaredCallee.isEmpty()
                    || containerObjectId == 0) {
                return null;
            }
            MethodEvent definition = methodByCall.get(definitionCallId);
            if (definition == null || !definitionMethod.equals(
                    definition.method)) {
                return null;
            }

            List<RuntimeEvent> events = runtimeByCall.getOrDefault(
                    definitionCallId, Collections.emptyList());
            long normalExitSeq = -1L;
            Map<Long, RuntimeEvent> enters = new LinkedHashMap<>();
            Map<Long, RuntimeEvent> returns = new LinkedHashMap<>();
            for (RuntimeEvent event : events) {
                if ("METHOD_EXIT_NORMAL".equals(event.kind)) {
                    if (normalExitSeq >= 0L) return null;
                    normalExitSeq = event.seq;
                    continue;
                }
                if (!siteId.equals(event.siteId)
                        || !declaredCallee.equals(event.declaredCallee)
                        || event.invocationId <= 0L) {
                    continue;
                }
                if ("CALL_SITE_ENTER".equals(event.kind)
                        && event.objectId == containerObjectId) {
                    if (enters.put(event.invocationId, event) != null) {
                        return null;
                    }
                } else if ("CALL_SITE_RETURN".equals(event.kind)) {
                    if (returns.put(event.invocationId, event) != null) {
                        return null;
                    }
                }
            }
            if (normalExitSeq < anchorCompletionSeq) return null;

            List<Long> completions = new ArrayList<>();
            long firstMutationEnterSeq = Long.MAX_VALUE;
            for (Map.Entry<Long, RuntimeEvent> entry : enters.entrySet()) {
                RuntimeEvent completion = returns.get(entry.getKey());
                if (completion == null || completion.seq
                        < entry.getValue().seq
                        || completion.seq > normalExitSeq) {
                    return null;
                }
                firstMutationEnterSeq = Math.min(firstMutationEnterSeq,
                        entry.getValue().seq);
                completions.add(completion.seq);
            }
            completions.sort(Long::compareTo);
            int anchor = completions.indexOf(anchorCompletionSeq);
            if (anchor < 0 || completions.isEmpty()) return null;
            return new ExactMutationFold(definitionCallId, normalExitSeq,
                    firstMutationEnterSeq, anchor + 1, completions);
        }

    }
}
