package edu.uva.liftlab.graphchecker.runtime;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Instantiates static symbolic regions with invocation-specific unit-test
 * evidence and turns them into replayable concolic activation plans.
 *
 * <p>This class deliberately does not execute the concolic VM. It establishes
 * the concrete discovery/replay contract: which invocation is the region
 * root, which values become symbols, which observed branches are assumptions,
 * and which graph-selected branches may be negated by the engine.</p>
 */
final class RuntimeRegionPlanner {
    private static final int MAX_INSTANCES = 10000;
    private static final int MAX_CALLS_PER_INSTANCE = 10000;
    private static final int MAX_PATH_SIGNATURE_EVENTS = 512;
    private static final Pattern PARAMETER = Pattern.compile("\\.param(\\d+):");
    private static final Pattern LOCAL_CELL = Pattern.compile(
            "^(<.+>)::([^#]+)(?:#.*)?$");
    private static final Pattern FIELD_SIGNATURE = Pattern.compile(
            "<([^:]+):\\s+([^()<>]+)\\s+([^\\s()>]+)>");
    private static final Pattern FIELD_PROJECTION = Pattern.compile(
            "#field:([^#@]+)");
    private static final Pattern GETTER_IN_GUARD = Pattern.compile(
            "\\b((?:get|is)[A-Z][A-Za-z0-9_]*)\\s*\\(");
    private static final String VM_CURRENT_TIME_MILLIS_RETURN =
            "<java.lang.System: long currentTimeMillis()>.return";
    private static final String VM_INTRINSIC_DEFERRED_AUTHORITY =
            "EXACT_VM_INTRINSIC_PLACEHOLDER_SCHEDULER_VALIDATION_V1";
    private static final String CALL_RETURN_DEFERRED_AUTHORITY =
            "AUTHORITATIVE_SCHEDULER_DEFINITION_INDEX_REQUIRED_V1";
    private static final String UNRESOLVED_INPUT_PROVENANCE_AUTHORITY =
            "STATIC_EXACT_DEPENDENCY_METHOD_CONSUMER_SET_V1";
    static final String ROOT_ARGUMENT_SELECTOR_SCHEMA_V1 =
            "EXACT_RUNTIME_ROOT_ARGUMENT_TYPES_V1";
    static final String ROOT_ARGUMENT_SELECTOR_AUTHORITY_V1 =
            "RUNTIME_METHOD_ARGUMENT_EXACT_TYPES_"
                    + "PREDICATE_RELATIVE_ORDINAL_V1";
    static final String ROOT_ARGUMENT_SELECTOR_SCHEMA =
            "EXACT_RUNTIME_ROOT_ARGUMENT_TYPES_AND_RECEIVER_V2";
    static final String ROOT_ARGUMENT_SELECTOR_AUTHORITY =
            "RUNTIME_METHOD_ARGUMENT_EXACT_TYPES_DISTINCT_RECEIVER_"
                    + "AND_WITHIN_RECEIVER_ORDINAL_V2";
    static final String ROOT_ARGUMENT_PREDICATE_KIND =
            "EXACT_RUNTIME_TYPE";
    static final String ROOT_CONTEXT_SELECTION_AUTHORITY =
            "TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_THREAD_NAME_"
                    + "CONTEXT_ORDINAL_V1";

    private RuntimeRegionPlanner() {
    }

    static Result plan(File regionFile, List<MethodEvent> methods,
                       List<RuntimeEvent> runtimeEvents,
                       List<FieldAccessEvent> fieldEvents) {
        return plan(regionFile, null, methods, runtimeEvents, fieldEvents);
    }

    static Result plan(File regionFile, File regionEdgeFile,
                       List<MethodEvent> methods,
                       List<RuntimeEvent> runtimeEvents,
                       List<FieldAccessEvent> fieldEvents) {
        Result result = new Result();
        List<StaticRegion> regions = readRegions(regionFile, result.warnings);
        List<StaticRegionEdge> regionEdges = readRegionEdges(regionEdgeFile,
                result.warnings);
        List<MethodEvent> methodEvents = sortedMethods(methods);
        List<RuntimeEvent> executions = sortedRuntime(runtimeEvents);
        List<FieldAccessEvent> fields = sortedFields(fieldEvents);

        Map<Long, MethodEvent> calls = new LinkedHashMap<>();
        Map<String, List<MethodEvent>> methodsBySignature = new LinkedHashMap<>();
        for (MethodEvent event : methodEvents) {
            calls.put(event.callId, event);
            add(methodsBySignature, event.method, event);
        }

        int instanceIndex = 0;
        int activationIndex = 0;
        int partialCount = 0;
        int fullyObservedCount = 0;
        int replayableCount = 0;
        int truncatedCallTreeInstanceCount = 0;
        int truncatedPathSignatureInstanceCount = 0;
        long skippedContainedCallCount = 0L;
        long skippedPathSignatureEventCount = 0L;
        Map<String, List<InstanceEvidence>> evidenceByRegion = new LinkedHashMap<>();
        Map<String, Integer> validationCounts = new LinkedHashMap<>();

        outer:
        for (StaticRegion region : regions) {
            List<RootCandidate> roots = rootCandidates(region, regions,
                    methodsBySignature, calls);
            if (roots.isEmpty()) {
                result.unobservedRegionIds.add(region.regionId);
                continue;
            }
            for (RootCandidate candidate : roots) {
                if (instanceIndex >= MAX_INSTANCES) {
                    result.truncated = true;
                    break outer;
                }
                MethodEvent root = candidate.event;
                ContainedCallSelection callSelection = containedCalls(root,
                        methodEvents, calls);
                Set<Long> containedCalls = callSelection.calls;
                if (callSelection.truncated) {
                    result.truncated = true;
                    truncatedCallTreeInstanceCount++;
                    skippedContainedCallCount += callSelection.skipped;
                }
                Set<String> observedMethods = new LinkedHashSet<>();
                List<MethodEvent> containedMethodEvents = new ArrayList<>();
                for (MethodEvent event : methodEvents) {
                    if (containedCalls.contains(event.callId)) {
                        observedMethods.add(event.method);
                        containedMethodEvents.add(event);
                    }
                }
                boolean fullyObserved = !callSelection.truncated
                        && observedMethods.containsAll(region.methods);
                Set<String> runtimeAdmittedMethods = new LinkedHashSet<>(
                        observedMethods);
                runtimeAdmittedMethods.removeAll(region.methods);
                if (fullyObserved) {
                    fullyObservedCount++;
                } else {
                    partialCount++;
                }

                int ordinal = invocationOrdinal(root, methodEvents);
                int ordinalWithinContext = invocationOrdinalWithinContext(
                        root, methodEvents);
                Map<String, Object> rootArgumentSelector =
                        runtimeRootArgumentSelector(root, methodEvents,
                                executions);
                String instanceId = region.regionId + "@" + safeToken(root.test)
                        + "#call" + root.callId;

                List<RuntimeEvent> containedRuntime = containedRuntimeEvents(
                        containedCalls, executions);
                List<FieldAccessEvent> containedFields = containedFieldEvents(
                        containedCalls, fields);
                PathSignatureSelection pathSelection = pathSignature(
                        containedRuntime);
                List<String> pathSignature = pathSelection.signature;
                if (pathSelection.truncated) {
                    result.truncated = true;
                    truncatedPathSignatureInstanceCount++;
                    skippedPathSignatureEventCount += pathSelection.skipped;
                }
                boolean runtimePathEvidenceComplete = !callSelection.truncated
                        && !pathSelection.truncated;
                List<String> runtimeGaps = new ArrayList<>();
                if (callSelection.truncated) {
                    runtimeGaps.add("CONTAINED_CALL_TREE_LIMIT_EXCEEDED");
                }
                if (pathSelection.truncated) {
                    runtimeGaps.add("PATH_SIGNATURE_LIMIT_EXCEEDED");
                }
                List<String> actualCallees = actualCallees(containedMethodEvents,
                        containedRuntime);
                List<Map<String, Object>> inputObjects = inputObservations(
                        region, root, containedCalls, containedRuntime,
                        containedFields, containedMethodEvents);
                List<Map<String, Object>> symbolize = symbolizeActions(
                        region, root, inputObjects, containedRuntime,
                        containedFields);
                List<Map<String, Object>> outputs = outputActions(region);
                List<Map<String, Object>> branchPlan = branchActions(
                        region, containedRuntime);
                boolean anchorObserved = observedMethods.contains(region.anchorMethod)
                        || invokedAnchor(containedRuntime, region.anchorMethod);
                int observedInputCount = countObserved(inputObjects);
                int deferredInputCount = countDeferred(inputObjects);
                int observedBranchCount = countObservedBranches(branchPlan);
                boolean inputsResolved = observedInputCount + deferredInputCount
                        == inputObjects.size();
                boolean branchesResolved = observedBranchCount == branchPlan.size();
                boolean symbolizeActionsReady = symbolizeActionsReady(
                        symbolize);
                boolean boundaryReady = inputsResolved && branchesResolved
                        && region.inputSelectionComplete
                        && runtimePathEvidenceComplete
                        && symbolizeActionsReady;
                String validationStatus = !runtimePathEvidenceComplete
                        ? "TRUNCATED_RUNTIME_PATH" : anchorObserved
                        ? "VALIDATED_PATH" : "PARTIAL_PATH";
                boolean replayable = anchorObserved
                        && runtimePathEvidenceComplete;
                boolean symbolicReady = replayable && boundaryReady;
                if (replayable) {
                    replayableCount++;
                }
                increment(validationCounts, validationStatus);

                boolean finalRootIsStatic = root.method.equals(region.rootMethod);
                String rootSelection = finalRootIsStatic
                        ? "RUNTIME_CONFIRMED_STATIC_CANDIDATE"
                        : "RUNTIME_SELECTED_ENTRY";

                Map<String, Object> instance = object(
                        "regionInstanceId", instanceId,
                        "regionId", region.regionId,
                        "test", root.test,
                        "rootCallId", root.callId,
                        "staticRootMethod", region.rootMethod,
                        "finalRootMethod", root.method,
                        "observedRootMethod", root.method,
                        "rootAuthority", "RUNTIME_CALL_TREE",
                        "rootObserved", true,
                        "staticRootObserved", candidate.staticRootObserved,
                        "rootSelection", rootSelection,
                        "process", root.process,
                        "threadId", root.tid,
                        "threadName", root.threadName,
                        "threadRole", threadRole(root.threadName),
                        "receiverObjectId", root.objectId,
                        "receiverType", root.receiverType,
                        "invocationOrdinal", ordinal,
                        "pathSignature", pathSignature,
                        "pathSignatureEventCount", pathSelection.total,
                        "pathSignatureLimit", MAX_PATH_SIGNATURE_EVENTS,
                        "pathSignatureTruncated", pathSelection.truncated,
                        "containedCallCount", containedCalls.size(),
                        "containedCallLimit", MAX_CALLS_PER_INSTANCE,
                        "containedCallTreeTruncated", callSelection.truncated,
                        "runtimePathEvidenceComplete",
                        runtimePathEvidenceComplete,
                        "runtimeGaps", runtimeGaps,
                        "actualCallees", actualCallees,
                        "observedMethods", sorted(observedMethods),
                        "runtimeAdmittedMethods",
                        sorted(runtimeAdmittedMethods),
                        "runtimeMethodAdmissionAuthority",
                        "EXACT_SAME_THREAD_DESCENDANT_CALL_TREE_V1",
                        "missingMethods", difference(region.methods, observedMethods),
                        "inputObjects", inputObjects,
                        "anchorObserved", anchorObserved,
                        "observedInputCount", observedInputCount,
                        "deferredInputCount", deferredInputCount,
                        "staticInputSelectionComplete",
                        region.inputSelectionComplete,
                        "staticUnresolvedInputs", region.unresolvedInputs,
                        "observedBranchCount", observedBranchCount,
                        "symbolizeActionsReady", symbolizeActionsReady,
                        "boundaryReady", boundaryReady,
                        "validationStatus", validationStatus,
                        "symbolicReady", symbolicReady,
                        "fullyObserved", fullyObserved,
                        "replayable", replayable,
                        "observed", true,
                        "precision", fullyObserved
                                ? "RUNTIME_CALL_TREE" : "PARTIAL_RUNTIME_CALL_TREE");
                addRootContextSelector(instance, root,
                        ordinalWithinContext);
                if (!rootArgumentSelector.isEmpty()) {
                    instance.put("runtimeRootArgumentSelector",
                            rootArgumentSelector);
                }
                result.instances.add(instance);

                Map<String, Object> validation = object(
                        "regionInstanceId", instanceId,
                        "regionId", region.regionId,
                        "status", validationStatus,
                        "rootObserved", true,
                        "staticRootObserved", candidate.staticRootObserved,
                        "runtimeSelectedRoot", root.method,
                        "rootAuthority", "RUNTIME_CALL_TREE",
                        "rootSelection", rootSelection,
                        "anchorObserved", anchorObserved,
                        "sameThreadCallTree", true,
                        "process", root.process,
                        "threadId", root.tid,
                        "pathSignatureEventCount", pathSelection.total,
                        "pathSignatureTruncated", pathSelection.truncated,
                        "containedCallCount", containedCalls.size(),
                        "containedCallTreeTruncated", callSelection.truncated,
                        "runtimePathEvidenceComplete",
                        runtimePathEvidenceComplete,
                        "runtimeGaps", runtimeGaps,
                        "observedMethods", sorted(observedMethods),
                        "runtimeAdmittedMethods",
                        sorted(runtimeAdmittedMethods),
                        "runtimeMethodAdmissionAuthority",
                        "EXACT_SAME_THREAD_DESCENDANT_CALL_TREE_V1",
                        "staticAlternativeMethodsNotObserved",
                        difference(region.methods, observedMethods),
                        "inputPortCount", inputObjects.size(),
                        "observedInputCount", observedInputCount,
                        "deferredInputCount", deferredInputCount,
                        "staticInputSelectionComplete",
                        region.inputSelectionComplete,
                        "staticUnresolvedInputs", region.unresolvedInputs,
                        "branchPolicyCount", branchPlan.size(),
                        "observedBranchCount", observedBranchCount,
                        "symbolizeActionsReady", symbolizeActionsReady,
                        "symbolicReady", symbolicReady);
                result.regionValidations.add(validation);
                if (runtimePathEvidenceComplete) {
                    add(evidenceByRegion, region.regionId,
                            new InstanceEvidence(instanceId, region, root,
                                    containedCalls, containedMethodEvents,
                                    containedRuntime, containedFields,
                                    observedMethods, validationStatus,
                                    runtimePathEvidenceComplete));
                }

                Map<String, Object> activation = object(
                        "activationId", "ACT." + activationIndex++,
                        "regionInstanceId", instanceId,
                        "regionId", region.regionId,
                        "test", root.test,
                        "rootMethod", root.method,
                        "staticRootMethod", region.rootMethod,
                        "observedRootMethod", root.method,
                        "rootAuthority", "RUNTIME_CALL_TREE",
                        "rootSelection", rootSelection,
                        "receiverType", root.receiverType,
                        "invocationOrdinal", ordinal,
                        "rootCallId", root.callId,
                        "captureGoal", object(
                                "kind", "TARGET_BRANCH",
                                "scope", "ONE_DIRECTED_BRANCH"),
                        "anchorRequired", true,
                        "anchorObserved", anchorObserved,
                        "boundaryReady", boundaryReady,
                        "pathSignatureEventCount", pathSelection.total,
                        "pathSignatureLimit", MAX_PATH_SIGNATURE_EVENTS,
                        "pathSignatureTruncated", pathSelection.truncated,
                        "containedCallCount", containedCalls.size(),
                        "containedCallLimit", MAX_CALLS_PER_INSTANCE,
                        "containedCallTreeTruncated", callSelection.truncated,
                        "runtimePathEvidenceComplete",
                        runtimePathEvidenceComplete,
                        "runtimeGaps", runtimeGaps,
                        "symbolize", symbolize,
                        "branches", branchPlan,
                        "outputs", outputs,
                        "requiredModels", region.models,
                        "staticInputSelectionComplete",
                        region.inputSelectionComplete,
                        "staticUnresolvedInputs", region.unresolvedInputs,
                        "replayable", replayable,
                        "symbolicReady", symbolicReady,
                        "replayMode", replayable
                                ? "RUNTIME_SELECTED_ROOT_REPLAY"
                                : "NO_VALIDATED_RUNTIME_PATH",
                        "engine", "openjdk8-zero-concolic");
                addRootContextSelector(activation, root,
                        ordinalWithinContext);
                if (!rootArgumentSelector.isEmpty()) {
                    activation.put("runtimeRootArgumentSelector",
                            rootArgumentSelector);
                }
                result.activations.add(activation);
                instanceIndex++;
            }
        }

        List<UpstreamEdgeBinding> edgeBindings = new ArrayList<>();
        validateRegionEdges(regionEdges, evidenceByRegion, result,
                edgeBindings);
        int upstreamActivationCount = deriveUpstreamActivations(
                edgeBindings, result);
        int mapValueElementProjectionCount =
                refineMapValueElementProjectionActivations(result);

        result.summary.put("staticRegionCount", regions.size());
        result.summary.put("staticRegionEdgeCount", regionEdges.size());
        result.summary.put("runtimeRegionInstanceCount", result.instances.size());
        result.summary.put("activationCount", result.activations.size());
        result.summary.put("upstreamActivationCount", upstreamActivationCount);
        result.summary.put("mapValueElementProjectionCount",
                mapValueElementProjectionCount);
        result.summary.put("fullyObservedCount", fullyObservedCount);
        result.summary.put("partialCount", partialCount);
        result.summary.put("replayableCount", replayableCount);
        result.summary.put("truncatedCallTreeInstanceCount",
                truncatedCallTreeInstanceCount);
        result.summary.put("truncatedPathSignatureInstanceCount",
                truncatedPathSignatureInstanceCount);
        result.summary.put("skippedContainedCallCount",
                skippedContainedCallCount);
        result.summary.put("skippedPathSignatureEventCount",
                skippedPathSignatureEventCount);
        result.summary.put("regionValidationCounts", validationCounts);
        result.summary.put("runtimeRegionEdgeValidationCount",
                result.edgeValidations.size());
        result.summary.put("confirmedReadFromRegionEdgeCount",
                countStatus(result.edgeValidations, "CONFIRMED_READ_FROM"));
        result.summary.put("orderedProtocolEndpointRegionEdgeCount",
                countStatus(result.edgeValidations, "ORDERED_ENDPOINTS"));
        result.summary.put("confirmedRuntimeValueEqualityEdgeCount",
                countStatus(result.edgeValidations,
                        "CONFIRMED_RUNTIME_VALUE_EQUALITY"));
        result.summary.put("unprovenPortMappingEdgeCount",
                countStatus(result.edgeValidations,
                        "PORT_MAPPING_OBSERVED_VALUE_EQUALITY_UNPROVEN"));
        result.summary.put("endpointObservedRegionEdgeCount",
                countStatus(result.edgeValidations, "ENDPOINTS_OBSERVED"));
        result.summary.put("unconfirmedReadFromRegionEdgeCount",
                countStatus(result.edgeValidations, "UNCONFIRMED_READ_FROM"));
        result.summary.put("unobservedRegionEdgeCount",
                countStatus(result.edgeValidations, "UNOBSERVED"));
        result.summary.put("unobservedRegionIds", result.unobservedRegionIds);
        result.summary.put("warningCount", result.warnings.size());
        result.summary.put("warnings", result.warnings);
        result.summary.put("truncated", result.truncated);
        result.summary.put("precision", "STATIC_REGION_PLUS_RUNTIME_CALL_TREE");
        return result;
    }

    private static List<RootCandidate> rootCandidates(
            StaticRegion region,
            List<StaticRegion> regions,
            Map<String, List<MethodEvent>> methodsBySignature,
            Map<Long, MethodEvent> calls) {
        List<RootCandidate> roots = new ArrayList<>();
        Set<Long> selectedCalls = new LinkedHashSet<>();
        List<StaticRegion> anchorPeers = regionsSharingAnchor(region, regions);
        List<MethodEvent> anchors = values(
                methodsBySignature.get(region.anchorMethod));

        // Static analysis supplies a candidate method set, but an observed
        // anchor invocation supplies the authority for the final root. Walk
        // that invocation's concrete same-thread ancestry and retain the
        // highest observed entry that is actually part of this region. This
        // ignores unrelated invocations of the static candidate. When several
        // regions share the same suffix/anchor, an exact root in the concrete
        // ancestry owns the invocation. A below-root fallback is admitted only
        // when its observed lineage is unique to this region; otherwise the
        // shared suffix is ambiguous and must not manufacture one activation
        // per static region.
        for (MethodEvent anchor : anchors) {
            List<MethodEvent> lineage = concreteLineage(anchor, calls);
            Set<String> exactRootOwners = exactRootOwners(lineage, anchorPeers);
            if (!exactRootOwners.isEmpty()
                    && !exactRootOwners.contains(region.regionId)) {
                continue;
            }
            if (exactRootOwners.isEmpty() && anchorPeers.size() > 1
                    && !hasRegionExclusiveLineage(
                    lineage, region, anchorPeers)) {
                continue;
            }

            MethodEvent selected = anchor;
            boolean staticRootObserved = exactRootOwners.contains(
                    region.regionId);
            for (MethodEvent entry : lineage) {
                if (region.methods.contains(entry.method)) {
                    selected = entry;
                }
            }
            if (selectedCalls.add(selected.callId)) {
                roots.add(new RootCandidate(selected, staticRootObserved));
            }
        }

        if (!roots.isEmpty()) {
            return roots;
        }

        // Anchors observed elsewhere in the workload are not evidence that a
        // static root reached this anchor. Returning the static root here would
        // turn an unrelated shared-suffix invocation into a false region
        // activation (for example registration/addKeys as heartbeat/addKeys).
        if (!anchors.isEmpty()) {
            return roots;
        }

        // If the anchor signature is absent from the trace altogether, a
        // partial trace may still contain the candidate entry. Preserve that
        // evidence for diagnostics, without claiming a validated path.
        for (MethodEvent event : values(methodsBySignature.get(region.rootMethod))) {
            if (selectedCalls.add(event.callId)) {
                roots.add(new RootCandidate(event, true));
            }
        }
        return roots;
    }

    private static List<StaticRegion> regionsSharingAnchor(
            StaticRegion region, List<StaticRegion> regions) {
        List<StaticRegion> result = new ArrayList<>();
        for (StaticRegion candidate : values(regions)) {
            if (safe(region.anchorMethod).equals(safe(candidate.anchorMethod))) {
                result.add(candidate);
            }
        }
        return result;
    }

    private static List<MethodEvent> concreteLineage(
            MethodEvent anchor, Map<Long, MethodEvent> calls) {
        List<MethodEvent> result = new ArrayList<>();
        result.add(anchor);
        long cursor = anchor.parentCallId;
        Set<Long> seen = new LinkedHashSet<>();
        while (cursor > 0L && seen.add(cursor)) {
            MethodEvent parent = calls.get(cursor);
            if (parent == null || !sameContext(anchor, parent)) {
                break;
            }
            result.add(parent);
            cursor = parent.parentCallId;
        }
        return result;
    }

    private static Set<String> exactRootOwners(
            List<MethodEvent> lineage, List<StaticRegion> regions) {
        Set<String> result = new LinkedHashSet<>();
        for (MethodEvent event : lineage) {
            for (StaticRegion region : regions) {
                if (event.method.equals(region.rootMethod)) {
                    result.add(region.regionId);
                }
            }
        }
        return result;
    }

    private static boolean hasRegionExclusiveLineage(
            List<MethodEvent> lineage, StaticRegion region,
            List<StaticRegion> anchorPeers) {
        for (MethodEvent event : lineage) {
            if (!region.methods.contains(event.method)) {
                continue;
            }
            int owners = 0;
            for (StaticRegion peer : anchorPeers) {
                if (peer.methods.contains(event.method)) {
                    owners++;
                }
            }
            if (owners == 1) {
                return true;
            }
        }
        return false;
    }

    private static int invocationOrdinal(MethodEvent target,
                                         List<MethodEvent> methods) {
        int ordinal = 0;
        for (MethodEvent event : methods) {
            if (!target.test.equals(event.test)
                    || !target.method.equals(event.method)) {
                continue;
            }
            ordinal++;
            if (event.callId == target.callId) {
                return ordinal;
            }
        }
        return 1;
    }

    /**
     * Stable replay ordinal for one exact runtime root context.  Trace thread
     * ids are deliberately excluded because JVM-assigned ids change across
     * executions.  The receiver runtime class is mandatory for contexts
     * emitted by this planner; a non-empty thread name further separates
     * same-class worker roles such as producer and consumer executors.
     */
    private static int invocationOrdinalWithinContext(
            MethodEvent target, List<MethodEvent> methods) {
        int ordinal = 0;
        for (MethodEvent event : methods) {
            if (!target.test.equals(event.test)
                    || !target.method.equals(event.method)
                    || !target.receiverType.equals(event.receiverType)
                    || !target.threadName.equals(event.threadName)) {
                continue;
            }
            ordinal++;
            if (event.callId == target.callId) return ordinal;
        }
        return 1;
    }

    private static void addRootContextSelector(Map<String, Object> target,
                                               MethodEvent root,
                                               int ordinalWithinContext) {
        if (target == null || root == null || root.receiverType.isEmpty()) {
            return;
        }
        target.put("receiverRuntimeClass", root.receiverType);
        if (!root.threadName.isEmpty()) {
            target.put("threadName", root.threadName);
        }
        target.put("threadIdSelectionUsed", false);
        target.put("invocationOrdinalWithinContext",
                Math.max(1, ordinalWithinContext));
        target.put("rootContextSelectionAuthority",
                ROOT_CONTEXT_SELECTION_AUTHORITY);
    }

    /**
     * Builds a replay selector from the exact non-null reference arguments
     * observed at the selected root invocation.  Candidate occurrences are
     * first restricted to the same stable receiver-class/thread context as
     * the target, then selection identifies the distinct receiver and its
     * matching invocation ordinal.  Other worker contexts and same-typed
     * calls on unrelated instances therefore cannot shift the activation.
     */
    private static Map<String, Object> runtimeRootArgumentSelector(
            MethodEvent target, List<MethodEvent> methods,
            List<RuntimeEvent> runtimeEvents) {
        List<String> parameterTypes = methodParameterTypes(target.method);
        if (parameterTypes.isEmpty()) {
            return Collections.emptyMap();
        }

        Map<Integer, String> observed = rootArgumentRuntimeTypes(target,
                runtimeEvents);
        List<Map<String, Object>> predicates = new ArrayList<>();
        for (int index = 0; index < parameterTypes.size(); index++) {
            if (primitiveType(parameterTypes.get(index))) {
                continue;
            }
            String runtimeType = safe(observed.get(index));
            if (runtimeType.isEmpty()) {
                // Null reference arguments intentionally provide no exact
                // type predicate.  Primitive arguments are ignored above.
                continue;
            }
            predicates.add(object(
                    "kind", ROOT_ARGUMENT_PREDICATE_KIND,
                    "argumentIndex", index,
                    "runtimeType", runtimeType));
        }
        if (predicates.isEmpty()) {
            return Collections.emptyMap();
        }

        Map<Integer, Integer> receiverOrdinals = new LinkedHashMap<>();
        Map<Integer, Integer> matchesByReceiver = new LinkedHashMap<>();
        int receiverOrdinal = -1;
        int matchOrdinalWithinReceiver = -1;
        for (MethodEvent candidate : methods) {
            if (!target.test.equals(candidate.test)
                    || !target.method.equals(candidate.method)
                    || !sameStableRootContext(target, candidate)
                    || !matchesRootArgumentPredicates(candidate,
                    runtimeEvents, predicates)) {
                continue;
            }
            Integer candidateReceiverOrdinal = receiverOrdinals.get(
                    candidate.objectId);
            if (candidateReceiverOrdinal == null) {
                candidateReceiverOrdinal = receiverOrdinals.size() + 1;
                receiverOrdinals.put(candidate.objectId,
                        candidateReceiverOrdinal);
            }
            Integer previousWithin = matchesByReceiver.get(candidate.objectId);
            int candidateWithin = previousWithin == null
                    ? 1 : previousWithin + 1;
            matchesByReceiver.put(candidate.objectId, candidateWithin);
            if (candidate.callId == target.callId) {
                receiverOrdinal = candidateReceiverOrdinal;
                matchOrdinalWithinReceiver = candidateWithin;
                break;
            }
        }
        if (receiverOrdinal <= 0 || matchOrdinalWithinReceiver <= 0) {
            // The target itself must satisfy predicates derived from its own
            // METHOD_ARGUMENT rows.  Refuse to emit an inconsistent selector.
            return Collections.emptyMap();
        }
        return object(
                "schema", ROOT_ARGUMENT_SELECTOR_SCHEMA,
                "authority", ROOT_ARGUMENT_SELECTOR_AUTHORITY,
                "predicates", predicates,
                "receiverOrdinal", receiverOrdinal,
                "matchOrdinalWithinReceiver", matchOrdinalWithinReceiver);
    }

    private static boolean sameStableRootContext(MethodEvent target,
                                                 MethodEvent candidate) {
        if (target.receiverType.isEmpty()) {
            return true;
        }
        return target.receiverType.equals(candidate.receiverType)
                && target.threadName.equals(candidate.threadName);
    }

    private static boolean matchesRootArgumentPredicates(
            MethodEvent candidate, List<RuntimeEvent> runtimeEvents,
            List<Map<String, Object>> predicates) {
        Map<Integer, String> observed = rootArgumentRuntimeTypes(candidate,
                runtimeEvents);
        for (Map<String, Object> predicate : predicates) {
            Object rawIndex = predicate.get("argumentIndex");
            int index = rawIndex instanceof Number
                    ? ((Number) rawIndex).intValue() : -1;
            if (index < 0 || !string(predicate.get("runtimeType")).equals(
                    safe(observed.get(index)))) {
                return false;
            }
        }
        return true;
    }

    private static Map<Integer, String> rootArgumentRuntimeTypes(
            MethodEvent method, List<RuntimeEvent> runtimeEvents) {
        Map<Integer, String> result = new LinkedHashMap<>();
        Set<Integer> ambiguous = new LinkedHashSet<>();
        for (RuntimeEvent event : runtimeEvents) {
            if (!"METHOD_ARGUMENT".equals(event.kind)
                    || event.callId != method.callId
                    || !method.method.equals(event.method)
                    || event.argumentIndex < 0
                    || event.runtimeType.isEmpty()) {
                continue;
            }
            String previous = result.put(event.argumentIndex,
                    event.runtimeType);
            if (previous != null && !previous.equals(event.runtimeType)) {
                ambiguous.add(event.argumentIndex);
            }
        }
        for (Integer index : ambiguous) {
            result.remove(index);
        }
        return result;
    }

    private static List<String> methodParameterTypes(String signature) {
        if (signature == null) return Collections.emptyList();
        int open = signature.indexOf('(');
        int close = signature.lastIndexOf(')');
        if (open < 0 || close < open) return Collections.emptyList();
        String parameters = signature.substring(open + 1, close).trim();
        if (parameters.isEmpty()) return Collections.emptyList();
        List<String> result = new ArrayList<>();
        for (String parameter : parameters.split(",", -1)) {
            String type = parameter.trim();
            if (type.isEmpty()) return Collections.emptyList();
            result.add(type);
        }
        return result;
    }

    private static ContainedCallSelection containedCalls(
            MethodEvent root, List<MethodEvent> methods,
            Map<Long, MethodEvent> calls) {
        Set<Long> result = new LinkedHashSet<>();
        result.add(root.callId);
        long skipped = 0L;
        for (MethodEvent event : methods) {
            if (event.seq < root.seq || !sameContext(root, event)) {
                continue;
            }
            // Static region methods select the root and describe the initial
            // dependency closure.  Once that exact invocation is selected,
            // its observed same-thread descendants are authoritative runtime
            // members too.  Filtering them by region.methods used to discard
            // concrete interface targets and helper calls (for example an
            // expiry remover invoked by addKeys) even though their parent-call
            // chain was recorded exactly.  Parent ancestry, not a static
            // membership guess, is the bounded admission proof here.
            long cursor = event.callId;
            Set<Long> seen = new LinkedHashSet<>();
            while (cursor > 0L && seen.add(cursor)) {
                if (cursor == root.callId) {
                    if (result.contains(event.callId)) {
                        break;
                    }
                    if (result.size() >= MAX_CALLS_PER_INSTANCE) {
                        skipped++;
                    } else {
                        result.add(event.callId);
                    }
                    break;
                }
                MethodEvent parent = calls.get(cursor);
                if (parent == null || !sameContext(root, parent)) {
                    break;
                }
                cursor = parent.parentCallId;
            }
        }
        return new ContainedCallSelection(result, skipped > 0L, skipped);
    }

    private static boolean sameContext(MethodEvent left, MethodEvent right) {
        return left != null && right != null
                && left.tid == right.tid
                && safe(left.process).equals(safe(right.process))
                && safe(left.test).equals(safe(right.test));
    }

    private static List<RuntimeEvent> containedRuntimeEvents(
            Set<Long> calls, List<RuntimeEvent> events) {
        List<RuntimeEvent> result = new ArrayList<>();
        for (RuntimeEvent event : events) {
            if (calls.contains(event.callId)) {
                result.add(event);
            }
        }
        return result;
    }

    private static List<FieldAccessEvent> containedFieldEvents(
            Set<Long> calls, List<FieldAccessEvent> events) {
        List<FieldAccessEvent> result = new ArrayList<>();
        for (FieldAccessEvent event : events) {
            if (calls.contains(event.callId)) {
                result.add(event);
            }
        }
        return result;
    }

    private static PathSignatureSelection pathSignature(
            List<RuntimeEvent> events) {
        List<String> result = new ArrayList<>();
        int total = 0;
        for (RuntimeEvent event : events) {
            if ("BRANCH".equals(event.kind) && event.hasOutcome) {
                total++;
                if (result.size() < MAX_PATH_SIGNATURE_EVENTS) {
                    result.add(event.siteId + "=" + event.outcome);
                }
            }
        }
        long skipped = Math.max(0L, (long) total - result.size());
        return new PathSignatureSelection(result, total, skipped > 0L,
                skipped);
    }

    private static List<String> actualCallees(List<MethodEvent> methodEvents,
                                               List<RuntimeEvent> events) {
        Map<Long, RuntimeEvent> sites = new LinkedHashMap<>();
        for (RuntimeEvent event : events) {
            if ("CALL_SITE_ENTER".equals(event.kind)) {
                sites.put(event.invocationId, event);
            }
        }
        Set<String> result = new LinkedHashSet<>();
        for (MethodEvent method : methodEvents) {
            RuntimeEvent site = sites.get(method.parentSiteId);
            if (site != null) {
                result.add(site.siteId + "=>" + method.method);
            }
        }
        return limited(sorted(result), 512);
    }

    private static boolean invokedAnchor(List<RuntimeEvent> events,
                                         String anchorMethod) {
        if (anchorMethod == null || anchorMethod.isEmpty()) {
            return false;
        }
        for (RuntimeEvent event : events) {
            if ("CALL_SITE_ENTER".equals(event.kind)
                    && anchorMethod.equals(event.declaredCallee)) {
                return true;
            }
        }
        return false;
    }

    private static List<Map<String, Object>> inputObservations(
            StaticRegion region, MethodEvent root, Set<Long> calls,
            List<RuntimeEvent> events, List<FieldAccessEvent> fields,
            List<MethodEvent> methods) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (StaticPort port : region.inputs) {
            Map<String, Object> observation = object(
                    "portId", port.portId,
                    "cell", port.cell,
                    "sourceKind", port.sourceKind,
                    "projection", port.projection,
                    "observed", false);
            int parameter = parameterIndex(port.cell);
            String staticInputMethod = methodInCell(port.cell);
            boolean rootArgument = parameter >= 0
                    && (staticInputMethod.isEmpty()
                    || staticInputMethod.equals(root.method));
            if (rootArgument) {
                RuntimeEvent argument = methodArgument(events, root.callId, parameter);
                if (argument != null) {
                    observation.put("observed", true);
                    observation.put("location", "ARGUMENT");
                    observation.put("index", parameter);
                    observation.put("runtimeType", argument.runtimeType);
                    observation.put("objectId", argument.objectId);
                    observation.put("primitiveValue", argument.primitiveValue);
                }
            }
            if (!Boolean.TRUE.equals(observation.get("observed"))) {
                FieldAccessEvent field = matchingField(fields, port, root,
                        methods, events);
                if (field != null) {
                    observation.put("observed", true);
                    observation.put("location",
                            materializableFieldLocation(port));
                    observation.put("field", field.field);
                    observation.put("fieldReceiverObjectId", field.receiverObjectId);
                    observation.put("valueObjectId", field.valueObjectId);
                    observation.put("primitiveValue", field.primitiveValue);
                    observation.put("accessKind", field.kind);
                }
            }
            if (!Boolean.TRUE.equals(observation.get("observed"))) {
                AccessorReturnObservation accessor =
                        matchingPrimitiveAccessorReturn(region, port, events);
                if (accessor != null) {
                    // Older discovery overlays did not instrument every
                    // trivial inherited getter body, but they did record the
                    // exact caller/site receiver and its primitive return.
                    // The static port is admitted only from an exact
                    // accessor_field_return edge.  This join therefore
                    // identifies the same declared field without matching by
                    // field name or by a value alone.  Replay still
                    // symbolizes the real getfield and independently checks
                    // the accessor context in ConcolicRegionRuntime.
                    observation.put("observed", true);
                    observation.put("location", "HEAP_OBJECT_FIELD");
                    observation.put("field", port.cell);
                    observation.put("fieldReceiverObjectId",
                            accessor.enter.objectId);
                    observation.put("primitiveValue",
                            accessor.returned.primitiveValue);
                    observation.put("accessKind", "ACCESSOR_RETURN");
                    observation.put("observationAuthority",
                            "RUNTIME_EXACT_ACCESSOR_CALL_RETURN_PLUS_"
                                    + "STATIC_DIRECT_FIELD_ACCESSOR_V1");
                    observation.put("accessorInvocationId",
                            accessor.enter.invocationId);
                    observation.put("accessorRuntimeType",
                            accessor.enter.runtimeType);
                }
            }
            if (!Boolean.TRUE.equals(observation.get("observed"))
                    && parameter >= 0 && !rootArgument) {
                observation.put("location", "REGION_LIVE_IN");
                observation.put("deferredResolution", true);
                observation.put("crossMethodArgument", true);
                observation.put("staticInputMethod", staticInputMethod);
                observation.put("runtimeInputMethod", root.method);
                observation.put("rebaseRejectedAuthority",
                        "STATIC_INPUT_METHOD_DIFFERS_FROM_RUNTIME_ROOT");
            }
            if (!Boolean.TRUE.equals(observation.get("observed"))
                    && "PROTOCOL_INPUT".equals(port.sourceKind)) {
                // Callback/decoder projections may live below the Java method
                // argument boundary. The concolic bridge resolves the cell at
                // the first matching runtime value probe.
                observation.put("location", "REGION_LIVE_IN");
                observation.put("deferredResolution", true);
            }
            if (!Boolean.TRUE.equals(observation.get("observed"))
                    && "ENVIRONMENT".equals(port.sourceKind)
                    && VM_CURRENT_TIME_MILLIS_RETURN.equals(port.cell)) {
                // This is the sole environment value currently backed by a
                // customized-VM symbolic placeholder.  It remains unforced
                // during replay; the scheduler and importer validate that
                // exact contract before admitting a summary.
                observation.put("location", "ENVIRONMENT_MODEL");
                observation.put("deferredResolution", true);
                observation.put("deferredResolutionAuthority",
                        VM_INTRINSIC_DEFERRED_AUTHORITY);
            }
            if (!Boolean.TRUE.equals(observation.get("observed"))
                    && "OPAQUE_CALL".equals(port.sourceKind)) {
                // A call-return live-in is resolved lazily from the
                // authoritative static DefinitionIndex.  Zero or ambiguous
                // exact definitions remain a scheduler-side hard failure.
                observation.put("location", "CALL_RETURN");
                observation.put("deferredResolution", true);
                observation.put("deferredResolutionAuthority",
                        CALL_RETURN_DEFERRED_AUTHORITY);
            }
            if (!Boolean.TRUE.equals(observation.get("observed"))
                    && "SHARED_HEAP".equals(port.sourceKind)
                    && !fieldCell(port.cell).declaredSignature) {
                // A method-local "#field:name" projection has no declared
                // owner.  Replaying it as HEAP_OBJECT_FIELD would make the
                // bytecode transformer search by field name alone and can
                // bind an unrelated owner. Keep it as an explicit live-in
                // gap until static analysis or runtime evidence supplies the
                // canonical declared field signature.
                observation.put("location", "REGION_LIVE_IN");
                observation.put("deferredResolution", true);
                observation.put("fieldBindingGap",
                        "MISSING_CANONICAL_DECLARED_FIELD_SIGNATURE");
            }
            result.add(observation);
        }
        return result;
    }

    private static String materializableFieldLocation(StaticPort port) {
        if ("RECEIVER_FIELD".equals(port.sourceKind)) {
            return "RECEIVER_FIELD";
        }
        if ("SHARED_HEAP".equals(port.sourceKind)) {
            return "HEAP_OBJECT_FIELD";
        }
        return "FIELD";
    }

    private static RuntimeEvent methodArgument(List<RuntimeEvent> events,
                                               long callId, int index) {
        for (RuntimeEvent event : events) {
            if ("METHOD_ARGUMENT".equals(event.kind)
                    && event.callId == callId
                    && event.argumentIndex == index) {
                return event;
            }
        }
        return null;
    }

    private static FieldAccessEvent matchingField(List<FieldAccessEvent> fields,
                                                   StaticPort port,
                                                   MethodEvent root,
                                                   List<MethodEvent> methods,
                                                   List<RuntimeEvent> events) {
        FieldCell expected = fieldCell(port.cell);
        if (!expected.materializable()) {
            return null;
        }
        Map<Long, MethodEvent> methodsByCall = new LinkedHashMap<>();
        for (MethodEvent method : values(methods)) {
            methodsByCall.put(method.callId, method);
        }
        Map<Long, RuntimeEvent> callSitesByInvocation = new LinkedHashMap<>();
        for (RuntimeEvent event : values(events)) {
            if ("CALL_SITE_ENTER".equals(event.kind)
                    && event.invocationId > 0L) {
                callSitesByInvocation.put(event.invocationId, event);
            }
        }
        FieldAccessEvent fallback = null;
        for (FieldAccessEvent field : fields) {
            if (!sameField(expected, fieldCell(field.field))) {
                continue;
            }
            String accessMethod = string(port.materializationMetadata.get(
                    "accessMethod"));
            String accessSiteId = string(port.materializationMetadata.get(
                    "accessSiteId"));
            String accessAuthority = string(port.materializationMetadata.get(
                    "accessSiteAuthority"));
            int accessUnitIndex = port.materializationMetadata.get(
                    "accessUnitIndex") instanceof Number
                    ? ((Number) port.materializationMetadata.get(
                    "accessUnitIndex")).intValue() : -1;
            boolean directSiteConstrained = !accessMethod.isEmpty()
                    || !accessSiteId.isEmpty() || accessUnitIndex >= 0
                    || !accessAuthority.isEmpty();
            if (directSiteConstrained
                    && (!("STATIC_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1"
                    .equals(accessAuthority))
                    || !accessMethod.equals(field.method)
                    || accessUnitIndex != field.unitIndex
                    || !accessSiteId.equals(field.siteId)
                    || !accessSiteId.equals(field.method + "#u"
                    + field.unitIndex))) {
                continue;
            }
            String accessorCallerMethod = string(
                    port.materializationMetadata.get(
                            "accessorCallerMethod"));
            String accessorCallSiteId = string(
                    port.materializationMetadata.get(
                            "accessorCallSiteId"));
            String accessorDeclaredCallee = string(
                    port.materializationMetadata.get(
                            "accessorDeclaredCallee"));
            String accessorAuthority = string(
                    port.materializationMetadata.get(
                            "accessorCallSiteAuthority"));
            String accessorImplementationMethod = string(
                    port.materializationMetadata.get(
                            "accessorImplementationMethod"));
            String accessorImplementationAuthority = string(
                    port.materializationMetadata.get(
                            "accessorImplementationAuthority"));
            int accessorCallUnitIndex = port.materializationMetadata.get(
                    "accessorCallUnitIndex") instanceof Number
                    ? ((Number) port.materializationMetadata.get(
                    "accessorCallUnitIndex")).intValue() : -1;
            boolean accessorConstrained = !accessorCallerMethod.isEmpty()
                    || !accessorCallSiteId.isEmpty()
                    || !accessorDeclaredCallee.isEmpty()
                    || !accessorAuthority.isEmpty()
                    || !accessorImplementationMethod.isEmpty()
                    || !accessorImplementationAuthority.isEmpty()
                    || accessorCallUnitIndex >= 0;
            if (accessorConstrained) {
                MethodEvent fieldMethod = methodsByCall.get(field.callId);
                RuntimeEvent parentSite = fieldMethod == null ? null
                        : callSitesByInvocation.get(
                        fieldMethod.parentSiteId);
                if (!("STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                        .concat("ACCESSOR_CALLSITE_V1").equals(
                                accessorAuthority))
                        || parentSite == null
                        || !accessorCallerMethod.equals(parentSite.method)
                        || !accessorCallSiteId.equals(parentSite.siteId)
                        || !accessorCallSiteId.equals(accessorCallerMethod
                        + "#u" + accessorCallUnitIndex)
                        || !accessorDeclaredCallee.equals(
                        parentSite.declaredCallee)
                        || !"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY"
                        .equals(accessorImplementationAuthority)
                        || !accessorImplementationMethod.equals(
                        field.method)) {
                    continue;
                }
            }
            if ("RECEIVER_FIELD".equals(port.sourceKind)
                    && root.objectId != 0
                    && field.receiverObjectId != root.objectId) {
                continue;
            }
            if ("FIELD_READ".equals(field.kind)) {
                return field;
            }
            fallback = field;
        }
        return fallback;
    }

    /**
     * Recovers a promoted primitive declared-field observation from the
     * unique exact accessor call when the discovery overlay did not emit the
     * getter body's FIELD_READ.  This is intentionally narrower than a
     * generic call-return fallback: all static accessor metadata must be
     * present and authoritative, the caller/site/callee tuple must match one
     * runtime invocation, the resolved implementation must belong to the
     * selected static region, and exactly one well-typed return must pair
     * with that invocation.
     */
    private static AccessorReturnObservation matchingPrimitiveAccessorReturn(
            StaticRegion region, StaticPort port,
            List<RuntimeEvent> events) {
        FieldCell expected = fieldCell(port.cell);
        if (!expected.declaredSignature
                || !primitiveType(expected.type)) {
            return null;
        }

        String accessSignature = string(port.materializationMetadata.get(
                "accessFieldSignature"));
        String accessOwner = string(port.materializationMetadata.get(
                "accessOwnerClass"));
        String accessType = string(port.materializationMetadata.get(
                "accessFieldType"));
        String accessField = string(port.materializationMetadata.get(
                "accessField"));
        String caller = string(port.materializationMetadata.get(
                "accessorCallerMethod"));
        String site = string(port.materializationMetadata.get(
                "accessorCallSiteId"));
        String declaredCallee = string(port.materializationMetadata.get(
                "accessorDeclaredCallee"));
        String callAuthority = string(port.materializationMetadata.get(
                "accessorCallSiteAuthority"));
        String implementation = string(port.materializationMetadata.get(
                "accessorImplementationMethod"));
        String implementationAuthority = string(
                port.materializationMetadata.get(
                        "accessorImplementationAuthority"));
        int unit = port.materializationMetadata.get("accessorCallUnitIndex")
                instanceof Number ? ((Number) port.materializationMetadata
                .get("accessorCallUnitIndex")).intValue() : -1;
        if (!expected.signature().equals(accessSignature)
                || !expected.owner.equals(accessOwner)
                || !expected.type.equals(accessType)
                || !expected.name.equals(accessField)
                || caller.isEmpty() || unit < 0
                || !site.equals(caller + "#u" + unit)
                || declaredCallee.isEmpty() || implementation.isEmpty()
                || !expected.type.equals(methodReturnType(declaredCallee))
                || !expected.type.equals(methodReturnType(implementation))
                || !"STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                .concat("ACCESSOR_CALLSITE_V1").equals(callAuthority)
                || !"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY"
                .equals(implementationAuthority)
                || !region.methods.contains(caller)
                || !(region.methods.contains(implementation)
                || accessorAdmittedByOutputSlice(region, port.portId,
                caller, implementation))) {
            return null;
        }

        AccessorReturnObservation selected = null;
        for (RuntimeEvent enter : events) {
            if (!"CALL_SITE_ENTER".equals(enter.kind)
                    || enter.invocationId <= 0L || enter.callId <= 0L
                    || enter.objectId == 0 || enter.runtimeType.isEmpty()
                    || !caller.equals(enter.method)
                    || !site.equals(enter.siteId)
                    || !declaredCallee.equals(enter.declaredCallee)) {
                continue;
            }
            RuntimeEvent pairedReturn = null;
            for (RuntimeEvent returned : events) {
                if (!"CALL_SITE_RETURN".equals(returned.kind)
                        || returned.seq <= enter.seq
                        || returned.invocationId != enter.invocationId
                        || returned.callId != enter.callId
                        || !caller.equals(returned.method)
                        || !site.equals(returned.siteId)
                        || !declaredCallee.equals(returned.declaredCallee)
                        || !exactPrimitiveValue(expected.type,
                        returned.primitiveValue)) {
                    continue;
                }
                if (pairedReturn != null) {
                    return null;
                }
                pairedReturn = returned;
            }
            if (pairedReturn == null || selected != null) {
                return null;
            }
            selected = new AccessorReturnObservation(enter, pairedReturn);
        }
        return selected;
    }

    private static boolean accessorAdmittedByOutputSlice(
            StaticRegion region, String inputPort, String caller,
            String implementation) {
        for (StaticOutputSlice slice : region.outputSlices.values()) {
            if (slice.inputPorts.contains(safe(inputPort))
                    && slice.methods.contains(safe(caller))
                    && slice.methods.contains(safe(implementation))) {
                return true;
            }
        }
        return false;
    }

    private static boolean primitiveType(String type) {
        String declared = safe(type);
        return "boolean".equals(declared) || "char".equals(declared)
                || "byte".equals(declared) || "short".equals(declared)
                || "int".equals(declared) || "long".equals(declared)
                || "float".equals(declared) || "double".equals(declared);
    }

    private static boolean exactPrimitiveValue(String type, String value) {
        String declared = safe(type);
        String concrete = safe(value);
        try {
            if ("boolean".equals(declared)) {
                return "true".equals(concrete) || "false".equals(concrete);
            }
            if ("char".equals(declared)) {
                return concrete.length() == 1;
            }
            if ("byte".equals(declared)) {
                Byte.parseByte(concrete);
                return true;
            }
            if ("short".equals(declared)) {
                Short.parseShort(concrete);
                return true;
            }
            if ("int".equals(declared)) {
                Integer.parseInt(concrete);
                return true;
            }
            if ("long".equals(declared)) {
                Long.parseLong(concrete);
                return true;
            }
            if ("float".equals(declared)) {
                Float.parseFloat(concrete);
                return true;
            }
            if ("double".equals(declared)) {
                Double.parseDouble(concrete);
                return true;
            }
        } catch (NumberFormatException ignored) {
            return false;
        }
        return false;
    }

    private static List<Map<String, Object>> symbolizeActions(
            StaticRegion region, MethodEvent root,
            List<Map<String, Object>> inputObjects,
            List<RuntimeEvent> runtimeEvents,
            List<FieldAccessEvent> fieldEvents) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (int index = 0; index < region.inputs.size(); index++) {
            StaticPort port = region.inputs.get(index);
            Map<String, Object> observation = inputObjects.get(index);
            String location = string(observation.get("location"));
            Map<String, Object> action = object(
                    "symbol", port.portId,
                    "cell", port.cell,
                    "sourceKind", port.sourceKind,
                    "projection", port.projection,
                    "location", location.isEmpty()
                            ? locationFor(port) : location,
                    "observed", Boolean.TRUE.equals(observation.get("observed")));
            String declaredJavaType = declaredJavaType(port.cell);
            if (!declaredJavaType.isEmpty()) {
                action.put("javaType", declaredJavaType);
            }
            // Preserve exact leaf/path declarations carried by the static
            // port.  They are required for local/call-return array leaves,
            // whose root definition is resolved only by the scheduler.
            action.putAll(port.materializationMetadata);
            copy(observation, action, "index", "field", "objectId",
                    "fieldReceiverObjectId", "valueObjectId", "runtimeType",
                    "primitiveValue", "deferredResolution", "runtimeRebased",
                    "deferredResolutionAuthority",
                    "staticInputMethod", "runtimeInputMethod",
                    "rebaseAuthority", "crossMethodArgument",
                    "rebaseRejectedAuthority", "fieldBindingGap",
                    "accessKind", "observationAuthority",
                    "accessorInvocationId", "accessorRuntimeType");
            if ("HEAP_OBJECT_FIELD".equals(action.get("location"))) {
                FieldCell observedField = fieldCell(
                        string(observation.get("field")));
                FieldCell staticField = fieldCell(port.cell);
                FieldCell exact = observedField.declaredSignature
                        ? observedField : staticField.declaredSignature
                        ? staticField : FieldCell.unresolved();
                if (!exact.declaredSignature) {
                    action.put("location", "REGION_LIVE_IN");
                    action.put("deferredResolution", true);
                    action.put("fieldBindingGap",
                            "MISSING_CANONICAL_DECLARED_FIELD_SIGNATURE");
                } else {
                    action.put("accessOwnerClass", exact.owner);
                    action.put("accessField", exact.name);
                    action.put("accessFieldType", exact.type);
                    action.put("javaType", exact.type);
                    action.put("accessFieldSignature", exact.signature());
                    action.put("accessFieldAuthority",
                            observedField.declaredSignature
                                    ? "RUNTIME_FIELD_ACCESS_DECLARATION"
                                    : "STATIC_CANONICAL_DECLARED_FIELD");
                }
            }
            if ("RECEIVER_FIELD".equals(action.get("location"))) {
                action.put("receiverObjectId", root.objectId);
                action.put("materializationMode", "SHALLOW_FIELD");
            } else if ("ARGUMENT".equals(action.get("location"))) {
                Object observedObjectId = observation.get("objectId");
                int objectId = observedObjectId instanceof Number
                        ? ((Number) observedObjectId).intValue() : 0;
                int argumentIndex = observation.get("index") instanceof Number
                        ? ((Number) observation.get("index")).intValue()
                        : parameterIndex(port.cell);
                List<String> fields = observedArgumentFields(region,
                        root.method, argumentIndex, objectId, runtimeEvents);
                if (!fields.isEmpty()) {
                    action.put("location", "ARGUMENT_FIELD");
                    action.put("fields", fields);
                    action.put("materializationMode", "SELECTIVE_FIELDS");
                } else {
                    action.put("materializationMode", "RECURSIVE_OBJECT");
                }
            }
            result.add(action);
        }
        applyExactConsumedArrayFieldEvidence(result, root, fieldEvents);
        return result;
    }

    private static List<String> observedArgumentFields(
            StaticRegion region, String rootMethod, int argumentIndex,
            int argumentObjectId,
            List<RuntimeEvent> runtimeEvents) {
        if (argumentObjectId == 0) {
            return Collections.emptyList();
        }
        Set<String> fields = new LinkedHashSet<>();
        fields.addAll(region.argumentPathFields(rootMethod, argumentIndex));

        Set<String> relevantGetters = new LinkedHashSet<>();
        for (BranchPolicy branch : region.branches) {
            collectGetters(branch.guard, relevantGetters);
        }
        // The planner keeps a normalized Jimple branch as the executable
        // branch policy.  Higher-level guards recovered by the static pass
        // (for example allKeys.get(request.getKeyId()) == null) are emitted as
        // FAILURE_PREDICATE outputs.  Consult those predicates as well so the
        // runtime materializer does not lose the source-level field projection.
        for (StaticPort output : region.outputs) {
            if ("FAILURE_PREDICATE".equals(output.kind)) {
                collectGetters(output.cell, relevantGetters);
            }
        }
        if (!relevantGetters.isEmpty()) {
            for (RuntimeEvent event : runtimeEvents) {
                if (!"CALL_SITE_ENTER".equals(event.kind)
                        || event.objectId != argumentObjectId) {
                    continue;
                }
                String getter = methodName(event.declaredCallee);
                if (!relevantGetters.contains(getter)) {
                    continue;
                }
                String stem = getter.startsWith("get")
                        ? getter.substring(3) : getter.substring(2);
                if (!stem.isEmpty()) {
                    fields.add(Character.toLowerCase(stem.charAt(0))
                            + stem.substring(1));
                }
            }
        }
        return sorted(fields);
    }

    /**
     * Completes the static array-leaf declaration with the one concrete
     * getfield that consumed it in this region instance.  A class/name match
     * alone is deliberately insufficient: repeated reads, a missing unit
     * index/site id, a different object-id path, or a null array all leave the
     * action incomplete.  Runtime materialization is one-shot, so the planner
     * must prove one occurrence rather than silently selecting one.
     */
    private static void applyExactConsumedArrayFieldEvidence(
            List<Map<String, Object>> actions, MethodEvent root,
            List<FieldAccessEvent> fieldEvents) {
        for (Map<String, Object> action : actions) {
            ArrayFieldLeaf leaf = ArrayFieldLeaf.from(action);
            if (!leaf.fieldBackedArray) {
                continue;
            }
            clearConsumedFieldEvidence(action);
            if (!leaf.complete()) {
                markConsumedFieldIncomplete(action, leaf.issue);
                continue;
            }

            List<FieldAccessEvent> matches = new ArrayList<>();
            for (FieldAccessEvent event : values(fieldEvents)) {
                if (!"FIELD_READ".equals(event.kind)
                        || event.unitIndex < 0
                        || event.method.isEmpty()
                        || !event.siteId.equals(event.method + "#u"
                        + event.unitIndex)
                        || event.receiverObjectId == 0
                        || event.valueObjectId == 0
                        || !sameField(leaf.declaration,
                        fieldCell(event.field))) {
                    continue;
                }
                matches.add(event);
            }
            if (matches.size() != 1) {
                markConsumedFieldIncomplete(action,
                        matches.isEmpty()
                                ? "NO_EXACT_NON_NULL_RUNTIME_FIELD_READ"
                                : "REPEATED_OR_AMBIGUOUS_RUNTIME_FIELD_READ:"
                                + matches.size());
                continue;
            }

            FieldAccessEvent consumed = matches.get(0);
            String rootAuthority = consumedFieldRootAuthority(action, root,
                    leaf.path, consumed, fieldEvents);
            if (rootAuthority.isEmpty()) {
                markConsumedFieldIncomplete(action,
                        "CONSUMED_FIELD_ROOT_IDENTITY_NOT_PROVEN");
                continue;
            }

            action.put("fieldPath", new ArrayList<>(leaf.path));
            action.put("leafField", leaf.declaration.name);
            action.put("leafOwnerClass", leaf.declaration.owner);
            action.put("leafFieldSignature", leaf.declaration.signature());
            action.put("javaType", leaf.declaration.type);
            action.put("javaTypeAuthority",
                    "STATIC_EXACT_CONSUMED_LEAF_FIELD_DECLARATION");
            if (!action.containsKey("fieldPathLeafDeclarations")) {
                List<Map<String, Object>> declarations = new ArrayList<>();
                declarations.add(object(
                        "fieldPath", new ArrayList<>(leaf.path),
                        "fieldSignature", leaf.declaration.signature(),
                        "declaredFieldOwnerClass", leaf.declaration.owner,
                        "declaredFieldType", leaf.declaration.type,
                        "complete", true));
                action.put("fieldPathLeafDeclarations", declarations);
            }
            action.put("consumedFieldMethod", consumed.method);
            action.put("consumedFieldUnitIndex", consumed.unitIndex);
            action.put("consumedFieldSiteId", consumed.siteId);
            action.put("consumedFieldSiteAuthority",
                    "RUNTIME_UNIQUE_STATIC_LEAF_GETFIELD_SITE_AND_OWNER_"
                            + "WITHIN_REGION_INSTANCE_V1");
            action.put("consumedFieldRootAuthority", rootAuthority);
            action.put("consumedFieldRuntimeEventSeq", consumed.seq);
            action.put("consumedFieldReceiverObjectId",
                    consumed.receiverObjectId);
            action.put("consumedFieldValueObjectId",
                    consumed.valueObjectId);
            action.put("consumedFieldOccurrence", 1);
            action.put("consumedFieldOccurrenceAuthority",
                    "UNIQUE_CONTAINED_RUNTIME_FIELD_READ_V1");
            if ("LOCAL_DEFINITION_ROOT_PENDING_AUTHORITATIVE_"
                    .concat("SCHEDULER_DEFINITION_INDEX_V1").equals(
                            rootAuthority)) {
                action.put("consumedFieldSiteBindingComplete", true);
                action.put("consumedFieldBindingComplete", false);
                action.put("consumedFieldBindingIssue",
                        "LOCAL_ROOT_DEFINITION_PENDING_SCHEDULER");
            } else {
                action.put("consumedFieldBindingComplete", true);
                action.remove("consumedFieldBindingIssue");
            }
        }
    }

    private static void clearConsumedFieldEvidence(
            Map<String, Object> action) {
        for (String key : new String[]{
                "consumedFieldMethod", "consumedFieldUnitIndex",
                "consumedFieldSiteId", "consumedFieldSiteAuthority",
                "consumedFieldRootAuthority",
                "consumedFieldRuntimeEventSeq",
                "consumedFieldReceiverObjectId",
                "consumedFieldValueObjectId", "consumedFieldOccurrence",
                "consumedFieldOccurrenceAuthority",
                "consumedFieldSiteBindingComplete",
                "consumedFieldPendingRootKind",
                "consumedFieldPendingRootMethod",
                "consumedFieldPendingRootLocal"}) {
            action.remove(key);
        }
        action.put("consumedFieldBindingComplete", false);
    }

    private static void markConsumedFieldIncomplete(
            Map<String, Object> action, String issue) {
        action.put("consumedFieldBindingComplete", false);
        action.put("consumedFieldBindingIssue", firstNonBlank(issue,
                "EXACT_CONSUMED_FIELD_EVIDENCE_INCOMPLETE"));
    }

    private static String consumedFieldRootAuthority(
            Map<String, Object> action, MethodEvent root, List<String> path,
            FieldAccessEvent consumed,
            List<FieldAccessEvent> fieldEvents) {
        String location = string(action.get("location"));
        String mode = string(action.get("bindingMode"));
        if ("ARGUMENT_FIELD".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location)) {
            int index = action.get("index") instanceof Number
                    ? ((Number) action.get("index")).intValue() : -1;
            int rootObjectId = action.get("objectId") instanceof Number
                    ? ((Number) action.get("objectId")).intValue() : 0;
            return index >= 0 && runtimeFieldPathIdentity(rootObjectId, path,
                    consumed, fieldEvents)
                    ? "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_"
                    + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY" : "";
        }
        if ("RECEIVER_FIELD".equals(location)) {
            return root != null && runtimeFieldPathIdentity(root.objectId,
                    path, consumed, fieldEvents)
                    ? "ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_"
                    + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY" : "";
        }
        Matcher pendingLocal = LOCAL_CELL.matcher(string(action.get(
                "cell")));
        if ("REGION_LIVE_IN".equals(location)
                && pendingLocal.matches()) {
            action.put("consumedFieldPendingRootKind",
                    "LOCAL_DEFINITION");
            action.put("consumedFieldPendingRootMethod",
                    pendingLocal.group(1));
            action.put("consumedFieldPendingRootLocal",
                    pendingLocal.group(2));
            return "LOCAL_DEFINITION_ROOT_PENDING_AUTHORITATIVE_"
                    + "SCHEDULER_DEFINITION_INDEX_V1";
        }
        if ("CALL_RETURN".equals(location)) {
            action.put("consumedFieldPendingRootKind",
                    "CALL_RETURN_DEFINITION");
            return "LOCAL_DEFINITION_ROOT_PENDING_AUTHORITATIVE_"
                    + "SCHEDULER_DEFINITION_INDEX_V1";
        }
        if ("LOCAL_DEFINITION".equals(mode)) {
            List<Map<String, Object>> definitions = mapRows(action.get(
                    "definitionSites"));
            String method = string(action.get("method"));
            String local = string(action.get("local"));
            if (method.isEmpty() || local.isEmpty()
                    || definitions.size() != 1
                    || !(definitions.get(0).get("unitIndex")
                    instanceof Number)
                    || ((Number) definitions.get(0).get("unitIndex"))
                    .intValue() < 0) {
                return "";
            }
            return "LOCAL_DEFINITION_IDENTITY_AT_EXACT_DEFINITION_SITE_"
                    + "AND_LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
        }

        // A generic heap input may in fact be rooted at the activation's
        // receiver.  Prefer that stronger identity proof whenever the entire
        // runtime field path joins from the entry receiver.  Otherwise only a
        // direct one-segment leaf can use the real getfield base itself as the
        // input owner; no unregistered nested root is accepted.
        if (root != null && runtimeFieldPathIdentity(root.objectId, path,
                consumed, fieldEvents)) {
            return "ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_"
                    + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
        }
        return path.size() == 1
                ? "DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_OWNER_V1" : "";
    }

    private static boolean runtimeFieldPathIdentity(
            int rootObjectId, List<String> path,
            FieldAccessEvent consumed,
            List<FieldAccessEvent> fieldEvents) {
        if (rootObjectId == 0 || path == null || path.isEmpty()
                || consumed == null) {
            return false;
        }
        int owner = rootObjectId;
        for (int index = 0; index < path.size(); index++) {
            String segment = safe(path.get(index));
            List<FieldAccessEvent> matches = new ArrayList<>();
            for (FieldAccessEvent event : values(fieldEvents)) {
                FieldCell field = fieldCell(event.field);
                if ("FIELD_READ".equals(event.kind)
                        && event.seq <= consumed.seq
                        && event.receiverObjectId == owner
                        && field.declaredSignature
                        && field.name.equals(segment)) {
                    matches.add(event);
                }
            }
            if (matches.size() != 1) {
                return false;
            }
            FieldAccessEvent selected = matches.get(0);
            boolean leaf = index == path.size() - 1;
            if (leaf) {
                return selected == consumed
                        || selected.seq == consumed.seq;
            }
            if (selected.valueObjectId == 0) {
                return false;
            }
            owner = selected.valueObjectId;
        }
        return false;
    }

    private static final class ArrayFieldLeaf {
        private final boolean fieldBackedArray;
        private final FieldCell declaration;
        private final List<String> path;
        private final String issue;

        private ArrayFieldLeaf(boolean fieldBackedArray,
                               FieldCell declaration,
                               List<String> path, String issue) {
            this.fieldBackedArray = fieldBackedArray;
            this.declaration = declaration;
            this.path = path;
            this.issue = safe(issue);
        }

        private boolean complete() {
            return fieldBackedArray && declaration.declaredSignature
                    && !path.isEmpty() && issue.isEmpty();
        }

        private static ArrayFieldLeaf from(Map<String, Object> action) {
            String javaType = string(action.get("javaType"));
            String location = string(action.get("location"));
            String mode = string(action.get("bindingMode"));
            boolean fieldShape = "ARGUMENT_FIELD".equals(location)
                    || "ARGUMENT_FIELD_PATH".equals(location)
                    || "RECEIVER_FIELD".equals(location)
                    || "HEAP_OBJECT_FIELD".equals(location)
                    || "FIELD".equals(location)
                    || "FIELD_ACCESS".equals(mode);

            List<List<String>> paths = new ArrayList<>();
            List<String> directPath = stringList(action.get("fieldPath"));
            if (!directPath.isEmpty()) paths.add(directPath);
            Object nested = action.get("fieldPaths");
            if (paths.isEmpty() && nested instanceof Collection<?>) {
                for (Object candidate : (Collection<?>) nested) {
                    List<String> path = stringList(candidate);
                    if (!path.isEmpty()) paths.add(path);
                }
            }

            Set<String> signatures = new LinkedHashSet<>();
            signatures.add(string(action.get("leafFieldSignature")));
            signatures.add(string(action.get("accessFieldSignature")));
            signatures.add(string(action.get("field")));
            signatures.add(string(action.get("cell")));
            for (Map<String, Object> row : mapRows(action.get(
                    "fieldPathLeafDeclarations"))) {
                List<String> declarationPath = stringList(row.get(
                        "fieldPath"));
                if (!declarationPath.isEmpty()) paths.add(declarationPath);
                signatures.add(string(row.get("fieldSignature")));
            }
            signatures.remove("");

            boolean declaredArray = false;
            for (String signature : signatures) {
                FieldCell field = fieldCell(signature);
                if (field.declaredSignature
                        && isArrayJavaType(field.type)) {
                    declaredArray = true;
                    break;
                }
            }
            Matcher localCell = LOCAL_CELL.matcher(string(action.get(
                    "cell")));
            if (declaredArray && ("LOCAL_DEFINITION".equals(mode)
                    || "REGION_LIVE_IN".equals(location)
                    && localCell.matches()
                    || "CALL_RETURN".equals(location))) {
                fieldShape = true;
            }
            boolean array = isArrayJavaType(javaType) || declaredArray;
            boolean backed = fieldShape && array;
            if (!backed) {
                return new ArrayFieldLeaf(false, FieldCell.unresolved(),
                        Collections.<String>emptyList(), "");
            }
            if (!javaType.isEmpty() && !isArrayJavaType(javaType)) {
                return new ArrayFieldLeaf(true, FieldCell.unresolved(),
                        Collections.<String>emptyList(),
                        "ACTION_TYPE_CONFLICTS_WITH_ARRAY_LEAF_DECLARATION");
            }

            Set<String> uniquePaths = new LinkedHashSet<>();
            List<List<String>> normalizedPaths = new ArrayList<>();
            for (List<String> path : paths) {
                if (uniquePaths.add(joinPath(path))) {
                    normalizedPaths.add(path);
                }
            }
            Set<String> exactSignatures = new LinkedHashSet<>();
            FieldCell selected = FieldCell.unresolved();
            for (String signature : signatures) {
                FieldCell field = fieldCell(signature);
                if (field.declaredSignature && isArrayJavaType(field.type)
                        && (javaType.isEmpty()
                        || sameArrayJavaType(javaType, field.type))) {
                    exactSignatures.add(field.signature());
                    selected = field;
                }
            }
            if (normalizedPaths.isEmpty() && selected.declaredSignature) {
                normalizedPaths.add(Collections.singletonList(selected.name));
            }
            if (normalizedPaths.size() != 1) {
                return new ArrayFieldLeaf(true, FieldCell.unresolved(),
                        Collections.<String>emptyList(),
                        "ARRAY_LEAF_PATH_NOT_UNIQUE:"
                                + normalizedPaths.size());
            }
            List<String> selectedPath = normalizedPaths.get(0);
            if (exactSignatures.size() != 1
                    || !selected.declaredSignature
                    || !selected.name.equals(selectedPath.get(
                    selectedPath.size() - 1))) {
                return new ArrayFieldLeaf(true, FieldCell.unresolved(),
                        selectedPath,
                        "ARRAY_LEAF_DECLARATION_NOT_UNIQUE_OR_MISMATCHED:"
                                + exactSignatures.size());
            }
            return new ArrayFieldLeaf(true, selected, selectedPath, "");
        }
    }

    private static boolean isArrayJavaType(String type) {
        String value = safe(type).trim();
        return value.startsWith("[") || value.endsWith("[]");
    }

    private static boolean sameArrayJavaType(String left, String right) {
        return safe(left).replace(" ", "").equals(
                safe(right).replace(" ", ""));
    }

    private static void collectGetters(String expression,
                                       Set<String> destination) {
        Matcher matcher = GETTER_IN_GUARD.matcher(safe(expression));
        while (matcher.find()) {
            destination.add(matcher.group(1));
        }
    }

    private static String locationFor(StaticPort port) {
        if (parameterIndex(port.cell) >= 0) {
            return "ARGUMENT";
        }
        if ("RECEIVER_FIELD".equals(port.sourceKind)) {
            return "RECEIVER_FIELD";
        }
        if ("SHARED_HEAP".equals(port.sourceKind)) {
            return "HEAP_OBJECT_FIELD";
        }
        if ("PROTOCOL_INPUT".equals(port.sourceKind)
                || "RPC_INPUT".equals(port.sourceKind)) {
            return "REGION_LIVE_IN";
        }
        if ("ENVIRONMENT".equals(port.sourceKind)) {
            return "ENVIRONMENT_MODEL";
        }
        if ("OPAQUE_CALL".equals(port.sourceKind)) {
            return "CALL_RETURN";
        }
        return "REGION_LIVE_IN";
    }

    private static List<Map<String, Object>> outputActions(StaticRegion region) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (StaticPort port : region.outputs) {
            result.add(outputAction(port));
        }
        return result;
    }

    private static Map<String, Object> outputAction(StaticPort port) {
        return object(
                "symbol", port.portId,
                "cell", port.cell,
                "kind", port.kind,
                "location", "FAILURE_PREDICATE".equals(port.kind)
                        ? "THROW_OR_BRANCH" : "RETURN_OR_HEAP_EFFECT");
    }

    private static List<Map<String, Object>> branchActions(
            StaticRegion region, List<RuntimeEvent> events) {
        Map<String, List<RuntimeEvent>> observed = new LinkedHashMap<>();
        for (RuntimeEvent event : events) {
            if ("BRANCH".equals(event.kind)) {
                add(observed, event.siteId, event);
            }
        }
        List<Map<String, Object>> result = new ArrayList<>();
        for (BranchPolicy policy : region.branches) {
            List<RuntimeEvent> occurrences = values(observed.get(policy.siteId));
            RuntimeEvent event = selectBranchOccurrence(occurrences,
                    policy.requiredOutcome);
            Boolean observedOutcome = event != null && event.hasOutcome
                    ? event.outcome : null;
            Boolean matchesRequired = observedOutcome != null
                    && policy.requiredOutcome != null
                    ? observedOutcome.equals(policy.requiredOutcome) : null;
            List<Map<String, Object>> occurrenceRows = new ArrayList<>();
            int selectedOccurrence = -1;
            for (int index = 0; index < occurrences.size(); index++) {
                RuntimeEvent occurrence = occurrences.get(index);
                Boolean occurrenceMatches = occurrence.hasOutcome
                        && policy.requiredOutcome != null
                        ? occurrence.outcome == policy.requiredOutcome : null;
                if (occurrence == event) {
                    selectedOccurrence = index + 1;
                }
                occurrenceRows.add(object(
                        "occurrence", index + 1,
                        "seq", occurrence.seq,
                        "callId", occurrence.callId,
                        "outcome", occurrence.hasOutcome
                                ? occurrence.outcome : null,
                        "matchesRequiredOutcome", occurrenceMatches));
            }
            result.add(object(
                    "siteId", policy.siteId,
                    "policy", policy.policy,
                    "guard", policy.guard,
                    "requiredOutcome", policy.requiredOutcome,
                    "role", policy.role,
                    "observed", event != null,
                    "observedOutcome", observedOutcome,
                    "matchesRequiredOutcome", matchesRequired,
                    "occurrenceCount", occurrences.size(),
                    "selectedOccurrence", selectedOccurrence,
                    "occurrences", occurrenceRows,
                    "action", "EXPLORE".equals(policy.policy)
                            ? "ALLOW_NEGATION" : "PIN_TO_TRACE"));
        }
        return result;
    }

    /**
     * Selects the concrete occurrence that witnesses the static path contract.
     * Repeated callback and loop branches commonly execute both directions in
     * one region invocation, so retaining only the last event loses the path
     * that actually reached the anchor.  If no occurrence has the required
     * direction, the last concrete occurrence remains the scheduler's flip
     * candidate.
     */
    private static RuntimeEvent selectBranchOccurrence(
            List<RuntimeEvent> occurrences, Boolean requiredOutcome) {
        RuntimeEvent selected = null;
        for (RuntimeEvent occurrence : occurrences) {
            selected = occurrence;
            if (requiredOutcome != null && occurrence.hasOutcome
                    && occurrence.outcome == requiredOutcome) {
                return occurrence;
            }
        }
        return selected;
    }

    private static int countObserved(List<Map<String, Object>> observations) {
        int count = 0;
        for (Map<String, Object> observation : observations) {
            if (Boolean.TRUE.equals(observation.get("observed"))) {
                count++;
            }
        }
        return count;
    }

    private static int countDeferred(List<Map<String, Object>> observations) {
        int count = 0;
        for (Map<String, Object> observation : observations) {
            if (!Boolean.TRUE.equals(observation.get("observed"))
                    && Boolean.TRUE.equals(observation.get("deferredResolution"))) {
                count++;
            }
        }
        return count;
    }

    private static int countObservedBranches(List<Map<String, Object>> branches) {
        int count = 0;
        for (Map<String, Object> branch : branches) {
            if (Boolean.TRUE.equals(branch.get("observed"))) {
                count++;
            }
        }
        return count;
    }

    private static void validateRegionEdges(
            List<StaticRegionEdge> staticEdges,
            Map<String, List<InstanceEvidence>> evidenceByRegion,
            Result result, List<UpstreamEdgeBinding> edgeBindings) {
        for (StaticRegionEdge edge : staticEdges) {
            List<InstanceEvidence> upstreamInstances = values(
                    evidenceByRegion.get(edge.fromRegion));
            List<InstanceEvidence> downstreamInstances = values(
                    evidenceByRegion.get(edge.toRegion));
            int endpointPairs = 0;
            int orderedPairs = 0;
            int siteObservedPairs = 0;
            int readFromPairs = 0;
            int valueEqualityPairs = 0;
            List<Map<String, Object>> evidence = new ArrayList<>();
            List<Map<String, Object>> validatedBindings = new ArrayList<>();
            String endpointCorrelationAuthority =
                    endpointCorrelationAuthority(edge);
            Map<String, List<FingerprintMatch>> selectedValueMatches =
                    nearestEndpointFingerprintMatches(edge,
                            upstreamInstances, downstreamInstances);
            for (InstanceEvidence upstream : upstreamInstances) {
                for (InstanceEvidence downstream : downstreamInstances) {
                    if (!upstream.root.test.equals(downstream.root.test)) {
                        continue;
                    }
                    boolean siteObserved = observesSite(downstream.runtimeEvents,
                            edge.siteId)
                            || (rpcPortMapping(edge)
                            && observesMappedRpcInvocation(downstream.runtimeEvents,
                            edge.fromPort, edge.toPort));
                    if (!"SHARED_STATE".equals(edge.kind)
                            && (!observesPortMethod(upstream, edge.fromPort)
                            || (!observesPortMethod(downstream, edge.toPort)
                            && !siteObserved))) {
                        continue;
                    }
                    endpointPairs++;
                    boolean sameProcess = upstream.root.process.equals(
                            downstream.root.process);
                    if (siteObserved) {
                        siteObservedPairs++;
                    }
                    List<FingerprintMatch> valueMatches = values(
                            selectedValueMatches.get(endpointInstancePairKey(
                                    upstream, downstream)));
                    FingerprintMatch valueMatch = valueMatches.isEmpty()
                            ? null : valueMatches.get(0);
                    SharedReadFrom readFrom = "SHARED_STATE".equals(edge.kind)
                            ? sharedReadFrom(edge, upstream, downstream) : null;
                    // A complete endpoint match and a confirmed read-from
                    // carry their own global-trace order evidence.  In
                    // particular, a long-lived writer region can continue
                    // after the consumer read, so comparing region lastSeq()
                    // values must not override the concrete writeSeq <=
                    // readSeq witness established by sharedReadFrom().
                    boolean ordered = !edge.requiresOrder || siteObserved
                            || valueMatch != null || readFrom != null
                            || (sameProcess && upstream.lastSeq()
                            <= downstream.lastSeq());
                    if (ordered) {
                        orderedPairs++;
                    }
                    if (readFrom != null) {
                        readFromPairs++;
                        edgeBindings.add(new UpstreamEdgeBinding(edge,
                                upstream, downstream, readFrom));
                    }
                    valueEqualityPairs += valueMatches.size();
                    Map<String, Object> row = object(
                            "fromRegionInstance", upstream.instanceId,
                            "toRegionInstance", downstream.instanceId,
                            "test", upstream.root.test,
                            "fromProcess", upstream.root.process,
                            "fromThreadId", upstream.root.tid,
                            "toProcess", downstream.root.process,
                            "toThreadId", downstream.root.tid,
                            "sameProcess", sameProcess,
                            "differentThread", !sameProcess
                                    || upstream.root.tid != downstream.root.tid,
                            "siteObserved", siteObserved,
                            "orderConfirmed", ordered);
                    if (valueMatch != null) {
                        row.put("fromEndpointSeq", valueMatch.from.seq);
                        row.put("toEndpointSeq", valueMatch.to.seq);
                        row.put("fromFingerprintSource",
                                valueMatch.from.source);
                        row.put("toFingerprintSource",
                                valueMatch.to.source);
                        row.put("valueFingerprint",
                                valueMatch.from.digest);
                        row.put("valueEqualityObserved", true);
                        row.put("valueEqualityAuthority",
                                "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
                        row.put("endpointOrderAuthority",
                                "GLOBAL_TRACE_ENDPOINT_SEQUENCE");
                        row.put("endpointCorrelationAuthority",
                                endpointCorrelationAuthority);
                    }
                    if (readFrom != null) {
                        row.put("writeSeq", readFrom.writerEventSeq());
                        row.put("readSeq", readFrom.read.seq);
                        row.put("field", readFrom.write.field);
                        row.put("writeEvidenceKind",
                                readFrom.writeEvidence.kind);
                        row.put("writerSiteId", readFrom.writerSiteId());
                        row.put("writerCallId", readFrom.writerCallId());
                        row.put("writerOccurrence",
                                upstream.runtimeOccurrence(
                                        readFrom.writeEvidence.mutation));
                        row.put("receiverObjectId",
                                readFrom.write.receiverObjectId);
                        row.put("valueObjectId",
                                readFrom.write.valueObjectId);
                    }
                    if (readFrom != null || valueMatch != null) {
                        validatedBindings.add(row);
                    }
                    for (int matchIndex = 1;
                         matchIndex < valueMatches.size(); matchIndex++) {
                        FingerprintMatch additional = valueMatches.get(
                                matchIndex);
                        Map<String, Object> additionalRow =
                                new LinkedHashMap<>(row);
                        additionalRow.put("fromEndpointSeq",
                                additional.from.seq);
                        additionalRow.put("toEndpointSeq",
                                additional.to.seq);
                        additionalRow.put("fromFingerprintSource",
                                additional.from.source);
                        additionalRow.put("toFingerprintSource",
                                additional.to.source);
                        additionalRow.put("valueFingerprint",
                                additional.from.digest);
                        validatedBindings.add(additionalRow);
                    }
                    if (evidence.size() < 16) {
                        evidence.add(row);
                    }
                }
            }

            String status;
            String validation;
            if ("SHARED_STATE".equals(edge.kind)) {
                if (readFromPairs > 0) {
                    status = "CONFIRMED_READ_FROM";
                    validation = "FIELD_RECEIVER_IDENTITY_AND_WRITE_BEFORE_READ";
                } else if (endpointPairs > 0) {
                    status = "UNCONFIRMED_READ_FROM";
                    validation = "ENDPOINTS_OBSERVED_BUT_NO_MATCHING_RUNTIME_WRITE_READ";
                } else {
                    status = "UNOBSERVED";
                    validation = "NO_REGION_INSTANCE_PAIR";
                }
            } else if (endpointPairs == 0) {
                status = "UNOBSERVED";
                validation = "NO_REGION_INSTANCE_PAIR";
            } else if (valueEqualityPairs > 0) {
                status = "CONFIRMED_RUNTIME_VALUE_EQUALITY";
                validation = "COMPLETE_ENDPOINT_VALUE_FINGERPRINT_EQUALITY";
            } else if (orderedPairs > 0) {
                status = "PORT_MAPPING_OBSERVED_VALUE_EQUALITY_UNPROVEN";
                validation = "ORDERED_ENDPOINTS_WITHOUT_COMPLETE_MATCHING_"
                        + "VALUE_FINGERPRINT";
            } else {
                status = "ENDPOINTS_OBSERVED";
                validation = "PORT_ORDER_AND_VALUE_EQUALITY_UNPROVEN";
            }

            boolean readFromComposable = "CONFIRMED_READ_FROM".equals(status);
            boolean equalityComposable =
                    "CONFIRMED_RUNTIME_VALUE_EQUALITY".equals(status);
            boolean composable = readFromComposable || equalityComposable;

            Map<String, Object> validationRow = object(
                    "edgeId", edge.edgeId,
                    "fromRegion", edge.fromRegion,
                    "toRegion", edge.toRegion,
                    "kind", edge.kind,
                    "relation", composable
                            ? readFromComposable ? "READ_FROM" : "EQUALITY"
                            : "",
                    "candidateRelation", firstNonBlank(
                            edge.candidateRelation, edge.relation),
                    "fromPort", edge.fromPort,
                    "toPort", edge.toPort,
                    "requiresOrder", edge.requiresOrder,
                    "requiresObjectIdentity", edge.requiresObjectIdentity,
                    "mappingKind", edge.mappingKind,
                    "mappingAuthority", "SHARED_STATE".equals(edge.kind)
                            ? "" : "STATIC_FORMAT_AND_PORT_MAPPING",
                    "sourceMappingAuthority", edge.mappingAuthority,
                    "payloadEqualityCheckRequired",
                    edge.payloadEqualityCheckRequired,
                    "siteId", edge.siteId,
                    "status", status,
                    "validation", validation,
                    "validatedRelation", readFromComposable ? "READ_FROM"
                            : equalityComposable ? "EQUALITY" : "",
                    "composable", composable,
                    "eligibleForRecursiveDiscovery", endpointPairs > 0
                            && (!edge.requiresOrder || orderedPairs > 0),
                    "eligibleForAutomaticDerivation", composable,
                    "eligibleForAutomaticSmt", composable,
                    "mappingOnly", !composable,
                    "semanticAssertionsAllowed", composable,
                    "exclusionReason", composable ? ""
                            : "NO_RUNTIME_VALIDATED_VALUE_RELATION",
                    "endpointPairCount", endpointPairs,
                    "orderedPairCount", orderedPairs,
                    "siteObservedPairCount", siteObservedPairs,
                    "confirmedReadFromPairCount", readFromPairs,
                    "confirmedValueEqualityPairCount", valueEqualityPairs,
                    "valueEqualityObserved", equalityComposable,
                    "valueEqualityAuthority", equalityComposable
                            ? "RUNTIME_COMPLETE_VALUE_FINGERPRINT" : "",
                    "endpointOrderAuthority", equalityComposable
                            ? "GLOBAL_TRACE_ENDPOINT_SEQUENCE" : "",
                    "endpointCorrelationAuthority", equalityComposable
                            ? endpointCorrelationAuthority
                            : "",
                    "validatedBindingCount", validatedBindings.size(),
                    "validatedBindings", validatedBindings,
                    "evidence", evidence);
            if (edge.canonicalMetadataPresent) {
                validationRow.put("fromOutputPort", edge.fromOutputPort);
                validationRow.put("fromOutputCell", edge.fromOutputCell);
                validationRow.put("aliasProofEdgeIds",
                        new ArrayList<>(edge.aliasProofEdgeIds));
                validationRow.put("aliasProofAuthority",
                        edge.aliasProofAuthority);
                validationRow.put("aliasProofComplete",
                        edge.aliasProofComplete);
            }
            result.edgeValidations.add(validationRow);
        }
    }

    /**
     * Derives a separate upstream-output activation from confirmed runtime
     * read-from evidence.  The original path activation is preserved because a
     * region may simultaneously contain the target and provide an output for
     * another region query.
     */
    private static int deriveUpstreamActivations(
            List<UpstreamEdgeBinding> bindings, Result result) {
        Map<String, Map<String, Object>> baseByInstance = new LinkedHashMap<>();
        for (Map<String, Object> activation : result.activations) {
            baseByInstance.put(string(activation.get("regionInstanceId")),
                    activation);
        }

        Map<String, List<UpstreamEdgeBinding>> grouped = new LinkedHashMap<>();
        Set<String> seen = new LinkedHashSet<>();
        for (UpstreamEdgeBinding binding : bindings) {
            StaticPort output = binding.edge.producerOutputFor(
                    binding.upstream.region);
            if (output == null) {
                result.warnings.add("confirmed upstream edge "
                        + binding.edge.edgeId + " has no unique output port for "
                        + binding.edge.producerOutputEndpoint());
                continue;
            }
            binding.output = output;
            binding.downstreamInput = binding.downstream.region.inputFor(
                    binding.edge.toPort);
            String identity = binding.identity();
            if (!seen.add(identity)) {
                continue;
            }
            add(grouped, binding.upstream.instanceId + "\n" + output.portId,
                    binding);
        }

        int activationIndex = 0;
        for (List<UpstreamEdgeBinding> group : grouped.values()) {
            UpstreamEdgeBinding first = group.get(0);
            Map<String, Object> base = baseByInstance.get(
                    first.upstream.instanceId);
            if (base == null) {
                result.warnings.add("confirmed upstream instance has no base "
                        + "activation: " + first.upstream.instanceId);
                continue;
            }

            Map<String, Object> activation = new LinkedHashMap<>(base);
            String derivedId = "ACT.UPSTREAM." + activationIndex++;
            activation.put("activationId", derivedId);
            activation.put("derivedFromActivationId",
                    string(base.get("activationId")));
            activation.remove("summaryMode");
            activation.put("captureGoal", object(
                    "kind", "OUTPUT_CLOSURE",
                    "scope", "BOUNDED_OUTPUT_RELEVANT_PATHS",
                    "authority", "RUNTIME_CONFIRMED_READ_FROM"));
            activation.put("upstreamSelectionAuthority",
                    "FIELD_RECEIVER_IDENTITY_AND_WRITE_BEFORE_READ");
            activation.put("anchorRequired", false);
            activation.put("upstreamEventRequired", true);
            activation.put("upstreamEventObserved", true);
            activation.put("replayable", true);
            activation.put("replayMode",
                    "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");

            List<Map<String, Object>> selectedOutputs = new ArrayList<>();
            selectedOutputs.add(outputAction(first.output));
            activation.put("outputs", selectedOutputs);
            activation.put("requestedOutput", object(
                    "portId", first.output.portId,
                    "cell", first.output.cell,
                    "kind", first.output.kind,
                    "selectionAuthority", "CONFIRMED_READ_FROM_EDGE"));

            StaticOutputSlice staticOutputSlice = first.upstream.region
                    .outputSliceFor(first.output.portId);
            StaticOutputSlice outputSlice = staticOutputSlice == null
                    ? null : staticOutputSlice.runtimeRefined(first.upstream);
            if (outputSlice == null) {
                activation.put("requestedOutputSlicePolicy",
                        "CONSERVATIVE_STATIC_REGION_FRONTIER");
                activation.put("requestedOutputSliceComplete", false);
                activation.put("symbolicReady", false);
                activation.put("boundaryReady", false);
                result.warnings.add("upstream output has no static backward "
                        + "slice: " + first.output.portId);
            } else {
                List<Map<String, Object>> selectedInputs = selectActivationRows(
                        base.get("symbolize"), outputSlice.inputPorts, "symbol");
                applySliceDrivenArgumentFieldPaths(selectedInputs, outputSlice);
                List<Map<String, Object>> containerBindings = copyRows(
                        outputSlice.containerElementFieldBindings);
                // Canonicalize a promoted array alias before a container
                // declaration tries to resolve its input port.  Otherwise a
                // declaration that truthfully names the weak projected port
                // fails before that port can be rewritten to the exact leaf.
                applyExactConsumedArrayFieldEvidence(selectedInputs,
                        first.upstream.root, first.upstream.fieldEvents);
                boolean inputAliasesReady =
                        canonicalizeExactRuntimeArrayInputAliases(
                                selectedInputs, outputSlice,
                                containerBindings);
                boolean containerBindingsReady = inputAliasesReady
                        && applyContainerElementFieldBindings(selectedInputs,
                        containerBindings);
                // Container-element declarations can introduce another exact
                // leaf contract for their base/container actions.  Rejoin
                // consumed reads after applying those declarations as well.
                if (containerBindingsReady) {
                    applyExactConsumedArrayFieldEvidence(selectedInputs,
                            first.upstream.root,
                            first.upstream.fieldEvents);
                }
                List<Map<String, Object>> selectedBranches = selectActivationRows(
                        base.get("branches"), outputSlice.sites, "siteId");
                boolean sliceReady = outputSlice.complete
                        && outputSlice.captureBindingsComplete
                        && containerBindingsReady
                        && inputAliasesReady
                        && symbolizeActionsReady(selectedInputs)
                        && branchActionsReady(selectedBranches);
                activation.put("symbolize", selectedInputs);
                activation.put("branches", selectedBranches);
                activation.put("requestedOutputMethods",
                        new ArrayList<>(outputSlice.methods));
                activation.put("requestedOutputSlicePolicy",
                        outputSlice.selection);
                activation.put("requestedOutputSliceRefinementPolicy",
                        "OBSERVED_REGION_CALL_TREE");
                activation.put("requestedOutputSliceRefinementComplete",
                        outputSlice.runtimeRefinementComplete);
                activation.put("requestedOutputSliceComplete",
                        outputSlice.complete);
                activation.put("requestedOutputSlice", outputSlice.toMap());
                activation.put("requestedOutputCapture",
                        copyRows(outputSlice.captureBindings));
                activation.put("requestedOutputCaptureRequired",
                        outputSlice.captureBindingsRequired);
                activation.put("requestedOutputCaptureComplete",
                        outputSlice.captureBindingsComplete);
                if (!containerBindings.isEmpty()) {
                    activation.put("containerElementFieldBindings",
                            containerBindings);
                }
                activation.put("boundaryReady", sliceReady);
                activation.put("symbolicReady", sliceReady);
            }

            List<Map<String, Object>> bindingRows = new ArrayList<>();
            for (UpstreamEdgeBinding binding : group) {
                bindingRows.add(binding.toMap());
            }
            activation.put("edgeBindingCount", bindingRows.size());
            activation.put("edgeBindings", bindingRows);
            activation.put("selectedUpstreamEvent", first.eventMap());

            StaticPort input = first.upstream.region.exactInputFor(
                    first.output.cell);
            if (input != null && (outputSlice == null
                    || outputSlice.inputPorts.contains(input.portId))) {
                List<Map<String, Object>> heapBindings = new ArrayList<>();
                heapBindings.add(object(
                        "inputPort", input.portId,
                        "outputPort", first.output.portId,
                        "cell", first.output.cell,
                        "bindingAuthority",
                        "STATIC_CELL_IDENTITY_PLUS_RUNTIME_READ_FROM"));
                activation.put("heapStateBindings", heapBindings);
            }
            result.activations.add(activation);
        }
        return activationIndex;
    }

    /**
     * Coalesces a promoted nested-field input with the exact consumed array
     * leaf that denotes the same live Java field in this region instance.
     *
     * <p>The custom VM assigns one engine array id to one live Java array.
     * Consequently, symbolizing the same array through two region ports does
     * not create two independent inputs: it creates an alias that the
     * importer intentionally rejects.  Canonicalization must therefore happen
     * before replay, while the discovery execution's exact receiver/value
     * identities and the planner's consumed-leaf declaration are still
     * available.  A field name or Java type alone is never sufficient.</p>
     */
    private static boolean canonicalizeExactRuntimeArrayInputAliases(
            List<Map<String, Object>> selectedInputs,
            StaticOutputSlice outputSlice,
            List<Map<String, Object>> containerBindings) {
        Map<String, List<Map<String, Object>>> actionsByPort =
                new LinkedHashMap<>();
        for (Map<String, Object> action : values(selectedInputs)) {
            add(actionsByPort, string(action.get("symbol")), action);
        }

        Map<String, String> canonicalByAlias = new LinkedHashMap<>();
        List<Map<String, Object>> proofs = new ArrayList<>();
        List<String> issues = new ArrayList<>();
        for (Map<String, Object> aliasAction : values(selectedInputs)) {
            String aliasPort = string(aliasAction.get("symbol"));
            String aliasCell = string(aliasAction.get("cell"));
            List<String> path = dependencyFieldPath(aliasCell);
            FieldCell baseField = fieldCell(aliasCell);
            if (aliasPort.isEmpty() || path.size() != 2
                    || !baseField.declaredSignature
                    || !path.get(0).equals(baseField.name)) {
                continue;
            }

            List<Map<String, Object>> staticCandidates = new ArrayList<>();
            for (Map<String, Object> candidate : values(selectedInputs)) {
                if (candidate == aliasAction) continue;
                FieldCell leaf = exactConsumedArrayLeaf(candidate);
                if (leaf.declaredSignature
                        && baseField.type.equals(leaf.owner)
                        && path.get(1).equals(leaf.name)) {
                    staticCandidates.add(candidate);
                }
            }
            if (staticCandidates.isEmpty()) {
                // This is an ordinary nested scalar/object projection, not a
                // duplicate representation of a selected exact array leaf.
                continue;
            }

            String authorityIssue = projectedAliasAuthorityIssue(
                    outputSlice, aliasPort);
            if (!authorityIssue.isEmpty()) {
                issues.add(aliasPort + ":" + authorityIssue);
                continue;
            }
            if (staticCandidates.size() != 1) {
                issues.add(aliasPort
                        + ":EXACT_ARRAY_ALIAS_CANONICAL_PORT_NOT_UNIQUE:"
                        + staticCandidates.size());
                continue;
            }

            Map<String, Object> canonicalAction = staticCandidates.get(0);
            String canonicalPort = string(canonicalAction.get("symbol"));
            FieldCell leaf = exactConsumedArrayLeaf(canonicalAction);
            String runtimeIssue = hasExactCellIdentityBinding(outputSlice,
                    canonicalPort) ? exactRuntimeArrayAliasIssue(aliasAction,
                    canonicalAction, baseField, leaf)
                    : "CANONICAL_ARRAY_PORT_LACKS_EXACT_CELL_IDENTITY";
            if (!runtimeIssue.isEmpty()) {
                issues.add(aliasPort + ":" + runtimeIssue);
                continue;
            }
            String old = canonicalByAlias.put(aliasPort, canonicalPort);
            if (old != null && !old.equals(canonicalPort)) {
                issues.add(aliasPort
                        + ":ARRAY_ALIAS_CANONICALIZATION_NOT_FUNCTIONAL");
                continue;
            }

            int baseReceiver = number(aliasAction,
                    "fieldReceiverObjectId");
            int intermediateOwner = number(aliasAction, "valueObjectId");
            Map<String, Object> proof = object(
                    "schemaVersion", 1,
                    "kind", "CANONICAL_ARRAY_INPUT_ALIAS",
                    "aliasInputPort", aliasPort,
                    "canonicalInputPort", canonicalPort,
                    "aliasInputCell", aliasCell,
                    "canonicalInputCell", string(canonicalAction.get(
                            "cell")),
                    "fieldPath", new ArrayList<>(path),
                    "baseFieldSignature", baseField.signature(),
                    "leafFieldSignature", leaf.signature(),
                    "baseReceiverObjectId", baseReceiver,
                    "intermediateOwnerObjectId", intermediateOwner,
                    "canonicalLeafReceiverObjectId", number(
                            canonicalAction, "fieldReceiverObjectId"),
                    "canonicalArrayValueObjectId", number(
                            canonicalAction, "valueObjectId"),
                    "consumedFieldSiteId", string(canonicalAction.get(
                            "consumedFieldSiteId")),
                    "staticAuthority",
                    "PROJECTED_FRONTIER_TO_EXACT_CONSUMED_ARRAY_LEAF_V1",
                    "runtimeIdentityAuthority",
                    "BASE_FIELD_VALUE_EQUALS_EXACT_LEAF_RECEIVER_V1",
                    "aliasBindingCount", aliasBindingCount(outputSlice,
                            aliasPort),
                    "aliasBindingAuthorities", aliasBindingValues(
                            outputSlice, aliasPort, "bindingAuthority"),
                    "aliasDependencyCells", aliasBindingValues(outputSlice,
                            aliasPort, "dependencyCell"),
                    "complete", true);
            proofs.add(proof);
        }

        if (!issues.isEmpty()) {
            outputSlice.inputAliasCanonicalizationIssues.addAll(issues);
            outputSlice.runtimeRefinementComplete = false;
            outputSlice.complete = false;
            return false;
        }
        if (canonicalByAlias.isEmpty()) {
            return true;
        }

        // The canonical exact binding already exists.  Promoted/projected
        // rows are proof of the alias, not additional definitions of the
        // canonical input; retaining them under the canonical port would
        // manufacture duplicate input bindings.
        List<Map<String, Object>> retainedBindings = new ArrayList<>();
        for (Map<String, Object> binding : outputSlice.inputBindings) {
            if (!canonicalByAlias.containsKey(string(binding.get(
                    "inputPort")))) {
                retainedBindings.add(binding);
            }
        }
        outputSlice.inputBindings.clear();
        outputSlice.inputBindings.addAll(retainedBindings);
        for (Map<String, Object> declaration : values(containerBindings)) {
            rewriteContainerAlias(declaration, canonicalByAlias,
                    actionsByPort);
        }
        for (Map<String, Object> declaration
                : outputSlice.containerElementFieldBindings) {
            rewriteContainerAlias(declaration, canonicalByAlias,
                    actionsByPort);
        }
        outputSlice.inputPorts.removeAll(canonicalByAlias.keySet());
        outputSlice.inputAliasCanonicalizations.addAll(proofs);
        selectedInputs.removeIf(action -> canonicalByAlias.containsKey(
                string(action.get("symbol"))));
        return true;
    }

    private static FieldCell exactConsumedArrayLeaf(
            Map<String, Object> action) {
        if (!Boolean.TRUE.equals(action.get("observed"))
                || !Boolean.TRUE.equals(action.get(
                "consumedFieldBindingComplete"))) {
            return FieldCell.unresolved();
        }
        String signature = firstNonBlank(
                string(action.get("leafFieldSignature")),
                string(action.get("accessFieldSignature")),
                string(action.get("field")),
                string(action.get("cell")));
        FieldCell leaf = fieldCell(signature);
        List<String> path = stringList(action.get("fieldPath"));
        String javaType = string(action.get("javaType"));
        return leaf.declaredSignature && isArrayJavaType(leaf.type)
                && sameArrayJavaType(leaf.type, javaType)
                && path.size() == 1 && leaf.name.equals(path.get(0))
                ? leaf : FieldCell.unresolved();
    }

    private static String projectedAliasAuthorityIssue(
            StaticOutputSlice slice, String aliasPort) {
        boolean found = false;
        for (Map<String, Object> binding : slice.inputBindings) {
            if (!aliasPort.equals(string(binding.get("inputPort")))) {
                continue;
            }
            found = true;
            String authority = string(binding.get("bindingAuthority"));
            if (!("OUTPUT_SLICE_FRONTIER_PROMOTION".equals(authority)
                    || "UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN".equals(
                    authority))) {
                return "PROJECTED_ARRAY_ALIAS_AUTHORITY_INVALID:"
                        + authority;
            }
        }
        return found ? "" : "PROJECTED_ARRAY_ALIAS_BINDING_MISSING";
    }

    private static String exactRuntimeArrayAliasIssue(
            Map<String, Object> alias, Map<String, Object> canonical,
            FieldCell baseField, FieldCell leaf) {
        FieldCell observedBase = fieldCell(string(alias.get(
                "accessFieldSignature")));
        int baseReceiver = number(alias, "fieldReceiverObjectId");
        int intermediateOwner = number(alias, "valueObjectId");
        int leafReceiver = number(canonical, "fieldReceiverObjectId");
        int arrayValue = number(canonical, "valueObjectId");
        if (!Boolean.TRUE.equals(alias.get("observed"))
                || !baseField.signature().equals(observedBase.signature())) {
            return "PROJECTED_ARRAY_BASE_FIELD_OBSERVATION_NOT_EXACT";
        }
        if (!baseField.type.equals(leaf.owner)
                || !isArrayJavaType(leaf.type)) {
            return "PROJECTED_ARRAY_LEAF_DECLARATION_MISMATCH";
        }
        if (baseReceiver == 0 || intermediateOwner == 0
                || leafReceiver == 0 || arrayValue == 0) {
            return "PROJECTED_ARRAY_RUNTIME_IDENTITY_MISSING";
        }
        if (intermediateOwner != leafReceiver) {
            return "PROJECTED_ARRAY_RUNTIME_FIELD_CHAIN_MISMATCH";
        }
        return "";
    }

    private static boolean hasExactCellIdentityBinding(
            StaticOutputSlice slice, String canonicalPort) {
        int count = 0;
        for (Map<String, Object> binding : slice.inputBindings) {
            if (!canonicalPort.equals(string(binding.get("inputPort")))) {
                continue;
            }
            if (!"EXACT_CELL_IDENTITY".equals(string(binding.get(
                    "bindingAuthority")))) {
                return false;
            }
            count++;
        }
        return count == 1;
    }

    private static int aliasBindingCount(StaticOutputSlice slice,
                                         String aliasPort) {
        int count = 0;
        for (Map<String, Object> binding : slice.inputBindings) {
            if (aliasPort.equals(string(binding.get("inputPort")))) {
                count++;
            }
        }
        return count;
    }

    private static List<String> aliasBindingValues(StaticOutputSlice slice,
                                                   String aliasPort,
                                                   String field) {
        List<String> result = new ArrayList<>();
        for (Map<String, Object> binding : slice.inputBindings) {
            if (aliasPort.equals(string(binding.get("inputPort")))) {
                result.add(string(binding.get(field)));
            }
        }
        return result;
    }

    private static void rewriteContainerAlias(
            Map<String, Object> declaration,
            Map<String, String> canonicalByAlias,
            Map<String, List<Map<String, Object>>> actionsByPort) {
        String alias = string(declaration.get("containerInputPort"));
        String canonical = canonicalByAlias.get(alias);
        if (canonical == null) return;
        declaration.put("containerInputPort", canonical);
        List<Map<String, Object>> actions = actionsByPort.get(canonical);
        if (actions != null && actions.size() == 1) {
            declaration.put("containerInputCell", string(actions.get(0).get(
                    "cell")));
        }
        declaration.put("containerInputAliasSourcePort", alias);
        declaration.put("containerInputAliasAuthority",
                "EXACT_RUNTIME_FIELD_CHAIN_TO_CANONICAL_LEAF_INPUT_V1");
    }

    private static int number(Map<String, Object> row, String field) {
        Object value = row == null ? null : row.get(field);
        return value instanceof Number ? ((Number) value).intValue() : 0;
    }

    /**
     * Lifts an exact downstream array-element field demand back through a
     * producer's Map view/toArray projection.  This is deliberately a second
     * pass: every confirmed read-from activation must exist before we decide
     * which downstream output slice is actually selected for the same region
     * instance.  A region-wide static field family is not sufficient.
     *
     * <p>The emitted declaration is the static half of the recursive runtime
     * evidence contract.  The runtime snapshots the finite backing-map view
     * while the producer input is materialized, symbolizes the demanded
     * fields, and later verifies the real output array index-by-index by
     * object identity.  Import remains independently fail-closed until those
     * same-execution observations are complete.</p>
     */
    private static int refineMapValueElementProjectionActivations(
            Result result) {
        Map<String, List<Map<String, Object>>> selectedByInstance =
                new LinkedHashMap<>();
        for (Map<String, Object> activation : result.activations) {
            if (!"OUTPUT_CLOSURE".equals(captureGoalKind(activation))
                    || !Boolean.TRUE.equals(activation.get(
                    "requestedOutputSliceComplete"))) {
                continue;
            }
            String instance = string(activation.get("regionInstanceId"));
            if (!instance.isEmpty()) {
                add(selectedByInstance, instance, activation);
            }
        }

        int emitted = 0;
        for (Map<String, Object> activation : result.activations) {
            Map<String, Object> producerSlice = mapValue(
                    activation.get("requestedOutputSlice"));
            List<Map<String, Object>> edgeBindings = mapRows(
                    activation.get("edgeBindings"));
            if (producerSlice == null || edgeBindings.isEmpty()) {
                continue;
            }

            List<DownstreamContainerDemand> demands = new ArrayList<>();
            Set<String> demandIds = new LinkedHashSet<>();
            List<String> issues = new ArrayList<>();
            for (Map<String, Object> edge : edgeBindings) {
                String downstreamInstance = string(edge.get(
                        "toRegionInstance"));
                String downstreamInput = string(edge.get("toInputPort"));
                List<Map<String, Object>> selected = values(
                        selectedByInstance.get(downstreamInstance));
                for (Map<String, Object> downstream : selected) {
                    Map<String, Object> downstreamSlice = mapValue(
                            downstream.get("requestedOutputSlice"));
                    if (downstreamSlice == null) {
                        continue;
                    }
                    for (Map<String, Object> declaration : mapRows(
                            downstreamSlice.get(
                                    "containerElementFieldBindings"))) {
                        if (!downstreamInput.equals(string(declaration.get(
                                "containerInputPort")))) {
                            continue;
                        }
                        DownstreamContainerDemand demand =
                                DownstreamContainerDemand.from(edge,
                                        downstream, declaration);
                        if (!demand.complete()) {
                            issues.add("INCOMPLETE_DOWNSTREAM_CONTAINER_DEMAND:"
                                    + firstNonBlank(demand.bindingId,
                                    downstreamInput));
                            continue;
                        }
                        if (demandIds.add(demand.identity())) {
                            demands.add(demand);
                        }
                    }
                }
            }
            if (demands.isEmpty() && issues.isEmpty()) {
                continue;
            }

            MapValueProjectionProof proof =
                    MapValueProjectionProof.from(producerSlice);
            if (!proof.complete) {
                issues.add(firstNonBlank(proof.issue,
                        "INCOMPLETE_MAP_VIEW_TO_ARRAY_PROJECTION_PROOF"));
            }

            List<Map<String, Object>> declarations = new ArrayList<>();
            if (issues.isEmpty()) {
                for (DownstreamContainerDemand demand : demands) {
                    Map<String, Object> declaration = object(
                            "schemaVersion", 1,
                            "kind",
                            "MAP_VALUE_TO_OUTPUT_ARRAY_ELEMENT_FIELD",
                            "bindingId", "MAP_OUTPUT_ELEMENT:"
                                    + demand.edgeId + ":" + demand.bindingId,
                            "mapInputPort", proof.mapInputPort,
                            "mapInputCell", proof.mapInputCell,
                            "outputPort", string(activationOutputPort(
                                    activation)),
                            "outputCell", string(activationOutputCell(
                                    activation)),
                            "outputFieldPath", proof.outputFieldPath,
                            "outputValidationMode",
                            Boolean.TRUE.equals(activation.get(
                                    "requestedOutputCaptureRequired"))
                                    ? "EXACT_REQUESTED_OUTPUT_CAPTURE"
                                    : "ROOT_RETURN_PROJECTED_FIELD",
                            "mapProjectionOperation", proof.operation,
                            "mapViewSiteId", proof.mapViewSiteId,
                            "snapshotSiteId", proof.snapshotSiteId,
                            "downstreamRegion",
                            string(demand.downstreamActivation.get(
                                    "regionId")),
                            "downstreamRegionInstance",
                            string(demand.downstreamActivation.get(
                                    "regionInstanceId")),
                            "downstreamInputPort",
                            demand.downstreamInputPort,
                            "downstreamBaseInputSymbol",
                            demand.baseInputSymbol,
                            "downstreamContainerBindingId",
                            demand.bindingId,
                            "declaredFieldSignature",
                            demand.declaredFieldSignature,
                            "declaredFieldOwnerClass",
                            demand.declaredFieldOwnerClass,
                            "declaredFieldType",
                            demand.declaredFieldType,
                            "declaredFieldName",
                            demand.declaredFieldName,
                            "fieldPath", demand.fieldPath,
                            "selectorAuthority",
                            "CURRENT_EXECUTION_ENTRY_SNAPSHOT_THEN_EXACT_"
                                    + "OUTPUT_INDEX_IDENTITY",
                            "identityValidationRequired", true,
                            "identityValidationTiming",
                            "ENTRY_SNAPSHOT_AND_OUTPUT_CAPTURE_SAME_EXECUTION",
                            "crossExecutionOrdinalAuthority", "NONE",
                            "readFromEdgeId", demand.edgeId,
                            "projectionProofCausalEdgeIds",
                            proof.causalEdgeIds,
                            "projectionProofAuthority",
                            "STATIC_EXACT_MAP_VIEW_TO_ARRAY_CHAIN_PLUS_"
                                    + "RUNTIME_SELECTED_DOWNSTREAM_ELEMENT_DEMAND",
                            "recursiveElementProjectionComposable", true,
                            "complete", true);
                    declarations.add(declaration);
                }
            }

            activation.put("mapValueElementFieldProjections",
                    declarations);
            activation.put("mapValueElementProjectionCaptureReady",
                    issues.isEmpty() && !declarations.isEmpty());
            activation.put("mapValueElementProjectionIssues", issues);
            boolean composable = issues.isEmpty()
                    && !declarations.isEmpty();
            activation.put("recursiveElementProjectionComposable",
                    composable);
            activation.remove("recursiveElementProjectionCompositionGap");
            // Preserve all pre-existing readiness decisions when the static
            // declaration is complete. Runtime identity evidence is checked
            // later by the importer. A static proof/declaration failure still
            // closes this activation before scheduling.
            if (!composable) {
                activation.put("symbolicReady", false);
                activation.put("boundaryReady", false);
            }
            if (!issues.isEmpty()) {
                result.warnings.add("map value/output element projection "
                        + "failed closed for " + string(activation.get(
                        "activationId")) + ": " + issues);
            }
            emitted += declarations.size();
        }
        return emitted;
    }

    static int refineMapValueElementProjectionActivationsForTests(
            Result result) {
        return refineMapValueElementProjectionActivations(result);
    }

    private static String captureGoalKind(Map<String, Object> activation) {
        Map<String, Object> goal = mapValue(activation.get("captureGoal"));
        return goal == null ? "" : string(goal.get("kind"));
    }

    private static Object activationOutputPort(
            Map<String, Object> activation) {
        Map<String, Object> requested = mapValue(
                activation.get("requestedOutput"));
        return requested == null ? "" : requested.get("portId");
    }

    private static Object activationOutputCell(
            Map<String, Object> activation) {
        Map<String, Object> requested = mapValue(
                activation.get("requestedOutput"));
        return requested == null ? "" : requested.get("cell");
    }

    private static List<Map<String, Object>> selectActivationRows(
            Object value, Set<String> selected, String key) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (!(value instanceof Collection<?>)) {
            return result;
        }
        for (Object item : (Collection<?>) value) {
            if (!(item instanceof Map<?, ?>)) {
                continue;
            }
            @SuppressWarnings("unchecked")
            Map<String, Object> row = (Map<String, Object>) item;
            if (selected.contains(string(row.get(key)))) {
                result.add(new LinkedHashMap<>(row));
            }
        }
        return result;
    }

    private static List<Map<String, Object>> copyRows(
            Collection<Map<String, Object>> rows) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (rows != null) {
            for (Map<String, Object> row : rows) {
                result.add(new LinkedHashMap<>(row));
            }
        }
        return result;
    }

    /**
     * Binds runtime actions to the exact static declaration endpoints.  The
     * declaration itself has already survived observed-method and retained-
     * port refinement; this final check prevents an activation with duplicate
     * or mismatched actions from falling back to field-name materialization.
     */
    private static boolean applyContainerElementFieldBindings(
            List<Map<String, Object>> actions,
            List<Map<String, Object>> declarations) {
        Set<String> bindingIds = new LinkedHashSet<>();
        for (Map<String, Object> declaration : declarations) {
            String bindingId = string(declaration.get("bindingId"));
            String base = string(declaration.get("baseInputSymbol"));
            String container = string(declaration.get(
                    "containerInputPort"));
            String fieldSignature = string(declaration.get(
                    "declaredFieldSignature"));
            String containerCell = string(declaration.get(
                    "containerInputCell"));
            Map<String, Object> baseAction = uniqueAction(actions, base);
            Map<String, Object> containerAction = uniqueAction(actions,
                    container);
            if (bindingId.isEmpty() || !bindingIds.add(bindingId)
                    || baseAction == null || containerAction == null
                    || baseAction == containerAction
                    || !fieldSignature.equals(string(baseAction.get(
                    "cell")))
                    || !containerCell.equals(string(containerAction.get(
                    "cell")))) {
                return false;
            }
            String observedBaseField = string(baseAction.get("field"));
            String observedContainerField = string(containerAction.get(
                    "field"));
            if (!observedBaseField.isEmpty()
                    && !fieldSignature.equals(observedBaseField)
                    || !observedContainerField.isEmpty()
                    && !containerCell.equals(observedContainerField)) {
                return false;
            }
            FieldCell field = fieldCell(fieldSignature);
            FieldCell containerField = fieldCell(containerCell);
            if (!field.declaredSignature
                    || !containerField.declaredSignature) {
                return false;
            }
            @SuppressWarnings("unchecked")
            List<String> path = declaration.get("fieldPath")
                    instanceof Collection<?> ? new ArrayList<>((Collection<
                    String>) declaration.get("fieldPath"))
                    : Collections.<String>emptyList();
            if (path.size() != 1 || !field.name.equals(path.get(0))) {
                return false;
            }
            baseAction.put("field", fieldSignature);
            baseAction.put("fieldPath", path);
            baseAction.put("bindingMode", "FIELD_ACCESS");
            baseAction.put("accessOwnerClass", field.owner);
            baseAction.put("accessField", field.name);
            baseAction.put("accessFieldType", field.type);
            baseAction.put("javaType", field.type);
            baseAction.put("accessFieldSignature", field.signature());
            baseAction.put("accessFieldAuthority",
                    "STATIC_EXACT_CONTAINER_ELEMENT_FIELD_DECLARATION");

            containerAction.put("field", containerCell);
            containerAction.put("fieldPath", Collections.singletonList(
                    containerField.name));
            containerAction.put("bindingMode", "FIELD_ACCESS");
            containerAction.put("accessOwnerClass", containerField.owner);
            containerAction.put("accessField", containerField.name);
            containerAction.put("accessFieldType", containerField.type);
            containerAction.put("javaType", containerField.type);
            containerAction.put("accessFieldSignature",
                    containerField.signature());
            containerAction.put("accessFieldAuthority",
                    "STATIC_EXACT_CONTAINER_INPUT_FIELD_DECLARATION");
        }
        return true;
    }

    private static Map<String, Object> uniqueAction(
            List<Map<String, Object>> actions, String symbol) {
        Map<String, Object> match = null;
        for (Map<String, Object> action : actions) {
            if (!symbol.equals(string(action.get("symbol")))) {
                continue;
            }
            if (match != null) {
                return null;
            }
            match = action;
        }
        return match;
    }

    /**
     * Refines a root-argument carrier using only the dependency paths proven
     * by the requested output slice.  The static planner may bind several
     * nested field cells to one unambiguous argument port; recursively
     * symbolizing that entire argument would include unrelated object state.
     *
     * <p>Only deepest paths are retained.  If {@code payload} and
     * {@code payload.entries} are both dependencies, materializing the former
     * as an object reference is redundant and broader than materializing the
     * latter on its concrete leaf owner.</p>
     */
    private static void applySliceDrivenArgumentFieldPaths(
            List<Map<String, Object>> actions, StaticOutputSlice slice) {
        Map<String, List<List<String>>> pathsByPort = new LinkedHashMap<>();
        Map<String, List<String>> cellsByPort = new LinkedHashMap<>();
        Map<String, Map<String, String>> leafDeclarationsByPort =
                new LinkedHashMap<>();
        Set<String> carrierPorts = new LinkedHashSet<>();
        for (Map<String, Object> binding : slice.inputBindings) {
            if (!"UNIQUE_ROOT_ARGUMENT_CARRIER".equals(
                    string(binding.get("bindingAuthority")))) {
                continue;
            }
            String port = string(binding.get("inputPort"));
            if (port.isEmpty()) {
                continue;
            }
            carrierPorts.add(port);
            String cell = string(binding.get("dependencyCell"));
            add(cellsByPort, port, cell);
            List<String> path = dependencyFieldPath(cell);
            List<String> explicitPath = new ArrayList<>(stringSet(
                    binding.get("fieldPath")));
            if (!explicitPath.isEmpty()) {
                path = explicitPath;
            }
            if (!path.isEmpty()) {
                add(pathsByPort, port, path);
                String explicitLeaf = firstNonBlank(string(binding.get(
                        "leafFieldSignature")), string(binding.get(
                        "declaredFieldSignature")));
                FieldCell declaredLeaf = fieldCell(explicitLeaf);
                if (!declaredLeaf.declaredSignature) {
                    FieldCell dependencyField = fieldCell(cell);
                    if (dependencyField.declaredSignature
                            && dependencyField.name.equals(path.get(
                            path.size() - 1))) {
                        explicitLeaf = dependencyField.signature();
                        declaredLeaf = dependencyField;
                    }
                }
                if (declaredLeaf.declaredSignature
                        && declaredLeaf.name.equals(path.get(
                        path.size() - 1))) {
                    Map<String, String> declarations =
                            leafDeclarationsByPort.computeIfAbsent(port,
                                    ignored -> new LinkedHashMap<>());
                    declarations.put(joinPath(path), explicitLeaf);
                }
            }
        }

        for (Map<String, Object> action : actions) {
            String symbol = string(action.get("symbol"));
            if (!carrierPorts.contains(symbol)
                    || !"ROOT_ARGUMENT".equals(
                    string(action.get("sourceKind")))) {
                continue;
            }
            List<List<String>> paths = deepestFieldPaths(pathsByPort.get(symbol));
            action.put("location", "ARGUMENT_FIELD_PATH");
            action.remove("fields");
            action.put("fieldPaths", paths);
            action.put("fieldPathSourceCells", new ArrayList<>(
                    values(cellsByPort.get(symbol))));
            action.put("fieldPathBindingAuthority",
                    "STATIC_OUTPUT_SLICE_UNIQUE_ROOT_ARGUMENT_CARRIER");
            action.put("fieldPathSelectionComplete", !paths.isEmpty());
            action.put("materializationMode", "SELECTIVE_FIELD_PATHS");
            Map<String, String> declared = leafDeclarationsByPort.get(symbol);
            if (paths.size() == 1 && declared != null) {
                String signature = declared.get(joinPath(paths.get(0)));
                FieldCell leaf = fieldCell(signature);
                if (leaf.declaredSignature) {
                    List<Map<String, Object>> rows = new ArrayList<>();
                    rows.add(object("fieldPath", paths.get(0),
                            "fieldSignature", signature,
                            "declaredFieldOwnerClass", leaf.owner,
                            "declaredFieldType", leaf.type,
                            "complete", true));
                    action.put("fieldPathLeafDeclarations", rows);
                    action.put("javaType", leaf.type);
                    action.put("javaTypeAuthority",
                            "STATIC_EXACT_SLICE_LEAF_FIELD_DECLARATION");
                }
            }
        }
    }

    private static List<String> dependencyFieldPath(String cell) {
        List<String> result = new ArrayList<>();
        Matcher signature = FIELD_SIGNATURE.matcher(safe(cell));
        if (!signature.find()) {
            return result;
        }
        result.add(signature.group(3).trim());
        Matcher projection = FIELD_PROJECTION.matcher(
                safe(cell).substring(signature.end()));
        while (projection.find()) {
            String field = projection.group(1).trim();
            if (!field.isEmpty()) {
                result.add(field);
            }
        }
        return result;
    }

    private static List<List<String>> deepestFieldPaths(
            List<List<String>> candidates) {
        List<List<String>> unique = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        for (List<String> candidate : values(candidates)) {
            if (candidate == null || candidate.isEmpty()) {
                continue;
            }
            String identity = joinPath(candidate);
            if (seen.add(identity)) {
                unique.add(new ArrayList<>(candidate));
            }
        }

        List<List<String>> result = new ArrayList<>();
        for (List<String> candidate : unique) {
            boolean prefix = false;
            for (List<String> other : unique) {
                if (other.size() > candidate.size()
                        && pathStartsWith(other, candidate)) {
                    prefix = true;
                    break;
                }
            }
            if (!prefix) {
                result.add(candidate);
            }
        }
        return result;
    }

    private static boolean pathStartsWith(List<String> path,
                                          List<String> prefix) {
        if (path.size() < prefix.size()) {
            return false;
        }
        for (int index = 0; index < prefix.size(); index++) {
            if (!safe(path.get(index)).equals(safe(prefix.get(index)))) {
                return false;
            }
        }
        return true;
    }

    private static String joinPath(List<String> path) {
        StringBuilder result = new StringBuilder();
        for (String segment : path) {
            if (result.length() > 0) {
                result.append('\u0000');
            }
            result.append(safe(segment));
        }
        return result.toString();
    }

    private static boolean symbolizeActionsReady(
            List<Map<String, Object>> actions) {
        for (Map<String, Object> action : actions) {
            if (!Boolean.TRUE.equals(action.get("observed"))
                    && (!Boolean.TRUE.equals(action.get("deferredResolution"))
                    || !deferredSymbolizeActionReady(action))) {
                return false;
            }
            if ("ARGUMENT_FIELD_PATH".equals(action.get("location"))
                    && !Boolean.TRUE.equals(
                    action.get("fieldPathSelectionComplete"))) {
                return false;
            }
            ArrayFieldLeaf leaf = ArrayFieldLeaf.from(action);
            if (leaf.fieldBackedArray && (!leaf.complete()
                    || !Boolean.TRUE.equals(action.get(
                    "consumedFieldBindingComplete")))) {
                return false;
            }
        }
        return true;
    }

    private static boolean deferredSymbolizeActionReady(
            Map<String, Object> action) {
        String location = string(action.get("location"));
        if ("ENVIRONMENT_MODEL".equals(location)) {
            return "ENVIRONMENT".equals(string(action.get("sourceKind")))
                    && VM_CURRENT_TIME_MILLIS_RETURN.equals(
                    string(action.get("cell")))
                    && VM_INTRINSIC_DEFERRED_AUTHORITY.equals(
                    string(action.get("deferredResolutionAuthority")));
        }
        if ("CALL_RETURN".equals(location)) {
            return "OPAQUE_CALL".equals(string(action.get("sourceKind")))
                    && CALL_RETURN_DEFERRED_AUTHORITY.equals(
                    string(action.get("deferredResolutionAuthority")));
        }
        return true;
    }

    private static boolean branchActionsReady(
            List<Map<String, Object>> actions) {
        for (Map<String, Object> action : actions) {
            if (!Boolean.TRUE.equals(action.get("observed"))) {
                return false;
            }
        }
        return true;
    }

    private static boolean rpcPortMapping(StaticRegionEdge edge) {
        return edge != null && ("RPC_RETURN".equals(edge.kind)
                || "RPC_ARGUMENT".equals(edge.kind));
    }

    /**
     * Correlates each complete downstream endpoint with one source region
     * instance.  A digest match alone is not enough when several concurrent
     * handshakes carry the same value.  HDFS SASL username transfer first
     * selects the most recently entered source instance whose root precedes
     * the downstream root, then selects the nearest matching source endpoint
     * in that instance.  Other transfers retain nearest-endpoint correlation.
     * Endpoint sequence remains the authority for transfer order; root
     * sequence only disambiguates the SASL connection/activation lifetime.
     */
    private static Map<String, List<FingerprintMatch>>
    nearestEndpointFingerprintMatches(
            StaticRegionEdge edge, List<InstanceEvidence> sources,
            List<InstanceEvidence> targets) {
        Map<String, List<FingerprintMatch>> result = new LinkedHashMap<>();
        if ("SHARED_STATE".equals(edge.kind)) {
            return result;
        }
        boolean correlateByRootLifetime =
                saslUsernameRootLifetimeCorrelation(edge);
        Map<String, List<EndpointFingerprint>> sourceFingerprints =
                new LinkedHashMap<>();
        for (InstanceEvidence source : sources) {
            sourceFingerprints.put(source.instanceId,
                    endpointFingerprints(edge, source, true));
        }

        for (InstanceEvidence targetInstance : targets) {
            List<EndpointFingerprint> targetFingerprints =
                    endpointFingerprints(edge, targetInstance, false);
            for (EndpointFingerprint target : targetFingerprints) {
                InstanceEvidence bestInstance = null;
                FingerprintMatch bestMatch = null;
                for (InstanceEvidence sourceInstance : sources) {
                    if (!sourceInstance.root.test.equals(
                            targetInstance.root.test)
                            || (correlateByRootLifetime
                            && sourceInstance.root.seq
                            > targetInstance.root.seq)
                            || !endpointPairObserved(edge, sourceInstance,
                            targetInstance)) {
                        continue;
                    }
                    FingerprintMatch candidate =
                            nearestMatchingSourceEndpoint(edge,
                                    values(sourceFingerprints.get(
                                            sourceInstance.instanceId)),
                                    target);
                    if (candidate == null) {
                        continue;
                    }
                    if (betterEndpointCorrelation(correlateByRootLifetime,
                            sourceInstance, candidate, bestInstance,
                            bestMatch)) {
                        bestInstance = sourceInstance;
                        bestMatch = candidate;
                    }
                }
                if (bestInstance != null) {
                    add(result, endpointInstancePairKey(bestInstance,
                            targetInstance), bestMatch);
                }
            }
        }
        return result;
    }

    private static boolean betterEndpointCorrelation(
            boolean correlateByRootLifetime,
            InstanceEvidence candidateInstance,
            FingerprintMatch candidate,
            InstanceEvidence currentInstance,
            FingerprintMatch current) {
        if (currentInstance == null) {
            return true;
        }
        if (correlateByRootLifetime
                && candidateInstance.root.seq != currentInstance.root.seq) {
            return candidateInstance.root.seq > currentInstance.root.seq;
        }
        if (candidate.distance() != current.distance()) {
            return candidate.distance() < current.distance();
        }
        if (candidate.from.seq != current.from.seq) {
            return candidate.from.seq > current.from.seq;
        }
        return candidateInstance.instanceId.compareTo(
                currentInstance.instanceId) < 0;
    }

    private static boolean saslUsernameRootLifetimeCorrelation(
            StaticRegionEdge edge) {
        return edge != null
                && "hdfs_sasl_username".equals(edge.mappingKind);
    }

    private static String endpointCorrelationAuthority(
            StaticRegionEdge edge) {
        return saslUsernameRootLifetimeCorrelation(edge)
                ? "NEAREST_PRECEDING_SOURCE_ROOT_THEN_ENDPOINT"
                : "NEAREST_PRECEDING_MATCHING_SOURCE_ENDPOINT";
    }

    private static FingerprintMatch nearestMatchingSourceEndpoint(
            StaticRegionEdge edge, List<EndpointFingerprint> sources,
            EndpointFingerprint target) {
        FingerprintMatch best = null;
        for (EndpointFingerprint source : sources) {
            if (!source.digest.equals(target.digest)
                    || (edge.requiresOrder && source.seq > target.seq)) {
                continue;
            }
            FingerprintMatch candidate = new FingerprintMatch(source, target);
            if (best == null || candidate.distance() < best.distance()
                    || (candidate.distance() == best.distance()
                    && source.seq > best.from.seq)) {
                best = candidate;
            }
        }
        return best;
    }

    private static boolean endpointPairObserved(
            StaticRegionEdge edge, InstanceEvidence source,
            InstanceEvidence target) {
        if ("SHARED_STATE".equals(edge.kind)) {
            return true;
        }
        boolean siteObserved = observesSite(target.runtimeEvents, edge.siteId)
                || (rpcPortMapping(edge)
                && observesMappedRpcInvocation(target.runtimeEvents,
                edge.fromPort, edge.toPort));
        return observesPortMethod(source, edge.fromPort)
                && (observesPortMethod(target, edge.toPort) || siteObserved);
    }

    private static String endpointInstancePairKey(
            InstanceEvidence source, InstanceEvidence target) {
        return source.instanceId + '\u0000' + target.instanceId;
    }

    private static List<EndpointFingerprint> endpointFingerprints(
            StaticRegionEdge edge, InstanceEvidence evidence,
            boolean source) {
        String port = source ? edge.fromPort : edge.toPort;
        String method = methodInCell(port);
        int parameter = parameterIndex(port);
        boolean methodReturn = port.contains(">.return");
        List<EndpointFingerprint> result = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        for (RuntimeEvent event : evidence.runtimeEvents) {
            if (!event.valueFingerprintComplete
                    || event.valueFingerprint.isEmpty()) continue;
            String authority = "";
            if (parameter >= 0 && "METHOD_ARGUMENT".equals(event.kind)
                    && method.equals(event.method)
                    && parameter == event.argumentIndex) {
                authority = "METHOD_ARGUMENT";
            } else if (methodReturn
                    && "METHOD_EXIT_NORMAL".equals(event.kind)
                    && method.equals(event.method)) {
                authority = "METHOD_RETURN";
            } else if (!source
                    && "hdfs_sasl_username".equals(edge.mappingKind)
                    && "CALL_SITE_RETURN".equals(event.kind)
                    && method.equals(event.method)
                    && nameCallbackDefaultNameGetter(
                    event.declaredCallee)) {
                authority = "HDFS_SASL_NAME_CALLBACK_DEFAULT_RETURN";
            } else if (!source && "CALL_SITE_RETURN".equals(event.kind)
                    && edge.siteId.equals(event.siteId)) {
                authority = "MAPPED_CALL_RETURN_SITE";
            } else if (!source && rpcPortMapping(edge)
                    && "CALL_SITE_RETURN".equals(event.kind)
                    && method.equals(event.method)
                    && methodName(methodInCell(edge.fromPort)).equals(
                    methodName(event.declaredCallee))) {
                authority = "MAPPED_RPC_CALL_RETURN";
            } else if (source && "RPC_ARGUMENT".equals(edge.kind)
                    && "CALL_ARGUMENT".equals(event.kind)
                    && method.equals(event.method)) {
                authority = "MAPPED_RPC_CALL_ARGUMENT";
            }
            if (!authority.isEmpty()) {
                addFingerprint(result, seen, new EndpointFingerprint(event.seq,
                        event.valueFingerprint, authority));
            }
        }
        FieldCell expectedField = fieldCell(port);
        if (expectedField.materializable()) {
            for (FieldAccessEvent event : evidence.fieldEvents) {
                if (!event.valueFingerprintComplete
                        || event.valueFingerprint.isEmpty()
                        || !sameField(expectedField,
                        fieldCell(event.field))) {
                    continue;
                }
                addFingerprint(result, seen, new EndpointFingerprint(event.seq,
                        event.valueFingerprint, "FIELD_VALUE"));
            }
        }
        return result;
    }

    private static boolean nameCallbackDefaultNameGetter(
            String declaredCallee) {
        String method = safe(declaredCallee);
        return method.startsWith(
                "<javax.security.auth.callback.NameCallback:")
                && "getDefaultName".equals(methodName(method));
    }

    private static void addFingerprint(List<EndpointFingerprint> result,
                                       Set<String> seen,
                                       EndpointFingerprint value) {
        String key = value.seq + "\n" + value.digest + "\n" + value.source;
        if (seen.add(key)) result.add(value);
    }

    private static boolean observesSite(List<RuntimeEvent> events, String siteId) {
        if (siteId == null || siteId.isEmpty()) {
            return false;
        }
        for (RuntimeEvent event : events) {
            if (siteId.equals(event.siteId)) {
                return true;
            }
        }
        return false;
    }

    private static boolean observesPortMethod(InstanceEvidence evidence,
                                              String port) {
        String method = methodInCell(port);
        if (method.isEmpty()) {
            // Synthetic protocol cells may not carry a Java method.  Their
            // region instance is the strongest endpoint evidence available.
            return true;
        }
        return evidence.observedMethods.contains(method);
    }

    private static boolean observesMappedRpcInvocation(List<RuntimeEvent> events,
                                                       String fromPort,
                                                       String toPort) {
        String callerMethod = methodInCell(toPort);
        String rpcMethodName = methodName(methodInCell(fromPort));
        if (callerMethod.isEmpty() || rpcMethodName.isEmpty()) {
            return false;
        }
        for (RuntimeEvent event : events) {
            if ("CALL_SITE_ENTER".equals(event.kind)
                    && callerMethod.equals(event.method)
                    && rpcMethodName.equals(methodName(event.declaredCallee))) {
                return true;
            }
        }
        return false;
    }

    private static String methodInCell(String cell) {
        String value = safe(cell);
        for (int start = value.indexOf('<'); start >= 0;
             start = value.indexOf('<', start + 1)) {
            int colon = value.indexOf(':', start + 1);
            int open = colon < 0 ? -1 : value.indexOf('(', colon + 1);
            int close = open < 0 ? -1 : value.indexOf(')', open + 1);
            if (colon < 0 || open < 0 || close < 0) {
                continue;
            }
            int end = close + 1;
            if (end < value.length() && value.charAt(end) == '>') {
                return value.substring(start, end + 1);
            }
        }
        return "";
    }

    private static String methodName(String signature) {
        String value = safe(signature);
        int open = value.lastIndexOf('(');
        int space = open < 0 ? -1 : value.lastIndexOf(' ', open);
        return space < 0 || open <= space ? "" : value.substring(space + 1, open);
    }

    private static SharedReadFrom sharedReadFrom(StaticRegionEdge edge,
                                                 InstanceEvidence upstream,
                                                 InstanceEvidence downstream) {
        if (!upstream.root.process.equals(downstream.root.process)) {
            return null;
        }
        FieldCell fromField = fieldCell(edge.fromPort);
        FieldCell toField = fieldCell(edge.toPort);
        if (!fromField.materializable() || !toField.materializable()
                || !sameField(fromField, toField)) {
            return null;
        }
        for (FieldAccessEvent write : upstream.fieldEvents) {
            WriteEvidence writeEvidence = writeEvidence(write,
                    upstream.runtimeEvents);
            if (writeEvidence == null
                    || !sameField(fromField, fieldCell(write.field))
                    || write.receiverObjectId == 0) {
                continue;
            }
            long writerSeq = writeEvidence.mutation == null
                    ? write.seq : writeEvidence.mutation.seq;
            for (FieldAccessEvent read : downstream.fieldEvents) {
                if (!"FIELD_READ".equals(read.kind)
                        || !sameField(toField, fieldCell(read.field))
                        || read.receiverObjectId == 0
                        || write.receiverObjectId != read.receiverObjectId
                        || writerSeq > read.seq) {
                    continue;
                }
                return new SharedReadFrom(write, read, writeEvidence);
            }
        }
        return null;
    }

    private static WriteEvidence writeEvidence(FieldAccessEvent field,
                                               List<RuntimeEvent> events) {
        if ("FIELD_WRITE".equals(field.kind)) {
            return new WriteEvidence("FIELD_ASSIGNMENT", null);
        }
        if (!"FIELD_READ".equals(field.kind) || field.valueObjectId == 0) {
            return null;
        }
        for (RuntimeEvent event : events) {
            if (event.seq < field.seq || event.callId != field.callId
                    || !"CALL_SITE_ENTER".equals(event.kind)
                    || event.objectId != field.valueObjectId
                    || !isContainerMutator(event.declaredCallee)) {
                continue;
            }
            return new WriteEvidence("FIELD_CONTAINER_MUTATION", event);
        }
        return null;
    }

    private static boolean isContainerMutator(String signature) {
        String value = safe(signature);
        return value.contains(" put(")
                || value.contains(" putAll(")
                || value.contains(" remove(")
                || value.contains(" clear(")
                || value.contains(" replace(")
                || value.contains(" compute(")
                || value.contains(" computeIfAbsent(")
                || value.contains(" computeIfPresent(")
                || value.contains(" merge(")
                || value.contains(" add(")
                || value.contains(" addAll(")
                || value.contains(" set(");
    }

    private static int countStatus(List<Map<String, Object>> rows, String status) {
        int count = 0;
        for (Map<String, Object> row : rows) {
            if (status.equals(string(row.get("status")))) {
                count++;
            }
        }
        return count;
    }

    private static void increment(Map<String, Integer> counts, String key) {
        Integer previous = counts.get(key);
        counts.put(key, previous == null ? 1 : previous + 1);
    }

    private static List<StaticRegion> readRegions(File file,
                                                   List<String> warnings) {
        List<StaticRegion> result = new ArrayList<>();
        if (file == null || !file.isFile()) {
            warnings.add("symbolic region file not found: "
                    + (file == null ? "null" : file.getPath()));
            return result;
        }
        try (BufferedReader reader = Files.newBufferedReader(file.toPath(),
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                String trimmed = line.trim();
                if (trimmed.isEmpty()) {
                    continue;
                }
                StaticRegion region = StaticRegion.fromJson(trimmed);
                if (region.regionId.isEmpty() || region.rootMethod.isEmpty()) {
                    warnings.add("ignored malformed region row");
                    continue;
                }
                result.add(region);
            }
        } catch (IOException exception) {
            warnings.add("failed to read symbolic regions: " + exception);
        }
        return result;
    }

    private static List<StaticRegionEdge> readRegionEdges(File file,
                                                           List<String> warnings) {
        List<StaticRegionEdge> result = new ArrayList<>();
        if (file == null) {
            return result;
        }
        if (!file.isFile()) {
            warnings.add("symbolic region edge file not found: " + file.getPath());
            return result;
        }
        try (BufferedReader reader = Files.newBufferedReader(file.toPath(),
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                String trimmed = line.trim();
                if (trimmed.isEmpty()) {
                    continue;
                }
                StaticRegionEdge edge = StaticRegionEdge.fromJson(trimmed);
                if (edge.edgeId.isEmpty() || edge.fromRegion.isEmpty()
                        || edge.toRegion.isEmpty()) {
                    warnings.add("ignored malformed region edge row");
                    continue;
                }
                result.add(edge);
            }
        } catch (IOException exception) {
            warnings.add("failed to read symbolic region edges: " + exception);
        }
        return result;
    }

    static final class Result {
        final List<Map<String, Object>> instances = new ArrayList<>();
        final List<Map<String, Object>> activations = new ArrayList<>();
        final List<Map<String, Object>> regionValidations = new ArrayList<>();
        final List<Map<String, Object>> edgeValidations = new ArrayList<>();
        final Map<String, Object> summary = new LinkedHashMap<>();
        final List<String> warnings = new ArrayList<>();
        final Set<String> unobservedRegionIds = new LinkedHashSet<>();
        boolean truncated;

        String instancesJsonl() {
            return jsonl(instances);
        }

        String activationsJsonl() {
            return jsonl(activations);
        }

        String regionValidationsJsonl() {
            return jsonl(regionValidations);
        }

        String edgeValidationsJsonl() {
            return jsonl(edgeValidations);
        }

        String summaryJson() {
            return json(summary);
        }
    }

    private static final class ContainedCallSelection {
        private final Set<Long> calls;
        private final boolean truncated;
        private final long skipped;

        private ContainedCallSelection(Set<Long> calls, boolean truncated,
                                       long skipped) {
            this.calls = calls;
            this.truncated = truncated;
            this.skipped = skipped;
        }
    }

    private static final class PathSignatureSelection {
        private final List<String> signature;
        private final int total;
        private final boolean truncated;
        private final long skipped;

        private PathSignatureSelection(List<String> signature, int total,
                                       boolean truncated, long skipped) {
            this.signature = signature;
            this.total = total;
            this.truncated = truncated;
            this.skipped = skipped;
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
        final long timeNanos;

        MethodEvent(long seq, String test, String process, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId,
                    long timeNanos) {
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
            this.timeNanos = timeNanos;
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
        final boolean hasOutcome;
        final boolean outcome;
        final String valueFingerprint;
        final boolean valueFingerprintComplete;
        final int valueFingerprintNodes;
        final String valueFingerprintReason;

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     int argumentIndex, String runtimeType, int objectId,
                     String primitiveValue, boolean hasOutcome,
                     boolean outcome) {
            this(seq, kind, method, callId, invocationId, parentSiteId,
                    siteId, "", argumentIndex, runtimeType, objectId,
                    primitiveValue, hasOutcome, outcome, "", false, 0,
                    "LEGACY_EVENT_NO_FINGERPRINT");
        }

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     String declaredCallee, int argumentIndex,
                     String runtimeType, int objectId,
                     String primitiveValue, boolean hasOutcome,
                     boolean outcome) {
            this(seq, kind, method, callId, invocationId, parentSiteId,
                    siteId, declaredCallee, argumentIndex, runtimeType,
                    objectId, primitiveValue, hasOutcome, outcome, "",
                    false, 0, "LEGACY_EVENT_NO_FINGERPRINT");
        }

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     String declaredCallee, int argumentIndex,
                     String runtimeType, int objectId,
                     String primitiveValue, boolean hasOutcome,
                     boolean outcome, String valueFingerprint,
                     boolean valueFingerprintComplete,
                     int valueFingerprintNodes,
                     String valueFingerprintReason) {
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
            this.hasOutcome = hasOutcome;
            this.outcome = outcome;
            this.valueFingerprint = safe(valueFingerprint);
            this.valueFingerprintComplete = valueFingerprintComplete;
            this.valueFingerprintNodes = valueFingerprintNodes;
            this.valueFingerprintReason = safe(valueFingerprintReason);
        }
    }

    private static final class AccessorReturnObservation {
        private final RuntimeEvent enter;
        private final RuntimeEvent returned;

        private AccessorReturnObservation(RuntimeEvent enter,
                                          RuntimeEvent returned) {
            this.enter = enter;
            this.returned = returned;
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
        final String valueFingerprint;
        final boolean valueFingerprintComplete;
        final int valueFingerprintNodes;
        final String valueFingerprintReason;

        FieldAccessEvent(long seq, String kind, String method, long callId,
                         String field, int receiverObjectId, int valueObjectId,
                         String primitiveValue) {
            this(seq, kind, method, callId, -1, "", field, receiverObjectId,
                    valueObjectId, primitiveValue, "", false, 0,
                    "LEGACY_EVENT_NO_FINGERPRINT");
        }

        FieldAccessEvent(long seq, String kind, String method, long callId,
                         String field, int receiverObjectId, int valueObjectId,
                         String primitiveValue, String valueFingerprint,
                         boolean valueFingerprintComplete,
                         int valueFingerprintNodes,
                         String valueFingerprintReason) {
            this(seq, kind, method, callId, -1, "", field,
                    receiverObjectId, valueObjectId, primitiveValue,
                    valueFingerprint, valueFingerprintComplete,
                    valueFingerprintNodes, valueFingerprintReason);
        }

        FieldAccessEvent(long seq, String kind, String method, long callId,
                         int unitIndex, String siteId, String field,
                         int receiverObjectId, int valueObjectId,
                         String primitiveValue, String valueFingerprint,
                         boolean valueFingerprintComplete,
                         int valueFingerprintNodes,
                         String valueFingerprintReason) {
            this.seq = seq;
            this.kind = safe(kind);
            this.method = safe(method);
            this.callId = callId;
            this.unitIndex = unitIndex;
            this.siteId = safe(siteId);
            this.field = safe(field);
            this.receiverObjectId = receiverObjectId;
            this.valueObjectId = valueObjectId;
            this.primitiveValue = safe(primitiveValue);
            this.valueFingerprint = safe(valueFingerprint);
            this.valueFingerprintComplete = valueFingerprintComplete;
            this.valueFingerprintNodes = valueFingerprintNodes;
            this.valueFingerprintReason = safe(valueFingerprintReason);
        }
    }

    private static final class StaticRegion {
        private String regionId = "";
        private String rootMethod = "";
        private String anchorMethod = "";
        private final Set<String> methods = new LinkedHashSet<>();
        private final List<StaticPort> inputs = new ArrayList<>();
        private final List<StaticPort> outputs = new ArrayList<>();
        private final Map<String, StaticOutputSlice> outputSlices =
                new LinkedHashMap<>();
        private final List<BranchPolicy> branches = new ArrayList<>();
        private final List<String> models = new ArrayList<>();
        private boolean inputSelectionComplete = true;
        private final List<String> unresolvedInputs = new ArrayList<>();
        private final Map<String, Map<Integer, List<String>>> argumentPathFields =
                new LinkedHashMap<>();

        private List<String> argumentPathFields(String method, int argumentIndex) {
            Map<Integer, List<String>> byArgument = argumentPathFields.get(
                    safe(method));
            if (byArgument == null) {
                return Collections.emptyList();
            }
            List<String> fields = byArgument.get(argumentIndex);
            return fields == null ? Collections.emptyList() : fields;
        }

        private StaticPort outputFor(String endpoint) {
            return portFor(outputs, endpoint, true);
        }

        private StaticPort inputFor(String endpoint) {
            return portFor(inputs, endpoint, true);
        }

        private StaticPort exactInputFor(String endpoint) {
            return portFor(inputs, endpoint, false);
        }

        private StaticOutputSlice outputSliceFor(String outputPort) {
            return outputSlices.get(safe(outputPort));
        }

        private StaticPort portFor(List<StaticPort> ports, String endpoint,
                                   boolean allowUniqueFieldFallback) {
            String value = safe(endpoint);
            for (StaticPort port : ports) {
                if (value.equals(port.portId) || value.equals(port.cell)) {
                    return port;
                }
            }
            if (!allowUniqueFieldFallback) {
                return null;
            }
            FieldCell expectedField = fieldCell(value);
            if (!expectedField.materializable()) {
                return null;
            }
            StaticPort match = null;
            for (StaticPort port : ports) {
                if (!sameField(expectedField, fieldCell(port.cell))) {
                    continue;
                }
                if (match != null) {
                    return null;
                }
                match = port;
            }
            return match;
        }

        private static StaticRegion fromJson(String json) {
            StaticRegion region = new StaticRegion();
            region.regionId = jsonString(json, "regionId");
            region.rootMethod = jsonString(json, "rootMethod");
            region.anchorMethod = firstNonBlank(jsonString(json, "anchorMethod"),
                    region.rootMethod);
            region.methods.addAll(jsonStringArray(json, "methods"));
            region.methods.add(region.rootMethod);
            for (String object : jsonObjectArray(json, "symbolicInputs")) {
                region.inputs.add(new StaticPort(
                        jsonString(object, "portId"),
                        jsonString(object, "cell"),
                        jsonString(object, "sourceKind"),
                        jsonString(object, "projection"), "",
                        StaticPort.materializationMetadata(object)));
            }
            for (String object : jsonObjectArray(json, "outputs")) {
                region.outputs.add(new StaticPort(
                        jsonString(object, "portId"),
                        jsonString(object, "cell"), "", "",
                        jsonString(object, "kind")));
            }
            for (String object : jsonObjectArray(json, "outputSlices")) {
                StaticOutputSlice slice = StaticOutputSlice.fromJson(object);
                if (!slice.outputPort.isEmpty()) {
                    region.outputSlices.put(slice.outputPort, slice);
                }
            }
            for (String object : jsonObjectArray(json, "branchPolicies")) {
                region.branches.add(new BranchPolicy(
                        jsonString(object, "siteId"),
                        jsonString(object, "policy"),
                        jsonString(object, "guard"),
                        jsonOptionalBoolean(object, "requiredOutcome"),
                        jsonString(object, "role")));
            }
            for (String object : jsonObjectArray(json, "argumentPathFields")) {
                String method = jsonString(object, "method");
                int argumentIndex = jsonInt(object, "argumentIndex", -1);
                List<String> fields = jsonStringArray(object, "fields");
                if (!method.isEmpty() && argumentIndex >= 0 && !fields.isEmpty()) {
                    region.argumentPathFields
                            .computeIfAbsent(method,
                                    ignored -> new LinkedHashMap<>())
                            .put(argumentIndex, fields);
                }
            }
            region.models.addAll(jsonStringArray(json, "models"));
            region.inputSelectionComplete = jsonBoolean(json,
                    "inputSelectionComplete", true);
            region.unresolvedInputs.addAll(jsonStringArray(json,
                    "unresolvedInputs"));
            return region;
        }
    }

    private static final class StaticRegionEdge {
        private String edgeId = "";
        private String fromRegion = "";
        private String toRegion = "";
        private String fromPort = "";
        private String fromOutputPort = "";
        private String fromOutputCell = "";
        private final List<String> aliasProofEdgeIds = new ArrayList<>();
        private String aliasProofAuthority = "";
        private boolean aliasProofComplete;
        private boolean canonicalMetadataPresent;
        private String toPort = "";
        private String kind = "";
        private String relation = "";
        private String candidateRelation = "";
        private String siteId = "";
        private boolean requiresOrder;
        private boolean requiresObjectIdentity;
        private String mappingKind = "";
        private String mappingAuthority = "";
        private boolean payloadEqualityCheckRequired;

        private static StaticRegionEdge fromJson(String json) {
            StaticRegionEdge edge = new StaticRegionEdge();
            edge.edgeId = jsonString(json, "edgeId");
            edge.fromRegion = jsonString(json, "fromRegion");
            edge.toRegion = jsonString(json, "toRegion");
            edge.fromPort = jsonString(json, "fromPort");
            edge.fromOutputPort = jsonString(json, "fromOutputPort");
            edge.fromOutputCell = jsonString(json, "fromOutputCell");
            edge.aliasProofEdgeIds.addAll(jsonStringArray(json,
                    "aliasProofEdgeIds"));
            edge.aliasProofAuthority = jsonString(json,
                    "aliasProofAuthority");
            edge.aliasProofComplete = jsonBoolean(json,
                    "aliasProofComplete", false);
            edge.canonicalMetadataPresent = jsonHasField(json,
                    "fromOutputPort") || jsonHasField(json,
                    "fromOutputCell") || jsonHasField(json,
                    "aliasProofEdgeIds") || jsonHasField(json,
                    "aliasProofAuthority") || jsonHasField(json,
                    "aliasProofComplete");
            edge.toPort = jsonString(json, "toPort");
            edge.kind = jsonString(json, "kind");
            edge.relation = jsonString(json, "relation");
            edge.candidateRelation = firstNonBlank(jsonString(json,
                    "candidateRelation"), edge.relation);
            edge.siteId = jsonString(json, "siteId");
            edge.requiresOrder = jsonBoolean(json, "requiresOrder", false);
            edge.requiresObjectIdentity = jsonBoolean(json,
                    "requiresObjectIdentity", false);
            edge.mappingKind = jsonString(json, "mappingKind");
            edge.mappingAuthority = jsonString(json, "mappingAuthority");
            edge.payloadEqualityCheckRequired = jsonBoolean(json,
                    "payloadEqualityCheckRequired",
                    "EQUALITY".equals(edge.candidateRelation));
            return edge;
        }

        /**
         * Runtime endpoint correlation keeps using {@link #fromPort}.  Only
         * producer-output selection consumes a complete exact alias proof;
         * an edge with no canonical schema keeps its exact raw endpoint, while
         * any partially populated canonical schema fails closed.
         */
        private String producerOutputEndpoint() {
            if (!canonicalMetadataPresent) {
                return fromPort;
            }
            return canonicalAliasValid() ? fromOutputPort : "";
        }

        private boolean usesCanonicalOutput() {
            return canonicalAliasValid();
        }

        private boolean canonicalAliasValid() {
            return canonicalMetadataPresent && aliasProofComplete
                    && !aliasProofEdgeIds.isEmpty()
                    && (("STATIC_EXACT_PROJECTED_RETURN_VALUE_FLOW_"
                    + "AND_DECLARED_RETURN_FIELD").equals(
                    aliasProofAuthority)
                    || "CONFIGURED_RPC_PRODUCER_RETURN_AND_STATIC_EXACT_"
                    .concat("PUBLISH_VALUE_FLOW_V1").equals(
                    aliasProofAuthority))
                    && !fromOutputPort.isEmpty()
                    && !fromOutputCell.isEmpty();
        }

        private StaticPort producerOutputFor(StaticRegion region) {
            StaticPort output = region.outputFor(producerOutputEndpoint());
            if (!usesCanonicalOutput()) {
                return output;
            }
            StaticPort cellMatch = region.outputFor(fromOutputCell);
            return output != null && cellMatch != null
                    && output.portId.equals(cellMatch.portId)
                    && output.cell.equals(cellMatch.cell)
                    ? output : null;
        }
    }

    private static final class InstanceEvidence {
        private final String instanceId;
        private final StaticRegion region;
        private final MethodEvent root;
        private final Set<Long> calls;
        private final List<MethodEvent> methodEvents;
        private final List<RuntimeEvent> runtimeEvents;
        private final List<FieldAccessEvent> fieldEvents;
        private final Set<String> observedMethods;
        private final String validationStatus;
        private final boolean runtimePathEvidenceComplete;

        private InstanceEvidence(String instanceId, StaticRegion region,
                                 MethodEvent root, Set<Long> calls,
                                 List<MethodEvent> methodEvents,
                                 List<RuntimeEvent> runtimeEvents,
                                 List<FieldAccessEvent> fieldEvents,
                                 Set<String> observedMethods,
                                 String validationStatus,
                                 boolean runtimePathEvidenceComplete) {
            this.instanceId = instanceId;
            this.region = region;
            this.root = root;
            this.calls = new LinkedHashSet<>(calls);
            this.methodEvents = new ArrayList<>(methodEvents);
            this.runtimeEvents = new ArrayList<>(runtimeEvents);
            this.fieldEvents = new ArrayList<>(fieldEvents);
            this.observedMethods = new LinkedHashSet<>(observedMethods);
            this.validationStatus = validationStatus;
            this.runtimePathEvidenceComplete = runtimePathEvidenceComplete;
        }

        private long firstMethodSeq(String method) {
            if (method == null || method.isEmpty()) {
                return 0L;
            }
            for (MethodEvent event : methodEvents) {
                if (method.equals(event.method)) {
                    return event.seq;
                }
            }
            return 0L;
        }

        private int runtimeOccurrence(RuntimeEvent target) {
            if (target == null) {
                return 1;
            }
            int occurrence = 0;
            for (RuntimeEvent event : runtimeEvents) {
                if (target.kind.equals(event.kind)
                        && target.method.equals(event.method)
                        && target.siteId.equals(event.siteId)) {
                    occurrence++;
                    if (event == target || event.seq == target.seq) {
                        return occurrence;
                    }
                }
            }
            return 1;
        }

        private List<RuntimeEvent> matchingCallArguments(
                Map<String, Object> binding) {
            List<RuntimeEvent> result = new ArrayList<>();
            String caller = string(binding.get("callerMethod"));
            String site = string(binding.get("siteId"));
            String callee = string(binding.get("calleeMethod"));
            int argument = binding.get("argumentIndex") instanceof Number
                    ? ((Number) binding.get("argumentIndex")).intValue() : -1;
            int unit = binding.get("unitIndex") instanceof Number
                    ? ((Number) binding.get("unitIndex")).intValue() : -1;
            for (RuntimeEvent event : runtimeEvents) {
                if (!"CALL_ARGUMENT".equals(event.kind)
                        || !caller.equals(event.method)
                        || !site.equals(event.siteId)
                        || argument != event.argumentIndex
                        || !callee.isEmpty()
                        && !callee.equals(event.declaredCallee)
                        || unit >= 0 && !site.endsWith("#u" + unit)) {
                    continue;
                }
                result.add(event);
            }
            return result;
        }

        private int callArgumentOccurrence(Map<String, Object> binding,
                                           RuntimeEvent target) {
            int occurrence = 0;
            for (RuntimeEvent event : matchingCallArguments(binding)) {
                occurrence++;
                if (event == target || event.seq == target.seq) {
                    return occurrence;
                }
            }
            return 0;
        }

        private List<RuntimeEvent> matchingMethodReturns(
                Map<String, Object> binding) {
            List<RuntimeEvent> result = new ArrayList<>();
            String method = string(binding.get("method"));
            if (method.isEmpty()) return result;
            for (RuntimeEvent event : runtimeEvents) {
                if ("METHOD_EXIT_NORMAL".equals(event.kind)
                        && method.equals(event.method)) {
                    result.add(event);
                }
            }
            result.sort(Comparator.comparingLong(value -> value.seq));
            return result;
        }

        /**
         * Returns native-run writes that can witness a FIELD_ASSIGNMENT_RHS
         * request.  FieldAccessEvent intentionally carries no inferred site;
         * the caller may use these rows only after proving that the static
         * method/field pair has one exact assignment site.
         */
        private List<FieldAccessEvent> matchingFieldAssignments(
                Map<String, Object> binding) {
            List<FieldAccessEvent> result = new ArrayList<>();
            String method = string(binding.get("method"));
            FieldCell expected = fieldCell(string(binding.get(
                    "fieldSignature")));
            if (method.isEmpty() || !expected.declaredSignature) {
                return result;
            }
            for (FieldAccessEvent event : fieldEvents) {
                if ("FIELD_WRITE".equals(event.kind)
                        && method.equals(event.method)
                        && sameField(expected, fieldCell(event.field))) {
                    result.add(event);
                }
            }
            result.sort(Comparator.comparingLong(value -> value.seq));
            return result;
        }

        private boolean oneFieldOwner(
                List<FieldAccessEvent> assignments) {
            int receiver = 0;
            for (FieldAccessEvent event : assignments) {
                if (event.receiverObjectId == 0) {
                    return false;
                }
                if (receiver == 0) {
                    receiver = event.receiverObjectId;
                } else if (receiver != event.receiverObjectId) {
                    return false;
                }
            }
            return receiver != 0;
        }

        private long lastSeq() {
            long last = root.seq;
            for (RuntimeEvent event : runtimeEvents) {
                last = Math.max(last, event.seq);
            }
            for (FieldAccessEvent event : fieldEvents) {
                last = Math.max(last, event.seq);
            }
            return last;
        }
    }

    private static final class SharedReadFrom {
        private final FieldAccessEvent write;
        private final FieldAccessEvent read;
        private final WriteEvidence writeEvidence;

        private SharedReadFrom(FieldAccessEvent write, FieldAccessEvent read,
                               WriteEvidence writeEvidence) {
            this.write = write;
            this.read = read;
            this.writeEvidence = writeEvidence;
        }

        private long writerEventSeq() {
            return writeEvidence.mutation == null
                    ? write.seq : writeEvidence.mutation.seq;
        }

        private long writerCallId() {
            return writeEvidence.mutation == null
                    ? write.callId : writeEvidence.mutation.callId;
        }

        private String writerSiteId() {
            return writeEvidence.mutation == null
                    ? "" : writeEvidence.mutation.siteId;
        }
    }

    private static final class EndpointFingerprint {
        private final long seq;
        private final String digest;
        private final String source;

        private EndpointFingerprint(long seq, String digest, String source) {
            this.seq = seq;
            this.digest = safe(digest);
            this.source = safe(source);
        }
    }

    private static final class FingerprintMatch {
        private final EndpointFingerprint from;
        private final EndpointFingerprint to;

        private FingerprintMatch(EndpointFingerprint from,
                                 EndpointFingerprint to) {
            this.from = from;
            this.to = to;
        }

        private long distance() {
            return Math.abs(to.seq - from.seq);
        }
    }

    private static final class WriteEvidence {
        private final String kind;
        private final RuntimeEvent mutation;

        private WriteEvidence(String kind, RuntimeEvent mutation) {
            this.kind = kind;
            this.mutation = mutation;
        }
    }

    private static final class UpstreamEdgeBinding {
        private final StaticRegionEdge edge;
        private final InstanceEvidence upstream;
        private final InstanceEvidence downstream;
        private final SharedReadFrom readFrom;
        private StaticPort output;
        private StaticPort downstreamInput;

        private UpstreamEdgeBinding(StaticRegionEdge edge,
                                    InstanceEvidence upstream,
                                    InstanceEvidence downstream,
                                    SharedReadFrom readFrom) {
            this.edge = edge;
            this.upstream = upstream;
            this.downstream = downstream;
            this.readFrom = readFrom;
        }

        private String identity() {
            return edge.edgeId + "\n" + upstream.instanceId + "\n"
                    + downstream.instanceId + "\n" + readFrom.writerEventSeq()
                    + "\n" + readFrom.read.seq;
        }

        private Map<String, Object> toMap() {
            Map<String, Object> result = object(
                    "edgeId", edge.edgeId,
                    "relation", "READ_FROM",
                    "fromRegion", edge.fromRegion,
                    "toRegion", edge.toRegion,
                    "fromRegionInstance", upstream.instanceId,
                    "toRegionInstance", downstream.instanceId,
                    "fromRootCallId", upstream.root.callId,
                    "toRootCallId", downstream.root.callId,
                    "fromOutputPort", output.portId,
                    "fromOutputCell", output.cell,
                    "toInputPort", downstreamInput == null
                            ? edge.toPort : downstreamInput.portId,
                    "toInputCell", downstreamInput == null
                            ? edge.toPort : downstreamInput.cell,
                    "writerEventSeq", readFrom.writerEventSeq(),
                    "readerEventSeq", readFrom.read.seq,
                    "writerCallId", readFrom.writerCallId(),
                    "writerSiteId", readFrom.writerSiteId(),
                    "writerOccurrence", upstream.runtimeOccurrence(
                            readFrom.writeEvidence.mutation),
                    "writeEvidenceKind", readFrom.writeEvidence.kind,
                    "field", readFrom.write.field,
                    "receiverObjectId", readFrom.write.receiverObjectId,
                    "valueObjectId", readFrom.write.valueObjectId,
                    "orderConfirmed", true,
                    "objectIdentityConfirmed",
                    readFrom.write.receiverObjectId
                            == readFrom.read.receiverObjectId,
                    "selectionAuthority",
                    "RUNTIME_CONFIRMED_READ_FROM");
            result.put("rawFromPort", edge.fromPort);
            result.put("canonicalOutputAliasUsed",
                    edge.usesCanonicalOutput());
            result.put("aliasProofEdgeIds",
                    new ArrayList<>(edge.aliasProofEdgeIds));
            result.put("aliasProofAuthority", edge.aliasProofAuthority);
            result.put("aliasProofComplete", edge.aliasProofComplete);
            return result;
        }

        private Map<String, Object> eventMap() {
            return object(
                    "rootCallId", upstream.root.callId,
                    "writerCallId", readFrom.writerCallId(),
                    "writerEventSeq", readFrom.writerEventSeq(),
                    "writerSiteId", readFrom.writerSiteId(),
                    "writerOccurrence", upstream.runtimeOccurrence(
                            readFrom.writeEvidence.mutation),
                    "writeEvidenceKind", readFrom.writeEvidence.kind,
                    "receiverObjectId", readFrom.write.receiverObjectId,
                    "valueObjectId", readFrom.write.valueObjectId,
                    "field", readFrom.write.field,
                    "authority", "RUNTIME_EVENT_TRACE");
        }
    }

    private static final class DownstreamContainerDemand {
        private final Map<String, Object> downstreamActivation;
        private final String edgeId;
        private final String downstreamInputPort;
        private final String bindingId;
        private final String baseInputSymbol;
        private final String declaredFieldSignature;
        private final String declaredFieldOwnerClass;
        private final String declaredFieldType;
        private final String declaredFieldName;
        private final List<String> fieldPath;
        private final boolean declarationComplete;

        private DownstreamContainerDemand(
                Map<String, Object> downstreamActivation, String edgeId,
                String downstreamInputPort, String bindingId,
                String baseInputSymbol, String declaredFieldSignature,
                String declaredFieldOwnerClass, String declaredFieldType,
                String declaredFieldName, List<String> fieldPath,
                boolean declarationComplete) {
            this.downstreamActivation = downstreamActivation;
            this.edgeId = edgeId;
            this.downstreamInputPort = downstreamInputPort;
            this.bindingId = bindingId;
            this.baseInputSymbol = baseInputSymbol;
            this.declaredFieldSignature = declaredFieldSignature;
            this.declaredFieldOwnerClass = declaredFieldOwnerClass;
            this.declaredFieldType = declaredFieldType;
            this.declaredFieldName = declaredFieldName;
            this.fieldPath = fieldPath;
            this.declarationComplete = declarationComplete;
        }

        private static DownstreamContainerDemand from(
                Map<String, Object> edge,
                Map<String, Object> downstreamActivation,
                Map<String, Object> declaration) {
            return new DownstreamContainerDemand(downstreamActivation,
                    string(edge.get("edgeId")),
                    string(edge.get("toInputPort")),
                    string(declaration.get("bindingId")),
                    string(declaration.get("baseInputSymbol")),
                    string(declaration.get("declaredFieldSignature")),
                    string(declaration.get("declaredFieldOwnerClass")),
                    string(declaration.get("declaredFieldType")),
                    string(declaration.get("declaredFieldName")),
                    new ArrayList<>(stringSet(declaration.get("fieldPath"))),
                    Boolean.TRUE.equals(declaration.get("complete"))
                            && Integer.valueOf(1).equals(declaration.get(
                            "schemaVersion"))
                            && "ARRAY_ELEMENT_FIELD".equals(string(
                            declaration.get("kind"))));
        }

        private boolean complete() {
            FieldCell field = fieldCell(declaredFieldSignature);
            return declarationComplete && !edgeId.isEmpty()
                    && !downstreamInputPort.isEmpty()
                    && !bindingId.isEmpty() && !baseInputSymbol.isEmpty()
                    && field.declaredSignature
                    && field.owner.equals(declaredFieldOwnerClass)
                    && field.type.equals(declaredFieldType)
                    && field.name.equals(declaredFieldName)
                    && fieldPath.equals(Collections.singletonList(
                    declaredFieldName));
        }

        private String identity() {
            return edgeId + "\n" + downstreamInputPort + "\n" + bindingId
                    + "\n" + declaredFieldSignature;
        }
    }

    private static final class MapValueProjectionProof {
        private final boolean complete;
        private final String issue;
        private final String operation;
        private final String mapInputPort;
        private final String mapInputCell;
        private final String mapViewSiteId;
        private final String snapshotSiteId;
        private final List<String> outputFieldPath;
        private final List<String> causalEdgeIds;

        private MapValueProjectionProof(boolean complete, String issue,
                                        String operation,
                                        String mapInputPort,
                                        String mapInputCell,
                                        String mapViewSiteId,
                                        String snapshotSiteId,
                                        List<String> outputFieldPath,
                                        List<String> causalEdgeIds) {
            this.complete = complete;
            this.issue = issue;
            this.operation = operation;
            this.mapInputPort = mapInputPort;
            this.mapInputCell = mapInputCell;
            this.mapViewSiteId = mapViewSiteId;
            this.snapshotSiteId = snapshotSiteId;
            this.outputFieldPath = outputFieldPath;
            this.causalEdgeIds = causalEdgeIds;
        }

        private static MapValueProjectionProof from(
                Map<String, Object> slice) {
            List<Map<String, Object>> edges = mapRows(slice.get(
                    "causalEdges"));
            List<Map<String, Object>> views = new ArrayList<>();
            List<Map<String, Object>> snapshots = new ArrayList<>();
            for (Map<String, Object> edge : edges) {
                if (!Integer.valueOf(1).equals(edge.get(
                        "containerProjectionContractVersion"))
                        || !Boolean.TRUE.equals(edge.get(
                        "receiverValueDependencyComplete"))
                        || !"JAVA_COLLECTION_API_EXACT_SIGNATURE_WHITELIST_V1"
                        .equals(string(edge.get(
                                "containerProjectionAuthority")))) {
                    continue;
                }
                String operation = string(edge.get(
                        "containerProjectionOperation"));
                if ("COLLECTION_TO_ARRAY".equals(operation)
                        && Boolean.TRUE.equals(edge.get("snapshot"))) {
                    snapshots.add(edge);
                } else if (("MAP_VALUES_VIEW".equals(operation)
                        || "MAP_KEY_SET_VIEW".equals(operation)
                        || "MAP_ENTRY_SET_VIEW".equals(operation))
                        && Boolean.TRUE.equals(edge.get("backedView"))) {
                    views.add(edge);
                }
            }

            List<Map<String, Object>[]> pairs = new ArrayList<>();
            for (Map<String, Object> view : views) {
                for (Map<String, Object> snapshot : snapshots) {
                    if (string(view.get("toCell")).equals(string(
                            snapshot.get("fromCell")))) {
                        @SuppressWarnings("unchecked")
                        Map<String, Object>[] pair = new Map[]{view, snapshot};
                        pairs.add(pair);
                    }
                }
            }
            if (pairs.size() != 1) {
                return incomplete(pairs.isEmpty()
                        ? "MISSING_EXACT_MAP_VIEW_TO_ARRAY_CHAIN"
                        : "AMBIGUOUS_MAP_VIEW_TO_ARRAY_CHAIN");
            }
            Map<String, Object> view = pairs.get(0)[0];
            Map<String, Object> snapshot = pairs.get(0)[1];
            String operation = string(view.get(
                    "containerProjectionOperation"));
            if ("MAP_ENTRY_SET_VIEW".equals(operation)
                    || !Boolean.TRUE.equals(view.get(
                    "elementIdentityPreserving"))) {
                return incomplete("MAP_ENTRY_SET_REQUIRES_KEY_VALUE_"
                        + "ASSOCIATION_PROOF");
            }

            String outputCell = string(slice.get("outputCell"));
            String arrayCell = string(snapshot.get("toCell"));
            List<String> outputPath = exactValuePath(arrayCell, outputCell,
                    edges);
            if (outputPath == null) {
                return incomplete("SNAPSHOT_ARRAY_DOES_NOT_REACH_"
                        + "REQUESTED_OUTPUT_BY_EXACT_VALUE_FLOW");
            }

            String mapCell = string(view.get("fromCell"));
            List<Map<String, Object>> matchingInputs = new ArrayList<>();
            Map<Map<String, Object>, List<String>> inputPaths =
                    new LinkedHashMap<>();
            for (Map<String, Object> input : mapRows(slice.get(
                    "inputBindings"))) {
                List<String> path = exactValuePath(string(input.get(
                        "dependencyCell")), mapCell, edges);
                if (path != null) {
                    matchingInputs.add(input);
                    inputPaths.put(input, path);
                }
            }
            if (matchingInputs.size() != 1) {
                return incomplete(matchingInputs.isEmpty()
                        ? "MAP_VIEW_RECEIVER_HAS_NO_EXACT_INPUT_PORT"
                        : "MAP_VIEW_RECEIVER_INPUT_PORT_IS_AMBIGUOUS");
            }
            Map<String, Object> input = matchingInputs.get(0);
            String inputPort = string(input.get("inputPort"));
            String inputCell = string(input.get("dependencyCell"));
            if (inputPort.isEmpty() || !fieldCell(inputCell)
                    .declaredSignature) {
                return incomplete("MAP_VIEW_RECEIVER_INPUT_IS_NOT_AN_EXACT_"
                        + "DECLARED_FIELD");
            }

            FieldCell outputField = fieldCell(outputCell);
            List<String> outputFieldPath = outputField.declaredSignature
                    ? Collections.singletonList(outputField.name)
                    : Collections.<String>emptyList();
            Set<String> proofSet = new LinkedHashSet<>();
            String viewId = edgeId(view);
            String snapshotId = edgeId(snapshot);
            if (viewId.isEmpty() || snapshotId.isEmpty()) {
                return incomplete("MAP_VIEW_PROJECTION_HAS_NO_CAUSAL_EDGE_IDS");
            }
            proofSet.addAll(inputPaths.get(input));
            proofSet.add(viewId);
            proofSet.add(snapshotId);
            proofSet.addAll(outputPath);
            return new MapValueProjectionProof(true, "", operation,
                    inputPort, inputCell, string(view.get("siteId")),
                    string(snapshot.get("siteId")), outputFieldPath,
                    new ArrayList<>(proofSet));
        }

        private static MapValueProjectionProof incomplete(String issue) {
            return new MapValueProjectionProof(false, issue, "", "", "",
                    "", "", Collections.<String>emptyList(),
                    Collections.<String>emptyList());
        }

        private static List<String> exactValuePath(
                String from, String to, List<Map<String, Object>> edges) {
            if (from.isEmpty() || to.isEmpty()) return null;
            Set<String> reached = new LinkedHashSet<>();
            List<String> pending = new ArrayList<>();
            Map<String, String> previousCell = new LinkedHashMap<>();
            Map<String, String> previousEdge = new LinkedHashMap<>();
            reached.add(from);
            pending.add(from);
            for (int index = 0; index < pending.size(); index++) {
                String current = pending.get(index);
                if (to.equals(current)) break;
                for (Map<String, Object> edge : edges) {
                    if (!exactValueFlowEdge(edge)
                            || !current.equals(string(edge.get(
                            "fromCell")))) {
                        continue;
                    }
                    String next = string(edge.get("toCell"));
                    if (!next.isEmpty() && reached.add(next)) {
                        previousCell.put(next, current);
                        previousEdge.put(next, edgeId(edge));
                        pending.add(next);
                    }
                }
            }
            if (!reached.contains(to)) return null;
            List<String> reversed = new ArrayList<>();
            String current = to;
            while (!from.equals(current)) {
                String edge = previousEdge.get(current);
                String previous = previousCell.get(current);
                if (edge == null || edge.isEmpty() || previous == null) {
                    return null;
                }
                reversed.add(edge);
                current = previous;
            }
            Collections.reverse(reversed);
            return reversed;
        }

        private static boolean exactValueFlowEdge(
                Map<String, Object> edge) {
            if (Integer.valueOf(1).equals(edge.get(
                    "containerProjectionContractVersion"))) {
                return Boolean.TRUE.equals(edge.get(
                        "receiverValueDependencyComplete"))
                        && "JAVA_COLLECTION_API_EXACT_SIGNATURE_WHITELIST_V1"
                        .equals(string(edge.get(
                                "containerProjectionAuthority")));
            }
            String transfer = string(edge.get("transferKind"));
            String kind = string(edge.get("kind"));
            if ("VALUE_PASS".equals(transfer)) {
                return "local_def_use".equals(kind)
                        || "projected_local_def_use".equals(kind);
            }
            if ("HEAP_READ".equals(transfer)) {
                return "field_read".equals(kind)
                        || "projected_field_read".equals(kind);
            }
            if ("HEAP_WRITE".equals(transfer)) {
                return "field_write".equals(kind)
                        || "projected_field_write".equals(kind);
            }
            if ("IDENTITY_BINDING".equals(transfer)) {
                return "call_argument".equals(kind)
                        || "caller_argument".equals(kind);
            }
            return "CONSTRUCT".equals(transfer)
                    && "constructor_caller_argument".equals(kind);
        }

        private static String edgeId(Map<String, Object> edge) {
            return firstNonBlank(string(edge.get("edgeId")),
                    string(edge.get("id")));
        }
    }

    private static final class StaticOutputSlice {
        private String outputPort = "";
        private String outputCell = "";
        private String selection = "";
        private boolean complete;
        private boolean structuralComplete;
        private boolean regionTruncated;
        private boolean sliceTruncated;
        private boolean methodBudgetTruncated;
        private boolean causalCellBudgetTruncated;
        private final List<String> structuralIssues = new ArrayList<>();
        private final Set<String> inputPorts = new LinkedHashSet<>();
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<String> sites = new LinkedHashSet<>();
        private final List<String> causalEdgeIds = new ArrayList<>();
        private final List<Map<String, Object>> causalEdges =
                new ArrayList<>();
        private final List<Map<String, Object>> inputBindings =
                new ArrayList<>();
        private final List<Map<String, Object>>
                inputAliasCanonicalizations = new ArrayList<>();
        private final List<String> inputAliasCanonicalizationIssues =
                new ArrayList<>();
        private int requestedStateTransformerContractVersion;
        private boolean requestedStateTransformerContractApplicable;
        private String requestedStateTransformerContractOutputPort = "";
        private String requestedStateTransformerContractOutputCell = "";
        private final List<Map<String, Object>>
                requestedStateTransformerObligations = new ArrayList<>();
        private int requestedStateTransformerObligationCount;
        private final List<String> requestedStateTransformerContractIssues =
                new ArrayList<>();
        private boolean requestedStateTransformerContractComplete;
        private String requestedStateTransformerContractAuthority = "";
        private final List<Map<String, Object>> heapInitializers =
                new ArrayList<>();
        private final List<Map<String, Object>> captureBindings =
                new ArrayList<>();
        private final List<Map<String, Object>>
                containerElementFieldBindings = new ArrayList<>();
        private boolean captureBindingsRequired;
        private boolean captureBindingsComplete = true;
        private final List<String> captureBindingIssues = new ArrayList<>();
        private boolean captureDischargedByHeapEffectTransformer;
        private String captureDischargeInputPort = "";
        private String captureDischargeAuthority = "";
        private final List<String> unresolvedInputs = new ArrayList<>();
        private final List<Map<String, Object>> unresolvedInputDetails =
                new ArrayList<>();
        private boolean unresolvedInputProvenanceComplete;
        private boolean runtimeRefined;
        private boolean runtimeRefinementComplete = true;
        private final Set<String> staticInputPorts = new LinkedHashSet<>();
        private final Set<String> staticMethods = new LinkedHashSet<>();
        private final Set<String> staticSites = new LinkedHashSet<>();
        private final List<String> staticCausalEdgeIds = new ArrayList<>();
        private final Set<String> excludedInputPorts = new LinkedHashSet<>();
        private final Set<String> excludedMethods = new LinkedHashSet<>();
        private final Set<String> runtimeOnlyMethods = new LinkedHashSet<>();
        private final Set<String> excludedSites = new LinkedHashSet<>();
        private final Set<String> excludedPathAlternativeSites =
                new LinkedHashSet<>();
        private final List<Map<String, Object>>
                excludedAlternativeUnresolvedInputs = new ArrayList<>();
        private final List<String> excludedCausalEdgeIds = new ArrayList<>();
        private final List<String> prestateElisions = new ArrayList<>();

        private static StaticOutputSlice fromJson(String json) {
            StaticOutputSlice slice = new StaticOutputSlice();
            slice.outputPort = jsonString(json, "outputPort");
            slice.outputCell = jsonString(json, "outputCell");
            slice.selection = jsonString(json, "selection");
            slice.complete = jsonBoolean(json, "complete", false);
            slice.inputPorts.addAll(jsonStringArray(json, "inputPorts"));
            slice.methods.addAll(jsonStringArray(json, "methods"));
            slice.sites.addAll(jsonStringArray(json, "sites"));
            slice.causalEdgeIds.addAll(jsonStringArray(json,
                    "causalEdgeIds"));
            for (String binding : jsonObjectArray(json, "inputBindings")) {
                Map<String, Object> parsed = object(
                        "dependencyCell", jsonString(binding,
                        "dependencyCell"),
                        "inputPort", jsonString(binding, "inputPort"),
                        "bindingAuthority", jsonString(binding,
                        "bindingAuthority"),
                        "dependencyMethods", jsonStringArray(binding,
                        "dependencyMethods"));
                // Preserve the exact projected-leaf declaration emitted by
                // the static slice.  Dropping these fields used to collapse a
                // nested array carrier back to its root argument type, which
                // made an exact consumed-getfield join impossible downstream.
                List<String> fieldPath = jsonStringArray(binding,
                        "fieldPath");
                if (!fieldPath.isEmpty()) {
                    parsed.put("fieldPath", fieldPath);
                }
                String leafSignature = firstNonBlank(jsonString(binding,
                        "leafFieldSignature"), jsonString(binding,
                        "declaredFieldSignature"));
                if (!leafSignature.isEmpty()) {
                    parsed.put("leafFieldSignature", leafSignature);
                }
                String declaredSignature = jsonString(binding,
                        "declaredFieldSignature");
                if (!declaredSignature.isEmpty()) {
                    parsed.put("declaredFieldSignature",
                            declaredSignature);
                }
                if (jsonHasField(binding,
                        "requestedStateTransformerSinkSites")) {
                    parsed.put("requestedStateTransformerSinkSites",
                            jsonStringArray(binding,
                                    "requestedStateTransformerSinkSites"));
                    parsed.put("requestedStateTransformerGuardSites",
                            jsonStringArray(binding,
                                    "requestedStateTransformerGuardSites"));
                    parsed.put(
                            "requestedStateTransformerSinkClosureComplete",
                            jsonBoolean(binding,
                                    "requestedStateTransformerSinkClosureComplete",
                                    false));
                    parsed.put("requestedStateTransformerSinkExclusive",
                            jsonBoolean(binding,
                                    "requestedStateTransformerSinkExclusive",
                                    false));
                    parsed.put(
                            "requestedStateTransformerUnclassifiedEdgeIds",
                            jsonStringArray(binding,
                                    "requestedStateTransformerUnclassifiedEdgeIds"));
                    parsed.put("requestedStateTransformerSinkAuthority",
                            jsonString(binding,
                                    "requestedStateTransformerSinkAuthority"));
                }
                slice.inputBindings.add(parsed);
            }
            for (String edge : jsonObjectArray(json, "causalEdges")) {
                slice.causalEdges.add(causalEdgeReference(edge));
            }
            slice.requestedStateTransformerContractVersion = jsonInt(json,
                    "requestedStateTransformerContractVersion", 0);
            slice.requestedStateTransformerContractApplicable = jsonBoolean(
                    json, "requestedStateTransformerContractApplicable",
                    false);
            slice.requestedStateTransformerContractOutputPort = jsonString(
                    json, "requestedStateTransformerContractOutputPort");
            slice.requestedStateTransformerContractOutputCell = jsonString(
                    json, "requestedStateTransformerContractOutputCell");
            for (String obligation : jsonObjectArray(json,
                    "requestedStateTransformerObligations")) {
                slice.requestedStateTransformerObligations.add(object(
                        "siteId", jsonString(obligation, "siteId"),
                        "method", jsonString(obligation, "method"),
                        "targetCell", jsonString(obligation, "targetCell"),
                        "transferKind", jsonString(obligation,
                        "transferKind"),
                        "kind", jsonString(obligation, "kind"),
                        "causalEdgeIds", jsonStringArray(obligation,
                        "causalEdgeIds"),
                        "authority", jsonString(obligation, "authority")));
            }
            slice.requestedStateTransformerObligationCount = jsonInt(json,
                    "requestedStateTransformerObligationCount", -1);
            slice.requestedStateTransformerContractIssues.addAll(
                    jsonStringArray(json,
                            "requestedStateTransformerContractIssues"));
            slice.requestedStateTransformerContractComplete = jsonBoolean(
                    json, "requestedStateTransformerContractComplete",
                    false);
            slice.requestedStateTransformerContractAuthority = jsonString(
                    json, "requestedStateTransformerContractAuthority");
            for (String initializer : jsonObjectArray(json,
                    "heapInitializers")) {
                slice.heapInitializers.add(object(
                        "initializerId", jsonString(initializer,
                        "initializerId"),
                        "kind", jsonString(initializer, "kind"),
                        "allocatedType", jsonString(initializer,
                        "allocatedType"),
                        "allocationCell", jsonString(initializer,
                        "allocationCell"),
                        "allocationValueCell", jsonString(initializer,
                        "allocationValueCell"),
                        "allocationEdgeId", jsonString(initializer,
                        "allocationEdgeId"),
                        "allocationMethod", jsonString(initializer,
                        "allocationMethod"),
                        "allocationSiteId", jsonString(initializer,
                        "allocationSiteId"),
                        "allocationUnitIndex", jsonInt(initializer,
                        "allocationUnitIndex", -1),
                        "constructor", jsonString(initializer,
                        "constructor"),
                        "constructorArgumentCount", jsonInt(initializer,
                        "constructorArgumentCount", -1),
                        "constructorSiteId", jsonString(initializer,
                        "constructorSiteId"),
                        "constructorUnitIndex", jsonInt(initializer,
                        "constructorUnitIndex", -1),
                        "outputPort", jsonString(initializer,
                        "outputPort"),
                        "outputCell", jsonString(initializer,
                        "outputCell"),
                        "proofEdgeIds", jsonStringArray(initializer,
                        "proofEdgeIds"),
                        "proofComplete", jsonBoolean(initializer,
                        "proofComplete", false),
                        "selectionAuthority", jsonString(initializer,
                        "selectionAuthority"),
                        "captureBoundaryRequirement", jsonString(initializer,
                        "captureBoundaryRequirement")));
            }
            slice.captureBindingsRequired = jsonBoolean(json,
                    "captureBindingsRequired", false);
            slice.captureBindingsComplete = jsonBoolean(json,
                    "captureBindingsComplete",
                    !slice.captureBindingsRequired);
            for (String binding : jsonObjectArray(json,
                    "captureBindings")) {
                slice.captureBindings.add(outputCaptureBinding(binding));
            }
            for (String binding : jsonObjectArray(json,
                    "containerElementFieldBindings")) {
                slice.containerElementFieldBindings.add(
                        containerElementFieldBinding(binding));
            }
            slice.captureBindingIssues.addAll(jsonStringArray(json,
                    "captureBindingIssues"));
            slice.unresolvedInputs.addAll(jsonStringArray(json,
                    "unresolvedInputs"));
            for (String detail : jsonObjectArray(json,
                    "unresolvedInputDetails")) {
                slice.unresolvedInputDetails.add(object(
                        "dependencyCell", jsonString(detail,
                        "dependencyCell"),
                        "dependencyMethods", jsonStringArray(detail,
                        "dependencyMethods"),
                        "reason", jsonString(detail, "reason"),
                        "diagnostic", jsonString(detail, "diagnostic"),
                        "provenanceAuthority", jsonString(detail,
                        "provenanceAuthority")));
            }
            slice.regionTruncated = jsonBoolean(json,
                    "regionTruncated", false);
            slice.sliceTruncated = jsonBoolean(json, "truncated", false);
            slice.methodBudgetTruncated = jsonBoolean(json,
                    "methodBudgetTruncated", false);
            slice.causalCellBudgetTruncated = jsonBoolean(json,
                    "causalCellBudgetTruncated", false);
            slice.structuralIssues.addAll(jsonStringArray(json,
                    "truncationReasons"));
            // New static artifacts state this fact explicitly.  For older
            // non-truncated artifacts, a non-empty exact causal-edge ledger
            // is the strongest recoverable structural fact; every other
            // completion component is recomputed independently below.
            slice.structuralComplete = jsonBoolean(json,
                    "structuralComplete", !slice.regionTruncated
                            && !slice.sliceTruncated
                            && !slice.methodBudgetTruncated
                            && !slice.causalCellBudgetTruncated
                            && !slice.causalEdgeIds.isEmpty());
            slice.unresolvedInputProvenanceComplete =
                    slice.validateUnresolvedInputProvenance();
            return slice;
        }

        private static Map<String, Object> outputCaptureBinding(String json) {
            return object(
                    "captureKind", firstNonBlank(jsonString(json,
                    "captureKind"), "CALL_ARGUMENT"),
                    "captureBindingId", jsonString(json,
                    "captureBindingId"),
                    "outputPort", jsonString(json, "outputPort"),
                    "outputCell", jsonString(json, "outputCell"),
                    "method", jsonString(json, "method"),
                    "callerMethod", jsonString(json, "callerMethod"),
                    "siteId", jsonString(json, "siteId"),
                    "unitIndex", jsonInt(json, "unitIndex", -1),
                    "unit", jsonString(json, "unit"),
                    "fieldSignature", jsonString(json,
                    "fieldSignature"),
                    "fieldOwnerExpression", jsonString(json,
                    "fieldOwnerExpression"),
                    "fieldOwnerCell", jsonString(json,
                    "fieldOwnerCell"),
                    "fieldOwnerDeclaredType", jsonString(json,
                    "fieldOwnerDeclaredType"),
                    "fieldOwnerBindingKind", jsonString(json,
                    "fieldOwnerBindingKind"),
                    "fieldOwnerBindingAuthority", jsonString(json,
                    "fieldOwnerBindingAuthority"),
                    "rhsExpression", jsonString(json, "rhsExpression"),
                    "rhsCell", jsonString(json, "rhsCell"),
                    "rhsCausalEdgeId", jsonString(json,
                    "rhsCausalEdgeId"),
                    "rhsRelation", jsonString(json, "rhsRelation"),
                    "rhsRelationComplete", jsonBoolean(json,
                    "rhsRelationComplete", false),
                    "rhsRelationAuthority", jsonString(json,
                    "rhsRelationAuthority"),
                    "returnExpression", jsonString(json,
                    "returnExpression"),
                    "returnCell", jsonString(json, "returnCell"),
                    "calleeMethod", jsonString(json, "calleeMethod"),
                    "argumentIndex", jsonInt(json, "argumentIndex", -1),
                    "argumentCell", jsonString(json, "argumentCell"),
                    "causalEdgeId", jsonString(json, "causalEdgeId"),
                    "transferKind", jsonString(json, "transferKind"),
                    "bindingKind", jsonString(json, "bindingKind"),
                    "bindingAuthority", jsonString(json,
                    "bindingAuthority"),
                    "occurrence", jsonInt(json, "occurrence", 0),
                    "occurrenceAuthority", jsonString(json,
                    "occurrenceAuthority"),
                    "runtimeFieldOwnerObjectId", jsonInt(json,
                    "runtimeFieldOwnerObjectId", 0),
                    "runtimeFieldOwnerBindingAuthority", jsonString(json,
                    "runtimeFieldOwnerBindingAuthority"),
                    "runtimeEventSeq", jsonInt(json,
                    "runtimeEventSeq", -1));
        }

        private static Map<String, Object> containerElementFieldBinding(
                String json) {
            return object(
                    "schemaVersion", jsonInt(json, "schemaVersion", -1),
                    "kind", jsonString(json, "kind"),
                    "bindingId", jsonString(json, "bindingId"),
                    "baseInputSymbol", jsonString(json,
                    "baseInputSymbol"),
                    "containerInputPort", jsonString(json,
                    "containerInputPort"),
                    "containerInputCell", jsonString(json,
                    "containerInputCell"),
                    "selectorAuthority", jsonString(json,
                    "selectorAuthority"),
                    "elementIndex", jsonInt(json, "elementIndex", -2),
                    "elementOccurrence", jsonInt(json,
                    "elementOccurrence", -2),
                    "fieldPath", jsonStringArray(json, "fieldPath"),
                    "declaredFieldSignature", jsonString(json,
                    "declaredFieldSignature"),
                    "declaredFieldOwnerClass", jsonString(json,
                    "declaredFieldOwnerClass"),
                    "declaredFieldType", jsonString(json,
                    "declaredFieldType"),
                    "declaredFieldName", jsonString(json,
                    "declaredFieldName"),
                    "method", jsonString(json, "method"),
                    "fieldMaterializationSiteId", jsonString(json,
                    "fieldMaterializationSiteId"),
                    "arrayLoadSiteId", jsonString(json,
                    "arrayLoadSiteId"),
                    "proofCausalEdgeIds", jsonStringArray(json,
                    "proofCausalEdgeIds"),
                    "proofAuthority", jsonString(json,
                    "proofAuthority"),
                    "complete", jsonBoolean(json, "complete", false));
        }

        private Map<String, Object> copyContainerElementFieldBinding(
                Map<String, Object> declaration) {
            Map<String, Object> copy = new LinkedHashMap<>(declaration);
            copy.put("fieldPath", new ArrayList<>(stringSet(
                    declaration.get("fieldPath"))));
            Object proof = declaration.get("proofCausalEdgeIds");
            copy.put("proofCausalEdgeIds", proof instanceof Collection<?>
                    ? new ArrayList<>((Collection<?>) proof)
                    : new ArrayList<Object>());
            return copy;
        }

        private boolean completeContainerElementFieldDeclaration(
                Map<String, Object> declaration,
                Set<String> retainedStaticInputPorts, String method) {
            String base = string(declaration.get("baseInputSymbol"));
            String container = string(declaration.get(
                    "containerInputPort"));
            String containerCell = string(declaration.get(
                    "containerInputCell"));
            String fieldSignature = string(declaration.get(
                    "declaredFieldSignature"));
            FieldCell field = fieldCell(fieldSignature);
            FieldCell containerField = fieldCell(containerCell);
            String selector = string(declaration.get(
                    "selectorAuthority"));
            int index = intValue(declaration.get("elementIndex"), -2);
            int occurrence = intValue(declaration.get(
                    "elementOccurrence"), -2);
            boolean selectorComplete = "EXACT_ARRAY_INDEX".equals(selector)
                    ? index >= 0 && occurrence > 0
                    : "DISCOVER_UNIQUE_IDENTITY_INDEX".equals(selector)
                    && index == -1 && occurrence == -1;
            Set<String> path = stringSet(declaration.get("fieldPath"));
            Set<String> proof = stringSet(declaration.get(
                    "proofCausalEdgeIds"));
            return intValue(declaration.get("schemaVersion"), -1) == 1
                    && "ARRAY_ELEMENT_FIELD".equals(string(declaration.get(
                    "kind")))
                    && Boolean.TRUE.equals(declaration.get("complete"))
                    && !string(declaration.get("bindingId")).isEmpty()
                    && !base.isEmpty() && !container.isEmpty()
                    && !base.equals(container)
                    && retainedStaticInputPorts.contains(base)
                    && retainedStaticInputPorts.contains(container)
                    && selectorComplete
                    && field.declaredSignature
                    && containerField.declaredSignature
                    && containerField.type.endsWith("[]")
                    && field.owner.equals(string(declaration.get(
                    "declaredFieldOwnerClass")))
                    && field.type.equals(string(declaration.get(
                    "declaredFieldType")))
                    && field.name.equals(string(declaration.get(
                    "declaredFieldName")))
                    && path.equals(Collections.singleton(field.name))
                    && method.equals(string(declaration.get("method")))
                    && exactUnitSite(method, string(declaration.get(
                    "fieldMaterializationSiteId")))
                    && sites.contains(string(declaration.get(
                    "fieldMaterializationSiteId")))
                    && exactUnitSite(method, string(declaration.get(
                    "arrayLoadSiteId")))
                    && sites.contains(string(declaration.get(
                    "arrayLoadSiteId")))
                    && proof.size() == 4 && !proof.contains("")
                    && new LinkedHashSet<>(causalEdgeIds).containsAll(proof)
                    && "STATIC_EXACT_CONTAINER_ARRAY_ACCESSOR_DECLARED_"
                    .concat("FIELD_FOUR_EDGE_JOIN_V1").equals(string(
                    declaration.get("proofAuthority")));
        }

        private int intValue(Object value, int fallback) {
            return value instanceof Number
                    ? ((Number) value).intValue() : fallback;
        }

        private boolean exactUnitSite(String method, String site) {
            return !method.isEmpty() && safe(site).matches(
                    Pattern.quote(method) + "#u[0-9]+");
        }

        private static Map<String, Object> causalEdgeReference(String json) {
            Map<String, Object> result = object(
                    "edgeId", jsonString(json, "edgeId"),
                    "method", jsonString(json, "method"),
                    "siteId", jsonString(json, "siteId"),
                    "fromCell", jsonString(json, "fromCell"),
                    "toCell", jsonString(json, "toCell"),
                    "transferKind", jsonString(json, "transferKind"),
                    "kind", jsonString(json, "kind"));
            int projectionVersion = jsonInt(json,
                    "containerProjectionContractVersion", -1);
            if (projectionVersion >= 0) {
                result.put("containerProjectionContractVersion",
                        projectionVersion);
                copyString(json, result, "containerProjectionOperation");
                copyString(json, result, "containerProjectionAuthority");
                copyString(json, result, "elementRelation");
                copyString(json, result, "iterationOrderAuthority");
                for (String field : new String[]{
                        "receiverValueDependencyComplete",
                        "elementIdentityPreserving",
                        "mappingAssociationPreserving", "backedView",
                        "snapshot", "containerEqualityAsserted"}) {
                    Boolean value = jsonOptionalBoolean(json, field);
                    if (value != null) result.put(field, value);
                }
            }
            copyString(json, result, "guardSiteId");
            copyString(json, result, "guardedMutationSiteId");
            copyString(json, result, "guardedMutationsAuthority");
            Boolean required = jsonOptionalBoolean(json,
                    "requiredOutcome");
            if (required != null) result.put("requiredOutcome", required);
            int count = jsonInt(json, "guardedMutationCount", -1);
            if (count >= 0) result.put("guardedMutationCount", count);
            List<Map<String, Object>> mutations = new ArrayList<>();
            for (String mutation : jsonObjectArray(json,
                    "guardedMutations")) {
                Map<String, Object> row = object(
                        "guardSiteId", jsonString(mutation, "guardSiteId"),
                        "guardedMutationSiteId", jsonString(mutation,
                        "guardedMutationSiteId"),
                        "method", jsonString(mutation, "method"),
                        "unitIndex", jsonInt(mutation, "unitIndex", -1));
                Boolean mutationRequired = jsonOptionalBoolean(mutation,
                        "requiredOutcome");
                if (mutationRequired != null) {
                    row.put("requiredOutcome", mutationRequired);
                }
                mutations.add(row);
            }
            if (!mutations.isEmpty()) result.put("guardedMutations",
                    mutations);
            return result;
        }

        private static void copyString(String json,
                                       Map<String, Object> result,
                                       String field) {
            String value = jsonString(json, field);
            if (!value.isEmpty()) result.put(field, value);
        }

        private boolean validateUnresolvedInputProvenance() {
            if (unresolvedInputs.isEmpty()) {
                return unresolvedInputDetails.isEmpty();
            }
            if (unresolvedInputDetails.size() != unresolvedInputs.size()
                    || new LinkedHashSet<>(unresolvedInputs).size()
                    != unresolvedInputs.size()) {
                return false;
            }
            Set<String> diagnostics = new LinkedHashSet<>();
            for (Map<String, Object> detail : unresolvedInputDetails) {
                String diagnostic = string(detail.get("diagnostic"));
                String cell = string(detail.get("dependencyCell"));
                String reason = string(detail.get("reason"));
                Object rawMethods = detail.get("dependencyMethods");
                Set<String> dependencyMethods = stringSet(
                        rawMethods);
                if (diagnostic.isEmpty() || cell.isEmpty()
                        || reason.isEmpty() || dependencyMethods.isEmpty()
                        || !(rawMethods instanceof Collection<?>)
                        || dependencyMethods.size()
                        != ((Collection<?>) rawMethods).size()
                        || !diagnostic.startsWith(cell + " [")
                        || !supportedUnresolvedInputReason(reason)
                        || !UNRESOLVED_INPUT_PROVENANCE_AUTHORITY.equals(
                        string(detail.get("provenanceAuthority")))
                        || !diagnostics.add(diagnostic)) {
                    return false;
                }
            }
            return diagnostics.equals(new LinkedHashSet<>(unresolvedInputs));
        }

        private static boolean supportedUnresolvedInputReason(
                String reason) {
            return "NO_MATERIALIZABLE_REGION_BOUNDARY_REPRESENTATION"
                    .equals(reason)
                    || "OUTPUT_SLICE_DEPENDENCY_PROMOTION_CAPACITY_EXCEEDED"
                    .equals(reason)
                    || "INCOMPATIBLE_PROMOTED_DECLARED_FIELD_PORT"
                    .equals(reason)
                    || "OUTPUT_SLICE_INPUT_HAS_NO_REGION_PORT".equals(reason);
        }

        private void refineUnresolvedInputs(Set<String> observed,
                                            StaticOutputSlice refined) {
            boolean provenanceComplete =
                    validateUnresolvedInputProvenance();
            refined.unresolvedInputProvenanceComplete = provenanceComplete;
            if (!provenanceComplete) {
                refined.unresolvedInputs.addAll(unresolvedInputs);
                refined.unresolvedInputDetails.addAll(
                        copyRows(unresolvedInputDetails));
                if (!unresolvedInputs.isEmpty()
                        || !unresolvedInputDetails.isEmpty()) {
                    refined.runtimeRefinementComplete = false;
                }
                return;
            }
            for (Map<String, Object> detail : unresolvedInputDetails) {
                Set<String> dependencyMethods = stringSet(
                        detail.get("dependencyMethods"));
                boolean exactStaticMethods = !dependencyMethods.isEmpty()
                        && methods.containsAll(dependencyMethods);
                boolean observedDependency = intersects(dependencyMethods,
                        observed);
                if (exactStaticMethods && !observedDependency) {
                    refined.excludedAlternativeUnresolvedInputs.add(
                            new LinkedHashMap<>(detail));
                    continue;
                }
                String diagnostic = string(detail.get("diagnostic"));
                refined.unresolvedInputs.add(diagnostic);
                refined.unresolvedInputDetails.add(
                        new LinkedHashMap<>(detail));
                if (!exactStaticMethods) {
                    // A missing, ambiguous, or out-of-slice method set must
                    // never be interpreted as proof of an unobserved path.
                    refined.runtimeRefinementComplete = false;
                    refined.unresolvedInputProvenanceComplete = false;
                }
            }
        }

        private StaticOutputSlice runtimeRefined(InstanceEvidence evidence) {
            StaticOutputSlice refined = new StaticOutputSlice();
            refined.outputPort = outputPort;
            refined.outputCell = outputCell;
            refined.selection = selection;
            refined.runtimeRefined = true;
            refined.structuralComplete = structuralComplete;
            refined.regionTruncated = regionTruncated;
            refined.sliceTruncated = sliceTruncated;
            refined.methodBudgetTruncated = methodBudgetTruncated;
            refined.causalCellBudgetTruncated = causalCellBudgetTruncated;
            refined.structuralIssues.addAll(structuralIssues);
            refined.staticInputPorts.addAll(inputPorts);
            refined.staticMethods.addAll(methods);
            refined.staticSites.addAll(sites);
            refined.staticCausalEdgeIds.addAll(causalEdgeIds);
            refined.captureBindingsRequired = captureBindingsRequired;
            refined.captureBindingsComplete = captureBindingsComplete;
            refined.captureBindingIssues.addAll(captureBindingIssues);
            refined.requestedStateTransformerContractVersion =
                    requestedStateTransformerContractVersion;
            refined.requestedStateTransformerContractApplicable =
                    requestedStateTransformerContractApplicable;
            refined.requestedStateTransformerContractOutputPort =
                    requestedStateTransformerContractOutputPort;
            refined.requestedStateTransformerContractOutputCell =
                    requestedStateTransformerContractOutputCell;
            refined.requestedStateTransformerContractIssues.addAll(
                    requestedStateTransformerContractIssues);
            refined.requestedStateTransformerContractComplete =
                    requestedStateTransformerContractComplete;
            refined.requestedStateTransformerContractAuthority =
                    requestedStateTransformerContractAuthority;

            Set<String> observed = new LinkedHashSet<>(
                    evidence.observedMethods);
            refineUnresolvedInputs(observed, refined);
            refined.methods.addAll(sorted(observed));
            refined.excludedMethods.addAll(difference(methods, observed));
            refined.runtimeOnlyMethods.addAll(difference(observed, methods));
            if (!refined.runtimeOnlyMethods.isEmpty()) {
                // Runtime call-tree membership proves that these helpers ran,
                // but it cannot invent their static input/field dependency
                // closure.  Keep them for diagnostics and branch capture,
                // while forcing a fresh static refinement before the summary
                // is admitted to SMT composition.
                refined.runtimeRefinementComplete = false;
                for (String method : refined.runtimeOnlyMethods) {
                    refined.unresolvedInputs.add(
                            "RUNTIME_OBSERVED_METHOD_OUTSIDE_STATIC_OUTPUT_"
                                    + "SLICE:" + method);
                }
                refined.unresolvedInputProvenanceComplete = false;
            }
            boolean filtersAlternatives = !refined.excludedMethods.isEmpty();

            Set<String> retainedTransformerSites = new LinkedHashSet<>();
            for (Map<String, Object> obligation
                    : requestedStateTransformerObligations) {
                String method = string(obligation.get("method"));
                if (!filtersAlternatives || observed.contains(method)) {
                    Map<String, Object> retained = new LinkedHashMap<>(
                            obligation);
                    Object edgeIds = obligation.get("causalEdgeIds");
                    if (edgeIds instanceof Collection<?>) {
                        retained.put("causalEdgeIds", new ArrayList<>(
                                (Collection<?>) edgeIds));
                    }
                    refined.requestedStateTransformerObligations.add(
                            retained);
                    String site = string(obligation.get("siteId"));
                    if (!site.isEmpty()) {
                        retainedTransformerSites.add(site);
                    }
                } else if (method.isEmpty()) {
                    refined.requestedStateTransformerObligations.add(
                            new LinkedHashMap<>(obligation));
                    refined.runtimeRefinementComplete = false;
                }
            }
            refined.requestedStateTransformerObligationCount =
                    refined.requestedStateTransformerObligations.size();

            Set<String> staticBranchSites = new LinkedHashSet<>();
            for (BranchPolicy branch : evidence.region.branches) {
                staticBranchSites.add(branch.siteId);
            }
            Set<String> observedBranchSites = new LinkedHashSet<>();
            for (RuntimeEvent event : evidence.runtimeEvents) {
                if ("BRANCH".equals(event.kind)
                        && !event.siteId.isEmpty()) {
                    observedBranchSites.add(event.siteId);
                }
            }
            for (String site : sites) {
                if (staticBranchSites.contains(site)
                        && !observedBranchSites.contains(site)) {
                    if (evidence.runtimePathEvidenceComplete) {
                        // OUTPUT_CLOSURE is one concrete runtime path.  A
                        // static branch in an observed method is still an
                        // alternative when its exact site did not execute.
                        // A fresh flipped run can admit it later.
                        refined.excludedSites.add(site);
                        refined.excludedPathAlternativeSites.add(site);
                        continue;
                    }
                    // Never turn a truncated call/path record into negative
                    // branch evidence.
                    refined.sites.add(site);
                    refined.runtimeRefinementComplete = false;
                    continue;
                }
                String method = methodInCell(site);
                if (method.isEmpty()) {
                    refined.sites.add(site);
                    if (filtersAlternatives) {
                        refined.runtimeRefinementComplete = false;
                    }
                } else if (observed.contains(method)) {
                    refined.sites.add(site);
                } else {
                    refined.excludedSites.add(site);
                }
            }
            // Static sites describe the dependency closure.  Every branch
            // actually encountered under the selected root is also relevant
            // to bounded path closure, including helper methods admitted by
            // the runtime region call tree.
            for (RuntimeEvent event : evidence.runtimeEvents) {
                if ("BRANCH".equals(event.kind)
                        && observed.contains(event.method)
                        && !event.siteId.isEmpty()) {
                    refined.sites.add(event.siteId);
                }
            }

            List<Map<String, Object>> retainedBindings = new ArrayList<>();
            Set<String> retainedPorts = new LinkedHashSet<>();
            for (Map<String, Object> binding : inputBindings) {
                Set<String> bindingMethods = stringSet(
                        binding.get("dependencyMethods"));
                boolean retain = !filtersAlternatives
                        || intersects(bindingMethods, observed);
                if (filtersAlternatives && bindingMethods.isEmpty()) {
                    // Old artifacts lack dependency-method provenance.  Keep
                    // the input conservatively, but do not report a complete
                    // runtime refinement.
                    retain = true;
                    refined.runtimeRefinementComplete = false;
                }
                String port = string(binding.get("inputPort"));
                if (retain) {
                    Map<String, Object> retained = new LinkedHashMap<>(
                            binding);
                    if (requestedStateTransformerContractVersion > 0
                            && retained.containsKey(
                            "requestedStateTransformerSinkSites")) {
                        Set<String> sinks = stringSet(retained.get(
                                "requestedStateTransformerSinkSites"));
                        sinks.retainAll(retainedTransformerSites);
                        retained.put("requestedStateTransformerSinkSites",
                                new ArrayList<>(sinks));
                    }
                    retainedBindings.add(retained);
                    if (!port.isEmpty()) {
                        retainedPorts.add(port);
                    }
                } else if (!port.isEmpty()) {
                    refined.excludedInputPorts.add(port);
                }
            }
            if (inputBindings.isEmpty()) {
                retainedPorts.addAll(inputPorts);
                if (filtersAlternatives && !inputPorts.isEmpty()) {
                    refined.runtimeRefinementComplete = false;
                }
            }

            for (Map<String, Object> initializer : heapInitializers) {
                String method = string(initializer.get("allocationMethod"));
                if (!filtersAlternatives || observed.contains(method)) {
                    refined.heapInitializers.add(
                            new LinkedHashMap<>(initializer));
                } else if (method.isEmpty()) {
                    refined.heapInitializers.add(
                            new LinkedHashMap<>(initializer));
                    refined.runtimeRefinementComplete = false;
                }
            }

            // A retained fresh-allocation proof supersedes an otherwise
            // conservative old-state port for this same selected path.
            boolean selectedFreshInitializer = false;
            for (Map<String, Object> initializer : refined.heapInitializers) {
                if (outputCell.equals(string(initializer.get("outputCell")))
                        && Boolean.TRUE.equals(initializer.get(
                        "proofComplete"))
                        && evidence.root.method.equals(string(initializer.get(
                        "allocationMethod")))) {
                    for (FieldAccessEvent event : evidence.fieldEvents) {
                        if ("FIELD_WRITE".equals(event.kind)
                                && event.receiverObjectId
                                == evidence.root.objectId
                                && sameField(fieldCell(outputCell),
                                fieldCell(event.field))) {
                            selectedFreshInitializer = true;
                            break;
                        }
                    }
                    if (selectedFreshInitializer) {
                        break;
                    }
                }
            }
            if (selectedFreshInitializer) {
                List<Map<String, Object>> withoutPrestate = new ArrayList<>();
                for (Map<String, Object> binding : retainedBindings) {
                    if (outputCell.equals(string(binding.get(
                            "dependencyCell")))) {
                        String port = string(binding.get("inputPort"));
                        refined.prestateElisions.add(port
                                + ":FRESH_INITIALIZER_ON_SELECTED_RUNTIME_PATH");
                    } else {
                        withoutPrestate.add(binding);
                    }
                }
                retainedBindings = withoutPrestate;
                retainedPorts.clear();
                for (Map<String, Object> binding : retainedBindings) {
                    String port = string(binding.get("inputPort"));
                    if (!port.isEmpty()) {
                        retainedPorts.add(port);
                    }
                }
            }
            refined.inputBindings.addAll(retainedBindings);
            refined.inputPorts.addAll(sorted(retainedPorts));
            for (String port : inputPorts) {
                if (!refined.inputPorts.contains(port)) {
                    refined.excludedInputPorts.add(port);
                }
            }

            // A container-element declaration is path-specific.  Retain it
            // only when its exact materialization method was observed and
            // both of its statically named input ports survived runtime
            // alternative refinement.  Malformed production declarations
            // fail the requested-output activation closed; they are never
            // silently downgraded to the legacy one-static-field symbol.
            for (Map<String, Object> declaration
                    : containerElementFieldBindings) {
                String method = string(declaration.get("method"));
                boolean methodObserved = !method.isEmpty()
                        && observed.contains(method);
                if (!methodObserved) {
                    if (methods.contains(method)) {
                        // This is an unobserved static alternative, so its
                        // exact selector is irrelevant to this activation.
                        continue;
                    }
                    refined.runtimeRefinementComplete = false;
                    continue;
                }
                String base = string(declaration.get("baseInputSymbol"));
                String container = string(declaration.get(
                        "containerInputPort"));
                boolean portsRetained = refined.inputPorts.contains(base)
                        && refined.inputPorts.contains(container);
                if (!portsRetained
                        || !completeContainerElementFieldDeclaration(
                        declaration, inputPorts, method)) {
                    refined.runtimeRefinementComplete = false;
                    continue;
                }
                refined.containerElementFieldBindings.add(
                        copyContainerElementFieldBinding(declaration));
            }

            Map<String, Map<String, Object>> causalById =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : causalEdges) {
                String id = string(edge.get("edgeId"));
                if (!id.isEmpty()) {
                    causalById.put(id, edge);
                }
            }
            boolean causalMetadataComplete = causalById.keySet().containsAll(
                    causalEdgeIds);
            for (String id : causalEdgeIds) {
                Map<String, Object> edge = causalById.get(id);
                if (!filtersAlternatives) {
                    refined.causalEdgeIds.add(id);
                    if (edge != null) {
                        refined.causalEdges.add(new LinkedHashMap<>(edge));
                    }
                    continue;
                }
                if (edge == null) {
                    refined.causalEdgeIds.add(id);
                    refined.runtimeRefinementComplete = false;
                    continue;
                }
                String method = firstNonBlank(string(edge.get("method")),
                        methodInCell(string(edge.get("siteId"))));
                if (method.isEmpty()) {
                    refined.causalEdgeIds.add(id);
                    refined.causalEdges.add(new LinkedHashMap<>(edge));
                    refined.runtimeRefinementComplete = false;
                } else if (observed.contains(method)) {
                    refined.causalEdgeIds.add(id);
                    refined.causalEdges.add(new LinkedHashMap<>(edge));
                } else {
                    refined.excludedCausalEdgeIds.add(id);
                }
            }
            if (!causalMetadataComplete && !causalEdgeIds.isEmpty()) {
                refined.runtimeRefinementComplete = false;
            }
            refined.structuralComplete = structuralComplete
                    && !sliceTruncated
                    && !methodBudgetTruncated
                    && !causalCellBudgetTruncated
                    && !refined.causalEdgeIds.isEmpty();
            boolean staticTransformerContractLedgerComplete =
                    requestedStateTransformerContractComplete
                            && requestedStateTransformerContractIssues.isEmpty()
                            && requestedStateTransformerObligationCount
                            == requestedStateTransformerObligations.size();
            // This fact is deliberately independent of
            // runtimeRefinementComplete.  Capture discharge consumes both
            // facts as siblings below; making either one define the other
            // creates a cycle in which a missing capture prevents the
            // mutation transformer from being selected in the first place.
            refined.requestedStateTransformerContractComplete =
                    refined.runtimeRefinedTransformerContractComplete(
                            staticTransformerContractLedgerComplete);
            refineRuntimeCapture(refined, evidence, observed,
                    retainedBindings, retainedPorts);
            boolean transformerContractReady =
                    !requestedStateTransformerContractApplicable
                            || refined.requestedStateTransformerContractComplete;
            refined.complete = refined.structuralComplete
                    && refined.runtimeRefinementComplete
                    && refined.unresolvedInputs.isEmpty()
                    && refined.unresolvedInputProvenanceComplete
                    && transformerContractReady
                    && refined.captureBindingsComplete;
            return refined;
        }

        /**
         * Revalidates the exact transformer ledger after static alternatives
         * have been removed.  This validation intentionally does not read or
         * write {@link #runtimeRefinementComplete}; the final readiness gate
         * requires the two independent facts together.
         */
        private boolean runtimeRefinedTransformerContractComplete(
                boolean staticContractLedgerComplete) {
            if (!requestedStateTransformerContractApplicable) {
                return false;
            }
            if (!staticContractLedgerComplete
                    || requestedStateTransformerContractVersion != 1
                    || !outputPort.equals(
                    requestedStateTransformerContractOutputPort)
                    || !outputCell.equals(
                    requestedStateTransformerContractOutputCell)
                    || !"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1"
                    .equals(requestedStateTransformerContractAuthority)
                    || !requestedStateTransformerContractIssues.isEmpty()
                    || requestedStateTransformerObligations.isEmpty()
                    || requestedStateTransformerObligationCount
                    != requestedStateTransformerObligations.size()) {
                return false;
            }

            Map<String, Map<String, Object>> edgesById =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : causalEdges) {
                String id = string(edge.get("edgeId"));
                if (id.isEmpty() || edgesById.put(id, edge) != null) {
                    return false;
                }
            }
            Set<String> obligationSites = new LinkedHashSet<>();
            for (Map<String, Object> obligation
                    : requestedStateTransformerObligations) {
                String site = string(obligation.get("siteId"));
                String method = string(obligation.get("method"));
                String kind = string(obligation.get("kind"));
                Set<String> edgeIds = stringSet(obligation.get(
                        "causalEdgeIds"));
                if (site.isEmpty() || method.isEmpty()
                        || !obligationSites.add(site)
                        || !methods.contains(method)
                        || !outputCell.equals(string(obligation.get(
                        "targetCell")))
                        || !"HEAP_WRITE".equals(string(obligation.get(
                        "transferKind")))
                        || !("field_write".equals(kind)
                        || "field_mutation".equals(kind))
                        || !"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL"
                        .equals(string(obligation.get("authority")))
                        || edgeIds.isEmpty()) {
                    return false;
                }
                for (String edgeId : edgeIds) {
                    Map<String, Object> edge = edgesById.get(edgeId);
                    if (edge == null
                            || !method.equals(string(edge.get("method")))
                            || !site.equals(string(edge.get("siteId")))
                            || !"HEAP_WRITE".equals(string(edge.get(
                            "transferKind")))
                            || !kind.equals(string(edge.get("kind")))) {
                        return false;
                    }
                }
            }
            return true;
        }

        /**
         * Finalizes the output capture only after path alternatives, inputs,
         * initializers, and causal edges have all been runtime-refined.
         */
        private void refineRuntimeCapture(StaticOutputSlice refined,
                                          InstanceEvidence evidence,
                                          Set<String> observed,
                                          List<Map<String, Object>>
                                                  retainedBindings,
                                          Set<String> retainedPorts) {
            String heapEffectCaptureInput =
                    refined.heapEffectCaptureDischargeInput(
                            retainedBindings, retainedPorts);
            boolean heapEffectCaptureDischarged =
                    mutationCaptureDischargeReady(refined, evidence,
                            observed, heapEffectCaptureInput);
            if (heapEffectCaptureDischarged) {
                // An in-place container mutation has no assignment RHS to
                // capture.  The exact same-cell pre-state port plus the
                // importer-validated, path-ordered heap effects is the
                // relational output.  Do not manufacture a second Map
                // reference expression or treat put/remove as putfield.
                refined.captureBindings.clear();
                refined.captureBindingsRequired = false;
                refined.captureBindingsComplete = true;
                refined.captureBindingIssues.clear();
                refined.captureDischargedByHeapEffectTransformer = true;
                refined.captureDischargeInputPort = heapEffectCaptureInput;
                refined.captureDischargeAuthority =
                        "HEAP_EFFECT_STATE_TRANSFORMER";
                return;
            }

            if (captureBindingsRequired) {
                refined.captureBindings.clear();
                int matchedCaptureCount = 0;
                boolean fieldAssignmentRequested = false;
                boolean methodReturnRequested = false;
                for (Map<String, Object> binding : captureBindings) {
                    String captureKind = firstNonBlank(string(binding.get(
                            "captureKind")), "CALL_ARGUMENT");
                    if ("FIELD_ASSIGNMENT_RHS".equals(captureKind)) {
                        fieldAssignmentRequested = true;
                        String method = string(binding.get("method"));
                        String fieldSignature = string(binding.get(
                                "fieldSignature"));
                        if (!observed.contains(method)) {
                            continue;
                        }
                        Set<String> staticSites = new LinkedHashSet<>();
                        for (Map<String, Object> candidate
                                : captureBindings) {
                            if ("FIELD_ASSIGNMENT_RHS".equals(
                                    firstNonBlank(string(candidate.get(
                                            "captureKind")),
                                            "CALL_ARGUMENT"))
                                    && method.equals(string(candidate.get(
                                    "method")))
                                    && fieldSignature.equals(string(
                                    candidate.get("fieldSignature")))) {
                                staticSites.add(string(candidate.get(
                                        "siteId")));
                            }
                        }
                        if (staticSites.size() != 1) {
                            refined.captureBindingIssues.add(
                                    "RUNTIME_FIELD_WRITE_SITE_NOT_UNIQUE:"
                                            + method + ":"
                                            + fieldSignature);
                            continue;
                        }
                        List<FieldAccessEvent> assignments = evidence
                                .matchingFieldAssignments(binding);
                        if (assignments.isEmpty()) {
                            continue;
                        }
                        if (!evidence.oneFieldOwner(assignments)) {
                            refined.captureBindingIssues.add(
                                    "RUNTIME_FIELD_ASSIGNMENT_OWNER_"
                                            + "AMBIGUOUS:"
                                            + string(binding.get("siteId")));
                            continue;
                        }
                        FieldAccessEvent match = assignments.get(
                                assignments.size() - 1);
                        Map<String, Object> exact =
                                new LinkedHashMap<>(binding);
                        exact.put("occurrence", assignments.size());
                        exact.put("occurrenceAuthority",
                                "RUNTIME_UNIQUE_STATIC_FIELD_ASSIGNMENT_"
                                        + "SITE_LAST_WRITE_OCCURRENCE");
                        exact.put("runtimeFieldOwnerObjectId",
                                match.receiverObjectId);
                        exact.put("runtimeFieldOwnerBindingAuthority",
                                "RUNTIME_EXACT_FIELD_WRITE_RECEIVER_IDENTITY");
                        exact.put("runtimeCallId", match.callId);
                        exact.put("runtimeEventSeq", match.seq);
                        refined.captureBindings.add(exact);
                        matchedCaptureCount++;
                        continue;
                    }

                    if ("METHOD_RETURN_VALUE".equals(captureKind)) {
                        methodReturnRequested = true;
                        String method = string(binding.get("method"));
                        if (!observed.contains(method)) {
                            continue;
                        }
                        List<RuntimeEvent> returns = evidence
                                .matchingMethodReturns(binding);
                        // METHOD_EXIT_NORMAL has the exact method/call id but
                        // intentionally no Jimple return-site id.  Refine only
                        // a unique invocation; otherwise the static hook's
                        // requested occurrence would be a guess.
                        if (returns.size() != 1) {
                            if (returns.size() > 1) {
                                refined.captureBindingIssues.add(
                                        "RUNTIME_METHOD_RETURN_"
                                                + "OCCURRENCE_AMBIGUOUS:"
                                                + method + ":"
                                                + returns.size());
                            }
                            continue;
                        }
                        RuntimeEvent match = returns.get(0);
                        Map<String, Object> exact =
                                new LinkedHashMap<>(binding);
                        exact.put("occurrence", 1);
                        exact.put("occurrenceAuthority",
                                "RUNTIME_EXACT_METHOD_RETURN_OCCURRENCE");
                        exact.put("runtimeCallId", match.callId);
                        exact.put("runtimeEventSeq", match.seq);
                        refined.captureBindings.add(exact);
                        matchedCaptureCount++;
                        continue;
                    }

                    String caller = string(binding.get("callerMethod"));
                    if (!observed.contains(caller)) {
                        continue;
                    }
                    List<RuntimeEvent> matches = evidence
                            .matchingCallArguments(binding);
                    for (RuntimeEvent match : matches) {
                        Map<String, Object> exact =
                                new LinkedHashMap<>(binding);
                        exact.put("occurrence", evidence
                                .callArgumentOccurrence(binding, match));
                        exact.put("occurrenceAuthority",
                                "RUNTIME_EXACT_CALL_ARGUMENT_OCCURRENCE");
                        exact.put("runtimeInvocationId",
                                match.invocationId);
                        exact.put("runtimeEventSeq", match.seq);
                        refined.captureBindings.add(exact);
                        matchedCaptureCount++;
                    }
                }
                if (matchedCaptureCount != 1) {
                    refined.captureBindingsComplete = false;
                    refined.runtimeRefinementComplete = false;
                    String failure;
                    if (matchedCaptureCount == 0) {
                        failure = fieldAssignmentRequested
                                ? "NO_RUNTIME_EXACT_FIELD_ASSIGNMENT_MATCH"
                                : methodReturnRequested
                                ? "NO_RUNTIME_EXACT_METHOD_RETURN_MATCH"
                                : "NO_RUNTIME_EXACT_CALL_ARGUMENT_MATCH";
                    } else {
                        failure = (fieldAssignmentRequested
                                ? "AMBIGUOUS_RUNTIME_FIELD_ASSIGNMENT_MATCH:"
                                : methodReturnRequested
                                ? "AMBIGUOUS_RUNTIME_METHOD_RETURN_MATCH:"
                                : "AMBIGUOUS_RUNTIME_CALL_ARGUMENT_MATCH:")
                                + matchedCaptureCount;
                    }
                    refined.captureBindingIssues.add(failure);
                }
            } else {
                refined.captureBindings.addAll(copyRows(captureBindings));
            }
        }

        private boolean mutationCaptureDischargeReady(
                StaticOutputSlice refined, InstanceEvidence evidence,
                Set<String> observed, String heapEffectCaptureInput) {
            if (!captureBindingsRequired || captureBindingsComplete
                    || heapEffectCaptureInput.isEmpty()
                    || !evidence.runtimePathEvidenceComplete
                    || !refined.structuralComplete
                    || !refined.runtimeRefinementComplete
                    || !refined.runtimeOnlyMethods.isEmpty()
                    || !refined.unresolvedInputs.isEmpty()
                    || !refined.unresolvedInputProvenanceComplete
                    || !refined.requestedStateTransformerContractComplete) {
                return false;
            }

            // A retained exact capture is authoritative and must not be
            // replaced by heap effects.  Capture declarations belonging only
            // to methods excluded as static alternatives are irrelevant to
            // this concrete runtime path.
            for (Map<String, Object> binding : captureBindings) {
                String method = firstNonBlank(string(binding.get("method")),
                        string(binding.get("callerMethod")));
                if (method.isEmpty() || observed.contains(method)) {
                    return false;
                }
            }

            Set<String> allMutationSites = new LinkedHashSet<>();
            for (Map<String, Object> obligation
                    : requestedStateTransformerObligations) {
                if ("field_mutation".equals(string(obligation.get("kind")))) {
                    allMutationSites.add(string(obligation.get("siteId")));
                }
            }
            Set<String> retainedMutationSites = new LinkedHashSet<>();
            for (Map<String, Object> obligation
                    : refined.requestedStateTransformerObligations) {
                if (!"field_mutation".equals(string(obligation.get("kind")))) {
                    return false;
                }
                retainedMutationSites.add(string(obligation.get("siteId")));
            }
            if (retainedMutationSites.isEmpty()
                    || retainedMutationSites.contains("")
                    || captureBindingIssues.isEmpty()) {
                return false;
            }

            String prefix =
                    "REQUESTED_TRANSFORMER_HAS_NO_EXACT_FIELD_ASSIGNMENT_RHS:";
            Set<String> retainedIssueSites = new LinkedHashSet<>();
            for (String issue : captureBindingIssues) {
                if (!issue.startsWith(prefix)) {
                    return false;
                }
                String site = issue.substring(prefix.length());
                if (!allMutationSites.contains(site)) {
                    return false;
                }
                if (retainedMutationSites.contains(site)
                        && !retainedIssueSites.add(site)) {
                    return false;
                }
            }
            return retainedIssueSites.equals(retainedMutationSites);
        }

        /**
         * Returns the one exact requested-field pre-state input that can be
         * threaded through the existing heap-effect SSA model.  This is only
         * a capture-plan discharge: the importer must still prove every
         * retained mutation is a supported, runtime-observed transformer.
         */
        private String heapEffectCaptureDischargeInput(
                List<Map<String, Object>> retainedBindings,
                Set<String> retainedPorts) {
            if (requestedStateTransformerContractVersion != 1
                    || !requestedStateTransformerContractApplicable
                    || !requestedStateTransformerContractComplete
                    || !outputPort.equals(
                    requestedStateTransformerContractOutputPort)
                    || !outputCell.equals(
                    requestedStateTransformerContractOutputCell)
                    || !"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1"
                    .equals(requestedStateTransformerContractAuthority)
                    || requestedStateTransformerObligations.isEmpty()
                    || !supportedMapStateCell(outputCell)) {
                return "";
            }
            for (Map<String, Object> obligation
                    : requestedStateTransformerObligations) {
                if (!"field_mutation".equals(string(obligation.get("kind")))
                        || !"HEAP_WRITE".equals(string(obligation.get(
                        "transferKind")))
                        || !outputCell.equals(string(obligation.get(
                        "targetCell")))
                        || string(obligation.get("siteId")).isEmpty()
                        || string(obligation.get("method")).isEmpty()) {
                    return "";
                }
            }
            String match = "";
            for (Map<String, Object> binding : retainedBindings) {
                if (!outputCell.equals(string(binding.get(
                        "dependencyCell")))
                        || !"EXACT_CELL_IDENTITY".equals(string(binding.get(
                        "bindingAuthority")))) {
                    continue;
                }
                String port = string(binding.get("inputPort"));
                if (port.isEmpty() || !retainedPorts.contains(port)
                        || !match.isEmpty()) {
                    return "";
                }
                match = port;
            }
            return match;
        }

        private static boolean supportedMapStateCell(String cell) {
            FieldCell field = fieldCell(cell);
            if (!field.declaredSignature) {
                return false;
            }
            String type = field.type;
            return "java.util.Map".equals(type)
                    || "java.util.SortedMap".equals(type)
                    || "java.util.NavigableMap".equals(type)
                    || "java.util.HashMap".equals(type)
                    || "java.util.LinkedHashMap".equals(type)
                    || "java.util.TreeMap".equals(type)
                    || "java.util.Hashtable".equals(type)
                    || "java.util.WeakHashMap".equals(type)
                    || "java.util.IdentityHashMap".equals(type)
                    || "java.util.concurrent.ConcurrentMap".equals(type)
                    || "java.util.concurrent.ConcurrentHashMap".equals(type)
                    || "java.util.concurrent.ConcurrentNavigableMap".equals(
                    type)
                    || "java.util.concurrent.ConcurrentSkipListMap".equals(
                    type);
        }

        private Map<String, Object> toMap() {
            Map<String, Object> result = object(
                    "outputPort", outputPort,
                    "outputCell", outputCell,
                    "inputPorts", new ArrayList<>(inputPorts),
                    "inputBindings", inputBindings,
                    "inputAliasCanonicalizations",
                    inputAliasCanonicalizations,
                    "inputAliasCanonicalizationIssues",
                    inputAliasCanonicalizationIssues,
                    "inputAliasCanonicalizationComplete",
                    inputAliasCanonicalizationIssues.isEmpty(),
                    "methods", new ArrayList<>(methods),
                    "sites", new ArrayList<>(sites),
                    "causalEdgeIds", causalEdgeIds,
                    "causalEdges", causalEdges,
                    "causalEdgeCount", causalEdgeIds.size(),
                    "heapInitializers", heapInitializers,
                    "captureBindings", captureBindings,
                    "captureBindingsRequired", captureBindingsRequired,
                    "captureBindingsComplete", captureBindingsComplete,
                    "captureBindingIssues", captureBindingIssues,
                    "captureDischargedByHeapEffectTransformer",
                    captureDischargedByHeapEffectTransformer,
                    "captureDischargeInputPort",
                    captureDischargeInputPort,
                    "captureDischargeOutputPort", outputPort,
                    "captureDischargeOutputCell", outputCell,
                    "captureDischargeAuthority",
                    captureDischargeAuthority,
                    "containerElementFieldBindings",
                    containerElementFieldBindings,
                    "unresolvedInputs", unresolvedInputs,
                    "unresolvedInputDetails", unresolvedInputDetails,
                    "unresolvedInputProvenanceComplete",
                    unresolvedInputProvenanceComplete,
                    "structuralComplete", structuralComplete,
                    "regionTruncated", regionTruncated,
                    "truncated", sliceTruncated,
                    "methodBudgetTruncated", methodBudgetTruncated,
                    "causalCellBudgetTruncated",
                    causalCellBudgetTruncated,
                    "truncationReasons", structuralIssues,
                    "complete", complete,
                    "selection", selection);
            if (requestedStateTransformerContractVersion > 0) {
                result.put("requestedStateTransformerContractVersion",
                        requestedStateTransformerContractVersion);
                result.put("requestedStateTransformerContractApplicable",
                        requestedStateTransformerContractApplicable);
                result.put("requestedStateTransformerContractOutputPort",
                        requestedStateTransformerContractOutputPort);
                result.put("requestedStateTransformerContractOutputCell",
                        requestedStateTransformerContractOutputCell);
                result.put("requestedStateTransformerObligations",
                        requestedStateTransformerObligations);
                result.put("requestedStateTransformerObligationCount",
                        requestedStateTransformerObligationCount);
                result.put("requestedStateTransformerContractIssues",
                        requestedStateTransformerContractIssues);
                result.put("requestedStateTransformerContractComplete",
                        requestedStateTransformerContractComplete);
                result.put("requestedStateTransformerContractAuthority",
                        requestedStateTransformerContractAuthority);
            }
            if (runtimeRefined) {
                result.put("runtimeRefined", true);
                result.put("runtimeRefinementAuthority",
                        "OBSERVED_REGION_CALL_TREE_AND_STATIC_DEPENDENCY_METHOD_PROVENANCE");
                result.put("runtimeRefinementComplete",
                        runtimeRefinementComplete);
                result.put("staticInputPorts",
                        new ArrayList<>(staticInputPorts));
                result.put("staticMethods", new ArrayList<>(staticMethods));
                result.put("staticSites", new ArrayList<>(staticSites));
                result.put("staticCausalEdgeIds", staticCausalEdgeIds);
                result.put("excludedAlternativeInputPorts",
                        new ArrayList<>(excludedInputPorts));
                result.put("excludedAlternativeMethods",
                        new ArrayList<>(excludedMethods));
                result.put("runtimeObservedMethodsOutsideStaticSlice",
                        new ArrayList<>(runtimeOnlyMethods));
                result.put("excludedAlternativeSites",
                        new ArrayList<>(excludedSites));
                result.put("excludedPathAlternativeSites",
                        new ArrayList<>(excludedPathAlternativeSites));
                result.put("excludedAlternativeUnresolvedInputs",
                        excludedAlternativeUnresolvedInputs);
                result.put("excludedAlternativeCausalEdgeIds",
                        excludedCausalEdgeIds);
                result.put("prestateElisions", prestateElisions);
            }
            return result;
        }
    }

    private static final class StaticPort {
        private final String portId;
        private final String cell;
        private final String sourceKind;
        private final String projection;
        private final String kind;
        private final Map<String, Object> materializationMetadata;

        private StaticPort(String portId, String cell, String sourceKind,
                           String projection, String kind) {
            this(portId, cell, sourceKind, projection, kind,
                    Collections.<String, Object>emptyMap());
        }

        private StaticPort(String portId, String cell, String sourceKind,
                           String projection, String kind,
                           Map<String, Object> materializationMetadata) {
            this.portId = safe(portId);
            this.cell = safe(cell);
            this.sourceKind = safe(sourceKind);
            this.projection = safe(projection);
            this.kind = safe(kind);
            this.materializationMetadata = new LinkedHashMap<>(
                    materializationMetadata == null
                            ? Collections.<String, Object>emptyMap()
                            : materializationMetadata);
        }

        private static Map<String, Object> materializationMetadata(
                String json) {
            Map<String, Object> result = new LinkedHashMap<>();
            for (String field : new String[]{"javaType", "inputJavaType",
                    "field", "leafFieldSignature", "leafField",
                    "leafOwnerClass", "accessFieldSignature",
                    "accessField", "accessOwnerClass", "accessFieldType",
                    "bindingMode", "method", "local", "accessMethod",
                    "accessSiteId", "accessSiteAuthority",
                    "accessorCallerMethod", "accessorCallSiteId",
                    "accessorDeclaredCallee",
                    "accessorCallSiteAuthority",
                    "accessorImplementationMethod",
                    "accessorImplementationAuthority"}) {
                String value = jsonString(json, field);
                if (!value.isEmpty()) result.put(field, value);
            }
            int accessUnitIndex = jsonInt(json, "accessUnitIndex", -1);
            if (accessUnitIndex >= 0) {
                result.put("accessUnitIndex", accessUnitIndex);
            }
            int accessorCallUnitIndex = jsonInt(json,
                    "accessorCallUnitIndex", -1);
            if (accessorCallUnitIndex >= 0) {
                result.put("accessorCallUnitIndex",
                        accessorCallUnitIndex);
            }
            List<String> path = jsonStringArray(json, "fieldPath");
            if (!path.isEmpty()) result.put("fieldPath", path);
            List<Map<String, Object>> declarations = new ArrayList<>();
            for (String declaration : jsonObjectArray(json,
                    "fieldPathLeafDeclarations")) {
                String signature = jsonString(declaration,
                        "fieldSignature");
                List<String> declarationPath = jsonStringArray(
                        declaration, "fieldPath");
                if (!signature.isEmpty() && !declarationPath.isEmpty()) {
                    declarations.add(object(
                            "fieldPath", declarationPath,
                            "fieldSignature", signature,
                            "declaredFieldOwnerClass", jsonString(
                            declaration, "declaredFieldOwnerClass"),
                            "declaredFieldType", jsonString(declaration,
                            "declaredFieldType"),
                            "complete", jsonBoolean(declaration,
                            "complete", true)));
                }
            }
            if (!declarations.isEmpty()) {
                result.put("fieldPathLeafDeclarations", declarations);
            }
            return result;
        }
    }

    /** Exact-enough identity for a materializable Java field. */
    private static final class FieldCell {
        private final String owner;
        private final String type;
        private final String name;
        private final boolean declaredSignature;

        private FieldCell(String owner, String type, String name,
                          boolean declaredSignature) {
            this.owner = safe(owner).trim();
            this.type = safe(type).trim();
            this.name = safe(name).trim();
            this.declaredSignature = declaredSignature;
        }

        private boolean materializable() {
            return !owner.isEmpty() && !name.isEmpty();
        }

        private static FieldCell unresolved() {
            return new FieldCell("", "", "", false);
        }

        private String signature() {
            return declaredSignature
                    ? "<" + owner + ": " + type + " " + name + ">"
                    : "";
        }
    }

    private static final class BranchPolicy {
        private final String siteId;
        private final String policy;
        private final String guard;
        private final Boolean requiredOutcome;
        private final String role;

        private BranchPolicy(String siteId, String policy, String guard,
                             Boolean requiredOutcome, String role) {
            this.siteId = safe(siteId);
            this.policy = safe(policy);
            this.guard = safe(guard);
            this.requiredOutcome = requiredOutcome;
            this.role = safe(role);
        }
    }

    private static final class RootCandidate {
        private final MethodEvent event;
        private final boolean staticRootObserved;

        private RootCandidate(MethodEvent event, boolean staticRootObserved) {
            this.event = event;
            this.staticRootObserved = staticRootObserved;
        }
    }

    private static int parameterIndex(String cell) {
        Matcher matcher = PARAMETER.matcher(safe(cell));
        return matcher.find() ? parseInt(matcher.group(1), -1) : -1;
    }

    private static String declaredJavaType(String cell) {
        FieldCell field = fieldCell(cell);
        if (field.declaredSignature && !field.type.isEmpty()) {
            return field.type;
        }
        Matcher parameter = Pattern.compile(
                "\\.param\\d+:([^#]+)").matcher(safe(cell));
        return parameter.find() ? parameter.group(1).trim() : "";
    }

    private static FieldCell fieldCell(String value) {
        String cell = safe(value);
        Matcher declared = FIELD_SIGNATURE.matcher(cell);
        if (declared.find()) {
            return new FieldCell(declared.group(1), declared.group(2),
                    declared.group(3), true);
        }

        Matcher projection = FIELD_PROJECTION.matcher(cell);
        if (!projection.find()) {
            return FieldCell.unresolved();
        }
        String name = projection.group(1).trim();
        int projectionAt = projection.start();
        if (cell.startsWith("@this: ")) {
            return new FieldCell(cell.substring("@this: ".length(),
                    projectionAt), "", name, false);
        }

        Matcher parameter = Pattern.compile(
                "\\.param\\d+:([^#]+)#field:").matcher(cell);
        if (parameter.find()) {
            return new FieldCell(parameter.group(1), "", name, false);
        }

        if (cell.substring(0, projectionAt).endsWith(">.return")) {
            String returnedMethod = methodInCell(cell);
            String returnedType = methodReturnType(returnedMethod);
            if (!returnedType.isEmpty()) {
                return new FieldCell(returnedType, "", name, false);
            }
        }
        // A method local does not carry its declared runtime type.  Matching
        // it by the projected field name alone would conflate unrelated
        // owners (for example two distinct allKeys fields), so fail closed.
        return FieldCell.unresolved();
    }

    private static String methodReturnType(String signature) {
        String value = safe(signature);
        int colon = value.indexOf(':');
        int open = value.lastIndexOf('(');
        int methodSeparator = open < 0 ? -1 : value.lastIndexOf(' ', open);
        if (colon < 0 || methodSeparator <= colon) {
            return "";
        }
        return value.substring(colon + 1, methodSeparator).trim();
    }

    private static boolean sameField(FieldCell left, FieldCell right) {
        if (left == null || right == null
                || !left.materializable() || !right.materializable()
                || !left.owner.equals(right.owner)
                || !left.name.equals(right.name)) {
            return false;
        }
        return !left.declaredSignature || !right.declaredSignature
                || left.type.equals(right.type);
    }

    private static String threadRole(String threadName) {
        String value = safe(threadName);
        String lower = value.toLowerCase(Locale.ROOT);
        if (lower.contains("dataxceiver")) {
            return "DataXceiver";
        }
        if (lower.contains("ipc") || lower.contains("rpc")) {
            return "RPCHandler";
        }
        if (lower.contains("updater") || lower.contains("monitor")) {
            return "BackgroundUpdater";
        }
        if (lower.contains("dispatcher")) {
            return "Dispatcher";
        }
        return value.isEmpty() ? "unknown" : value;
    }

    private static List<MethodEvent> sortedMethods(List<MethodEvent> values) {
        List<MethodEvent> result = new ArrayList<>();
        if (values != null) {
            result.addAll(values);
        }
        result.sort(Comparator.comparingLong(value -> value.seq));
        return result;
    }

    private static List<RuntimeEvent> sortedRuntime(List<RuntimeEvent> values) {
        List<RuntimeEvent> result = new ArrayList<>();
        if (values != null) {
            result.addAll(values);
        }
        result.sort(Comparator.comparingLong(value -> value.seq));
        return result;
    }

    private static List<FieldAccessEvent> sortedFields(List<FieldAccessEvent> values) {
        List<FieldAccessEvent> result = new ArrayList<>();
        if (values != null) {
            result.addAll(values);
        }
        result.sort(Comparator.comparingLong(value -> value.seq));
        return result;
    }

    private static <T> void add(Map<String, List<T>> map, String key, T value) {
        map.computeIfAbsent(safe(key), ignored -> new ArrayList<>()).add(value);
    }

    private static <T> List<T> values(List<T> values) {
        return values == null ? Collections.emptyList() : values;
    }

    private static Set<String> stringSet(Object value) {
        Set<String> result = new LinkedHashSet<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                String text = string(item);
                if (!text.isEmpty()) {
                    result.add(text);
                }
            }
        }
        return result;
    }

    /** Ordered field paths are semantic; repeated segment names are valid. */
    private static List<String> stringList(Object value) {
        List<String> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                String text = string(item);
                if (!text.isEmpty()) {
                    result.add(text);
                }
            }
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> mapValue(Object value) {
        return value instanceof Map<?, ?>
                ? (Map<String, Object>) value : null;
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> mapRows(Object value) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (!(value instanceof Collection<?>)) {
            return result;
        }
        for (Object item : (Collection<?>) value) {
            if (item instanceof Map<?, ?>) {
                result.add((Map<String, Object>) item);
            }
        }
        return result;
    }

    private static boolean intersects(Collection<String> left,
                                      Collection<String> right) {
        if (left == null || right == null) {
            return false;
        }
        for (String value : left) {
            if (right.contains(value)) {
                return true;
            }
        }
        return false;
    }

    private static List<String> difference(Collection<String> expected,
                                           Collection<String> observed) {
        Set<String> result = new LinkedHashSet<>(expected);
        result.removeAll(observed);
        return sorted(result);
    }

    private static List<String> sorted(Collection<String> values) {
        List<String> result = new ArrayList<>();
        if (values != null) {
            result.addAll(values);
        }
        Collections.sort(result);
        return result;
    }

    private static <T> List<T> limited(List<T> values, int limit) {
        return values.size() <= limit
                ? values : new ArrayList<>(values.subList(0, limit));
    }

    private static void copy(Map<String, Object> from, Map<String, Object> to,
                             String... keys) {
        for (String key : keys) {
            if (from.containsKey(key)) {
                to.put(key, from.get(key));
            }
        }
    }

    private static String safeToken(String value) {
        return safe(value).replaceAll("[^A-Za-z0-9_.-]+", "_");
    }

    private static String string(Object value) {
        return value == null ? "" : String.valueOf(value);
    }

    private static String safe(String value) {
        return value == null ? "" : value;
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

    private static int parseInt(String value, int fallback) {
        try {
            return Integer.parseInt(value);
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static Map<String, Object> object(Object... values) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index + 1 < values.length; index += 2) {
            result.put(String.valueOf(values[index]), values[index + 1]);
        }
        return result;
    }

    private static String jsonl(List<Map<String, Object>> rows) {
        StringBuilder builder = new StringBuilder();
        for (Map<String, Object> row : rows) {
            builder.append(json(row)).append('\n');
        }
        return builder.toString();
    }

    private static String json(Object value) {
        if (value == null) {
            return "null";
        }
        if (value instanceof String) {
            return quote((String) value);
        }
        if (value instanceof Number || value instanceof Boolean) {
            return String.valueOf(value);
        }
        if (value instanceof Map) {
            StringBuilder builder = new StringBuilder("{");
            boolean first = true;
            for (Map.Entry<?, ?> entry : ((Map<?, ?>) value).entrySet()) {
                if (!first) {
                    builder.append(',');
                }
                first = false;
                builder.append(quote(String.valueOf(entry.getKey()))).append(':')
                        .append(json(entry.getValue()));
            }
            return builder.append('}').toString();
        }
        if (value instanceof Collection) {
            StringBuilder builder = new StringBuilder("[");
            boolean first = true;
            for (Object item : (Collection<?>) value) {
                if (!first) {
                    builder.append(',');
                }
                first = false;
                builder.append(json(item));
            }
            return builder.append(']').toString();
        }
        return quote(String.valueOf(value));
    }

    private static String quote(String value) {
        StringBuilder builder = new StringBuilder("\"");
        for (int index = 0; index < safe(value).length(); index++) {
            char ch = value.charAt(index);
            if (ch == '\\' || ch == '"') {
                builder.append('\\').append(ch);
            } else if (ch == '\n') {
                builder.append("\\n");
            } else if (ch == '\r') {
                builder.append("\\r");
            } else if (ch == '\t') {
                builder.append("\\t");
            } else {
                builder.append(ch);
            }
        }
        return builder.append('"').toString();
    }

    private static String jsonString(String json, String field) {
        Pattern pattern = Pattern.compile("\\\"" + Pattern.quote(field)
                + "\\\"\\s*:\\s*\\\"((?:\\\\.|[^\\\"\\\\])*)\\\"");
        Matcher matcher = pattern.matcher(safe(json));
        return matcher.find() ? unescape(matcher.group(1)) : "";
    }

    private static boolean jsonHasField(String json, String field) {
        return Pattern.compile("\\\"" + Pattern.quote(field)
                + "\\\"\\s*:").matcher(safe(json)).find();
    }

    private static boolean jsonBoolean(String json, String field,
                                       boolean fallback) {
        Pattern pattern = Pattern.compile("\\\"" + Pattern.quote(field)
                + "\\\"\\s*:\\s*(true|false)");
        Matcher matcher = pattern.matcher(safe(json));
        return matcher.find() ? Boolean.parseBoolean(matcher.group(1)) : fallback;
    }

    private static Boolean jsonOptionalBoolean(String json, String field) {
        Pattern pattern = Pattern.compile("\\\"" + Pattern.quote(field)
                + "\\\"\\s*:\\s*(true|false)");
        Matcher matcher = pattern.matcher(safe(json));
        return matcher.find() ? Boolean.valueOf(matcher.group(1)) : null;
    }

    private static int jsonInt(String json, String field, int fallback) {
        Pattern pattern = Pattern.compile("\\\"" + Pattern.quote(field)
                + "\\\"\\s*:\\s*(-?[0-9]+)");
        Matcher matcher = pattern.matcher(safe(json));
        return matcher.find() ? parseInt(matcher.group(1), fallback) : fallback;
    }

    private static List<String> jsonStringArray(String json, String field) {
        String raw = jsonArray(json, field);
        if (raw.isEmpty()) {
            return Collections.emptyList();
        }
        List<String> result = new ArrayList<>();
        Matcher matcher = Pattern.compile("\\\"((?:\\\\.|[^\\\"\\\\])*)\\\"")
                .matcher(raw);
        while (matcher.find()) {
            result.add(unescape(matcher.group(1)));
        }
        return result;
    }

    private static List<String> jsonObjectArray(String json, String field) {
        String raw = jsonArray(json, field);
        if (raw.isEmpty()) {
            return Collections.emptyList();
        }
        List<String> result = new ArrayList<>();
        int depth = 0;
        int start = -1;
        boolean string = false;
        boolean escaped = false;
        for (int index = 0; index < raw.length(); index++) {
            char ch = raw.charAt(index);
            if (string) {
                if (escaped) {
                    escaped = false;
                } else if (ch == '\\') {
                    escaped = true;
                } else if (ch == '"') {
                    string = false;
                }
                continue;
            }
            if (ch == '"') {
                string = true;
            } else if (ch == '{') {
                if (depth++ == 0) {
                    start = index;
                }
            } else if (ch == '}' && depth > 0 && --depth == 0 && start >= 0) {
                result.add(raw.substring(start, index + 1));
                start = -1;
            }
        }
        return result;
    }

    private static String jsonArray(String json, String field) {
        String source = safe(json);
        int fieldAt = source.indexOf('"' + field + '"');
        if (fieldAt < 0) {
            return "";
        }
        int start = source.indexOf('[', fieldAt + field.length() + 2);
        if (start < 0) {
            return "";
        }
        int depth = 0;
        boolean string = false;
        boolean escaped = false;
        for (int index = start; index < source.length(); index++) {
            char ch = source.charAt(index);
            if (string) {
                if (escaped) {
                    escaped = false;
                } else if (ch == '\\') {
                    escaped = true;
                } else if (ch == '"') {
                    string = false;
                }
                continue;
            }
            if (ch == '"') {
                string = true;
            } else if (ch == '[') {
                depth++;
            } else if (ch == ']' && --depth == 0) {
                return source.substring(start, index + 1);
            }
        }
        return "";
    }

    private static String unescape(String value) {
        StringBuilder builder = new StringBuilder();
        boolean escaped = false;
        for (int index = 0; index < safe(value).length(); index++) {
            char ch = value.charAt(index);
            if (!escaped && ch == '\\') {
                escaped = true;
                continue;
            }
            if (escaped) {
                if (ch == 'n') {
                    builder.append('\n');
                } else if (ch == 'r') {
                    builder.append('\r');
                } else if (ch == 't') {
                    builder.append('\t');
                } else {
                    builder.append(ch);
                }
                escaped = false;
            } else {
                builder.append(ch);
            }
        }
        if (escaped) {
            builder.append('\\');
        }
        return builder.toString();
    }
}
