package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.SymbolicEnvironment;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
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
    private static final Pattern PARAMETER_TYPE = Pattern.compile(
            "\\.param\\d+:([^#]+)");
    private static final Pattern PARAMETER_FIELD_PROJECTION = Pattern.compile(
            "\\.param\\d+:([^#]+)#field:");
    private static final Pattern LOCAL_CELL = Pattern.compile(
            "^(<.+>)::([^#]+)(?:#.*)?$");
    private static final Pattern FIELD_SIGNATURE = Pattern.compile(
            "<([^:]+):\\s+([^()<>]+)\\s+([^\\s()>]+)>");
    private static final Pattern FIELD_PROJECTION = Pattern.compile(
            "#field:([^#@]+)");
    private static final Pattern GETTER_IN_GUARD = Pattern.compile(
            "\\b((?:get|is)[A-Z][A-Za-z0-9_]*)\\s*\\(");
    private static final Pattern UNIT_SITE_SUFFIX = Pattern.compile(
            "#u[0-9]+");
    private static final Pattern UNSAFE_TOKEN_CHARACTERS = Pattern.compile(
            "[^A-Za-z0-9_.-]+");
    private static final Pattern JSON_QUOTED_STRING = Pattern.compile(
            "\\\"((?:\\\\.|[^\\\"\\\\])*)\\\"");
    private static final Pattern DEFAULT_EXECUTOR_THREAD_NAME =
            Pattern.compile("^pool-[0-9]+-thread-([0-9]+)$");
    private static final Pattern DEFAULT_OBJECT_IDENTITY_THREAD_NAME =
            Pattern.compile("^([A-Za-z_$][A-Za-z0-9_$.]*?)@"
                    + "[0-9a-fA-F]+$");
    private static final String VM_INTRINSIC_DEFERRED_AUTHORITY =
            "EXACT_VM_INTRINSIC_PLACEHOLDER_SCHEDULER_VALIDATION_V1";
    private static final String CALL_RETURN_DEFERRED_AUTHORITY =
            "AUTHORITATIVE_SCHEDULER_DEFINITION_INDEX_REQUIRED_V1";
    private static final String UNRESOLVED_INPUT_PROVENANCE_AUTHORITY =
            "STATIC_EXACT_DEPENDENCY_METHOD_CONSUMER_SET_V1";
    static final String ROOT_ARGUMENT_PREDICATE_KIND =
            "EXACT_RUNTIME_TYPE";
    static final String RUNTIME_UNIQUE_EXACT_FIELD_READ_SITE_AUTHORITY =
            "RUNTIME_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1";
    static final String STATIC_INPUT_FIELD_PROJECTION_AUTHORITY =
            "STATIC_EXACT_FIELD_PROJECTION_AND_RESOLVED_DECLARATION_V1";
    static final String STATIC_INPUT_FIELD_PROJECTION_DECLARATION_AUTHORITY =
            "SOOT_RESOLVED_DECLARATION_HIERARCHY";
    private static final int STATIC_DATAFLOW_EDGE_SCHEMA_VERSION = 2;
    private static final int STATIC_REGION_SCHEMA_VERSION = 2;
    private static final String STATIC_DATAFLOW_ASSERTABLE = "ASSERTABLE";
    private RuntimeRegionPlanner() {
    }

    static Result plan(File regionFile, File regionEdgeFile,
                       File staticGraphFile, List<MethodEvent> methods,
                       List<RuntimeEvent> runtimeEvents,
                       List<FieldAccessEvent> fieldEvents) {
        if (staticGraphFile == null || !staticGraphFile.isFile()) {
            throw new IllegalArgumentException(
                    "runtime planning requires the frozen static graph");
        }
        Result result = new Result();
        List<StaticRegion> regions = readRegions(regionFile);
        List<StaticRegionEdge> regionEdges = readRegionEdges(regionEdgeFile);
        regionEdges = expandMappingOnlyProtocolProducerRegions(regions,
                regionEdges);
        StaticProjectionIndex staticProjections =
                readStaticProjectionIndex(staticGraphFile);
        resolveStaticCausalEdgeReferences(regions, staticProjections);
        List<MethodEvent> methodEvents = sortedMethods(methods);
        List<RuntimeEvent> executions = sortedRuntime(runtimeEvents);
        List<FieldAccessEvent> fields = sortedFields(fieldEvents);
        RootArgumentRuntimeTypeIndex rootArgumentRuntimeTypes =
                RootArgumentRuntimeTypeIndex.build(executions);
        RuntimeTraceIndex trace = RuntimeTraceIndex.build(methodEvents,
                executions, fields);
        Map<Long, MethodEvent> calls = trace.methodsByCall;
        Map<String, List<MethodEvent>> methodsBySignature =
                trace.methodsBySignature;
        RuntimeFieldAccessIndex runtimeFieldAccesses =
                RuntimeFieldAccessIndex.build(fields, calls);

        int instanceIndex = 0;
        int activationIndex = 0;
        Map<String, List<InstanceEvidence>> evidenceByRegion = new LinkedHashMap<>();
        Map<String, List<InstanceEvidence>> sharedStateEvidenceByRegion =
                new LinkedHashMap<>();
        List<InstanceEvidence> allInstanceEvidence = new ArrayList<>();

        outer:
        for (StaticRegion region : regions) {
            List<RootCandidate> roots = rootCandidates(region, regions,
                    methodsBySignature, calls);
            if (roots.isEmpty()) {
                continue;
            }
            for (RootCandidate candidate : roots) {
                if (instanceIndex >= MAX_INSTANCES) {
                    break outer;
                }
                MethodEvent root = candidate.event;
                ContainedCallSelection callSelection =
                        trace.containedCalls(root);
                Set<Long> containedCalls = callSelection.calls;
                Set<String> observedMethods = new LinkedHashSet<>();
                List<MethodEvent> containedMethodEvents =
                        trace.methods(containedCalls);
                for (MethodEvent event : containedMethodEvents) {
                    observedMethods.add(event.method);
                }

                int ordinal = trace.invocationOrdinal(root);
                int ordinalWithinContext =
                        trace.invocationOrdinalWithinContext(root);
                Map<String, Object> rootArgumentSelector =
                        runtimeRootArgumentSelector(root, methodEvents,
                                rootArgumentRuntimeTypes);
                String instanceId = region.regionId + "@" + safeToken(root.test)
                        + "#call" + root.callId;

                List<RuntimeEvent> containedRuntime =
                        trace.runtimeEvents(containedCalls);
                List<FieldAccessEvent> containedFields =
                        trace.fieldEvents(containedCalls);
                PathSignatureSelection pathSelection = pathSignature(
                        containedRuntime);
                boolean runtimePathEvidenceComplete = !callSelection.truncated
                        && !pathSelection.truncated;
                List<String> runtimeGaps = new ArrayList<>();
                if (callSelection.truncated) {
                    runtimeGaps.add("CONTAINED_CALL_TREE_LIMIT_EXCEEDED");
                }
                if (pathSelection.truncated) {
                    runtimeGaps.add("PATH_SIGNATURE_LIMIT_EXCEEDED");
                }
                ConcreteDemandSlice demandSlice = staticProjections.reslice(
                        region, runtimePathEvidenceComplete,
                        observedMethods, root.method, root, containedCalls,
                        runtimeFieldAccesses);
                List<StaticPort> concreteInputs = demandSlice.inputs(region);
                List<Map<String, Object>> inputObjects = inputObservations(
                        region, concreteInputs, root,
                        containedRuntime,
                        containedFields, containedMethodEvents);
                List<Map<String, Object>> symbolize = symbolizeActions(
                        region, concreteInputs, root, inputObjects,
                        containedRuntime, containedFields);
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
                boolean demandHasSymbolicPotential = !concreteInputs.isEmpty()
                        || region.inputs.isEmpty() || region.branches.isEmpty();
                boolean boundaryReady = inputsResolved && branchesResolved
                        && region.inputSelectionComplete
                        && runtimePathEvidenceComplete
                        && symbolizeActionsReady;
                boolean replayable = anchorObserved
                        && runtimePathEvidenceComplete;
                boolean symbolicReady = replayable && boundaryReady;
                if (!demandHasSymbolicPotential) {
                    symbolicReady = false;
                }

                InstanceEvidence instanceEvidence = new InstanceEvidence(
                        instanceId, region, root, containedCalls,
                        containedMethodEvents, containedRuntime,
                        containedFields, observedMethods,
                        portIds(concreteInputs), demandSlice,
                        runtimePathEvidenceComplete,
                        !callSelection.truncated);
                allInstanceEvidence.add(instanceEvidence);
                if (!callSelection.truncated && !containedFields.isEmpty()) {
                    // Exact shared-state event correlation does not consume
                    // the bounded branch signature. Keep these instances in a
                    // separate pool so a long-running outer loop cannot hide
                    // a precise contained FIELD_READ -> mutator -> FIELD_READ
                    // witness, while every other edge kind remains fail-closed
                    // on complete runtime path evidence.
                    add(sharedStateEvidenceByRegion, region.regionId,
                            instanceEvidence);
                }
                if (runtimePathEvidenceComplete) {
                    add(evidenceByRegion, region.regionId,
                            instanceEvidence);
                }

                Map<String, Object> activation = object(
                        "activationId", "ACT." + activationIndex++,
                        "regionInstanceId", instanceId,
                        "regionId", region.regionId,
                        "test", root.test,
                        "rootSelector", rootSelector(root, ordinal,
                                ordinalWithinContext,
                                rootArgumentSelector),
                        "rootCallId", root.callId,
                        "runtimeDefinitionMethods",
                        demandSlice.definitionMethods(observedMethods),
                        "targetMethod", region.anchorMethod,
                        "captureGoal", object(
                                "kind", "TARGET_BRANCH",
                                "scope", "ONE_DIRECTED_BRANCH"),
                        "admission", admission(replayable, symbolicReady,
                                replayable
                                        ? "RUNTIME_SELECTED_ROOT_REPLAY"
                                        : "NO_VALIDATED_RUNTIME_PATH",
                                runtimeGaps, pathSelection.truncated,
                                callSelection.truncated),
                        "symbolize", symbolize,
                        "branches", branchPlan);
                result.activations.add(activation);
                instanceIndex++;
            }
        }

        RuntimeRelationEvidenceCache relationEvidence =
                new RuntimeRelationEvidenceCache();
        collectConfirmedExternalInputPromotions(regionEdges,
                evidenceByRegion, sharedStateEvidenceByRegion,
                staticProjections, relationEvidence);
        refreshPromotedConcreteInputRows(allInstanceEvidence, result);

        List<UpstreamEdgeBinding> edgeBindings = new ArrayList<>();
        validateRegionEdges(regionEdges, evidenceByRegion,
                sharedStateEvidenceByRegion, staticProjections, result,
                edgeBindings, relationEvidence);
        deriveUpstreamActivations(edgeBindings, staticProjections, result);
        refineMapValueElementProjectionActivations(result);
        finalizeOutputClosureArtifacts(result);
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
            for (MethodEvent entry : lineage) {
                if (region.methods.contains(entry.method)) {
                    selected = entry;
                }
            }
            if (selectedCalls.add(selected.callId)) {
                roots.add(new RootCandidate(selected));
            }
        }

        if (!roots.isEmpty()) {
            return roots;
        }

        // Anchors observed elsewhere in the workload are not evidence that a
        // static root reached this anchor. Returning the static root here would
        // turn an unrelated shared-suffix invocation into a false region
        // activation (for example one registration callback as another).
        if (!anchors.isEmpty()) {
            return roots;
        }

        // If the anchor signature is absent from the trace altogether, a
        // partial trace may still contain the candidate entry. Preserve that
        // evidence for diagnostics, without claiming a validated path.
        for (MethodEvent event : values(methodsBySignature.get(region.rootMethod))) {
            if (selectedCalls.add(event.callId)) {
                roots.add(new RootCandidate(event));
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

    private static Map<String, Object> rootSelector(
            MethodEvent root, int globalOrdinal, int contextOrdinal,
            Map<String, Object> arguments) {
        Map<String, Object> result = object("method", root.method);
        if (root.receiverType.isEmpty()) {
            result.put("kind", "GLOBAL_INVOCATION");
            result.put("ordinal", Math.max(1, globalOrdinal));
            if (arguments != null && !arguments.isEmpty()) {
                result.put("arguments", arguments);
            }
            return result;
        }
        result.put("kind", "RECEIVER_CONTEXT");
        result.put("receiverClass", root.receiverType);
        String stableThreadContext = stableRootThreadContext(root.threadName);
        if (!stableThreadContext.isEmpty()) {
            result.put("thread", stableThreadContext);
        }
        result.put("ordinal", Math.max(1, contextOrdinal));
        if (arguments != null && !arguments.isEmpty()) {
            result.put("arguments", arguments);
        }
        return result;
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
            RootArgumentRuntimeTypeIndex runtimeTypes) {
        List<String> parameterTypes = methodParameterTypes(target.method);
        if (parameterTypes.isEmpty()) {
            return Collections.emptyMap();
        }

        Map<Integer, String> observed = runtimeTypes.typesFor(target);
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
                    runtimeTypes, predicates)) {
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
                && stableRootThreadContext(target.threadName).equals(
                stableRootThreadContext(candidate.threadName));
    }

    private static boolean matchesRootArgumentPredicates(
            MethodEvent candidate, RootArgumentRuntimeTypeIndex runtimeTypes,
            List<Map<String, Object>> predicates) {
        Map<Integer, String> observed = runtimeTypes.typesFor(candidate);
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

    private static boolean sameContext(MethodEvent left, MethodEvent right) {
        return left != null && right != null
                && left.tid == right.tid
                && safe(left.process).equals(safe(right.process))
                && safe(left.test).equals(safe(right.test));
    }

    private static PathSignatureSelection pathSignature(
            List<RuntimeEvent> events) {
        int total = 0;
        for (RuntimeEvent event : events) {
            if ("BRANCH".equals(event.kind) && event.hasOutcome) {
                if (++total > MAX_PATH_SIGNATURE_EVENTS) {
                    return new PathSignatureSelection(true);
                }
            }
        }
        return new PathSignatureSelection(false);
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
            StaticRegion region, List<StaticPort> concreteInputs,
            MethodEvent root,
            List<RuntimeEvent> events, List<FieldAccessEvent> fields,
            List<MethodEvent> methods) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (StaticPort port : concreteInputs) {
            String fieldBindingGap = "";
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
                    boolean staticExactSite =
                            authoritativeStaticFieldReadSite(port, field);
                    boolean runtimeExactSite = !staticExactSite
                            && uniqueExactContainedFieldRead(fields, port,
                            root, field);
                    boolean protocolFieldRequiresExactSite =
                            "PROTOCOL_INPUT".equals(port.sourceKind);
                    if (!protocolFieldRequiresExactSite || staticExactSite
                            || runtimeExactSite) {
                        observation.put("observed", true);
                        observation.put("location",
                                protocolFieldRequiresExactSite
                                        ? "HEAP_OBJECT_FIELD"
                                        : materializableFieldLocation(port));
                        observation.put("field", field.field);
                        observation.put("fieldReceiverObjectId",
                                field.receiverObjectId);
                        observation.put("valueObjectId", field.valueObjectId);
                        observation.put("primitiveValue", field.primitiveValue);
                        observation.put("accessKind", field.kind);
                        observation.put("fieldEventSeq", field.seq);
                        observation.put("fieldCallId", field.callId);
                        observation.put("fieldEventIdentityAuthority",
                                "CONTAINED_RUNTIME_FIELD_EVENT_SEQ_AND_CALL_ID_V1");
                        if (protocolFieldRequiresExactSite) {
                            observation.put("bindingMode", "FIELD_ACCESS");
                        }
                        if (runtimeExactSite) {
                            observation.put("accessMethod", field.method);
                            observation.put("accessUnitIndex", field.unitIndex);
                            observation.put("accessSiteId", field.siteId);
                            observation.put("accessSiteAuthority",
                                    RUNTIME_UNIQUE_EXACT_FIELD_READ_SITE_AUTHORITY);
                            observation.put("observationAuthority",
                                    RUNTIME_UNIQUE_EXACT_FIELD_READ_SITE_AUTHORITY);
                        }
                    } else {
                        // A concrete value was observed, but selecting an
                        // arbitrary same-field access would let the runtime
                        // hook symbolize a different protocol object. Keep
                        // this as a live-in until an exact unique declared
                        // read site is available.
                        fieldBindingGap =
                                "MISSING_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE";
                    }
                }
            }
            if (!Boolean.TRUE.equals(observation.get("observed"))) {
                AccessorReturnObservation accessor =
                        matchingAccessorReturn(region, port, events);
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
                    observation.put("valueObjectId",
                            accessor.returned.objectId);
                    observation.put("runtimeType",
                            accessor.returned.runtimeType);
                    observation.put("valueFingerprint",
                            accessor.returned.valueFingerprint);
                    observation.put("valueFingerprintComplete",
                            accessor.returned.valueFingerprintComplete);
                    observation.put("valueFingerprintNodes",
                            accessor.returned.valueFingerprintNodes);
                    observation.put("valueFingerprintReason",
                            accessor.returned.valueFingerprintReason);
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
                if (!fieldBindingGap.isEmpty()) {
                    observation.put("fieldBindingGap", fieldBindingGap);
                }
            }
            if (!Boolean.TRUE.equals(observation.get("observed"))
                    && "ENVIRONMENT".equals(port.sourceKind)
                    && SymbolicEnvironment.isCurrentTimeMillisReturn(
                    port.cell)) {
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

    private static boolean authoritativeStaticFieldReadSite(
            StaticPort port, FieldAccessEvent field) {
        if (port == null || field == null || !"FIELD_READ".equals(field.kind)) {
            return false;
        }
        FieldCell expected = fieldCell(port.cell);
        FieldCell actual = fieldCell(field.field);
        String method = string(port.materializationMetadata.get(
                "accessMethod"));
        String site = string(port.materializationMetadata.get(
                "accessSiteId"));
        String authority = string(port.materializationMetadata.get(
                "accessSiteAuthority"));
        int unit = port.materializationMetadata.get("accessUnitIndex")
                instanceof Number ? ((Number) port.materializationMetadata.get(
                "accessUnitIndex")).intValue() : -1;
        return "STATIC_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1".equals(
                authority)
                && expected.declaredSignature
                && actual.declaredSignature
                && expected.signature().equals(actual.signature())
                && unit >= 0
                && method.equals(field.method)
                && unit == field.unitIndex
                && site.equals(method + "#u" + unit)
                && site.equals(field.siteId);
    }

    /**
     * Admits runtime-derived materialization metadata only when one contained
     * non-root read has the complete declared owner/type/name and a canonical
     * method/unit site. This is deliberately stricter than matchingField():
     * its purpose is selecting a bytecode hook, not merely explaining where
     * an input value was observed.
     */
    private static boolean uniqueExactContainedFieldRead(
            List<FieldAccessEvent> fields, StaticPort port,
            MethodEvent root, FieldAccessEvent selected) {
        FieldCell expected = fieldCell(port == null ? "" : port.cell);
        if (!expected.declaredSignature || selected == null
                || !"FIELD_READ".equals(selected.kind)
                || selected.callId == root.callId
                || selected.receiverObjectId == 0
                || selected.unitIndex < 0
                || !selected.siteId.equals(selected.method + "#u"
                + selected.unitIndex)) {
            return false;
        }
        int exactReadCount = 0;
        FieldAccessEvent only = null;
        for (FieldAccessEvent field : values(fields)) {
            FieldCell actual = fieldCell(field.field);
            if (!"FIELD_READ".equals(field.kind)
                    || field.callId == root.callId
                    || field.receiverObjectId == 0
                    || field.unitIndex < 0
                    || !field.siteId.equals(field.method + "#u"
                    + field.unitIndex)
                    || !actual.declaredSignature
                    || !expected.signature().equals(actual.signature())) {
                continue;
            }
            exactReadCount++;
            only = field;
        }
        return exactReadCount == 1 && only == selected;
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
     * Recovers a declared scalar-field observation from the unique exact
     * accessor call when the discovery overlay did not emit the getter
     * body's FIELD_READ.  This is intentionally narrower than a generic
     * call-return fallback: all static accessor metadata must be present and
     * authoritative, the caller/site/callee tuple must match one runtime
     * invocation, and exactly one well-typed return must pair with it.
     * Primitive returns require a parseable primitive value. String returns
     * require an exact runtime type and a complete value fingerprint.
     */
    private static AccessorReturnObservation matchingAccessorReturn(
            StaticRegion region, StaticPort port,
            List<RuntimeEvent> events) {
        FieldCell expected = fieldCell(port.cell);
        if (!expected.declaredSignature
                || !accessorReturnObservableType(expected.type)) {
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
                || !region.methods.contains(caller)) {
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
                        || !wellTypedAccessorReturn(expected.type,
                        returned)) {
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

    private static boolean accessorReturnObservableType(String type) {
        return primitiveType(type) || "java.lang.String".equals(safe(type));
    }

    private static boolean wellTypedAccessorReturn(
            String type, RuntimeEvent returned) {
        if (primitiveType(type)) {
            return exactPrimitiveValue(type, returned.primitiveValue);
        }
        return "java.lang.String".equals(type)
                && type.equals(returned.runtimeType)
                && returned.objectId != 0
                && returned.valueFingerprintComplete
                && !returned.valueFingerprint.isEmpty()
                && returned.valueFingerprintNodes > 0;
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
            StaticRegion region, List<StaticPort> concreteInputs,
            MethodEvent root,
            List<Map<String, Object>> inputObjects,
            List<RuntimeEvent> runtimeEvents,
            List<FieldAccessEvent> fieldEvents) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (int index = 0; index < concreteInputs.size(); index++) {
            StaticPort port = concreteInputs.get(index);
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
                    "valueFingerprint", "valueFingerprintComplete",
                    "valueFingerprintNodes", "valueFingerprintReason",
                    "deferredResolutionAuthority",
                    "staticInputMethod", "runtimeInputMethod",
                    "rebaseAuthority", "crossMethodArgument",
                    "rebaseRejectedAuthority", "fieldBindingGap",
                    "accessKind", "observationAuthority", "bindingMode",
                    "fieldEventSeq", "fieldCallId",
                    "fieldEventIdentityAuthority",
                    "accessMethod", "accessUnitIndex", "accessSiteId",
                    "accessSiteAuthority",
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
                    restoreExactDirectFieldPathLeafMetadata(port, action,
                            exact);
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

    private static void restoreExactDirectFieldPathLeafMetadata(
            StaticPort port, Map<String, Object> action,
            FieldCell observedRoot) {
        Map<String, Object> metadata = port.materializationMetadata;
        if (!"STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1".equals(
                string(metadata.get("fieldPathAuthority")))) {
            return;
        }
        List<String> path = stringList(metadata.get("fieldPath"));
        FieldCell staticRoot = fieldCell(port.cell);
        FieldCell leaf = fieldCell(string(metadata.get(
                "leafFieldSignature")));
        if (path.size() < 2 || path.size() > 4
                || !path.equals(dependencyFieldPath(port.cell))
                || !staticRoot.declaredSignature
                || !observedRoot.signature().equals(
                staticRoot.signature())
                || !leaf.declaredSignature
                || !leaf.name.equals(path.get(path.size() - 1))
                || !primitiveType(leaf.type)
                || !staticRoot.signature().equals(string(metadata.get(
                "accessFieldSignature")))
                || !staticRoot.owner.equals(string(metadata.get(
                "accessOwnerClass")))
                || !staticRoot.name.equals(string(metadata.get(
                "accessField")))) {
            return;
        }
        action.put("bindingMode", "FIELD_ACCESS");
        action.put("javaType", leaf.type);
        // Keep the hook declaration in accessFieldSignature, while the
        // action's symbolic field identity denotes only the scalar leaf.
        action.put("field", leaf.signature());
        action.put("fieldPath", path);
        action.put("accessOwnerClass", staticRoot.owner);
        action.put("accessField", staticRoot.name);
        action.put("accessFieldType", staticRoot.type);
        action.put("accessFieldSignature", staticRoot.signature());
        action.put("leafFieldSignature", leaf.signature());
        action.put("leafOwnerClass", leaf.owner);
        action.put("leafField", leaf.name);
        action.put("fieldPathAuthority",
                "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1");
        // Publish the leaf declaration proven above as a first-class row.
        // The scheduler cannot derive the owner of a path such as
        // State.state#guard#enabled from the root signature alone: that
        // signature only declares GuardNode, while the scalar leaf belongs
        // to BooleanLeaf.  Keeping the exact path/signature join explicit
        // lets it validate the deep leaf without guessing through types.
        List<Map<String, Object>> declarations = new ArrayList<>();
        declarations.add(object(
                "fieldPath", new ArrayList<>(path),
                "fieldSignature", leaf.signature(),
                "declaredFieldOwnerClass", leaf.owner,
                "declaredFieldType", leaf.type,
                "complete", true));
        action.put("fieldPathLeafDeclarations", declarations);
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
                    policy.requiredOutcome,
                    policy.requiredSuccessorIndices);
            if (policy.isSwitch() && event != null
                    && (!event.hasSuccessorIndex
                    || !policy.branchKind.equals(event.branchKind))) {
                event = null;
            }
            Boolean observedOutcome = event != null && event.hasOutcome
                    ? event.outcome : null;
            Integer observedSuccessor = event != null
                    && event.hasSuccessorIndex
                    ? event.successorIndex : null;
            Boolean matchesRequired = observedOutcome != null
                    && policy.requiredOutcome != null
                    ? observedOutcome.equals(policy.requiredOutcome) : null;
            Boolean matchesRequiredSuccessor = observedSuccessor != null
                    && !policy.requiredSuccessorIndices.isEmpty()
                    ? policy.requiredSuccessorIndices.contains(
                    observedSuccessor) : null;
            List<Map<String, Object>> occurrenceRows = new ArrayList<>();
            int selectedOccurrence = -1;
            for (int index = 0; index < occurrences.size(); index++) {
                RuntimeEvent occurrence = occurrences.get(index);
                Boolean occurrenceMatches = occurrence.hasOutcome
                        && policy.requiredOutcome != null
                        ? occurrence.outcome == policy.requiredOutcome : null;
                Boolean occurrenceSuccessorMatches =
                        occurrence.hasSuccessorIndex
                                && !policy.requiredSuccessorIndices.isEmpty()
                                ? policy.requiredSuccessorIndices.contains(
                                occurrence.successorIndex) : null;
                if (occurrence == event) {
                    selectedOccurrence = index + 1;
                }
                occurrenceRows.add(object(
                        "occurrence", index + 1,
                        "seq", occurrence.seq,
                        "callId", occurrence.callId,
                        "outcome", occurrence.hasOutcome
                                ? occurrence.outcome : null,
                        "matchesRequiredOutcome", occurrenceMatches,
                        "successorIndex", occurrence.hasSuccessorIndex
                                ? occurrence.successorIndex : null,
                        "matchesRequiredSuccessor",
                        occurrenceSuccessorMatches));
            }
            result.add(object(
                    "siteId", policy.siteId,
                    "policy", policy.policy,
                    "guard", policy.guard,
                    "requiredOutcome", policy.requiredOutcome,
                    "requiredSuccessorIndices",
                    policy.requiredSuccessorIndices,
                    "branchKind", policy.branchKind,
                    "switchCaseKeys", policy.switchCaseKeys,
                    "defaultSuccessorIndex",
                    policy.defaultSuccessorIndex,
                    "observed", event != null,
                    "observedOutcome", observedOutcome,
                    "matchesRequiredOutcome", matchesRequired,
                    "observedSuccessorIndex", observedSuccessor,
                    "matchesRequiredSuccessor",
                    matchesRequiredSuccessor,
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
            List<RuntimeEvent> occurrences, Boolean requiredOutcome,
            List<Integer> requiredSuccessorIndices) {
        RuntimeEvent selected = null;
        for (RuntimeEvent occurrence : occurrences) {
            selected = occurrence;
            if (occurrence.hasSuccessorIndex
                    && requiredSuccessorIndices != null
                    && requiredSuccessorIndices.contains(
                    occurrence.successorIndex)) {
                return occurrence;
            }
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
            Map<String, List<InstanceEvidence>> sharedStateEvidenceByRegion,
            StaticProjectionIndex staticProjections, Result result,
            List<UpstreamEdgeBinding> edgeBindings,
            RuntimeRelationEvidenceCache relationEvidence) {
        for (StaticRegionEdge edge : staticEdges) {
            Map<String, List<InstanceEvidence>> selectedEvidence =
                    "SHARED_STATE".equals(edge.kind)
                            ? sharedStateEvidenceByRegion : evidenceByRegion;
            List<InstanceEvidence> upstreamInstances = values(
                    selectedEvidence.get(edge.fromRegion));
            List<InstanceEvidence> downstreamInstances = values(
                    selectedEvidence.get(edge.toRegion));
            int endpointPairs = 0;
            int orderedPairs = 0;
            int readFromPairs = 0;
            int valueEqualityPairs = 0;
            int demandPrunedPairCount = 0;
            List<Map<String, Object>> validatedBindings = new ArrayList<>();
            String endpointCorrelationAuthority =
                    endpointCorrelationAuthority();
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
                    ConsumerInputResolution retainedInputResolution =
                            downstream.resolveConsumerInput(edge.toPort,
                                    staticProjections);
                    if (retainedInputResolution == null) {
                        demandPrunedPairCount++;
                        continue;
                    }
                    endpointPairs++;
                    boolean sameProcess = upstream.root.process.equals(
                            downstream.root.process);
                    List<FingerprintMatch> valueMatches = values(
                            selectedValueMatches.get(endpointInstancePairKey(
                                    upstream, downstream)));
                    FingerprintMatch valueMatch = valueMatches.isEmpty()
                            ? null : valueMatches.get(0);
                    SharedReadFrom readFrom = "SHARED_STATE".equals(edge.kind)
                            ? relationEvidence.sharedReadFrom(edge, upstream,
                            downstream) : null;
                    if (readFrom != null
                            && !projectionReadFromIdentityConfirmed(
                            retainedInputResolution, readFrom)) {
                        readFrom = null;
                    }
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
                        if (edge.producerOutputFor(upstream.region) != null) {
                            edgeBindings.add(new UpstreamEdgeBinding(edge,
                                    upstream, downstream, readFrom));
                        }
                    }
                    valueEqualityPairs += valueMatches.size();
                    Map<String, Object> row = object(
                            "fromRegionInstance", upstream.instanceId,
                            "toRegionInstance", downstream.instanceId);
                    if (readFrom != null) {
                        addReadFromEvidence(row, readFrom);
                    } else if (valueMatch != null) {
                        addValueEqualityEvidence(row, valueMatch,
                                endpointCorrelationAuthority);
                    }
                    if (readFrom != null || valueMatch != null) {
                        validatedBindings.add(row);
                    }
                    for (int matchIndex = readFrom == null ? 1
                            : valueMatches.size();
                         matchIndex < valueMatches.size(); matchIndex++) {
                        FingerprintMatch additional = valueMatches.get(
                                matchIndex);
                        Map<String, Object> additionalRow =
                                new LinkedHashMap<>(row);
                        addValueEqualityEvidence(additionalRow, additional,
                                endpointCorrelationAuthority);
                        validatedBindings.add(additionalRow);
                    }
                }
            }

            String state;
            if ("SHARED_STATE".equals(edge.kind)) {
                if (readFromPairs > 0) {
                    state = "CONFIRMED_READ_FROM";
                } else if (demandPrunedPairCount > 0
                        && endpointPairs == 0) {
                    state = "PRUNED_BY_CONCRETE_DEMAND_SLICE";
                } else if (endpointPairs > 0) {
                    state = "UNCONFIRMED_READ_FROM";
                } else {
                    state = "UNOBSERVED";
                }
            } else if (demandPrunedPairCount > 0
                    && endpointPairs == 0) {
                state = "PRUNED_BY_CONCRETE_DEMAND_SLICE";
            } else if (endpointPairs == 0) {
                state = "UNOBSERVED";
            } else if (valueEqualityPairs > 0) {
                state = "CONFIRMED_RUNTIME_VALUE_EQUALITY";
            } else if (orderedPairs > 0) {
                state = "PORT_MAPPING_OBSERVED_VALUE_EQUALITY_UNPROVEN";
            } else {
                state = "ENDPOINTS_OBSERVED";
            }

            Map<String, Object> validationRow = object(
                    "schemaVersion", 2,
                    "kind", "RUNTIME_REGION_EDGE_EVIDENCE",
                    "edgeId", edge.edgeId,
                    "fromRegion", edge.fromRegion,
                    "toRegion", edge.toRegion,
                    "transportKind", edge.kind,
                    "fromPort", edge.fromPort,
                    "toPort", edge.toPort,
                    "state", state,
                    "bindings", validatedBindings);
            if (!edge.mappingKind.isEmpty()) {
                validationRow.put("mappingKind", edge.mappingKind);
            }
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
            if (!edge.producerCandidateGroup.isEmpty()) {
                validationRow.put("_producerRegionCandidateGroup",
                        edge.producerCandidateGroup);
            }
            result.edgeValidations.add(validationRow);
        }
        enforceUniqueExpandedProtocolProducer(result.edgeValidations);
    }

    private static void addValueEqualityEvidence(
            Map<String, Object> target, FingerprintMatch match,
            String correlationAuthority) {
        target.put("evidenceKind", "COMPLETE_VALUE_EQUALITY_V1");
        target.put("writerEventSeq", match.from.seq);
        target.put("readerEventSeq", match.to.seq);
        target.put("valueFingerprint", match.from.digest);
        if (!safe(correlationAuthority).isEmpty()) {
            target.put("correlationAuthority", correlationAuthority);
        }
    }

    private static void addReadFromEvidence(
            Map<String, Object> target, SharedReadFrom readFrom) {
        boolean mutation = readFrom.writeEvidence.mutation != null;
        target.put("evidenceKind", mutation
                ? "CONTAINER_MUTATION_READ_FROM_V1"
                : "FIELD_ASSIGNMENT_READ_FROM_V1");
        target.put("writerEventSeq", readFrom.writerEventSeq());
        target.put("readerEventSeq", readFrom.read.seq);
        target.put("field", readFrom.write.field);
        target.put("receiverObjectId", readFrom.write.receiverObjectId);
        if (!mutation) {
            return;
        }
        target.put("valueObjectId", readFrom.write.valueObjectId);
        target.put("readerValueObjectId", readFrom.read.valueObjectId);
        target.put("writerFieldReadSeq", readFrom.write.seq);
        target.put("mutatorEnterSeq",
                readFrom.writeEvidence.mutation.seq);
        target.put("mutationCompletionSeq",
                readFrom.writeEvidence.completion.seq);
        target.put("mutationInvocationId",
                readFrom.writeEvidence.mutation.invocationId);
        target.put("mutatorDeclaredCallee",
                readFrom.writeEvidence.mutation.declaredCallee);
    }

    /**
     * Adds only externally confirmed boundary inputs to the provisional local
     * demand slices.  This pass has no retained-input gate: the runtime
     * relation is the evidence that authorizes the promotion.  Rendering then
     * runs once against the final, monotonic input sets.
     */
    private static void collectConfirmedExternalInputPromotions(
            List<StaticRegionEdge> staticEdges,
            Map<String, List<InstanceEvidence>> evidenceByRegion,
            Map<String, List<InstanceEvidence>> sharedStateEvidenceByRegion,
            StaticProjectionIndex staticProjections,
            RuntimeRelationEvidenceCache relationEvidence) {
        for (StaticRegionEdge edge : staticEdges) {
            Map<String, List<InstanceEvidence>> selectedEvidence =
                    "SHARED_STATE".equals(edge.kind)
                            ? sharedStateEvidenceByRegion : evidenceByRegion;
            List<InstanceEvidence> upstreamInstances = values(
                    selectedEvidence.get(edge.fromRegion));
            List<InstanceEvidence> downstreamInstances = values(
                    selectedEvidence.get(edge.toRegion));
            Map<String, List<FingerprintMatch>> valueMatches =
                    "SHARED_STATE".equals(edge.kind)
                            ? Collections.emptyMap()
                            : nearestEndpointFingerprintMatches(edge,
                            upstreamInstances, downstreamInstances);
            for (InstanceEvidence upstream : upstreamInstances) {
                for (InstanceEvidence downstream : downstreamInstances) {
                    if (!upstream.root.test.equals(downstream.root.test)) {
                        continue;
                    }
                    // A confirmed transport/shared-state value supplements a
                    // runtime-selected region; it must not turn a merely
                    // overlapping static candidate into a second concrete
                    // region.  Truncated paths remain eligible when their
                    // anchor was observed (important for long-running
                    // workers), while wrong-subclass/wrong-exception
                    // candidates fail closed here.
                    if (!upstream.anchorObserved
                            || !downstream.anchorObserved) {
                        continue;
                    }
                    boolean siteObserved = observesSite(
                            downstream.runtimeEvents, edge.siteId)
                            || rpcPortMapping(edge)
                            && observesMappedRpcInvocation(
                            downstream.runtimeEvents, edge.fromPort,
                            edge.toPort);
                    if (!"SHARED_STATE".equals(edge.kind)
                            && (!observesPortMethod(upstream, edge.fromPort)
                            || (!observesPortMethod(downstream, edge.toPort)
                            && !siteObserved))) {
                        continue;
                    }
                    SharedReadFrom readFrom = "SHARED_STATE".equals(edge.kind)
                            ? relationEvidence.sharedReadFrom(edge, upstream,
                            downstream) : null;
                    FingerprintMatch valueMatch = first(values(
                            valueMatches.get(endpointInstancePairKey(
                                    upstream, downstream))));
                    if (readFrom == null && valueMatch == null) {
                        continue;
                    }

                    ConsumerInputResolution resolution = downstream
                            .resolveExternalCandidateInput(edge.toPort,
                                    staticProjections);
                    if (resolution == null
                            || !projectionReadFromIdentityConfirmed(
                            resolution, readFrom)) {
                        continue;
                    }
                    downstream.promoteExternalInput(resolution.port);

                    if (readFrom == null) {
                        continue;
                    }
                    StaticPort output = edge.producerOutputFor(
                            upstream.region);
                    StaticOutputSlice staticSlice = output == null ? null
                            : upstream.region.outputSliceFor(output.portId);
                    StaticOutputSlice outputSlice = staticSlice == null ? null
                            : staticSlice.runtimeRefined(upstream);
                    if (outputSlice == null) {
                        continue;
                    }
                    upstream.concreteDemandSlice.methods.addAll(
                            outputSlice.methods);
                    for (String inputPort : outputSlice.inputPorts) {
                        StaticPort input = upstream.region.exactInputFor(
                                inputPort);
                        if (input == null) {
                            continue;
                        }
                        upstream.promoteExternalInput(input);
                    }
                }
            }
        }
    }

    private static <T> T first(List<T> values) {
        return values == null || values.isEmpty() ? null : values.get(0);
    }

    /** Rebuilds activation execution inputs from the promoted demand set. */
    private static void refreshPromotedConcreteInputRows(
            List<InstanceEvidence> evidence, Result result) {
        Map<String, Map<String, Object>> activations = rowsByInstanceId(
                result.activations);
        for (InstanceEvidence instance : evidence) {
            if (!instance.concreteDemandSlice.externalInputPromoted) {
                continue;
            }
            List<StaticPort> concreteInputs =
                    instance.concreteDemandSlice.inputs(instance.region);
            List<Map<String, Object>> inputObjects = inputObservations(
                    instance.region, concreteInputs, instance.root,
                    instance.runtimeEvents,
                    instance.fieldEvents, instance.methodEvents);
            List<Map<String, Object>> symbolize = symbolizeActions(
                    instance.region, concreteInputs, instance.root,
                    inputObjects, instance.runtimeEvents,
                    instance.fieldEvents);
            List<Map<String, Object>> branches = branchActions(
                    instance.region, instance.runtimeEvents);
            int observedInputCount = countObserved(inputObjects);
            int deferredInputCount = countDeferred(inputObjects);
            boolean inputsResolved = observedInputCount + deferredInputCount
                    == inputObjects.size();
            boolean branchesResolved = countObservedBranches(branches)
                    == branches.size();
            boolean symbolizeReady = symbolizeActionsReady(symbolize);
            boolean symbolicPotential = !concreteInputs.isEmpty()
                    || instance.region.inputs.isEmpty()
                    || instance.region.branches.isEmpty();
            boolean boundaryReady = inputsResolved && branchesResolved
                    && instance.region.inputSelectionComplete
                    && instance.runtimePathEvidenceComplete
                    && symbolizeReady;

            Map<String, Object> activation = activations.get(
                    instance.instanceId);
            boolean replayable = admissionReplayable(activation);
            boolean symbolicReady = replayable && boundaryReady
                    && symbolicPotential;

            if (activation != null) {
                activation.put("symbolize", symbolize);
                activation.put("branches", branches);
                activation.put("runtimeDefinitionMethods",
                        instance.concreteDemandSlice.definitionMethods(
                                instance.observedMethods));
                activation.put("admission", admission(replayable,
                        symbolicReady, admissionMode(activation),
                        Collections.emptyList(), false, false));
            }
        }
    }

    private static Map<String, Map<String, Object>> rowsByInstanceId(
            List<Map<String, Object>> rows) {
        Map<String, Map<String, Object>> result = new LinkedHashMap<>();
        for (Map<String, Object> row : rows) {
            String id = string(row.get("regionInstanceId"));
            if (!id.isEmpty()) {
                result.put(id, row);
            }
        }
        return result;
    }

    private static Map<String, Object> admission(
            boolean replayable, boolean ready, String mode,
            Collection<?> gaps, boolean pathTruncated,
            boolean callTreeTruncated) {
        List<Object> blockers = new ArrayList<>();
        if (gaps != null) blockers.addAll(gaps);
        if (pathTruncated) blockers.add(object(
                "kind", "PATH_SIGNATURE_TRUNCATED"));
        if (callTreeTruncated) blockers.add(object(
                "kind", "CONTAINED_CALL_TREE_TRUNCATED"));
        if (replayable && !ready && blockers.isEmpty()) {
            blockers.add(object("kind", "SYMBOLIC_BOUNDARY_NOT_READY"));
        }
        return object(
                "state", ready ? "READY"
                        : replayable ? "DISCOVERED" : "BLOCKED",
                "mode", safe(mode),
                "blockers", blockers);
    }

    private static boolean admissionReplayable(
            Map<String, Object> activation) {
        Map<String, Object> admission = activation == null ? null
                : mapValue(activation.get("admission"));
        String state = admission == null ? ""
                : string(admission.get("state"));
        return "READY".equals(state) || "DISCOVERED".equals(state)
                || "EXECUTABLE".equals(state);
    }

    private static String admissionMode(Map<String, Object> activation) {
        Map<String, Object> admission = activation == null ? null
                : mapValue(activation.get("admission"));
        return admission == null ? "" : string(admission.get("mode"));
    }

    /**
     * Exact output identity enumerates candidates but does not prove which
     * enclosing root executed the transfer.  Accept one producer only when a
     * single candidate has the existing complete runtime fingerprint/order
     * witness.  Multiple matching regions remain useful evidence, but none is
     * admitted to recursive SMT composition.
     */
    private static void enforceUniqueExpandedProtocolProducer(
            List<Map<String, Object>> validations) {
        Map<String, List<Map<String, Object>>> byGroup =
                new LinkedHashMap<>();
        for (Map<String, Object> row : validations) {
            String group = string(row.get(
                    "_producerRegionCandidateGroup"));
            if (!group.isEmpty()) {
                add(byGroup, group, row);
            }
        }
        for (List<Map<String, Object>> candidates : byGroup.values()) {
            List<Map<String, Object>> confirmed = new ArrayList<>();
            for (Map<String, Object> candidate : candidates) {
                if ("CONFIRMED_RUNTIME_VALUE_EQUALITY".equals(
                        string(candidate.get("state")))) {
                    confirmed.add(candidate);
                }
            }
            if (confirmed.size() > 1) {
                for (Map<String, Object> ambiguous : confirmed) {
                    ambiguous.put("state",
                            "AMBIGUOUS_RUNTIME_PRODUCER_REGION");
                }
            }
        }
        for (Map<String, Object> validation : validations) {
            validation.remove("_producerRegionCandidateGroup");
        }
    }

    /**
     * Derives a separate upstream-output activation from confirmed runtime
     * read-from evidence.  The original path activation is preserved because a
     * region may simultaneously contain the target and provide an output for
     * another region query.
     */
    private static void deriveUpstreamActivations(
            List<UpstreamEdgeBinding> bindings,
            StaticProjectionIndex staticProjections, Result result) {
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
                continue;
            }
            binding.output = output;
            // A runtime edge records the concrete/raw consumer cell.  Lift
            // that cell to the target region namespace only when the static
            // catalog declares one exact matching symbolic input.  A
            // same-field fallback is not sufficient here: projected fields
            // can have a different SMT sort from their owning object, and an
            // arbitrary first match would silently create a false in/out
            // equality.
            ConsumerInputResolution inputResolution =
                    binding.downstream.resolveConsumerInput(
                            binding.edge.toPort, staticProjections);
            if (!projectionReadFromIdentityConfirmed(inputResolution,
                    binding.readFrom)) {
                inputResolution = null;
            }
            if (inputResolution == null) {
                continue;
            }
            binding.downstreamInput = inputResolution.port;
            binding.downstreamInputProjection = inputResolution.projection;
            String identity = binding.identity();
            if (!seen.add(identity)) {
                continue;
            }
            add(grouped, binding.upstream.instanceId + "\n"
                    + binding.downstream.instanceId, binding);
        }

        int activationIndex = 0;
        for (List<UpstreamEdgeBinding> demand : grouped.values()) {
            UpstreamEdgeBinding first = demand.get(0);
            Map<String, Object> base = baseByInstance.get(
                    first.upstream.instanceId);
            if (base == null) {
                continue;
            }

            Map<String, Object> activation = new LinkedHashMap<>(base);
            String derivedId = "ACT.UPSTREAM." + activationIndex++;
            boolean writerPathReplayable =
                    first.upstream.runtimePathEvidenceComplete;
            activation.put("activationId", derivedId);
            activation.remove("summaryMode");
            activation.put("captureGoal", object(
                    "kind", "OUTPUT_CLOSURE",
                    "scope", "BOUNDED_OUTPUT_RELEVANT_PATHS"));

            Map<String, List<UpstreamEdgeBinding>> byOutput =
                    new LinkedHashMap<>();
            for (UpstreamEdgeBinding binding : demand) {
                add(byOutput, binding.output.portId, binding);
            }
            List<UpstreamOutputMemberPlan> members = new ArrayList<>();
            List<String> issues = new ArrayList<>();
            for (String outputPort : sorted(byOutput.keySet())) {
                UpstreamOutputMemberPlan member =
                        upstreamOutputMemberPlan(base,
                                byOutput.get(outputPort));
                members.add(member);
                if (!member.issue.isEmpty()) {
                    issues.add(member.issue);
                }
            }

            OutputClosureContract outputClosure = null;
            if (issues.isEmpty()) {
                List<OutputClosureContract> contracts = new ArrayList<>();
                for (UpstreamOutputMemberPlan member : members) {
                    contracts.add(member.contract);
                }
                try {
                    outputClosure = OutputClosureCodec.merge(contracts);
                } catch (RuntimeException unsupported) {
                    issues.add("JOINT_OUTPUT_CLOSURE_UNSUPPORTED:"
                            + safe(unsupported.getMessage()));
                }
            }

            if (issues.isEmpty()
                    && !mergeUpstreamMemberExecution(activation, members,
                    issues)) {
                outputClosure = null;
            }
            if (issues.isEmpty()) {
                activation.put("_plannerOutputClosure", outputClosure);
                activation.put("_plannerOutputMembers", members);
            } else {
                activation.put("symbolize", Collections.emptyList());
                activation.put("branches", Collections.emptyList());
                activation.remove("containerElementFieldBindings");
                activation.remove("heapStateBindings");
            }

            activation.put("admission", admission(writerPathReplayable,
                    writerPathReplayable && issues.isEmpty(),
                    writerPathReplayable
                            ? "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY"
                            : "RUNTIME_READ_FROM_WITNESS_ONLY_PATH_TRUNCATED",
                    issues, false, !writerPathReplayable));

            List<Map<String, Object>> bindingRows = new ArrayList<>();
            for (UpstreamEdgeBinding binding : demand) {
                bindingRows.add(binding.toMap());
            }
            activation.put("edgeBindings", bindingRows);
            result.activations.add(activation);
        }
    }

    private static UpstreamOutputMemberPlan upstreamOutputMemberPlan(
            Map<String, Object> base, List<UpstreamEdgeBinding> bindings) {
        UpstreamEdgeBinding first = bindings.get(0);
        StaticOutputSlice declared = first.upstream.region.outputSliceFor(
                first.output.portId);
        StaticOutputSlice outputSlice = declared == null ? null
                : declared.runtimeRefined(first.upstream);
        if (outputSlice == null) {
            return UpstreamOutputMemberPlan.failed(first.output,
                    "OUTPUT_MEMBER_HAS_NO_STATIC_BACKWARD_SLICE:"
                            + first.output.portId);
        }

        List<Map<String, Object>> selectedInputs = selectActivationRows(
                base.get("symbolize"), outputSlice.inputPorts, "symbol");
        Set<String> selectedInputPorts = new LinkedHashSet<>();
        for (Map<String, Object> selectedInput : selectedInputs) {
            addNonBlank(selectedInputPorts,
                    string(selectedInput.get("symbol")));
        }
        boolean inputSelectionComplete = selectedInputPorts.containsAll(
                outputSlice.inputPorts);
        applySliceDrivenArgumentFieldPaths(selectedInputs, outputSlice);
        List<Map<String, Object>> containerBindings = copyRows(
                outputSlice.containerElementFieldBindings);
        applyExactConsumedArrayFieldEvidence(selectedInputs,
                first.upstream.root, first.upstream.fieldEvents);
        boolean inputAliasesReady = canonicalizeExactRuntimeInputAliases(
                selectedInputs, outputSlice, containerBindings,
                first.upstream.fieldEvents);
        boolean containerBindingsReady = inputAliasesReady
                && applyContainerElementFieldBindings(selectedInputs,
                containerBindings);
        if (containerBindingsReady) {
            applyExactConsumedArrayFieldEvidence(selectedInputs,
                    first.upstream.root, first.upstream.fieldEvents);
        }
        List<Map<String, Object>> selectedBranches = selectActivationRows(
                base.get("branches"), outputSlice.sites, "siteId");
        boolean sliceReady = outputSlice.complete
                && outputSlice.captureBindingsComplete
                && inputSelectionComplete
                && containerBindingsReady
                && inputAliasesReady
                && symbolizeActionsReady(selectedInputs)
                && branchActionsReady(selectedBranches);
        List<Map<String, Object>> heapBindings = new ArrayList<>();
        StaticPort input = first.upstream.region.exactInputFor(
                first.output.cell);
        if (input != null && outputSlice.inputPorts.contains(input.portId)) {
            heapBindings.add(object(
                    "inputPort", input.portId,
                    "outputPort", first.output.portId,
                    "cell", first.output.cell,
                    "bindingAuthority",
                    "STATIC_CELL_IDENTITY_PLUS_RUNTIME_READ_FROM"));
        }
        if (!sliceReady) {
            List<String> causes = new ArrayList<>();
            if (!outputSlice.complete) {
                causes.add("STATIC_SLICE_INCOMPLETE");
            }
            if (!outputSlice.captureBindingsComplete) {
                causes.add("CAPTURE_BINDINGS_INCOMPLETE");
            }
            if (!inputSelectionComplete) {
                Set<String> missing = new LinkedHashSet<>(
                        outputSlice.inputPorts);
                missing.removeAll(selectedInputPorts);
                causes.add("MISSING_INPUT_PORTS=" + missing);
            }
            if (!inputAliasesReady) {
                causes.add("INPUT_ALIASES_UNRESOLVED");
            }
            if (!containerBindingsReady) {
                causes.add("CONTAINER_BINDINGS_UNRESOLVED");
            }
            if (!symbolizeActionsReady(selectedInputs)) {
                List<String> unready = new ArrayList<>();
                for (Map<String, Object> action : selectedInputs) {
                    if (!symbolizeActionsReady(Collections.singletonList(
                            action))) {
                        unready.add(string(action.get("symbol")) + "@"
                                + string(action.get("location")) + "["
                                + string(action.get("cell")) + "]");
                    }
                }
                causes.add("SYMBOLIZE_ACTIONS_INCOMPLETE=" + unready);
            }
            if (!branchActionsReady(selectedBranches)) {
                causes.add("BRANCH_ACTIONS_INCOMPLETE");
            }
            return new UpstreamOutputMemberPlan(first.output, outputSlice,
                    selectedInputs, selectedBranches, containerBindings,
                    heapBindings, null,
                    "OUTPUT_MEMBER_INCOMPLETE:" + first.output.portId
                            + ":" + String.join(",", causes));
        }

        final OutputClosureContract contract;
        try {
            contract = OutputClosureCodec.singleton(
                    first.upstream.region.regionId,
                    first.upstream.instanceId, first.upstream.root.callId,
                    first.output.portId, first.output.cell, first.output.kind,
                    "CONFIRMED_READ_FROM_EDGE",
                    JsonParser.parseString(json(outputSlice.toMap()))
                            .getAsJsonObject());
        } catch (RuntimeException malformed) {
            return new UpstreamOutputMemberPlan(first.output, outputSlice,
                    selectedInputs, selectedBranches, containerBindings,
                    heapBindings, null,
                    "OUTPUT_MEMBER_CONTRACT_INVALID:"
                            + first.output.portId + ":"
                            + safe(malformed.getMessage()));
        }
        return new UpstreamOutputMemberPlan(first.output, outputSlice,
                selectedInputs, selectedBranches, containerBindings,
                heapBindings, contract, "");
    }

    private static boolean mergeUpstreamMemberExecution(
            Map<String, Object> activation,
            List<UpstreamOutputMemberPlan> members, List<String> issues) {
        Map<String, Map<String, Object>> inputs = new LinkedHashMap<>();
        Map<String, Map<String, Object>> branches = new LinkedHashMap<>();
        Map<String, Map<String, Object>> containers = new LinkedHashMap<>();
        Map<String, Map<String, Object>> heaps = new LinkedHashMap<>();
        for (UpstreamOutputMemberPlan member : members) {
            mergeExactRows(inputs, member.selectedInputs, "symbol",
                    "SYMBOLIZE_ACTION", issues);
            mergeExactRows(branches, member.selectedBranches, "siteId",
                    "BRANCH_ACTION", issues);
            mergeExactRows(containers, member.containerBindings, "bindingId",
                    "CONTAINER_BINDING", issues);
            mergeExactRows(heaps, member.heapBindings, "outputPort",
                    "HEAP_STATE_BINDING", issues);
        }
        if (!issues.isEmpty()) return false;
        activation.put("symbolize", new ArrayList<>(inputs.values()));
        activation.put("branches", new ArrayList<>(branches.values()));
        if (containers.isEmpty()) {
            activation.remove("containerElementFieldBindings");
        } else {
            activation.put("containerElementFieldBindings",
                    new ArrayList<>(containers.values()));
        }
        if (heaps.isEmpty()) {
            activation.remove("heapStateBindings");
        } else {
            activation.put("heapStateBindings",
                    new ArrayList<>(heaps.values()));
        }
        return true;
    }

    private static void mergeExactRows(
            Map<String, Map<String, Object>> target,
            List<Map<String, Object>> rows, String keyField, String label,
            List<String> issues) {
        for (Map<String, Object> row : rows) {
            String key = string(row.get(keyField));
            if (key.isEmpty()) key = json(row);
            Map<String, Object> previous = target.putIfAbsent(key, row);
            if (previous != null && !json(previous).equals(json(row))) {
                issues.add("CONFLICTING_" + label + ":" + key);
            }
        }
    }

    private static void finalizeOutputClosureArtifacts(Result result) {
        for (Map<String, Object> activation : result.activations) {
            activation.remove("_plannerOutputMembers");
            Object encoded = activation.remove("_plannerOutputClosure");
            if (encoded instanceof OutputClosureContract) {
                activation.put(OutputClosureContract.FIELD,
                        ((OutputClosureContract) encoded).toJson());
            }
        }
    }

    private static final class UpstreamOutputMemberPlan {
        private final StaticPort output;
        private final StaticOutputSlice outputSlice;
        private final List<Map<String, Object>> selectedInputs;
        private final List<Map<String, Object>> selectedBranches;
        private final List<Map<String, Object>> containerBindings;
        private final List<Map<String, Object>> heapBindings;
        private final OutputClosureContract contract;
        private final String issue;

        private UpstreamOutputMemberPlan(
                StaticPort output, StaticOutputSlice outputSlice,
                List<Map<String, Object>> selectedInputs,
                List<Map<String, Object>> selectedBranches,
                List<Map<String, Object>> containerBindings,
                List<Map<String, Object>> heapBindings,
                OutputClosureContract contract, String issue) {
            this.output = output;
            this.outputSlice = outputSlice;
            this.selectedInputs = selectedInputs;
            this.selectedBranches = selectedBranches;
            this.containerBindings = containerBindings;
            this.heapBindings = heapBindings;
            this.contract = contract;
            this.issue = issue;
        }

        private static UpstreamOutputMemberPlan failed(
                StaticPort output, String issue) {
            return new UpstreamOutputMemberPlan(output, null,
                    Collections.<Map<String, Object>>emptyList(),
                    Collections.<Map<String, Object>>emptyList(),
                    Collections.<Map<String, Object>>emptyList(),
                    Collections.<Map<String, Object>>emptyList(),
                    null, issue);
        }
    }

    /** A projected consumer input may only inherit a shared-state relation
     * when the runtime observed the same non-zero value object on both sides.
     * Exact input-cell bindings do not need this additional projection gate. */
    private static boolean projectionReadFromIdentityConfirmed(
            ConsumerInputResolution resolution, SharedReadFrom readFrom) {
        return resolution == null || resolution.projection == null
                || readFrom != null && projectedValueIdentityConfirmed(
                true, readFrom.write.valueObjectId,
                readFrom.read.valueObjectId);
    }

    static boolean projectedValueIdentityConfirmed(
            boolean projected, int writerValueObjectId,
            int readerValueObjectId) {
        return !projected || writerValueObjectId != 0
                && writerValueObjectId == readerValueObjectId;
    }

    /**
     * Coalesces a projected nested-field input with an exact primitive field
     * or consumed array leaf that denotes the same live Java field in this
     * region instance.
     *
     * <p>Symbolizing the same field through two region ports does not create
     * two independent inputs: it creates an alias that the importer
     * intentionally rejects. Canonicalization must therefore happen before
     * replay, while the discovery execution's exact receiver/value identities
     * are still available. A field name or Java type alone is never
     * sufficient.</p>
     */
    private static boolean canonicalizeExactRuntimeInputAliases(
            List<Map<String, Object>> selectedInputs,
            StaticOutputSlice outputSlice,
            List<Map<String, Object>> containerBindings,
            List<FieldAccessEvent> fieldEvents) {
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
                FieldCell leaf = exactRuntimeAliasLeaf(candidate);
                if (leaf.declaredSignature
                        && baseField.type.equals(leaf.owner)
                        && path.get(1).equals(leaf.name)) {
                    staticCandidates.add(candidate);
                }
            }
            if (staticCandidates.isEmpty()) {
                // This projection has no exact selected leaf representation.
                continue;
            }

            FieldCell leaf = exactRuntimeAliasLeaf(staticCandidates.get(0));
            boolean arrayAlias = isArrayJavaType(leaf.type);
            String aliasKind = arrayAlias ? "ARRAY" : "PRIMITIVE";
            String authorityIssue = projectedAliasAuthorityIssue(
                    outputSlice, aliasAction, path, aliasKind);
            if (!authorityIssue.isEmpty()) {
                issues.add(aliasPort + ":" + authorityIssue);
                continue;
            }
            if (staticCandidates.size() != 1) {
                issues.add(aliasPort
                        + ":EXACT_" + aliasKind
                        + "_ALIAS_CANONICAL_PORT_NOT_UNIQUE:"
                        + staticCandidates.size());
                continue;
            }

            Map<String, Object> canonicalAction = staticCandidates.get(0);
            String canonicalPort = string(canonicalAction.get("symbol"));
            leaf = exactRuntimeAliasLeaf(canonicalAction);
            String runtimeIssue = hasExactCellIdentityBinding(outputSlice,
                    canonicalPort)
                    ? arrayAlias
                    ? exactRuntimeArrayAliasIssue(aliasAction,
                    canonicalAction, baseField, leaf, fieldEvents)
                    : exactRuntimePrimitiveAliasIssue(aliasAction,
                    canonicalAction, baseField, leaf, fieldEvents)
                    : "CANONICAL_" + aliasKind
                    + "_PORT_LACKS_EXACT_CELL_IDENTITY";
            if (!runtimeIssue.isEmpty()) {
                issues.add(aliasPort + ":" + runtimeIssue);
                continue;
            }
            String old = canonicalByAlias.put(aliasPort, canonicalPort);
            if (old != null && !old.equals(canonicalPort)) {
                issues.add(aliasPort
                        + ":" + aliasKind
                        + "_ALIAS_CANONICALIZATION_NOT_FUNCTIONAL");
                continue;
            }

            int baseReceiver = number(aliasAction,
                    "fieldReceiverObjectId");
            int intermediateOwner = number(aliasAction, "valueObjectId");
            Map<String, Object> proof = object(
                    "schemaVersion", 1,
                    "kind", "CANONICAL_" + aliasKind + "_INPUT_ALIAS",
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
                    "staticAuthority",
                    arrayAlias
                            ? "PROJECTED_FRONTIER_TO_EXACT_CONSUMED_"
                            + "ARRAY_LEAF_V1"
                            : "PROJECTED_FRONTIER_TO_EXACT_PRIMITIVE_"
                            + "FIELD_V1",
                    "runtimeIdentityAuthority",
                    "BASE_FIELD_VALUE_EQUALS_EXACT_LEAF_RECEIVER_V1",
                    "aliasBindingCount", aliasBindingCount(outputSlice,
                            aliasPort),
                    "aliasBindingAuthorities", aliasBindingValues(
                            outputSlice, aliasPort, "bindingAuthority"),
                    "aliasDependencyCells", aliasBindingValues(outputSlice,
                            aliasPort, "dependencyCell"),
                    "complete", true);
            FieldAccessEvent baseRead = exactActionFieldEvent(aliasAction,
                    fieldEvents);
            FieldAccessEvent leafRead = exactActionFieldEvent(
                    canonicalAction, fieldEvents);
            proof.put("baseFieldEventSeq", baseRead.seq);
            proof.put("canonicalLeafFieldEventSeq", leafRead.seq);
            if (arrayAlias) {
                proof.put("canonicalArrayValueObjectId", number(
                        canonicalAction, "valueObjectId"));
                proof.put("consumedFieldSiteId", string(canonicalAction.get(
                        "consumedFieldSiteId")));
            } else {
                proof.put("canonicalPrimitiveValue", string(
                        canonicalAction.get("primitiveValue")));
            }
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

    private static FieldCell exactRuntimeAliasLeaf(
            Map<String, Object> action) {
        FieldCell primitive = exactRuntimePrimitiveLeaf(action);
        return primitive.declaredSignature
                ? primitive : exactConsumedArrayLeaf(action);
    }

    /** Returns the exact observed primitive field represented by an action. */
    private static FieldCell exactRuntimePrimitiveLeaf(
            Map<String, Object> action) {
        FieldCell cell = fieldCell(string(action.get("cell")));
        FieldCell observed = fieldCell(string(action.get(
                "accessFieldSignature")));
        String javaType = string(action.get("javaType"));
        return Boolean.TRUE.equals(action.get("observed"))
                && "HEAP_OBJECT_FIELD".equals(string(action.get(
                "location")))
                && "FIELD_READ".equals(string(action.get("accessKind")))
                && "RUNTIME_FIELD_ACCESS_DECLARATION".equals(string(
                action.get("accessFieldAuthority")))
                && cell.declaredSignature && observed.declaredSignature
                && cell.signature().equals(observed.signature())
                && primitiveType(cell.type) && cell.type.equals(javaType)
                && exactPrimitiveValue(cell.type, string(action.get(
                "primitiveValue")))
                && number(action, "fieldReceiverObjectId") != 0
                ? cell : FieldCell.unresolved();
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
            StaticOutputSlice slice, Map<String, Object> aliasAction,
            List<String> path, String aliasKind) {
        String aliasPort = string(aliasAction.get("symbol"));
        String aliasCell = string(aliasAction.get("cell"));
        String projection = string(aliasAction.get("projection"));
        if (path.size() != 2
                || !projection.equals("field:" + path.get(1))) {
            return "PROJECTED_" + aliasKind
                    + "_ALIAS_ACTION_PATH_MISMATCH";
        }
        int count = 0;
        for (Map<String, Object> binding : slice.inputBindings) {
            if (!aliasPort.equals(string(binding.get("inputPort")))) {
                continue;
            }
            count++;
            if (!aliasCell.equals(string(binding.get("dependencyCell")))) {
                return "PROJECTED_" + aliasKind
                        + "_ALIAS_DEPENDENCY_CELL_MISMATCH";
            }
            String authority = string(binding.get("bindingAuthority"));
            boolean exactChain = "UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN".equals(
                    authority);
            boolean arrayPromotion = "ARRAY".equals(aliasKind)
                    && "OUTPUT_SLICE_FRONTIER_PROMOTION".equals(authority);
            if (!exactChain && !arrayPromotion) {
                return "PROJECTED_" + aliasKind
                        + "_ALIAS_AUTHORITY_INVALID:" + authority;
            }
        }
        if (count == 0) {
            return "PROJECTED_" + aliasKind + "_ALIAS_BINDING_MISSING";
        }
        return "PRIMITIVE".equals(aliasKind) && count != 1
                ? "PROJECTED_PRIMITIVE_ALIAS_BINDING_COUNT:" + count : "";
    }

    private static String exactRuntimePrimitiveAliasIssue(
            Map<String, Object> alias, Map<String, Object> canonical,
            FieldCell baseField, FieldCell leaf,
            List<FieldAccessEvent> fieldEvents) {
        FieldCell observedBase = fieldCell(string(alias.get(
                "accessFieldSignature")));
        int baseReceiver = number(alias, "fieldReceiverObjectId");
        int intermediateOwner = number(alias, "valueObjectId");
        int leafReceiver = number(canonical, "fieldReceiverObjectId");
        if (!Boolean.TRUE.equals(alias.get("observed"))
                || !"HEAP_OBJECT_FIELD".equals(string(alias.get(
                "location")))
                || !"FIELD_READ".equals(string(alias.get("accessKind")))
                || !"RUNTIME_FIELD_ACCESS_DECLARATION".equals(string(
                alias.get("accessFieldAuthority")))
                || !baseField.signature().equals(observedBase.signature())) {
            return "PROJECTED_PRIMITIVE_BASE_FIELD_OBSERVATION_NOT_EXACT";
        }
        if (!baseField.type.equals(leaf.owner)
                || !primitiveType(leaf.type)) {
            return "PROJECTED_PRIMITIVE_LEAF_DECLARATION_MISMATCH";
        }
        if (baseReceiver == 0 || intermediateOwner == 0
                || leafReceiver == 0) {
            return "PROJECTED_PRIMITIVE_RUNTIME_IDENTITY_MISSING";
        }
        if (intermediateOwner != leafReceiver) {
            return "PROJECTED_PRIMITIVE_RUNTIME_FIELD_CHAIN_MISMATCH";
        }
        return exactRuntimeFieldAliasCutIssue(alias, canonical, leaf,
                fieldEvents, "PRIMITIVE");
    }

    private static String exactRuntimeFieldAliasCutIssue(
            Map<String, Object> alias, Map<String, Object> canonical,
            FieldCell leaf, List<FieldAccessEvent> fieldEvents,
            String aliasKind) {
        FieldAccessEvent baseRead = exactActionFieldEvent(alias, fieldEvents);
        FieldAccessEvent leafRead = exactActionFieldEvent(canonical,
                fieldEvents);
        if (baseRead == null || leafRead == null
                || baseRead.seq >= leafRead.seq) {
            return "PROJECTED_" + aliasKind
                    + "_RUNTIME_EVENT_ORDER_MISMATCH";
        }
        for (FieldAccessEvent event : values(fieldEvents)) {
            if (event.seq <= baseRead.seq || event.seq >= leafRead.seq
                    || !"FIELD_WRITE".equals(event.kind)
                    || event.receiverObjectId != leafRead.receiverObjectId
                    || !leaf.signature().equals(
                    event.parsedField.signature())) {
                continue;
            }
            return "PROJECTED_" + aliasKind
                    + "_INTERVENING_LEAF_WRITE";
        }
        return "";
    }

    private static FieldAccessEvent exactActionFieldEvent(
            Map<String, Object> action,
            List<FieldAccessEvent> fieldEvents) {
        if (!"CONTAINED_RUNTIME_FIELD_EVENT_SEQ_AND_CALL_ID_V1".equals(
                string(action.get("fieldEventIdentityAuthority")))) {
            return null;
        }
        long seq = longNumber(action, "fieldEventSeq");
        long callId = longNumber(action, "fieldCallId");
        FieldCell field = fieldCell(string(action.get(
                "accessFieldSignature")));
        int receiver = number(action, "fieldReceiverObjectId");
        if (seq <= 0L || callId <= 0L || !field.declaredSignature
                || receiver == 0) {
            return null;
        }
        FieldAccessEvent selected = null;
        for (FieldAccessEvent event : values(fieldEvents)) {
            if (event.seq != seq || event.callId != callId
                    || !"FIELD_READ".equals(event.kind)
                    || event.receiverObjectId != receiver
                    || !field.signature().equals(
                    event.parsedField.signature())) {
                continue;
            }
            if (selected != null) {
                return null;
            }
            selected = event;
        }
        return selected;
    }

    private static String exactRuntimeArrayAliasIssue(
            Map<String, Object> alias, Map<String, Object> canonical,
            FieldCell baseField, FieldCell leaf,
            List<FieldAccessEvent> fieldEvents) {
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
        return exactRuntimeFieldAliasCutIssue(alias, canonical, leaf,
                fieldEvents, "ARRAY");
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
    }

    private static int number(Map<String, Object> row, String field) {
        Object value = row == null ? null : row.get(field);
        return value instanceof Number ? ((Number) value).intValue() : 0;
    }

    private static long longNumber(Map<String, Object> row, String field) {
        Object value = row == null ? null : row.get(field);
        return value instanceof Number ? ((Number) value).longValue() : 0L;
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
    private static void refineMapValueElementProjectionActivations(
            Result result) {
        Map<String, List<Map<String, Object>>> selectedByInstance =
                new LinkedHashMap<>();
        for (Map<String, Object> activation : result.activations) {
            UpstreamOutputMemberPlan member =
                    singletonPlannerOutputMember(activation);
            if (!"OUTPUT_CLOSURE".equals(captureGoalKind(activation))
                    || member == null || !member.outputSlice.complete) {
                continue;
            }
            String instance = string(activation.get("regionInstanceId"));
            if (!instance.isEmpty()) {
                add(selectedByInstance, instance, activation);
            }
        }

        for (Map<String, Object> activation : result.activations) {
            UpstreamOutputMemberPlan producerMember =
                    singletonPlannerOutputMember(activation);
            Map<String, Object> producerSlice = producerMember == null
                    ? null : producerMember.outputSlice.toMap();
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
                    UpstreamOutputMemberPlan downstreamMember =
                            singletonPlannerOutputMember(downstream);
                    if (downstreamMember == null) {
                        continue;
                    }
                    for (Map<String, Object> declaration : mapRows(
                            downstreamMember.outputSlice.toMap().get(
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
                            "outputPort", producerMember.output.portId,
                            "outputCell", producerMember.output.cell,
                            "outputFieldPath", proof.outputFieldPath,
                            "outputValidationMode",
                            producerMember.outputSlice.captureBindingsRequired
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
                            "crossExecutionOrdinalAuthority", "NONE",
                            "projectionProofCausalEdgeIds",
                            proof.causalEdgeIds,
                            "complete", true);
                    declarations.add(declaration);
                }
            }

            activation.put("mapValueElementFieldProjections",
                    declarations);
            boolean composable = issues.isEmpty()
                    && !declarations.isEmpty();
            activation.remove("recursiveElementProjectionCompositionGap");
            // Preserve all pre-existing readiness decisions when the static
            // declaration is complete. Runtime identity evidence is checked
            // later by the importer. A static proof/declaration failure still
            // closes this activation before scheduling.
            if (!composable) {
                activation.put("admission", admission(false, false,
                        admissionMode(activation), issues, false, false));
            }
        }
    }

    private static String captureGoalKind(Map<String, Object> activation) {
        Map<String, Object> goal = mapValue(activation.get("captureGoal"));
        return goal == null ? "" : string(goal.get("kind"));
    }

    private static UpstreamOutputMemberPlan singletonPlannerOutputMember(
            Map<String, Object> activation) {
        Object encoded = activation == null ? null
                : activation.get("_plannerOutputMembers");
        if (!(encoded instanceof List<?>)
                || ((List<?>) encoded).size() != 1
                || !(((List<?>) encoded).get(0)
                instanceof UpstreamOutputMemberPlan)) {
            return null;
        }
        return (UpstreamOutputMemberPlan) ((List<?>) encoded).get(0);
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
            boolean directPathSnapshot =
                    "STATIC_EXACT_DIRECT_ARRAY_ELEMENT_FIELD_PATH_"
                    .concat("CHAIN_V1").equals(string(declaration.get(
                    "proofAuthority")));
            if (bindingId.isEmpty() || !bindingIds.add(bindingId)
                    || baseAction == null || containerAction == null
                    || baseAction == containerAction
                    || !directPathSnapshot
                    && !fieldSignature.equals(string(baseAction.get(
                    "cell")))
                    || !containerCell.equals(string(containerAction.get(
                    "cell")))) {
                return false;
            }
            String observedBaseField = string(baseAction.get("field"));
            String observedContainerField = string(containerAction.get(
                    "field"));
            if (!directPathSnapshot && !observedBaseField.isEmpty()
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
            if (path.isEmpty() || path.size() > 4
                    || !field.name.equals(path.get(path.size() - 1))) {
                return false;
            }
            FieldCell accessField = field;
            if (directPathSnapshot) {
                String baseCell = string(baseAction.get("cell"));
                accessField = fieldCell(baseCell);
                if (!accessField.declaredSignature
                        || !path.equals(dependencyFieldPath(baseCell))
                        || !path.equals(stringList(baseAction.get(
                        "fieldPath")))
                        || !fieldSignature.equals(string(baseAction.get(
                        "leafFieldSignature")))
                        || !accessField.signature().equals(string(
                        baseAction.get("accessFieldSignature")))
                        || !accessField.name.equals(string(baseAction.get(
                        "accessField")))
                        || !accessField.owner.equals(string(baseAction.get(
                        "accessOwnerClass")))) {
                    return false;
                }
                baseAction.put("leafFieldSignature", field.signature());
                baseAction.put("leafOwnerClass", field.owner);
                baseAction.put("leafField", field.name);
            }
            // The hook stays on the first declared field, but the symbolic
            // identity denotes only the final scalar leaf.
            baseAction.put("field", directPathSnapshot
                    ? field.signature() : accessField.signature());
            baseAction.put("fieldPath", path);
            baseAction.put("bindingMode", "FIELD_ACCESS");
            baseAction.put("accessOwnerClass", accessField.owner);
            baseAction.put("accessField", accessField.name);
            baseAction.put("accessFieldType", accessField.type);
            baseAction.put("javaType", field.type);
            baseAction.put("accessFieldSignature", accessField.signature());
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
                    && SymbolicEnvironment.isCurrentTimeMillisReturn(
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
     * instance. A digest match alone is not enough when several concurrent
     * transfers carry the same value, so the nearest matching endpoint is the
     * authority for transfer order.
     */
    private static Map<String, List<FingerprintMatch>>
    nearestEndpointFingerprintMatches(
            StaticRegionEdge edge, List<InstanceEvidence> sources,
            List<InstanceEvidence> targets) {
        Map<String, List<FingerprintMatch>> result = new LinkedHashMap<>();
        if ("SHARED_STATE".equals(edge.kind)) {
            return result;
        }
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
                    if (betterEndpointCorrelation(sourceInstance, candidate,
                            bestInstance, bestMatch)) {
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
            InstanceEvidence candidateInstance,
            FingerprintMatch candidate,
            InstanceEvidence currentInstance,
            FingerprintMatch current) {
        if (currentInstance == null) {
            return true;
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

    private static String endpointCorrelationAuthority() {
        return "NEAREST_PRECEDING_MATCHING_SOURCE_ENDPOINT";
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
        // Runtime instance correlation intentionally keeps using the raw
        // protocol endpoint (see endpointPairObserved).  A projected method
        // local, however, does not carry a declared field owner and therefore
        // cannot safely match a FIELD_READ/FIELD_WRITE fingerprint by itself.
        // When the static edge supplies a complete exact alias proof, use the
        // canonical producer output cell solely for source value capture.
        // The consumer remains tied to its raw runtime endpoint.
        String port = source
                ? edge.sourceFingerprintEndpoint(evidence.region)
                : edge.toPort;
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
        if (!upstream.containedCallTreeComplete
                || !downstream.containedCallTreeComplete) {
            return null;
        }
        FieldCell fromField = edge.fromField;
        FieldCell toField = edge.toField;
        if (!fromField.materializable() || !toField.materializable()
                || !sameField(fromField, toField)) {
            return null;
        }
        SharedReadFrom selected = null;
        for (FieldAccessEvent write : upstream.fieldEvents) {
            if (!sameField(fromField, write.parsedField)
                    || write.receiverObjectId == 0) {
                continue;
            }
            for (FieldAccessEvent read : downstream.fieldEvents) {
                if (!"FIELD_READ".equals(read.kind)
                        || !sameField(toField, read.parsedField)
                        || read.receiverObjectId == 0
                        || write.receiverObjectId != read.receiverObjectId) {
                    continue;
                }
                WriteEvidence writeEvidence = writeEvidence(write, upstream,
                        read.seq);
                if (writeEvidence == null) {
                    continue;
                }
                if (writeEvidence.mutation != null
                        && (write.valueObjectId == 0
                        || read.valueObjectId == 0
                        || write.valueObjectId != read.valueObjectId)) {
                    continue;
                }
                SharedReadFrom candidate = new SharedReadFrom(write, read,
                        writeEvidence);
                if (selected == null
                        || candidate.writerEventSeq()
                        > selected.writerEventSeq()) {
                    selected = candidate;
                }
            }
        }
        return selected;
    }

    private static WriteEvidence writeEvidence(FieldAccessEvent field,
                                               InstanceEvidence instance,
                                               long readSeq) {
        if ("FIELD_WRITE".equals(field.kind)) {
            if (field.seq > readSeq) {
                return null;
            }
            return new WriteEvidence(null, null);
        }
        if (!"FIELD_READ".equals(field.kind) || field.valueObjectId == 0) {
            return null;
        }
        WriteEvidence selected = null;
        for (RuntimeEvent event : instance.runtimeEvents) {
            if (event.seq <= field.seq
                    || !"CALL_SITE_ENTER".equals(event.kind)
                    || event.objectId != field.valueObjectId
                    || !isContainerMutator(event.declaredCallee)) {
                continue;
            }
            RuntimeEvent completion = completedCall(event,
                    instance.runtimeEvents);
            if (completion == null || completion.seq > readSeq) {
                continue;
            }
            if (event.callId != field.callId
                    && !instance.calls.contains(event.callId)) {
                continue;
            }
            WriteEvidence candidate = new WriteEvidence(event, completion);
            if (selected == null
                    || candidate.writerEventSeq()
                    > selected.writerEventSeq()) {
                selected = candidate;
            }
        }
        return selected;
    }

    private static RuntimeEvent completedCall(RuntimeEvent enter,
                                              List<RuntimeEvent> events) {
        if (enter == null || enter.invocationId <= 0L) {
            return null;
        }
        for (RuntimeEvent event : events) {
            if (event.seq > enter.seq
                    && "CALL_SITE_RETURN".equals(event.kind)
                    && event.invocationId == enter.invocationId
                    && event.callId == enter.callId
                    && event.siteId.equals(enter.siteId)) {
                return event;
            }
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

    private static void addNonBlank(Set<String> values, String value) {
        String normalized = safe(value);
        if (!normalized.isEmpty()) {
            values.add(normalized);
        }
    }

    private static StaticProjectionIndex readStaticProjectionIndex(File file) {
        StaticProjectionIndex result = new StaticProjectionIndex();
        if (!file.isFile()) {
            result.catalogReadComplete = false;
            result.catalogFailure = "FROZEN_STATIC_GRAPH_NOT_FOUND";
            return result;
        }
        try (BufferedReader reader = Files.newBufferedReader(file.toPath(),
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                result.catalogRowCount++;
                StaticDataflowProjectionEdge edge =
                        StaticDataflowProjectionEdge.fromJson(line);
                if (edge == null || edge.edgeId.isEmpty()
                        || result.byId.containsKey(edge.edgeId)) {
                    result.catalogInvalidRowCount++;
                    continue;
                }
                result.add(edge,
                        StaticOutputSlice.causalEdgeReference(line));
            }
        } catch (IOException exception) {
            result.catalogReadComplete = false;
            result.catalogFailure = "FROZEN_STATIC_GRAPH_READ_FAILED";
        }
        if (result.catalogReadComplete && result.catalogRowCount == 0) {
            result.catalogFailure = "FROZEN_STATIC_GRAPH_EMPTY";
        } else if (result.catalogReadComplete
                && result.catalogInvalidRowCount > 0) {
            result.catalogFailure = "FROZEN_STATIC_GRAPH_INVALID_ROWS:"
                    + result.catalogInvalidRowCount;
        }
        return result;
    }

    private static void resolveStaticCausalEdgeReferences(
            List<StaticRegion> regions, StaticProjectionIndex projections) {
        for (StaticRegion region : regions) {
            for (StaticOutputSlice slice : region.outputSlices.values()) {
                String failure = projections.resolveCausalEdges(slice);
                if (failure.isEmpty()) {
                    continue;
                }
                slice.structuralComplete = false;
                slice.complete = false;
                if (!slice.structuralIssues.contains(failure)) {
                    slice.structuralIssues.add(failure);
                }
            }
        }
    }

    private static List<StaticRegion> readRegions(File file) {
        List<StaticRegion> result = new ArrayList<>();
        if (file == null || !file.isFile()) {
            throw new IllegalArgumentException(
                    "symbolic region artifact is required: " + file);
        }
        try (BufferedReader reader = Files.newBufferedReader(file.toPath(),
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                String trimmed = line.trim();
                if (trimmed.isEmpty()) {
                    continue;
                }
                if (jsonTopLevelInt(trimmed, "schemaVersion", -1)
                        != STATIC_REGION_SCHEMA_VERSION) {
                    throw new IllegalArgumentException(
                            "unsupported symbolic region schema");
                }
                StaticRegion region = StaticRegion.fromJson(trimmed);
                if (region.regionId.isEmpty() || region.rootMethod.isEmpty()) {
                    throw new IllegalArgumentException(
                            "malformed symbolic region row");
                }
                result.add(region);
            }
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "failed to read symbolic regions: " + file, exception);
        }
        return result;
    }

    private static List<StaticRegionEdge> readRegionEdges(File file) {
        List<StaticRegionEdge> result = new ArrayList<>();
        if (file == null) {
            return result;
        }
        if (!file.isFile()) {
            throw new IllegalArgumentException(
                    "symbolic region edge artifact is missing: " + file);
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
                    throw new IllegalArgumentException(
                            "malformed symbolic region edge row");
                }
                result.add(edge);
            }
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "failed to read symbolic region edges: " + file,
                    exception);
        }
        return result;
    }

    /**
     * Older frozen catalogs assigned a mapping-only protocol edge to the
     * first region that enclosed its producer endpoint.  The endpoint can be
     * enclosed by several roots, however, and the concrete workload is the
     * authority for which root actually produced a transfer.  Recover all
     * producer candidates using exact catalog identity only.  Runtime value
     * fingerprint and ordering validation subsequently chooses a unique
     * candidate; no region or protocol name participates in this expansion.
     */
    private static List<StaticRegionEdge>
    expandMappingOnlyProtocolProducerRegions(
            List<StaticRegion> regions, List<StaticRegionEdge> edges) {
        List<StaticRegionEdge> result = new ArrayList<>();
        int catalogOrdinal = 0;
        for (StaticRegionEdge edge : edges) {
            if (!edge.mappingOnlyProtocol()) {
                result.add(edge);
                catalogOrdinal++;
                continue;
            }
            List<String> producerRegions = new ArrayList<>();
            Set<String> seen = new LinkedHashSet<>();
            for (StaticRegion region : regions) {
                if (edge.hasExactProducerOutput(region)
                        && seen.add(region.regionId)) {
                    producerRegions.add(region.regionId);
                }
            }
            if (producerRegions.isEmpty()) {
                result.add(edge);
                catalogOrdinal++;
                continue;
            }
            String group = "REGION_EDGE_PRODUCER_CANDIDATES."
                    + catalogOrdinal;
            for (String producerRegion : producerRegions) {
                result.add(edge.forProducerRegion(producerRegion, group));
            }
            catalogOrdinal++;
        }
        return result;
    }

    static final class Result {
        final List<Map<String, Object>> activations = new ArrayList<>();
        final List<Map<String, Object>> edgeValidations = new ArrayList<>();

        String activationsJsonl() {
            return jsonl(activations);
        }

        String edgeValidationsJsonl() {
            return jsonl(edgeValidations);
        }

    }

    /**
     * One-pass lookup table for exact root METHOD_ARGUMENT runtime types.
     * The trace may contain hundreds of thousands of unrelated execution
     * events, so selectors must not rediscover the same (method, callId)
     * facts by scanning that trace once per candidate root.
     */
    static final class RootArgumentRuntimeTypeIndex {
        private final Map<String, Map<Long, RootArgumentTypes>> byMethod =
                new LinkedHashMap<>();

        static RootArgumentRuntimeTypeIndex build(
                List<RuntimeEvent> runtimeEvents) {
            RootArgumentRuntimeTypeIndex result =
                    new RootArgumentRuntimeTypeIndex();
            for (RuntimeEvent event : values(runtimeEvents)) {
                if (!"METHOD_ARGUMENT".equals(event.kind)
                        || event.argumentIndex < 0
                        || event.runtimeType.isEmpty()) {
                    continue;
                }
                Map<Long, RootArgumentTypes> byCall = result.byMethod.get(
                        event.method);
                if (byCall == null) {
                    byCall = new LinkedHashMap<>();
                    result.byMethod.put(event.method, byCall);
                }
                RootArgumentTypes types = byCall.get(event.callId);
                if (types == null) {
                    types = new RootArgumentTypes();
                    byCall.put(event.callId, types);
                }
                types.observe(event.argumentIndex, event.runtimeType);
            }
            for (Map<Long, RootArgumentTypes> byCall
                    : result.byMethod.values()) {
                for (RootArgumentTypes types : byCall.values()) {
                    types.freeze();
                }
            }
            return result;
        }

        Map<Integer, String> typesFor(MethodEvent method) {
            if (method == null) {
                return Collections.emptyMap();
            }
            Map<Long, RootArgumentTypes> byCall = byMethod.get(method.method);
            if (byCall == null) {
                return Collections.emptyMap();
            }
            RootArgumentTypes types = byCall.get(method.callId);
            return types == null ? Collections.emptyMap() : types.values();
        }

    }

    private static final class RootArgumentTypes {
        private final Map<Integer, String> observed = new LinkedHashMap<>();
        private final Set<Integer> ambiguous = new LinkedHashSet<>();
        private Map<Integer, String> frozen = Collections.emptyMap();

        private void observe(int index, String runtimeType) {
            if (ambiguous.contains(index)) {
                return;
            }
            String previous = observed.get(index);
            if (previous == null) {
                observed.put(index, runtimeType);
            } else if (!previous.equals(runtimeType)) {
                observed.remove(index);
                ambiguous.add(index);
            }
        }

        private void freeze() {
            frozen = Collections.unmodifiableMap(
                    new LinkedHashMap<>(observed));
        }

        private Map<Integer, String> values() {
            return frozen;
        }
    }

    private static final class ContainedCallSelection {
        private final Set<Long> calls;
        private final boolean truncated;

        private ContainedCallSelection(Set<Long> calls, boolean truncated) {
            this.calls = calls;
            this.truncated = truncated;
        }
    }

    private static final class PathSignatureSelection {
        private final boolean truncated;

        private PathSignatureSelection(boolean truncated) {
            this.truncated = truncated;
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

        MethodEvent(long seq, String test, String process, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId) {
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
        final boolean hasSuccessorIndex;
        final int successorIndex;
        final String branchKind;
        final String switchCaseKeys;

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
            this(seq, kind, method, callId, invocationId, parentSiteId,
                    siteId, declaredCallee, argumentIndex, runtimeType,
                    objectId, primitiveValue, hasOutcome, outcome,
                    valueFingerprint, valueFingerprintComplete,
                    valueFingerprintNodes, valueFingerprintReason,
                    false, -1, "", "");
        }

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     String declaredCallee, int argumentIndex,
                     String runtimeType, int objectId,
                     String primitiveValue, boolean hasOutcome,
                     boolean outcome, String valueFingerprint,
                     boolean valueFingerprintComplete,
                     int valueFingerprintNodes,
                     String valueFingerprintReason,
                     boolean hasSuccessorIndex, int successorIndex,
                     String branchKind, String switchCaseKeys) {
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
            this.hasSuccessorIndex = hasSuccessorIndex;
            this.successorIndex = successorIndex;
            this.branchKind = safe(branchKind);
            this.switchCaseKeys = safe(switchCaseKeys);
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
        final FieldCell parsedField;
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
            this.parsedField = fieldCell(this.field);
            this.receiverObjectId = receiverObjectId;
            this.valueObjectId = valueObjectId;
            this.primitiveValue = safe(primitiveValue);
            this.valueFingerprint = safe(valueFingerprint);
            this.valueFingerprintComplete = valueFingerprintComplete;
            this.valueFingerprintNodes = valueFingerprintNodes;
            this.valueFingerprintReason = safe(valueFingerprintReason);
        }
    }

    /**
     * Immutable indexes over the sorted trace. Per-root planning walks the
     * concrete child-call tree and touches only events owned by that subtree;
     * it no longer rescans the complete method/runtime/field trace for every
     * region instance.
     */
    private static final class RuntimeTraceIndex {
        private final Map<Long, MethodEvent> methodsByCall =
                new LinkedHashMap<>();
        private final Map<String, List<MethodEvent>> methodsBySignature =
                new LinkedHashMap<>();
        private final Map<Long, List<MethodEvent>> childrenByParent =
                new LinkedHashMap<>();
        private final Map<Long, List<RuntimeEvent>> runtimeByCall =
                new LinkedHashMap<>();
        private final Map<Long, List<FieldAccessEvent>> fieldsByCall =
                new LinkedHashMap<>();
        private final Map<Long, Integer> globalOrdinals =
                new LinkedHashMap<>();
        private final Map<Long, Integer> contextOrdinals =
                new LinkedHashMap<>();

        private static RuntimeTraceIndex build(
                List<MethodEvent> methods, List<RuntimeEvent> runtime,
                List<FieldAccessEvent> fields) {
            RuntimeTraceIndex result = new RuntimeTraceIndex();
            Map<String, Integer> globalCounts = new LinkedHashMap<>();
            Map<String, Integer> contextCounts = new LinkedHashMap<>();
            for (MethodEvent event : values(methods)) {
                result.methodsByCall.put(event.callId, event);
                add(result.methodsBySignature, event.method, event);
                result.childrenByParent.computeIfAbsent(event.parentCallId,
                        ignored -> new ArrayList<>()).add(event);

                String global = event.test + "\n" + event.method;
                int globalOrdinal = globalCounts.getOrDefault(global, 0) + 1;
                globalCounts.put(global, globalOrdinal);
                result.globalOrdinals.put(event.callId, globalOrdinal);

                String context = global + "\n" + event.receiverType + "\n"
                        + stableRootThreadContext(event.threadName);
                int contextOrdinal =
                        contextCounts.getOrDefault(context, 0) + 1;
                contextCounts.put(context, contextOrdinal);
                result.contextOrdinals.put(event.callId, contextOrdinal);
            }
            for (RuntimeEvent event : values(runtime)) {
                result.runtimeByCall.computeIfAbsent(event.callId,
                        ignored -> new ArrayList<>()).add(event);
            }
            for (FieldAccessEvent event : values(fields)) {
                result.fieldsByCall.computeIfAbsent(event.callId,
                        ignored -> new ArrayList<>()).add(event);
            }
            return result;
        }

        private int invocationOrdinal(MethodEvent method) {
            return globalOrdinals.getOrDefault(method.callId, 1);
        }

        private int invocationOrdinalWithinContext(MethodEvent method) {
            return contextOrdinals.getOrDefault(method.callId, 1);
        }

        private ContainedCallSelection containedCalls(MethodEvent root) {
            Set<Long> calls = new LinkedHashSet<>();
            Deque<Long> pending = new ArrayDeque<>();
            calls.add(root.callId);
            pending.add(root.callId);
            boolean truncated = false;
            while (!pending.isEmpty()) {
                long parent = pending.removeFirst();
                for (MethodEvent child : values(childrenByParent.get(parent))) {
                    if (child.seq < root.seq || !sameContext(root, child)
                            || calls.contains(child.callId)) {
                        continue;
                    }
                    if (calls.size() >= MAX_CALLS_PER_INSTANCE) {
                        truncated = true;
                        continue;
                    }
                    calls.add(child.callId);
                    pending.addLast(child.callId);
                }
            }
            return new ContainedCallSelection(calls, truncated);
        }

        private List<MethodEvent> methods(Set<Long> calls) {
            List<MethodEvent> result = new ArrayList<>();
            for (long call : calls) {
                MethodEvent event = methodsByCall.get(call);
                if (event != null) result.add(event);
            }
            result.sort(Comparator.comparingLong(value -> value.seq));
            return result;
        }

        private List<RuntimeEvent> runtimeEvents(Set<Long> calls) {
            List<RuntimeEvent> result = new ArrayList<>();
            for (long call : calls) {
                result.addAll(values(runtimeByCall.get(call)));
            }
            result.sort(Comparator.comparingLong(value -> value.seq));
            return result;
        }

        private List<FieldAccessEvent> fieldEvents(Set<Long> calls) {
            List<FieldAccessEvent> result = new ArrayList<>();
            for (long call : calls) {
                result.addAll(values(fieldsByCall.get(call)));
            }
            result.sort(Comparator.comparingLong(value -> value.seq));
            return result;
        }
    }

    /**
     * Indexed runtime heap events used by the post-runtime demand slice.  A
     * field is crossed only when one exact executed FIELD_READ can be joined
     * to the frozen HEAP_READ row and the latest same-object write is both
     * inside the selected call closure and joined to one frozen HEAP_WRITE
     * RHS.  Missing or ambiguous joins remain concrete.
     */
    private static final class RuntimeFieldAccessIndex {
        private final Map<String, List<FieldAccessEvent>> readsBySite =
                new LinkedHashMap<>();
        private final Map<String, List<FieldAccessEvent>> writesByContext =
                new LinkedHashMap<>();
        private final Map<String, List<FieldAccessEvent>> unscopedWrites =
                new LinkedHashMap<>();

        private static RuntimeFieldAccessIndex build(
                List<FieldAccessEvent> fields,
                Map<Long, MethodEvent> calls) {
            RuntimeFieldAccessIndex result = new RuntimeFieldAccessIndex();
            for (FieldAccessEvent event : values(fields)) {
                String field = exactFieldKey(event.field);
                if (field.isEmpty()) {
                    continue;
                }
                if ("FIELD_READ".equals(event.kind)
                        && exactRuntimeFieldSite(event)) {
                    add(result.readsBySite, fieldSiteKey(event.method,
                            event.siteId, event.unitIndex, field), event);
                } else if ("FIELD_WRITE".equals(event.kind)) {
                    MethodEvent call = calls == null ? null
                            : calls.get(event.callId);
                    if (call == null) {
                        add(result.unscopedWrites,
                                receiverFieldKey(event.receiverObjectId,
                                        field), event);
                    } else {
                        add(result.writesByContext, contextFieldKey(
                                call.test, call.process,
                                event.receiverObjectId, field), event);
                    }
                }
            }
            return result;
        }

        private RuntimeHeapDefinition reachingDefinition(
                StaticDataflowProjectionEdge readDefinition,
                MethodEvent root, Set<Long> containedCalls,
                Set<String> observedMethods,
                StaticProjectionIndex staticProjections) {
            String field = exactFieldKey(readDefinition.fromCell);
            if (root == null || containedCalls == null
                    || staticProjections == null || field.isEmpty()) {
                return RuntimeHeapDefinition.concrete();
            }

            List<FieldAccessEvent> matchingReads = new ArrayList<>();
            for (FieldAccessEvent event : values(readsBySite.get(
                    fieldSiteKey(readDefinition.method,
                            readDefinition.siteId,
                            readDefinition.unitIndex, field)))) {
                if (containedCalls.contains(event.callId)) {
                    matchingReads.add(event);
                }
            }
            if (matchingReads.size() != 1) {
                return RuntimeHeapDefinition.concrete();
            }

            FieldAccessEvent read = matchingReads.get(0);
            if (read.receiverObjectId == 0) {
                return RuntimeHeapDefinition.concrete();
            }

            List<FieldAccessEvent> writes = values(writesByContext.get(
                    contextFieldKey(root.test, root.process,
                            read.receiverObjectId, field)));
            FieldAccessEvent latest = latestBefore(writes, read.seq);
            FieldAccessEvent unknown = latestBefore(values(
                    unscopedWrites.get(receiverFieldKey(
                            read.receiverObjectId, field))), read.seq);
            if (unknown != null && (latest == null
                    || unknown.seq >= latest.seq)) {
                return RuntimeHeapDefinition.concrete();
            }
            if (latest == null) {
                return RuntimeHeapDefinition.entry();
            }
            if (!containedCalls.contains(latest.callId)) {
                return RuntimeHeapDefinition.entry();
            }

            StaticDataflowProjectionEdge writeDefinition =
                    staticProjections.uniqueRuntimeHeapWriteDefinition(
                            latest, readDefinition.fromCell,
                            observedMethods);
            if (writeDefinition == null) {
                return RuntimeHeapDefinition.concrete();
            }
            return RuntimeHeapDefinition.internal(writeDefinition);
        }

        private static FieldAccessEvent latestBefore(
                List<FieldAccessEvent> events, long upperExclusive) {
            int low = 0;
            int high = events.size();
            while (low < high) {
                int middle = (low + high) >>> 1;
                if (events.get(middle).seq < upperExclusive) {
                    low = middle + 1;
                } else {
                    high = middle;
                }
            }
            return low == 0 ? null : events.get(low - 1);
        }

        private static boolean exactRuntimeFieldSite(
                FieldAccessEvent event) {
            return event != null && !event.method.isEmpty()
                    && !event.siteId.isEmpty() && event.unitIndex >= 0;
        }

        private static String exactFieldKey(String field) {
            FieldCell parsed = fieldCell(field);
            return parsed.declaredSignature && parsed.materializable()
                    ? parsed.owner + '\n' + parsed.type + '\n' + parsed.name
                    : "";
        }

        private static String fieldSiteKey(String method, String site,
                                           int unitIndex, String field) {
            return safe(method) + '\n' + safe(site) + '\n' + unitIndex
                    + '\n' + safe(field);
        }

        private static String receiverFieldKey(int receiver, String field) {
            return receiver + "\n" + safe(field);
        }

        private static String contextFieldKey(String test, String process,
                                              int receiver, String field) {
            return safe(test) + '\n' + safe(process) + '\n'
                    + receiverFieldKey(receiver, field);
        }
    }

    private static final class RuntimeHeapDefinition {
        private final boolean concreteBound;
        private final StaticDataflowProjectionEdge writeDefinition;

        private RuntimeHeapDefinition(boolean concreteBound,
                StaticDataflowProjectionEdge writeDefinition) {
            this.concreteBound = concreteBound;
            this.writeDefinition = writeDefinition;
        }

        private static RuntimeHeapDefinition internal(
                StaticDataflowProjectionEdge writeDefinition) {
            return new RuntimeHeapDefinition(false, writeDefinition);
        }

        private static RuntimeHeapDefinition entry() {
            return new RuntimeHeapDefinition(false, null);
        }

        private static RuntimeHeapDefinition concrete() {
            return new RuntimeHeapDefinition(true, null);
        }

        private boolean internal() {
            return writeDefinition != null;
        }

        private boolean concreteBound() {
            return concreteBound;
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
        private boolean inputSelectionComplete = true;
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

        private ConsumerInputResolution resolveConsumerInput(
                String endpoint, StaticProjectionIndex projections,
                Set<String> retainedPortIds, Set<String> demandEdgeIds,
                Set<String> observedMethods) {
            String value = safe(endpoint);
            StaticPort exact = null;
            int exactMatches = 0;
            for (StaticPort port : inputs) {
                if (retainedPortIds != null
                        && !retainedPortIds.contains(port.portId)) {
                    continue;
                }
                if (!value.equals(port.portId)
                        && !value.equals(port.cell)) {
                    continue;
                }
                exact = port;
                exactMatches++;
            }
            if (exactMatches == 1) {
                return new ConsumerInputResolution(exact, null);
            }
            if (exactMatches > 1 || projections == null) {
                return null;
            }
            List<StaticPort> retained = new ArrayList<>();
            for (StaticPort port : inputs) {
                if (retainedPortIds == null
                        || retainedPortIds.contains(port.portId)) {
                    retained.add(port);
                }
            }
            DirectDemandInputResolution direct =
                    projections.uniqueDirectDemandDefinition(value,
                            retained, demandEdgeIds, observedMethods);
            if (direct.ambiguous) {
                return null;
            }
            if (direct.port != null) {
                return new ConsumerInputResolution(direct.port, null);
            }
            StaticProjectionProof proof = projections.uniqueProof(value,
                    retained);
            return proof == null ? null
                    : new ConsumerInputResolution(proof.targetPort, proof);
        }

        private StaticPort exactInputFor(String endpoint) {
            return portFor(inputs, endpoint, false);
        }

        private StaticPort uniqueDemandFrontierPort(
                String cell, Set<String> observedMethods,
                String runtimeRootMethod) {
            StaticPort selected = null;
            for (StaticPort input : inputs) {
                if (!cell.equals(input.cell)) {
                    continue;
                }
                if (selected != null) {
                    return null;
                }
                selected = input;
            }
            if (selected == null) {
                return null;
            }
            if (exactDeclaredFieldCell(cell)) {
                return selected;
            }
            String sourceKind = selected.sourceKind;
            if ("ENVIRONMENT".equals(sourceKind)
                    || "PROTOCOL_INPUT".equals(sourceKind)) {
                return selected;
            }
            String method = methodInCell(cell);
            if (cell.contains(".param")
                    && safe(runtimeRootMethod).equals(method)) {
                return selected;
            }
            if ("OPAQUE_CALL".equals(sourceKind)
                    && !observedMethods.contains(method)) {
                return selected;
            }
            return null;
        }

        private boolean runtimeHeapReachingDefinitionEligible(String cell) {
            for (StaticPort input : inputs) {
                if (!cell.equals(input.cell)) {
                    continue;
                }
                // Protocol/environment boundaries can be represented by an
                // accessor or VM placeholder even when the frozen graph row
                // is spelled HEAP_READ.  They are not ordinary shared-heap
                // entry state and must retain their dedicated resolution.
                if (!"SHARED_HEAP".equals(input.sourceKind)) {
                    return false;
                }
            }
            return true;
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
                        jsonIntArray(object,
                                "requiredSuccessorIndices"),
                        jsonString(object, "branchKind"),
                        jsonIntArray(object, "switchCaseKeys"),
                        jsonInt(object, "defaultSuccessorIndex", -1)));
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
            region.inputSelectionComplete = jsonBoolean(json,
                    "inputSelectionComplete", true);
            return region;
        }
    }

    private static final class ConsumerInputResolution {
        private final StaticPort port;
        private final StaticProjectionProof projection;

        private ConsumerInputResolution(StaticPort port,
                                        StaticProjectionProof projection) {
            this.port = port;
            this.projection = projection;
        }
    }

    private static final class DirectDemandInputResolution {
        private final StaticPort port;
        private final boolean ambiguous;

        private DirectDemandInputResolution(StaticPort port,
                                            boolean ambiguous) {
            this.port = port;
            this.ambiguous = ambiguous;
        }

        private static DirectDemandInputResolution absent() {
            return new DirectDemandInputResolution(null, false);
        }

        private static DirectDemandInputResolution ambiguous() {
            return new DirectDemandInputResolution(null, true);
        }
    }

    /**
     * Exact static proof that an object-valued edge endpoint may be consumed
     * through one declared field projection.  Candidate discovery may inspect
     * the target cell spelling, but admission requires all three immutable
     * graph rows: the object-flow base edge, its field-sensitive projected
     * edge, and a Soot-resolved accessor declaration for that exact projected
     * receiver.
     */
    private static final class StaticProjectionProof {
        private final StaticPort targetPort;
        private final String baseCell;
        private final String targetCell;
        private final List<String> fieldPath;
        private final List<String> evidenceEdgeIds;
        private final String declaredFieldSignature;
        private final String declaredFieldType;

        private StaticProjectionProof(StaticPort targetPort,
                String baseCell, String targetCell, List<String> fieldPath,
                List<String> evidenceEdgeIds,
                String declaredFieldSignature, String declaredFieldType) {
            this.targetPort = targetPort;
            this.baseCell = safe(baseCell);
            this.targetCell = safe(targetCell);
            this.fieldPath = new ArrayList<>(fieldPath);
            this.evidenceEdgeIds = new ArrayList<>(evidenceEdgeIds);
            this.declaredFieldSignature = safe(declaredFieldSignature);
            this.declaredFieldType = safe(declaredFieldType);
        }

        private boolean sameDeclaration(StaticProjectionProof other) {
            return other != null && baseCell.equals(other.baseCell)
                    && targetCell.equals(other.targetCell)
                    && fieldPath.equals(other.fieldPath)
                    && declaredFieldSignature.equals(
                    other.declaredFieldSignature)
                    && declaredFieldType.equals(other.declaredFieldType);
        }
    }

    private static final class StaticProjectionIndex {
        private boolean catalogReadComplete = true;
        private int catalogRowCount;
        private int catalogInvalidRowCount;
        private String catalogFailure = "";
        private final Map<String, StaticDataflowProjectionEdge> byId =
                new LinkedHashMap<>();
        private final Map<String, Map<String, Object>> causalReferencesById =
                new LinkedHashMap<>();
        private final Map<String, List<StaticDataflowProjectionEdge>>
                projectedByObjectCell = new LinkedHashMap<>();
        private final Map<String, List<StaticDataflowProjectionEdge>>
                declarationsByProjectedCell = new LinkedHashMap<>();
        private final Map<String, List<StaticDataflowProjectionEdge>>
                incomingByCell = new LinkedHashMap<>();
        private final Map<String, List<StaticDataflowProjectionEdge>>
                guardsBySite = new LinkedHashMap<>();
        private void add(StaticDataflowProjectionEdge edge,
                         Map<String, Object> causalReference) {
            if (edge == null || edge.edgeId.isEmpty()) {
                return;
            }
            byId.put(edge.edgeId, edge);
            if (causalReference != null) {
                causalReferencesById.put(edge.edgeId,
                        new LinkedHashMap<>(causalReference));
            }
            if (!edge.toCell.isEmpty()) {
                RuntimeRegionPlanner.add(incomingByCell, edge.toCell, edge);
            }
            if ("GUARD".equals(edge.transferKind)
                    && !edge.siteId.isEmpty()) {
                RuntimeRegionPlanner.add(guardsBySite, edge.siteId, edge);
            }
            if (edge.exactProjectedFieldEdge()) {
                if (!edge.objectFromCell.isEmpty()) {
                    RuntimeRegionPlanner.add(projectedByObjectCell,
                            edge.objectFromCell, edge);
                }
                if (!edge.objectToCell.isEmpty()
                        && !edge.objectToCell.equals(edge.objectFromCell)) {
                    RuntimeRegionPlanner.add(projectedByObjectCell,
                            edge.objectToCell, edge);
                }
            }
            if (edge.exactResolvedAccessorDeclaration()) {
                RuntimeRegionPlanner.add(declarationsByProjectedCell,
                        edge.fromCell, edge);
            }
        }

        private String resolveCausalEdges(StaticOutputSlice slice) {
            slice.causalEdges.clear();
            if (slice.causalEdgeIds.isEmpty()) {
                return "";
            }
            if (!catalogReadComplete || catalogRowCount == 0
                    || catalogInvalidRowCount > 0) {
                return firstNonBlank(catalogFailure,
                        "STATIC_DATAFLOW_CATALOG_NOT_AUTHORITATIVE");
            }
            Set<String> seen = new LinkedHashSet<>();
            for (String id : slice.causalEdgeIds) {
                Map<String, Object> reference = causalReferencesById.get(id);
                if (id.isEmpty() || !seen.add(id) || reference == null) {
                    slice.causalEdges.clear();
                    return "STATIC_CAUSAL_EDGE_ID_UNRESOLVED:" + id;
                }
                slice.causalEdges.add(new LinkedHashMap<>(reference));
            }
            return "";
        }

        private StaticProjectionProof uniqueProof(String baseCell,
                                                   List<StaticPort> ports) {
            StaticProjectionProof selected = null;
            for (StaticPort port : ports) {
                StaticProjectionProof proof = proofFor(baseCell, port);
                if (proof == null) {
                    continue;
                }
                // Uniqueness is over target region input declarations, not
                // merely cell text. Duplicate ports are ambiguous too.
                if (selected != null) {
                    return null;
                }
                selected = proof;
            }
            return selected;
        }

        private StaticProjectionProof proofFor(String baseCell,
                                                StaticPort targetPort) {
            StaticProjectionProof selected = null;
            for (StaticDataflowProjectionEdge projected : values(
                    projectedByObjectCell.get(baseCell))) {
                ProjectionOrientation orientation = projected.orientation(
                        baseCell, targetPort.cell);
                if (orientation == null) {
                    continue;
                }
                StaticDataflowProjectionEdge base = byId.get(
                        projected.projectionBaseEdgeId);
                if (!projected.exactlyProjects(base, orientation)) {
                    continue;
                }
                for (StaticDataflowProjectionEdge declaration : values(
                        declarationsByProjectedCell.get(
                                orientation.peerProjectedCell))) {
                    if (!declaration.declares(orientation.peerObjectCell,
                            orientation.peerProjectedCell,
                            projected.fieldPath)) {
                        continue;
                    }
                    StaticProjectionProof candidate =
                            new StaticProjectionProof(targetPort, baseCell,
                                    targetPort.cell, projected.fieldPath,
                                    java.util.Arrays.asList(base.edgeId,
                                            projected.edgeId,
                                            declaration.edgeId),
                                    declaration.declaredFieldSignature,
                                    declaration.declaredFieldType);
                    if (selected == null) {
                        selected = candidate;
                    } else if (!selected.sameDeclaration(candidate)) {
                        // Conflicting resolved declarations make even one
                        // target input unsafe to canonicalize.
                        return null;
                    }
                }
            }
            return selected;
        }

        /**
         * Resolves a raw runtime endpoint through one exact definition that
         * the concrete demand slice itself selected.  This is deliberately
         * narrower than arbitrary graph reachability: an unrelated frozen
         * edge cannot revive a pruned candidate input, and two distinct
         * retained inputs fail closed.
         */
        private DirectDemandInputResolution uniqueDirectDemandDefinition(
                String endpoint, List<StaticPort> retainedPorts,
                Set<String> demandEdgeIds, Set<String> observedMethods) {
            if (endpoint.isEmpty() || retainedPorts.isEmpty()
                    || demandEdgeIds == null || demandEdgeIds.isEmpty()
                    || observedMethods == null || observedMethods.isEmpty()) {
                return DirectDemandInputResolution.absent();
            }
            StaticPort selected = null;
            for (StaticDataflowProjectionEdge edge : values(
                    incomingByCell.get(endpoint))) {
                if (!demandEdgeIds.contains(edge.edgeId)
                        || !edge.toCell.equals(endpoint)
                        || !edge.exactDirectDemandInputDefinition(
                        observedMethods)) {
                    continue;
                }
                for (StaticPort port : retainedPorts) {
                    if (!edge.fromCell.equals(port.cell)) {
                        continue;
                    }
                    // Uniqueness is over the immutable evidence row, not only
                    // the resolved port. Duplicate direct definitions for the
                    // same retained input are still ambiguous.
                    if (selected != null) {
                        return DirectDemandInputResolution.ambiguous();
                    }
                    selected = port;
                }
            }
            return selected == null
                    ? DirectDemandInputResolution.absent()
                    : new DirectDemandInputResolution(selected, false);
        }

        /**
         * Re-slices the frozen graph after runtime has selected one concrete
         * same-thread root call tree.  This is intentionally a graph-index
         * operation, not a second Soot execution.
         */
        private ConcreteDemandSlice reslice(StaticRegion region,
                boolean runtimePathEvidenceComplete,
                Set<String> observedMethods, String runtimeRootMethod,
                MethodEvent runtimeRoot, Set<Long> containedCalls,
                RuntimeFieldAccessIndex runtimeFieldAccesses) {
            ConcreteDemandSlice result = new ConcreteDemandSlice();
            if (!catalogReadComplete || catalogRowCount == 0
                    || catalogInvalidRowCount > 0 || byId.isEmpty()) {
                return result;
            }
            if (region.outputs.isEmpty() && region.branches.isEmpty()) {
                for (StaticPort input : region.inputs) {
                    result.inputPortIds.add(input.portId);
                }
                return result;
            }
            if (!runtimePathEvidenceComplete || observedMethods == null
                    || observedMethods.isEmpty()) {
                return result;
            }

            Set<String> seeds = new LinkedHashSet<>();
            boolean failureDirected = false;
            for (StaticPort output : region.outputs) {
                if ("FAILURE_PREDICATE".equals(output.kind)) {
                    failureDirected = true;
                } else if (!output.cell.isEmpty()) {
                    seeds.add(output.cell);
                }
            }
            for (BranchPolicy branch : region.branches) {
                String branchMethod = methodInCell(branch.siteId);
                if (!observedMethods.contains(branchMethod)
                        || failureDirected
                        && !region.anchorMethod.equals(branchMethod)) {
                    continue;
                }
                for (StaticDataflowProjectionEdge edge : values(
                        guardsBySite.get(branch.siteId))) {
                    if (!edge.exactGuardDependency(observedMethods)) {
                        continue;
                    }
                    addNonBlank(seeds, edge.fromCell);
                }
            }
            if (seeds.isEmpty()) {
                return result;
            }

            Deque<String> work = new ArrayDeque<>(seeds);
            Set<String> visited = new LinkedHashSet<>();
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (cell.isEmpty() || !visited.add(cell)) {
                    continue;
                }
                if (visited.size() > 20000) {
                    break;
                }

                StaticPort frontier = region.uniqueDemandFrontierPort(cell,
                        observedMethods, runtimeRootMethod);
                if (frontier != null) {
                    result.inputPortIds.add(frontier.portId);
                    continue;
                }

                List<StaticDataflowProjectionEdge> definitions =
                        exactDefinitions(cell, observedMethods);
                if (definitions.isEmpty()) {
                    continue;
                }
                definitions = preferCanonicalDeclaredFieldReads(
                        definitions);
                for (StaticDataflowProjectionEdge definition : definitions) {
                    result.edgeIds.add(definition.edgeId);
                    addNonBlank(result.methods, definition.method);
                    if (definition.exactDeclaredHeapRead()
                            && region.runtimeHeapReachingDefinitionEligible(
                            definition.fromCell)) {
                        RuntimeHeapDefinition heapDefinition =
                                runtimeFieldAccesses.reachingDefinition(
                                        definition, runtimeRoot,
                                        containedCalls, observedMethods,
                                        this);
                        if (heapDefinition.internal()) {
                            StaticDataflowProjectionEdge writeDefinition =
                                    heapDefinition.writeDefinition;
                            result.edgeIds.add(writeDefinition.edgeId);
                            addNonBlank(result.methods,
                                    writeDefinition.method);
                            work.addLast(writeDefinition.fromCell);
                            continue;
                        }
                        if (heapDefinition.concreteBound()) {
                            continue;
                        }
                    }
                    if (!definition.fromCell.isEmpty()) {
                        work.addLast(definition.fromCell);
                    }
                }
            }
            return result;
        }

        private StaticDataflowProjectionEdge uniqueRuntimeHeapWriteDefinition(
                FieldAccessEvent write, String declaredField,
                Set<String> observedMethods) {
            StaticDataflowProjectionEdge selected = null;
            for (StaticDataflowProjectionEdge edge : values(
                    incomingByCell.get(declaredField))) {
                if (!edge.exactHeapWriteAt(write, declaredField,
                        observedMethods)) {
                    continue;
                }
                if (selected != null) {
                    return null;
                }
                selected = edge;
            }
            return selected;
        }

        private List<StaticDataflowProjectionEdge> exactDefinitions(
                String cell, Set<String> observedMethods) {
            List<StaticDataflowProjectionEdge> result = new ArrayList<>();
            for (StaticDataflowProjectionEdge edge : values(
                    incomingByCell.get(cell))) {
                if (edge.exactConcreteDefinition(observedMethods)) {
                    result.add(edge);
                }
            }
            return result;
        }

        /** Parallel declared and receiver-projected getfield rows encode one
         * JVM definition.  Prefer the declared field so the re-slice produces
         * a materializable scalar port instead of a carrier projection. */
        private List<StaticDataflowProjectionEdge>
        preferCanonicalDeclaredFieldReads(
                List<StaticDataflowProjectionEdge> definitions) {
            Map<String, List<StaticDataflowProjectionEdge>> bySite =
                    new LinkedHashMap<>();
            for (StaticDataflowProjectionEdge edge : definitions) {
                String key = edge.method + "\n" + edge.siteId + "\n"
                        + edge.unitIndex + "\n" + edge.toCell;
                RuntimeRegionPlanner.add(bySite, key, edge);
            }
            List<StaticDataflowProjectionEdge> result = new ArrayList<>();
            for (List<StaticDataflowProjectionEdge> sameSite
                    : bySite.values()) {
                List<StaticDataflowProjectionEdge> declared =
                        new ArrayList<>();
                boolean projectedAlias = false;
                for (StaticDataflowProjectionEdge edge : sameSite) {
                    if (exactDeclaredFieldCell(edge.fromCell)
                            && "HEAP_READ".equals(edge.transferKind)) {
                        declared.add(edge);
                    } else if (edge.fromCell.contains("#field:")) {
                        projectedAlias = true;
                    }
                }
                if (projectedAlias && declared.size() == 1) {
                    result.add(declared.get(0));
                } else {
                    result.addAll(sameSite);
                }
            }
            return result;
        }
    }

    /** Result of the post-runtime demand slice over the frozen static graph. */
    private static final class ConcreteDemandSlice {
        private boolean externalInputPromoted;
        private final Set<String> inputPortIds = new LinkedHashSet<>();
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<String> edgeIds = new LinkedHashSet<>();

        private List<StaticPort> inputs(StaticRegion region) {
            List<StaticPort> result = new ArrayList<>();
            for (StaticPort input : region.inputs) {
                if (inputPortIds.contains(input.portId)) {
                    result.add(input);
                }
            }
            return result;
        }

        private List<String> definitionMethods(Set<String> observedMethods) {
            Set<String> result = new LinkedHashSet<>();
            if (observedMethods != null) {
                result.addAll(observedMethods);
            }
            result.addAll(methods);
            return sorted(result);
        }

        private void promoteExternalInput(StaticPort port) {
            if (port == null || port.portId.isEmpty()) {
                return;
            }
            inputPortIds.add(port.portId);
            externalInputPromoted = true;
        }
    }

    private static final class ProjectionOrientation {
        private final String peerObjectCell;
        private final String peerProjectedCell;

        private ProjectionOrientation(String peerObjectCell,
                                      String peerProjectedCell) {
            this.peerObjectCell = safe(peerObjectCell);
            this.peerProjectedCell = safe(peerProjectedCell);
        }
    }

    private static final class StaticDataflowProjectionEdge {
        private final String edgeId;
        private final String kind;
        private final String transferKind;
        private final String relation;
        private final boolean assertable;
        private final String fromCell;
        private final String toCell;
        private final String objectFromCell;
        private final String objectToCell;
        private final String projectionBaseEdgeId;
        private final List<String> fieldPath;
        private final boolean fieldSensitive;
        private final String declaredFieldSignature;
        private final String declaredFieldOwner;
        private final String declaredFieldType;
        private final String declaredFieldName;
        private final String declaredFieldAuthority;
        private final String invoke;
        private final String accessorImplementationMethod;
        private final String accessorImplementationAuthority;
        private final String method;
        private final String siteId;
        private final int unitIndex;

        private StaticDataflowProjectionEdge(String edgeId, String kind,
                String transferKind, String relation, boolean assertable,
                String fromCell, String toCell, String objectFromCell,
                String objectToCell, String projectionBaseEdgeId,
                List<String> fieldPath, boolean fieldSensitive,
                String declaredFieldSignature, String declaredFieldOwner,
                String declaredFieldType, String declaredFieldName,
                String declaredFieldAuthority, String invoke,
                String accessorImplementationMethod,
                String accessorImplementationAuthority,
                String method, String siteId, int unitIndex) {
            this.edgeId = safe(edgeId);
            this.kind = safe(kind);
            this.transferKind = safe(transferKind);
            this.relation = safe(relation);
            this.assertable = assertable;
            this.fromCell = safe(fromCell);
            this.toCell = safe(toCell);
            this.objectFromCell = safe(objectFromCell);
            this.objectToCell = safe(objectToCell);
            this.projectionBaseEdgeId = safe(projectionBaseEdgeId);
            this.fieldPath = new ArrayList<>(fieldPath);
            this.fieldSensitive = fieldSensitive;
            this.declaredFieldSignature = safe(declaredFieldSignature);
            this.declaredFieldOwner = safe(declaredFieldOwner);
            this.declaredFieldType = safe(declaredFieldType);
            this.declaredFieldName = safe(declaredFieldName);
            this.declaredFieldAuthority = safe(declaredFieldAuthority);
            this.invoke = safe(invoke);
            this.accessorImplementationMethod = safe(
                    accessorImplementationMethod);
            this.accessorImplementationAuthority = safe(
                    accessorImplementationAuthority);
            this.method = safe(method);
            this.siteId = safe(siteId);
            this.unitIndex = unitIndex;
        }

        private static StaticDataflowProjectionEdge fromJson(String json) {
            if (jsonTopLevelInt(json, "schemaVersion", -1)
                    != STATIC_DATAFLOW_EDGE_SCHEMA_VERSION) {
                return null;
            }
            String id = jsonString(json, "id");
            if (id.isEmpty()) {
                return null;
            }
            return new StaticDataflowProjectionEdge(id,
                    jsonString(json, "kind"),
                    jsonString(json, "transferKind"),
                    jsonString(json, "relation"),
                    staticDataflowAssertable(json),
                    jsonString(json, "fromCell"),
                    jsonString(json, "toCell"),
                    jsonString(json, "objectFromCell"),
                    jsonString(json, "objectToCell"),
                    jsonString(json, "projectionBaseEdgeId"),
                    exactFieldPath(jsonString(json, "fieldPath")),
                    jsonBoolean(json, "fieldSensitive", false),
                    jsonString(json, "declaredFieldSignature"),
                    jsonString(json, "declaredFieldOwner"),
                    jsonString(json, "declaredFieldType"),
                    jsonString(json, "declaredFieldName"),
                    jsonString(json, "declaredFieldAuthority"),
                    jsonString(json, "invoke"),
                    jsonString(json, "accessorImplementationMethod"),
                    jsonString(json, "accessorImplementationAuthority"),
                    jsonString(json, "method"),
                    jsonString(json, "siteId"),
                    jsonInt(json, "unitIndex", -1));
        }

        private boolean exactConcreteDefinition(
                Set<String> observedMethods) {
            if (method.isEmpty() || !observedMethods.contains(method)
                    || !assertable
                    || !("value_flow".equals(relation)
                    || "taint_depends_on".equals(relation))) {
                return false;
            }
            return !"GUARD".equals(transferKind)
                    && !"SEED".equals(transferKind)
                    && !"EXCEPTION".equals(transferKind);
        }

        /**
         * A raw runtime consumer endpoint may be canonicalized to a retained
         * demand input only through one direct frozen heap-read value-flow
         * row. The broader concrete-definition predicate is intentionally
         * insufficient here: value passes and taint dependencies must not
         * revive a pruned region boundary input.
         */
        private boolean exactDirectDemandInputDefinition(
                Set<String> observedMethods) {
            return exactDeclaredHeapRead()
                    && "value_flow".equals(relation)
                    && exactConcreteDefinition(observedMethods);
        }

        private boolean exactDeclaredHeapRead() {
            return "HEAP_READ".equals(transferKind)
                    && exactDeclaredFieldCell(fromCell)
                    && !method.isEmpty() && !siteId.isEmpty()
                    && unitIndex >= 0;
        }

        private boolean exactHeapWriteAt(FieldAccessEvent write,
                String declaredField, Set<String> observedMethods) {
            return write != null
                    && "HEAP_WRITE".equals(transferKind)
                    && declaredField.equals(toCell)
                    && !fromCell.isEmpty()
                    && exactConcreteDefinition(observedMethods)
                    && method.equals(write.method)
                    && siteId.equals(write.siteId)
                    && unitIndex == write.unitIndex;
        }

        private boolean exactGuardDependency(Set<String> observedMethods) {
            return observedMethods.contains(method)
                    && "GUARD".equals(transferKind)
                    && assertable
                    && "control_depends_on".equals(relation)
                    && !fromCell.isEmpty();
        }

        private boolean exactProjectedFieldEdge() {
            return ("projected_field_read".equals(kind)
                    || "projected_field_write".equals(kind)
                    || "projected_instance_field_read".equals(kind)
                    || "projected_instance_field_write".equals(kind))
                    && !projectionBaseEdgeId.isEmpty()
                    && !fieldPath.isEmpty() && fieldSensitive
                    && exactAutomaticValueFlow();
        }

        private boolean exactResolvedAccessorDeclaration() {
            if (!"accessor_field_return".equals(kind)
                    || !exactAutomaticValueFlow()
                    || !fieldSensitive || fieldPath.isEmpty()
                    || !STATIC_INPUT_FIELD_PROJECTION_DECLARATION_AUTHORITY
                    .equals(declaredFieldAuthority)
                    || !"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY".equals(
                    accessorImplementationAuthority)) {
                return false;
            }
            Matcher field = FIELD_SIGNATURE.matcher(
                    declaredFieldSignature);
            return field.matches()
                    && field.group(1).trim().equals(declaredFieldOwner)
                    && field.group(2).trim().equals(declaredFieldType)
                    && field.group(3).trim().equals(declaredFieldName)
                    && declaredFieldName.equals(fieldPath.get(
                    fieldPath.size() - 1))
                    && declaredFieldType.equals(methodReturnType(invoke))
                    && declaredFieldType.equals(methodReturnType(
                    accessorImplementationMethod));
        }

        private boolean exactAutomaticValueFlow() {
            return assertable && "value_flow".equals(relation);
        }

        private ProjectionOrientation orientation(String baseCell,
                                                   String targetCell) {
            String suffix = fieldPathSuffix(fieldPath);
            if (suffix.isEmpty()
                    || !targetCell.equals(baseCell + suffix)) {
                return null;
            }
            boolean atFrom = baseCell.equals(objectFromCell)
                    && targetCell.equals(fromCell);
            boolean atTo = baseCell.equals(objectToCell)
                    && targetCell.equals(toCell);
            if (atFrom == atTo) {
                return null;
            }
            return atFrom
                    ? new ProjectionOrientation(objectToCell, toCell)
                    : new ProjectionOrientation(objectFromCell, fromCell);
        }

        private boolean exactlyProjects(
                StaticDataflowProjectionEdge base,
                ProjectionOrientation orientation) {
            if (base == null || orientation == null
                    || !kind.substring("projected_".length()).equals(
                    base.kind)
                    || !transferKind.equals(base.transferKind)
                    || !relation.equals(base.relation)
                    || !base.exactAutomaticValueFlow()) {
                return false;
            }
            return fromCell.equals(objectFromCell
                    + fieldPathSuffix(fieldPath))
                    && toCell.equals(objectToCell
                    + fieldPathSuffix(fieldPath))
                    && base.fromCell.equals(objectFromCell)
                    && base.toCell.equals(objectToCell);
        }

        private boolean declares(String objectCell, String projectedCell,
                                 List<String> expectedPath) {
            return exactResolvedAccessorDeclaration()
                    && objectFromCell.equals(objectCell)
                    && fromCell.equals(projectedCell)
                    && fieldPath.equals(expectedPath);
        }

        private static List<String> exactFieldPath(String rawPath) {
            String value = safe(rawPath);
            List<String> result = new ArrayList<>();
            Matcher matcher = FIELD_PROJECTION.matcher(value);
            int cursor = 0;
            while (matcher.find()) {
                if (matcher.start() != cursor) {
                    return Collections.emptyList();
                }
                String field = matcher.group(1).trim();
                if (field.isEmpty()) {
                    return Collections.emptyList();
                }
                result.add(field);
                cursor = matcher.end();
            }
            return cursor == value.length() ? result
                    : Collections.<String>emptyList();
        }

        private static String fieldPathSuffix(List<String> path) {
            StringBuilder result = new StringBuilder();
            for (String field : path) {
                if (safe(field).isEmpty()) {
                    return "";
                }
                result.append("#field:").append(field);
            }
            return result.toString();
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
        private String siteId = "";
        private boolean requiresOrder;
        private boolean requiresObjectIdentity;
        private String mappingKind = "";
        private boolean mappingOnly;
        private String producerCandidateGroup = "";
        private FieldCell fromField = FieldCell.unresolved();
        private FieldCell toField = FieldCell.unresolved();

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
            edge.fromField = fieldCell(edge.fromPort);
            edge.toField = fieldCell(edge.toPort);
            edge.kind = jsonString(json, "kind");
            edge.siteId = jsonString(json, "siteId");
            edge.requiresOrder = jsonBoolean(json, "requiresOrder", false);
            edge.requiresObjectIdentity = jsonBoolean(json,
                    "requiresObjectIdentity", false);
            edge.mappingKind = jsonString(json, "mappingKind");
            edge.mappingOnly = "MAPPING_ONLY".equals(
                    jsonString(json, "semanticMode"));
            return edge;
        }

        private boolean mappingOnlyProtocol() {
            return mappingOnly && !kind.isEmpty()
                    && !"SHARED_STATE".equals(kind);
        }

        private boolean hasExactProducerOutput(StaticRegion region) {
            if (region == null) {
                return false;
            }
            for (StaticPort output : region.outputs) {
                if (!canonicalMetadataPresent) {
                    if (fromPort.equals(output.portId)
                            || fromPort.equals(output.cell)) {
                        return true;
                    }
                    continue;
                }
                if (canonicalAliasValid()
                        && fromOutputPort.equals(output.portId)
                        && fromOutputCell.equals(output.cell)) {
                    return true;
                }
            }
            return false;
        }

        private StaticRegionEdge forProducerRegion(String producerRegion,
                                                   String candidateGroup) {
            StaticRegionEdge copy = new StaticRegionEdge();
            copy.edgeId = edgeId;
            copy.fromRegion = safe(producerRegion);
            copy.toRegion = toRegion;
            copy.fromPort = fromPort;
            copy.fromOutputPort = fromOutputPort;
            copy.fromOutputCell = fromOutputCell;
            copy.aliasProofEdgeIds.addAll(aliasProofEdgeIds);
            copy.aliasProofAuthority = aliasProofAuthority;
            copy.aliasProofComplete = aliasProofComplete;
            copy.canonicalMetadataPresent = canonicalMetadataPresent;
            copy.toPort = toPort;
            copy.kind = kind;
            copy.siteId = siteId;
            copy.requiresOrder = requiresOrder;
            copy.requiresObjectIdentity = requiresObjectIdentity;
            copy.mappingKind = mappingKind;
            copy.mappingOnly = mappingOnly;
            copy.producerCandidateGroup = safe(candidateGroup);
            copy.fromField = fromField;
            copy.toField = toField;
            return copy;
        }

        /**
         * Runtime instance correlation keeps using {@link #fromPort}.
         * Producer-output selection and source value capture may consume a
         * complete exact alias proof; an edge with no canonical schema keeps
         * its exact raw endpoint, while any partially populated canonical
         * schema fails closed.
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

        private String sourceFingerprintEndpoint(StaticRegion region) {
            return usesCanonicalOutput() && producerOutputFor(region) != null
                    ? fromOutputCell : fromPort;
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
        private final boolean anchorObserved;
        private final Set<String> concreteInputPortIds;
        private final Set<String> concreteDemandEdgeIds;
        private final ConcreteDemandSlice concreteDemandSlice;
        private final Map<String, ConsumerInputResolution>
                consumerInputResolutionCache = new LinkedHashMap<>();
        private final Set<String> unresolvedConsumerInputCache =
                new LinkedHashSet<>();
        private final Map<String, ConsumerInputResolution>
                externalCandidateInputResolutionCache =
                new LinkedHashMap<>();
        private final Set<String> unresolvedExternalCandidateInputCache =
                new LinkedHashSet<>();
        private final boolean runtimePathEvidenceComplete;
        private final boolean containedCallTreeComplete;

        private InstanceEvidence(String instanceId, StaticRegion region,
                                 MethodEvent root, Set<Long> calls,
                                 List<MethodEvent> methodEvents,
                                 List<RuntimeEvent> runtimeEvents,
                                 List<FieldAccessEvent> fieldEvents,
                                 Set<String> observedMethods,
                                 Set<String> concreteInputPortIds,
                                 ConcreteDemandSlice concreteDemandSlice,
                                 boolean runtimePathEvidenceComplete,
                                 boolean containedCallTreeComplete) {
            this.instanceId = instanceId;
            this.region = region;
            this.root = root;
            this.calls = new LinkedHashSet<>(calls);
            this.methodEvents = new ArrayList<>(methodEvents);
            this.runtimeEvents = new ArrayList<>(runtimeEvents);
            this.fieldEvents = new ArrayList<>(fieldEvents);
            this.observedMethods = new LinkedHashSet<>(observedMethods);
            this.anchorObserved = this.observedMethods.contains(
                    region.anchorMethod)
                    || invokedAnchor(this.runtimeEvents,
                    region.anchorMethod);
            this.concreteInputPortIds = new LinkedHashSet<>(
                    concreteInputPortIds);
            this.concreteDemandSlice = concreteDemandSlice;
            this.concreteDemandEdgeIds = new LinkedHashSet<>(
                    concreteDemandSlice.edgeIds);
            this.runtimePathEvidenceComplete = runtimePathEvidenceComplete;
            this.containedCallTreeComplete = containedCallTreeComplete;
        }

        private boolean promoteExternalInput(StaticPort port) {
            if (port == null || port.portId.isEmpty()) {
                return false;
            }
            boolean added = concreteInputPortIds.add(port.portId);
            if (!added) {
                return false;
            }
            concreteDemandSlice.promoteExternalInput(port);
            consumerInputResolutionCache.clear();
            unresolvedConsumerInputCache.clear();
            return true;
        }

        /**
         * Resolves a runtime-confirmed external endpoint against the full
         * static candidate input set, but permits a local alias only when the
         * already-selected concrete demand edges prove that exact direct
         * definition. This keeps protocol and shared-state boundary recovery
         * independent of edge iteration order without reopening arbitrary
         * frozen-graph reachability.
         */
        private ConsumerInputResolution resolveExternalCandidateInput(
                String endpoint, StaticProjectionIndex projections) {
            String key = safe(endpoint);
            if (externalCandidateInputResolutionCache.containsKey(key)) {
                return externalCandidateInputResolutionCache.get(key);
            }
            if (unresolvedExternalCandidateInputCache.contains(key)) {
                return null;
            }
            ConsumerInputResolution resolution = region.resolveConsumerInput(
                    key, projections, null, concreteDemandEdgeIds,
                    observedMethods);
            if (resolution == null) {
                unresolvedExternalCandidateInputCache.add(key);
            } else {
                externalCandidateInputResolutionCache.put(key, resolution);
            }
            return resolution;
        }

        private ConsumerInputResolution resolveConsumerInput(
                String endpoint, StaticProjectionIndex projections) {
            String key = safe(endpoint);
            if (consumerInputResolutionCache.containsKey(key)) {
                return consumerInputResolutionCache.get(key);
            }
            if (unresolvedConsumerInputCache.contains(key)) {
                return null;
            }
            ConsumerInputResolution resolution = region.resolveConsumerInput(
                    key, projections, concreteInputPortIds,
                    concreteDemandEdgeIds,
                    observedMethods);
            if (resolution == null) {
                unresolvedConsumerInputCache.add(key);
            } else {
                consumerInputResolutionCache.put(key, resolution);
            }
            return resolution;
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

    /** Reuses exact shared-state correlation across promotion and rendering. */
    private static final class RuntimeRelationEvidenceCache {
        private final Map<String, SharedReadFrom> confirmedReadFrom =
                new LinkedHashMap<>();
        private final Set<String> absentReadFrom = new LinkedHashSet<>();

        private SharedReadFrom sharedReadFrom(StaticRegionEdge edge,
                InstanceEvidence upstream, InstanceEvidence downstream) {
            String key = edge.fromPort + "\n" + edge.toPort + "\n"
                    + upstream.instanceId + "\n" + downstream.instanceId;
            if (confirmedReadFrom.containsKey(key)) {
                return confirmedReadFrom.get(key);
            }
            if (absentReadFrom.contains(key)) {
                return null;
            }
            SharedReadFrom result = RuntimeRegionPlanner.sharedReadFrom(edge,
                    upstream, downstream);
            if (result == null) {
                absentReadFrom.add(key);
            } else {
                confirmedReadFrom.put(key, result);
            }
            return result;
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
                    ? write.seq : writeEvidence.writerEventSeq();
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
        private final RuntimeEvent mutation;
        private final RuntimeEvent completion;

        private WriteEvidence(RuntimeEvent mutation,
                              RuntimeEvent completion) {
            this.mutation = mutation;
            this.completion = completion;
        }

        private long writerEventSeq() {
            return completion == null
                    ? mutation == null ? 0L : mutation.seq : completion.seq;
        }
    }

    private static final class UpstreamEdgeBinding {
        private final StaticRegionEdge edge;
        private final InstanceEvidence upstream;
        private final InstanceEvidence downstream;
        private final SharedReadFrom readFrom;
        private StaticPort output;
        private StaticPort downstreamInput;
        private StaticProjectionProof downstreamInputProjection;

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
                    "schemaVersion", 2,
                    "edgeId", edge.edgeId,
                    "fromRegion", edge.fromRegion,
                    "toRegion", edge.toRegion,
                    "fromRegionInstance", upstream.instanceId,
                    "toRegionInstance", downstream.instanceId,
                    "fromRootCallId", upstream.root.callId,
                    "toRootCallId", downstream.root.callId,
                    "fromOutputPort", output.portId,
                    "fromOutputCell", output.cell,
                    "toInputPort", downstreamInput.portId,
                    "toInputCell", downstreamInput.cell);
            addReadFromEvidence(result, readFrom);
            result.put("inputProjectionUsed",
                    downstreamInputProjection != null);
            if (downstreamInputProjection != null) {
                result.put("inputProjectionComplete", true);
                result.put("inputProjectionPath", new ArrayList<>(
                        downstreamInputProjection.fieldPath));
                result.put("inputProjectionEvidenceEdgeIds",
                        new ArrayList<>(downstreamInputProjection
                                .evidenceEdgeIds));
                result.put("inputProjectionEvidenceAuthority",
                        STATIC_INPUT_FIELD_PROJECTION_AUTHORITY);
                result.put("inputProjectionBaseCell",
                        downstreamInputProjection.baseCell);
                result.put("inputProjectionTargetCell",
                        downstreamInputProjection.targetCell);
                result.put("inputProjectionDeclaredFieldSignature",
                        downstreamInputProjection.declaredFieldSignature);
                result.put("inputProjectionDeclaredFieldType",
                        downstreamInputProjection.declaredFieldType);
                result.put("inputProjectionDeclaredFieldAuthority",
                        STATIC_INPUT_FIELD_PROJECTION_DECLARATION_AUTHORITY);
                result.put("inputProjectionValueObjectIdentityConfirmed",
                        readFrom.write.valueObjectId != 0
                                && readFrom.write.valueObjectId
                                == readFrom.read.valueObjectId);
            }
            result.put("aliasProofEdgeIds",
                    new ArrayList<>(edge.aliasProofEdgeIds));
            result.put("aliasProofAuthority", edge.aliasProofAuthority);
            result.put("aliasProofComplete", edge.aliasProofComplete);
            return result;
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
        private boolean requestedStateTransformerContractPresent;
        private final List<Map<String, Object>>
                requestedStateTransformerObligations = new ArrayList<>();
        private final List<String> requestedStateTransformerContractIssues =
                new ArrayList<>();
        private boolean requestedStateTransformerContractComplete;
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
        private boolean runtimeRefinementComplete = true;
        private final Set<String> staticSites = new LinkedHashSet<>();

        private static final class FieldPathRuntimeCandidate {
            private final StaticPort port;
            private final String portId;
            private final List<String> path;
            private final String leafFieldSignature;
            private final String accessMethod;
            private final FieldAccessEvent event;

            private FieldPathRuntimeCandidate(
                    StaticPort port, Collection<String> path,
                    String leafFieldSignature, String accessMethod,
                    FieldAccessEvent event) {
                this.port = port;
                this.portId = port.portId;
                this.path = new ArrayList<>(path);
                this.leafFieldSignature = safe(leafFieldSignature);
                this.accessMethod = safe(accessMethod);
                this.event = event;
            }
        }

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
            slice.requestedStateTransformerContractPresent = jsonHasField(
                    json, "requestedStateTransformerContractComplete");
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
            slice.requestedStateTransformerContractIssues.addAll(
                    jsonStringArray(json,
                            "requestedStateTransformerContractIssues"));
            slice.requestedStateTransformerContractComplete = jsonBoolean(
                    json, "requestedStateTransformerContractComplete",
                    false);
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
            slice.structuralComplete = jsonBoolean(json,
                    "structuralComplete", false);
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
                    "materializationMode", jsonString(json,
                    "materializationMode"),
                    "method", jsonString(json, "method"),
                    "fieldMaterializationSiteId", jsonString(json,
                    "fieldMaterializationSiteId"),
                    "arrayLoadSiteId", jsonString(json,
                    "arrayLoadSiteId"),
                    "requestedStateTransformerSiteId", jsonString(json,
                    "requestedStateTransformerSiteId"),
                    "proofCausalEdgeIds", jsonStringArray(json,
                    "proofCausalEdgeIds"),
                    "proofAuthority", jsonString(json,
                    "proofAuthority"),
                    "complete", jsonBoolean(json, "complete", false));
        }

        private Map<String, Object> copyContainerElementFieldBinding(
                Map<String, Object> declaration) {
            Map<String, Object> copy = new LinkedHashMap<>(declaration);
            copy.put("fieldPath", new ArrayList<>(stringList(
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
            List<String> path = stringList(declaration.get("fieldPath"));
            List<String> proofRows = stringList(declaration.get(
                    "proofCausalEdgeIds"));
            Set<String> proof = new LinkedHashSet<>(proofRows);
            int schemaVersion = intValue(declaration.get(
                    "schemaVersion"), -1);
            String materializationMode = string(declaration.get(
                    "materializationMode"));
            boolean direct = schemaVersion == 1
                    && (materializationMode.isEmpty()
                    || "FIELD_ACCESS_HOOK".equals(materializationMode))
                    && path.equals(Collections.singletonList(field.name))
                    && !proof.isEmpty()
                    && proofRows.size() == proof.size()
                    && "STATIC_EXACT_CONTAINER_ARRAY_FIELD_TO_MAP_PUT_"
                    .concat("KEY_VALUE_V1").equals(string(declaration.get(
                    "proofAuthority")))
                    && exactContainerTransformerSite(declaration, method,
                    proof);
            boolean snapshot = schemaVersion == 2
                    && "CONTAINER_SNAPSHOT".equals(materializationMode)
                    && !path.isEmpty() && path.size() <= 4
                    && field.name.equals(path.get(path.size() - 1))
                    && proof.size() == 5
                    && "STATIC_EXACT_ARRAY_ELEMENT_MAP_PUT_VALUE_AND_"
                    .concat("DECLARED_FIELD_FIVE_EDGE_JOIN_V1").equals(
                    string(declaration.get("proofAuthority")));
            boolean directPathSnapshot = schemaVersion == 2
                    && "CONTAINER_SNAPSHOT".equals(materializationMode)
                    && path.size() >= 2 && path.size() <= 4
                    && field.name.equals(path.get(path.size() - 1))
                    && primitiveType(field.type)
                    && proofRows.size() == proof.size()
                    && proof.size() == 4 * path.size()
                    && "STATIC_EXACT_DIRECT_ARRAY_ELEMENT_FIELD_PATH_"
                    .concat("CHAIN_V1").equals(string(declaration.get(
                    "proofAuthority")));
            return (direct || snapshot || directPathSnapshot)
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
                    && method.equals(string(declaration.get("method")))
                    && exactUnitSite(method, string(declaration.get(
                    "fieldMaterializationSiteId")))
                    && sites.contains(string(declaration.get(
                    "fieldMaterializationSiteId")))
                    && exactUnitSite(method, string(declaration.get(
                    "arrayLoadSiteId")))
                    && sites.contains(string(declaration.get(
                    "arrayLoadSiteId")))
                    && !proof.contains("")
                    && new LinkedHashSet<>(causalEdgeIds).containsAll(proof);
        }

        private boolean exactContainerTransformerSite(
                Map<String, Object> declaration, String method,
                Set<String> proofEdgeIds) {
            String site = string(declaration.get(
                    "requestedStateTransformerSiteId"));
            if (!exactUnitSite(method, site) || !sites.contains(site)) {
                return false;
            }
            int matches = 0;
            for (Map<String, Object> obligation
                    : requestedStateTransformerObligations) {
                if (!site.equals(string(obligation.get("siteId")))
                        || !method.equals(string(obligation.get("method")))
                        || !outputCell.equals(string(obligation.get(
                        "targetCell")))
                        || !"HEAP_WRITE".equals(string(obligation.get(
                        "transferKind")))
                        || !"field_mutation".equals(string(obligation.get(
                        "kind")))
                        || !"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL"
                        .equals(string(obligation.get("authority")))) {
                    continue;
                }
                Set<String> obligationEdges = stringSet(obligation.get(
                        "causalEdgeIds"));
                if (obligationEdges.isEmpty()
                        || !proofEdgeIds.containsAll(obligationEdges)) {
                    return false;
                }
                matches++;
            }
            return matches == 1;
        }

        private int intValue(Object value, int fallback) {
            return value instanceof Number
                    ? ((Number) value).intValue() : fallback;
        }

        private boolean exactUnitSite(String method, String site) {
            String candidate = safe(site);
            if (method.isEmpty() || !candidate.startsWith(method)) {
                return false;
            }
            Matcher suffix = UNIT_SITE_SUFFIX.matcher(candidate);
            suffix.region(method.length(), candidate.length());
            return suffix.matches();
        }

        private static Map<String, Object> causalEdgeReference(String json) {
            Map<String, Object> result = object(
                    "edgeId", firstNonBlank(jsonString(json, "edgeId"),
                            jsonString(json, "id")),
                    "method", jsonString(json, "method"),
                    "siteId", jsonString(json, "siteId"),
                    "fromCell", jsonString(json, "fromCell"),
                    "toCell", jsonString(json, "toCell"),
                    "transferKind", jsonString(json, "transferKind"),
                    "kind", jsonString(json, "kind"),
                    "invoke", jsonString(json, "invoke"));
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
            Boolean required = jsonOptionalBoolean(json,
                    "requiredOutcome");
            if (required != null) result.put("requiredOutcome", required);
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
            refined.structuralComplete = structuralComplete;
            refined.regionTruncated = regionTruncated;
            refined.sliceTruncated = sliceTruncated;
            refined.methodBudgetTruncated = methodBudgetTruncated;
            refined.causalCellBudgetTruncated = causalCellBudgetTruncated;
            refined.structuralIssues.addAll(structuralIssues);
            refined.staticSites.addAll(sites);
            refined.captureBindingsRequired = captureBindingsRequired;
            refined.captureBindingsComplete = captureBindingsComplete;
            refined.captureBindingIssues.addAll(captureBindingIssues);
            refined.requestedStateTransformerContractPresent =
                    requestedStateTransformerContractPresent;
            refined.requestedStateTransformerContractIssues.addAll(
                    requestedStateTransformerContractIssues);
            refined.requestedStateTransformerContractComplete =
                    requestedStateTransformerContractComplete;

            // The semantic backward slice is the region boundary authority.
            // Runtime evidence selects one path through that declared slice;
            // it must neither grow the slice with incidental callees nor
            // reject an otherwise complete region because such callees ran.
            Set<String> observed = new LinkedHashSet<>(
                    evidence.observedMethods);
            observed.retainAll(methods);
            refineUnresolvedInputs(observed, refined);
            refined.methods.addAll(sorted(observed));
            boolean filtersAlternatives = observed.size() != methods.size();

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
                String port = string(binding.get("inputPort"));
                if (retain) {
                    Map<String, Object> retained = new LinkedHashMap<>(
                            binding);
                    if (requestedStateTransformerContractPresent
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
                        continue;
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
            collapseRuntimeConfirmedFieldPathAliases(evidence,
                    retainedBindings, refined);
            retainedPorts.clear();
            for (Map<String, Object> binding : retainedBindings) {
                String port = string(binding.get("inputPort"));
                if (!port.isEmpty()) {
                    retainedPorts.add(port);
                }
            }
            refined.inputBindings.addAll(retainedBindings);
            refined.inputPorts.addAll(sorted(retainedPorts));

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
                            && !requestedStateTransformerObligations.isEmpty();
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
                    !requestedStateTransformerContractPresent
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
         * The static graph carries every canonical suffix of an exact field
         * chain.  Runtime receiver/value identity decides whether two such
         * ports are the same concrete chain: a longer read must produce the
         * exact receiver consumed by its immediately shorter suffix.  This
         * keeps independent same-name fields while removing duplicate hooks
         * before concolic scheduling.
         */
        private void collapseRuntimeConfirmedFieldPathAliases(
                InstanceEvidence evidence,
                List<Map<String, Object>> retainedBindings,
                StaticOutputSlice refined) {
            Map<String, FieldPathRuntimeCandidate> candidates =
                    new LinkedHashMap<>();
            for (Map<String, Object> binding : retainedBindings) {
                String portId = string(binding.get("inputPort"));
                StaticPort port = evidence.region.exactInputFor(portId);
                FieldPathRuntimeCandidate candidate =
                        runtimeFieldPathCandidate(evidence, port);
                if (candidate != null) {
                    candidates.put(portId, candidate);
                }
            }
            Map<String, List<FieldPathRuntimeCandidate>> claims =
                    new LinkedHashMap<>();
            for (FieldPathRuntimeCandidate longer : candidates.values()) {
                for (FieldPathRuntimeCandidate suffix : candidates.values()) {
                    if (longer == suffix
                            || longer.path.size() != suffix.path.size() + 1
                            || !longer.path.subList(1, longer.path.size())
                            .equals(suffix.path)
                            || !longer.leafFieldSignature.equals(
                            suffix.leafFieldSignature)
                            || !longer.accessMethod.equals(
                            suffix.accessMethod)
                            || longer.event.callId != suffix.event.callId
                            || longer.event.seq >= suffix.event.seq
                            || longer.event.valueObjectId == 0
                            || longer.event.valueObjectId
                            != suffix.event.receiverObjectId) {
                        continue;
                    }
                    claims.computeIfAbsent(suffix.portId,
                            ignored -> new ArrayList<>()).add(longer);
                }
            }
            Set<String> remove = new LinkedHashSet<>();
            for (Map.Entry<String, List<FieldPathRuntimeCandidate>> entry
                    : claims.entrySet()) {
                if (entry.getValue().size() != 1) {
                    continue;
                }
                FieldPathRuntimeCandidate suffix = candidates.get(
                        entry.getKey());
                FieldPathRuntimeCandidate replacement = entry.getValue()
                        .get(0);
                remove.add(suffix.portId);
                refined.inputAliasCanonicalizations.add(object(
                        "fromInputPort", suffix.portId,
                        "toInputPort", replacement.portId,
                        "fromCell", suffix.port.cell,
                        "toCell", replacement.port.cell,
                        "producerValueObjectId",
                        replacement.event.valueObjectId,
                        "suffixReceiverObjectId",
                        suffix.event.receiverObjectId,
                        "authority",
                        "RUNTIME_EXACT_ADJACENT_FIELD_PATH_RECEIVER_"
                                + "VALUE_IDENTITY_V1"));
            }
            if (remove.isEmpty()) {
                return;
            }
            retainedBindings.removeIf(binding -> remove.contains(string(
                    binding.get("inputPort"))));
        }

        private FieldPathRuntimeCandidate runtimeFieldPathCandidate(
                InstanceEvidence evidence, StaticPort port) {
            if (port == null || !"STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1"
                    .equals(string(port.materializationMetadata.get(
                            "fieldPathAuthority")))) {
                return null;
            }
            List<String> path = stringList(port.materializationMetadata.get(
                    "fieldPath"));
            String leaf = string(port.materializationMetadata.get(
                    "leafFieldSignature"));
            String method = string(port.materializationMetadata.get(
                    "accessMethod"));
            if (path.size() < 2 || leaf.isEmpty() || method.isEmpty()) {
                return null;
            }
            FieldAccessEvent selected = null;
            for (FieldAccessEvent event : evidence.fieldEvents) {
                if (!authoritativeStaticFieldReadSite(port, event)) {
                    continue;
                }
                if (selected != null) {
                    return null;
                }
                selected = event;
            }
            return selected == null ? null : new FieldPathRuntimeCandidate(
                    port, path, leaf, method, selected);
        }

        /**
         * Revalidates the exact transformer ledger after static alternatives
         * have been removed.  This validation intentionally does not read or
         * write {@link #runtimeRefinementComplete}; the final readiness gate
         * requires the two independent facts together.
         */
        private boolean runtimeRefinedTransformerContractComplete(
                boolean staticContractLedgerComplete) {
            if (!requestedStateTransformerContractPresent) {
                return false;
            }
            if (!staticContractLedgerComplete
                    || !requestedStateTransformerContractIssues.isEmpty()
                    || requestedStateTransformerObligations.isEmpty()) {
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
                                : "NO_RUNTIME_EXACT_CALL_ARGUMENT_MATCH";
                    } else {
                        failure = (fieldAssignmentRequested
                                ? "AMBIGUOUS_RUNTIME_FIELD_ASSIGNMENT_MATCH:"
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
            if (!requestedStateTransformerContractPresent
                    || !requestedStateTransformerContractComplete
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
                    "methods", new ArrayList<>(methods),
                    "sites", new ArrayList<>(sites),
                    "causalEdgeIds", causalEdgeIds,
                    "causalEdges", causalEdges,
                    "heapInitializers", heapInitializers,
                    "captureBindings", captureBindings,
                    "captureBindingsRequired", captureBindingsRequired,
                    "captureBindingsComplete", captureBindingsComplete,
                    "captureBindingIssues", captureBindingIssues,
                    "captureDischargedByHeapEffectTransformer",
                    captureDischargedByHeapEffectTransformer,
                    "captureDischargeInputPort",
                    captureDischargeInputPort,
                    "captureDischargeAuthority",
                    captureDischargeAuthority,
                    "containerElementFieldBindings",
                    containerElementFieldBindings,
                    "unresolvedInputs", unresolvedInputs,
                    "unresolvedInputDetails", unresolvedInputDetails,
                    "truncationReasons", structuralIssues,
                    "complete", complete,
                    "selection", selection);
            if (requestedStateTransformerContractPresent) {
                result.put("requestedStateTransformerObligations",
                        requestedStateTransformerObligations);
                result.put("requestedStateTransformerContractIssues",
                        requestedStateTransformerContractIssues);
                result.put("requestedStateTransformerContractComplete",
                        requestedStateTransformerContractComplete);
            }
            result.put("staticSites", new ArrayList<>(staticSites));
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
                    "accessorImplementationAuthority",
                    "fieldPathAuthority"}) {
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
        private final List<Integer> requiredSuccessorIndices;
        private final String branchKind;
        private final List<Integer> switchCaseKeys;
        private final int defaultSuccessorIndex;

        private BranchPolicy(String siteId, String policy, String guard,
                             Boolean requiredOutcome,
                             List<Integer> requiredSuccessorIndices,
                             String branchKind,
                             List<Integer> switchCaseKeys,
                             int defaultSuccessorIndex) {
            this.siteId = safe(siteId);
            this.policy = safe(policy);
            this.guard = safe(guard);
            this.requiredOutcome = requiredOutcome;
            this.requiredSuccessorIndices = Collections.unmodifiableList(
                    new ArrayList<>(requiredSuccessorIndices));
            this.branchKind = safe(branchKind);
            this.switchCaseKeys = Collections.unmodifiableList(
                    new ArrayList<>(switchCaseKeys));
            this.defaultSuccessorIndex = defaultSuccessorIndex;
        }

        private boolean isSwitch() {
            return "TABLE_SWITCH".equals(branchKind)
                    || "LOOKUP_SWITCH".equals(branchKind);
        }
    }

    private static final class RootCandidate {
        private final MethodEvent event;

        private RootCandidate(MethodEvent event) {
            this.event = event;
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
        Matcher parameter = PARAMETER_TYPE.matcher(safe(cell));
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

        Matcher parameter = PARAMETER_FIELD_PROJECTION.matcher(cell);
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

    /** True only for a canonical declared field cell, not a carrier with a
     * trailing {@code #field:...} projection. */
    private static boolean exactDeclaredFieldCell(String value) {
        return FIELD_SIGNATURE.matcher(safe(value)).matches();
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

    /**
     * Returns the replay-stable portion of a root thread context. Ordinary
     * worker names remain exact. The JDK default executor pool generation is
     * process-global and therefore changes when unrelated pools are created;
     * normalize that number while retaining the worker index. Object-identity
     * suffixes are normalized while retaining the logical thread type.
     */
    private static String stableRootThreadContext(String threadName) {
        String value = safe(threadName);
        Matcher executor = DEFAULT_EXECUTOR_THREAD_NAME.matcher(value);
        if (executor.matches()) {
            return "pool-*-thread-" + executor.group(1);
        }
        Matcher objectIdentity = DEFAULT_OBJECT_IDENTITY_THREAD_NAME.matcher(
                value);
        return objectIdentity.matches()
                ? objectIdentity.group(1) + "@*" : value;
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

    private static Set<String> portIds(List<StaticPort> ports) {
        Set<String> result = new LinkedHashSet<>();
        for (StaticPort port : values(ports)) {
            addNonBlank(result, port.portId);
        }
        return result;
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

    private static List<String> sorted(Collection<String> values) {
        List<String> result = new ArrayList<>();
        if (values != null) {
            result.addAll(values);
        }
        Collections.sort(result);
        return result;
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
        return UNSAFE_TOKEN_CHARACTERS.matcher(safe(value)).replaceAll("_");
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
        if (value instanceof JsonElement) {
            return value.toString();
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

    private static boolean staticDataflowAssertable(String json) {
        return jsonTopLevelInt(json, "schemaVersion", -1)
                == STATIC_DATAFLOW_EDGE_SCHEMA_VERSION
                && STATIC_DATAFLOW_ASSERTABLE.equals(
                jsonString(json, "semanticMode"));
    }

    private static int jsonTopLevelInt(String json, String field,
                                       int fallback) {
        try {
            JsonElement parsed = JsonParser.parseString(json);
            if (!parsed.isJsonObject()) {
                return fallback;
            }
            JsonObject object = parsed.getAsJsonObject();
            JsonElement value = object.get(field);
            return value == null || !value.isJsonPrimitive()
                    || !value.getAsJsonPrimitive().isNumber()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
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
        Matcher matcher = JSON_QUOTED_STRING.matcher(raw);
        while (matcher.find()) {
            result.add(unescape(matcher.group(1)));
        }
        return result;
    }

    private static List<Integer> jsonIntArray(String json, String field) {
        String raw = jsonArray(json, field);
        if (raw.isEmpty()) {
            return Collections.emptyList();
        }
        List<Integer> result = new ArrayList<>();
        Matcher matcher = Pattern.compile("-?(?:0|[1-9][0-9]*)")
                .matcher(raw);
        while (matcher.find()) {
            result.add(parseInt(matcher.group(), 0));
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
