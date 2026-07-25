package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.SymbolicEnvironment;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
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
import java.util.function.ToLongFunction;
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
    private static final Gson GSON = new Gson();
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
    private static final Pattern FIELD_PROJECTION = Pattern.compile(
            "#field:([^#@]+)");
    private static final Pattern GETTER_IN_GUARD = Pattern.compile(
            "\\b((?:get|is)[A-Z][A-Za-z0-9_]*)\\s*\\(");
    private static final Pattern UNIT_SITE_SUFFIX = Pattern.compile(
            "#u[0-9]+");
    private static final Pattern UNSAFE_TOKEN_CHARACTERS = Pattern.compile(
            "[^A-Za-z0-9_.-]+");
    private static final Pattern DEFAULT_EXECUTOR_THREAD_NAME =
            Pattern.compile("^pool-[0-9]+-thread-([0-9]+)$");
    private static final Pattern DEFAULT_OBJECT_IDENTITY_THREAD_NAME =
            Pattern.compile("^([A-Za-z_$][A-Za-z0-9_$.]*?)@"
                    + "[0-9a-fA-F]+$");
    private static final String VM_INTRINSIC_DEFERRED_AUTHORITY =
            "EXACT_VM_INTRINSIC_PLACEHOLDER_SCHEDULER_VALIDATION_V1";
    private static final String CALL_RETURN_DEFERRED_AUTHORITY =
            "AUTHORITATIVE_SCHEDULER_DEFINITION_INDEX_REQUIRED_V1";
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
        Map<String, List<StaticRegion>> regionsByAnchor =
                new LinkedHashMap<>();
        for (StaticRegion region : regions) {
            add(regionsByAnchor, region.anchorMethod, region);
        }
        StaticProjectionIndex staticProjections =
                readStaticProjectionIndex(staticGraphFile);
        resolveStaticCausalEdgeReferences(regions, staticProjections);
        List<MethodEvent> methodEvents = sorted(methods,
                value -> value.seq);
        List<RuntimeEvent> executions = sorted(runtimeEvents,
                value -> value.seq);
        List<FieldAccessEvent> fields = sorted(fieldEvents,
                value -> value.seq);
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
        Map<String, List<InstanceEvidence>> evidenceByRegion = new LinkedHashMap<>();
        Map<String, List<InstanceEvidence>> sharedStateEvidenceByRegion =
                new LinkedHashMap<>();
        List<InstanceEvidence> allInstanceEvidence = new ArrayList<>();

        outer:
        for (StaticRegion region : regions) {
            List<MethodEvent> roots = rootCandidates(region,
                    values(regionsByAnchor.get(region.anchorMethod)),
                    methodsBySignature, calls);
            if (roots.isEmpty()) {
                continue;
            }
            for (MethodEvent root : roots) {
                if (instanceIndex >= MAX_INSTANCES) {
                    break outer;
                }
                ContainedCallSelection callSelection =
                        trace.containedCalls(root);
                Set<Long> containedCalls = callSelection.calls;
                Set<String> observedMethods = new LinkedHashSet<>();
                List<MethodEvent> containedMethodEvents =
                        trace.methods(containedCalls);
                for (MethodEvent event : containedMethodEvents) {
                    observedMethods.add(event.method);
                }

                String instanceId = region.regionId + "@" + safeToken(root.test)
                        + "#call" + root.callId;

                List<RuntimeEvent> containedRuntime =
                        trace.runtimeEvents(containedCalls);
                List<FieldAccessEvent> containedFields =
                        trace.fieldEvents(containedCalls);
                boolean pathSignatureTruncated = pathSignatureTruncated(
                        containedRuntime);
                boolean runtimePathEvidenceComplete = !callSelection.truncated
                        && !pathSignatureTruncated;
                ConcreteDemandSlice demandSlice = staticProjections.reslice(
                        region, runtimePathEvidenceComplete,
                        observedMethods, root.method, root, containedCalls,
                        runtimeFieldAccesses);

                InstanceEvidence instanceEvidence = new InstanceEvidence(
                        instanceId, region, root, containedCalls,
                        containedMethodEvents, containedRuntime,
                        containedFields, observedMethods,
                        portIds(demandSlice.inputs(region)), demandSlice,
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
                instanceIndex++;
            }
        }

        RuntimeRelationEvidenceCache relationEvidence =
                new RuntimeRelationEvidenceCache(trace);
        collectConfirmedExternalInputPromotions(regionEdges,
                evidenceByRegion, sharedStateEvidenceByRegion,
                staticProjections, relationEvidence);
        Map<String, RegionPlanDraft> planDrafts = buildRegionPlans(
                allInstanceEvidence, trace, rootArgumentRuntimeTypes);

        List<UpstreamEdgeBinding> edgeBindings = new ArrayList<>();
        validateRegionEdges(regionEdges, evidenceByRegion,
                sharedStateEvidenceByRegion, staticProjections, result,
                edgeBindings, relationEvidence);
        List<OutputGoalDraft> outputGoals = attachOutputRelationGoals(
                edgeBindings, staticProjections, planDrafts);
        refineMapValueElementProjectionGoals(outputGoals);
        for (RegionPlanDraft plan : planDrafts.values()) {
            if (!plan.goals.isEmpty()) {
                result.regionPlans.add(plan.toMap());
            }
        }
        return result;
    }

    private static List<MethodEvent> rootCandidates(
            StaticRegion region,
            List<StaticRegion> anchorPeers,
            Map<String, List<MethodEvent>> methodsBySignature,
            Map<Long, MethodEvent> calls) {
        List<MethodEvent> roots = new ArrayList<>();
        Set<Long> selectedCalls = new LinkedHashSet<>();
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
                roots.add(selected);
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
                roots.add(event);
            }
        }
        return roots;
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

    private static boolean pathSignatureTruncated(
            List<RuntimeEvent> events) {
        int total = 0;
        for (RuntimeEvent event : events) {
            if ("BRANCH".equals(event.kind) && event.hasOutcome) {
                if (++total > MAX_PATH_SIGNATURE_EVENTS) {
                    return true;
                }
            }
        }
        return false;
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
            List<StaticPort> concreteInputs,
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
            if ("HEAP_PRESTATE".equals(port.sourceKind)) {
                FramePrestatePath frame = framePrestatePath(
                        root, port.cell, fields);
                if (frame.complete()) {
                    observation.put("observed", true);
                    observation.put("location", "RECEIVER_FIELD");
                    observation.put("field", frame.field.signature());
                    observation.put("fieldPath",
                            new ArrayList<>(frame.path));
                    observation.put("leafFieldSignature",
                            frame.field.signature());
                    observation.put("frameConditionAuthority",
                            "RUNTIME_UNIQUE_ROOT_TO_OUTPUT_OWNER_FIELD_PATH");
                    observation.put("receiverObjectId", root.objectId);
                } else {
                    observation.put("location", "REGION_LIVE_IN");
                    observation.put("fieldBindingGap",
                            "MISSING_UNIQUE_FRAME_PRESTATE_FIELD_PATH");
                }
                result.add(observation);
                continue;
            }
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
            if (!Boolean.TRUE.equals(observation.get("observed"))
                    && parameter >= 0 && !rootArgument) {
                observation.put("location", "REGION_LIVE_IN");
                observation.put("deferredResolution", true);
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

    /**
     * Resolves the requested field's concrete owner back to the selected
     * region receiver.  Discovery already records reference-valued getfield
     * edges and the exact putfield receiver; one unique bounded path is
     * sufficient to materialize the entry value before any region code runs.
     */
    private static FramePrestatePath framePrestatePath(
            MethodEvent root, String outputCell,
            List<FieldAccessEvent> fields) {
        FieldCell requested = fieldCell(outputCell);
        if (root == null || root.objectId == 0
                || !requested.declaredSignature
                || isArrayJavaType(requested.type)) {
            return FramePrestatePath.incomplete();
        }

        Set<Integer> owners = new LinkedHashSet<>();
        long firstWrite = Long.MAX_VALUE;
        for (FieldAccessEvent event : values(fields)) {
            if ("FIELD_WRITE".equals(event.kind)
                    && event.receiverObjectId != 0
                    && sameField(requested, fieldCell(event.field))) {
                owners.add(event.receiverObjectId);
                firstWrite = Math.min(firstWrite, event.seq);
            }
        }
        if (owners.size() != 1) {
            return FramePrestatePath.incomplete();
        }
        int targetOwner = owners.iterator().next();
        List<String> ownerPath = targetOwner == root.objectId
                ? Collections.<String>emptyList()
                : uniqueObjectFieldPath(root.objectId, targetOwner,
                firstWrite, fields);
        if (ownerPath == null) {
            return FramePrestatePath.incomplete();
        }
        List<String> path = new ArrayList<>(ownerPath);
        path.add(requested.name);
        return new FramePrestatePath(requested, path);
    }

    private static List<String> uniqueObjectFieldPath(
            int rootObjectId, int targetObjectId, long beforeSeq,
            List<FieldAccessEvent> fields) {
        List<ObjectPathState> queue = new ArrayList<>();
        queue.add(new ObjectPathState(rootObjectId,
                Collections.<String>emptyList(),
                Collections.singleton(rootObjectId)));
        Set<String> matches = new LinkedHashSet<>();
        List<String> selected = null;
        for (int cursor = 0; cursor < queue.size(); cursor++) {
            ObjectPathState state = queue.get(cursor);
            if (state.path.size() >= 4) {
                continue;
            }
            for (FieldAccessEvent event : values(fields)) {
                FieldCell field = fieldCell(event.field);
                if (!"FIELD_READ".equals(event.kind)
                        || event.seq >= beforeSeq
                        || event.receiverObjectId != state.objectId
                        || event.valueObjectId == 0
                        || !field.declaredSignature
                        || state.visited.contains(event.valueObjectId)) {
                    continue;
                }
                List<String> path = new ArrayList<>(state.path);
                path.add(field.name);
                Set<Integer> visited = new LinkedHashSet<>(state.visited);
                visited.add(event.valueObjectId);
                if (event.valueObjectId == targetObjectId) {
                    String key = joinPath(path);
                    if (matches.add(key)) {
                        selected = path;
                    }
                } else {
                    queue.add(new ObjectPathState(event.valueObjectId,
                            path, visited));
                }
            }
        }
        return matches.size() == 1 ? selected : null;
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
        String method = port.materialization.method();
        String site = port.materialization.siteId();
        int unit = port.materialization.unitIndex();
        return port.materialization.kind()
                == MaterializationSpec.Kind.FIELD_READ
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
            String accessMethod = port.materialization.method();
            String accessSiteId = port.materialization.siteId();
            int accessUnitIndex = port.materialization.unitIndex();
            boolean directSiteConstrained = port.materialization.kind()
                    == MaterializationSpec.Kind.FIELD_READ;
            if (directSiteConstrained
                    && (!accessMethod.equals(field.method)
                    || accessUnitIndex != field.unitIndex
                    || !accessSiteId.equals(field.siteId)
                    || !accessSiteId.equals(field.method + "#u"
                    + field.unitIndex))) {
                continue;
            }
            String accessorCallerMethod = port.materialization.method();
            String accessorCallSiteId = port.materialization.siteId();
            String accessorDeclaredCallee =
                    port.materialization.declaredCallee();
            String accessorImplementationMethod =
                    port.materialization.implementationMethod();
            int accessorCallUnitIndex =
                    port.materialization.unitIndex();
            boolean accessorConstrained = port.materialization.kind()
                    == MaterializationSpec.Kind.ACCESSOR_RETURN;
            if (accessorConstrained) {
                MethodEvent fieldMethod = methodsByCall.get(field.callId);
                RuntimeEvent parentSite = fieldMethod == null ? null
                        : callSitesByInvocation.get(
                        fieldMethod.parentSiteId);
                if (parentSite == null
                        || !accessorCallerMethod.equals(parentSite.method)
                        || !accessorCallSiteId.equals(parentSite.siteId)
                        || !accessorCallSiteId.equals(accessorCallerMethod
                        + "#u" + accessorCallUnitIndex)
                        || !accessorDeclaredCallee.equals(
                        parentSite.declaredCallee)
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

    private static boolean primitiveType(String type) {
        String declared = safe(type);
        return "boolean".equals(declared) || "char".equals(declared)
                || "byte".equals(declared) || "short".equals(declared)
                || "int".equals(declared) || "long".equals(declared)
                || "float".equals(declared) || "double".equals(declared);
    }

    private static boolean exactPrimitiveValue(String type, String value) {
        String concrete = safe(value);
        try {
            if ("boolean".equals(type)) {
                return "true".equals(concrete) || "false".equals(concrete);
            }
            if ("char".equals(type)) {
                return concrete.length() == 1;
            }
            if ("byte".equals(type)) {
                Byte.parseByte(concrete);
            } else if ("short".equals(type)) {
                Short.parseShort(concrete);
            } else if ("int".equals(type)) {
                Integer.parseInt(concrete);
            } else if ("long".equals(type)) {
                Long.parseLong(concrete);
            } else if ("float".equals(type)) {
                Float.parseFloat(concrete);
            } else if ("double".equals(type)) {
                Double.parseDouble(concrete);
            } else {
                return false;
            }
            return true;
        } catch (NumberFormatException ignored) {
            return false;
        }
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
            String declaredJavaType = firstNonBlank(port.javaType,
                    declaredJavaType(port.cell));
            if (!declaredJavaType.isEmpty()) {
                action.put("javaType", declaredJavaType);
            }
            // Preserve exact leaf/path declarations carried by the static
            // port.  They are required for local/call-return array leaves,
            // whose root definition is resolved only by the scheduler.
            action.putAll(port.materialization.actionFields());
            copy(observation, action, "index", "field", "objectId",
                    "fieldReceiverObjectId", "valueObjectId", "runtimeType",
                    "primitiveValue", "deferredResolution",
                    "valueFingerprint", "valueFingerprintComplete",
                    "deferredResolutionAuthority",
                    "fieldBindingGap", "accessKind", "bindingMode",
                    "fieldEventSeq", "fieldCallId",
                    "fieldEventIdentityAuthority",
                    "accessMethod", "accessUnitIndex", "accessSiteId",
                    "accessSiteAuthority",
                    "accessorInvocationId", "accessorRuntimeType",
                    "fieldPath", "leafFieldSignature",
                    "frameConditionAuthority", "receiverObjectId");
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
        MaterializationSpec spec = port.materialization;
        if (!spec.directFieldPath()) {
            return;
        }
        List<String> path = spec.path();
        FieldCell staticRoot = fieldCell(port.cell);
        FieldCell leaf = fieldCell(spec.leafField());
        if (path.size() < 2 || path.size() > 4
                || !path.equals(dependencyFieldPath(port.cell))
                || !staticRoot.declaredSignature
                || !observedRoot.signature().equals(
                staticRoot.signature())
                || !leaf.declaredSignature
                || !leaf.name.equals(path.get(path.size() - 1))
                || !primitiveType(leaf.type)
                || !staticRoot.signature().equals(spec.rootField())) {
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
                markConsumedFieldIncomplete(action);
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
                markConsumedFieldIncomplete(action);
                continue;
            }

            FieldAccessEvent consumed = matches.get(0);
            String rootAuthority = consumedFieldRootAuthority(action, root,
                    leaf.path, consumed, fieldEvents);
            if (rootAuthority.isEmpty()) {
                markConsumedFieldIncomplete(action);
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
            action.put("consumedFieldOccurrence", 1);
            action.put("consumedFieldOccurrenceAuthority",
                    "UNIQUE_CONTAINED_RUNTIME_FIELD_READ_V1");
            if ("LOCAL_DEFINITION_ROOT_PENDING_AUTHORITATIVE_"
                    .concat("SCHEDULER_DEFINITION_INDEX_V1").equals(
                            rootAuthority)) {
                action.put("consumedFieldSiteBindingComplete", true);
                action.put("consumedFieldBindingComplete", false);
            } else {
                action.put("consumedFieldBindingComplete", true);
            }
        }
    }

    private static void clearConsumedFieldEvidence(
            Map<String, Object> action) {
        for (String key : new String[]{
                "consumedFieldMethod", "consumedFieldUnitIndex",
                "consumedFieldSiteId", "consumedFieldSiteAuthority",
                "consumedFieldRootAuthority",
                "consumedFieldOccurrence",
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
            Map<String, Object> action) {
        action.put("consumedFieldBindingComplete", false);
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
        if ("HEAP_PRESTATE".equals(port.sourceKind)) {
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
            List<Map<String, Object>> occurrenceRows = new ArrayList<>();
            int selectedOccurrence = -1;
            for (int index = 0; index < occurrences.size(); index++) {
                RuntimeEvent occurrence = occurrences.get(index);
                if (occurrence == event) {
                    selectedOccurrence = index + 1;
                }
                occurrenceRows.add(object(
                        "occurrence", index + 1,
                        "outcome", occurrence.hasOutcome
                                ? occurrence.outcome : null));
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
                    "selectedOccurrence", selectedOccurrence,
                    "occurrences", occurrenceRows));
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
                    "NEAREST_PRECEDING_MATCHING_SOURCE_ENDPOINT";
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
                    boolean ordered = siteObserved || valueMatch != null
                            || readFrom != null
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
            if (edge.usesCanonicalOutput()) {
                validationRow.put("fromOutputPort", edge.fromOutputPort);
                validationRow.put("fromOutputCell", edge.fromOutputCell);
                validationRow.put("aliasProofEdgeIds",
                        new ArrayList<>(edge.aliasProofEdgeIds));
                validationRow.put("aliasProofAuthority",
                        edge.aliasProofAuthority);
                validationRow.put("aliasProofComplete", true);
            }
            result.edgeValidations.add(validationRow);
        }
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

    /** Builds each region-instance plan once, after all demand promotion. */
    private static Map<String, RegionPlanDraft> buildRegionPlans(
            List<InstanceEvidence> evidence, RuntimeTraceIndex trace,
            RootArgumentRuntimeTypeIndex rootArgumentRuntimeTypes) {
        Map<String, RegionPlanDraft> drafts = new LinkedHashMap<>();
        for (InstanceEvidence instance : evidence) {
            List<StaticPort> concreteInputs =
                    instance.concreteDemandSlice.inputs(instance.region);
            List<Map<String, Object>> inputObjects = inputObservations(
                    concreteInputs, instance.root,
                    instance.runtimeEvents,
                    instance.fieldEvents, instance.methodEvents);
            List<Map<String, Object>> symbolize = symbolizeActions(
                    instance.region, concreteInputs, instance.root,
                    inputObjects, instance.runtimeEvents,
                    instance.fieldEvents);
            List<Map<String, Object>> branches = branchActions(
                    instance.region, instance.runtimeEvents);
            boolean branchesResolved = branchActionsReady(branches);
            boolean symbolizeReady = symbolizeActionsReady(symbolize);
            boolean symbolicPotential = !concreteInputs.isEmpty()
                    || instance.region.inputs.isEmpty()
                    || instance.region.branches.isEmpty();
            boolean boundaryReady = branchesResolved
                    && instance.region.inputSelectionComplete
                    && instance.runtimePathEvidenceComplete
                    && symbolizeReady;
            boolean replayable = instance.anchorObserved
                    && instance.runtimePathEvidenceComplete;
            boolean symbolicReady = replayable && boundaryReady
                    && symbolicPotential;
            List<String> runtimeGaps = new ArrayList<>();
            if (!instance.containedCallTreeComplete) {
                runtimeGaps.add("CONTAINED_CALL_TREE_LIMIT_EXCEEDED");
            } else if (!instance.runtimePathEvidenceComplete) {
                runtimeGaps.add("PATH_SIGNATURE_LIMIT_EXCEEDED");
            }
            RegionPlanDraft plan = new RegionPlanDraft(instance,
                    rootSelector(instance.root,
                            trace.invocationOrdinal(instance.root),
                            trace.invocationOrdinalWithinContext(instance.root),
                            runtimeRootArgumentSelector(instance.root,
                                    values(trace.methodsBySignature.get(
                                            instance.root.method)),
                                    rootArgumentRuntimeTypes)),
                    instance.concreteDemandSlice.definitionMethods(
                            instance.observedMethods),
                    admission(replayable, symbolicReady,
                            replayable
                                    ? "RUNTIME_SELECTED_ROOT_REPLAY"
                                    : "NO_VALIDATED_RUNTIME_PATH",
                            runtimeGaps),
                    symbolize, branches);
            if (instance.region.isTargetClosure()) {
                plan.goals.add(plan.baseGoal(targetReachGoalId(
                                instance.instanceId,
                                instance.region.anchorMethod),
                        "TARGET_REACH_CLOSURE"));
            }
            drafts.put(instance.instanceId, plan);
        }
        return drafts;
    }

    private static Map<String, Object> admission(
            boolean replayable, boolean ready, String mode,
            Collection<?> gaps) {
        List<Object> blockers = new ArrayList<>();
        if (gaps != null) blockers.addAll(gaps);
        if (replayable && !ready && blockers.isEmpty()) {
            blockers.add(object("kind", "SYMBOLIC_BOUNDARY_NOT_READY"));
        }
        return object(
                "state", ready ? "READY"
                        : replayable ? "DISCOVERED" : "BLOCKED",
                "mode", safe(mode),
                "blockers", blockers);
    }

    private static String admissionMode(Map<String, Object> goal) {
        Map<String, Object> admission = goal == null ? null
                : mapValue(goal.get("admission"));
        return admission == null ? "" : string(admission.get("mode"));
    }

    /**
     * Attaches bounded output-relation goals to the one activation envelope
     * that represents the concrete upstream region invocation.
     *
     * <p>A read-from demand is not a new invocation. Keeping it as a goal
     * preserves goal-local input, branch, admission, and output-closure
     * scope without copying the region instance plan.</p>
     */
    private static List<OutputGoalDraft> attachOutputRelationGoals(
            List<UpstreamEdgeBinding> bindings,
            StaticProjectionIndex staticProjections,
            Map<String, RegionPlanDraft> plansByInstance) {
        List<OutputGoalDraft> outputGoals = new ArrayList<>();
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

        for (List<UpstreamEdgeBinding> demand : grouped.values()) {
            UpstreamEdgeBinding first = demand.get(0);
            RegionPlanDraft base = plansByInstance.get(
                    first.upstream.instanceId);
            if (base == null) {
                continue;
            }

            Map<String, Object> outputGoal = base.baseGoal(
                    outputRelationGoalId(demand),
                    "OUTPUT_RELATION_CLOSURE");
            boolean writerPathReplayable =
                    first.upstream.runtimePathEvidenceComplete;

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
                    && !mergeOutputGoalExecution(outputGoal, members,
                    issues)) {
                outputClosure = null;
            }
            if (issues.isEmpty()) {
                outputGoal.put(OutputClosureContract.FIELD,
                        outputClosure.toJson());
                outputGoals.add(new OutputGoalDraft(
                        base, outputGoal, members));
            } else {
                outputGoal.put("symbolize", Collections.emptyList());
                outputGoal.put("branches", Collections.emptyList());
                outputGoal.remove("containerElementFieldBindings");
                outputGoal.remove("heapStateBindings");
            }

            outputGoal.put("admission", admission(writerPathReplayable,
                    writerPathReplayable && issues.isEmpty(),
                    writerPathReplayable
                            ? "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY"
                            : "RUNTIME_READ_FROM_WITNESS_ONLY_PATH_TRUNCATED",
                    issues));

            List<Map<String, Object>> bindingRows = new ArrayList<>();
            for (UpstreamEdgeBinding binding : demand) {
                bindingRows.add(binding.toMap());
            }
            outputGoal.put("edgeBindings", bindingRows);
            base.goals.add(outputGoal);
        }
        return outputGoals;
    }

    private static UpstreamOutputMemberPlan upstreamOutputMemberPlan(
            RegionPlanDraft base, List<UpstreamEdgeBinding> bindings) {
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
                base.symbolize, outputSlice.inputPorts, "symbol");
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
        outputSlice.validateNormalExitFieldCapture(input, selectedInputs);
        List<Map<String, Object>> selectedBranches = selectActivationRows(
                base.branches, outputSlice.sites, "siteId");
        boolean sliceReady = outputSlice.complete
                && outputSlice.captureBindingsComplete
                && inputSelectionComplete
                && containerBindingsReady
                && inputAliasesReady
                && symbolizeActionsReady(selectedInputs)
                && branchActionsReady(selectedBranches);
        if (!sliceReady) {
            List<String> causes = new ArrayList<>();
            if (!outputSlice.complete) {
                causes.add("STATIC_SLICE_INCOMPLETE");
            }
            if (!outputSlice.captureBindingsComplete) {
                causes.add("CAPTURE_BINDINGS_INCOMPLETE"
                        + (outputSlice.captureBindingIssues.isEmpty()
                        ? "" : "=" + outputSlice.captureBindingIssues));
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

    private static boolean mergeOutputGoalExecution(
            Map<String, Object> goal,
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
        goal.put("symbolize", new ArrayList<>(inputs.values()));
        goal.put("branches", new ArrayList<>(branches.values()));
        if (containers.isEmpty()) {
            goal.remove("containerElementFieldBindings");
        } else {
            goal.put("containerElementFieldBindings",
                    new ArrayList<>(containers.values()));
        }
        if (heaps.isEmpty()) {
            goal.remove("heapStateBindings");
        } else {
            goal.put("heapStateBindings",
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
    private static void refineMapValueElementProjectionGoals(
            List<OutputGoalDraft> outputGoals) {
        Map<String, List<OutputGoalDraft>> selectedByInstance =
                new LinkedHashMap<>();
        for (OutputGoalDraft context : outputGoals) {
            UpstreamOutputMemberPlan member = context.singleMember();
            if (member == null || !member.outputSlice.complete) {
                continue;
            }
            String instance = context.plan.instance.instanceId;
            if (!instance.isEmpty()) {
                add(selectedByInstance, instance, context);
            }
        }

        for (OutputGoalDraft context : outputGoals) {
            Map<String, Object> goal = context.goal;
            UpstreamOutputMemberPlan producerMember =
                    context.singleMember();
            StaticOutputSlice producerSlice = producerMember == null
                    ? null : producerMember.outputSlice;
            List<Map<String, Object>> edgeBindings = mapRows(
                    goal.get("edgeBindings"));
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
                List<OutputGoalDraft> selected = values(
                        selectedByInstance.get(downstreamInstance));
                for (OutputGoalDraft downstream : selected) {
                    UpstreamOutputMemberPlan downstreamMember =
                            downstream.singleMember();
                    if (downstreamMember == null) {
                        continue;
                    }
                    for (Map<String, Object> declaration
                            : downstreamMember.outputSlice
                            .containerElementFieldBindings) {
                        if (!downstreamInput.equals(string(declaration.get(
                                "containerInputPort")))) {
                            continue;
                        }
                        DownstreamContainerDemand demand =
                                DownstreamContainerDemand.from(edge,
                                        downstream.plan.toMap(), declaration);
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
                            !producerMember.outputSlice.captureBindings
                                    .isEmpty()
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
                            demand.declaredField.owner,
                            "declaredFieldType",
                            demand.declaredField.type,
                            "declaredFieldName",
                            demand.declaredField.name,
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

            goal.put("mapValueElementFieldProjections",
                    declarations);
            boolean composable = issues.isEmpty()
                    && !declarations.isEmpty();
            // Preserve all pre-existing readiness decisions when the static
            // declaration is complete. Runtime identity evidence is checked
            // later by the importer. A static proof/declaration failure still
            // closes this goal before scheduling.
            if (!composable) {
                goal.put("admission", admission(false, false,
                        admissionMode(goal), issues));
            }
        }
    }

    private static String targetReachGoalId(
            String regionInstanceId, String targetMethod) {
        return "GOAL.TARGET_REACH." + stableId(regionInstanceId + "\n"
                + safe(targetMethod));
    }

    private static String outputRelationGoalId(
            List<UpstreamEdgeBinding> demand) {
        if (demand == null || demand.isEmpty()) {
            throw new IllegalArgumentException(
                    "output relation goal requires one demand binding");
        }
        UpstreamEdgeBinding first = demand.get(0);
        List<String> members = new ArrayList<>();
        for (UpstreamEdgeBinding binding : demand) {
            members.add(string(binding.edge.edgeId) + "\t"
                    + (binding.output == null ? ""
                    : binding.output.portId) + "\t"
                    + (binding.downstreamInput == null ? ""
                    : binding.downstreamInput.portId));
        }
        Collections.sort(members);
        return "GOAL.OUTPUT_RELATION." + stableId(
                first.upstream.instanceId + "\n"
                        + first.downstream.instanceId + "\n"
                        + String.join("\n", members));
    }

    private static String stableId(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(safe(value).getBytes(
                    StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte item : bytes) {
                result.append(String.format("%02x", item & 0xff));
            }
            return result.substring(0, 20);
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException("SHA-256 is unavailable",
                    impossible);
        }
    }

    private static final class RegionPlanDraft {
        private final InstanceEvidence instance;
        private final Map<String, Object> rootSelector;
        private final List<String> runtimeDefinitionMethods;
        private final Map<String, Object> admission;
        private final List<Map<String, Object>> symbolize;
        private final List<Map<String, Object>> branches;
        private final List<Map<String, Object>> goals = new ArrayList<>();

        private RegionPlanDraft(
                InstanceEvidence instance, Map<String, Object> rootSelector,
                List<String> runtimeDefinitionMethods,
                Map<String, Object> admission,
                List<Map<String, Object>> symbolize,
                List<Map<String, Object>> branches) {
            this.instance = instance;
            this.rootSelector = rootSelector;
            this.runtimeDefinitionMethods = runtimeDefinitionMethods;
            this.admission = admission;
            this.symbolize = symbolize;
            this.branches = branches;
        }

        private Map<String, Object> baseGoal(String goalId, String kind) {
            return object(
                    "goalId", goalId,
                    "kind", kind,
                    "runtimeDefinitionMethods", runtimeDefinitionMethods,
                    "admission", admission,
                    "symbolize", symbolize,
                    "branches", branches);
        }

        private Map<String, Object> toMap() {
            return object(
                    "regionInstanceId", instance.instanceId,
                    "regionId", instance.region.regionId,
                    "test", instance.root.test,
                    "rootSelector", rootSelector,
                    "targetMethod", instance.region.anchorMethod,
                    "closureGoals", goals);
        }
    }

    private static final class OutputGoalDraft {
        private final RegionPlanDraft plan;
        private final Map<String, Object> goal;
        private final List<UpstreamOutputMemberPlan> members;

        private OutputGoalDraft(RegionPlanDraft plan,
                                Map<String, Object> goal,
                                List<UpstreamOutputMemberPlan> members) {
            this.plan = plan;
            this.goal = goal;
            this.members = members;
        }

        private UpstreamOutputMemberPlan singleMember() {
            return members.size() == 1 ? members.get(0) : null;
        }
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
        return FieldPathSpec.path(cell);
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
                    && (!(action.get("fieldPaths")
                    instanceof Collection<?>)
                    || ((Collection<?>) action.get("fieldPaths")).isEmpty())) {
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
                            nearestMatchingSourceEndpoint(values(
                                    sourceFingerprints.get(
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

    private static FingerprintMatch nearestMatchingSourceEndpoint(
            List<EndpointFingerprint> sources,
            EndpointFingerprint target) {
        FingerprintMatch best = null;
        for (EndpointFingerprint source : sources) {
            if (!source.digest.equals(target.digest)
                    || source.seq > target.seq) {
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
                                                 InstanceEvidence downstream,
                                                 RuntimeTraceIndex trace) {
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
        WriteCandidateIndex writes = WriteCandidateIndex.build(
                fromField, upstream, trace);
        SharedReadFrom selected = null;
        for (FieldAccessEvent read : trace.fieldEvents(
                toField, downstream.calls)) {
            if (!"FIELD_READ".equals(read.kind)
                    || !sameField(toField, read.parsedField)
                    || read.receiverObjectId == 0) {
                continue;
            }
            WriteCandidate write = writes.latestFor(read);
            if (write == null) {
                continue;
            }
            SharedReadFrom candidate = new SharedReadFrom(
                    write.field, read, write.evidence);
            if (selected == null
                    || candidate.writerEventSeq()
                    > selected.writerEventSeq()) {
                selected = candidate;
            }
        }
        return selected;
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
        int rows = 0;
        try (BufferedReader reader = Files.newBufferedReader(file.toPath(),
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                rows++;
                JsonObject row = parseJsonObject(line);
                StaticDataflowProjectionEdge edge =
                        StaticDataflowProjectionEdge.fromJson(row);
                if (edge == null || edge.edgeId.isEmpty()
                        || result.byId.containsKey(edge.edgeId)) {
                    throw new IllegalArgumentException(
                            "malformed or duplicate frozen static graph edge");
                }
                result.add(edge, StaticOutputSlice.causalEdgeReference(row));
            }
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "failed to read frozen static graph: " + file, exception);
        }
        if (rows == 0) {
            throw new IllegalArgumentException(
                    "frozen static graph must not be empty");
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
                JsonObject row = parseJsonObject(trimmed);
                if (jsonInt(row, "schemaVersion", -1)
                        != STATIC_REGION_SCHEMA_VERSION) {
                    throw new IllegalArgumentException(
                            "unsupported symbolic region schema");
                }
                StaticRegion region = StaticRegion.fromJson(row);
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
                StaticRegionEdge edge = StaticRegionEdge.fromJson(
                        parseJsonObject(trimmed));
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

    static final class Result {
        final List<Map<String, Object>> regionPlans = new ArrayList<>();
        final List<Map<String, Object>> edgeValidations = new ArrayList<>();

        String regionPlansJsonl() {
            return jsonl(regionPlans);
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

        private Map<Integer, String> values() {
            return observed;
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
                    primitiveValue, hasOutcome, outcome, "", false);
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
                    false);
        }

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     String declaredCallee, int argumentIndex,
                     String runtimeType, int objectId,
                     String primitiveValue, boolean hasOutcome,
                     boolean outcome, String valueFingerprint,
                     boolean valueFingerprintComplete) {
            this(seq, kind, method, callId, invocationId, parentSiteId,
                    siteId, declaredCallee, argumentIndex, runtimeType,
                    objectId, primitiveValue, hasOutcome, outcome,
                    valueFingerprint, valueFingerprintComplete,
                    false, -1, "", "");
        }

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     String declaredCallee, int argumentIndex,
                     String runtimeType, int objectId,
                     String primitiveValue, boolean hasOutcome,
                     boolean outcome, String valueFingerprint,
                     boolean valueFingerprintComplete,
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
            this.hasSuccessorIndex = hasSuccessorIndex;
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
        final FieldCell parsedField;
        final int receiverObjectId;
        final int valueObjectId;
        final String primitiveValue;
        final String valueFingerprint;
        final boolean valueFingerprintComplete;

        FieldAccessEvent(long seq, String kind, String method, long callId,
                         String field, int receiverObjectId, int valueObjectId,
                         String primitiveValue) {
            this(seq, kind, method, callId, -1, "", field, receiverObjectId,
                    valueObjectId, primitiveValue, "", false);
        }

        FieldAccessEvent(long seq, String kind, String method, long callId,
                         String field, int receiverObjectId, int valueObjectId,
                         String primitiveValue, String valueFingerprint,
                         boolean valueFingerprintComplete) {
            this(seq, kind, method, callId, -1, "", field,
                    receiverObjectId, valueObjectId, primitiveValue,
                    valueFingerprint, valueFingerprintComplete);
        }

        FieldAccessEvent(long seq, String kind, String method, long callId,
                         int unitIndex, String siteId, String field,
                         int receiverObjectId, int valueObjectId,
                         String primitiveValue, String valueFingerprint,
                         boolean valueFingerprintComplete) {
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
        private final Map<String, List<MethodEvent>> invocationsByTestMethod =
                new LinkedHashMap<>();
        private final Map<String, List<FieldAccessEvent>>
                fieldEventsByReceiver = new LinkedHashMap<>();
        private final Map<String, List<FieldAccessEvent>> fieldReadsByField =
                new LinkedHashMap<>();
        private final Map<Integer, List<RuntimeEvent>> mutatorsByObject =
                new LinkedHashMap<>();
        private final Map<Long, RuntimeEvent> completionsByInvocation =
                new LinkedHashMap<>();
        private final Map<String, List<TraceEndpoint>> endpointsByDigest =
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
                add(result.invocationsByTestMethod,
                        testMethodKey(event.test, event.method), event);
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
                if ("CALL_SITE_ENTER".equals(event.kind)
                        && event.objectId != 0
                        && isContainerMutator(event.declaredCallee)) {
                    result.mutatorsByObject.computeIfAbsent(
                            event.objectId,
                            ignored -> new ArrayList<>()).add(event);
                } else if ("CALL_SITE_RETURN".equals(event.kind)
                        && event.invocationId > 0L) {
                    result.completionsByInvocation.putIfAbsent(
                            event.invocationId, event);
                }
                if (event.valueFingerprintComplete
                        && !event.valueFingerprint.isEmpty()) {
                    add(result.endpointsByDigest, event.valueFingerprint,
                            new TraceEndpoint(event.seq, event.callId));
                }
            }
            for (FieldAccessEvent event : values(fields)) {
                result.fieldsByCall.computeIfAbsent(event.callId,
                        ignored -> new ArrayList<>()).add(event);
                String field = RuntimeFieldAccessIndex.exactFieldKey(
                        event.field);
                if (!field.isEmpty() && event.receiverObjectId != 0) {
                    add(result.fieldEventsByReceiver,
                            RuntimeFieldAccessIndex.receiverFieldKey(
                                    event.receiverObjectId, field), event);
                    if ("FIELD_READ".equals(event.kind)) {
                        add(result.fieldReadsByField, field, event);
                    }
                }
                if (event.valueFingerprintComplete
                        && !event.valueFingerprint.isEmpty()) {
                    add(result.endpointsByDigest, event.valueFingerprint,
                            new TraceEndpoint(event.seq, event.callId));
                }
            }
            return result;
        }

        private static String testMethodKey(String test, String method) {
            return safe(test) + '\n' + safe(method);
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

        private List<FieldAccessEvent> fieldEvents(
                FieldCell field, Set<Long> calls) {
            String key = RuntimeFieldAccessIndex.exactFieldKey(
                    field.signature());
            if (key.isEmpty()) {
                return Collections.emptyList();
            }
            List<FieldAccessEvent> result = new ArrayList<>();
            for (FieldAccessEvent event : values(fieldReadsByField.get(key))) {
                if (calls.contains(event.callId)) {
                    result.add(event);
                }
            }
            return result;
        }

        private List<RuntimeEvent> mutators(int objectId) {
            return values(mutatorsByObject.get(objectId));
        }

        private RuntimeEvent completion(RuntimeEvent enter) {
            if (enter == null || enter.invocationId <= 0L) {
                return null;
            }
            RuntimeEvent completion = completionsByInvocation.get(
                    enter.invocationId);
            return completion != null
                    && completion.seq > enter.seq
                    && completion.callId == enter.callId
                    && completion.siteId.equals(enter.siteId)
                    ? completion : null;
        }

        private List<TraceEndpoint> endpoints(String digest) {
            return values(endpointsByDigest.get(safe(digest)));
        }
    }

    private static final class TraceEndpoint {
        private final long seq;
        private final long callId;

        private TraceEndpoint(long seq, long callId) {
            this.seq = seq;
            this.callId = callId;
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
        private String selection = "";
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

        private StaticPort frameInputFor(String outputCell) {
            StaticPort selected = null;
            for (StaticPort input : inputs) {
                if (!"HEAP_PRESTATE".equals(input.sourceKind)
                        || !outputCell.equals(input.cell)) {
                    continue;
                }
                if (selected != null) {
                    return null;
                }
                selected = input;
            }
            return selected;
        }

        private StaticPort uniqueDemandFrontierPort(
                String cell, Set<String> observedMethods,
                String runtimeRootMethod) {
            StaticPort selected = null;
            for (StaticPort input : inputs) {
                if ("HEAP_PRESTATE".equals(input.sourceKind)) {
                    continue;
                }
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

        private boolean isTargetClosure() {
            return "EXCEPTION_BACKWARD_CAUSAL_CLOSURE".equals(selection);
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

        private static StaticRegion fromJson(JsonObject json) {
            StaticRegion region = new StaticRegion();
            region.regionId = jsonString(json, "regionId");
            region.rootMethod = jsonString(json, "rootMethod");
            region.anchorMethod = firstNonBlank(jsonString(json, "anchorMethod"),
                    region.rootMethod);
            region.selection = jsonString(json, "selection");
            region.methods.addAll(jsonStringArray(json, "methods"));
            region.methods.add(region.rootMethod);
            for (JsonObject object : jsonObjectArray(json,
                    "symbolicInputs")) {
                region.inputs.add(new StaticPort(
                        jsonString(object, "portId"),
                        jsonString(object, "cell"),
                        jsonString(object, "sourceKind"),
                        jsonString(object, "projection"), "",
                        jsonString(object, "javaType"),
                        MaterializationSpec.decode(object)));
            }
            for (JsonObject object : jsonObjectArray(json, "outputs")) {
                region.outputs.add(new StaticPort(
                        jsonString(object, "portId"),
                        jsonString(object, "cell"), "", "",
                        jsonString(object, "kind"),
                        jsonString(object, "javaType"),
                        MaterializationSpec.none()));
            }
            for (JsonObject object : jsonObjectArray(json,
                    "outputSlices")) {
                StaticOutputSlice slice = StaticOutputSlice.fromJson(object);
                if (!slice.outputPort.isEmpty()) {
                    region.outputSlices.put(slice.outputPort, slice);
                }
            }
            for (JsonObject object : jsonObjectArray(json,
                    "branchPolicies")) {
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
            for (JsonObject object : jsonObjectArray(json,
                    "argumentPathFields")) {
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
                                    fieldCell(declaration
                                            .declaredFieldSignature).type);
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
                    StaticPort frameInput = region.outputSlices.containsKey(
                            output.portId) ? region.frameInputFor(
                            output.cell) : null;
                    if (frameInput != null) {
                        result.inputPortIds.add(frameInput.portId);
                    }
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
        private final String invoke;
        private final String accessorImplementationMethod;
        private final String method;
        private final String siteId;
        private final int unitIndex;

        private StaticDataflowProjectionEdge(String edgeId, String kind,
                String transferKind, String relation, boolean assertable,
                String fromCell, String toCell, String objectFromCell,
                String objectToCell, String projectionBaseEdgeId,
                List<String> fieldPath, boolean fieldSensitive,
                String declaredFieldSignature, String invoke,
                String accessorImplementationMethod,
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
            this.invoke = safe(invoke);
            this.accessorImplementationMethod = safe(
                    accessorImplementationMethod);
            this.method = safe(method);
            this.siteId = safe(siteId);
            this.unitIndex = unitIndex;
        }

        private static StaticDataflowProjectionEdge fromJson(
                JsonObject json) {
            if (jsonInt(json, "schemaVersion", -1)
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
                    jsonString(json, "invoke"),
                    jsonString(json, "accessorImplementationMethod"),
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
                    || !fieldSensitive || fieldPath.isEmpty()) {
                return false;
            }
            FieldCell field = fieldCell(declaredFieldSignature);
            return field.declaredSignature
                    && field.name.equals(fieldPath.get(
                    fieldPath.size() - 1))
                    && field.type.equals(methodReturnType(invoke))
                    && field.type.equals(methodReturnType(
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
        private String toPort = "";
        private String kind = "";
        private String siteId = "";
        private boolean mappingOnly;
        private FieldCell fromField = FieldCell.unresolved();
        private FieldCell toField = FieldCell.unresolved();

        private static StaticRegionEdge fromJson(JsonObject json) {
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
            edge.toPort = jsonString(json, "toPort");
            edge.fromField = fieldCell(edge.fromPort);
            edge.toField = fieldCell(edge.toPort);
            edge.kind = jsonString(json, "kind");
            edge.siteId = jsonString(json, "siteId");
            edge.mappingOnly = "MAPPING_ONLY".equals(
                    jsonString(json, "semanticMode"));
            return edge;
        }

        private String producerOutputEndpoint() {
            return usesCanonicalOutput() ? fromOutputPort
                    : mappingOnly && !"SHARED_STATE".equals(kind)
                    ? "" : fromPort;
        }

        private boolean usesCanonicalOutput() {
            return canonicalAliasValid();
        }

        private String sourceFingerprintEndpoint(StaticRegion region) {
            if (producerOutputFor(region) == null) {
                return "";
            }
            return usesCanonicalOutput() ? fromOutputCell : fromPort;
        }

        private boolean canonicalAliasValid() {
            return aliasProofComplete
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
                        || !callee.equals(event.declaredCallee)
                        || !site.endsWith("#u" + unit)) {
                    continue;
                }
                result.add(event);
            }
            return result;
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
        private final RuntimeTraceIndex trace;
        private final Map<String, SharedReadFrom> confirmedReadFrom =
                new LinkedHashMap<>();
        private final Set<String> absentReadFrom = new LinkedHashSet<>();

        private RuntimeRelationEvidenceCache(RuntimeTraceIndex trace) {
            this.trace = trace;
        }

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
                    upstream, downstream, trace);
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

    /**
     * Writer candidates for one upstream instance, grouped by exact receiver.
     * Construction is linear in that instance's field events plus the
     * mutators of the referenced container objects. Reads use one upper-bound
     * search instead of a write-by-read Cartesian scan.
     */
    private static final class WriteCandidateIndex {
        private final Map<Integer, List<WriteCandidate>> byReceiver =
                new LinkedHashMap<>();

        private static WriteCandidateIndex build(
                FieldCell field, InstanceEvidence instance,
                RuntimeTraceIndex trace) {
            WriteCandidateIndex result = new WriteCandidateIndex();
            Set<String> seen = new LinkedHashSet<>();
            for (FieldAccessEvent event : instance.fieldEvents) {
                if (!sameField(field, event.parsedField)
                        || event.receiverObjectId == 0) {
                    continue;
                }
                if ("FIELD_WRITE".equals(event.kind)) {
                    result.add(event, new WriteEvidence(null, null), seen);
                    continue;
                }
                if (!"FIELD_READ".equals(event.kind)
                        || event.valueObjectId == 0) {
                    continue;
                }
                for (RuntimeEvent mutation
                        : trace.mutators(event.valueObjectId)) {
                    if (mutation.seq <= event.seq
                            || !instance.calls.contains(mutation.callId)) {
                        continue;
                    }
                    RuntimeEvent completion = trace.completion(mutation);
                    if (completion == null
                            || !instance.calls.contains(completion.callId)) {
                        continue;
                    }
                    result.add(event, new WriteEvidence(
                            mutation, completion), seen);
                }
            }
            for (List<WriteCandidate> candidates
                    : result.byReceiver.values()) {
                candidates.sort(Comparator.comparingLong(
                        WriteCandidate::writerEventSeq));
            }
            return result;
        }

        private void add(FieldAccessEvent field, WriteEvidence evidence,
                         Set<String> seen) {
            long writerSeq = evidence.mutation == null
                    ? field.seq : evidence.writerEventSeq();
            String identity = field.receiverObjectId + "\n" + field.seq
                    + "\n" + writerSeq;
            if (!seen.add(identity)) {
                return;
            }
            byReceiver.computeIfAbsent(field.receiverObjectId,
                    ignored -> new ArrayList<>()).add(
                    new WriteCandidate(field, evidence));
        }

        private WriteCandidate latestFor(FieldAccessEvent read) {
            List<WriteCandidate> candidates = values(
                    byReceiver.get(read.receiverObjectId));
            int low = 0;
            int high = candidates.size();
            while (low < high) {
                int middle = (low + high) >>> 1;
                if (candidates.get(middle).writerEventSeq() <= read.seq) {
                    low = middle + 1;
                } else {
                    high = middle;
                }
            }
            for (int index = low - 1; index >= 0; index--) {
                WriteCandidate candidate = candidates.get(index);
                if (candidate.evidence.mutation == null
                        || candidate.field.valueObjectId != 0
                        && read.valueObjectId != 0
                        && candidate.field.valueObjectId
                        == read.valueObjectId) {
                    return candidate;
                }
            }
            return null;
        }
    }

    private static final class WriteCandidate {
        private final FieldAccessEvent field;
        private final WriteEvidence evidence;

        private WriteCandidate(FieldAccessEvent field,
                               WriteEvidence evidence) {
            this.field = field;
            this.evidence = evidence;
        }

        private long writerEventSeq() {
            return evidence.mutation == null
                    ? field.seq : evidence.writerEventSeq();
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
        private final FieldCell declaredField;
        private final List<String> fieldPath;
        private final boolean declarationComplete;

        private DownstreamContainerDemand(
                Map<String, Object> downstreamActivation, String edgeId,
                String downstreamInputPort, String bindingId,
                String baseInputSymbol, String declaredFieldSignature,
                List<String> fieldPath,
                boolean declarationComplete) {
            this.downstreamActivation = downstreamActivation;
            this.edgeId = edgeId;
            this.downstreamInputPort = downstreamInputPort;
            this.bindingId = bindingId;
            this.baseInputSymbol = baseInputSymbol;
            this.declaredFieldSignature = declaredFieldSignature;
            this.declaredField = fieldCell(declaredFieldSignature);
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
                    new ArrayList<>(stringSet(declaration.get("fieldPath"))),
                    Boolean.TRUE.equals(declaration.get("complete"))
                            && Integer.valueOf(1).equals(declaration.get(
                            "schemaVersion"))
                            && "ARRAY_ELEMENT_FIELD".equals(string(
                            declaration.get("kind"))));
        }

        private boolean complete() {
            return declarationComplete && !edgeId.isEmpty()
                    && !downstreamInputPort.isEmpty()
                    && !bindingId.isEmpty() && !baseInputSymbol.isEmpty()
                    && declaredField.declaredSignature
                    && fieldPath.equals(Collections.singletonList(
                    declaredField.name));
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
                StaticOutputSlice slice) {
            List<Map<String, Object>> edges = slice.causalEdges;
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

            String outputCell = slice.outputCell;
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
            for (Map<String, Object> input : slice.inputBindings) {
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
        private boolean complete;
        private boolean structuralComplete;
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
        private boolean captureBindingsComplete = true;
        private final List<String> captureBindingIssues = new ArrayList<>();
        private boolean captureDischargedByHeapEffectTransformer;
        private String captureDischargeInputPort = "";
        private String captureDischargeAuthority = "";
        private final List<Map<String, Object>> inputGaps =
                new ArrayList<>();
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

        private static StaticOutputSlice fromJson(JsonObject json) {
            StaticOutputSlice slice = new StaticOutputSlice();
            slice.outputPort = jsonString(json, "outputPort");
            slice.outputCell = jsonString(json, "outputCell");
            slice.inputPorts.addAll(jsonStringArray(json, "inputPorts"));
            slice.methods.addAll(jsonStringArray(json, "methods"));
            slice.sites.addAll(jsonStringArray(json, "sites"));
            slice.causalEdgeIds.addAll(jsonStringArray(json,
                    "causalEdgeIds"));
            for (JsonObject binding : jsonObjectArray(json,
                    "inputBindings")) {
                Map<String, Object> parsed = jsonMap(binding);
                if (!parsed.containsKey("leafFieldSignature")
                        && parsed.containsKey("declaredFieldSignature")) {
                    parsed.put("leafFieldSignature",
                            parsed.get("declaredFieldSignature"));
                }
                slice.inputBindings.add(parsed);
            }
            slice.requestedStateTransformerContractPresent = jsonHasField(
                    json, "requestedStateTransformerContractComplete");
            for (JsonObject obligation : jsonObjectArray(json,
                    "requestedStateTransformerObligations")) {
                slice.requestedStateTransformerObligations.add(
                        jsonMap(obligation));
            }
            slice.requestedStateTransformerContractIssues.addAll(
                    jsonStringArray(json,
                            "requestedStateTransformerContractIssues"));
            slice.requestedStateTransformerContractComplete = jsonBoolean(
                    json, "requestedStateTransformerContractComplete",
                    false);
            for (JsonObject initializer : jsonObjectArray(json,
                    "heapInitializers")) {
                slice.heapInitializers.add(jsonMap(initializer));
            }
            for (JsonObject binding : jsonObjectArray(json,
                    "captureBindings")) {
                slice.captureBindings.add(jsonMap(binding));
            }
            slice.captureBindingsComplete = jsonBoolean(json,
                    "captureBindingsComplete",
                    slice.captureBindings.isEmpty());
            for (JsonObject binding : jsonObjectArray(json,
                    "containerElementFieldBindings")) {
                slice.containerElementFieldBindings.add(jsonMap(binding));
            }
            slice.captureBindingIssues.addAll(jsonStringArray(json,
                    "captureBindingIssues"));
            for (JsonObject detail : jsonObjectArray(json, "inputGaps")) {
                slice.inputGaps.add(jsonMap(detail));
            }
            slice.structuralIssues.addAll(jsonStringArray(json,
                    "truncationReasons"));
            return slice;
        }

        private Map<String, Object> copyContainerElementFieldBinding(
                Map<String, Object> declaration) {
            Map<String, Object> copy = new LinkedHashMap<>(declaration);
            FieldCell field = fieldCell(string(declaration.get(
                    "declaredFieldSignature")));
            if (field.declaredSignature) {
                copy.put("declaredFieldOwnerClass", field.owner);
                copy.put("declaredFieldType", field.type);
                copy.put("declaredFieldName", field.name);
            }
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

        private static Map<String, Object> causalEdgeReference(
                JsonObject json) {
            Map<String, Object> result = jsonMap(json);
            result.put("edgeId", firstNonBlank(string(result.remove("edgeId")),
                    string(result.remove("id"))));
            result.keySet().retainAll(new LinkedHashSet<>(
                    java.util.Arrays.asList(
                            "edgeId", "method", "siteId", "fromCell", "toCell",
                            "transferKind", "kind", "invoke",
                            "containerProjectionContractVersion",
                            "containerProjectionOperation",
                            "containerProjectionAuthority", "elementRelation",
                            "iterationOrderAuthority",
                            "receiverValueDependencyComplete",
                            "elementIdentityPreserving",
                            "mappingAssociationPreserving", "backedView",
                            "snapshot", "containerEqualityAsserted",
                            "guardSiteId", "guardedMutationSiteId",
                            "requiredOutcome", "guardedMutations")));
            return result;
        }

        private boolean validInputGaps() {
            Set<String> diagnostics = new LinkedHashSet<>();
            for (Map<String, Object> detail : inputGaps) {
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
                        || !diagnostics.add(diagnostic)) {
                    return false;
                }
            }
            return true;
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

        private void refineInputGaps(Set<String> observed,
                                     StaticOutputSlice refined) {
            if (!validInputGaps()) {
                refined.inputGaps.addAll(copyRows(inputGaps));
                refined.runtimeRefinementComplete = false;
                return;
            }
            for (Map<String, Object> detail : inputGaps) {
                Set<String> dependencyMethods = stringSet(
                        detail.get("dependencyMethods"));
                boolean exactStaticMethods = !dependencyMethods.isEmpty()
                        && methods.containsAll(dependencyMethods);
                boolean observedDependency = intersects(dependencyMethods,
                        observed);
                if (exactStaticMethods && !observedDependency) {
                    continue;
                }
                refined.inputGaps.add(new LinkedHashMap<>(detail));
                if (!exactStaticMethods) {
                    // A missing, ambiguous, or out-of-slice method set must
                    // never be interpreted as proof of an unobserved path.
                    refined.runtimeRefinementComplete = false;
                }
            }
        }

        private StaticOutputSlice runtimeRefined(InstanceEvidence evidence) {
            StaticOutputSlice refined = new StaticOutputSlice();
            refined.outputPort = outputPort;
            refined.outputCell = outputCell;
            refined.structuralIssues.addAll(structuralIssues);
            refined.staticSites.addAll(sites);
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
            refineInputGaps(observed, refined);
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
            refined.structuralComplete = structuralIssues.isEmpty()
                    && !causalEdgeIds.isEmpty()
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
                    && refined.inputGaps.isEmpty()
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
            if (port == null || !port.materialization.directFieldPath()) {
                return null;
            }
            List<String> path = port.materialization.path();
            String leaf = port.materialization.leafField();
            String method = port.materialization.method();
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
                // In-place containers use the exact same-cell pre-state plus
                // importer-validated, path-ordered heap effects. They do not
                // need a separate scalar output capture.
                refined.captureBindings.clear();
                refined.captureBindingsComplete = true;
                refined.captureBindingIssues.clear();
                refined.captureDischargedByHeapEffectTransformer = true;
                refined.captureDischargeInputPort = heapEffectCaptureInput;
                refined.captureDischargeAuthority =
                        "HEAP_EFFECT_STATE_TRANSFORMER";
                return;
            }

            if (!captureBindings.isEmpty()) {
                refined.captureBindings.clear();
                int matchedCaptureCount = 0;
                boolean exitFieldRequested = false;
                for (Map<String, Object> binding : captureBindings) {
                    String captureKind = string(binding.get("captureKind"));
                    if ("REGION_EXIT_FIELD".equals(captureKind)) {
                        exitFieldRequested = true;
                        refined.captureBindings.add(
                                new LinkedHashMap<>(binding));
                        continue;
                    }
                    if (!"CALL_ARGUMENT".equals(captureKind)) {
                        refined.captureBindingsComplete = false;
                        refined.runtimeRefinementComplete = false;
                        refined.captureBindingIssues.add(
                                "UNSUPPORTED_OUTPUT_CAPTURE_KIND:"
                                        + captureKind);
                        continue;
                    }

                    String caller = string(binding.get("callerMethod"));
                    if (!observed.contains(caller)) {
                        continue;
                    }
                    List<RuntimeEvent> matches = evidence
                            .matchingCallArguments(binding);
                    for (int index = 0; index < matches.size(); index++) {
                        Map<String, Object> exact =
                                new LinkedHashMap<>(binding);
                        exact.put("occurrence", index + 1);
                        refined.captureBindings.add(exact);
                        matchedCaptureCount++;
                    }
                }
                if (!exitFieldRequested && matchedCaptureCount != 1) {
                    refined.captureBindingsComplete = false;
                    refined.runtimeRefinementComplete = false;
                    String failure;
                    if (matchedCaptureCount == 0) {
                        failure = "NO_RUNTIME_EXACT_CALL_ARGUMENT_MATCH";
                    } else {
                        failure = "AMBIGUOUS_RUNTIME_CALL_ARGUMENT_MATCH:"
                                + matchedCaptureCount;
                    }
                    refined.captureBindingIssues.add(failure);
                }
            }
        }

        /**
         * A scalar/reference field output is read once from its exact
         * receiver path at normal region exit. This directly observes the
         * final symbolic heap state, so assignment sites and seed-path write
         * occurrences are not capture identities.
         */
        private void validateNormalExitFieldCapture(
                StaticPort input, List<Map<String, Object>> actions) {
            if (captureBindings.isEmpty()) {
                return;
            }
            for (Map<String, Object> capture : captureBindings) {
                if (!"REGION_EXIT_FIELD".equals(
                        string(capture.get("captureKind")))) {
                    return;
                }
            }
            FieldCell field = fieldCell(outputCell);
            Map<String, Object> action = captureDischargeAction(actions,
                    input == null ? "" : input.portId);
            Map<String, Object> request = captureBindings.size() == 1
                    ? captureBindings.get(0) : null;
            List<String> exactPath = action == null
                    ? Collections.<String>emptyList()
                    : stringList(action.get("fieldPath"));
            List<String> declaredPath = request == null
                    ? Collections.<String>emptyList()
                    : stringList(request.get("fieldPath"));
            boolean supported = field.declaredSignature
                    && !isArrayJavaType(field.type)
                    && !supportedMapStateCell(outputCell)
                    && input != null
                    && action != null && request != null
                    && input.portId.equals(string(request.get(
                    "accessRootInputPort")))
                    && outputCell.equals(string(request.get(
                    "fieldSignature")))
                    && field.type.equals(string(request.get("javaType")))
                    && field.type.replace('/', '.').equals(
                    string(action.get("javaType")).replace('/', '.'))
                    && !declaredPath.isEmpty() && !exactPath.isEmpty()
                    && declaredPath.get(declaredPath.size() - 1).equals(
                    exactPath.get(exactPath.size() - 1));
            if (!supported || !captureBindingsComplete
                    || !captureBindingIssues.isEmpty()
                    || requestedStateTransformerContractPresent
                    && !requestedStateTransformerContractComplete) {
                captureBindingsComplete = false;
                runtimeRefinementComplete = false;
                captureBindingIssues.add(
                        "NORMAL_EXIT_FIELD_PATH_CAPTURE_NOT_PROVEN");
                return;
            }
            request.put("fieldPath", new ArrayList<>(exactPath));
            captureBindingIssues.clear();
        }

        private Map<String, Object> captureDischargeAction(
                List<Map<String, Object>> actions, String inputPort) {
            Map<String, Object> match = null;
            for (Map<String, Object> action : actions) {
                if (!inputPort.equals(string(action.get("symbol")))
                        || !outputCell.equals(string(action.get("cell")))
                        || !"HEAP_PRESTATE".equals(string(action.get(
                        "sourceKind")))
                        || !"RECEIVER_FIELD".equals(string(action.get(
                        "location")))
                        || !"RUNTIME_UNIQUE_ROOT_TO_OUTPUT_OWNER_FIELD_PATH"
                        .equals(string(action.get(
                                "frameConditionAuthority")))
                        || !outputCell.equals(string(action.get(
                                "leafFieldSignature")))
                        || stringList(action.get("fieldPath")).isEmpty()) {
                    continue;
                }
                if (match != null) {
                    return null;
                }
                match = action;
            }
            return match;
        }

        private boolean mutationCaptureDischargeReady(
                StaticOutputSlice refined, InstanceEvidence evidence,
                Set<String> observed, String heapEffectCaptureInput) {
            if (captureBindingsComplete
                    || heapEffectCaptureInput.isEmpty()
                    || !evidence.runtimePathEvidenceComplete
                    || !refined.structuralComplete
                    || !refined.runtimeRefinementComplete
                    || !refined.inputGaps.isEmpty()
                    || !refined.requestedStateTransformerContractComplete) {
                return false;
            }

            // A retained exact capture is authoritative and must not be
            // replaced by heap effects.  Capture declarations belonging only
            // to methods excluded as static alternatives are irrelevant to
            // this concrete runtime path.
            for (Map<String, Object> binding : captureBindings) {
                String method = string(binding.get("callerMethod"));
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
                    "REQUESTED_TRANSFORMER_HAS_NO_FINAL_STATE_CAPTURE:";
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
                    "captureBindingsComplete", captureBindingsComplete,
                    "captureDischargedByHeapEffectTransformer",
                    captureDischargedByHeapEffectTransformer,
                    "captureDischargeInputPort",
                    captureDischargeInputPort,
                    "captureDischargeAuthority",
                    captureDischargeAuthority,
                    "containerElementFieldBindings",
                    containerElementFieldBindings,
                    "inputGaps", inputGaps,
                    "truncationReasons", structuralIssues,
                    "complete", complete);
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
        private final String javaType;
        private final MaterializationSpec materialization;

        private StaticPort(String portId, String cell, String sourceKind,
                           String projection, String kind, String javaType,
                           MaterializationSpec materialization) {
            this.portId = safe(portId);
            this.cell = safe(cell);
            this.sourceKind = safe(sourceKind);
            this.projection = safe(projection);
            this.kind = safe(kind);
            this.javaType = safe(javaType);
            this.materialization = materialization == null
                    ? MaterializationSpec.none() : materialization;
        }
    }

    private static final class FramePrestatePath {
        private final FieldCell field;
        private final List<String> path;

        private FramePrestatePath(FieldCell field, List<String> path) {
            this.field = field;
            this.path = new ArrayList<>(path);
        }

        private static FramePrestatePath incomplete() {
            return new FramePrestatePath(FieldCell.unresolved(),
                    Collections.<String>emptyList());
        }

        private boolean complete() {
            return field.declaredSignature && !path.isEmpty();
        }
    }

    private static final class ObjectPathState {
        private final int objectId;
        private final List<String> path;
        private final Set<Integer> visited;

        private ObjectPathState(int objectId, List<String> path,
                                Set<Integer> visited) {
            this.objectId = objectId;
            this.path = new ArrayList<>(path);
            this.visited = new LinkedHashSet<>(visited);
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
        DeclaredField declared = FieldPathSpec.declaredField(cell);
        if (declared != null) {
            return new FieldCell(declared.owner(), declared.type(),
                    declared.name(), true);
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
        DeclaredField field = FieldPathSpec.declaredField(value);
        return field != null && field.signature().equals(safe(value));
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

    private static <T> List<T> sorted(List<T> values,
                                      ToLongFunction<T> sequence) {
        List<T> result = new ArrayList<>();
        if (values != null) {
            result.addAll(values);
        }
        result.sort(Comparator.comparingLong(sequence));
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

    private static void copy(Map<String, Object> from, Map<String, Object> to,
                             String... keys) {
        for (String key : keys) {
            if (from.containsKey(key)) to.put(key, from.get(key));
        }
    }

    private static Map<String, Object> jsonMap(JsonObject source) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (Map.Entry<String, JsonElement> entry : source.entrySet()) {
            result.put(entry.getKey(), jsonValue(entry.getValue()));
        }
        return result;
    }

    private static Object jsonValue(JsonElement value) {
        if (value == null || value.isJsonNull()) return null;
        if (value.isJsonObject()) return jsonMap(value.getAsJsonObject());
        if (value.isJsonArray()) {
            List<Object> result = new ArrayList<>();
            for (JsonElement element : value.getAsJsonArray()) {
                result.add(jsonValue(element));
            }
            return result;
        }
        if (value.getAsJsonPrimitive().isBoolean()) {
            return value.getAsBoolean();
        }
        if (value.getAsJsonPrimitive().isString()) {
            return value.getAsString();
        }
        String number = value.getAsString();
        try {
            return Long.valueOf(number);
        } catch (NumberFormatException notIntegral) {
            return new java.math.BigDecimal(number);
        }
    }

    private static String jsonl(List<Map<String, Object>> rows) {
        StringBuilder builder = new StringBuilder();
        for (Map<String, Object> row : rows) {
            builder.append(json(row)).append('\n');
        }
        return builder.toString();
    }

    private static String json(Object value) {
        return GSON.toJson(value);
    }

    private static JsonObject parseJsonObject(String json) {
        JsonElement parsed = JsonParser.parseString(json);
        if (!parsed.isJsonObject()) {
            throw new IllegalArgumentException("JSONL row must be an object");
        }
        return parsed.getAsJsonObject();
    }

    private static String jsonString(JsonObject json, String field) {
        JsonElement value = json.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isString()
                ? value.getAsString() : "";
    }

    private static boolean jsonHasField(JsonObject json, String field) {
        return json.has(field);
    }

    private static boolean staticDataflowAssertable(JsonObject json) {
        return jsonInt(json, "schemaVersion", -1)
                == STATIC_DATAFLOW_EDGE_SCHEMA_VERSION
                && STATIC_DATAFLOW_ASSERTABLE.equals(
                jsonString(json, "semanticMode"));
    }

    private static boolean jsonBoolean(JsonObject json, String field,
                                       boolean fallback) {
        Boolean value = jsonOptionalBoolean(json, field);
        return value == null ? fallback : value;
    }

    private static Boolean jsonOptionalBoolean(JsonObject json,
                                                String field) {
        JsonElement value = json.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean()
                ? value.getAsBoolean() : null;
    }

    private static int jsonInt(JsonObject json, String field, int fallback) {
        JsonElement value = json.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isNumber()
                ? value.getAsInt() : fallback;
    }

    private static List<String> jsonStringArray(JsonObject json,
                                                String field) {
        JsonArray values = jsonArray(json, field);
        if (values == null) {
            return Collections.emptyList();
        }
        List<String> result = new ArrayList<>();
        for (JsonElement value : values) {
            if (value.isJsonPrimitive()
                    && value.getAsJsonPrimitive().isString()) {
                result.add(value.getAsString());
            }
        }
        return result;
    }

    private static List<Integer> jsonIntArray(JsonObject json,
                                              String field) {
        JsonArray values = jsonArray(json, field);
        if (values == null) {
            return Collections.emptyList();
        }
        List<Integer> result = new ArrayList<>();
        for (JsonElement value : values) {
            if (value.isJsonPrimitive()
                    && value.getAsJsonPrimitive().isNumber()) {
                result.add(value.getAsInt());
            }
        }
        return result;
    }

    private static List<JsonObject> jsonObjectArray(JsonObject json,
                                                    String field) {
        JsonArray values = jsonArray(json, field);
        if (values == null) {
            return Collections.emptyList();
        }
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement value : values) {
            if (value.isJsonObject()) {
                result.add(value.getAsJsonObject());
            }
        }
        return result;
    }

    private static JsonArray jsonArray(JsonObject json, String field) {
        JsonElement value = json.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : null;
    }
}
