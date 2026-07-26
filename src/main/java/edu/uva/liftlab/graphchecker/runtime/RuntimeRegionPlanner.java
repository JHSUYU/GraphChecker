package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.SymbolicEnvironment;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;

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

        int instanceIndex = 0;
        Map<String, List<InstanceEvidence>> evidenceByRegion = new LinkedHashMap<>();
        Map<String, List<InstanceEvidence>> sharedStateEvidenceByRegion =
                new LinkedHashMap<>();
        List<InstanceEvidence> allInstanceEvidence = new ArrayList<>();

        outer:
        for (StaticRegion region : regions) {
            List<MethodEvent> roots = rootCandidates(region,
                    values(regionsByAnchor.get(region.anchorMethod)),
                    trace.methodsBySignature, trace.methodsByCall);
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
                        trace);

                InstanceEvidence instanceEvidence = new InstanceEvidence(
                        instanceId, region, root, containedCalls,
                        containedRuntime, containedFields, observedMethods,
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
                relationEvidence);
        Map<String, RegionPlanDraft> planDrafts = buildRegionPlans(
                allInstanceEvidence, trace, rootArgumentRuntimeTypes);

        List<UpstreamEdgeBinding> edgeBindings = new ArrayList<>();
        validateRegionEdges(regionEdges, evidenceByRegion,
                sharedStateEvidenceByRegion, result,
                edgeBindings, relationEvidence);
        attachOutputRelationGoals(edgeBindings, planDrafts);
        for (RegionPlanDraft plan : planDrafts.values()) {
            if (!plan.goals.isEmpty()) {
                plan.stripPlannerEvidence();
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

        if (!roots.isEmpty() || !anchors.isEmpty()) {
            return roots;
        }

        // Pure producer regions can have no observed target anchor. In that
        // case the exact static root entry is the runtime output invocation.
        for (MethodEvent event : values(methodsBySignature.get(
                region.rootMethod))) {
            if (selectedCalls.add(event.callId)) roots.add(event);
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
            if ("BRANCH".equals(event.kind) && event.outcome != null
                    && ++total > MAX_PATH_SIGNATURE_EVENTS) {
                return true;
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
            MethodEvent root, List<FieldAccessEvent> fields,
            RuntimeTraceIndex trace) {
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
                RuntimeEvent argument = trace.methodArgument(root.callId,
                        parameter);
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
                        trace);
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
                        if (protocolFieldRequiresExactSite) {
                            observation.put("bindingMode", "FIELD_ACCESS");
                        }
                        if (runtimeExactSite) {
                            observation.put("accessMethod", field.method);
                            observation.put("accessUnitIndex", field.unitIndex);
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
                || !RuntimeTraceIndex.exactRuntimeFieldSite(selected)) {
            return false;
        }
        int exactReadCount = 0;
        FieldAccessEvent only = null;
        for (FieldAccessEvent field : values(fields)) {
            FieldCell actual = fieldCell(field.field);
            if (!"FIELD_READ".equals(field.kind)
                    || field.callId == root.callId
                    || field.receiverObjectId == 0
                    || !RuntimeTraceIndex.exactRuntimeFieldSite(field)
                    || !actual.declaredSignature
                    || !expected.signature().equals(actual.signature())) {
                continue;
            }
            exactReadCount++;
            only = field;
        }
        return exactReadCount == 1 && only == selected;
    }

    private static FieldAccessEvent matchingField(List<FieldAccessEvent> fields,
                                                   StaticPort port,
                                                   MethodEvent root,
                                                   RuntimeTraceIndex trace) {
        FieldCell expected = fieldCell(port.cell);
        if (!expected.materializable()) {
            return null;
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
                    || !accessSiteId.equals(field.siteId))) {
                continue;
            }
            String accessorCallerMethod = port.materialization.method();
            String accessorCallSiteId = port.materialization.siteId();
            String accessorDeclaredCallee =
                    port.materialization.declaredCallee();
            String accessorImplementationMethod =
                    port.materialization.implementationMethod();
            boolean accessorConstrained = port.materialization.kind()
                    == MaterializationSpec.Kind.ACCESSOR_RETURN;
            if (accessorConstrained) {
                MethodEvent fieldMethod = trace.methodsByCall.get(
                        field.callId);
                RuntimeEvent parentSite = fieldMethod == null ? null
                        : trace.callSitesByInvocation.get(
                        fieldMethod.parentSiteId);
                if (parentSite == null
                        || !accessorCallerMethod.equals(parentSite.method)
                        || !accessorCallSiteId.equals(parentSite.siteId)
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
                    "fieldEventSeq",
                    "accessMethod", "accessUnitIndex",
                    "accessorInvocationId", "accessorRuntimeType",
                    "fieldPath", "leafFieldSignature",
                    "receiverObjectId");
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
                    action.put("javaType", exact.type);
                    action.put("accessFieldSignature", exact.signature());
                    if (port.cell.equals(exact.signature())
                            && stringList(action.get("fieldPath")).isEmpty()) {
                        action.put("fieldPath", Collections.singletonList(
                                exact.name));
                        action.put("leafFieldSignature", exact.signature());
                    }
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
                List<String> fields = observedArgumentFields(region,
                        objectId, runtimeEvents);
                if (!fields.isEmpty()) {
                    List<List<String>> paths = new ArrayList<>();
                    for (String field : fields) {
                        paths.add(Collections.singletonList(field));
                    }
                    action.put("location", "ARGUMENT_FIELD_PATH");
                    action.put("fieldPaths", paths);
                    action.put("materializationMode",
                            "SELECTIVE_FIELD_PATHS");
                } else {
                    action.put("materializationMode", "RECURSIVE_OBJECT");
                }
            }
            result.add(action);
        }
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
        action.put("accessFieldSignature", staticRoot.signature());
        action.put("leafFieldSignature", leaf.signature());
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
                "fieldSignature", leaf.signature()));
        action.put("fieldPathLeafDeclarations", declarations);
    }

    private static List<String> observedArgumentFields(
            StaticRegion region, int argumentObjectId,
            List<RuntimeEvent> runtimeEvents) {
        if (argumentObjectId == 0) {
            return Collections.emptyList();
        }
        Set<String> fields = new LinkedHashSet<>();

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

    private static boolean isArrayJavaType(String type) {
        String value = safe(type).trim();
        return value.startsWith("[") || value.endsWith("[]");
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
                    && (event.successorIndex == null
                    || !policy.branchKind.equals(event.branchKind))) {
                event = null;
            }
            Boolean observedOutcome = event == null ? null : event.outcome;
            Integer observedSuccessor = event == null
                    ? null : event.successorIndex;
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
                        "outcome", occurrence.outcome));
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
            if (occurrence.successorIndex != null
                    && requiredSuccessorIndices != null
                    && requiredSuccessorIndices.contains(
                    occurrence.successorIndex)) {
                return occurrence;
            }
            if (requiredOutcome != null
                    && requiredOutcome.equals(occurrence.outcome)) {
                return occurrence;
            }
        }
        return selected;
    }

    private static void validateRegionEdges(
            List<StaticRegionEdge> staticEdges,
            Map<String, List<InstanceEvidence>> evidenceByRegion,
            Map<String, List<InstanceEvidence>> sharedStateEvidenceByRegion,
            Result result, List<UpstreamEdgeBinding> edgeBindings,
            RuntimeRelationEvidenceCache relationEvidence) {
        for (StaticRegionEdge edge : staticEdges) {
            Map<String, List<InstanceEvidence>> selectedEvidence =
                    "SHARED_STATE".equals(edge.kind)
                            ? sharedStateEvidenceByRegion : evidenceByRegion;
            List<InstanceEvidence> upstreamInstances = values(
                    selectedEvidence.get(edge.fromRegion));
            List<InstanceEvidence> downstreamInstances = values(
                    selectedEvidence.get(edge.toRegion));
            boolean endpointObserved = false;
            boolean orderedObserved = false;
            boolean readFromObserved = false;
            boolean valueEqualityObserved = false;
            boolean demandPruned = false;
            List<Map<String, Object>> validatedBindings = new ArrayList<>();
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
                            downstream.resolveConsumerInput(edge.toPort);
                    if (retainedInputResolution == null) {
                        demandPruned = true;
                        continue;
                    }
                    endpointObserved = true;
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
                        orderedObserved = true;
                    }
                    if (readFrom != null) {
                        readFromObserved = true;
                        if (edge.producerOutputFor(upstream.region) != null) {
                            edgeBindings.add(new UpstreamEdgeBinding(edge,
                                    upstream, downstream, readFrom));
                        }
                    }
                    valueEqualityObserved |= !valueMatches.isEmpty();
                    Map<String, Object> row = object(
                            "fromRegionInstance", upstream.instanceId,
                            "toRegionInstance", downstream.instanceId);
                    if (readFrom != null) {
                        addReadFromEvidence(row, readFrom);
                    } else if (valueMatch != null) {
                        addValueEqualityEvidence(row, valueMatch);
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
                        addValueEqualityEvidence(additionalRow, additional);
                        validatedBindings.add(additionalRow);
                    }
                }
            }

            String state;
            if ("SHARED_STATE".equals(edge.kind)) {
                if (readFromObserved) {
                    state = "CONFIRMED_READ_FROM";
                } else if (demandPruned && !endpointObserved) {
                    state = "PRUNED_BY_CONCRETE_DEMAND_SLICE";
                } else if (endpointObserved) {
                    state = "UNCONFIRMED_READ_FROM";
                } else {
                    state = "UNOBSERVED";
                }
            } else if (demandPruned && !endpointObserved) {
                state = "PRUNED_BY_CONCRETE_DEMAND_SLICE";
            } else if (!endpointObserved) {
                state = "UNOBSERVED";
            } else if (valueEqualityObserved) {
                state = "CONFIRMED_RUNTIME_VALUE_EQUALITY";
            } else if (orderedObserved) {
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
            if (edge.canonicalAliasValid()) {
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
            Map<String, Object> target, FingerprintMatch match) {
        target.put("evidenceKind", "COMPLETE_VALUE_EQUALITY_V1");
        target.put("writerEventSeq", match.from.seq);
        target.put("readerEventSeq", match.to.seq);
        target.put("valueFingerprint", match.from.digest);
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
                            .resolveExternalCandidateInput(edge.toPort);
                    if (resolution == null) {
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
                    concreteInputs, instance.root, instance.fieldEvents,
                    trace);
            List<Map<String, Object>> symbolize = symbolizeActions(
                    instance.region, concreteInputs, instance.root,
                    inputObjects, instance.runtimeEvents,
                    instance.fieldEvents);
            List<Map<String, Object>> branches = branchActions(
                    instance.region, instance.runtimeEvents);
            boolean symbolicPotential = !concreteInputs.isEmpty()
                    || instance.region.inputs.isEmpty()
                    || instance.region.branches.isEmpty();
            boolean replayable = instance.anchorObserved
                    && instance.runtimePathEvidenceComplete;
            boolean ready = replayable && symbolicPotential
                    && instance.region.inputSelectionComplete
                    && symbolizeActionsReady(symbolize)
                    && branchActionsReady(branches);
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
                    admission(replayable, ready,
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
    private static void attachOutputRelationGoals(
            List<UpstreamEdgeBinding> bindings,
            Map<String, RegionPlanDraft> plansByInstance) {
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
                            binding.edge.toPort);
            if (inputResolution == null) {
                continue;
            }
            binding.downstreamInput = inputResolution.port;
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
            } else {
                outputGoal.put("symbolize", Collections.emptyList());
                outputGoal.put("branches", Collections.emptyList());
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
        StaticPort input = first.upstream.region.exactInputFor(
                first.output.cell);
        outputSlice.validateNormalExitFieldCapture(input, selectedInputs);
        Set<String> outputBranchSites = new LinkedHashSet<>(
                outputSlice.staticSites);
        outputBranchSites.addAll(outputSlice.sites);
        List<Map<String, Object>> selectedBranches = selectActivationRows(
                base.branches, outputBranchSites, "siteId");
        boolean inputsReady = symbolizeActionsReady(selectedInputs);
        boolean sliceReady = outputSlice.complete
                && outputSlice.captureBindingIssues.isEmpty()
                && inputSelectionComplete
                && inputsReady;
        if (!sliceReady) {
            List<String> causes = new ArrayList<>();
            if (!outputSlice.complete) {
                causes.add("STATIC_SLICE_INCOMPLETE");
            }
            if (!outputSlice.captureBindingIssues.isEmpty()) {
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
            if (!inputsReady) {
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
            return new UpstreamOutputMemberPlan(first.output, outputSlice,
                    selectedInputs, selectedBranches, null,
                    "OUTPUT_MEMBER_INCOMPLETE:" + first.output.portId
                            + ":" + String.join(",", causes));
        }

        final OutputClosureContract contract;
        try {
            contract = OutputClosureCodec.singleton(
                    first.upstream.region.regionId,
                    first.upstream.instanceId, first.upstream.root.callId,
                    first.output.portId, first.output.cell, first.output.kind,
                    first.output.javaType,
                    GSON.toJsonTree(outputSlice.toMap()).getAsJsonObject());
        } catch (RuntimeException malformed) {
            return new UpstreamOutputMemberPlan(first.output, outputSlice,
                    selectedInputs, selectedBranches, null,
                    "OUTPUT_MEMBER_CONTRACT_INVALID:"
                            + first.output.portId + ":"
                            + safe(malformed.getMessage()));
        }
        return new UpstreamOutputMemberPlan(first.output, outputSlice,
                selectedInputs, selectedBranches, contract, "");
    }

    private static boolean mergeOutputGoalExecution(
            Map<String, Object> goal,
            List<UpstreamOutputMemberPlan> members, List<String> issues) {
        Map<String, Map<String, Object>> inputs = new LinkedHashMap<>();
        Map<String, Map<String, Object>> branches = new LinkedHashMap<>();
        for (UpstreamOutputMemberPlan member : members) {
            mergeExactRows(inputs, member.selectedInputs, "symbol",
                    "SYMBOLIZE_ACTION", issues);
            mergeExactRows(branches, member.selectedBranches, "siteId",
                    "BRANCH_ACTION", issues);
        }
        if (!issues.isEmpty()) return false;
        goal.put("symbolize", new ArrayList<>(inputs.values()));
        goal.put("branches", new ArrayList<>(branches.values()));
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
        private final OutputClosureContract contract;
        private final String issue;

        private UpstreamOutputMemberPlan(
                StaticPort output, StaticOutputSlice outputSlice,
                List<Map<String, Object>> selectedInputs,
                List<Map<String, Object>> selectedBranches,
                OutputClosureContract contract, String issue) {
            this.output = output;
            this.outputSlice = outputSlice;
            this.selectedInputs = selectedInputs;
            this.selectedBranches = selectedBranches;
            this.contract = contract;
            this.issue = issue;
        }

        private static UpstreamOutputMemberPlan failed(
                StaticPort output, String issue) {
            return new UpstreamOutputMemberPlan(output, null,
                    Collections.<Map<String, Object>>emptyList(),
                    Collections.<Map<String, Object>>emptyList(),
                    null, issue);
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

        private void stripPlannerEvidence() {
            for (Map<String, Object> goal : goals) {
                for (Map<String, Object> action : mapRows(
                        goal.get("symbolize"))) {
                    action.remove("fieldEventSeq");
                }
            }
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
            action.put("fieldPaths", paths);
            action.put("materializationMode", "SELECTIVE_FIELD_PATHS");
            Map<String, String> declared = leafDeclarationsByPort.get(symbol);
            if (paths.size() == 1 && declared != null) {
                String signature = declared.get(joinPath(paths.get(0)));
                FieldCell leaf = fieldCell(signature);
                if (leaf.declaredSignature) {
                    List<Map<String, Object>> rows = new ArrayList<>();
                    rows.add(object("fieldPath", paths.get(0),
                            "fieldSignature", signature));
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
        List<JsonObject> rows = readArtifactRows(file,
                "frozen static graph", true);
        for (JsonObject row : rows) {
            StaticDataflowProjectionEdge edge =
                    StaticDataflowProjectionEdge.fromJson(row);
            if (edge == null || edge.edgeId.isEmpty()
                    || result.byId.containsKey(edge.edgeId)) {
                throw new IllegalArgumentException(
                        "malformed or duplicate frozen static graph edge");
            }
            result.add(edge, StaticOutputSlice.causalEdgeReference(row));
        }
        if (rows.isEmpty()) {
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
        for (JsonObject row : readArtifactRows(file,
                "symbolic region artifact", true)) {
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
        return result;
    }

    private static List<StaticRegionEdge> readRegionEdges(File file) {
        List<StaticRegionEdge> result = new ArrayList<>();
        for (JsonObject row : readArtifactRows(file,
                "symbolic region edge artifact", false)) {
            StaticRegionEdge edge = StaticRegionEdge.fromJson(row);
            if (edge.edgeId.isEmpty() || edge.fromRegion.isEmpty()
                    || edge.toRegion.isEmpty()) {
                throw new IllegalArgumentException(
                        "malformed symbolic region edge row");
            }
            result.add(edge);
        }
        return result;
    }

    private static List<JsonObject> readArtifactRows(
            File file, String label, boolean required) {
        if (file == null) {
            if (required) {
                throw new IllegalArgumentException(label + " is required");
            }
            return Collections.emptyList();
        }
        if (!file.isFile()) {
            throw new IllegalArgumentException(label + " is missing: "
                    + file);
        }
        List<JsonObject> result = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(file.toPath(),
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                JsonObject row = GSON.fromJson(line, JsonObject.class);
                if (row == null) {
                    throw new IllegalArgumentException(
                            label + " row must be an object");
                }
                result.add(row);
            }
        } catch (IOException exception) {
            throw new IllegalStateException("failed to read " + label
                    + ": " + file, exception);
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
        final Boolean outcome;
        final String valueFingerprint;
        final boolean valueFingerprintComplete;
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
                    primitiveValue, hasOutcome ? outcome : null, "", false,
                    null, "", "");
        }

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     String declaredCallee, int argumentIndex,
                     String runtimeType, int objectId,
                     String primitiveValue, boolean hasOutcome,
                     boolean outcome) {
            this(seq, kind, method, callId, invocationId, parentSiteId,
                    siteId, declaredCallee, argumentIndex, runtimeType,
                    objectId, primitiveValue,
                    hasOutcome ? outcome : null, "", false,
                    null, "", "");
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
                    objectId, primitiveValue,
                    hasOutcome ? outcome : null,
                    valueFingerprint, valueFingerprintComplete,
                    null, "", "");
        }

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, long parentSiteId, String siteId,
                     String declaredCallee, int argumentIndex,
                     String runtimeType, int objectId,
                     String primitiveValue, Boolean outcome,
                     String valueFingerprint,
                     boolean valueFingerprintComplete,
                     Integer successorIndex,
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
            this.outcome = outcome;
            this.valueFingerprint = safe(valueFingerprint);
            this.valueFingerprintComplete = valueFingerprintComplete;
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
            this.siteId = unitIndex >= 0 && !this.method.isEmpty()
                    ? this.method + "#u" + unitIndex : safe(siteId);
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
        private final Map<String, List<FieldAccessEvent>> fieldReadsBySite =
                new LinkedHashMap<>();
        private final Map<String, List<FieldAccessEvent>> writesByContext =
                new LinkedHashMap<>();
        private final Map<String, List<FieldAccessEvent>> unscopedWrites =
                new LinkedHashMap<>();
        private final Map<Integer, List<RuntimeEvent>> mutatorsByObject =
                new LinkedHashMap<>();
        private final Map<Long, RuntimeEvent> callSitesByInvocation =
                new LinkedHashMap<>();
        private final Map<Long, RuntimeEvent> completionsByInvocation =
                new LinkedHashMap<>();
        private final Map<Long, Map<Integer, RuntimeEvent>>
                methodArgumentsByCall = new LinkedHashMap<>();
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
                        && event.invocationId > 0L) {
                    result.callSitesByInvocation.putIfAbsent(
                            event.invocationId, event);
                    if (event.objectId != 0
                            && isContainerMutator(event.declaredCallee)) {
                        result.mutatorsByObject.computeIfAbsent(
                                event.objectId,
                                ignored -> new ArrayList<>()).add(event);
                    }
                } else if ("CALL_SITE_RETURN".equals(event.kind)
                        && event.invocationId > 0L) {
                    result.completionsByInvocation.putIfAbsent(
                            event.invocationId, event);
                } else if ("METHOD_ARGUMENT".equals(event.kind)
                        && event.argumentIndex >= 0) {
                    result.methodArgumentsByCall.computeIfAbsent(
                            event.callId, ignored -> new LinkedHashMap<>())
                            .putIfAbsent(event.argumentIndex, event);
                }
            }
            for (FieldAccessEvent event : values(fields)) {
                result.fieldsByCall.computeIfAbsent(event.callId,
                        ignored -> new ArrayList<>()).add(event);
                String field = exactFieldKey(event.field);
                if (!field.isEmpty() && event.receiverObjectId != 0) {
                    add(result.fieldEventsByReceiver,
                            receiverFieldKey(event.receiverObjectId, field),
                            event);
                    if ("FIELD_READ".equals(event.kind)) {
                        add(result.fieldReadsByField, field, event);
                    }
                }
                if (!field.isEmpty() && "FIELD_READ".equals(event.kind)
                        && exactRuntimeFieldSite(event)) {
                    add(result.fieldReadsBySite, fieldSiteKey(event.method,
                            event.siteId, event.unitIndex, field), event);
                } else if (!field.isEmpty()
                        && "FIELD_WRITE".equals(event.kind)) {
                    MethodEvent call = result.methodsByCall.get(event.callId);
                    if (call == null) {
                        add(result.unscopedWrites, receiverFieldKey(
                                event.receiverObjectId, field), event);
                    } else {
                        add(result.writesByContext, contextFieldKey(
                                call.test, call.process,
                                event.receiverObjectId, field), event);
                    }
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
            String key = exactFieldKey(field.signature());
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

        private RuntimeEvent methodArgument(long callId, int index) {
            Map<Integer, RuntimeEvent> arguments =
                    methodArgumentsByCall.get(callId);
            return arguments == null ? null : arguments.get(index);
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
            for (FieldAccessEvent event : values(fieldReadsBySite.get(
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
        private StaticPort outputFor(String endpoint) {
            return portFor(outputs, endpoint, true);
        }

        private ConsumerInputResolution resolveConsumerInput(
                String endpoint, Set<String> retainedPortIds) {
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
                return new ConsumerInputResolution(exact);
            }
            return null;
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
            region.inputSelectionComplete = jsonBoolean(json,
                    "inputSelectionComplete", true);
            return region;
        }
    }

    private static final class ConsumerInputResolution {
        private final StaticPort port;

        private ConsumerInputResolution(StaticPort port) {
            this.port = port;
        }
    }

    private static final class StaticProjectionIndex {
        private final Map<String, StaticDataflowProjectionEdge> byId =
                new LinkedHashMap<>();
        private final Map<String, Map<String, Object>> causalReferencesById =
                new LinkedHashMap<>();
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

        /**
         * Re-slices the frozen graph after runtime has selected one concrete
         * same-thread root call tree.  This is intentionally a graph-index
         * operation, not a second Soot execution.
         */
        private ConcreteDemandSlice reslice(StaticRegion region,
                boolean runtimePathEvidenceComplete,
                Set<String> observedMethods, String runtimeRootMethod,
                MethodEvent runtimeRoot, Set<Long> containedCalls,
                RuntimeTraceIndex trace) {
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
                                trace.reachingDefinition(
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

    private static final class StaticDataflowProjectionEdge {
        private final String edgeId;
        private final String transferKind;
        private final String relation;
        private final boolean assertable;
        private final String fromCell;
        private final String toCell;
        private final String method;
        private final String siteId;
        private final int unitIndex;

        private StaticDataflowProjectionEdge(String edgeId,
                String transferKind, String relation, boolean assertable,
                String fromCell, String toCell, String method,
                String siteId, int unitIndex) {
            this.edgeId = safe(edgeId);
            this.transferKind = safe(transferKind);
            this.relation = safe(relation);
            this.assertable = assertable;
            this.fromCell = safe(fromCell);
            this.toCell = safe(toCell);
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
                    jsonString(json, "transferKind"),
                    jsonString(json, "relation"),
                    staticDataflowAssertable(json),
                    jsonString(json, "fromCell"),
                    jsonString(json, "toCell"),
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
            return edge;
        }

        private String producerOutputEndpoint() {
            return canonicalAliasValid() ? fromOutputPort
                    : "SHARED_STATE".equals(kind) ? fromPort : "";
        }

        private String sourceFingerprintEndpoint(StaticRegion region) {
            if (producerOutputFor(region) == null) {
                return "";
            }
            return canonicalAliasValid() ? fromOutputCell : fromPort;
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
            if (!canonicalAliasValid()) {
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
        private final List<RuntimeEvent> runtimeEvents;
        private final List<FieldAccessEvent> fieldEvents;
        private final Set<String> observedMethods;
        private final boolean anchorObserved;
        private final Set<String> concreteInputPortIds;
        private final ConcreteDemandSlice concreteDemandSlice;
        private final boolean runtimePathEvidenceComplete;
        private final boolean containedCallTreeComplete;

        private InstanceEvidence(String instanceId, StaticRegion region,
                                 MethodEvent root, Set<Long> calls,
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
            return true;
        }

        private ConsumerInputResolution resolveExternalCandidateInput(
                String endpoint) {
            return region.resolveConsumerInput(endpoint, null);
        }

        private ConsumerInputResolution resolveConsumerInput(
                String endpoint) {
            return region.resolveConsumerInput(endpoint,
                    concreteInputPortIds);
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
            result.put("aliasProofEdgeIds",
                    new ArrayList<>(edge.aliasProofEdgeIds));
            result.put("aliasProofAuthority", edge.aliasProofAuthority);
            result.put("aliasProofComplete", edge.aliasProofComplete);
            return result;
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
        private final List<Map<String, Object>> captureBindings =
                new ArrayList<>();
        private final List<String> captureBindingIssues = new ArrayList<>();
        private final List<Map<String, Object>> inputGaps =
                new ArrayList<>();
        private boolean runtimeRefinementComplete = true;
        private final Set<String> staticSites = new LinkedHashSet<>();

        private static final class FieldPathRuntimeCandidate {
            private final String portId;
            private final List<String> path;
            private final String leafFieldSignature;
            private final String accessMethod;
            private final FieldAccessEvent event;

            private FieldPathRuntimeCandidate(
                    StaticPort port, Collection<String> path,
                    String leafFieldSignature, String accessMethod,
                    FieldAccessEvent event) {
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
            for (JsonObject binding : jsonObjectArray(json,
                    "captureBindings")) {
                slice.captureBindings.add(jsonMap(binding));
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
            refined.captureBindingIssues.addAll(captureBindingIssues);
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

            collapseRuntimeConfirmedFieldPathAliases(evidence,
                    retainedBindings);
            retainedPorts.clear();
            for (Map<String, Object> binding : retainedBindings) {
                String port = string(binding.get("inputPort"));
                if (!port.isEmpty()) {
                    retainedPorts.add(port);
                }
            }
            refined.inputBindings.addAll(retainedBindings);
            refined.inputPorts.addAll(sorted(retainedPorts));

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
            for (Map<String, Object> binding : captureBindings) {
                refined.captureBindings.add(new LinkedHashMap<>(binding));
            }
            refined.complete = refined.structuralComplete
                    && refined.runtimeRefinementComplete
                    && refined.inputGaps.isEmpty()
                    && refined.captureBindingIssues.isEmpty();
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
                List<Map<String, Object>> retainedBindings) {
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
                remove.add(suffix.portId);
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
         * A field output is read once from its exact
         * receiver path at normal region exit. This directly observes the
         * final symbolic value or ContainerRelation, so assignment sites and
         * seed-path write occurrences are not capture identities.
         */
        private void validateNormalExitFieldCapture(
                StaticPort input, List<Map<String, Object>> actions) {
            if (captureBindings.isEmpty()) {
                return;
            }
            FieldCell field = fieldCell(outputCell);
            Map<String, Object> action = regionExitCaptureAction(actions,
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
            if (!supported || !captureBindingIssues.isEmpty()) {
                runtimeRefinementComplete = false;
                captureBindingIssues.add(
                        "NORMAL_EXIT_FIELD_PATH_CAPTURE_NOT_PROVEN");
                return;
            }
            request.put("fieldPath", new ArrayList<>(exactPath));
            captureBindingIssues.clear();
        }

        private Map<String, Object> regionExitCaptureAction(
                List<Map<String, Object>> actions, String inputPort) {
            Map<String, Object> match = null;
            for (Map<String, Object> action : actions) {
                if (!inputPort.equals(string(action.get("symbol")))
                        || !outputCell.equals(string(action.get("cell")))
                        || !"HEAP_PRESTATE".equals(string(action.get(
                        "sourceKind")))
                        || !"RECEIVER_FIELD".equals(string(action.get(
                        "location")))
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

        private Map<String, Object> toMap() {
            Map<String, Object> result = object(
                    "outputPort", outputPort,
                    "outputCell", outputCell,
                    "inputPorts", new ArrayList<>(inputPorts),
                    "inputBindings", inputBindings,
                    "methods", new ArrayList<>(methods),
                    "sites", new ArrayList<>(sites),
                    "causalEdgeIds", causalEdgeIds,
                    "causalEdges", causalEdges,
                    "captureBindings", captureBindings,
                    "captureBindingIssues", captureBindingIssues,
                    "inputGaps", inputGaps,
                    "truncationReasons", structuralIssues,
                    "complete", complete);
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
