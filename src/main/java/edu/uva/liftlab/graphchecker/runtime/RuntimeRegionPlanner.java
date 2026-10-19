package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;
import com.google.gson.ToNumberPolicy;
import edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts;
import edu.uva.liftlab.graphchecker.causynth.MapFields;
import edu.uva.liftlab.graphchecker.causynth.RecordedAccesses;
import edu.uva.liftlab.graphchecker.causynth.RecordedHeap;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.ZkChain;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.DeclaredSiteCapture;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.RuntimePlanArtifact;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.io.IOException;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.AbstractMap;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.UUID;
import java.util.function.Function;
import java.util.function.ToLongFunction;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.longNumber;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.number;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.object;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.rows;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.stringValue;

public final class RuntimeRegionPlanner {
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();
    public static final SourceRef UNREGISTERED_SOURCE = new SourceRef(
            "TEST_DRIVER", "WORKLOAD", "workload/unregistered", 0L);
    static final String COMMUNICATION_ENTRY = "COMMUNICATION_ENTRY";
    private RuntimeRegionPlanner() {
    }

    static Result planSkeletonGraph(List<StaticProgram.RegionRow> skeletons,
                                    List<MethodEvent> methods,
                                    List<RuntimeEvent> runtimeEvents,
                                    List<FieldAccessEvent> fieldEvents,
                                    List<ProtocolEvent> protocolEvents,
                                    Set<String> declaredSites,
                                    Map<String, String> fieldCalls,
                                    Map<String, Map<String, Boolean>> receiverReads) {
        TraceIndex trace = new TraceIndex(methods, runtimeEvents,
                fieldEvents, protocolEvents);
        Result result = new Result();
        result.staticRegionCount = skeletons.size();
        Set<String> skeletonRoots = new LinkedHashSet<>();
        for (StaticProgram.RegionRow skeleton : skeletons) {
            String authority = skeleton.rootAuthority;
            if ((!validRootAuthority(authority)
                    && !COMMUNICATION_ENTRY.equals(authority)
                    && !"STATE_WRITER_ENTRY".equals(authority))
                    || CausynthStaticFacts.constructor(skeleton.rootMethod)
                    && !"FAILURE_TARGET_ENTRY".equals(authority)) {
                throw new IllegalArgumentException(
                        "region skeleton has no authoritative execution "
                                + "context root: " + skeleton.rootMethod);
            }
            if (!skeletonRoots.add(skeleton.rootMethod)) {
                throw new IllegalArgumentException(
                        "duplicate region skeleton root: "
                                + skeleton.rootMethod);
            }
        }
        Map<Long, Map<String, Object>> activationByCall =
                new LinkedHashMap<>();
        Map<Long, StaticProgram.RegionRow> foldedRoots =
                new LinkedHashMap<>();
        List<PlannedRoot> plannedRoots = new ArrayList<>();
        for (boolean endpoints : new boolean[]{false, true}) {
            for (StaticProgram.RegionRow skeleton : skeletons) {
                if (endpoints != COMMUNICATION_ENTRY.equals(
                        skeleton.rootAuthority)) {
                    continue;
                }
                for (MethodEvent root : trace.methods(skeleton.rootMethod)) {
                    if (root.regionFolded) {
                        foldedRoots.put(root.callId, skeleton);
                        continue;
                    }
                    Set<String> observed = trace.methodNames(
                            trace.subtree(root.callId));
                    if (Collections.disjoint(observed,
                            skeleton.anchorMethods)) {
                        continue;
                    }
                    plannedRoots.add(new PlannedRoot(skeleton, root));
                }
            }
        }
        Set<Long> plannedRootCalls = new LinkedHashSet<>();
        for (PlannedRoot planned : plannedRoots) {
            plannedRootCalls.add(planned.root.callId);
        }
        Map<Long, Long> foldOwners = new LinkedHashMap<>();
        for (Long folded : foldedRoots.keySet()) {
            for (Long call : trace.enclosingCalls(folded)) {
                if (call.longValue() == folded.longValue()
                        || !plannedRootCalls.contains(call)) {
                    continue;
                }
                foldOwners.put(folded, call);
                break;
            }
        }
        for (PlannedRoot planned : plannedRoots) {
            addSkeletonActivation(activationByCall, planned.skeleton,
                    planned.root, trace, declaredSites, foldedRoots,
                    foldOwners);
        }
        stampActivationContainment(activationByCall, trace);
        stampFoldedRegionEntries(foldedRoots, foldOwners, activationByCall,
                trace);
        stampFieldOwners(activationByCall.values(), trace, fieldCalls,
                receiverReads);
        stampSignatures(activationByCall.values(), trace);
        result.runtimeInstances.addAll(activationByCall.values());
        stampRecordedExchanges(result, trace, protocolEvents);
        return result;
    }

    private static void stampFieldOwners(
            Collection<Map<String, Object>> activations, TraceIndex trace,
            Map<String, String> fieldCalls,
            Map<String, Map<String, Boolean>> receiverReads) {
        for (Map<String, Object> activation : activations) {
            Map<String, Set<Integer>> owners = new HashMap<>();
            Map<String, Set<Integer>> referents = new HashMap<>();
            Map<String, Set<Integer>> receivers = new HashMap<>();
            Set<String> elsewhere = new HashSet<>();
            Set<Integer> named = new HashSet<>();
            for (Long call : MapFields.longValues(
                    activation.get("callIds"))) {
                MethodEvent entered = trace.methodByCall.get(call);
                if (entered != null) {
                    named.add(entered.objectId);
                    for (Map.Entry<String, Boolean> read
                            : receiverReads.getOrDefault(entered.method,
                            Collections.<String, Boolean>emptyMap())
                            .entrySet()) {
                        if (!read.getValue() || entered.objectId == 0) {
                            elsewhere.add(read.getKey());
                        } else {
                            receivers.computeIfAbsent(read.getKey(),
                                    ignored -> new HashSet<>())
                                    .add(entered.objectId);
                        }
                    }
                }
                for (FieldAccessEvent event : trace.fieldsByCall.getOrDefault(
                        call, Collections.<FieldAccessEvent>emptyList())) {
                    named.add(event.receiverObjectId);
                    named.add(event.valueObjectId);
                    owners.computeIfAbsent(event.field,
                            ignored -> new HashSet<>())
                            .add(event.receiverObjectId);
                    if (event.valueObjectId != 0) {
                        referents.computeIfAbsent(event.field,
                                ignored -> new HashSet<>())
                                .add(event.valueObjectId);
                    }
                }
                for (RuntimeEvent event : trace.runtimeByCall.getOrDefault(
                        call, Collections.<RuntimeEvent>emptyList())) {
                    named.add(event.objectId);
                    String field = fieldCalls.get(event.siteId);
                    if (field != null && event.objectId != 0
                            && "CALL_SITE_ENTER".equals(event.kind)) {
                        owners.computeIfAbsent(field,
                                ignored -> new HashSet<>())
                                .add(event.objectId);
                    }
                }
            }
            if (!owners.isEmpty()) {
                activation.put(RuntimeSelectedRegionFinalizer.FIELD_OWNERS,
                        owners);
            }
            if (!referents.isEmpty()) {
                activation.put(
                        RuntimeSelectedRegionFinalizer.FIELD_REFERENTS,
                        referents);
            }
            receivers.keySet().removeAll(elsewhere);
            if (!receivers.isEmpty()) {
                activation.put(
                        RuntimeSelectedRegionFinalizer.RECEIVER_HOLDERS,
                        receivers);
            }
            named.remove(0);
            int[] objects = new int[named.size()];
            int next = 0;
            for (int object : named) objects[next++] = object;
            Arrays.sort(objects);
            activation.put(RuntimeSelectedRegionFinalizer.NAMED_OBJECTS,
                    objects);
        }
    }

    private static void stampSignatures(
            Collection<Map<String, Object>> activations, TraceIndex trace) {
        for (Map<String, Object> activation : activations) {
            List<Map.Entry<Long, String>> events = new ArrayList<>();
            for (Long call : MapFields.longValues(
                    activation.get("callIds"))) {
                MethodEvent entered = trace.methodByCall.get(call);
                if (entered != null) {
                    events.add(new AbstractMap.SimpleEntry<>(
                            entered.seq, "M " + entered.method + " "
                                    + entered.objectId));
                }
                for (RuntimeEvent event : trace.runtimeByCall.getOrDefault(
                        call, Collections.<RuntimeEvent>emptyList())) {
                    events.add(new AbstractMap.SimpleEntry<>(
                            event.seq, "R " + event.kind + " "
                                    + event.siteId + " "
                                    + event.declaredCallee + " "
                                    + event.argumentIndex + " "
                                    + event.runtimeType + " "
                                    + event.objectId + " "
                                    + event.primitiveValue + " "
                                    + event.outcome + " "
                                    + event.successorIndex + " "
                                    + event.branchKind + " "
                                    + event.switchCaseKeys));
                }
                for (FieldAccessEvent event : trace.fieldsByCall.getOrDefault(
                        call, Collections.<FieldAccessEvent>emptyList())) {
                    events.add(new AbstractMap.SimpleEntry<>(
                            event.seq, "F " + event.kind + " "
                                    + event.siteId + " " + event.field + " "
                                    + event.receiverObjectId + " "
                                    + event.valueObjectId + " "
                                    + event.primitiveValue + " "
                                    + event.version));
                }
                for (ProtocolEvent event : trace.protocolByCall.getOrDefault(
                        call, Collections.<ProtocolEvent>emptyList())) {
                    events.add(new AbstractMap.SimpleEntry<>(
                            event.seq, "P " + event.direction + " "
                                    + event.transport + " "
                                    + event.exchangeLeg() + " "
                                    + event.declaredCallee + " "
                                    + event.producerEndpointId));
                }
            }
            if (events.isEmpty()) continue;
            events.sort(Map.Entry.comparingByKey());
            StringBuilder signed = new StringBuilder();
            for (Map.Entry<Long, String> event : events) {
                signed.append(event.getValue()).append('\n');
            }
            activation.put(RuntimeSelectedRegionFinalizer.SIGNATURE,
                    ArtifactIO.digest(signed.toString(), 32));
            activation.put(RuntimeSelectedRegionFinalizer.FIRST_SEQ,
                    events.get(0).getKey());
            activation.put(RuntimeSelectedRegionFinalizer.LAST_SEQ,
                    events.get(events.size() - 1).getKey());
        }
    }

    static RecordedAccesses recordedAccesses(
            Collection<FieldAccessEvent> fields,
            Collection<RuntimeEvent> runtime,
            Map<String, String> storingCalls,
            Map<String, String> fieldCalls) {
        RecordedAccesses.Builder accesses = new RecordedAccesses.Builder();
        for (FieldAccessEvent event : fields) {
            accesses.add(event.field, event.seq, event.callId,
                    "FIELD_WRITE".equals(event.kind));
        }
        for (RuntimeEvent event : runtime) {
            if (!"CALL_SITE_ENTER".equals(event.kind)) continue;
            String stored = storingCalls.get(event.siteId);
            String field = fieldCalls.get(event.siteId);
            if (stored != null) {
                accesses.add(stored, event.seq, event.callId, true);
            } else if (field != null) {
                accesses.add(field, event.seq, event.callId, false);
            }
        }
        return accesses.build();
    }

    static RecordedHeap recordedHeap(Collection<MethodEvent> methods,
                                     Collection<FieldAccessEvent> fields,
                                     Collection<RuntimeEvent> runtime,
                                     Collection<Map<String, Object>>
                                             activations,
                                     Map<String, String> storingCalls,
                                     Map<String, String> fieldCalls) {
        RecordedHeap.Builder heap = new RecordedHeap.Builder();
        Map<Long, String> contexts = new HashMap<>();
        for (MethodEvent event : methods) {
            String context = causalContext(event);
            contexts.put(event.callId, context);
            heap.mention(event.objectId, context);
        }
        for (Map<String, Object> activation : activations) {
            long root = longNumber(activation.get("rootCallId"), -1L);
            heap.occurrence(root, contexts.getOrDefault(root, ""));
        }
        for (FieldAccessEvent event : fields) {
            String context = contexts.getOrDefault(event.callId, "");
            heap.mention(event.receiverObjectId, context);
            heap.mention(event.valueObjectId, context);
            if (event.receiverObjectId == 0) {
                heap.root(event.valueObjectId);
            } else {
                heap.edge(event.receiverObjectId, event.valueObjectId);
            }
        }
        Map<Long, Integer> storing = new HashMap<>();
        Map<Long, Integer> returning = new HashMap<>();
        for (RuntimeEvent event : sorted(runtime, value -> value.seq)) {
            heap.mention(event.objectId,
                    contexts.getOrDefault(event.callId, ""));
            if ("CALL_SITE_ENTER".equals(event.kind)) {
                if (storingCalls.containsKey(event.siteId)) {
                    storing.put(event.invocationId, event.objectId);
                } else if (fieldCalls.containsKey(event.siteId)) {
                    returning.put(event.invocationId, event.objectId);
                }
            } else if ("CALL_ARGUMENT".equals(event.kind)) {
                Integer holder = storing.get(event.invocationId);
                if (holder != null) heap.edge(holder, event.objectId);
            } else if ("CALL_SITE_RETURN".equals(event.kind)) {
                storing.remove(event.invocationId);
                Integer holder = returning.remove(event.invocationId);
                if (holder != null) heap.edge(holder, event.objectId);
            } else if (event.kind.startsWith("CALL_SITE_")) {
                storing.remove(event.invocationId);
                returning.remove(event.invocationId);
            }
        }
        return heap.build();
    }

    static String causalContext(MethodEvent event) {
        String key = event.requestKey;
        if (key.isEmpty() || key.endsWith("#0")) return "";
        return event.window + "|" + key;
    }

    private static final class PlannedRoot {
        private final StaticProgram.RegionRow skeleton;
        private final MethodEvent root;

        private PlannedRoot(StaticProgram.RegionRow skeleton,
                            MethodEvent root) {
            this.skeleton = skeleton;
            this.root = root;
        }
    }

    private static void stampFoldedRegionEntries(
            Map<Long, StaticProgram.RegionRow> foldedRoots,
            Map<Long, Long> foldOwners,
            Map<Long, Map<String, Object>> activationByCall,
            TraceIndex trace) {
        List<Long> ordered = new ArrayList<>(foldedRoots.keySet());
        Collections.sort(ordered);
        for (Long folded : ordered) {
            StaticProgram.RegionRow skeleton = foldedRoots.get(folded);
            Long owner = foldOwners.get(folded);
            Map<String, Object> enclosing = owner == null ? null
                    : activationByCall.get(owner);
            if (enclosing == null) continue;
            List<String> held = new ArrayList<>(strings(enclosing.get(
                    RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS)));
            if (!held.contains(skeleton.regionId)) {
                held.add(skeleton.regionId);
            }
            enclosing.put(RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS,
                    held);
            List<String> callers = new ArrayList<>();
            MethodEvent event = trace.methodByCall.get(folded);
            while (event != null && event.callId != owner.longValue()) {
                event = trace.methodByCall.get(event.parentCallId);
                if (event != null) callers.add(event.method);
            }
            Object prior = enclosing.get(
                    RuntimeSelectedRegionFinalizer.FOLDED_ENTRY_CALLERS);
            List<Object> entries = prior instanceof List
                    ? new ArrayList<Object>((List<?>) prior)
                    : new ArrayList<Object>();
            entries.add(callers);
            enclosing.put(RuntimeSelectedRegionFinalizer.FOLDED_ENTRY_CALLERS,
                    entries);
        }
    }

    private static void stampRecordedExchanges(
            Result result, TraceIndex trace,
            List<ProtocolEvent> protocolEvents) {
        Set<Long> activationRoots = new LinkedHashSet<>();
        for (Map<String, Object> activation : result.runtimeInstances) {
            long rootCallId = longNumber(activation.get("rootCallId"), -1L);
            if (rootCallId > 0L) activationRoots.add(rootCallId);
        }
        Map<Long, List<ProtocolEvent>> protocolByActivationRoot =
                new LinkedHashMap<>();
        for (ProtocolEvent event : protocolEvents) {
            for (Long call : trace.enclosingCalls(event.callId)) {
                if (activationRoots.contains(call)) {
                    protocolByActivationRoot.computeIfAbsent(call,
                            ignored -> new ArrayList<ProtocolEvent>())
                            .add(event);
                }
            }
        }
        stampSynchronousServerTransactions(result.runtimeInstances, trace,
                protocolEvents, protocolByActivationRoot);
        bindObservedCommunicationCaptures(result.runtimeInstances,
                protocolByActivationRoot, protocolEvents);
        retainInnermost(result.runtimeInstances, Collections::singletonList,
                RuntimeSelectedRegionFinalizer.OBSERVED_COMMUNICATION_CAPTURES,
                RuntimeRegionPlanner::communicationCaptureIdentity, false);
    }

    private static List<Map<String, Object>> retainedLoops(
            StaticProgram.RegionRow region, Set<String> occurrenceMethods) {
        List<Map<String, Object>> retained = new ArrayList<>();
        for (Map<String, Object> loop : region.retainedLoops) {
            if (occurrenceMethods.contains(
                    stringValue(loop.get("enclosingMethod")))) {
                retained.add(new LinkedHashMap<>(loop));
            }
        }
        return retained;
    }

    private static List<JsonObject> configuredSourcePhases(
            StaticProgram.RegionRow region, String occurrenceId,
            long activationRootCallId, TraceIndex trace) {
        Map<String, ConfiguredSourcePhaseContract.Declaration> bySite =
                region.sourcePhasesBySite();
        if (bySite.isEmpty()) return Collections.emptyList();
        Set<Long> subtree = trace.subtree(activationRootCallId);
        Map<Long, JsonObject> bySeq = new TreeMap<>();
        for (RuntimeEvent event : trace.runtime(subtree)) {
            if (!"CALL_SITE_ENTER".equals(event.kind)) continue;
            ConfiguredSourcePhaseContract.Declaration declaration =
                    bySite.get(event.siteId);
            if (declaration == null
                    || declaration.category() != RootCategory.HOOK) {
                continue;
            }
            if (!declaration.method().equals(event.method)
                    || event.seq <= 0L || event.callId <= 0L
                    || event.invocationId <= 0L) {
                throw new IllegalArgumentException(
                        "configured-source phase event differs "
                        + "from exact static site " + declaration.siteId());
            }
            bySeq.put(event.seq, ConfiguredSourcePhaseContract.occurrence(
                    declaration, occurrenceId, event.seq,
                    event.invocationId, event.declaredCallee,
                    enclosingCalls(trace, event.seq, event.callId,
                            activationRootCallId)));
        }
        for (FieldAccessEvent read : trace.reads(subtree)) {
            ConfiguredSourcePhaseContract.Declaration declaration =
                    bySite.get(read.siteId);
            if (declaration == null
                    || declaration.category() != RootCategory.CONFIG
                    || !declaration.fieldSignature().equals(read.field)) {
                continue;
            }
            if (read.seq <= 0L || read.callId <= 0L) {
                throw new IllegalArgumentException(
                        "configuration read event differs from exact static"
                        + " site " + declaration.siteId());
            }
            bySeq.put(read.seq, ConfiguredSourcePhaseContract
                    .configOccurrence(declaration, occurrenceId, read.seq,
                            read.field, enclosingCalls(trace, read.seq,
                                    read.callId, activationRootCallId)));
        }
        return new ArrayList<>(bySeq.values());
    }

    private static List<Long> enclosingCalls(TraceIndex trace, long seq,
                                             long callId,
                                             long activationRootCallId) {
        List<Long> enclosingCallIds = new ArrayList<>();
        MethodEvent owner = trace.methodByCall.get(callId);
        Set<Long> seen = new LinkedHashSet<>();
        while (owner != null && seen.add(owner.callId)) {
            enclosingCallIds.add(owner.callId);
            if (owner.callId == activationRootCallId) break;
            owner = trace.methodByCall.get(owner.parentCallId);
        }
        if (enclosingCallIds.isEmpty()
                || enclosingCallIds.get(enclosingCallIds.size() - 1)
                != activationRootCallId) {
            throw new IllegalArgumentException(
                    "configured-source phase event " + seq
                    + " is not enclosed by activation root "
                    + activationRootCallId);
        }
        return enclosingCallIds;
    }


    private static void stampSynchronousServerTransactions(
            List<Map<String, Object>> activations, TraceIndex trace,
            List<ProtocolEvent> protocolEvents,
            Map<Long, List<ProtocolEvent>> protocolByActivationRoot) {
        Map<String, Map<String, List<ProtocolEvent>>> legs =
                new LinkedHashMap<>();
        for (ProtocolEvent event : protocolEvents) {
            if (event.correlationId.isEmpty()) continue;
            legs.computeIfAbsent(event.direction + "\n" + event.half,
                    ignored -> new LinkedHashMap<>())
                    .computeIfAbsent(protocolTransactionKey(event),
                            ignored -> new ArrayList<>()).add(event);
        }
        Map<String, List<ProtocolEvent>> none = Collections.emptyMap();
        Map<String, List<ProtocolEvent>> requestReceives =
                legs.getOrDefault("RECEIVE\nREQUEST", none);
        Map<String, List<ProtocolEvent>> responseSends =
                legs.getOrDefault("SEND\nRESPONSE", none);
        Map<String, List<ProtocolEvent>> requestSends =
                legs.getOrDefault("SEND\nREQUEST", none);
        Map<String, List<ProtocolEvent>> responseReceives =
                legs.getOrDefault("RECEIVE\nRESPONSE", none);
        for (Map.Entry<String, List<ProtocolEvent>> transaction
                : requestSends.entrySet()) {
            List<ProtocolEvent> responses = responseReceives.getOrDefault(
                    transaction.getKey(), Collections.<ProtocolEvent>emptyList(
                            ));
            for (ProtocolEvent request : transaction.getValue()) {
                for (ProtocolEvent response : responses) {
                    if (response.seq <= request.seq || request.laneId <= 0L
                            || request.laneId != response.laneId
                            || request.spanId > 0L && response.spanId > 0L
                            && request.spanId != response.spanId) {
                        continue;
                    }
                    for (List<ProtocolEvent> owned
                            : protocolByActivationRoot.values()) {
                        if (owned.contains(request)
                                && !owned.contains(response)) {
                            owned.add(response);
                        }
                    }
                }
            }
        }
        for (Map.Entry<String, List<ProtocolEvent>> transaction
                : requestReceives.entrySet()) {
            List<ProtocolEvent> responses = responseSends.getOrDefault(
                    transaction.getKey(),
                    Collections.<ProtocolEvent>emptyList());
            for (ProtocolEvent receive : transaction.getValue()) {
                for (ProtocolEvent response : responses) {
                    if (response.seq <= receive.seq
                            || receive.laneId <= 0L
                            || receive.laneId != response.laneId) {
                        continue;
                    }
                    for (Map<String, Object> activation : activations) {
                        long rootCall = longNumber(
                                activation.get("rootCallId"), -1L);
                        MethodEvent root = trace.methodByCall.get(rootCall);
                        if (root == null || root.seq <= receive.seq
                                || root.seq >= response.seq
                                || root.laneId != receive.laneId) {
                            continue;
                        }
                        if (receive.spanId > 0L && root.spanId > 0L
                                && receive.spanId != root.spanId) {
                            continue;
                        }
                        if (receive.remoteParentSpanId > 0L
                                && root.remoteParentSpanId > 0L
                                && receive.remoteParentSpanId
                                != root.remoteParentSpanId) {
                            continue;
                        }
                        List<ProtocolEvent> owned = protocolByActivationRoot
                                .computeIfAbsent(rootCall,
                                        ignored -> new ArrayList<>());
                        if (!owned.contains(receive)) owned.add(receive);
                        if (!owned.contains(response)) owned.add(response);
                    }
                }
            }
        }
    }

    private static String protocolTransactionKey(ProtocolEvent event) {
        return event.transport + "\n" + event.correlationId + "\n"
                + event.attemptId;
    }

    private static void stampActivationContainment(
            Map<Long, Map<String, Object>> activationByCall,
            TraceIndex trace) {
        for (Map.Entry<Long, Map<String, Object>> entry
                : activationByCall.entrySet()) {
            List<String> enclosing = new ArrayList<>();
            for (Long callId : trace.enclosingCalls(entry.getKey())) {
                if (callId.longValue() == entry.getKey().longValue()) {
                    continue;
                }
                Map<String, Object> owner = activationByCall.get(callId);
                if (owner != null) {
                    enclosing.add(stringValue(owner.get("activationId")));
                }
            }
            if (!enclosing.isEmpty()) {
                entry.getValue().put("enclosingActivationIds", enclosing);
            }
        }
    }

    private static void addSkeletonActivation(
            Map<Long, Map<String, Object>> activationByCall,
            StaticProgram.RegionRow skeleton, MethodEvent root,
            TraceIndex trace, Set<String> declaredSites,
            Map<Long, StaticProgram.RegionRow> foldedRoots,
            Map<Long, Long> foldOwners) {
        Set<Long> subtree = trace.subtree(root.callId);
        Set<String> allowed = new LinkedHashSet<>(skeleton.methods);
        Set<Long> foldedCalls = new LinkedHashSet<>();
        List<StaticProgram.RegionRow> foldedHere = new ArrayList<>();
        for (Long call : subtree) {
            StaticProgram.RegionRow folded = foldedRoots.get(call);
            if (folded == null || !Long.valueOf(root.callId).equals(
                    foldOwners.get(call))) {
                continue;
            }
            if (!foldedHere.contains(folded)) foldedHere.add(folded);
            for (Long inner : trace.subtree(call)) {
                MethodEvent event = trace.methodByCall.get(inner);
                if (event != null && folded.methods.contains(event.method)) {
                    foldedCalls.add(inner);
                }
            }
        }
        Set<Long> calls = subtree;
        calls.removeIf(call -> {
            if (foldedCalls.contains(call)) return false;
            MethodEvent event = trace.methodByCall.get(call);
            return event == null || !allowed.contains(event.method);
        });
        Set<String> observed = trace.methodNames(calls);
        List<String> observedAnchors = new ArrayList<>();
        for (String anchor : skeleton.anchorMethods) {
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
        activation.put("activationId", recordedActivationKey(root));
        activation.put("regionId", skeleton.regionId);
        activation.put("rootCallId", root.callId);
        activation.put("rootMethod", root.method);
        activation.put("rootAuthority", skeleton.rootAuthority);
        activation.put("anchorMethod", observedAnchors.get(0));
        activation.put("anchorMethods", observedAnchors);
        activation.put("selection", skeleton.selection);
        activation.put("test", root.test);
        activation.put("occurrenceAddress", root.occurrenceAddress);
        if (root.laneId > 0L) activation.put("laneId", root.laneId);
        activation.put("callIds", new ArrayList<>(calls));
        activation.put("observedMethods", new ArrayList<>(observed));
        activation.put(
                RuntimeSelectedRegionFinalizer
                        .OBSERVED_COMMUNICATION_CAPTURES,
                observedCommunicationCaptures(skeleton, foldedHere, calls,
                        trace));
        List<Map<String, Object>> declared = declaredSiteCaptures(
                declaredSites, trace, calls, root);
        if (!declared.isEmpty()) {
            activation.put(DeclaredSiteCapture.PLAN_FIELD, declared);
        }
        activationByCall.put(root.callId, activation);
    }

    private static List<Map<String, Object>> observedCommunicationCaptures(
            StaticProgram.RegionRow skeleton,
            List<StaticProgram.RegionRow> folded, Set<Long> calls,
            TraceIndex trace) {
        List<RuntimeEvent> events = trace.runtime(calls);
        List<Map<String, Object>> observed = new ArrayList<>();
        List<Map<String, Object>> ports =
                new ArrayList<>(skeleton.communicationPorts);
        for (StaticProgram.RegionRow inside : folded) {
            for (Map<String, Object> port : inside.communicationPorts) {
                if (!ports.contains(port)) ports.add(port);
            }
        }
        for (Map<String, Object> port : ports) {
            String side = stringValue(port.get(
                    RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE));
            String portId = stringValue(port.get(
                    CommunicationCatalogContract.PORT_ID));
            if (!("IN".equals(side) || "OUT".equals(side))
                    || portId.isEmpty()) {
                continue;
            }
            for (RuntimeEvent event : events) {
                if (!communicationCaptureEvent(port, event)) continue;
                Map<String, Object> capture = new LinkedHashMap<>();
                capture.put("side", side);
                capture.put("portId", portId);
                capture.put("eventSeq", event.seq);
                observed.add(capture);
            }
        }
        return observed;
    }

    private static boolean communicationCaptureEvent(
            Map<String, Object> port, RuntimeEvent event) {
        String capture = stringValue(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        String method = stringValue(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        String callee = stringValue(port.get(
                CommunicationCatalogContract.DECLARED_CALLEE));
        int unitIndex = number(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX), -1);
        int argumentIndex = number(port.get(
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1);
        String siteId = method + "#u" + unitIndex;
        if (!method.equals(event.method)) return false;
        if (CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT.equals(
                capture)) {
            return "CALL_ARGUMENT".equals(event.kind)
                    && siteId.equals(event.siteId)
                    && callee.equals(event.declaredCallee)
                    && argumentIndex == event.argumentIndex;
        }
        if (CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(capture)) {
            return "CALL_SITE_RETURN".equals(event.kind)
                    && siteId.equals(event.siteId)
                    && callee.equals(event.declaredCallee);
        }
        if (CommunicationCatalogContract.CAPTURE_METHOD_PARAMETER.equals(
                capture)) {
            return "METHOD_ARGUMENT".equals(event.kind)
                    && argumentIndex == event.argumentIndex;
        }
        return CommunicationCatalogContract.CAPTURE_METHOD_RETURN.equals(
                capture) && "METHOD_EXIT_NORMAL".equals(event.kind);
    }

    private static void bindObservedCommunicationCaptures(
            Collection<Map<String, Object>> activations,
            Map<Long, List<ProtocolEvent>> protocolByActivationRoot,
            List<ProtocolEvent> protocolEvents) {
        for (Map<String, Object> activation : activations) {
            long rootCallId = longNumber(activation.get("rootCallId"), -1L);
            List<Map<String, Object>> bound = new ArrayList<>();
            List<ProtocolEvent> protocol = new ArrayList<>(
                    protocolByActivationRoot.getOrDefault(rootCallId,
                            Collections.<ProtocolEvent>emptyList()));
            List<Map<String, Object>> sent = new ArrayList<>();
            for (ProtocolEvent event : protocol) {
                if (!"SEND".equals(event.direction)) continue;
                Map<String, Object> leg = new LinkedHashMap<>();
                leg.put("exchangeLeg", event.exchangeLeg());
                leg.put("transportEventSeq", event.seq);
                sent.add(leg);
            }
            activation.put(RuntimeSelectedRegionFinalizer.SENT_EXCHANGE_LEGS,
                    sent);
            long laneId = longNumber(activation.get("laneId"), -1L);
            for (ProtocolEvent event : protocolEvents) {
                if (laneId > 0L && event.laneId == laneId
                        && !protocol.contains(event)) {
                    protocol.add(event);
                }
            }
            for (Map<String, Object> capture : rows(activation.get(
                    RuntimeSelectedRegionFinalizer
                            .OBSERVED_COMMUNICATION_CAPTURES))) {
                String side = stringValue(capture.get("side"));
                long capturedAt = longNumber(capture.get("eventSeq"), -1L);
                ProtocolEvent boundary = null;
                for (ProtocolEvent event : protocol) {
                    if (!("OUT".equals(side) ? "SEND".equals(event.direction)
                            : "RECEIVE".equals(event.direction))) {
                        continue;
                    }
                    if ("OUT".equals(side) && event.seq > capturedAt
                            && (boundary == null
                            || event.seq < boundary.seq)) {
                        boundary = event;
                    } else if ("IN".equals(side) && event.seq < capturedAt
                            && (boundary == null
                            || event.seq > boundary.seq)) {
                        boundary = event;
                    }
                }
                if ("IN".equals(side) && boundary != null) {
                    String exchange = boundary.exchangeLeg();
                    String transport = boundary.transport;
                    for (ProtocolEvent event : protocol) {
                        if (transport.equals(event.transport)
                                && "RECEIVE".equals(event.direction)
                                && event.seq < capturedAt
                                && exchange.equals(event.exchangeLeg())
                                && event.seq < boundary.seq) {
                            boundary = event;
                        }
                    }
                }
                if (boundary == null) continue;
                Map<String, Object> exact = new LinkedHashMap<>(capture);
                exact.put(CommunicationCatalogContract.TRANSPORT,
                        boundary.transport);
                exact.put("half", boundary.half);
                exact.put("exchangeLeg", boundary.exchangeLeg());
                exact.put("attemptId", boundary.attemptId);
                exact.put("transportEventSeq", boundary.seq);
                bound.add(exact);
                List<ProtocolEvent> owned = protocolByActivationRoot
                        .computeIfAbsent(rootCallId,
                                ignored -> new ArrayList<ProtocolEvent>());
                if (!owned.contains(boundary)) owned.add(boundary);
            }
            activation.put(RuntimeSelectedRegionFinalizer
                    .OBSERVED_COMMUNICATION_CAPTURES, bound);
        }
    }

    private static void retainInnermost(
            Collection<Map<String, Object>> owners,
            Function<Map<String, Object>, List<Map<String, Object>>> holders,
            String field, Function<Map<String, Object>, String> key,
            boolean dropEmpty) {
        Map<String, Set<String>> ownersByKey = new LinkedHashMap<>();
        for (Map<String, Object> owner : owners) {
            String id = stringValue(owner.get("activationId"));
            if (id.isEmpty()) continue;
            for (Map<String, Object> holder : holders.apply(owner)) {
                for (Map<String, Object> row : rows(holder.get(field))) {
                    String identity = key.apply(row);
                    if (!identity.isEmpty()) {
                        ownersByKey.computeIfAbsent(identity,
                                ignored -> new LinkedHashSet<>()).add(id);
                    }
                }
            }
        }
        Set<String> shadowed = new LinkedHashSet<>();
        for (Map<String, Object> child : owners) {
            String childId = stringValue(child.get("activationId"));
            List<String> enclosing = strings(child.get(
                    "enclosingActivationIds"));
            if (childId.isEmpty() || enclosing.isEmpty()) continue;
            for (Map<String, Object> holder : holders.apply(child)) {
                for (Map<String, Object> row : rows(holder.get(field))) {
                    String identity = key.apply(row);
                    Set<String> held = ownersByKey.get(identity);
                    if (held == null || !held.contains(childId)) continue;
                    for (String ancestor : enclosing) {
                        if (held.contains(ancestor)) {
                            shadowed.add(ancestor + "\n" + identity);
                        }
                    }
                }
            }
        }
        if (shadowed.isEmpty()) return;
        for (Map<String, Object> owner : owners) {
            String id = stringValue(owner.get("activationId"));
            for (Map<String, Object> holder : holders.apply(owner)) {
                List<Map<String, Object>> retained = new ArrayList<>();
                for (Map<String, Object> row : rows(holder.get(field))) {
                    if (!shadowed.contains(id + "\n" + key.apply(row))) {
                        retained.add(row);
                    }
                }
                if (dropEmpty && retained.isEmpty()) {
                    holder.remove(field);
                } else {
                    holder.put(field, retained);
                }
            }
        }
    }

    private static String communicationCaptureIdentity(
            Map<String, Object> capture) {
        String side = stringValue(capture.get("side"));
        String port = stringValue(capture.get("portId"));
        String exchange = stringValue(capture.get("exchangeLeg"));
        long event = longNumber(capture.get("eventSeq"), -1L);
        long transport = longNumber(capture.get("transportEventSeq"), -1L);
        if (side.isEmpty() || port.isEmpty() || exchange.isEmpty()
                || event < 0L || transport < 0L) {
            return "";
        }
        return side + "\n" + port + "\n" + event + "\n" + exchange
                + "\n" + transport;
    }

    private static void retainInnermostCommunicationConsumers(
            List<Map<String, Object>> plans) {
        Set<String> selectedRoots = new LinkedHashSet<>();
        for (Map<String, Object> plan : plans) {
            String root = rootSelectorMethod(plan);
            if (!root.isEmpty()) selectedRoots.add(root);
        }
        for (Map<String, Object> plan : plans) {
            Object encoded = plan.get(CommunicationHandoffSpec.FIELD);
            if (!(encoded instanceof List)) continue;
            String root = rootSelectorMethod(plan);
            List<?> declared = (List<?>) encoded;
            List<Object> retained = new ArrayList<>();
            for (Object element : declared) {
                if (!(element instanceof Map)) continue;
                Map<?, ?> site = (Map<?, ?>) element;
                String method = stringValue(site.get(
                        CommunicationCatalogContract
                                .PORT_DEFINITION_METHOD));
                boolean inbound = CommunicationHandoffSpec.IN.equals(
                        stringValue(site.get(
                                CommunicationHandoffSpec.SIDE)));
                if (inbound && !method.isEmpty() && !method.equals(root)
                        && selectedRoots.contains(method)) {
                    continue;
                }
                retained.add(element);
            }
            if (retained.size() == declared.size()) continue;
            if (retained.isEmpty()) {
                plan.remove(CommunicationHandoffSpec.FIELD);
            } else {
                plan.put(CommunicationHandoffSpec.FIELD, retained);
            }
        }
    }

    private static String rootSelectorMethod(Map<String, Object> plan) {
        Object selector = plan.get("rootSelector");
        return selector instanceof Map
                ? stringValue(((Map<?, ?>) selector).get("method")) : "";
    }

    private static void republishEnclosingActivationIds(
            List<Map<String, Object>> plans,
            Map<String, String> publishedActivationIds) {
        for (Map<String, Object> plan : plans) {
            if (!plan.containsKey("enclosingActivationIds")) continue;
            List<String> published = new ArrayList<>();
            for (String recorded : strings(
                    plan.get("enclosingActivationIds"))) {
                String name = publishedActivationIds.get(recorded);
                if (name != null && !published.contains(name)) {
                    published.add(name);
                }
            }
            if (published.isEmpty()) {
                plan.remove("enclosingActivationIds");
            } else {
                plan.put("enclosingActivationIds", published);
            }
        }
    }

    private static String exactBranchEventIdentity(
            Map<String, Object> branch, TraceIndex trace) {
        long eventSeq = longNumber(
                branch.get("selectedRuntimeEventSeq"), -1L);
        long statedCall = longNumber(branch.get("selectedCallId"), -1L);
        long recordedCall = trace.eventCallIdBySeq.uniqueValue(eventSeq);
        String site = stringValue(branch.get("siteId"));
        if (eventSeq < 0L || statedCall <= 0L || recordedCall <= 0L
                || statedCall != recordedCall || site.isEmpty()) {
            return "";
        }
        return eventSeq + "\n" + recordedCall + "\n" + site;
    }

    private static String exactMaterializationEventIdentity(
            Map<String, Object> action, TraceIndex trace) {
        long eventSeq = longNumber(action.get("eventSeq"), -1L);
        long statedCall = longNumber(action.get("callId"), -1L);
        long recordedCall = trace.eventCallIdBySeq.uniqueValue(eventSeq);
        if (eventSeq < 0L || recordedCall <= 0L
                || (statedCall > 0L && statedCall != recordedCall)) {
            return "";
        }
        String location = stringValue(action.get("location"));
        String binding = stringValue(action.get("bindingMode"));
        String site = stringValue(action.get("staticAccessSiteId"));
        if (site.isEmpty()) site = stringValue(action.get("siteId"));
        String cell = stringValue(action.get("cell"));
        String accessField = stringValue(action.get("accessFieldSignature"));
        String leafField = stringValue(action.get("leafFieldSignature"));
        String handoffPath = stringValue(action.get(
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH));
        List<String> fieldPath = strings(action.get("fieldPath"));
        int argumentIndex = number(action.get("argumentIndex"),
                number(action.get("index"), -1));
        if (location.isEmpty() && binding.isEmpty() && site.isEmpty()
                && cell.isEmpty() && accessField.isEmpty()
                && leafField.isEmpty() && handoffPath.isEmpty()
                && fieldPath.isEmpty() && argumentIndex < 0) {
            return "";
        }
        return eventSeq + "\n" + recordedCall + "\n" + location + "\n"
                + binding + "\n" + site + "\n" + cell + "\n"
                + accessField + "\n" + leafField + "\n" + handoffPath
                + "\n" + fieldPath + "\n" + argumentIndex;
    }

    private static boolean validRootAuthority(String authority) {
        return "THREAD_ENTRY".equals(authority)
                || "TASK_ENTRY".equals(authority)
                || "MAIN_ENTRY".equals(authority)
                || "EXPLICIT_FAULT_ENTRY".equals(authority)
                || "FAILURE_TARGET_ENTRY".equals(authority);
    }

    static LoopBoundPolicy declaredLoopBounds(
            List<Map<String, Object>> regions) {
        Map<String, Integer> declared = new TreeMap<>();
        for (Map<String, Object> region : regions) {
            for (Map<String, Object> loop : rows(region.get(
                    RuntimeSelectedRegionFinalizer.RETAINED_LOOPS))) {
                Object stated = loop.get(LoopBoundPolicy.LOOP_BODY_BOUND);
                if (stated == null) continue;
                String site = LoopBoundPolicy.loopSiteId(strings(
                        loop.get(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS)));
                int bound = LoopBoundPolicy.bodyBound(stated);
                if (site.isEmpty() || bound < 1) continue;
                Integer held = declared.put(site, Integer.valueOf(bound));
                if (held != null && held.intValue() != bound) {
                    throw new IllegalStateException(
                            LoopBoundPolicy.DECLARED_BOUND_SITE_UNDECLARED
                                    + ": loop " + site + " is declared under"
                                    + " K_L=" + held + " and K_L=" + bound
                                    + "; one loop has one prefix");
                }
            }
        }
        return LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.declaredDefault(), declared);
    }

    static Result plan(List<Map<String, Object>> regions,
                       String regionSource,
                       Collection<Map<String, Object>> runtimeSeeds,
                       List<MethodEvent> methods,
                       List<RuntimeEvent> runtimeEvents,
                       List<FieldAccessEvent> fieldEvents,
                       List<ProtocolEvent> protocolEvents,
                       Collection<Map<String, Object>> planGaps) {
        declaredLoopBounds(regions);
        TraceIndex trace = new TraceIndex(methods, runtimeEvents,
                fieldEvents, protocolEvents);
        Result result = new Result();
        result.planGaps.addAll(planGaps);
        Map<String, StaticProgram.RegionRow> regionById =
                new LinkedHashMap<>();
        for (StaticProgram.RegionRow region : StaticProgram.regionRows(
                regions, "SYMBOLIC_REGION", regionSource)) {
            declareCutPortCells(region);
            regionById.put(region.regionId, region);
        }
        Map<String, Map<String, Object>> planByOccurrence =
                new LinkedHashMap<>();
        Map<String, Integer> replayInvocationOrdinals =
                new LinkedHashMap<>();
        Map<String, String> publishedActivationIds = new LinkedHashMap<>();
        Set<String> publishedActivationNames = new LinkedHashSet<>();
        for (Map<String, Object> seed : runtimeSeeds) {
            if (!"RUNTIME_REGION_ACTIVATION".equals(
                    stringValue(seed.get("kind")))) {
                throw new IllegalArgumentException(
                        "concolic planning requires runtime activation seeds");
            }
            String regionId = stringValue(seed.get("regionId"));
            StaticProgram.RegionRow region = regionById.get(regionId);
            if (region == null) continue;
            long rootCallId = longNumber(seed.get("rootCallId"), -1L);
            MethodEvent root = trace.methodByCall.get(rootCallId);
            if (root == null) {
                throw new IllegalArgumentException("runtime activation seed "
                        + "references an unknown root call: " + regionId
                        + "#call" + rootCallId);
            }
            Set<String> allowedMethods = new LinkedHashSet<>(region.methods);
            Set<Long> calls = MapFields.longValues(seed.get("callIds"));
            if (calls.isEmpty()) calls = trace.subtree(rootCallId);
            Set<String> observedMethods = new LinkedHashSet<>(
                    strings(seed.get("observedMethods")));
            if (observedMethods.isEmpty()) {
                observedMethods.addAll(trace.methodNames(calls));
            }
            observedMethods.retainAll(allowedMethods);
            List<Map<String, Object>> branches = branches(
                    region.branchPolicies, trace.runtime(calls));
            boolean target = Boolean.TRUE.equals(MapFields.booleanValue(
                    seed.get(RuntimeSelectedRegionFinalizer
                            .FAILURE_TARGET_OCCURRENCE)));
            MethodEvent semanticContext = target
                    ? trace.selectedTargetContext(root, calls, branches)
                    : root;
            NodeId node = recordedNode(root);
            int replayInvocationOrdinal = replayInvocationOrdinals.merge(
                    replayInvocationScope(regionId, root, node),
                    1, Integer::sum);
            String occurrenceId = stringValue(seed.get("occurrenceId"));
            if (occurrenceId.isEmpty()) continue;
            if (planByOccurrence.containsKey(occurrenceId)) continue;
            String exactActivationId = stringValue(seed.get("activationId"));
            if (exactActivationId.isEmpty()) {
                throw new IllegalArgumentException("runtime activation seed "
                        + "carries no recorded call identity: " + regionId
                        + "#call" + rootCallId);
            }
            List<String> enclosingActivationIds = new ArrayList<>(
                    new LinkedHashSet<>(strings(seed.get(
                            "enclosingActivationIds"))));
            if (enclosingActivationIds.contains(exactActivationId)) {
                throw new IllegalArgumentException("runtime activation "
                        + exactActivationId + " encloses itself");
            }
            Set<String> retainedOccurrences = new LinkedHashSet<>(
                    region.runtimeOccurrenceIds);
            if (retainedOccurrences.isEmpty()) {
                throw new IllegalArgumentException("runtime-refined region "
                        + "has no retained activation seeds: " + regionId);
            }
            if (!retainedOccurrences.contains(occurrenceId)) continue;
            OccurrenceBinding.bindOccurrence(region.json, rootCallId,
                    occurrenceId);
            Set<String> occurrenceMethods =
                    new LinkedHashSet<>(observedMethods);
            if (allowedMethods.contains(root.method)) {
                occurrenceMethods.add(root.method);
            }
            Map<String, Object> goal = closureGoal(region, occurrenceId,
                    target, occurrenceMethods, branches);
            Map<String, Object> plan = new LinkedHashMap<>();
            plan.put("schemaVersion", 3);
            plan.put("kind", "CONCOLIC_REGION_PLAN");
            plan.put("occurrenceId", occurrenceId);
            plan.put("regionId", region.regionId);
            if (!region.rootAuthority.isEmpty()) {
                plan.put(LoopBoundPolicy.ROOT_AUTHORITY, region.rootAuthority);
            }
            if (region.rootLoop != null) {
                plan.put(LoopBoundPolicy.ROOT_LOOP, region.rootLoop);
            }
            Map<String, Object> plannedRootSelector = rootSelector(root,
                    node, semanticContext.requestKey,
                    semanticContext.requestApi, replayInvocationOrdinal);
            String plannedActivationId = activationId(occurrenceId,
                    plannedRootSelector);
            if (!publishedActivationNames.add(plannedActivationId)) {
                throw new IllegalStateException("two planned activations "
                        + "claimed one published activation identity: "
                        + plannedActivationId + " at " + occurrenceId);
            }
            publishedActivationIds.put(exactActivationId,
                    plannedActivationId);
            plan.put("activationId", plannedActivationId);
            if (!enclosingActivationIds.isEmpty()) {
                plan.put("enclosingActivationIds",
                        new ArrayList<>(enclosingActivationIds));
            }
            List<String> folded = strings(seed.get(
                    RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS));
            if (!folded.isEmpty()) {
                plan.put(RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS,
                        new ArrayList<>(folded));
            }
            List<Map<String, Object>> retainedLoops =
                    retainedLoops(region, occurrenceMethods);
            if (!retainedLoops.isEmpty()) {
                plan.put(LoopBoundPolicy.PLAN_FIELD, retainedLoops);
            }
            List<JsonObject> sourcePhases = configuredSourcePhases(
                    region, occurrenceId, rootCallId, trace);
            if (!sourcePhases.isEmpty()) {
                plan.put(ConfiguredSourcePhaseContract.PLAN_FIELD,
                        sourcePhases);
            }
            List<Map<String, Object>> captures = rows(
                    seed.get(DeclaredSiteCapture.PLAN_FIELD));
            if (!captures.isEmpty()) {
                plan.put(DeclaredSiteCapture.PLAN_FIELD, captures);
            }
            List<Map<String, Object>> handoffSites = attachSites(region);
            if (!handoffSites.isEmpty()) {
                plan.put(CommunicationHandoffSpec.FIELD, handoffSites);
            }
            plan.put("relationKey", relationKey(node, regionId));
            putTraceContext(plan, semanticContext, node);
            plan.put("rootSelector", plannedRootSelector);
            if (!region.anchorMethod.isEmpty()) {
                plan.put("targetMethod", region.anchorMethod);
            }
            String basis = RuntimeSelectedRegionFinalizer.ADMISSION_BASIS;
            String depth = RuntimeSelectedRegionFinalizer.DEMAND_DEPTH;
            if (seed.containsKey(basis)) {
                plan.put(basis, seed.get(basis));
                if (seed.containsKey(depth)) {
                    plan.put(depth, seed.get(depth));
                }
            }
            for (String stated : new String[] {
                    RuntimeSelectedRegionFinalizer.DECIDER_CLASS,
                    RuntimeSelectedRegionFinalizer.CONFINED_WRITERS,
                    RuntimeSelectedRegionFinalizer.ESCAPED_WRITERS,
                    RuntimeSelectedRegionFinalizer.STORE_FETCHES,
                    RuntimeSelectedRegionFinalizer.DOORS_ONLY,
                    RuntimeSelectedRegionFinalizer.DOORS_ONLY_DECLARED,
                    ZkChain.CONTENT_KEYS}) {
                if (seed.containsKey(stated)) {
                    plan.put(stated, seed.get(stated));
                }
            }
            for (String declared : new String[] {
                    RuntimeSelectedRegionFinalizer.DECLARED_OCCURRENCE,
                    RuntimeSelectedRegionFinalizer.CONTEXT_SHAPE,
                    RuntimeSelectedRegionFinalizer.RECORDED_BESIDE}) {
                if (seed.containsKey(declared)) {
                    plan.put(declared, seed.get(declared));
                }
            }
            plan.put(DeclaredSiteCapture.ROOT_CALL_ID, rootCallId);
            plan.put("closureGoals", Collections.singletonList(goal));
            stateAnchorOffAddress(plan, result.planGaps);
            result.regionPlans.add(plan);
            planByOccurrence.put(occurrenceId, plan);
        }
        republishEnclosingActivationIds(result.regionPlans,
                publishedActivationIds);
        retainInnermost(result.regionPlans, Collections::singletonList,
                DeclaredSiteCapture.PLAN_FIELD,
                capture -> String.valueOf(longNumber(capture.get(
                        DeclaredSiteCapture.INVOCATION_ID), -1L)), true);
        Function<Map<String, Object>, List<Map<String, Object>>> goals =
                plan -> rows(plan.get("closureGoals"));
        retainInnermost(result.regionPlans, goals, "symbolize",
                action -> exactMaterializationEventIdentity(action, trace),
                false);
        retainInnermost(result.regionPlans, goals, "branches",
                branch -> exactBranchEventIdentity(branch, trace), false);
        retainInnermostCommunicationConsumers(result.regionPlans);
        for (StaticProgram.RegionRow region : regionById.values()) {
            result.regionCatalog.add(catalogRow(region));
        }
        return result;
    }

    private static Map<String, Object> closureGoal(
            StaticProgram.RegionRow region, String occurrenceId,
            boolean target, Set<String> occurrenceMethods,
            List<Map<String, Object>> branches) {
        Map<String, Object> goal = new LinkedHashMap<>();
        goal.put("goalId", (target ? "GOAL.TARGET_REACH."
                : "GOAL.REGION_PATH.")
                + UUID.nameUUIDFromBytes(occurrenceId.getBytes(
                StandardCharsets.UTF_8)));
        goal.put("kind", target ? "TARGET_REACH_CLOSURE"
                : "REGION_PATH_CLOSURE");
        goal.put("runtimeDefinitionMethods",
                new ArrayList<>(occurrenceMethods));
        goal.put("admission", object("state", "READY",
                "mode", "RUNTIME_FAILURE_CLOSURE",
                "blockers", Collections.emptyList()));
        goal.put("symbolize", symbolize(region.symbolicInputs,
                occurrenceId));
        goal.put("branches", branches);
        return goal;
    }

    private static Map<String, Object> catalogRow(
            StaticProgram.RegionRow region) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", 3);
        row.put("kind", "SYMBOLIC_REGION");
        row.put("regionId", region.regionId);
        Object declaredSources = region.json.get(
                StaticSymbolicSourceDeclaration.FIELD);
        if (declaredSources != null) {
            row.put(StaticSymbolicSourceDeclaration.FIELD,
                    deepCopyValue(declaredSources));
        }
        return row;
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
        return normalizeScalar(value);
    }

    private static Object normalizeScalar(Object value) {
        if (value instanceof Integer || value instanceof Short
                || value instanceof Byte) {
            return ((Number) value).longValue();
        }
        if (value instanceof Float) {
            return ((Number) value).doubleValue();
        }
        return value;
    }

    private static JsonElement toJsonTreeFast(Object value) {
        if (value == null) {
            return JsonNull.INSTANCE;
        }
        if (value instanceof String) {
            return new JsonPrimitive((String) value);
        }
        if (value instanceof Boolean) {
            return new JsonPrimitive((Boolean) value);
        }
        if (value instanceof Number) {
            return new JsonPrimitive((Number) value);
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

    public static List<Map<String, Object>> attachSites(
            StaticProgram.RegionRow region) {
        Map<String, Map<String, Object>> byCapture = new LinkedHashMap<>();
        for (Map<String, Object> port : region.symbolicInputs) {
            Map<String, Object> site = handoffSite(port,
                    CommunicationHandoffSpec.IN);
            if (site != null) {
                byCapture.putIfAbsent(CommunicationCatalogContract
                        .captureKey(CommunicationHandoffSpec.IN, port), site);
            }
        }
        return new ArrayList<>(byCapture.values());
    }

    public static List<CommunicationHandoffSpec> exportSites(
            Collection<StaticProgram.RegionRow> skeletons) {
        Map<String, Map<String, Object>> byCapture = new LinkedHashMap<>();
        for (StaticProgram.RegionRow skeleton : skeletons) {
            for (Map<String, Object> port : skeleton.communicationPorts) {
                if (!CommunicationHandoffSpec.OUT.equals(stringValue(port.get(
                        RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE)))) {
                    continue;
                }
                Map<String, Object> site = handoffSite(port,
                        CommunicationHandoffSpec.OUT);
                if (site != null) {
                    byCapture.putIfAbsent(CommunicationCatalogContract
                            .captureKey(CommunicationHandoffSpec.OUT, port),
                            site);
                }
            }
        }
        JsonObject holder = new JsonObject();
        holder.add(CommunicationHandoffSpec.FIELD,
                toJsonTreeFast(new ArrayList<>(byCapture.values())));
        return CommunicationHandoffSpec.decode(holder);
    }

    private static Map<String, Object> handoffSite(Map<String, Object> port,
                                                   String side) {
        if (!declaredCutPort(port) || !symbolicLeafPort(port,
                stringValue(port.get("javaType")))) {
            return null;
        }
        return communicationHandoffSite(port, side);
    }

    private static Map<String, Object> communicationHandoffSite(
            Map<String, Object> port, String regionSide) {
        String capture = stringValue(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        if (capture.isEmpty()) return null;
        Map<String, Object> site = new LinkedHashMap<>();
        site.put(CommunicationHandoffSpec.SIDE, regionSide);
        site.put(CommunicationHandoffSpec.CAPTURE_KIND, capture);
        for (String field : new String[]{
                CommunicationCatalogContract.PORT_ID,
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                CommunicationCatalogContract.PORT_JAVA_TYPE,
                CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                CommunicationCatalogContract.PORT_CODEC_FIELD,
                CommunicationCatalogContract.DECLARED_CALLEE}) {
            String value = stringValue(port.get(field));
            if (!value.isEmpty()) site.put(field, value);
        }
        int unitIndex = number(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX), -1);
        int argumentIndex = number(port.get(
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1);
        if (unitIndex >= 0) {
            site.put(CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX,
                    unitIndex);
        }
        if (argumentIndex >= 0) {
            site.put(CommunicationCatalogContract.PORT_ARGUMENT_INDEX,
                    argumentIndex);
        }
        try {
            JsonObject encoded = toJsonTreeFast(site).getAsJsonObject();
            JsonObject holder = new JsonObject();
            JsonArray one = new JsonArray();
            one.add(encoded);
            holder.add(CommunicationHandoffSpec.FIELD, one);
            CommunicationHandoffSpec.decode(holder);
        } catch (RuntimeException incomplete) {
            return null;
        }
        return site;
    }

    private static boolean declaredCutPort(Map<String, Object> port) {
        return port != null
                && RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT
                .equals(stringValue(port.get("sourceKind")))
                && CommunicationCatalogContract.declaredPortId(
                stringValue(port.get("portId")));
    }

    private static void putTraceContext(Map<String, Object> target,
                                        MethodEvent event, NodeId node) {
        target.put("sourceKey", node.render());
        if (!event.requestKey.isEmpty()) {
            target.put("requestKey", event.requestKey);
        }
        if (!event.requestApi.isEmpty()) {
            target.put("requestApi", event.requestApi);
        }
    }

    private static List<Map<String, Object>> declaredSiteCaptures(
            Set<String> declaredSites, TraceIndex trace, Set<Long> calls,
            MethodEvent root) {
        if (declaredSites == null || declaredSites.isEmpty()) {
            return Collections.emptyList();
        }
        Map<Long, RuntimeEvent> entered = new LinkedHashMap<>();
        Map<String, Integer> ordinals = new LinkedHashMap<>();
        List<Map<String, Object>> captures = new ArrayList<>();
        for (RuntimeEvent event : trace.runtime(calls)) {
            if (event.invocationId <= 0L || event.siteId.isEmpty()
                    || event.declaredCallee.isEmpty()) {
                continue;
            }
            if ("CALL_SITE_ENTER".equals(event.kind)) {
                entered.put(event.invocationId, event);
                continue;
            }
            if (!"CALL_SITE_RETURN".equals(event.kind)
                    || (event.primitiveValue.isEmpty()
                    && event.objectId == 0)) {
                continue;
            }
            RuntimeEvent enter = entered.remove(event.invocationId);
            if (enter == null || !enter.siteId.equals(event.siteId)
                    || !enter.declaredCallee.equals(event.declaredCallee)) {
                continue;
            }
            String site = event.siteId + "\n" + event.declaredCallee;
            int ordinal = ordinals.merge(site, 1, Integer::sum);
            if (!declaredSites.contains(site)) continue;
            MethodEvent frame = trace.methodByCall.get(event.callId);
            captures.add(DeclaredSiteCapture.row(event.siteId,
                    event.declaredCallee, ordinal, event.primitiveValue,
                    event.seq, enter.callId, enter.invocationId,
                    root.callId, root.sourceKey,
                    frame == null ? "" : frame.sourceKey,
                    frame == null ? "" : frame.requestKey,
                    frame == null ? "" : frame.requestApi,
                    enter.objectId, enter.runtimeType, event.objectId));
        }
        return captures;
    }

    public static List<Map<String, Object>> symbolize(
            List<Map<String, Object>> ports, String occurrenceId) {
        Set<String> occurrenceOwnedCutPorts =
                occurrenceOwnedCutPortIds(ports, occurrenceId);
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> port : ports) {
            if (!declaredCutPort(port)) {
                throw new IllegalArgumentException("a region row holds a port"
                        + " that is not a declared cut port: " + port);
            }
            String owned = stringValue(port.get("occurrenceId"));
            if (!owned.isEmpty() && !owned.equals(occurrenceId)
                    || owned.isEmpty() && occurrenceOwnedCutPorts.contains(
                            stringValue(port.get("portId")))) {
                continue;
            }
            Map<String, Object> declared = declaredCutPortAction(port);
            if (declared != null) result.add(declared);
        }
        return result;
    }

    public static void declareCutPortCells(StaticProgram.RegionRow region) {
        List<Map<String, Object>> ports =
                new ArrayList<>(region.symbolicInputs);
        ports.addAll(region.outputs);
        for (Map<String, Object> port : ports) {
            if (declaredCutPort(port) && stringValue(port.get("cell")).isEmpty(
                    )) {
                String cell = RuntimeSelectedRegionFinalizer
                        .declaredCutPortCell(port);
                if (!cell.isEmpty()) port.put("cell", cell);
            }
        }
    }

    private static Set<String> occurrenceOwnedCutPortIds(
            List<Map<String, Object>> ports, String occurrenceId) {
        Set<String> result = new LinkedHashSet<>();
        for (Map<String, Object> port : ports) {
            if (declaredCutPort(port)
                    && occurrenceId.equals(stringValue(port.get(
                            "occurrenceId")))) {
                result.add(stringValue(port.get("portId")));
            }
        }
        return result;
    }

    private static Map<String, Object> declaredCutPortAction(
            Map<String, Object> port) {
        String portId = stringValue(port.get("portId"));
        String capture = stringValue(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        String definitionMethod = stringValue(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        String javaType = stringValue(port.get("javaType"));
        if (capture.isEmpty() || javaType.isEmpty()
                || definitionMethod.isEmpty()) {
            return null;
        }
        Map<String, Object> action = new LinkedHashMap<>(port);
        action.put("symbol", portId);
        action.put("observed", true);
        action.put("javaType", javaType);
        action.put("method", definitionMethod);
        action.put("rootMethod", definitionMethod);
        if (CommunicationCatalogContract.CAPTURE_METHOD_PARAMETER.equals(
                capture)) {
            int argumentIndex = number(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1);
            if (argumentIndex < 0) {
                return null;
            }
            action.put("location", "ARGUMENT");
            action.put(CommunicationCatalogContract.PORT_ARGUMENT_INDEX,
                    argumentIndex);
            action.put("index", argumentIndex);
            action.put("cell", RuntimeSelectedRegionFinalizer
                    .declaredCutPortCell(port));
        } else if (CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(
                capture)) {
            String declaredCallee = stringValue(port.get("declaredCallee"));
            int unitIndex = number(port.get(CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX), -1);
            if (declaredCallee.isEmpty() || unitIndex < 0) {
                return null;
            }
            action.put("location", "CALL_RETURN");
            action.put("cell", RuntimeSelectedRegionFinalizer
                    .declaredCutPortCell(port));
            action.put("unitIndex", unitIndex);
        } else {
            return null;
        }
        return action;
    }


    static boolean symbolicLeafPort(Map<String, Object> port,
                                    String javaType) {
        if (port != null && stringValue(port.get("symbolicDemand"))
                .startsWith("CONCRETE_")) {
            return false;
        }
        return symbolicLeafType(javaType);
    }

    private static boolean symbolicLeafType(String javaType) {
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                javaType);
        if (descriptor.length() == 1
                && "ZBCSIJFD".indexOf(descriptor.charAt(0)) >= 0) {
            return true;
        }
        if ("Ljava/lang/String;".equals(descriptor)) return true;
        int component = 0;
        while (component < descriptor.length()
                && descriptor.charAt(component) == '[') {
            component++;
        }
        return component > 0 && component + 1 == descriptor.length()
                && "ZBCSIJFD".indexOf(descriptor.charAt(component)) >= 0;
    }

    static List<Map<String, Object>> branches(
            List<Map<String, Object>> policies,
            List<RuntimeEvent> events) {
        Map<String, RuntimeEvent> firstBySite = new HashMap<>();
        for (RuntimeEvent event : events) {
            if ("BRANCH".equals(event.kind)) {
                firstBySite.putIfAbsent(event.siteId, event);
            }
        }
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> policy : policies) {
            RuntimeEvent selected = firstBySite.get(stringValue(
                    policy.get("siteId")));
            Map<String, Object> branch = new LinkedHashMap<>(policy);
            branch.put("observed", selected != null);
            branch.put("observedOutcome",
                    selected == null ? null : selected.outcome);
            branch.put("selectedOccurrence", selected == null ? 0 : 1);
            if (selected != null) {
                branch.put("selectedRuntimeEventSeq", selected.seq);
                branch.put("selectedCallId", selected.callId);
            }
            result.add(branch);
        }
        return result;
    }


    static Map<String, Object> rootSelector(
            MethodEvent root, NodeId node, String requestKey,
            String requestApi, int invocationOrdinal) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("method", root.method);
        if (root.receiverType.isEmpty()) {
            result.put("kind", "GLOBAL_INVOCATION");
        } else {
            result.put("kind", "RECEIVER_CONTEXT");
            result.put("receiverClass", root.receiverType);
        }
        result.put(CAUSAL_ANCHOR, causalAnchor(node, root.receiverAttributed,
                requestKey, requestApi));
        result.put(ROOT_INVOCATION_ORDINAL, invocationOrdinal);
        return result;
    }


    static final String CAUSAL_ANCHOR = "causalAnchor";
    static final String ROOT_INVOCATION_ORDINAL = "invocationOrdinal";
    static final String ANCHOR_REGISTERED_SOURCE = "REGISTERED_SOURCE";
    static final String ANCHOR_UNREGISTERED_SOURCE = "UNREGISTERED_SOURCE";
    static final String ANCHOR_INHERITED_CONTEXT = "INHERITED_CONTEXT";

    public static Map<String, Object> causalAnchor(NodeId node,
                                                   boolean receiverAttributed,
                                                   String requestKey,
                                                   String requestApi) {
        String sourceKey = node.render();
        Map<String, Object> anchor = new LinkedHashMap<>();
        anchor.put("sourceKey", sourceKey);
        anchor.put("kind", UNREGISTERED_SOURCE.key().equals(sourceKey)
                ? ANCHOR_UNREGISTERED_SOURCE
                : receiverAttributed
                ? ANCHOR_REGISTERED_SOURCE : ANCHOR_INHERITED_CONTEXT);
        if (requestKey != null && !requestKey.isEmpty()) {
            anchor.put("requestKey", requestKey);
        }
        if (requestApi != null && !requestApi.isEmpty()) {
            anchor.put("requestApi", requestApi);
        }
        return anchor;
    }

    private static String replayInvocationScope(
            String regionId, MethodEvent root, NodeId node) {
        return node.render() + "\n" + nonNull(regionId) + "\n"
                + nonNull(root.method);
    }

    private static NodeId recordedNode(MethodEvent root) {
        return OccurrenceAddress.parse(root.occurrenceAddress).node();
    }

    static void stateAnchorOffAddress(Map<String, Object> plan,
                                      List<Map<String, Object>> planGaps) {
        String occurrenceId = stringValue(plan.get("occurrenceId"));
        String node = OccurrenceAddress.parse(occurrenceId).node().render();
        Object selector = plan.get("rootSelector");
        Object anchor = selector instanceof Map
                ? ((Map<?, ?>) selector).get(CAUSAL_ANCHOR) : null;
        String anchored = anchor instanceof Map
                ? stringValue(((Map<?, ?>) anchor).get("sourceKey")) : "";
        String sourceKey = stringValue(plan.get("sourceKey"));
        if (node.equals(anchored) && node.equals(sourceKey)) return;
        RuntimeSelectedRegionFinalizer.planGap(planGaps,
                GapKind.TASK_UNANSWERED, GapClass.BLOCKING, occurrenceId,
                "its causal anchor names " + anchored + " and its sourceKey "
                        + sourceKey + ", but its occurrence address runs it on "
                        + node + "; the replay admits an activation by that"
                        + " address alone, so no activation can answer it");
    }

    static SourceRef sourceOf(SourceRef source) {
        return source == null ? UNREGISTERED_SOURCE : source;
    }


    public static String relationKey(NodeId node, String regionId) {
        return node.node() + "/relation/" + regionId;
    }

    static String recordedActivationKey(MethodEvent root) {
        return "ACT." + UUID.nameUUIDFromBytes((root.test + "\n"
                + root.sourceKey + "\n" + root.tid + "\n" + root.callId)
                .getBytes(StandardCharsets.UTF_8));
    }

    public static String activationId(String occurrenceId,
                               Map<String, Object> rootSelector) {
        return "ACT." + UUID.nameUUIDFromBytes((nonNull(occurrenceId) + "\n"
                + canonicalIdentity(rootSelector))
                .getBytes(StandardCharsets.UTF_8));
    }

    private static String canonicalIdentity(Object value) {
        StringBuilder text = new StringBuilder();
        appendCanonicalIdentity(text, value);
        return text.toString();
    }

    private static void appendCanonicalIdentity(StringBuilder text,
                                                Object value) {
        if (value instanceof Map<?, ?>) {
            Map<String, Object> members = new TreeMap<>();
            for (Map.Entry<?, ?> member
                    : ((Map<?, ?>) value).entrySet()) {
                members.put(String.valueOf(member.getKey()),
                        member.getValue());
            }
            text.append('{');
            for (Map.Entry<String, Object> member : members.entrySet()) {
                text.append(member.getKey()).append('=');
                appendCanonicalIdentity(text, member.getValue());
                text.append(';');
            }
            text.append('}');
        } else if (value instanceof Collection<?>) {
            text.append('[');
            for (Object item : (Collection<?>) value) {
                appendCanonicalIdentity(text, item);
                text.append(';');
            }
            text.append(']');
        } else {
            text.append(value);
        }
    }

    private static List<String> strings(Object value) {
        List<String> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (!stringValue(item).isEmpty()) {
                    result.add(stringValue(item));
                }
            }
        }
        return result;
    }



    private static <T> List<T> sorted(Collection<T> source,
                                      ToLongFunction<T> sequence) {
        List<T> result = new ArrayList<>(source);
        result.sort(Comparator.comparingLong(sequence));
        return result;
    }

    static final class Result {
        final List<Map<String, Object>> regionPlans = new ArrayList<>();
        final List<Map<String, Object>> regionCatalog = new ArrayList<>();
        final List<Map<String, Object>> planGaps = new ArrayList<>();
        final List<Map<String, Object>> runtimeInstances = new ArrayList<>();
        int staticRegionCount;

        void writeRuntimePlan(Path file) throws IOException {
            List<JsonObject> regions = new ArrayList<>();
            for (Map<String, Object> region : regionCatalog) {
                regions.add(toJsonTreeFast(region).getAsJsonObject());
            }
            List<JsonObject> gaps = new ArrayList<>();
            for (Map<String, Object> gap : planGaps) {
                gaps.add(toJsonTreeFast(gap).getAsJsonObject());
            }
            Files.createDirectories(file.toAbsolutePath().getParent());
            try (Writer output = Files.newBufferedWriter(file,
                    StandardCharsets.UTF_8)) {
                RuntimePlanArtifact.write(output, regions, gaps,
                        () -> regionPlans.stream().map(plan ->
                                toJsonTreeFast(plan).getAsJsonObject())
                                .iterator());
            }
        }

    }

    static final class MethodEvent {
        final long seq;
        final String test;
        final String threadName;
        final long tid;
        final String method;
        int objectId;
        final String receiverType;
        final long callId;
        final long parentCallId;
        final long parentSiteId;
        final long laneId;
        final long spanId;
        final long remoteParentSpanId;
        final SourceRef source;
        final String sourceKey;
        final boolean receiverAttributed;
        final String requestKey;
        final String requestApi;
        final String occurrenceAddress;
        final boolean regionFolded;
        final int window;
        MethodEvent(long seq, String test, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId,
                    long laneId, long spanId, long remoteParentSpanId,
                    SourceRef source, boolean receiverAttributed,
                    String requestKey, String requestApi,
                    String occurrenceAddress, boolean regionFolded,
                    int window) {
            this.occurrenceAddress = nonNull(occurrenceAddress);
            this.regionFolded = regionFolded;
            this.window = window;
            this.seq = seq;
            this.test = nonNull(test);
            this.threadName = nonNull(threadName);
            this.tid = tid;
            this.method = nonNull(method);
            this.objectId = objectId;
            this.receiverType = nonNull(receiverType);
            this.callId = callId;
            this.parentCallId = parentCallId;
            this.parentSiteId = parentSiteId;
            this.laneId = laneId;
            this.spanId = spanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.source = source;
            this.sourceKey = sourceOf(source).key();
            this.receiverAttributed = receiverAttributed;
            this.requestKey = nonNull(requestKey);
            this.requestApi = nonNull(requestApi);
        }

        MethodEvent unfolded() {
            return new MethodEvent(seq, test, threadName, tid, method,
                    objectId, receiverType, callId, parentCallId,
                    parentSiteId, laneId, spanId, remoteParentSpanId,
                    source, receiverAttributed, requestKey, requestApi,
                    occurrenceAddress, false, window);
        }
    }

    static final class ProtocolEvent {
        final long seq;
        final String direction;
        final String transport;
        final String correlationId;
        final String attemptId;
        final String half;
        final String threadName;
        final long tid;
        final String method;
        final long callId;
        final long invocationId;
        final String declaredCallee;
        final long laneId;
        final long spanId;
        final long remoteParentSpanId;
        final SourceRef source;
        final String requestKey;
        final String requestApi;
        final String producerEndpointId;
        final String producerEndpoint;
        ProtocolEvent(long seq, String direction, String transport,
                      String correlationId, String attemptId, String half,
                      String threadName, long tid, String method, long callId,
                      long invocationId, String declaredCallee,
                      long laneId, long spanId, long remoteParentSpanId,
                      SourceRef source, String requestKey, String requestApi,
                      String producerEndpointId, String producerEndpoint) {
            this.seq = seq;
            this.direction = nonNull(direction);
            this.transport = nonNull(transport);
            this.correlationId = nonNull(correlationId);
            this.attemptId = nonNull(attemptId);
            this.half = nonNull(half);
            this.threadName = nonNull(threadName);
            this.tid = tid;
            this.method = nonNull(method);
            this.callId = callId;
            this.invocationId = invocationId;
            this.declaredCallee = nonNull(declaredCallee);
            this.laneId = laneId;
            this.spanId = spanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.source = source;
            this.requestKey = nonNull(requestKey);
            this.requestApi = nonNull(requestApi);
            this.producerEndpointId = nonNull(producerEndpointId);
            this.producerEndpoint = nonNull(producerEndpoint);
        }

        String exchangeLeg() {
            String result = correlationId;
            if (!attemptId.isEmpty()) result += "\n" + attemptId;
            if (!half.isEmpty()) result += "\n" + half;
            return result;
        }
    }

    static final class RuntimeEvent {
        final long seq;
        final String kind;
        final String method;
        final long callId;
        final long invocationId;
        final String siteId;
        final String declaredCallee;
        final int argumentIndex;
        final String runtimeType;
        int objectId;
        final String primitiveValue;
        final Boolean outcome;
        final Integer successorIndex;
        final String branchKind;
        final String switchCaseKeys;

        RuntimeEvent(long seq, String kind, String method, long callId,
                     long invocationId, String siteId,
                     String declaredCallee, int argumentIndex,
                     String runtimeType, int objectId, String primitiveValue,
                     Boolean outcome, Integer successorIndex, String branchKind,
                     String switchCaseKeys) {
            this.seq = seq;
            this.kind = nonNull(kind);
            this.method = nonNull(method);
            this.callId = callId;
            this.invocationId = invocationId;
            this.siteId = nonNull(siteId);
            this.declaredCallee = nonNull(declaredCallee);
            this.argumentIndex = argumentIndex;
            this.runtimeType = nonNull(runtimeType);
            this.objectId = objectId;
            this.primitiveValue = nonNull(primitiveValue);
            this.outcome = outcome;
            this.successorIndex = successorIndex;
            this.branchKind = nonNull(branchKind);
            this.switchCaseKeys = nonNull(switchCaseKeys);
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
        int receiverObjectId;
        int valueObjectId;
        final String primitiveValue;
        int version;

        FieldAccessEvent(long seq, String kind, String method, long callId,
                         int unitIndex, String siteId, String field,
                         int receiverObjectId, int valueObjectId,
                         String primitiveValue) {
            this.seq = seq;
            this.kind = nonNull(kind);
            this.method = nonNull(method);
            this.callId = callId;
            this.unitIndex = unitIndex;
            this.siteId = unitIndex >= 0 && !this.method.isEmpty()
                    ? SiteId.of(this.method, unitIndex) : nonNull(siteId);
            this.field = nonNull(field);
            this.receiverObjectId = receiverObjectId;
            this.valueObjectId = valueObjectId;
            this.primitiveValue = nonNull(primitiveValue);
        }
    }

    private static final class LongLongMap {
        private static final long AMBIGUOUS = Long.MIN_VALUE;
        private long[] keys = new long[1 << 16];
        private long[] values = new long[1 << 16];
        private int size;

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
        private final Map<Long, MethodEvent> methodByCall =
                new LinkedHashMap<>();
        private final Map<String, List<MethodEvent>> methodsByName =
                new LinkedHashMap<>();
        private final Map<Long, List<Long>> children = new LinkedHashMap<>();
        private final Map<Long, List<RuntimeEvent>> runtimeByCall =
                new LinkedHashMap<>();
        private final Map<Long, List<FieldAccessEvent>> fieldsByCall =
                new HashMap<>();
        private final Map<Long, List<ProtocolEvent>> protocolByCall =
                new HashMap<>();
        private final LongLongMap eventCallIdBySeq = new LongLongMap();

        private TraceIndex(Collection<MethodEvent> methodEvents,
                           Collection<RuntimeEvent> runtimeEvents,
                           Collection<FieldAccessEvent> fieldEvents,
                           Collection<ProtocolEvent> protocolEvents) {
            for (MethodEvent event : sorted(methodEvents,
                    value -> value.seq)) {
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
            for (ProtocolEvent event : sorted(protocolEvents,
                    value -> value.seq)) {
                protocolByCall.computeIfAbsent(event.callId,
                        ignored -> new ArrayList<>()).add(event);
                registerEventCall(event.seq, event.callId);
            }
            Map<String, Integer> stores = new HashMap<>();
            for (FieldAccessEvent event : sorted(fieldEvents,
                    value -> value.seq)) {
                fieldsByCall.computeIfAbsent(event.callId,
                        ignored -> new ArrayList<>()).add(event);
                registerEventCall(event.seq, event.callId);
                event.version = stores.merge(event.field + "\n"
                        + event.receiverObjectId, "FIELD_WRITE".equals(
                                event.kind) ? 1 : 0, Integer::sum);
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
                if (method != null) result.add(method.method);
            }
            return result;
        }

        private Set<Long> enclosingCalls(long callId) {
            Set<Long> result = new LinkedHashSet<>();
            MethodEvent current = methodByCall.get(callId);
            while (current != null && result.add(current.callId)) {
                current = methodByCall.get(current.parentCallId);
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

        private List<FieldAccessEvent> reads(Set<Long> calls) {
            List<FieldAccessEvent> result = new ArrayList<>();
            for (Long call : calls) {
                for (FieldAccessEvent event : fieldsByCall.getOrDefault(call,
                        Collections.<FieldAccessEvent>emptyList())) {
                    if ("FIELD_READ".equals(event.kind)) result.add(event);
                }
            }
            result.sort(Comparator.comparingLong(value -> value.seq));
            return result;
        }

        private MethodEvent selectedTargetContext(
                MethodEvent root, Set<Long> calls,
                List<Map<String, Object>> branches) {
            for (Map<String, Object> branch : branches) {
                if (!Boolean.TRUE.equals(branch.get("failureTarget"))) {
                    continue;
                }
                long seq = longNumber(
                        branch.get("selectedRuntimeEventSeq"), -1L);
                long callId = eventCallIdBySeq.uniqueValue(seq);
                MethodEvent selected = methodByCall.get(callId);
                if (selected != null && calls.contains(callId)) {
                    return selected;
                }
            }
            return root;
        }

    }
}
