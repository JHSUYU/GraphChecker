package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.ToNumberPolicy;
import com.google.gson.reflect.TypeToken;
import edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import edu.uva.liftlab.graphchecker.concolic.AutomaticRegionEdge;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.concolic.RecordedReadFrom;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;

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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.UUID;
import java.util.function.ToLongFunction;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.GZIPInputStream;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.longNumber;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.number;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.rows;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.stringValue;

/** Binds region skeletons and refined region state to concrete activations. */
final class RuntimeRegionPlanner {
    private static final Type ROW =
            new TypeToken<Map<String, Object>>() { }.getType();
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();
    private static final Pattern FIELD = Pattern.compile(
            "^<[^:]+:\\s+([^()<>]+)\\s+[^\\s()>]+>$");
    private static final Pattern METHOD_PARAMETER_CELL = Pattern.compile(
            "^(<.+>)\\.param([0-9]+):(.+)$");
    private static final Pattern STATIC_SITE = Pattern.compile(
            "^(<.*>)#u([0-9]+)$");
    /** Logical source of a workload whose tracing never registered one. */
    static final SourceRef UNREGISTERED_SOURCE = new SourceRef(
            "TEST_DRIVER", "WORKLOAD", "workload/unregistered", 0L);
    /** Authority of one recorded exchange link between two occurrences. */
    static final String DELIVERY_LINK_AUTHORITY =
            "RECORDED_EXCHANGE_OCCURRENCE_LINK_V1";
    /** A recorded activation this stage could not attribute to a source. */
    static final String GAP_RUNTIME_SOURCE_UNSTAMPED =
            "RUNTIME_ACTIVATION_SOURCE_UNSTAMPED";
    /** Skeleton field naming why the admission half selected this region. */
    static final String ADMISSION_BASIS = "admissionBasis";
    /** Admission by the recorded version store of an enumerated location. */
    static final String SHARED_LOCATION_DEMAND_ADMISSION =
            "SHARED_LOCATION_DEMAND_V1";
    /** Skeleton field: the region whose demand admitted this one. */
    static final String DEMANDED_BY_REGIONS = "demandedByRegionIds";
    /** Skeleton field: the enumerated locations that demand covers. */
    static final String DEMANDED_SHARED_LOCATIONS =
            "demandedSharedLocations";
    /** The protocol server stub a run entered as its own region root. */
    static final String COMMUNICATION_ENTRY = "COMMUNICATION_ENTRY";
    private RuntimeRegionPlanner() {
    }

    static Result planSkeletonGraph(File skeletonFile,
                                    List<MethodEvent> methods) {
        return planSkeletonGraph(skeletonFile, methods,
                Collections.<RuntimeEvent>emptyList(),
                Collections.<ProtocolEvent>emptyList());
    }

    /** Binds static region skeletons to the activations a run performed. */
    static Result planSkeletonGraph(File skeletonFile,
                                    List<MethodEvent> methods,
                                    List<RuntimeEvent> runtimeEvents,
                                    List<ProtocolEvent> protocolEvents) {
        List<StaticProgram.RegionRow> skeletons = StaticProgram.regionRows(
                read(skeletonFile),
                RuntimeSelectedRegionFinalizer.SKELETON_KIND, skeletonFile);
        // The recorded call sites are part of this index, not an extra: the
        // across-cut attribution below asks which call site opened a frame,
        // and that answer lives in the CALL_SITE_ENTER events.
        TraceIndex trace = new TraceIndex(methods, runtimeEvents == null
                ? Collections.<RuntimeEvent>emptyList() : runtimeEvents,
                Collections.emptyList(), protocolEvents);
        Result result = new Result();
        result.staticRegionCount = skeletons.size();
        Set<String> skeletonRoots = new LinkedHashSet<>();
        for (StaticProgram.RegionRow skeleton : skeletons) {
            String authority = skeleton.rootAuthority;
            if ((!validRootAuthority(authority)
                    && !COMMUNICATION_ENTRY.equals(authority)
                    && !"STATE_WRITER_ENTRY".equals(authority))
                    || CausynthStaticFacts.constructor(
                            skeleton.rootMethod)) {
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
        // The communication endpoints are bound after the execution-context
        // roots, so a receiver nested in one of them sees its owner already
        // claimed.
        for (boolean endpoints : new boolean[]{false, true}) {
            for (StaticProgram.RegionRow skeleton : skeletons) {
                if (endpoints != COMMUNICATION_ENTRY.equals(
                        skeleton.rootAuthority)
                        || !endpoints && "AUTHORITY_ENVELOPE".equals(
                                skeleton.selection)) {
                    continue;
                }
                for (MethodEvent root : trace.methods(skeleton.rootMethod)) {
                    Set<String> observed = trace.methodNames(
                            trace.subtree(root.callId));
                    if (Collections.disjoint(observed,
                            skeleton.anchorMethods)) {
                        continue;
                    }
                    addSkeletonActivation(activationByCall, skeleton,
                            root, trace);
                }
            }
        }
        stampActivationContainment(activationByCall, trace);
        result.runtimeInstances.addAll(activationByCall.values());
        stampRecordedExchanges(result, trace, protocolEvents);
        return result;
    }



    /** Stamps every planned activation with the exchanges its own transport
     * hooks recorded, and links an exporting occurrence to the occurrence
     * that received the same exchange. */
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
        for (ProtocolEvent event : protocolEvents == null
                ? Collections.<ProtocolEvent>emptyList() : protocolEvents) {
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

        Map<String, List<Map<String, Object>>> receivedBy =
                new LinkedHashMap<>();
        Map<String, List<Map<String, Object>>> exportedByActivation =
                new LinkedHashMap<>();
        for (Map<String, Object> activation : result.runtimeInstances) {
            List<Map<String, Object>> exported = new ArrayList<>();
            for (ProtocolEvent event : protocolByActivationRoot.getOrDefault(
                    longNumber(activation.get("rootCallId"), -1L),
                    Collections.<ProtocolEvent>emptyList())) {
                if (event.correlationId.isEmpty()) continue;
                Map<String, Object> row = new LinkedHashMap<>();
                row.put("exchangeLeg", event.exchangeLeg());
                row.put("eventSeq", event.seq);
                row.put("attemptId", event.attemptId);
                row.put("half", event.half);
                row.put("transport", event.transport);
                row.put("requestKey", event.requestKey);
                row.put("requestApi", event.requestApi);
                // The hook runs inside the transport.
                String callSiteId = trace.callSiteId(event.callId,
                        event.invocationId);
                if (callSiteId.isEmpty()) {
                    callSiteId = trace.entrySiteId(event.callId);
                }
                row.put("callSiteId", callSiteId);
                row.put("declaredCallee", event.declaredCallee);
                if ("SEND".equals(event.direction)) {
                    exported.add(row);
                } else if ("RECEIVE".equals(event.direction)) {
                    Map<String, Object> receipt = new LinkedHashMap<>(row);
                    receipt.put("activation", activation);
                    receivedBy.computeIfAbsent(event.exchangeLeg(),
                            ignored -> new ArrayList<>()).add(receipt);
                }
            }
            exportedByActivation.put(stringValue(activation.get(
                    "activationId")),
                    exported);
        }
        for (Map<String, Object> activation : result.runtimeInstances) {
            for (Map<String, Object> exported
                    : exportedByActivation.getOrDefault(
                    stringValue(activation.get("activationId")),
                    Collections.<Map<String, Object>>emptyList())) {
                linkOneDelivery(result, activation, exported, receivedBy);
            }
        }
    }

    /** The retained loops of one occurrence: the region's declared rows whose
     * enclosing method this occurrence actually holds. */
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

    /** Exact executions of configured-source hook sites inside one occurrence.
     */
    private static List<JsonObject> configuredSourcePhases(
            StaticProgram.RegionRow region, String occurrenceId,
            long activationRootCallId, TraceIndex trace) {
        Map<String, ConfiguredSourcePhaseContract.Declaration> bySite =
                region.sourcePhasesBySite();
        if (bySite.isEmpty()) return Collections.emptyList();
        Set<Long> activationCalls = trace.subtree(activationRootCallId);
        List<RuntimeEvent> ordered = new ArrayList<>(
                trace.runtime(activationCalls));
        ordered.sort(Comparator.comparingLong(event -> event.seq));
        Map<String, Integer> ordinals = new LinkedHashMap<>();
        List<JsonObject> result = new ArrayList<>();
        for (RuntimeEvent event : ordered) {
            if (!"CALL_SITE_ENTER".equals(event.kind)) continue;
            ConfiguredSourcePhaseContract.Declaration declaration =
                    bySite.get(event.siteId);
            if (declaration == null) continue;
            if (!declaration.method().equals(event.method)
                    || event.seq <= 0L || event.callId <= 0L
                    || event.invocationId <= 0L) {
                throw new IllegalArgumentException(
                        "configured-source phase event differs "
                        + "from exact static site " + declaration.siteId());
            }
            int ordinal = ordinals.merge(declaration.identity(), 1,
                    Integer::sum);
            List<Long> enclosingCallIds = new ArrayList<>();
            MethodEvent owner = trace.methodByCall.get(event.callId);
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
                        "configured-source phase event "
                        + event.seq + " is not enclosed by activation root "
                        + activationRootCallId);
            }
            result.add(ConfiguredSourcePhaseContract.occurrence(
                    declaration, occurrenceId, ordinal, event.seq,
                    event.callId, event.invocationId,
                    event.declaredCallee, enclosingCallIds));
        }
        return result;
    }

    /**
     * Narrows a producer's source catalog from its long-lived activation root
     * to the exact dynamic call(s) that produced the selected output version.
     *
     * <p>A service-loop occurrence can contain several calls to the same
     * producer.  Those calls are useful while selecting a version, but once
     * the output closure names its exact runtime call they are not alternative
     * symbolic roots.  Keeping them here would attach unrelated rotations to
     * one output relation.  The retained per-site ordinals are rebuilt because
     * replay counts entries within this bounded catalog, not within the
     * discarded parent activation.</p>
     */
    static void boundConfiguredSourcePhasesToSelectedOutputCalls(
            Map<String, Object> plan, Map<String, Object> goal) {
        if (plan == null || goal == null
                || !plan.containsKey(ConfiguredSourcePhaseContract.PLAN_FIELD)) {
            return;
        }
        Set<Long> selectedCalls = new LinkedHashSet<>();
        Map<String, Object> closure = row(goal.get(OutputClosureContract.FIELD));
        for (Map<String, Object> member : rows(closure.get("members"))) {
            Map<String, Object> slice = row(member.get("slice"));
            long selected = longNumber(
                    slice.get("selectedRuntimeCallId"), -1L);
            long observed = longNumber(
                    slice.get("observedDefinitionCallId"), -1L);
            if (selected > 0L) selectedCalls.add(selected);
            if (observed > 0L) selectedCalls.add(observed);
            for (Map<String, Object> version : rows(
                    slice.get(BOUNDED_VERSION_SCOPES))) {
                long versionCall = longNumber(
                        version.get("selectedRuntimeCallId"), -1L);
                if (versionCall > 0L) selectedCalls.add(versionCall);
            }
        }
        // A closure without an exact call gives no authority to narrow the
        // activation catalog.  Leave it intact so missing evidence stays
        // visible to the later admission checks.
        if (selectedCalls.isEmpty()) return;

        JsonElement encoded = toJsonTreeFast(plan.get(
                ConfiguredSourcePhaseContract.PLAN_FIELD));
        List<ConfiguredSourcePhaseContract.Occurrence> phases =
                ConfiguredSourcePhaseContract.occurrencesOf(encoded, true);
        JsonArray rows = encoded.getAsJsonArray();
        Map<String, Integer> ordinals = new LinkedHashMap<>();
        List<JsonObject> bounded = new ArrayList<>();
        for (int index = 0; index < phases.size(); index++) {
            ConfiguredSourcePhaseContract.Occurrence phase =
                    phases.get(index);
            boolean enclosed = false;
            for (Long callId : phase.enclosingCallIds()) {
                if (selectedCalls.contains(callId)) {
                    enclosed = true;
                    break;
                }
            }
            if (!enclosed) continue;
            String identity = phase.phase().name() + "\n"
                    + phase.sourceId() + "\n" + phase.siteId();
            int ordinal = ordinals.merge(identity, 1, Integer::sum);
            JsonObject retained = rows.get(index).getAsJsonObject().deepCopy();
            retained.addProperty("baselineOrdinal", ordinal);
            retained.addProperty("phaseId",
                    ConfiguredSourcePhaseContract.phaseId(
                            phase.sourceOccurrenceId(), phase.siteId(),
                            phase.phase(), ordinal));
            bounded.add(retained);
        }
        if (bounded.isEmpty()) {
            plan.remove(ConfiguredSourcePhaseContract.PLAN_FIELD);
            return;
        }
        JsonArray strict = new JsonArray();
        for (JsonObject phase : bounded) strict.add(phase.deepCopy());
        ConfiguredSourcePhaseContract.occurrencesOf(strict, true);
        plan.put(ConfiguredSourcePhaseContract.PLAN_FIELD, bounded);
    }

    private static void linkOneDelivery(
            Result result, Map<String, Object> activation,
            Map<String, Object> exported,
            Map<String, List<Map<String, Object>>> receivedBy) {
        String activationId = stringValue(activation.get("activationId"));
        List<Map<String, Object>> deliveries = new ArrayList<>();
        for (Map<String, Object> delivery : receivedBy.getOrDefault(
                stringValue(exported.get("exchangeLeg")),
                Collections.<Map<String, Object>>emptyList())) {
            Map<String, Object> candidate = (Map<String, Object>)
                    delivery.get("activation");
            if (candidate != null && !activationId.equals(
                    stringValue(candidate.get("activationId")))) {
                deliveries.add(delivery);
            }
        }
        if (deliveries.isEmpty()) return;
        // Replay is distributed and therefore not required to reproduce one
        // receiver instance.
        Set<String> emitted = new LinkedHashSet<>();
        for (Map<String, Object> delivery : deliveries) {
            Map<String, Object> toActivation = (Map<String, Object>)
                    delivery.get("activation");
            String requestKey = stringValue(exported.get("requestKey"));
            if (!requestKey.equals(stringValue(
                    delivery.get("requestKey")))) {
                continue;
            }
            String identity = activationId + "\n"
                    + stringValue(toActivation.get("activationId")) + "\n"
                    + stringValue(exported.get("exchangeLeg")) + "\n"
                    + stringValue(exported.get("callSiteId"));
            if (!emitted.add(identity)) continue;
            Map<String, Object> link = new LinkedHashMap<>();
            link.put("schemaVersion", 3);
            link.put("kind", "RUNTIME_OCCURRENCE_LINK");
            link.put("linkKind", "SERVER_ENTRY");
            link.put("fromActivationId", activationId);
            link.put("fromRegionId", stringValue(activation.get("regionId")));
            link.put("fromRootCallId", activation.get("rootCallId"));
            link.put("callSiteId", stringValue(exported.get("callSiteId")));
            link.put("toActivationId",
                    stringValue(toActivation.get("activationId")));
            link.put("toRegionId", stringValue(toActivation.get("regionId")));
            link.put("toRootCallId", toActivation.get("rootCallId"));
            link.put("exchangeLeg", stringValue(exported.get("exchangeLeg")));
            link.put("senderEventSeq", exported.get("eventSeq"));
            link.put("receiverEventSeq", delivery.get("eventSeq"));
            link.put("attemptId", stringValue(exported.get("attemptId")));
            link.put("direction", stringValue(exported.get("half")));
            link.put("transport", stringValue(exported.get("transport")));
            link.put("requestKey", requestKey);
            link.put("requestApi", stringValue(exported.get("requestApi")));
            link.put("crossThread",
                    !String.valueOf(activation.get("threadId")).equals(
                            String.valueOf(toActivation.get("threadId"))));
            link.put("authority", DELIVERY_LINK_AUTHORITY);
            result.occurrenceLinks.add(link);
        }
    }

    /** Attributes the two transport hooks bracketing one synchronous server
     * invocation to the exact planned handler activation between them. */
    private static void stampSynchronousServerTransactions(
            List<Map<String, Object>> activations, TraceIndex trace,
            List<ProtocolEvent> protocolEvents,
            Map<Long, List<ProtocolEvent>> protocolByActivationRoot) {
        Map<String, List<ProtocolEvent>> requestReceives =
                new LinkedHashMap<>();
        Map<String, List<ProtocolEvent>> responseSends =
                new LinkedHashMap<>();
        Map<String, List<ProtocolEvent>> requestSends =
                new LinkedHashMap<>();
        Map<String, List<ProtocolEvent>> responseReceives =
                new LinkedHashMap<>();
        for (ProtocolEvent event : protocolEvents == null
                ? Collections.<ProtocolEvent>emptyList() : protocolEvents) {
            if (event.correlationId.isEmpty()) continue;
            String transaction = protocolTransactionKey(event);
            if ("RECEIVE".equals(event.direction)
                    && "REQUEST".equals(event.half)) {
                requestReceives.computeIfAbsent(transaction,
                        ignored -> new ArrayList<>()).add(event);
            } else if ("SEND".equals(event.direction)
                    && "REQUEST".equals(event.half)) {
                requestSends.computeIfAbsent(transaction,
                        ignored -> new ArrayList<>()).add(event);
            } else if ("SEND".equals(event.direction)
                    && "RESPONSE".equals(event.half)) {
                responseSends.computeIfAbsent(transaction,
                        ignored -> new ArrayList<>()).add(event);
            } else if ("RECEIVE".equals(event.direction)
                    && "RESPONSE".equals(event.half)) {
                responseReceives.computeIfAbsent(transaction,
                        ignored -> new ArrayList<>()).add(event);
            }
        }
        // A synchronous transport commonly receives the response after the
        // deep transport invocation that emitted the request has returned.
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

    /** Exact dynamic nesting between planned coarse occurrences. */
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
            TraceIndex trace) {
        Set<Long> calls = trace.subtree(root.callId);
        Set<String> allowed = new LinkedHashSet<>(skeleton.methods);
        calls.removeIf(call -> {
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
        activation.put("activationId", activationId(root));
        activation.put("regionId", skeleton.regionId);
        activation.put("rootCallId", root.callId);
        activation.put("rootMethod", root.method);
        activation.put("rootAuthority", skeleton.rootAuthority);
        activation.put("anchorMethod", observedAnchors.get(0));
        activation.put("anchorMethods", observedAnchors);
        activation.put("selection", skeleton.selection);
        // Present only when the admission half declared one, so a region
        // admitted by target reachability - every region this tree plans
        // today - produces exactly the seed it produced before.
        copyIfPresent(activation, skeleton.json, ADMISSION_BASIS);
        copyIfPresent(activation, skeleton.json, DEMANDED_BY_REGIONS);
        copyIfPresent(activation, skeleton.json, DEMANDED_SHARED_LOCATIONS);
        activation.put("test", root.test);
        activation.put("thread", root.threadName);
        activation.put("threadId", root.tid);
        putTraceContext(activation, root,
                activationSource(root, stampedSources(calls, trace)));
        activation.put("callIds", new ArrayList<>(calls));
        activation.put("observedMethods", new ArrayList<>(observed));
        activation.put(
                RuntimeSelectedRegionFinalizer
                        .OBSERVED_COMMUNICATION_CAPTURES,
                observedCommunicationCaptures(skeleton, calls, trace));
        activationByCall.put(root.callId, activation);
    }

    /** Exact configured cut captures that executed in this activation. */
    private static List<Map<String, Object>> observedCommunicationCaptures(
            StaticProgram.RegionRow skeleton, Set<Long> calls,
            TraceIndex trace) {
        List<RuntimeEvent> events = trace.runtime(calls);
        List<Map<String, Object>> observed = new ArrayList<>();
        for (Map<String, Object> port : skeleton.communicationPorts) {
            String side = stringValue(port.get(
                    RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE));
            String portId = stringValue(port.get(
                    CommunicationCatalogContract.PORT_ID));
            String direction = stringValue(port.get(
                    CommunicationCatalogContract.PORT_DIRECTION));
            if (!("IN".equals(side) || "OUT".equals(side))
                    || portId.isEmpty() || direction.isEmpty()) {
                continue;
            }
            for (RuntimeEvent event : events) {
                if (!communicationCaptureEvent(port, event)) continue;
                Map<String, Object> capture = new LinkedHashMap<>();
                capture.put("side", side);
                capture.put("portId", portId);
                capture.put("direction", direction);
                capture.put("transport", port.get(
                        CommunicationCatalogContract.TRANSPORT));
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

    /** Binds each capture to the boundary of its matching logical exchange. */
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
            long laneId = longNumber(activation.get("laneId"), -1L);
            for (ProtocolEvent event : protocolEvents == null
                    ? Collections.<ProtocolEvent>emptyList()
                    : protocolEvents) {
                if (laneId > 0L && event.laneId == laneId
                        && !protocol.contains(event)) {
                    protocol.add(event);
                }
            }
            for (Map<String, Object> capture : rows(activation.get(
                    RuntimeSelectedRegionFinalizer
                            .OBSERVED_COMMUNICATION_CAPTURES))) {
                String side = stringValue(capture.get("side"));
                String direction = stringValue(capture.get("direction"));
                String transport = stringValue(capture.get("transport"));
                long capturedAt = longNumber(capture.get("eventSeq"), -1L);
                ProtocolEvent boundary = null;
                for (ProtocolEvent event : protocol) {
                    if (!transport.equals(event.transport)
                            || !direction.equals(event.half)
                            || !("OUT".equals(side)
                            ? "SEND".equals(event.direction)
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
                    // A logical exchange may use several physical frames.
                    // Rewind from the adjacent frame to that exchange's
                    // first frame, where its carried values entered.
                    String exchange = boundary.exchangeLeg();
                    for (ProtocolEvent event : protocol) {
                        if (transport.equals(event.transport)
                                && direction.equals(event.half)
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

    /** Ranks how strong one region selection is when two fragments merge. */
    static int selectionRank(String selection) {
        if (selection != null && selection.startsWith("EXCEPTION")) {
            return 3;
        }
        if (selection != null && selection.startsWith("PROTOCOL")) {
            return 2;
        }
        return 1;
    }

    private static boolean validRootAuthority(String authority) {
        return "THREAD_ENTRY".equals(authority)
                || "TASK_ENTRY".equals(authority)
                || "MAIN_ENTRY".equals(authority)
                || "EXPLICIT_FAULT_ENTRY".equals(authority)
                // The annotated target's own activation, planned as a root
                // because no execution-context entry statically reaches it.
                || "FAILURE_TARGET_ENTRY".equals(authority);
    }

    /** Builds the refined-flow index once from already parsed rows. */
    static RefinedFlowIndex buildFlowIndex(
            List<Map<String, Object>> rows, File source) {
        return RefinedFlowIndex.build(rows, source);
    }

    /** In-memory planning entry point. {@code regionSource} and {@code
     * regionEdgeSource} only label diagnostics; rows must already be in the
     * exact JSONL value domain the file readers would produce. */
    static Result plan(List<Map<String, Object>> regions,
                       List<Map<String, Object>> regionEdges,
                       RefinedFlowIndex refinedFlow,
                       String regionSource, String regionEdgeSource,
                       Collection<Map<String, Object>> runtimeSeeds,
                       List<MethodEvent> methods,
                       List<RuntimeEvent> runtimeEvents,
                       List<FieldAccessEvent> fieldEvents,
                       List<ProtocolEvent> protocolEvents) {
        return plan(regions, regionEdges, refinedFlow, regionSource,
                regionEdgeSource, runtimeSeeds, methods, runtimeEvents,
                fieldEvents, protocolEvents, declaredLoopBounds(regions));
    }

    /** The campaign policy the planned rows themselves declare. */
    static LoopBoundPolicy declaredLoopBounds(
            List<Map<String, Object>> regions) {
        Map<String, Integer> declared = new TreeMap<>();
        for (Map<String, Object> region : regions == null
                ? Collections.<Map<String, Object>>emptyList() : regions) {
            for (Map<String, Object> loop : rows(region.get(
                    RuntimeSelectedRegionFinalizer.RETAINED_LOOPS))) {
                Object stated = loop.get(LoopBoundPolicy.LOOP_BODY_BOUND);
                // Absent is not zero and not the default: a row that states
                // no bound declares nothing, and reading the default out of
                // it would turn silence into a declaration.
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
        // README LOOP-1: a declared bound that happens to equal the inherited
        // default is still a declaration.
        return LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS, declared);
    }

    static Result plan(List<Map<String, Object>> regions,
                       List<Map<String, Object>> regionEdges,
                       RefinedFlowIndex refinedFlow,
                       String regionSource, String regionEdgeSource,
                       Collection<Map<String, Object>> runtimeSeeds,
                       List<MethodEvent> methods,
                       List<RuntimeEvent> runtimeEvents,
                       List<FieldAccessEvent> fieldEvents,
                       List<ProtocolEvent> protocolEvents,
                       LoopBoundPolicy loopBound) {
        TraceIndex trace = new TraceIndex(methods, runtimeEvents,
                fieldEvents, protocolEvents);
        Result result = new Result();
        result.staticRegionCount = regions.size();
        Map<String, StaticProgram.RegionRow> regionById =
                new LinkedHashMap<>();
        for (StaticProgram.RegionRow region : StaticProgram.regionRows(
                regions, "SYMBOLIC_REGION", regionSource)) {
            if (!"RUNTIME_REFINED_DATAFLOW".equals(region.graphKind)) {
                throw new IllegalArgumentException(
                        "region was not planned from the refined graph: "
                                + regionSource);
            }
            declareCutPortCells(region);
            regionById.put(region.regionId, region);
        }
        // The entry activation's goal - an activation planned as one
        // relation has one answer, so nothing is chosen there.
        Map<String, Map<String, Object>> goalByOccurrence =
                new LinkedHashMap<>();
        Map<String, Map<String, Object>> planByOccurrence =
                new LinkedHashMap<>();
        OccurrenceMinter minter = new OccurrenceMinter();
        Map<String, String> exactPorts = new LinkedHashMap<>();
        for (Map<String, Object> seed : runtimeSeeds == null
                ? Collections.<Map<String, Object>>emptyList()
                : runtimeSeeds) {
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
            Set<Long> calls = longNumbers(seed.get("callIds"));
            if (calls.isEmpty()) calls = trace.subtree(rootCallId);
            Set<String> observedMethods = new LinkedHashSet<>(
                    strings(seed.get("observedMethods")));
            if (observedMethods.isEmpty()) {
                observedMethods.addAll(trace.methodNames(calls));
            }
            observedMethods.retainAll(allowedMethods);
            List<Map<String, Object>> branches = branches(
                    region.branchPolicies, trace.runtime(calls));
            boolean target = region.selection .startsWith("EXCEPTION")
                    && observedFailureTargetActivation(branches);
            MethodEvent semanticContext = target
                    ? trace.selectedTargetContext(root, calls, branches)
                    : root;
            // The same upgrade the activation seed was stamped with, applied
            // to the same call set, so the identity this stage mints and the
            // one the finalizer minted are one answer and not two.
            List<SourceRef> stamped = stampedSources(calls, trace);
            SourceRef rootSource = activationSource(root, stamped);
            SourceRef source = semanticContext.source != null
                    ? semanticContext.source : rootSource;
            // Activation identity is minted before any port, edge, demand or
            // retention decision of this activation is read.
            int occurrenceIndex = minter.reserveOrdinal(source.key(),
                    regionId);
            String occurrenceId = minter.mint(regionId, rootCallId,
                    source.key(), occurrenceIndex);
            requireFinalizedOccurrence(seed, occurrenceId);
            Set<String> retainedOccurrences = new LinkedHashSet<>(
                    region.runtimeOccurrenceIds);
            if (retainedOccurrences.isEmpty()) {
                throw new IllegalArgumentException("runtime-refined region "
                        + "has no retained activation seeds: " + regionId);
            }
            if (!retainedOccurrences.contains(occurrenceId)) continue;
            // Runtime fixes the activation and the concrete sink.
            Map<String, Object> activation = new LinkedHashMap<>();
            activation.put("schemaVersion", 3);
            activation.put("kind", "RUNTIME_REGION_ACTIVATION");
            activation.put("activationId", activationId(root));
            activation.put("regionId", region.regionId);
            activation.put("occurrenceId", occurrenceId);
            activation.put("rootCallId", root.callId);
            activation.put("rootMethod", root.method);
            activation.put("selection", region.selection);
            activation.put("test", root.test);
            activation.put("thread", root.threadName);
            activation.put("threadId", root.tid);
            putTraceContext(activation, root);
            activation.put("callIds", new ArrayList<>(calls));
            activation.put("observedMethods",
                    new ArrayList<>(observedMethods));
            result.runtimeInstances.add(activation);
            // A run that registered no source is a named gap, not an
            // authority.
            String stampedAuthority = semanticContext.source != null
                    ? "EXPLICIT_TRACE_SOURCE"
                    : stamped.size() == 1 ? UPGRADED_SOURCE_AUTHORITY
                    : GAP_RUNTIME_SOURCE_UNSTAMPED;
            OccurrenceMinter.bindOccurrence(region.json, rootCallId,
                    occurrenceId);
            OccurrenceMinter.bindEdges(regionEdges, regionId, rootCallId,
                    occurrenceId);
            registerExactPorts(region, occurrenceId, exactPorts);
            List<Map<String, Object>> occurrenceSymbolize = symbolize(
                    region.symbolicInputs, occurrenceId, trace);
            List<Map<String, Object>> occurrenceBranches = branches;
            Set<String> occurrenceObserved =
                    new LinkedHashSet<>(observedMethods);
            // Static discovery supplies the candidate region; this concrete
            // activation supplies the methods worth slicing in the current
            // wave.
            Set<String> occurrenceMethods =
                    new LinkedHashSet<>(occurrenceObserved);
            if (allowedMethods.contains(root.method)) {
                occurrenceMethods.add(root.method);
            }
            boolean occurrenceTarget = target;
            long targetBoundaryUpperSeq = occurrenceTarget
                    ? targetBoundaryUpperSeq(occurrenceBranches, seed) : -1L;
            ReturnSlice targetSlice = occurrenceTarget
                    ? refinedFlow.targetReachSlice(regionId, occurrenceId,
                    occurrenceMethods, region.symbolicInputs, region.outputs,
                    region.branchPolicies, root.method, targetBoundaryUpperSeq)
                    : null;
            if (targetSlice != null) {
                occurrenceSymbolize = filterByText(occurrenceSymbolize,
                        "symbol", targetSlice.inputPorts);
                occurrenceBranches = filterByText(occurrenceBranches,
                        "siteId", targetSlice.branchSites);
                addMaterializationMethods(targetSlice.methods,
                        occurrenceSymbolize, occurrenceMethods);
                occurrenceObserved.retainAll(targetSlice.methods);
                occurrenceMethods = new LinkedHashSet<>(targetSlice.methods);
            }
            List<String> projectionBlockers =
                    occurrenceTarget && targetSlice != null
                            ? targetProjectionBlockers(
                            occurrenceBranches, seed)
                            : Collections.emptyList();
            Map<String, Object> goal = new LinkedHashMap<>();
            goal.put("goalId", (occurrenceTarget ? "GOAL.TARGET_REACH."
                    : "GOAL.OUTPUT_RELATION.")
                    + UUID.nameUUIDFromBytes(occurrenceId.getBytes(
                    StandardCharsets.UTF_8)));
            goal.put("kind", occurrenceTarget ? "TARGET_REACH_CLOSURE"
                    : "OUTPUT_RELATION_CLOSURE");
            goal.put("runtimeDefinitionMethods",
                    new ArrayList<>(occurrenceMethods));
            goal.put("baselineObservedMethods",
                    new ArrayList<>(occurrenceObserved));
            goal.put("admission", object("state", occurrenceTarget
                            ? projectionBlockers.isEmpty()
                            ? "READY" : "BLOCKED" : "DISCOVERED",
                    "mode", "RUNTIME_FAILURE_CLOSURE", "blockers",
                    occurrenceTarget ? projectionBlockers
                            : Collections.singletonList(
                            "OUTPUT_CLOSURE_PENDING")));
            goal.put("symbolize", occurrenceSymbolize);
            goal.put("branches", occurrenceBranches);
            goal.put("edgeBindings", new ArrayList<>());

            Map<String, Object> plan = new LinkedHashMap<>();
            plan.put("schemaVersion", 3);
            plan.put("kind", "CONCOLIC_REGION_PLAN");
            plan.put("sourceKey", source.key());
            plan.put("sourceKind", source.kind());
            plan.put("sourceRole", source.role());
            plan.put("sourceId", source.id());
            plan.put("sourceEpoch", source.epoch());
            // An unstamped activation never passes as attributed evidence: it
            // is either directly stamped or published as the explicit gap
            // above.
            plan.put("sourceAuthority",
                    occurrenceTarget && semanticContext != root
                            && semanticContext.source != null
                            ? "SELECTED_TARGET_EVENT_SOURCE"
                            : stampedAuthority);
            plan.put("occurrenceId", occurrenceId);
            plan.put("regionId", region.regionId);
            // The once-only-root rule (README "Loops"): a region rooted on a
            // service loop is one occurrence per iteration, addressed by the
            // per-iteration source epoch, and replay enters the loop BODY at
            // headerUnitIndex rather than the entry frame above it.  Both
            // names travel only when the rule fired.
            if (region.rootLoop != null) {
                plan.put(LoopBoundPolicy.ROOT_AUTHORITY, region.rootAuthority);
                plan.put(LoopBoundPolicy.ROOT_LOOP, region.rootLoop);
            }
            plan.put("activationId", activation.get("activationId"));
            // The retained loops this occurrence's selected methods hold, with
            // their kind and K_L.
            List<Map<String, Object>> retainedLoops =
                    retainedLoops(region, occurrenceMethods);
            if (!retainedLoops.isEmpty()) {
                plan.put(RETAINED_LOOPS_FIELD, retainedLoops);
            }
            List<JsonObject> sourcePhases = configuredSourcePhases(
                    region, occurrenceId, rootCallId, trace);
            if (!sourcePhases.isEmpty()) {
                plan.put(ConfiguredSourcePhaseContract.PLAN_FIELD,
                        sourcePhases);
            }
            // Where this occurrence hands a declared communication port to the
            // VM, or takes one from it.
            List<Map<String, Object>> handoffSites =
                    communicationHandoffSites(region);
            if (!handoffSites.isEmpty()) {
                plan.put(CommunicationHandoffSpec.FIELD, handoffSites);
            }
            String plannedRelationKey = relationKey(source, regionId);
            plan.put("relationKey", plannedRelationKey);
            putTraceContext(plan, semanticContext, source);
            plan.put("traceEvidence", object("rootCallId", root.callId,
                    "activationId", activation.get("activationId")));
            String rootAuthority = region.rootAuthority;
            plan.put("rootSelector", rootSelector(root, rootSource,
                    occurrenceTarget
                            && !"COMMUNICATION_ENTRY".equals(rootAuthority)
                            ? semanticContext.requestApi : ""));
            // A region with no anchor states no target method rather than
            // an empty one.
            if (!region.anchorMethod.isEmpty()) {
                plan.put("targetMethod", region.anchorMethod);
            }
            // Why this activation was admitted, when it was admitted by
            // anything other than reaching the target.
            if (seed.containsKey(ADMISSION_BASIS)) {
                plan.put(ADMISSION_BASIS, seed.get(ADMISSION_BASIS));
                copyIfPresent(plan, seed, DEMANDED_BY_REGIONS);
                copyIfPresent(plan, seed, DEMANDED_SHARED_LOCATIONS);
            }
            plan.put("closureGoals", Collections.singletonList(goal));
            result.regionPlans.add(plan);
            goalByOccurrence.put(occurrenceId, goal);
            planByOccurrence.put(occurrenceId, plan);
        }
        for (Map<String, Object> edge : regionEdges) {
            String edgeKind = stringValue(edge.get("kind"));
            if (!"RUNTIME_FIELD_FLOW".equals(edgeKind)
                    && !"RUNTIME_PROTOCOL_FLOW".equals(edgeKind)
                    && !"RUNTIME_COORDINATED_STATE_FLOW".equals(edgeKind)) {
                throw new IllegalArgumentException("invalid runtime region "
                        + "flow row in " + regionEdgeSource);
            }
            String fromOccurrence = stringValue(edge.get("fromOccurrenceId"));
            String toOccurrence = stringValue(edge.get("toOccurrenceId"));
            if (fromOccurrence.isEmpty() || toOccurrence.isEmpty()) {
                throw new IllegalArgumentException(
                        "runtime field flow has no selected activation: "
                                + stringValue(edge.get("edgeId")));
            }
            boolean protocol = "RUNTIME_PROTOCOL_FLOW".equals(edgeKind);
            boolean coordinated =
                    "RUNTIME_COORDINATED_STATE_FLOW".equals(edgeKind);
            boolean containerMutation = "CONTAINER_MUTATION".equals(
                    stringValue(edge.get("bindingKind")));
            // A protocol row must be a correlated delivery: one named
            // exchange, one attempt of it, and a send the receive followed.
            if (protocol && !AutomaticRegionEdge.tracedExchangeCandidate(
                    candidateExchangeRow(edge, fromOccurrence,
                            toOccurrence))) {
                throw new IllegalArgumentException(
                        "runtime protocol flow lacks a correlated exchange, "
                                + "attempt and ordered send/receive: "
                                + stringValue(edge.get("edgeId")));
            }
            String fromPort = exactPort(exactPorts, fromOccurrence,
                    "OUT", stringValue(edge.get("fromPort")), edge);
            String toPort = exactPort(exactPorts, toOccurrence,
                    "IN", stringValue(edge.get("toPort")), edge);
            Map<String, Object> evidence = new LinkedHashMap<>(edge);
            evidence.remove("fromPort");
            evidence.remove("toPort");
            evidence.remove("bindings");
            evidence.put("schemaVersion", 3);
            evidence.put("fromOccurrenceId", fromOccurrence);
            evidence.put("toOccurrenceId", toOccurrence);
            evidence.put("fromOutputPort", fromPort);
            evidence.put("toInputPort", toPort);
            evidence.put("evidenceKind", protocol
                    ? AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY
                    : coordinated
                    ? "DECLARED_FIELD_COORDINATION_CANDIDATE_V1"
                    : containerMutation
                    ? "CONTAINER_MUTATION_READ_FROM_V1"
                    : "FIELD_ASSIGNMENT_READ_FROM_V1");
            evidence.put("correlationAuthority", protocol
                    ? AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY
                    : coordinated
                    ? "FAILURE_SLICED_DECLARED_FIELD_FAMILY_V1"
                    : "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
            if (protocol) {
                evidence.put("protocolDirection", edge.get("direction"));
            }
            copyBindingContext(evidence, edge,
                    planByOccurrence.get(fromOccurrence),
                    planByOccurrence.get(toOccurrence));
            evidence.put("state", protocol
                    ? "CANDIDATE_TRACED_RPC_EXCHANGE"
                    : coordinated
                    ? "CANDIDATE_COORDINATED_STATE"
                    : "CONFIRMED_RUNTIME_IDENTITY");
            result.edgeValidations.add(evidence);
            Map<String, Object> producerGoal =
                    goalByOccurrence.get(fromOccurrence);
            if (producerGoal != null && "OUTPUT_RELATION_CLOSURE".equals(
                    stringValue(producerGoal.get("kind")))) {
                appendGoalBinding(producerGoal, evidence);
            }
            Map<String, Object> consumerGoal =
                    goalByOccurrence.get(toOccurrence);
            if (consumerGoal != null && consumerGoal != producerGoal) {
                // Consumer protocol arguments are symbolic expressions only
                // when this exact trusted incoming edge is present.
                appendGoalBinding(consumerGoal, evidence);
            }
        }
        // The catalog is published after activation binding so that every
        // emitted port names the occurrence that owns it.
        for (StaticProgram.RegionRow region : regionById.values()) {
            result.regionCatalog.add(deepCopy(region.json));
        }
        finalizeProducerGoals(result.regionPlans, result.edgeValidations,
                regionById, refinedFlow, trace, loopBound);
        declareSharedCarriers(result, regionById);
        return result;
    }

    /** Declares the shared locations each planned activation must select. */
    private static void declareSharedCarriers(
            Result result,
            Map<String, StaticProgram.RegionRow> regionById) {
        for (Map<String, Object> plan : result.regionPlans) {
            StaticProgram.RegionRow region = regionById.get(
                    stringValue(plan.get("regionId")));
            String occurrence = stringValue(plan.get("occurrenceId"));
            if (region == null || occurrence.isEmpty()) continue;
            for (Map<String, Object> goal : rows(plan.get("closureGoals"))) {
                List<Map<String, Object>> carriers = declaredSharedCarriers(
                        rows(goal.get("edgeBindings")), region, occurrence);
                carriers = mergeSharedCarriers(carriers,
                        demandedSharedCarriers(plan, region, occurrence));
                if (!carriers.isEmpty()) {
                    goal.put(ExecutionTask.SHARED_CARRIERS, carriers);
                }
            }
        }
    }

    /** One declaration per {@code (kind, declaring field, receiver path)}, the
     * exact key the task layer already uses for the rows these become.
     *
     * <p>README {@code STATE-1}.</p> */
    private static String sharedCarrierKey(Map<String, Object> carrier) {
        String field = sharedCarrierField(carrier);
        if (field.isEmpty()) return "";
        return stringValue(carrier.get("kind")) + "\n" + field + ":"
                + stringValue(carrier.get("descriptor")) + "\n"
                + strings(carrier.get("fieldPath"));
    }

    /** The {@code declaringClass#fieldName} this carrier declares. */
    private static String sharedCarrierField(Map<String, Object> carrier) {
        return RecordedReadFrom.fieldKey(
                stringValue(carrier.get("declaringClass")),
                stringValue(carrier.get("fieldName")));
    }
    /** Existing shared-location admission applied to this exact production
     * occurrence. */
    private static List<Map<String, Object>> demandedSharedCarriers(
            Map<String, Object> plan, StaticProgram.RegionRow region,
            String occurrence) {
        if (!SHARED_LOCATION_DEMAND_ADMISSION.equals(
                stringValue(plan.get(ADMISSION_BASIS)))) {
            return Collections.emptyList();
        }
        Set<String> demanded = new LinkedHashSet<>(strings(
                plan.get(DEMANDED_SHARED_LOCATIONS)));
        if (demanded.isEmpty()) return Collections.emptyList();

        List<Map<String, Object>> ports = new ArrayList<>();
        ports.addAll(region.symbolicInputs);
        ports.addAll(region.outputs);
        Map<String, Map<String, Object>> carriers = new LinkedHashMap<>();
        for (Map<String, Object> port : ports) {
            String portOccurrence = stringValue(port.get("occurrenceId"));
            if (!portOccurrence.isEmpty()
                    && !occurrence.equals(portOccurrence)) {
                continue;
            }
            List<String> declarations = strings(
                    port.get("fieldPathDeclarations"));
            FieldPathSpec.DeclaredField field = declarations.isEmpty()
                    ? null : FieldPathSpec.declaredField(
                    declarations.get(declarations.size() - 1));
            if (field == null) continue;
            String location = RecordedReadFrom.fieldKey(field.owner(),
                    field.name());
            if (!demanded.contains(location)) continue;
            String descriptor = JavaPrimitiveSmtSemantics
                    .javaTypeDescriptor(field.type());
            if (descriptor.isEmpty()) continue;
            String sourceKind = stringValue(port.get("sourceKind"));
            Map<String, Object> carrier = object(
                    "kind", mapCarrierType(field.type())
                            ? SharedStateEvidence.LOCATION_KIND_MAP_STATE
                            : "DECLARED_FIELD",
                    "declaringClass", field.owner(),
                    "fieldName", field.name(),
                    "descriptor", descriptor,
                    // Reuses the exact access-owner binding the input/output
                    // port already carries.
                    "sourceKind", sourceKind);
            if ("ACTIVATION_FIELD_RECEIVER".equals(sourceKind)) {
                carrier.put("fieldPath", Collections.emptyList());
            } else {
                List<String> path = carrierPath(field,
                        Collections.singletonList(port));
                if (path.isEmpty()) continue;
                carrier.put("fieldPath", path);
            }
            // README STATE-1: two ports naming one declared field on two
            // receiver paths are two demanded locations.
            carriers.putIfAbsent(sharedCarrierKey(carrier), carrier);
        }
        carriers.remove("");
        return new ArrayList<>(carriers.values());
    }

    private static boolean mapCarrierType(String javaType) {
        String type = stringValue(javaType);
        return "java.util.Map".equals(type)
                || "java.util.HashMap".equals(type)
                || "java.util.LinkedHashMap".equals(type);
    }

    /** Union of two carrier declarations under README {@code STATE-1}'s key.
     */
    private static List<Map<String, Object>> mergeSharedCarriers(
            Collection<Map<String, Object>> left,
            Collection<Map<String, Object>> right) {
        Map<String, Map<String, Object>> byCarrier = new LinkedHashMap<>();
        for (Map<String, Object> carrier : left) {
            byCarrier.putIfAbsent(sharedCarrierKey(carrier), carrier);
        }
        for (Map<String, Object> carrier : right) {
            byCarrier.putIfAbsent(sharedCarrierKey(carrier), carrier);
        }
        byCarrier.remove("");
        return new ArrayList<>(byCarrier.values());
    }







    /** {@code K_L} this plan's relations are closed under. */
    private static int loopBodyBound(Map<String, Object> plan,
                                     LoopBoundPolicy loopBound) {
        int campaign = loopBound == null
                ? LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS
                : loopBound.maxBackedgeTraversals();
        int declared = LoopBoundPolicy.bodyBound(plan == null ? null
                : plan.get(LoopBoundPolicy.LOOP_BODY_BOUND));
        return Math.max(campaign, declared);
    }




    /** One carrier declaration per declared field this goal still carries
     * undecided candidate writers for. */
    private static List<Map<String, Object>> declaredSharedCarriers(
            List<Map<String, Object>> bindings, StaticProgram.RegionRow region,
            String occurrence) {
        List<Map<String, Object>> receiverPorts = receiverRootedPorts(
                bindings, region, occurrence);
        // README STATE-1: keyed by the whole carrier, not by the declared
        // field, so two receiver paths to one declaration are two locations.
        Map<String, Map<String, Object>> byCarrier = new LinkedHashMap<>();
        for (Map<String, Object> binding : bindings) {
            if (!RecordedReadFrom.PROVENANCE_CANDIDATE.equals(stringValue(
                    binding.get(RecordedReadFrom.EDGE_PROVENANCE)))
                    || !endpointOf(binding, occurrence)) {
                continue;
            }
            List<String> declarations = strings(
                    binding.get("fieldPathDeclarations"));
            FieldPathSpec.DeclaredField carrier = declarations.isEmpty()
                    ? null : FieldPathSpec.declaredField(
                    declarations.get(declarations.size() - 1));
            if (carrier == null) continue;
            String field = RecordedReadFrom.fieldKey(carrier.owner(),
                    carrier.name());
            if (field.isEmpty() || !field.equals(stringValue(binding.get(
                    RecordedReadFrom.EDGE_FIELD)))) {
                continue;
            }
            List<String> path = carrierPath(carrier, receiverPorts);
            String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                    carrier.type());
            if (path.isEmpty() || descriptor.isEmpty()) continue;
            Map<String, Object> declared = object(
                    "kind", "DECLARED_FIELD",
                    "declaringClass", carrier.owner(),
                    "fieldName", carrier.name(),
                    "descriptor", descriptor,
                    "fieldPath", path);
            byCarrier.putIfAbsent(sharedCarrierKey(declared), declared);
        }
        byCarrier.remove("");
        return new ArrayList<>(byCarrier.values());
    }

    /** The receiver-rooted path to the object that declares {@code carrier}.
     */
    private static List<String> carrierPath(
            FieldPathSpec.DeclaredField carrier,
            List<Map<String, Object>> receiverPorts) {
        Set<List<String>> paths = new LinkedHashSet<>();
        for (Map<String, Object> port : receiverPorts) {
            List<String> path = strings(port.get("fieldPath"));
            List<String> declarations = strings(
                    port.get("fieldPathDeclarations"));
            if (path.isEmpty() || path.size() != declarations.size()) {
                continue;
            }
            FieldPathSpec.DeclaredField leaf = FieldPathSpec.declaredField(
                    declarations.get(declarations.size() - 1));
            if (leaf == null
                    || !leaf.name().equals(path.get(path.size() - 1))) {
                continue;
            }
            if (carrier.owner().equals(leaf.owner())
                    && carrier.name().equals(leaf.name())) {
                paths.add(path);
            } else if (carrier.owner().equals(leaf.type())) {
                List<String> extended = new ArrayList<>(path);
                extended.add(carrier.name());
                paths.add(extended);
            }
        }
        return paths.size() == 1 ? paths.iterator().next()
                : Collections.<String>emptyList();
    }

    /** Ports this goal's bindings name for this activation whose field path
     * the replay walks from the region receiver. */
    private static List<Map<String, Object>> receiverRootedPorts(
            List<Map<String, Object>> bindings, StaticProgram.RegionRow region,
            String occurrence) {
        List<Map<String, Object>> inputs = region.symbolicInputs;
        List<Map<String, Object>> outputs = region.outputs;
        Map<String, Map<String, Object>> inputByPort =
                uniquePorts(inputs, occurrence, true);
        Map<String, Map<String, Object>> outputByPort =
                uniquePorts(outputs, occurrence, false);
        List<Map<String, Object>> result = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        for (Map<String, Object> binding : bindings) {
            if (occurrence.equals(stringValue(binding.get("toOccurrenceId")))) {
                addReceiverRootedPort(result, seen, inputByPort.get(
                        stringValue(binding.get("toInputPort"))));
            }
            if (occurrence.equals(stringValue(binding.get(
                    "fromOccurrenceId")))) {
                addReceiverRootedPort(result, seen, outputByPort.get(
                        stringValue(binding.get("fromOutputPort"))));
            }
        }
        return result;
    }

    /** One linear pass for all exact port lookups of one occurrence. */
    private static Map<String, Map<String, Object>> uniquePorts(
            List<Map<String, Object>> ports, String occurrenceId,
            boolean input) {
        Map<String, Map<String, Object>> result = new LinkedHashMap<>();
        Set<String> ambiguous = new LinkedHashSet<>();
        for (Map<String, Object> port : ports) {
            if (!(input ? boundToInput(port, occurrenceId)
                    : boundTo(port, occurrenceId))) {
                continue;
            }
            String portId = stringValue(port.get("portId"));
            if (portId.isEmpty() || ambiguous.contains(portId)) continue;
            if (result.putIfAbsent(portId, port) != null) {
                result.remove(portId);
                ambiguous.add(portId);
            }
        }
        return result;
    }

    private static void addReceiverRootedPort(
            List<Map<String, Object>> result, Set<String> seen,
            Map<String, Object> port) {
        // "RECEIVER" is the activation root the replay resolves a field path
        // from.
        if (port == null || !"RECEIVER".equals(stringValue(port.get(
                "rootKind")))
                || !seen.add(stringValue(port.get("portId")))) {
            return;
        }
        result.add(port);
    }

    private static boolean endpointOf(Map<String, Object> binding,
                                      String occurrence) {
        return occurrence.equals(stringValue(binding.get("fromOccurrenceId")))
                || occurrence.equals(stringValue(binding.get(
                        "toOccurrenceId")));
    }

    /** The refined protocol row as the composition gate reads it, before the
     * port ids the planner is about to mint exist. */
    private static JsonObject candidateExchangeRow(
            Map<String, Object> edge, String fromOccurrence,
            String toOccurrence) {
        Map<String, Object> row = new LinkedHashMap<>(edge);
        row.put("fromOccurrenceId", fromOccurrence);
        row.put("toOccurrenceId", toOccurrence);
        row.put("fromOutputPort", stringValue(edge.get("fromPort")));
        row.put("toInputPort", stringValue(edge.get("toPort")));
        return toJsonTreeFast(row).getAsJsonObject();
    }

    private static void appendGoalBinding(
            Map<String, Object> goal, Map<String, Object> binding) {
        List<Map<String, Object>> bindings = rows(goal.get("edgeBindings"));
        String edgeId = stringValue(binding.get("edgeId"));
        for (Map<String, Object> prior : bindings) {
            if (!edgeId.isEmpty()
                    && edgeId.equals(stringValue(prior.get("edgeId")))
                    && stringValue(binding.get("fromOccurrenceId")).equals(
                    stringValue(prior.get("fromOccurrenceId")))
                    && stringValue(binding.get("toOccurrenceId")).equals(
                    stringValue(prior.get("toOccurrenceId")))) {
                return;
            }
        }
        bindings.add(binding);
        goal.put("edgeBindings", bindings);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> row(Object value) {
        return value instanceof Map<?, ?>
                ? (Map<String, Object>) value
                : Collections.emptyMap();
    }

    /** Structural replacement for the previous Gson round-trip copy with the
     * identical value domain: null-valued map entries are dropped, integral
     * numbers become Long, list nulls survive. */
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
        return RuntimeRefinedGraphBuilder.normalizeScalar(value);
    }

    /** Structural replacement for {@code GSON.toJsonTree} over the plain
     * Map/List/scalar rows this planner manipulates; mirrors Gson exactly,
     * including dropped null map entries and JsonNull list members. */
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

    /** The accessor identity a port row states, decoded once per read. */
    private static MaterializationSpec accessor(Map<String, Object> port) {
        return MaterializationSpec.decode(
                toJsonTreeFast(port).getAsJsonObject());
    }

    private static void copyIfPresent(Map<String, Object> target,
                                      Map<String, Object> source,
                                      String field) {
        if (source.containsKey(field)) target.put(field, source.get(field));
    }

    /** Freezes the complete demanded producer relation, bounded to the heap
     * writes some fatal-path consumer reads. */
    private static void finalizeProducerGoals(
            List<Map<String, Object>> plans,
            List<Map<String, Object>> causalEdges,
            Map<String, StaticProgram.RegionRow> regionById,
            RefinedFlowIndex refinedFlow, TraceIndex trace,
            LoopBoundPolicy loopBound) {
        List<PlannedOutputRelation> planned = planProducerGoals(plans,
                regionById, refinedFlow, trace, loopBound);
        // The bound is one fact over every planned occurrence at once, so it
        // is decided only once the slice that states each demand exists.
        Set<String> demandedOutputs = failureDemandedOutputs(plans, planned,
                causalEdges);
        for (PlannedOutputRelation relation : planned) {
            materializeProducerGoal(relation, demandedOutputs);
            boundConfiguredSourcePhasesToSelectedOutputCalls(
                    relation.plan, relation.goal);
        }
        // Loop trip counts are bounded by the same demand, and only once the
        // goals state their final demanded slice.  With no failure to direct
        // it the bound admits every loop, exactly as before it existed.
        if (demandedOutputs != null) markFailureRelevantLoops(plans);
    }

    /** Closes every demanded output of every producer occurrence.
     *
     * <p>Producer-goal completion is independent per plan over shared
     * read-only inputs (region catalog, refined-flow index, trace index), so
     * plans are processed on a bounded pool; every plan's goals are computed
     * exactly as in the sequential order and returned in plan order, which
     * keeps results and artifact order byte-identical.</p> */
    private static List<PlannedOutputRelation> planProducerGoals(
            List<Map<String, Object>> plans,
            Map<String, StaticProgram.RegionRow> regionById,
            RefinedFlowIndex refinedFlow, TraceIndex trace,
            LoopBoundPolicy loopBound) {
        int configured = Integer.getInteger(
                "causynth.aggregate.threads", 0);
        int threads = configured > 0 ? Math.min(configured, 32)
                : Math.max(1, Math.min(8,
                Runtime.getRuntime().availableProcessors() - 2));
        List<PlannedOutputRelation> planned = new ArrayList<>();
        if (threads <= 1 || plans.size() <= 1) {
            for (Map<String, Object> plan : plans) {
                PlannedOutputRelation relation = planProducerGoal(plan,
                        regionById, refinedFlow, trace, loopBound);
                if (relation != null) planned.add(relation);
            }
            return planned;
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
            List<java.util.concurrent.Future<PlannedOutputRelation>> pending =
                    new ArrayList<>();
            for (Map<String, Object> plan : plans) {
                pending.add(executor.submit(() -> planProducerGoal(plan,
                        regionById, refinedFlow, trace, loopBound)));
            }
            for (java.util.concurrent.Future<PlannedOutputRelation> future
                    : pending) {
                PlannedOutputRelation relation = future.get();
                if (relation != null) planned.add(relation);
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
        return planned;
    }

    /** One producer occurrence's demanded output relation, held between the
     * slice that closes each demanded endpoint and the failure-directed bound
     * that decides which of them the goal keeps. */
    private static final class PlannedOutputRelation {
        private final Map<String, Object> plan;
        private final Map<String, Object> goal;
        private final String occurrenceId;
        private final List<String> demandedEndpoints;
        private final Map<String, List<Map<String, Object>>> demandedBindings;
        private final List<Map<String, Object>> incomingBindings;
        private final List<String> blockers;
        /** Demanded endpoint to the one output port its bindings name. */
        private final Map<String, String> endpointPorts =
                new LinkedHashMap<>();
        /** Demanded endpoint to the contract its bounded versions closed. */
        private final Map<String, OutputClosureContract> closures =
                new LinkedHashMap<>();
        /** Demanded endpoint to the bindings those closed versions state. */
        private final Map<String, List<Map<String, Object>>> closedBindings =
                new LinkedHashMap<>();
        /** The output ports the producer region declares beyond the ones its
         * own identity mints - exactly the set its closure contract admits by
         * name.  A declaration is a static fact, so it is stated whether or
         * not the trace ever demanded the port. */
        private final Set<String> declaredOutputPorts =
                new LinkedHashSet<>();
        /** The output port every demanded endpoint names, closed or not. */
        private final Set<String> demandedPorts = new LinkedHashSet<>();

        PlannedOutputRelation(Map<String, Object> plan,
                              Map<String, Object> goal,
                              String occurrenceId,
                              List<String> demandedEndpoints,
                              Map<String, List<Map<String, Object>>>
                                      demandedBindings,
                              List<Map<String, Object>> incomingBindings,
                              List<String> blockers) {
            this.plan = plan;
            this.goal = goal;
            this.occurrenceId = occurrenceId;
            this.demandedEndpoints = demandedEndpoints;
            this.demandedBindings = demandedBindings;
            this.incomingBindings = incomingBindings;
            this.blockers = blockers;
        }

        void close(String endpoint, String outputPort,
                   OutputClosureContract closure,
                   List<Map<String, Object>> bindings) {
            endpointPorts.put(endpoint, outputPort);
            closures.put(endpoint, closure);
            closedBindings.put(endpoint, bindings);
        }
    }

    private static PlannedOutputRelation planProducerGoal(
            Map<String, Object> plan,
            Map<String, StaticProgram.RegionRow> regionById,
            RefinedFlowIndex refinedFlow, TraceIndex trace,
            LoopBoundPolicy loopBound) {
        int loopBodyBound = loopBodyBound(plan, loopBound);
        List<Map<String, Object>> goals = rows(plan.get("closureGoals"));
        if (goals.size() != 1 || !"OUTPUT_RELATION_CLOSURE".equals(
                stringValue(goals.get(0).get("kind")))) {
            return null;
        }
        Map<String, Object> base = goals.get(0);
        StaticProgram.RegionRow producerRegion = regionById.get(
                stringValue(plan.get("regionId")));
        String producerOccurrence = stringValue(plan.get("occurrenceId"));
        Map<String, List<Map<String, Object>>> byEndpoint =
                new LinkedHashMap<>();
        Map<String, String> canonicalOutputPort =
                canonicalAliasedOutputPorts(producerRegion,
                        producerOccurrence);
        List<Map<String, Object>> incomingBindings = new ArrayList<>();
        Set<String> exactResponseDeliveryEndpoints =
                new LinkedHashSet<>();
        for (Map<String, Object> binding
                : rows(base.get("edgeBindings"))) {
            boolean outgoing = producerOccurrence.equals(
                    stringValue(binding.get("fromOccurrenceId")));
            boolean incoming = producerOccurrence.equals(
                    stringValue(binding.get("toOccurrenceId")));
            String output = outgoing
                    ? stringValue(binding.get("fromOutputPort")) : "";
            if (outgoing && !output.isEmpty()) {
                output = canonicalOutputPort.getOrDefault(output, output);
                binding.put("fromOutputPort", output);
                String endpoint = semanticOutputEndpoint(binding,
                        producerRegion, producerOccurrence);
                // Missing endpoint metadata must not merge unrelated
                // ports.
                if (endpoint.isEmpty()) endpoint = "UNRESOLVED:" + output;
                byEndpoint.computeIfAbsent(endpoint,
                        ignored -> new ArrayList<>()).add(binding);
                if (exactResponseDeliveryBinding(binding,
                        producerRegion, producerOccurrence, output)) {
                    exactResponseDeliveryEndpoints.add(endpoint);
                }
            }
            if (incoming && !outgoing) incomingBindings.add(binding);
        }
        // A server occurrence selected by one exact response delivery
        // states its relation on that response.
        if (!exactResponseDeliveryEndpoints.isEmpty()) {
            byEndpoint.keySet().retainAll(
                    exactResponseDeliveryEndpoints);
        }
        List<String> demandedEndpoints = new ArrayList<>(
                byEndpoint.keySet());
        Collections.sort(demandedEndpoints);
        Map<String, List<List<Map<String, Object>>>> versionsByEndpoint =
                demandedBindingVersions(demandedEndpoints, byEndpoint,
                        loopBodyBound);
        // README REGION-1: one local occurrence is one coarse task and one
        // guarded summary.
        Map<String, Object> goal = deepCopy(base);
        Map<String, List<Map<String, Object>>> demandedBindings =
                new LinkedHashMap<>();
        List<Map<String, Object>> selectedBindings =
                new ArrayList<>(incomingBindings);
        for (String endpoint : demandedEndpoints) {
            List<Map<String, Object>> endpointBindings =
                    new ArrayList<>();
            for (List<Map<String, Object>> version
                    : versionsByEndpoint.getOrDefault(endpoint,
                    Collections.emptyList())) {
                endpointBindings.addAll(version);
            }
            demandedBindings.put(endpoint, endpointBindings);
            selectedBindings.addAll(endpointBindings);
        }
        goal.put("edgeBindings", selectedBindings);
        // The zero is the retired per-version goal index.
        String identity = stringValue(plan.get("occurrenceId"))
                + "\n" + demandedEndpoints + "\n" + 0
                + "\n" + bindingAlternativeIdentity(demandedBindings);
        goal.put("goalId", "GOAL.OUTPUT_RELATION."
                + UUID.nameUUIDFromBytes(identity.getBytes(
                StandardCharsets.UTF_8)));

        List<String> blockers = new ArrayList<>();
        PlannedOutputRelation relation = new PlannedOutputRelation(plan,
                goal, producerOccurrence, demandedEndpoints,
                demandedBindings, incomingBindings, blockers);
        for (String declared
                : contractDeclaredOutputPorts(producerRegion)) {
            relation.declaredOutputPorts.add(
                    canonicalOutputPort.getOrDefault(declared, declared));
        }
        if (demandedEndpoints.isEmpty()) {
            blockers.add("OUTPUT_DEMAND_SET_EMPTY");
        }
        for (String endpoint : demandedEndpoints) {
            List<Map<String, Object>> outputBindings =
                    demandedBindings.get(endpoint);
            String output = selectedOutputPort(outputBindings);
            if (output.isEmpty()) {
                blockers.add("OUTPUT_ENDPOINT_AMBIGUOUS:" + endpoint);
                continue;
            }
            relation.demandedPorts.add(output);
            // The endpoint's kind is a static fact about the port, so it
            // is decided once for every bounded version of it.
            Map<String, Object> cutPort = communicationOutputPort(
                    producerRegion, output, producerOccurrence);
            String capture = cutPort == null ? "" : stringValue(cutPort.get(
                    CommunicationCatalogContract
                            .PORT_OUTPUT_CAPTURE_KIND));
            boolean cutArgument = CommunicationCatalogContract
                    .CAPTURE_CALL_ARGUMENT.equals(capture);
            boolean callReturn = CommunicationCatalogContract
                    .CAPTURE_CALL_RETURN.equals(capture);
            boolean symbolicCutArgument = cutArgument
                    && symbolicLeafType(stringValue(cutPort.get(
                            "javaType")));
            boolean communicationEffect = CommunicationCatalogContract
                    .CAPTURE_METHOD_RETURN.equals(capture);
            // A structured request object is a concrete carrier for the
            // interaction, not one symbolic value.  The same holds for a
            // leaf-typed wire value once this region declares component
            // leaves inside it: those leaves are the symbolic values and
            // the carrier only transports them.
            if (cutArgument && !symbolicCutArgument) {
                continue;
            }
            List<OutputClosureContract> versions = new ArrayList<>();
            List<Map<String, Object>> versionBindings =
                    new ArrayList<>();
            for (List<Map<String, Object>> version
                    : versionsByEndpoint.get(endpoint)) {
                List<String> heapBlockers = new ArrayList<>();
                // A structured leaf has no argument or heap boundary of
                // its own; a cut argument closes one frame before the
                // transport instead of on a heap cell the transport owns;
                // and a server return is an interaction site, not a
                // symbolic whole-object value.
                OutputClosureContract closure = cutArgument || callReturn
                        || communicationEffect
                        ? declaredCutOutputClosure(plan, goal,
                        producerRegion, output, version, refinedFlow,
                        trace, loopBodyBound, heapBlockers, capture)
                        : directHeapOutputClosure(plan, goal,
                        producerRegion, output, version, refinedFlow,
                        trace, loopBodyBound, heapBlockers);
                if (closure == null) {
                    if (!heapBlockers.isEmpty()) {
                        addReasonsOnce(blockers, heapBlockers);
                    } else if (cutArgument || callReturn
                            || communicationEffect) {
                        // Not "pending".
                        addReasonOnce(blockers,
                                "OUTPUT_CLOSURE_CROSSES_CUT:" + output);
                    } else {
                        addReasonOnce(blockers,
                                "OUTPUT_CLOSURE_PENDING:" + output);
                    }
                } else {
                    versions.add(closure);
                    versionBindings.addAll(version);
                }
            }
            // One version of this endpoint failing to close is a named
            // blocker on the goal, not a reason to refuse the versions
            // that did close: the same rule an unrelated pending
            // endpoint already follows below.
            if (versions.isEmpty()) continue;
            relation.close(endpoint, output,
                    coarseOccurrenceOutputVersions(versions),
                    versionBindings);
        }
        return relation;
    }

    /** Publishes one planned producer relation, keeping only the demanded
     * endpoints the failure-directed bound admits. */
    private static void materializeProducerGoal(
            PlannedOutputRelation relation, Set<String> demandedOutputs) {
        Map<String, Object> plan = relation.plan;
        Map<String, Object> goal = relation.goal;
        List<String> blockers = relation.blockers;
        List<OutputClosureContract> members = new ArrayList<>();
        List<Map<String, Object>> successfulOutgoingBindings =
                new ArrayList<>();
        List<String> boundedEndpoints = new ArrayList<>();
        boolean bounded = false;
        for (String endpoint : relation.demandedEndpoints) {
            OutputClosureContract closure = relation.closures.get(endpoint);
            // A heap write no fatal-path consumer reads stands on no causal
            // chain to the failure, so it states no capture port.
            if (closure != null && !failureDemandedRelation(
                    relation.occurrenceId, closure, demandedOutputs)) {
                bounded = true;
                addReasonOnce(blockers, "OUTPUT_UNREAD_BY_FAILURE:"
                        + relation.endpointPorts.get(endpoint));
                continue;
            }
            boundedEndpoints.add(endpoint);
            if (closure == null) continue;
            members.add(closure);
            successfulOutgoingBindings.addAll(
                    relation.closedBindings.get(endpoint));
        }
        // The bound above can only ever speak about an endpoint the trace
        // demanded.  A port the region declares that no traced consumer ever
        // read leaves no endpoint at all, so without this it states nothing
        // and a coverage hole reads exactly like a closed relation.
        Set<String> boundPorts = new LinkedHashSet<>();
        for (OutputClosureContract closure : members) {
            for (OutputClosureContract.Member member : closure.members()) {
                boundPorts.add(member.portId());
            }
        }
        for (String port : relation.declaredOutputPorts) {
            if (boundPorts.contains(port)
                    || relation.demandedPorts.contains(port)) {
                continue;
            }
            addReasonOnce(blockers,
                    "OUTPUT_DECLARED_WITHOUT_CONSUMER:" + port);
        }
        if (bounded) {
            // The demand set the goal states is the bounded one.
            Map<String, List<Map<String, Object>>> demandedBindings =
                    new LinkedHashMap<>();
            List<Map<String, Object>> selectedBindings =
                    new ArrayList<>(relation.incomingBindings);
            for (String endpoint : boundedEndpoints) {
                List<Map<String, Object>> endpointBindings =
                        relation.demandedBindings.get(endpoint);
                demandedBindings.put(endpoint, endpointBindings);
                selectedBindings.addAll(endpointBindings);
            }
            goal.put("edgeBindings", selectedBindings);
            // The zero is the retired per-version goal index.
            String identity = relation.occurrenceId
                    + "\n" + boundedEndpoints + "\n" + 0
                    + "\n" + bindingAlternativeIdentity(demandedBindings);
            goal.put("goalId", "GOAL.OUTPUT_RELATION."
                    + UUID.nameUUIDFromBytes(identity.getBytes(
                    StandardCharsets.UTF_8)));
        }
        List<Map<String, Object>> incomingBindings =
                relation.incomingBindings;
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
            OutputClosureContract closure =
                    OutputClosureCodec.merge(members);
            Set<String> inputs = new LinkedHashSet<>(
                    closure.executionScope().inputPorts());
            List<Map<String, Object>> executableBindings =
                    new ArrayList<>();
            for (Map<String, Object> incoming : incomingBindings) {
                String input = stringValue(incoming.get("toInputPort"));
                // Failure closure already selected protocol topology.  Keep
                // its exact traced delivery even when the selected local
                // output path does not consume the carried scalar.
                if (inputs.contains(input) || "RUNTIME_PROTOCOL_FLOW".equals(
                        stringValue(incoming.get("kind")))) {
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
            List<Map<String, Object>> selectedSymbolize =
                    filterByText(rows(goal.get("symbolize")),
                            "symbol", inputs);
            goal.put("symbolize", selectedSymbolize);
            goal.put("branches", filterByText(
                    rows(goal.get("branches")), "siteId", sites));
        }
        List<Map<String, Object>> completeSet = new ArrayList<>();
        completeSet.add(goal);
        // Numbers the write this member is anchored on among the static
        // output endpoints of the one goal.
        assignOutputOccurrenceIdentity(completeSet);
        plan.put("closureGoals", completeSet);
        bindSelectedEffectCausalAnchor(plan, completeSet);
    }

    /** Whether some fatal-path consumer reads what one closed output states.
     *
     * <p>Fail-closed twice over: an output that states anything other than a
     * heap write is demanded, and so is every output at all when the run
     * recorded no failure to direct the bound.</p> */
    private static boolean failureDemandedRelation(String occurrenceId,
            OutputClosureContract closure, Set<String> demandedOutputs) {
        if (demandedOutputs == null) return true;
        for (OutputClosureContract.Member member : closure.members()) {
            if (!statesHeapWrite(member) || demandedOutputs.contains(
                    portDemand(occurrenceId, member.portId()))) {
                return true;
            }
        }
        return false;
    }

    /** Whether one output member states heap writes and nothing else. */
    private static boolean statesHeapWrite(
            OutputClosureContract.Member member) {
        JsonArray captures = member.captures();
        if (captures.size() == 0) return false;
        for (JsonElement capture : captures) {
            if (!capture.isJsonObject()) return false;
            JsonElement kind = capture.getAsJsonObject().get("captureKind");
            if (kind == null || !kind.isJsonPrimitive()) return false;
            String captureKind = kind.getAsString();
            if (!OutputCaptureSpec.FIELD_WRITE_STATE.equals(captureKind)
                    && !OutputCaptureSpec.MUTATION_STATE.equals(captureKind)) {
                return false;
            }
        }
        return true;
    }

    /** One occurrence-owned port, the key every demand here is stated in. */
    private static String portDemand(String occurrenceId, String portId) {
        return occurrenceId + "\n" + portId;
    }

    private static String demandOccurrence(String demand) {
        int at = demand.indexOf('\n');
        return at < 0 ? demand : demand.substring(0, at);
    }

    /**
     * Every output port the failure reads, closed backward from the fatal
     * occurrences over the recorded causal edges and each producer's own
     * dependency slice.
     *
     * <p>The failure states its own demanded inputs; a producer of one
     * demanded input states, in the slice that closed that output, exactly
     * the inputs it needs to restate it.  Nothing outside that closure stands
     * on a causal chain to the failure.  Object identity closes it: a
     * demanded write is one write of one object's state, so the other writes
     * of that same object, and the write that publishes that object to its
     * reader, are demanded with it.</p>
     *
     * <p>Returns {@code null} when the run recorded no fatal occurrence or no
     * causal edge: with no failure to direct it the bound admits every
     * demand, exactly as before it existed.</p>
     */
    private static Set<String> failureDemandedOutputs(
            List<Map<String, Object>> plans,
            List<PlannedOutputRelation> planned,
            List<Map<String, Object>> causalEdges) {
        Map<String, List<String>> sliceInputs = new LinkedHashMap<>();
        List<String> heapOutputs = new ArrayList<>();
        for (PlannedOutputRelation relation : planned) {
            for (OutputClosureContract closure : relation.closures.values()) {
                for (OutputClosureContract.Member member
                        : closure.members()) {
                    String demand = portDemand(relation.occurrenceId,
                            member.portId());
                    if (sliceInputs.containsKey(demand)) continue;
                    sliceInputs.put(demand, memberInputPorts(member));
                    if (statesHeapWrite(member)) heapOutputs.add(demand);
                }
            }
        }
        return failureDemandedOutputs(plans, causalEdges, sliceInputs,
                heapOutputs);
    }

    /** The bound itself, over the demand evidence alone: every occurrence's
     * plan, every recorded causal edge, the inputs each closed output's slice
     * states, and which of those outputs state a heap write. */
    static Set<String> failureDemandedOutputs(
            List<Map<String, Object>> plans,
            List<Map<String, Object>> causalEdges,
            Map<String, List<String>> sliceInputs,
            List<String> heapOutputs) {
        Set<String> targets = new LinkedHashSet<>();
        Set<String> plannedOccurrences = new LinkedHashSet<>();
        Deque<String> work = new ArrayDeque<>();
        for (Map<String, Object> plan : plans) {
            String occurrence = stringValue(plan.get("occurrenceId"));
            if (occurrence.isEmpty()) continue;
            plannedOccurrences.add(occurrence);
            for (Map<String, Object> goal : rows(plan.get("closureGoals"))) {
                if (!"TARGET_REACH_CLOSURE".equals(
                        stringValue(goal.get("kind")))) {
                    continue;
                }
                targets.add(occurrence);
                // A fatal occurrence's projected symbolic inputs are the
                // failure's own demand.
                for (Map<String, Object> symbol
                        : rows(goal.get("symbolize"))) {
                    String port = stringValue(symbol.get("portId"));
                    if (!port.isEmpty()) {
                        work.add(portDemand(occurrence, port));
                    }
                }
            }
        }
        if (targets.isEmpty() || causalEdges.isEmpty()) return null;

        Map<String, List<Map<String, Object>>> byConsumedInput =
                new LinkedHashMap<>();
        Map<String, List<Map<String, Object>>> byProducedOutput =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : causalEdges) {
            String consumer = stringValue(edge.get("toOccurrenceId"));
            String input = stringValue(edge.get("toInputPort"));
            if (!consumer.isEmpty() && !input.isEmpty()) {
                String demand = portDemand(consumer, input);
                byConsumedInput.computeIfAbsent(demand,
                        ignored -> new ArrayList<>()).add(edge);
                // A fatal occurrence reads what the trace delivered to it;
                // an occurrence with no plan states no slice to bound by.
                if (targets.contains(consumer)
                        || !plannedOccurrences.contains(consumer)) {
                    work.add(demand);
                }
            }
            String producer = stringValue(edge.get("fromOccurrenceId"));
            String output = stringValue(edge.get("fromOutputPort"));
            if (!producer.isEmpty() && !output.isEmpty()) {
                byProducedOutput.computeIfAbsent(
                        portDemand(producer, output),
                        ignored -> new ArrayList<>()).add(edge);
            }
        }

        Set<String> demandedInputs = new LinkedHashSet<>();
        Set<String> demandedOutputs = new LinkedHashSet<>();
        drainDemand(work, byConsumedInput, sliceInputs, demandedInputs,
                demandedOutputs);
        while (true) {
            Set<Long> demandedObjects = new LinkedHashSet<>();
            for (String demand : heapOutputs) {
                if (!demandedOutputs.contains(demand)) continue;
                for (Map<String, Object> edge : byProducedOutput.getOrDefault(
                        demand, Collections.<Map<String, Object>>emptyList())) {
                    long receiver = longNumber(
                            edge.get("receiverObjectId"), 0L);
                    if (receiver > 0L) demandedObjects.add(receiver);
                }
            }
            boolean grew = false;
            for (String demand : heapOutputs) {
                if (demandedOutputs.contains(demand)
                        || !statesDemandedObject(byProducedOutput.getOrDefault(
                        demand, Collections.<Map<String, Object>>emptyList()),
                        demandedObjects)) {
                    continue;
                }
                demandedOutputs.add(demand);
                grew = true;
                for (String port : sliceInputs.getOrDefault(demand,
                        Collections.<String>emptyList())) {
                    work.add(portDemand(demandOccurrence(demand), port));
                }
            }
            drainDemand(work, byConsumedInput, sliceInputs, demandedInputs,
                    demandedOutputs);
            if (!grew) break;
        }
        return demandedOutputs;
    }

    /** Whether one output writes, or publishes, an already demanded object. */
    private static boolean statesDemandedObject(
            List<Map<String, Object>> edges, Set<Long> demandedObjects) {
        for (Map<String, Object> edge : edges) {
            long receiver = longNumber(edge.get("receiverObjectId"), 0L);
            long value = longNumber(edge.get("valueObjectId"), 0L);
            if (receiver > 0L && demandedObjects.contains(receiver)
                    || value > 0L && demandedObjects.contains(value)) {
                return true;
            }
        }
        return false;
    }

    /** Closes the demand worklist: one demanded input demands the output that
     * produced it, and that output demands the inputs its slice states. */
    private static void drainDemand(Deque<String> work,
            Map<String, List<Map<String, Object>>> byConsumedInput,
            Map<String, List<String>> sliceInputs,
            Set<String> demandedInputs, Set<String> demandedOutputs) {
        while (!work.isEmpty()) {
            String input = work.removeFirst();
            if (!demandedInputs.add(input)) continue;
            for (Map<String, Object> edge : byConsumedInput.getOrDefault(input,
                    Collections.<Map<String, Object>>emptyList())) {
                String producer = stringValue(edge.get("fromOccurrenceId"));
                String output = stringValue(edge.get("fromOutputPort"));
                if (producer.isEmpty() || output.isEmpty()) continue;
                String demand = portDemand(producer, output);
                if (!demandedOutputs.add(demand)) continue;
                // No slice closed this output, so nothing restates it and it
                // demands nothing of its own producer.
                for (String port : sliceInputs.getOrDefault(demand,
                        Collections.<String>emptyList())) {
                    work.add(portDemand(producer, port));
                }
            }
        }
    }

    /**
     * The methods whose local control flow anything the failure reads can
     * still depend on, for one planned occurrence.
     *
     * <p>Union of what this occurrence's own <em>surviving</em> demand
     * evidence names: each closure goal's definition methods and the observed
     * methods retained inside them, the sites of every branch the goal's path
     * condition keeps, the mint sites of every symbolic input it projects,
     * the sites and methods of every demanded output member's slice, this
     * occurrence's root and its re-rooted loop body, and every configured
     * symbolic source it mints.  A goal whose outputs the failure-directed
     * bound dropped states no methods and so contributes none.</p>
     *
     * <p>Answers the empty set when the occurrence's demand evidence is not
     * decidable -- a target-reach goal whose projection is blocked, or a
     * closure that carries members but names no definition method.  Empty is
     * "unknown", and {@link #demandedLoopReason} reads it as "everything is
     * still required"; it is never "nothing is demanded".</p>
     */
    static Set<String> failureDemandedLoopScope(Map<String, Object> plan) {
        Set<String> scope = new LinkedHashSet<>();
        if (plan == null) return scope;
        addMethod(scope, stringValue(row(plan.get("rootSelector"))
                .get("method")));
        Map<String, Object> rootLoop = row(plan.get(LoopBoundPolicy.ROOT_LOOP));
        addMethod(scope, stringValue(rootLoop.get(
                LoopBoundPolicy.ROOT_LOOP_METHOD)));
        addSiteMethods(scope, stringValue(rootLoop.get(
                LoopBoundPolicy.LOOP_SITE_ID)));
        for (Map<String, Object> phase : rows(plan.get(
                ConfiguredSourcePhaseContract.PLAN_FIELD))) {
            addMethod(scope, stringValue(phase.get("method")));
            addSiteMethods(scope, stringValue(phase.get("siteId")));
        }
        for (Map<String, Object> goal : rows(plan.get("closureGoals"))) {
            boolean target = "TARGET_REACH_CLOSURE".equals(
                    stringValue(goal.get("kind")));
            if (target && !"READY".equals(stringValue(
                    row(goal.get("admission")).get("state")))) {
                // The projection that states what the failure reads is
                // blocked, so this occurrence has no decided demand at all.
                return Collections.emptySet();
            }
            List<String> definitions = strings(
                    goal.get("runtimeDefinitionMethods"));
            scope.addAll(definitions);
            scope.addAll(strings(goal.get("baselineObservedMethods")));
            for (Map<String, Object> branch : rows(goal.get("branches"))) {
                addSiteMethods(scope, stringValue(branch.get("siteId")));
            }
            for (Map<String, Object> symbol : rows(goal.get("symbolize"))) {
                addSiteMethods(scope, stringValue(symbol.get("siteId")));
            }
            Map<String, Object> closure = row(goal.get("outputClosure"));
            List<Map<String, Object>> members = rows(closure.get("members"));
            if (!members.isEmpty() && definitions.isEmpty()) {
                // A closed relation that names no definition method is
                // evidence this rule cannot read.
                return Collections.emptySet();
            }
            for (Map<String, Object> member : members) {
                Map<String, Object> slice = row(member.get("slice"));
                scope.addAll(strings(slice.get("methods")));
                for (String site : strings(slice.get("sites"))) {
                    addSiteMethods(scope, site);
                }
                for (String site : strings(slice.get("staticSites"))) {
                    addSiteMethods(scope, site);
                }
                addSiteMethods(scope, stringValue(
                        slice.get("captureAnchorSiteId")));
                addSiteMethods(scope, stringValue(
                        row(member.get("output")).get("outputSiteId")));
            }
        }
        scope.remove("");
        return scope;
    }

    private static void addMethod(Set<String> scope, String method) {
        if (!method.isEmpty()) scope.add(method);
    }

    private static void addSiteMethods(Set<String> scope, String siteId) {
        scope.addAll(LoopBoundPolicy.siteMethods(siteId));
    }

    /**
     * Why one retained loop's trip count is still demanded, or {@code ""}
     * when nothing the failure reads can observe how often it ran.
     *
     * <p>A loop's iteration count reaches the failure only through a value
     * defined inside it or a branch it controls, and both are stated by the
     * method the loop lives in.  A loop whose method no demanded slice, no
     * retained branch and no projected symbolic input names therefore
     * contributes nothing the failure can read, and its undeclared bound is
     * immaterial rather than a coverage gap.</p>
     *
     * <p>Fail-closed in three named ways: an undecidable scope keeps every
     * loop, a loop that names no method keeps itself, and any method the loop
     * names -- its enclosing method or the method of any control site of the
     * nest -- is enough to keep it.  This answer relaxes exactly one gap,
     * {@code BOUNDED_LOOP_BODY_BOUND_UNDECLARED}; the loop stays retained,
     * keeps its path-local count, and every out-of-bound refusal still
     * fires.</p>
     */
    static String demandedLoopReason(Set<String> demandedScope,
                                     Map<String, Object> loop) {
        if (demandedScope == null || demandedScope.isEmpty()) {
            return "FAILURE_DEMAND_SCOPE_UNDECIDED";
        }
        Set<String> named = new LinkedHashSet<>();
        addMethod(named, stringValue(
                loop == null ? null : loop.get("enclosingMethod")));
        if (loop != null) {
            addSiteMethods(named, stringValue(
                    loop.get(LoopBoundPolicy.LOOP_SITE_ID)));
            for (String site : strings(loop.get(
                    LoopBoundPolicy.LOOP_CONTROL_SITE_IDS))) {
                addSiteMethods(named, site);
            }
        }
        if (named.isEmpty()) return "LOOP_NAMES_NO_METHOD";
        for (String method : named) {
            if (demandedScope.contains(method)) {
                return "LOOP_METHOD_IN_FAILURE_DEMANDED_SLICE";
            }
        }
        return "";
    }

    /** Decides {@link LoopBoundPolicy#LOOP_FAILURE_RELEVANT} on every
     * retained loop of every planned occurrence, once the demand each
     * occurrence states is final. */
    private static void markFailureRelevantLoops(
            List<Map<String, Object>> plans) {
        for (Map<String, Object> plan : plans) {
            List<Map<String, Object>> loops = rows(
                    plan.get(RETAINED_LOOPS_FIELD));
            if (loops.isEmpty()) continue;
            Set<String> scope = failureDemandedLoopScope(plan);
            for (Map<String, Object> loop : loops) {
                String reason = demandedLoopReason(scope, loop);
                loop.put(LoopBoundPolicy.LOOP_FAILURE_RELEVANT,
                        Boolean.valueOf(!reason.isEmpty()));
                loop.put(LoopBoundPolicy.LOOP_RELEVANCE_AUTHORITY,
                        LoopBoundPolicy.FAILURE_DEMANDED_LOOP_SCOPE);
            }
        }
    }

    private static List<String> memberInputPorts(
            OutputClosureContract.Member member) {
        JsonElement ports = member.slice().get("inputPorts");
        List<String> result = new ArrayList<>();
        if (ports == null || !ports.isJsonArray()) return result;
        for (JsonElement port : ports.getAsJsonArray()) {
            if (port.isJsonPrimitive()) result.add(port.getAsString());
        }
        return result;
    }

    /** Binds a producer occurrence to the unique named request scope carried
     * by its selected communication effect. */
    private static void bindSelectedEffectCausalAnchor(
            Map<String, Object> plan, List<Map<String, Object>> goals) {
        if (plan == null
                || "COMMUNICATION_ENTRY".equals(
                stringValue(plan.get("rootAuthority")))
                || !selectedEffectsBeginAtRoot(plan, goals)) {
            return;
        }
        Set<String> requestApis = new LinkedHashSet<>();
        for (Map<String, Object> goal : goals) {
            for (Map<String, Object> binding
                    : rows(goal.get("edgeBindings"))) {
                String requestApi = stringValue(binding.get("requestApi"));
                if (!requestApi.isEmpty()) requestApis.add(requestApi);
            }
        }
        if (requestApis.size() != 1) return;
        Map<String, Object> selector = row(plan.get("rootSelector"));
        Map<String, Object> anchor = row(selector.get(CAUSAL_ANCHOR));
        if (!anchor.isEmpty()) {
            anchor.put("requestApi", requestApis.iterator().next());
        }
    }

    /** Whether every selected effect starts in the coarse occurrence root. */
    private static boolean selectedEffectsBeginAtRoot(
            Map<String, Object> plan, List<Map<String, Object>> goals) {
        String rootMethod = stringValue(row(plan.get("rootSelector")).get(
                "method"));
        if (rootMethod.isEmpty()) return false;
        boolean sawMember = false;
        for (Map<String, Object> goal : goals) {
            Map<String, Object> closure = row(goal.get("outputClosure"));
            for (Map<String, Object> member : rows(closure.get("members"))) {
                sawMember = true;
                Map<String, Object> replayEntry = row(
                        row(member.get("slice")).get("replayEntry"));
                String replayMethod = stringValue(replayEntry.get("method"));
                if (!replayMethod.isEmpty()
                        && !rootMethod.equals(replayMethod)) {
                    return false;
                }
            }
        }
        return sawMember;
    }

    /** Whether this binding is the response delivery that scopes this exact
     * server plan. */
    private static boolean exactResponseDeliveryBinding(
            Map<String, Object> binding, StaticProgram.RegionRow region,
            String occurrenceId, String outputPort) {
        if (!"RUNTIME_PROTOCOL_FLOW".equals(stringValue(binding.get("kind")))
                || !CommunicationCatalogContract.DIRECTION_RESPONSE.equals(
                stringValue(binding.get("protocolDirection")))
                || !communicationEffectOutput(region, outputPort,
                occurrenceId)) {
            return false;
        }
        return occurrenceId.equals(stringValue(binding.get(
                "fromOccurrenceId")));
    }


    /** The one declared-cut output port {@code outputPort} names on this
     * occurrence, or {@code null} when it is not a communication site. */
    private static Map<String, Object> communicationOutputPort(
            StaticProgram.RegionRow region, String outputPort,
            String occurrenceId) {
        if (region == null) return null;
        Map<String, Object> port = uniquePort(region.outputs,
                outputPort, occurrenceId);
        return port != null
                && RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT
                .equals(stringValue(port.get("sourceKind"))) ? port : null;
    }

    /** Whether a demanded output is Resp_out at a server-entry return. */
    private static boolean communicationEffectOutput(
            StaticProgram.RegionRow region, String outputPort,
            String occurrenceId) {
        Map<String, Object> port = communicationOutputPort(region,
                outputPort, occurrenceId);
        return port != null
                && CommunicationCatalogContract.CAPTURE_METHOD_RETURN.equals(
                stringValue(port.get(CommunicationCatalogContract
                        .PORT_OUTPUT_CAPTURE_KIND)));
    }


    /** Identifies a semantic output endpoint independently of the runtime port
     * id. */
    static String semanticOutputEndpoint(
            Map<String, Object> binding, StaticProgram.RegionRow region,
            String occurrenceId) {
        if (region == null) return "";
        String portId = stringValue(binding.get("fromOutputPort"));
        Map<String, Object> port = uniquePort(region.outputs,
                portId, occurrenceId);
        if (port == null) return "";
        String cell = stringValue(port.get("cell"));
        if (CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT.equals(
                stringValue(port.get(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND)))) {
            // One exact capture may fan out to several declared wire ports.
            // The port distinguishes those semantic outputs; repeated
            // deliveries of the same port remain versions of one endpoint.
            return "CUT\n" + stringValue(port.get(
                    CommunicationCatalogContract.CALL_SITE_ID))
                    + "\n" + stringValue(port.get("declaredCallee"))
                    + "\narg" + number(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1)
                    + "\n" + stringValue(port.get(
                    CommunicationCatalogContract.PORT_DIRECTION))
                    + "\n" + portId;
        }
        if (CommunicationCatalogContract.CAPTURE_METHOD_RETURN.equals(
                stringValue(port.get(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND)))) {
            return "COMMUNICATION_EFFECT\n" + stringValue(port.get(
                    CommunicationCatalogContract.PORT_DEFINITION_METHOD))
                    + "\n" + stringValue(port.get(
                    CommunicationCatalogContract.PORT_DIRECTION))
                    + "\n" + portId;
        }
        Map<String, Object> access = exactDemandedHeapOutput(port,
                Collections.singletonList(binding), occurrenceId);
        if (access == null) return "";
        List<String> declarations = strings(
                access.get("fieldPathDeclarations"));
        String declaration = declarations.isEmpty() ? cell
                : declarations.get(declarations.size() - 1);
        String kind = stringValue(access.get("bindingKind"));
        String site = stringValue(access.get("staticAccessSiteId"));
        if (kind.isEmpty() || site.isEmpty() || declaration.isEmpty()) {
            return "";
        }
        return "HEAP\n" + kind + "\n" + site + "\n"
                + stringValue(access.get("mutatorDeclaredCallee")) + "\n"
                + declaration;
    }

    private static String selectedOutputPort(
            List<Map<String, Object>> bindings) {
        String selected = "";
        for (Map<String, Object> binding : bindings) {
            String candidate = stringValue(binding.get("fromOutputPort"));
            if (candidate.isEmpty()) return "";
            if (selected.isEmpty()) selected = candidate;
            else if (!selected.equals(candidate)) return "";
        }
        return selected;
    }

    /** Folds output ports that observed one write through different access
     * paths onto one canonical port. */
    private static Map<String, String> canonicalAliasedOutputPorts(
            StaticProgram.RegionRow region, String occurrenceId) {
        Map<String, String> result = new LinkedHashMap<>();
        if (region == null) return result;
        Map<String, Map<String, Object>> canonical = new LinkedHashMap<>();
        List<Map<String, Object>> observed = new ArrayList<>();
        for (Map<String, Object> port : region.outputs) {
            if (!boundTo(port, occurrenceId)) {
                continue;
            }
            String write = observedWriteIdentity(port);
            if (write.isEmpty()) continue;
            observed.add(port);
            Map<String, Object> best = canonical.get(write);
            if (best == null || moreDirectAccessPath(port, best)) {
                canonical.put(write, port);
            }
        }
        for (Map<String, Object> port : observed) {
            Map<String, Object> best = canonical.get(
                    observedWriteIdentity(port));
            result.put(stringValue(port.get("portId")),
                    stringValue(best.get("portId")));
        }
        return result;
    }

    /** Identity of the single write a heap output port observed. */
    private static String observedWriteIdentity(Map<String, Object> port) {
        List<String> declarations = strings(
                port.get("fieldPathDeclarations"));
        long owner = longNumber(port.get("fieldReceiverObjectId"), -1L);
        long event = longNumber(port.get("eventSeq"), -1L);
        if (declarations.isEmpty() || owner < 0L || event < 0L) return "";
        return stringValue(port.get("bindingKind")) + "\n"
                + stringValue(port.get("siteId")) + "\n"
                + stringValue(port.get("mutatorDeclaredCallee")) + "\n"
                + declarations.get(declarations.size() - 1) + "\n"
                + owner + "\n" + event + "\n"
                + longNumber(port.get("valueObjectId"), -1L) + "\n"
                + longNumber(port.get("mutationCompletionSeq"), -1L);
    }

    private static boolean moreDirectAccessPath(Map<String, Object> port,
                                                Map<String, Object> other) {
        List<String> path = strings(port.get("fieldPathDeclarations"));
        List<String> best = strings(other.get("fieldPathDeclarations"));
        if (path.size() != best.size()) return path.size() < best.size();
        int order = String.join("\n", path)
                .compareTo(String.join("\n", best));
        return order != 0 ? order < 0
                : stringValue(port.get("portId")).compareTo(
                        stringValue(other.get("portId"))) < 0;
    }

    /** The demanded bounded write versions of this goal, per endpoint.
     *
     * <p>README REGION-1 keeps every bounded phase of one local occurrence
     * inside that occurrence, so a version here is one guarded phase of the
     * single closure goal and never a goal of its own.</p> */
    static Map<String, List<List<Map<String, Object>>>>
            demandedBindingVersions(
            List<String> outputs,
            Map<String, List<Map<String, Object>>> byOutput,
            int loopBodyBound) {
        Map<String, List<List<Map<String, Object>>>> choicesByOutput =
                new LinkedHashMap<>();
        int modelledVersions = 1;
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
            modelledVersions = Math.max(modelledVersions,
                    Math.min(choices.size(), loopBodyBound));
        }
        Map<String, List<List<Map<String, Object>>>> result =
                new LinkedHashMap<>();
        for (String output : outputs) {
            List<List<Map<String, Object>>> choices =
                    choicesByOutput.get(output);
            // The versions are in recorded write order, so the last modelled
            // one is the latest write this plan carries.
            result.put(output, new ArrayList<>(choices.subList(0,
                    Math.min(choices.size(), modelledVersions))));
        }
        return result;
    }

    /** Slice scope every bounded version of one endpoint contributes to the
     * one coarse member. */
    private static final List<String> VERSION_SCOPE_FIELDS =
            Collections.unmodifiableList(Arrays.asList(
                    "inputPorts", "sites", "staticSites", "methods",
                    "causalEdgeIds", "demandedHeapDeclarations",
                    "captureBindingIssues"));

    /** Exact replay slice retained beside a folded output. */
    static final String BOUNDED_VERSION_SCOPES = "boundedVersionScopes";

    /** Folds the bounded write versions of one demanded endpoint into the one
     * closure member README REGION-1 requires.
     *
     * <p>The fold keeps the union of every version's scope - input ports,
     * methods, branch/static sites and causal edge ids - so no version's
     * slice, and in particular no version's own delivery edge, is dropped from
     * what replay and the scheduler may select.</p> */
    static OutputClosureContract coarseOccurrenceOutputVersions(
            List<OutputClosureContract> versions) {
        if (versions.size() == 1) return versions.get(0);
        JsonObject folded = versions.get(versions.size() - 1).toJson();
        JsonObject anchor = folded.getAsJsonArray("members").get(0)
                .getAsJsonObject().getAsJsonObject("slice");
        JsonArray exactScopes = new JsonArray();
        for (OutputClosureContract versionContract : versions) {
            JsonObject member = versionContract.toJson()
                    .getAsJsonArray("members").get(0).getAsJsonObject();
            JsonObject output = member.getAsJsonObject("output");
            JsonObject version = member.getAsJsonObject("slice");
            // A writer version is one replay boundary, not just one set of
            // incoming edges.  Preserve its complete slice so scheduler
            // projection cannot combine one version's inputs with another
            // version's capture anchor, completion event, or replay entry.
            JsonObject exact = version.deepCopy();
            for (String field : Collections.singletonList(
                    "outputOccurrence")) {
                JsonElement value = output.get(field);
                if (value != null) exact.add(field, value.deepCopy());
            }
            exactScopes.add(exact);
        }
        anchor.add(BOUNDED_VERSION_SCOPES, exactScopes);
        for (int index = 0; index < versions.size() - 1; index++) {
            JsonObject version = versions.get(index).toJson()
                    .getAsJsonArray("members").get(0).getAsJsonObject()
                    .getAsJsonObject("slice");
            for (String field : VERSION_SCOPE_FIELDS) {
                unionStrings(anchor, version, field);
            }
        }
        return OutputClosureCodec.decodeEnvelope(folded);
    }

    /** Adds every value of one slice array the other does not already list. */
    private static void unionStrings(JsonObject target, JsonObject source,
                                     String field) {
        JsonElement added = source.get(field);
        if (added == null || !added.isJsonArray()) return;
        JsonElement present = target.get(field);
        JsonArray union = present != null && present.isJsonArray()
                ? present.getAsJsonArray() : new JsonArray();
        Set<String> seen = new LinkedHashSet<>();
        for (JsonElement value : union) seen.add(value.getAsString());
        for (JsonElement value : added.getAsJsonArray()) {
            if (seen.add(value.getAsString())) union.add(value);
        }
        target.add(field, union);
    }

    /** One reason is published once however many versions reported it. */
    private static void addReasonOnce(List<String> target, String reason) {
        if (!target.contains(reason)) target.add(reason);
    }

    private static void addReasonsOnce(List<String> target,
                                       List<String> reasons) {
        for (String reason : reasons) addReasonOnce(target, reason);
    }

    private static long bindingOccurrenceSeq(Map<String, Object> binding) {
        long writer = longNumber(binding.get("writerEventSeq"), -1L);
        return writer >= 0L ? writer : Long.MIN_VALUE;
    }

    private static String bindingAlternativeIdentity(
            Map<String, List<Map<String, Object>>> selected) {
        List<String> identity = new ArrayList<>();
        for (Map.Entry<String, List<Map<String, Object>>> entry
                : selected.entrySet()) {
            List<String> edges = new ArrayList<>();
            for (Map<String, Object> binding : entry.getValue()) {
                edges.add(stringValue(binding.get("edgeId")) + "@"
                        + bindingOccurrenceSeq(binding));
            }
            Collections.sort(edges);
            identity.add(entry.getKey() + "=" + edges);
        }
        Collections.sort(identity);
        return identity.toString();
    }

    /** Numbers repeated outputs at one static capture endpoint within the
     * bounded producer activation. */
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
                List<Map<String, Object>> captures = rows(
                        slice.get("captureBindings"));
                boolean regionExitField = !captures.isEmpty()
                        && captures.stream().allMatch(capture ->
                        OutputCaptureSpec.REGION_EXIT_FIELD.equals(stringValue(
                                capture.get("captureKind"))));
                if (regionExitField) {
                    // A region-exit field snapshot is selected by its binding
                    // and tracked owner, not by a dynamic write occurrence.
                    continue;
                }
                String siteId = staticOutputSiteId(output, slice);
                String shape = stringValue(output.get("cell")) + "\n"
                        + stringValue(output.get("kind")) + "\n"
                        + stringValue(output.get("javaTypeDescriptor")) + "\n"
                        + siteId;
                int explicit = number(
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
                for (Map<String, Object> capture : captures) {
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
            String captureKind = stringValue(capture.get("captureKind"));
            String method = stringValue(capture.get("definitionMethod"));
            // Every write endpoint is addressed by the unit of the method
            // that defined it; a value handed to a cut is not.
            String unit = method + "#u"
                    + number(capture.get("definitionUnitIndex"), -1);
            String callee = stringValue(capture.get("declaredCallee"));
            String field = stringValue(capture.get("fieldSignature"));
            if (OutputCaptureSpec.CALL_ARGUMENT.equals(captureKind)
                    || OutputCaptureSpec.CALL_RETURN.equals(captureKind)) {
                endpoints.add(captureKind + ":" + unit + ":" + callee
                        + (OutputCaptureSpec.CALL_ARGUMENT.equals(captureKind)
                        ? "#arg" + number(capture.get("argumentIndex"), -1)
                        : ""));
            } else if (OutputCaptureSpec.COMMUNICATION_EFFECT.equals(
                    captureKind)) {
                endpoints.add(captureKind + ":" + method);
            } else if (OutputCaptureSpec.MUTATION_STATE.equals(
                    captureKind)) {
                endpoints.add(captureKind + ":" + unit + ":" + callee
                        + ":" + field);
            } else if (OutputCaptureSpec.FIELD_WRITE_STATE.equals(
                    captureKind)) {
                endpoints.add(captureKind + ":" + unit + ":" + field);
            } else if (OutputCaptureSpec.REGION_EXIT_FIELD.equals(
                    captureKind)) {
                endpoints.add(captureKind + ":" + field + ":"
                        + strings(capture.get("fieldPath")));
            } else {
                throw new IllegalArgumentException(
                        "unsupported output capture kind: " + captureKind);
            }
        }
        if (endpoints.isEmpty()) {
            endpoints.add("REGION_EXIT:" + stringValue(output.get("cell")));
        }
        Collections.sort(endpoints);
        return String.join("|", endpoints);
    }

    private static void putOutputOccurrence(
            Map<String, Object> target, String siteId, int occurrence) {
        target.put("outputSiteId", siteId);
        target.put("outputOccurrence", occurrence);
    }

    private static OutputClosureContract directHeapOutputClosure(
            Map<String, Object> plan, Map<String, Object> goal,
            StaticProgram.RegionRow region, String outputPort,
            List<Map<String, Object>> bindings,
            RefinedFlowIndex refinedFlow, TraceIndex trace,
            int loopBodyBound, List<String> rejectionReasons) {
        if (region == null) return null;
        if (bindings.isEmpty()) return null;
        for (Map<String, Object> binding : bindings) {
            if (!AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                    toJsonTreeFast(binding).getAsJsonObject())) {
                return null;
            }
        }

        String occurrenceId = stringValue(plan.get("occurrenceId"));
        Map<String, Object> outputPortRow = uniquePort(
                region.outputs, outputPort, occurrenceId);
        Map<String, Object> output = exactDemandedHeapOutput(
                outputPortRow, bindings, occurrenceId);
        if (output == null) return null;
        String staticAccessSiteId = stringValue(output.get(
                "staticAccessSiteId"));
        Matcher staticSite = STATIC_SITE.matcher(staticAccessSiteId);
        int recordedOutputOccurrence = number(output.get(
                "activationLocalStaticSiteOccurrence"), -1);
        String bindingKind = stringValue(output.get("bindingKind"));
        // The recorded ordinal is trace provenance only.
        if (!staticSite.matches()) {
            return null;
        }
        String definitionMethod = staticSite.group(1);
        int definitionUnitIndex = Integer.parseInt(staticSite.group(2));
        boolean mutation = "CONTAINER_MUTATION".equals(bindingKind);
        boolean exactFieldAssignment = true;
        for (Map<String, Object> binding : bindings) {
            exactFieldAssignment &= "FIELD_ASSIGNMENT_READ_FROM_V1".equals(
                    stringValue(binding.get("evidenceKind")));
        }
        boolean directFieldWrite = "DECLARED_FIELD_ACCESS".equals(
                bindingKind) || exactFieldAssignment;
        String declaredCallee = stringValue(output.get(
                "mutatorDeclaredCallee"));
        if (!mutation && !directFieldWrite
                || mutation && declaredCallee.isEmpty()) {
            return null;
        }
        List<String> path = strings(output.get("fieldPath"));
        List<String> declarations = strings(
                output.get("fieldPathDeclarations"));
        if (path.isEmpty() || path.size() != declarations.size()) return null;
        String declaration = declarations.get(declarations.size() - 1);

        List<Map<String, Object>> regionInputs = region.symbolicInputs;
        List<Map<String, Object>> regionOutputs = region.outputs;
        Map<String, Object> priorStateInput = null;
        String javaType = leafType(declarations);
        String owner = CausynthStaticFacts.fieldOwner(declaration);
        if ("java.lang.Object".equals(javaType) || owner.isEmpty()) {
            return null;
        }
        String semanticDeclaration = declaration;
        String semanticJavaType = javaType;
        String atomicValueField = mutation
                ? OutputCaptureSpec.atomicArithmeticValueFieldSignature(
                declaredCallee) : "";
        if (!atomicValueField.isEmpty()) {
            FieldPathSpec.DeclaredField carrier =
                    FieldPathSpec.declaredField(declaration);
            FieldPathSpec.DeclaredField atomicLeaf =
                    FieldPathSpec.declaredField(atomicValueField);
            if (carrier == null || atomicLeaf == null
                    || !carrier.type().equals(atomicLeaf.owner())) {
                return null;
            }
            semanticDeclaration = atomicLeaf.signature();
            semanticJavaType = atomicLeaf.type();
        }

        long outputEventSeq = longNumber(output.get("eventSeq"), -1L);
        Set<Long> invocationCalls = trace.exactOutputInvocationCalls(
                traceEvidenceRootCall(plan), outputEventSeq);
        if (invocationCalls == null) {
            rejectionReasons.add("OUTPUT_INVOCATION_UNRESOLVED:"
                    + outputPort);
            return null;
        }
        Set<String> corridorMethods = trace.methodNames(invocationCalls);
        Set<String> allowed = new LinkedHashSet<>(
                strings(goal.get("runtimeDefinitionMethods")));
        Set<String> baselineMethods = new LinkedHashSet<>(strings(
                goal.get("baselineObservedMethods")));
        // One long-lived region occurrence may execute several independent
        // interactions before this output.
        allowed.removeIf(method -> baselineMethods.contains(method)
                && !corridorMethods.contains(method));
        allowed.addAll(corridorMethods);
        ExactMutationFold mutationFold = null;
        long relationBoundarySeq = Math.max(outputEventSeq,
                longNumber(output.get("mutationCompletionSeq"), -1L));
        if (mutation) {
            mutationFold = trace.exactMutationFold(outputEventSeq,
                    definitionMethod, staticAccessSiteId, declaredCallee,
                    number(output.get("valueObjectId"), 0));
            // A mutation relation denotes the state at the definition
            // invocation's normal exit.
            if (mutationFold == null || mutationFold.completions.isEmpty()
                    || mutationFold.completions.size() > loopBodyBound) {
                if (mutationFold != null
                        && mutationFold.completions.size() > loopBodyBound) {
                    addBoundInsufficient(rejectionReasons,
                            "MUTATION_FOLD", outputPort,
                            mutationFold.completions.size(), loopBodyBound);
                }
                return null;
            }
            relationBoundarySeq = mutationFold.normalExitSeq;
        }
        boolean boundedMutation = mutation
                && "BOUNDED_CONTAINER_STATE".equals(
                stringValue(outputPortRow.get("symbolicDemand")))
                && JavaContainerTypes.shape(javaType)
                != JavaContainerTypes.Shape.NONE;
        if (!boundedMutation) {
            priorStateInput = matchingFieldInputBeforeOutput(regionInputs,
                    occurrenceId, output, path, declarations);
        }
        // The corridor is the call chain that performed the store.
        if (!allowed.contains(definitionMethod)) return null;
        String planRootMethod = stringValue(
                row(plan.get("rootSelector")).get("method"));
        Set<String> seedMethods = new LinkedHashSet<>();
        seedMethods.add(planRootMethod);
        seedMethods.add(stringValue(output.get("rootMethod")));
        Map<String, Object> sliceOutput = output;
        if (!mutation) {
            // Runtime heap ports are rooted at the enclosing activation and
            // may not repeat the defining helper/site on the aggregate port.
            sliceOutput = deepCopy(output);
            sliceOutput.put("rootMethod", definitionMethod);
            sliceOutput.put("siteId", staticAccessSiteId);
        }
        ReturnSlice stateSlice = refinedFlow.dependencySlice(
                stringValue(plan.get("regionId")), occurrenceId, declaration,
                sliceOutput, allowed, regionInputs, regionOutputs,
                region.branchPolicies, seedMethods,
                RefinedFlowIndex.outputBoundarySeq(sliceOutput),
                GuardAdmission.EXPLICIT_FAULT_ONLY);
        if (stateSlice == null) return null;

        List<String> inputPorts = new ArrayList<>(stateSlice.inputPorts);
        Map<String, String> exactCommunicationInputs =
                exactPriorCommunicationInputs(goal, regionInputs,
                        occurrenceId, relationBoundarySeq, trace,
                        outputEventSeq);
        for (String port : exactCommunicationInputs.keySet()) {
            if (!inputPorts.contains(port)) inputPorts.add(port);
        }
        if (priorStateInput != null) {
            String priorStatePort = stringValue(priorStateInput.get("portId"));
            // Mutating an existing container depends on its prior bounded
            // state even when the static def-use graph only records the
            // mutator arguments.
            if (!priorStatePort.isEmpty()
                    && !inputPorts.contains(priorStatePort)) {
                inputPorts.add(0, priorStatePort);
            }
        }
        List<String> methods = new ArrayList<>(stateSlice.methods);
        if (methods.isEmpty()) {
            addIfAllowed(methods, allowed, stringValue(output.get(
                    "rootMethod")));
            addIfAllowed(methods, allowed, planRootMethod);
        }
        if (methods.isEmpty()) return null;
        // A communication component can be delivered before the helper that
        // writes this output.
        for (Map<String, Object> input : regionInputs) {
            if (!exactCommunicationInputs.containsKey(
                    stringValue(input.get("portId")))) {
                continue;
            }
            addIfAllowed(methods, allowed,
                    stringValue(input.get("definitionMethod")));
        }
        Set<String> methodSet = new LinkedHashSet<>(methods);
        methodSet.add(definitionMethod);
        methods = new ArrayList<>(methodSet);
        long definitionCallId = mutationFold == null
                ? trace.eventCallIdBySeq.uniqueValue(outputEventSeq)
                : mutationFold.definitionCallId;
        long evidenceRootCall = traceEvidenceRootCall(plan);
        MethodEvent replayContinuation = trace.methodByCall.get(
                evidenceRootCall);
        List<String> staticSites = new ArrayList<>(stateSlice.staticSites);
        if (!addReachingAccessorMaterializations(inputPorts, staticSites,
                regionInputs,
                occurrenceId, methodSet, relationBoundarySeq,
                invocationCalls, rejectionReasons, outputPort)) {
            return null;
        }
        List<Map<String, Object>> exactBranches = exactBranchReplay(
                region.branchPolicies, stateSlice.branchSites,
                trace, invocationCalls, relationBoundarySeq, loopBodyBound,
                rejectionReasons, outputPort);
        if (exactBranches == null) return null;
        boolean explicitFaultExitSnapshot = !mutation
                && priorStateInput != null
                && explicitFaultControlsStateTransition(inputPorts,
                regionInputs, exactBranches, occurrenceId, priorStateInput,
                outputEventSeq);
        removeGuardOnlyPathEnablers(inputPorts,
                stateSlice.guardOnlyInputPorts, regionInputs, occurrenceId,
                outputPort, declaration, stateSlice.branchSites,
                exactBranches, rejectionReasons);

        // README "observed topology and effects, never predicted": an output
        // this occurrence only ever wrote as a recorded constant, with no
        // declared input of its own reaching it, states no relation the
        // occurrence can produce a different answer for. Replay restores it
        // as the constant it was observed to be, so demanding it as a
        // produced member only makes the boundary unsatisfiable -- the
        // NameNode monitor's per-rotation DatanodeDescriptor#needKeyUpdate
        // walk is the case this names. The port stays declared on the
        // region, so a later iteration may still admit it once a replay
        // observes it as a NEW_EFFECT.
        if (!mutation && inputPorts.isEmpty()
                && !stringValue(output.get("primitiveValue")).isEmpty()) {
            rejectionReasons.add("OUTPUT_RECORDED_CONSTANT_NO_RELATION:"
                    + outputPort);
            return null;
        }

        // A repeated semantic output site needs one causal observation that
        // says which dynamic state transition this member belongs to.
        String captureAnchorPort = latestAccessorInputPort(
                inputPorts, regionInputs);

        if (!staticSites.contains(staticAccessSiteId)) {
            staticSites.add(staticAccessSiteId);
        }
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", outputPort);
        slice.addProperty("outputCell", semanticDeclaration);
        slice.add("inputPorts", stringsJson(inputPorts));
        if (!captureAnchorPort.isEmpty()) {
            slice.addProperty("captureAnchorPort", captureAnchorPort);
            String captureAnchorSite = perElementAccessorSite(
                    captureAnchorPort, inputPorts, regionInputs);
            if (!captureAnchorSite.isEmpty()) {
                slice.addProperty("captureAnchorSiteId", captureAnchorSite);
            }
        }
        slice.add("demandedHeapDeclarations", stringsJson(
                stateSlice.demandedHeapDeclarations));
        slice.add("sites", stringsJson(stateSlice.branchSites));
        slice.add("staticSites", stringsJson(staticSites));
        slice.add("methods", stringsJson(methods));
        if (replayContinuation != null && !replayContinuation.receiverType.isEmpty()) {
            slice.add(ExecutionTask.REPLAY_ENTRY, toJsonTreeFast(object(
                    "method", replayContinuation.method,
                    "receiverClass", replayContinuation.receiverType)));
        }
        // A mutation reached here only through a resolved fold.
        int outputOccurrence = mutation ? mutationFold.anchorOccurrence
                : recordedOutputOccurrence;
        if (outputOccurrence < 1) {
            rejectionReasons.add("OUTPUT_OCCURRENCE_UNRESOLVED:"
                    + outputPort);
            return null;
        }
        if (!explicitFaultExitSnapshot) {
            slice.addProperty("activationLocalOccurrence", outputOccurrence);
        }
        slice.addProperty("selectedRuntimeEventSeq", longNumber(
                output.get("eventSeq"), -1L));
        // Exact dynamic definition frame for this output member.
        slice.addProperty("selectedRuntimeCallId", definitionCallId);
        long selectedFieldReceiver = longNumber(
                output.get("fieldReceiverObjectId"), 0L);
        if (!mutation && selectedFieldReceiver != 0L) {
            // Exact trace identity used later to connect a field value
            // produced by one helper invocation to a read of that same object
            // in a later helper invocation of this region.
            slice.addProperty("selectedFieldReceiverObjectId",
                    selectedFieldReceiver);
        }
        String heapBoundaryKind = mutationFold != null
                ? "DEFINITION_INVOCATION_NORMAL_EXIT"
                : explicitFaultExitSnapshot ? "REGION_EXIT_FIELD_SNAPSHOT"
                : "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT";
        slice.addProperty("outputBoundaryKind", heapBoundaryKind);
        if (mutationFold != null) {
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
        }
        addConcretePrimitiveCallReturns(slice, trace, invocationCalls,
                stateSlice.staticSites, inputPorts, regionInputs,
                relationBoundarySeq);

        if (!addTrustedCausalEdgeIds(slice, bindings,
                exactCommunicationInputs.values())) {
            return null;
        }

        JsonObject capture = new JsonObject();
        String captureId = "CAPTURE." + UUID.nameUUIDFromBytes((
                stringValue(plan.get("occurrenceId")) + "\n" + outputPort
                        + "\n" + staticAccessSiteId)
                .getBytes(StandardCharsets.UTF_8));
        capture.addProperty("captureBindingId", captureId);
        capture.addProperty("captureKind", explicitFaultExitSnapshot
                ? OutputCaptureSpec.REGION_EXIT_FIELD : mutation
                ? OutputCaptureSpec.MUTATION_STATE
                : OutputCaptureSpec.FIELD_WRITE_STATE);
        capture.addProperty("outputPort", outputPort);
        capture.addProperty("outputCell", semanticDeclaration);
        List<String> capturePath = new ArrayList<>();
        capturePath.add(path.get(path.size() - 1));
        if (!atomicValueField.isEmpty()) {
            capturePath.add(FieldPathSpec.declaredField(
                    atomicValueField).name());
        }
        capture.add("fieldPath", stringsJson(capturePath));
        capture.addProperty("fieldSignature", semanticDeclaration);
        capture.addProperty("javaType", semanticJavaType);
        if (explicitFaultExitSnapshot) {
            capture.addProperty("accessRootInputPort",
                    stringValue(priorStateInput.get("portId")));
        }
        capture.addProperty("definitionMethod", definitionMethod);
        capture.addProperty("definitionUnitIndex", definitionUnitIndex);
        // Once-only-root rule: a heap write reached only through a callee of
        // the region's root frame (or ahead of a service loop's header) is not
        // dominated by the root body, so a once-entered or cache-guarded write
        // cannot be sampled by every occurrence.  Its recorded version is an
        // instance-level fact, not a per-occurrence obligation -- see
        // OutputCaptureSpec.INSTANCE_SCOPED_PRODUCER.  The port stays declared;
        // only completeness stops demanding a per-occurrence capture of it.
        if (!explicitFaultExitSnapshot
                && instanceScopedHeapWrite(plan, region, definitionMethod,
                        definitionUnitIndex)) {
            capture.addProperty(OutputCaptureSpec.INSTANCE_SCOPED_PRODUCER,
                    true);
        }
        String recordedPrimitiveValue = stringValue(output.get(
                "primitiveValue"));
        if (!mutation && inputPorts.isEmpty()
                && !recordedPrimitiveValue.isEmpty()) {
            capture.addProperty("recordedPrimitiveValue",
                    recordedPrimitiveValue);
        }
        if (mutation) {
            capture.addProperty("declaredCallee", declaredCallee);
        }
        String captureSiteId = mutation
                ? OutputCaptureSpec.MUTATION_STATE + ":"
                + staticAccessSiteId + ":"
                + declaredCallee + ":" + semanticDeclaration
                : OutputCaptureSpec.FIELD_WRITE_STATE + ":"
                + staticAccessSiteId + ":" + semanticDeclaration;
        if (!explicitFaultExitSnapshot) {
            capture.addProperty("outputSiteId", captureSiteId);
            capture.addProperty("outputOccurrence", outputOccurrence);
        }
        if (mutationFold != null) {
            capture.addProperty("occurrenceScope",
                    "DEFINITION_INVOCATION");
        } else if (!explicitFaultExitSnapshot) {
            capture.addProperty("occurrenceScope",
                    OutputCaptureSpec.REGION_ACTIVATION_SCOPE);
        }
        capture.addProperty("outputBoundaryKind", heapBoundaryKind);
        if (mutationFold != null) {
            capture.addProperty("definitionCompletionSeq",
                    mutationFold.normalExitSeq);
            capture.addProperty("foldedMutationCount",
                    mutationFold.completions.size());
        }
        addCaptureBinding(slice, capture);

        return OutputClosureCodec.singleton(
                stringValue(plan.get("relationKey")),
                stringValue(plan.get("regionId")),
                        Collections.<String>emptyList(),
                outputPort, semanticDeclaration, "HEAP_STATE",
                semanticJavaType, slice);
    }

    /**
     * Whether a heap-write demand names a write that is not dominated by the
     * region's root body, so its recorded version is an instance-level fact
     * rather than a per-occurrence obligation.
     *
     * <p>Judged from evidence the planner already holds and with no
     * workload-specific names.  A write directly in the region's own root
     * frame -- the {@code rootSelector} method, or the loop-holding method of
     * a {@code LOOP_BODY_ROOT} region within its loop body -- runs on the root
     * path of every occurrence and stays a per-occurrence demand.  A write
     * reached only through a callee of that frame (or ahead of a service
     * loop's header) is once-entered or cache-guarded: it cannot be sampled by
     * every occurrence, so an occurrence that did not observe it is not
     * incomplete because of it (the version is captured wherever an
     * occurrence's window did contain it, and a consumer still references a
     * real recorded version or is refused by name).  Only heap-write demands
     * carry this flag, and no matrix skeleton declares one, so this is inert
     * there.</p>
     */
    private static boolean instanceScopedHeapWrite(
            Map<String, Object> plan, StaticProgram.RegionRow region,
            String definitionMethod, int definitionUnitIndex) {
        if (definitionMethod == null || definitionMethod.isEmpty()) {
            return false;
        }
        // A write in the region's own root frame is root-body-local.
        String rootMethod = stringValue(
                row(plan.get("rootSelector")).get("method"));
        if (definitionMethod.equals(rootMethod)) return false;
        if (region != null && region.rootLoop != null) {
            String rootLoopMethod = stringValue(
                    region.rootLoop.get(LoopBoundPolicy.ROOT_LOOP_METHOD));
            if (definitionMethod.equals(rootLoopMethod)) {
                // In the loop-holding method: root-body-local unless it lies
                // ahead of the loop header, where it runs before the loop.
                int header = number(region.rootLoop.get(
                        LoopBoundPolicy.HEADER_UNIT_INDEX), -1);
                return header >= 0 && definitionUnitIndex >= 0
                        && definitionUnitIndex < header;
            }
        }
        // Reached only through a callee of the root frame: not dominated by
        // the root body, so a once-entered / cache-guarded write cannot be
        // sampled by every occurrence.
        return true;
    }

    /** The concrete interaction that supplied a heap output's structured
     * live-in. */
    private static Map<String, String> exactPriorCommunicationInputs(
            Map<String, Object> goal,
            List<Map<String, Object>> regionInputs,
            String occurrenceId,
            long outputBoundarySeq,
            TraceIndex trace,
            long outputEventSeq) {
        if (outputBoundarySeq < 0L || occurrenceId.isEmpty()
                || trace == null) {
            return Collections.emptyMap();
        }
        Set<String> communicationPorts = new LinkedHashSet<>();
        for (Map<String, Object> input : regionInputs) {
            if (!RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT.equals(
                    stringValue(input.get("sourceKind")))) {
                continue;
            }
            String portId = stringValue(input.get("portId"));
            if (!portId.isEmpty()) communicationPorts.add(portId);
        }
        if (communicationPorts.isEmpty()) return Collections.emptyMap();

        long outputRemoteSpan = trace.remoteParentSpanAt(outputEventSeq);
        List<Map<String, Object>> prior = new ArrayList<>();
        List<Map<String, Object>> sameSpan = new ArrayList<>();
        for (Map<String, Object> binding : rows(goal.get("edgeBindings"))) {
            if (!"RUNTIME_PROTOCOL_FLOW".equals(stringValue(binding.get(
                    "kind")))
                    || !occurrenceId.equals(
                    stringValue(binding.get("toOccurrenceId")))) {
                continue;
            }
            String portId = stringValue(binding.get("toInputPort"));
            long receivedAt = longNumber(
                    binding.get("receiverEventSeq"), -1L);
            if (!communicationPorts.contains(portId) || receivedAt < 0L
                    || receivedAt >= outputBoundarySeq) {
                continue;
            }
            prior.add(binding);
            ProtocolEvent delivery = trace.protocol(receivedAt);
            if (outputRemoteSpan > 0L && delivery != null
                    && delivery.remoteParentSpanId == outputRemoteSpan) {
                sameSpan.add(binding);
            }
        }
        List<Map<String, Object>> candidates = sameSpan.isEmpty()
                ? prior : sameSpan;
        return exactProtocolDeliveryInput(candidates);
    }

    /** Selects the latest observed delivery. */
    static Map<String, String> exactProtocolDeliveryInput(
            List<Map<String, Object>> candidates) {
        Map<String, Object> selected = null;
        for (Map<String, Object> candidate : candidates) {
            long seq = longNumber(candidate.get("receiverEventSeq"), -1L);
            long selectedSeq = selected == null ? -1L : longNumber(
                    selected.get("receiverEventSeq"), -1L);
            String identity = protocolDeliveryIdentity(candidate);
            String selectedIdentity = selected == null ? ""
                    : protocolDeliveryIdentity(selected);
            if (selected == null || seq > selectedSeq
                    || seq == selectedSeq
                    && identity.compareTo(selectedIdentity) < 0) {
                selected = candidate;
            }
        }
        if (selected == null) return Collections.emptyMap();

        String portId = stringValue(selected.get("toInputPort"));
        String edgeId = stringValue(selected.get("edgeId"));
        if (portId.isEmpty() || edgeId.isEmpty()) {
            return Collections.emptyMap();
        }
        Map<String, String> result = new LinkedHashMap<>();
        result.put(portId, edgeId);
        return result;
    }

    /** Stable identity of one observed protocol delivery, excluding port. */
    private static String protocolDeliveryIdentity(
            Map<String, Object> binding) {
        String direction = stringValue(binding.get("direction"));
        if (direction.isEmpty()) {
            direction = stringValue(binding.get("protocolDirection"));
        }
        return stringValue(binding.get("fromOccurrenceId")) + "\n"
                + stringValue(binding.get("toOccurrenceId")) + "\n"
                + stringValue(binding.get(
                CommunicationCatalogContract.EXCHANGE_SITE_KEY)) + "\n"
                + stringValue(binding.get("attemptId")) + "\n"
                + direction + "\n"
                + longNumber(binding.get("senderEventSeq"), -1L) + "\n"
                + longNumber(binding.get("receiverEventSeq"), -1L);
    }

    /** Writes the two-part identity every dynamic output boundary requires. */
    static boolean addExactOutputBoundary(
            JsonObject destination, long eventSeq, long callId) {
        if (destination == null || eventSeq <= 0L || callId <= 0L) {
            return false;
        }
        destination.addProperty("selectedRuntimeEventSeq", eventSeq);
        destination.addProperty("selectedRuntimeCallId", callId);
        return true;
    }

    /** Boundary label of a relation whose output is a value handed to a cut.
     */
    private static final String CUT_ARGUMENT_BOUNDARY =
            "EXACT_CALL_ARGUMENT_AT_CUT";

    private static final String CUT_RETURN_BOUNDARY =
            "EXACT_CALL_RETURN_AT_CUT";

    /** A semantic server return reached its declared response event. */
    private static final String COMMUNICATION_EFFECT_BOUNDARY =
            "DECLARED_COMMUNICATION_EFFECT";

    /** Closes one declared communication output on the exact frame that
     * produced it.
     *
     * <p>With {@code callArgument} this closes {@code T_C0}'s request half on
     * the cut argument itself: README section 3 gives a client prefix the
     * shape {@code T_C0(Input, Live_out, Req_out)} and sends {@code Req_out}
     * across the cut through the VM broker.  Otherwise it closes the guarded
     * server interaction at its real normal return.</p> */
    private static OutputClosureContract declaredCutOutputClosure(
            Map<String, Object> plan, Map<String, Object> goal,
            StaticProgram.RegionRow region, String outputPort,
            List<Map<String, Object>> bindings,
            RefinedFlowIndex refinedFlow, TraceIndex trace,
            int loopBodyBound, List<String> rejectionReasons,
            String captureKind) {
        if (region == null) return null;
        boolean callArgument = CommunicationCatalogContract
                .CAPTURE_CALL_ARGUMENT.equals(captureKind);
        boolean callReturn = CommunicationCatalogContract
                .CAPTURE_CALL_RETURN.equals(captureKind);
        boolean callOutput = callArgument || callReturn;
        String reason = callArgument ? "CUT_ARGUMENT"
                : callReturn ? "CUT_RETURN" : "COMMUNICATION_EFFECT";
        String occurrenceId = stringValue(plan.get("occurrenceId"));
        String regionId = stringValue(plan.get("regionId"));
        Map<String, Object> port = uniquePort(region.outputs,
                outputPort, occurrenceId);
        if (port == null || !captureKind.equals(
                stringValue(port.get(CommunicationCatalogContract
                        .PORT_OUTPUT_CAPTURE_KIND)))) {
            return null;
        }
        String definitionMethod = stringValue(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        String javaType = stringValue(port.get("javaType"));
        int definitionUnitIndex = number(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX), -1);
        int argumentIndex = number(port.get(
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1);
        String declaredCallee = stringValue(port.get("declaredCallee"));
        String cutSiteId = stringValue(port.get(
                CommunicationCatalogContract.CALL_SITE_ID));
        // Both halves of a cut site have to agree.
        if (definitionMethod.isEmpty() || javaType.isEmpty()
                || callOutput && (definitionUnitIndex < 0
                || callArgument && argumentIndex < 0
                || declaredCallee.isEmpty()
                || !DependencyRole.VALUE_FRONTIER.equals(
                effectiveDependencyRole(port, javaType))
                || !cutSiteId.equals(definitionMethod + "#u"
                + definitionUnitIndex))) {
            rejectionReasons.add(reason + "_PORT_INCOMPLETE:" + outputPort);
            return null;
        }

        if (bindings.isEmpty()) return null;
        for (Map<String, Object> binding : bindings) {
            if (!occurrenceId.equals(stringValue(binding.get(
                    "fromOccurrenceId")))
                    || !AutomaticRegionEdge.schedulableProducerBinding(
                    toJsonTreeFast(binding).getAsJsonObject())) {
                rejectionReasons.add(reason + "_BINDING_UNSCHEDULABLE:"
                        + outputPort + ":" + stringValue(binding.get(
                                "edgeId")));
                return null;
            }
        }

        long rootCallId = traceEvidenceRootCall(plan);
        String sliceCell = definitionMethod + ".return";
        RuntimeEvent boundary;
        if (callOutput) {
            sliceCell = refinedFlow.cutArgumentCell(regionId,
                    definitionMethod, cutSiteId, declaredCallee,
                    argumentIndex);
            if (callReturn) {
                sliceCell = refinedFlow.callReturnCell(regionId,
                        definitionMethod, cutSiteId, declaredCallee);
            }
            if (sliceCell.isEmpty()) {
                rejectionReasons.add(reason + "_VALUE_CELL_UNRESOLVED:"
                        + outputPort);
                return null;
            }
            List<RuntimeEvent> evaluations = trace.callEvents(
                    trace.subtree(rootCallId), cutSiteId, declaredCallee,
                    callArgument ? "CALL_ARGUMENT" : "CALL_SITE_RETURN",
                    argumentIndex);
            if (evaluations.size() != 1) {
                if (evaluations.isEmpty()) {
                    rejectionReasons.add(reason + "_UNOBSERVED:"
                            + outputPort);
                } else {
                    // Several evaluations of one cut argument inside one
                    // activation are several deliveries of one exchange.
                    addBoundInsufficient(rejectionReasons,
                            "CUT_ARGUMENT_OCCURRENCE", outputPort,
                            evaluations.size(), 1);
                }
                return null;
            }
            boundary = evaluations.get(0);
        } else {
            boundary = trace.uniqueNormalMethodExit(rootCallId,
                    definitionMethod);
            if (boundary == null) {
                rejectionReasons.add(reason + "_UNOBSERVED:" + outputPort);
                return null;
            }
        }

        Set<Long> invocationCalls = trace.exactOutputInvocationCalls(
                rootCallId, boundary.seq);
        if (invocationCalls == null) {
            rejectionReasons.add(reason + "_INVOCATION_UNRESOLVED:"
                    + outputPort);
            return null;
        }
        Set<String> corridorMethods = trace.methodNames(invocationCalls);
        Set<String> allowed = new LinkedHashSet<>(
                strings(goal.get("runtimeDefinitionMethods")));
        if (callOutput) {
            // One long-lived region occurrence may execute several
            // independent interactions before this output.
            Set<String> baselineMethods = new LinkedHashSet<>(strings(
                    goal.get("baselineObservedMethods")));
            allowed.removeIf(method -> baselineMethods.contains(method)
                    && !corridorMethods.contains(method));
        }
        allowed.addAll(corridorMethods);
        // The corridor is the call chain the cut argument was evaluated in;
        // a server return declares its own definition instead.
        if (!allowed.contains(definitionMethod)) {
            if (callOutput) return null;
            allowed.add(definitionMethod);
        }

        List<Map<String, Object>> regionInputs = region.symbolicInputs;
        List<Map<String, Object>> regionOutputs = region.outputs;
        List<Map<String, Object>> branchPolicies = region.branchPolicies;
        ReturnSlice outputSlice = refinedFlow.dependencySlice(
                regionId, occurrenceId, sliceCell, null, allowed,
                regionInputs, regionOutputs, branchPolicies,
                Collections.singleton(definitionMethod),
                boundary.seq, GuardAdmission.RELATION_INPUT_PORT);
        if (outputSlice == null) {
            if (!callArgument) {
                rejectionReasons.add(reason + "_GUARD_SLICE_UNRESOLVED:"
                        + outputPort);
            }
            return null;
        }

        List<String> inputPorts = new ArrayList<>(outputSlice.inputPorts);
        Set<String> methodSet = new LinkedHashSet<>(outputSlice.methods);
        methodSet.add(definitionMethod);
        methodSet.retainAll(allowed);
        if (methodSet.isEmpty()) return null;
        List<String> staticSites = new ArrayList<>(outputSlice.staticSites);
        if (!addReachingAccessorMaterializations(inputPorts, staticSites,
                regionInputs,
                occurrenceId, methodSet, boundary.seq, invocationCalls,
                rejectionReasons, outputPort)) {
            return null;
        }
        List<Map<String, Object>> exactBranches = exactBranchReplay(
                branchPolicies, outputSlice.branchSites, trace,
                invocationCalls, boundary.seq, loopBodyBound,
                rejectionReasons, outputPort);
        if (exactBranches == null) return null;
        removeGuardOnlyPathEnablers(inputPorts,
                outputSlice.guardOnlyInputPorts, regionInputs, occurrenceId,
                outputPort, sliceCell, outputSlice.branchSites,
                exactBranches, rejectionReasons);
        // A relation whose output does not depend on a single declared input
        // is not this occurrence's relation: it says the request is constant,
        // which would let the campaign run a producer that can never answer
        // a different question than the seed already did.
        if (callOutput && inputPorts.isEmpty()) {
            rejectionReasons.add(reason + "_RELATION_HAS_NO_INPUT:"
                    + outputPort);
            return null;
        }

        if (callOutput && !staticSites.contains(cutSiteId)) {
            staticSites.add(cutSiteId);
        }
        String outputCell = callOutput ? (callReturn
                ? declaredCallee + ".return" : sliceCell)
                : definitionMethod + ".communication.response";
        String boundaryKind = callArgument ? CUT_ARGUMENT_BOUNDARY
                : callReturn ? CUT_RETURN_BOUNDARY
                : COMMUNICATION_EFFECT_BOUNDARY;

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", outputPort);
        slice.addProperty("outputCell", outputCell);
        slice.add("inputPorts", stringsJson(inputPorts));
        slice.add("demandedHeapDeclarations", stringsJson(
                outputSlice.demandedHeapDeclarations));
        slice.add("sites", stringsJson(outputSlice.branchSites));
        slice.add("staticSites", stringsJson(staticSites));
        slice.add("methods", stringsJson(methodSet));
        slice.addProperty("activationLocalOccurrence", 1);
        // A call-argument cut is also a dynamic output boundary, and the event
        // sequence that orders a response does not by itself identify the
        // dynamic definition frame that produced it.
        if (!addExactOutputBoundary(slice, boundary.seq, boundary.callId)) {
            rejectionReasons.add(reason + "_BOUNDARY_IDENTITY_MISSING:"
                    + outputPort);
            return null;
        }
        slice.addProperty("outputBoundaryKind", boundaryKind);
        addConcretePrimitiveCallReturns(slice, trace, invocationCalls,
                outputSlice.staticSites, inputPorts, regionInputs,
                boundary.seq);
        if (!addTrustedCausalEdgeIds(slice, bindings,
                Collections.<String>emptyList())) {
            return null;
        }

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE."
                + UUID.nameUUIDFromBytes((occurrenceId + "\n" + outputPort
                + "\n" + (callOutput
                ? cutSiteId + "\n" + declaredCallee + "\n" + argumentIndex
                : definitionMethod + "\nCOMMUNICATION_EFFECT"))
                .getBytes(StandardCharsets.UTF_8)));
        capture.addProperty("captureKind", callOutput ? captureKind
                : OutputCaptureSpec.COMMUNICATION_EFFECT);
        capture.addProperty("outputPort", outputPort);
        capture.addProperty("outputCell", outputCell);
        capture.addProperty("javaType", javaType);
        capture.addProperty("definitionMethod", definitionMethod);
        if (callOutput) {
            capture.addProperty("definitionUnitIndex", definitionUnitIndex);
            capture.addProperty("declaredCallee", declaredCallee);
            if (callArgument) {
                capture.addProperty("argumentIndex", argumentIndex);
            }
        }
        capture.addProperty("occurrenceScope",
                OutputCaptureSpec.REGION_ACTIVATION_SCOPE);
        capture.addProperty("outputBoundaryKind", boundaryKind);
        // The same static endpoint assignOutputOccurrenceIdentity derives, so
        // the contract sees one answer here and one answer there.
        capture.addProperty("outputSiteId", callOutput
                ? captureKind + ":" + definitionMethod + "#u"
                + definitionUnitIndex + ":" + declaredCallee
                + (callArgument ? "#arg" + argumentIndex : "")
                : OutputCaptureSpec.COMMUNICATION_EFFECT + ":"
                + definitionMethod);
        capture.addProperty("outputOccurrence", 1);
        addCaptureBinding(slice, capture);

        try {
            return OutputClosureCodec.singleton(
                    stringValue(plan.get("relationKey")), regionId,
                    declaredOutputPortIds(regionOutputs), outputPort,
                    outputCell, callOutput
                            ? "REGION_OUTPUT" : "INTERACTION_EVENT",
                    javaType, slice);
        } catch (IllegalArgumentException refused) {
            // The canonical output-closure contract is the authority on what a
            // producer output may be, and it is asked rather than second
            // guessed.
            rejectionReasons.add(GAP_CUT_OUTPUT_PORT_REFUSED + ":"
                    + outputPort);
            return null;
        }
    }

    /** Publishes the distinct trusted producer edges a closure rests on,
     * plus any further edge its live-ins were delivered on. */
    private static boolean addTrustedCausalEdgeIds(
            JsonObject slice, List<Map<String, Object>> trusted,
            Collection<String> alsoAdmitted) {
        JsonArray edgeIds = new JsonArray();
        Set<String> seenEdges = new LinkedHashSet<>();
        for (Map<String, Object> binding : trusted) {
            String edgeId = stringValue(binding.get("edgeId"));
            if (edgeId.isEmpty() || !seenEdges.add(edgeId)) continue;
            edgeIds.add(edgeId);
        }
        for (String edgeId : alsoAdmitted) {
            if (!edgeId.isEmpty() && seenEdges.add(edgeId)) {
                edgeIds.add(edgeId);
            }
        }
        if (edgeIds.size() == 0) return false;
        slice.add("causalEdgeIds", edgeIds);
        return true;
    }

    /** Closes a slice with the one capture binding it publishes. */
    private static void addCaptureBinding(
            JsonObject slice, JsonObject capture) {
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());
    }

    /** The output ports the region declares that its own region identity
     * does not mint, which is the exact set an output-closure contract
     * publishes: a region-scoped port is admitted by that identity alone, so
     * re-declaring it says nothing about a consumer. */
    private static List<String> contractDeclaredOutputPorts(
            StaticProgram.RegionRow region) {
        if (region == null) return Collections.emptyList();
        String regionScoped = region.regionId + ".out.";
        List<String> declared = new ArrayList<>();
        for (String portId : declaredOutputPortIds(region.outputs)) {
            if (portId.startsWith(regionScoped)
                    && portId.length() > regionScoped.length()) {
                continue;
            }
            declared.add(portId);
        }
        return declared;
    }

    /** Every output port id the region declared, exactly as declared. */
    private static List<String> declaredOutputPortIds(
            List<Map<String, Object>> regionOutputs) {
        List<String> ids = new ArrayList<>();
        for (Map<String, Object> port : regionOutputs) {
            String id = stringValue(port.get("portId"));
            if (!id.isEmpty()) ids.add(id);
        }
        return ids;
    }

    /** A declared cut output the canonical closure contract will not carry. */
    static final String GAP_CUT_OUTPUT_PORT_REFUSED =
            "CUT_OUTPUT_PORT_OUTSIDE_CLOSURE_CONTRACT";

    /** Adds only accessor observations that can reach the selected exact
     * output. */
    private static boolean addReachingAccessorMaterializations(
            List<String> inputPorts,
            List<String> staticSites,
            List<Map<String, Object>> regionInputs,
            String occurrenceId, Set<String> selectedMethods,
            long outputBoundarySeq, Set<Long> invocationCalls,
            List<String> rejectionReasons, String outputPort) {
        if (outputBoundarySeq < 0L) return true;
        if (invocationCalls != null) {
            Map<String, List<Map<String, Object>>> byActivationEndpoint =
                    new LinkedHashMap<>();
            for (Map<String, Object> candidate : regionInputs) {
                if (!boundTo(candidate, occurrenceId)
                        || !"ACCESSOR_RETURN".equals(
                        stringValue(candidate.get("sourceKind")))) {
                    continue;
                }
                MaterializationSpec materialization = accessor(candidate);
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
                        + materialization.rootField() + "\n"
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
                addNonBlankUnique(inputPorts,
                        stringValue(candidate.get("portId")));
                addNonBlankUnique(staticSites, accessorSiteKey(candidate));
            }
            return true;
        }

        Map<String, Map<String, Object>> latestByEndpoint =
                new LinkedHashMap<>();
        Set<String> ambiguousEndpoints = new LinkedHashSet<>();
        for (Map<String, Object> candidate : regionInputs) {
            if (!boundTo(candidate, occurrenceId)
                    || !"ACCESSOR_RETURN".equals(
                    stringValue(candidate.get("sourceKind")))) {
                continue;
            }
            MaterializationSpec materialization = accessor(candidate);
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
                    + materialization.rootField() + "\n"
                    + materialization.path();
            Map<String, Object> prior = latestByEndpoint.get(endpoint);
            long priorSeq = prior == null ? -1L
                    : longNumber(prior.get("eventSeq"), -1L);
            if (eventSeq > priorSeq) {
                latestByEndpoint.put(endpoint, candidate);
                ambiguousEndpoints.remove(endpoint);
            } else if (eventSeq == priorSeq && prior != null
                    && !stringValue(prior.get("portId")).equals(
                    stringValue(candidate.get("portId")))) {
                ambiguousEndpoints.add(endpoint);
            }
        }
        for (Map.Entry<String, Map<String, Object>> selected
                : latestByEndpoint.entrySet()) {
            if (ambiguousEndpoints.contains(selected.getKey())) {
                // Two ports of one endpoint at one event are not one
                // materialization; neither is chosen, and the input the
                // relation therefore does not carry is named.
                rejectionReasons.add("ACCESSOR_MATERIALIZATION_AMBIGUOUS:"
                        + outputPort + ":"
                        + selected.getKey().replace('\n', '|'));
                continue;
            }
            Map<String, Object> candidate = selected.getValue();
            addNonBlankUnique(inputPorts,
                    stringValue(candidate.get("portId")));
            addNonBlankUnique(staticSites, accessorSiteKey(candidate));
        }
        return true;
    }

    private static void addNonBlankUnique(List<String> values, String value) {
        if (!value.isEmpty() && !values.contains(value)) values.add(value);
    }

    /**
     * The accessor site one capture anchor names when this member's inputs
     * hold more than one occurrence of it, or {@code ""} when the anchor is
     * a single observation.
     *
     * <p>README decision 2026-08-25 (declare fields, never occurrences or
     * selectors): a per-element mint site contributes one input port per
     * container element, so the latest observation of it is the last
     * element's ordinal. Pinning the anchor there writes discovery's
     * container cardinality into the demand -- the NameNode monitor anchored
     * its {@code allKeys} mutation on occurrence 49 of
     * {@code DelegationKey#expiryDate} -- and no replay whose map holds a
     * different number of keys can answer it. The site is what the member is
     * anchored on; which element minted it is not a fact the plan may
     * require, so the site travels beside the port and a prerequisite
     * derived from it is satisfied by any occurrence of that site.</p>
     */
    private static String perElementAccessorSite(
            String anchorPort, List<String> inputPorts,
            List<Map<String, Object>> regionInputs) {
        if (anchorPort == null || anchorPort.isEmpty()
                || regionInputs == null) {
            return "";
        }
        Map<String, String> siteByPort = new LinkedHashMap<>();
        Map<String, String> fieldByPort = new LinkedHashMap<>();
        for (Map<String, Object> candidate : regionInputs) {
            String port = stringValue(candidate.get("portId"));
            if (port.isEmpty() || !"ACCESSOR_RETURN".equals(
                    stringValue(candidate.get("sourceKind")))) {
                continue;
            }
            String site = accessorSiteKey(candidate);
            String field = firstAccessorField(candidate);
            if (!site.isEmpty()) siteByPort.putIfAbsent(port, site);
            if (!field.isEmpty()) fieldByPort.putIfAbsent(port, field);
        }
        String site = siteByPort.get(anchorPort);
        String field = fieldByPort.get(anchorPort);
        if (site == null || field == null) return "";
        int occurrences = 0;
        for (String port : new LinkedHashSet<>(inputPorts)) {
            if (site.equals(siteByPort.get(port))
                    && field.equals(fieldByPort.get(port))
                    && ++occurrences > 1) {
                return site;
            }
        }
        return "";
    }

    /** The one static site an accessor input port was read at. */
    private static String accessorSiteKey(Map<String, Object> port) {
        String declared = stringValue(port.get("staticAccessSiteId"));
        if (!declared.isEmpty()) return declared;
        String caller = stringValue(port.get("callerMethod"));
        int unitIndex = number(port.get("unitIndex"), -1);
        if (!caller.isEmpty() && unitIndex >= 0) {
            return caller + "#u" + unitIndex;
        }
        List<String> sites = strings(port.get("accessSites"));
        return sites.size() == 1 ? sites.get(0) : "";
    }

    /** The declared field an accessor input port returns. */
    private static String firstAccessorField(Map<String, Object> port) {
        for (String name : new String[]{"accessFieldSignature",
                "declaredFieldSignature", "leafFieldSignature", "cell"}) {
            String value = stringValue(port.get(name));
            if (!value.isEmpty()) return value;
        }
        return "";
    }

    static String latestAccessorInputPort(
            List<String> inputPorts,
            List<Map<String, Object>> regionInputs) {
        if (inputPorts == null || inputPorts.isEmpty()
                || regionInputs == null || regionInputs.isEmpty()) {
            return "";
        }
        Set<String> admitted = new LinkedHashSet<>(inputPorts);
        String selected = "";
        long selectedSeq = -1L;
        boolean ambiguous = false;
        for (Map<String, Object> candidate : regionInputs) {
            String port = stringValue(candidate.get("portId"));
            if (!admitted.contains(port)
                    || !"ACCESSOR_RETURN".equals(
                    stringValue(candidate.get("sourceKind")))) {
                continue;
            }
            long eventSeq = longNumber(candidate.get("eventSeq"), -1L);
            if (eventSeq > selectedSeq) {
                selected = port;
                selectedSeq = eventSeq;
                ambiguous = false;
            } else if (eventSeq == selectedSeq
                    && eventSeq >= 0L && !selected.equals(port)) {
                ambiguous = true;
            }
        }
        return selectedSeq >= 0L && !ambiguous ? selected : "";
    }

    /** Exact, invocation-local replay ordinals for a projected output. */
    private static List<Map<String, Object>> exactBranchReplay(
            List<Map<String, Object>> policies, Set<String> selectedSites,
            TraceIndex trace, Set<Long> invocationCalls,
            long outputBoundarySeq, int loopBodyBound,
            List<String> rejectionReasons, String outputPort) {
        List<Map<String, Object>> result = new ArrayList<>();
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
            String site = stringValue(policy.get("siteId"));
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
            if (selected.size() > loopBodyBound) {
                // Truncating an exact demanded branch stream changes the state
                // relation.
                addBoundInsufficient(rejectionReasons, "BRANCH_REPLAY",
                        outputPort, selected.size(), loopBodyBound);
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
                Map<String, Object> occurrence = object(
                        "occurrence", index + 1,
                        "outcome", event.outcome,
                        "eventSeq", event.seq,
                        "callId", event.callId);
                addExactSwitchDecision(occurrence, event);
                occurrences.add(occurrence);
            }
            replay.put("occurrences", occurrences);
            result.add(replay);
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

    /** Records selected primitive call returns that intentionally remain
     * concrete. */
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
            if (!selectedPorts.contains(stringValue(input.get(
                    "portId")))) continue;
            MaterializationSpec materialization = accessor(input);
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

    /** Materializes the concrete write selected by the demanded causal edge.
     */
    private static Map<String, Object> exactDemandedHeapOutput(
            Map<String, Object> port,
            List<Map<String, Object>> bindings,
            String occurrenceId) {
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
            if (!boundTo(access, occurrenceId)) {
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
        String site = stringValue(selected.get("staticAccessSiteId"));
        // The static endpoint identifies the relation.
        if (!STATIC_SITE.matcher(site).matches()) {
            return null;
        }
        Map<String, Object> exact = deepCopy(port);
        for (Map.Entry<String, Object> entry : selected.entrySet()) {
            exact.put(entry.getKey(), entry.getValue());
        }
        return exact;
    }

    private static Map<String, Object> uniquePort(
            List<Map<String, Object>> ports, String portId,
            String occurrenceId) {
        return uniquePort(ports, portId, occurrenceId, false);
    }

    /** The one port of this activation with {@code portId}, or null when the
     * activation has none or several. */
    private static Map<String, Object> uniquePort(
            List<Map<String, Object>> ports, String portId,
            String occurrenceId, boolean input) {
        Map<String, Object> match = null;
        for (Map<String, Object> port : ports) {
            if (!portId.equals(stringValue(port.get("portId")))
                    || !(input ? boundToInput(port, occurrenceId)
                    : boundTo(port, occurrenceId))) {
                continue;
            }
            if (match != null) return null;
            match = port;
        }
        return match;
    }

    private static Map<String, Object> matchingFieldInputBeforeOutput(
            List<Map<String, Object>> inputs, String occurrenceId,
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
            if (!boundTo(input, occurrenceId)
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
                    && !stringValue(match.get("portId")).equals(
                    stringValue(input.get("portId")))) {
                return null;
            }
        }
        return match;
    }

    /** Proves the minimal state-merge shape used by modeled RPC failure: the
     * exact field pre-state is read, an explicit symbolic fault decides
     * whether the update runs, and the recorded write follows that decision.
     */
    private static boolean explicitFaultControlsStateTransition(
            List<String> inputPorts, List<Map<String, Object>> inputs,
            List<Map<String, Object>> branches, String occurrenceId,
            Map<String, Object> preState, long outputEventSeq) {
        long preStateSeq = longNumber(preState.get("eventSeq"), -1L);
        if (preStateSeq < 0L || outputEventSeq <= preStateSeq) return false;
        Set<String> selected = new LinkedHashSet<>(inputPorts);
        long faultSeq = Long.MAX_VALUE;
        for (Map<String, Object> input : inputs) {
            long seq = longNumber(input.get("eventSeq"), -1L);
            if (boundTo(input, occurrenceId)
                    && selected.contains(stringValue(input.get("portId")))
                    && RuntimeSelectedRegionFinalizer
                    .EXPLICIT_SYMBOLIC_FAULT.equals(
                    stringValue(input.get("sourceKind")))
                    && seq > preStateSeq && seq < outputEventSeq) {
                faultSeq = Math.min(faultSeq, seq);
            }
        }
        if (faultSeq == Long.MAX_VALUE) return false;
        for (Map<String, Object> branch : branches) {
            long seq = longNumber(branch.get("selectedRuntimeEventSeq"),
                    -1L);
            if ("PATH_ASSUMPTION".equals(stringValue(branch.get("policy")))
                    && seq > faultSeq && seq < outputEventSeq) {
                return true;
            }
        }
        return false;
    }

    private static void addIfAllowed(Collection<String> methods,
                                     Set<String> allowed, String method) {
        if (!method.isEmpty() && allowed.contains(method)
                && !CausynthStaticFacts.constructor(method)
                && !methods.contains(method)) {
            methods.add(method);
        }
    }

    /** Keeps a producer's observed reachability guards concrete when their
     * symbolic-state authority belongs to a different output mutation.
     *
     * <p>The value/control distinction is already available from {@link
     * RefinedFlowIndex#dependencySlice}: the initial backward slice supplies
     * value inputs and the existing guard fixpoint adds control inputs.</p> */
    static void removeGuardOnlyPathEnablers(
            List<String> inputPorts, Set<String> guardOnlyInputPorts,
            List<Map<String, Object>> regionInputs, String occurrenceId,
            String outputPort, String outputCell,
            Set<String> selectedBranchSites,
            List<Map<String, Object>> branchPolicies,
            List<String> droppedReasons) {
        if (inputPorts.isEmpty() || guardOnlyInputPorts.isEmpty()) return;

        Set<String> observedPrefixGuards = new LinkedHashSet<>();
        for (Map<String, Object> branch : branchPolicies) {
            String site = stringValue(branch.get("siteId"));
            if (!selectedBranchSites.contains(site)
                    || !"EXPLORE".equals(stringValue(branch.get("policy")))
                    || Boolean.TRUE.equals(branch.get("loopControlGuard"))
                    || Boolean.TRUE.equals(branch.get("failureTarget"))
                    || !Boolean.TRUE.equals(branch.get("observed"))
                    || !(branch.get("requiredOutcome") instanceof Boolean)) {
                continue;
            }
            observedPrefixGuards.add(site);
        }
        if (observedPrefixGuards.isEmpty()) return;

        Set<String> candidates = new LinkedHashSet<>(inputPorts);
        candidates.retainAll(guardOnlyInputPorts);
        if (candidates.isEmpty()) return;

        Map<String, Boolean> removable = new LinkedHashMap<>();
        Set<String> represented = new LinkedHashSet<>();
        for (Map<String, Object> input : regionInputs) {
            String port = stringValue(input.get("portId"));
            if (!boundToInput(input, occurrenceId)
                    || !candidates.contains(port)) {
                continue;
            }
            represented.add(port);
            boolean pathOnly = guardOnlyBoundedFrontier(input, outputPort,
                    outputCell, observedPrefixGuards);
            removable.put(port, removable.containsKey(port)
                    ? removable.get(port) && pathOnly : pathOnly);
        }
        List<String> removed = new ArrayList<>();
        for (String port : inputPorts) {
            if (represented.contains(port)
                    && Boolean.TRUE.equals(removable.get(port))) {
                removed.add(port);
            }
        }
        inputPorts.removeAll(removed);
        // A dependency this relation no longer has is stated by name.
        for (String port : removed) {
            droppedReasons.add("GUARD_ONLY_PATH_ENABLER_REMOVED:"
                    + outputPort + ":" + port);
        }
    }

    private static boolean guardOnlyBoundedFrontier(
            Map<String, Object> input, String outputPort, String outputCell,
            Set<String> observedPrefixGuards) {
        String sourceKind = stringValue(input.get("sourceKind"));
        if (!("ACCESSOR_RETURN".equals(sourceKind)
                || RuntimeSelectedRegionFinalizer.EXTERNAL_CALL_RETURN
                .equals(sourceKind))
                || !DependencyRole.VALUE_FRONTIER.equals(
                stringValue(input.get("dependencyRole")))
                || !"BOUNDED_STATE_FRONTIER".equals(
                stringValue(input.get("symbolicDemand")))
                || !"STATIC_VALUE_SEMANTIC_MUTATION_GUARD_V1".equals(
                stringValue(input.get("boundedStateFrontierAuthority")))
                || strings(input.get("boundedMutationOutputPorts"))
                .contains(outputPort)
                || strings(input.get("boundedMutationOutputCells"))
                .contains(outputCell)) {
            return false;
        }
        for (String guard : strings(input.get(
                "boundedMutationGuardSites"))) {
            if (observedPrefixGuards.contains(guard)) return true;
        }
        return false;
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
            if (accepted.contains(stringValue(row.get(field)))) result.add(row);
        }
        return result;
    }

    private static List<String> targetProjectionBlockers(
            List<Map<String, Object>> branches, Map<String, Object> seed) {
        Set<String> result = new LinkedHashSet<>();
        List<Map<String, Object>> eligible = eligibleTargetSites(branches);
        Set<String> guardedTargets = guardedTargetCells(eligible);
        if (eligible.isEmpty() || guardedTargets.size() > 1) {
            result.add("UNSUPPORTED_AMBIGUOUS_TARGET_PATH:"
                    + guardedTargetLabel(eligible, guardedTargets));
            return new ArrayList<>(result);
        }
        try {
            // The cutoff is not used here, but a target whose failure
            // boundary is ambiguous still blocks: the value is discarded and
            // the refusal is the finding.
            selectedTargetCutoff(eligible, seed);
        } catch (IllegalArgumentException ambiguous) {
            result.add("UNSUPPORTED_AMBIGUOUS_TARGET_PATH:"
                    + safe(ambiguous.getMessage()));
        }
        return new ArrayList<>(result);
    }

    private static List<Map<String, Object>> eligibleTargetSites(
            List<Map<String, Object>> branches) {
        List<Map<String, Object>> eligible = new ArrayList<>();
        for (Map<String, Object> branch : branches) {
            if (eligibleTargetSite(branch)) eligible.add(branch);
        }
        return eligible;
    }

    /** Every throw the eligible failure guards of this occurrence control. */
    private static Set<String> guardedTargetCells(
            List<Map<String, Object>> eligible) {
        Set<String> cells = new LinkedHashSet<>();
        for (Map<String, Object> branch : eligible) {
            cells.addAll(strings(branch.get(
                    RuntimeSelectedRegionFinalizer.FAILURE_TARGET_CELLS)));
        }
        return cells;
    }

    private static String guardedTargetLabel(
            List<Map<String, Object>> eligible, Set<String> guardedTargets) {
        return guardedTargets.size() > 1
                ? guardedTargets.size() + "_GUARDED_FAILURE_TARGETS"
                : eligible.size() + "_ELIGIBLE_FAILURE_TARGETS";
    }

    /** The observed event that decided this occurrence's target.
     *
     * <p>A conjunct the seed never recorded a fatal prefix for is a conjunct,
     * not a rival target, and is skipped; a target whose recording names no
     * such event at all still fails closed, which is what {@code TARGET-1}
     * requires of missing target evidence.</p> */
    private static long selectedTargetCutoff(
            List<Map<String, Object>> eligible, Map<String, Object> seed) {
        long cutoff = -1L;
        IllegalArgumentException refusal = null;
        for (Map<String, Object> branch : eligible) {
            try {
                cutoff = Math.max(cutoff, exactTargetCutoff(branch, seed));
            } catch (IllegalArgumentException ambiguous) {
                if (refusal == null) refusal = ambiguous;
            }
        }
        if (cutoff >= 0L) return cutoff;
        throw refusal == null ? new IllegalArgumentException(
                "TARGET_EVENT_UNOBSERVED") : refusal;
    }

    /** Returns the exact observed failure boundary used to cut target inputs.
     */
    private static long targetBoundaryUpperSeq(
            List<Map<String, Object>> branches, Map<String, Object> seed) {
        List<Map<String, Object>> eligible = eligibleTargetSites(branches);
        if (eligible.isEmpty()
                || guardedTargetCells(eligible).size() > 1) {
            return -1L;
        }
        try {
            return selectedTargetCutoff(eligible, seed);
        } catch (IllegalArgumentException ambiguous) {
            return -1L;
        }
    }

    private static long exactTargetCutoff(
            Map<String, Object> branch, Map<String, Object> seed) {
        String site = stringValue(branch.get("siteId"));
        List<Map<String, Object>> contexts = rows(
                seed.get("fatalPrefixContexts"));
        if (!contexts.isEmpty()) {
            List<Map<String, Object>> matching = new ArrayList<>();
            for (Map<String, Object> context : contexts) {
                if (site.equals(stringValue(context.get("siteId")))) {
                    matching.add(context);
                }
            }
            if (matching.size() > 1) {
                throw new IllegalArgumentException(
                        "MULTIPLE_FATAL_PREFIX_CONTEXTS");
            }
            if (matching.isEmpty()) {
                throw new IllegalArgumentException(
                        "FATAL_PREFIX_SITE_MISMATCH");
            }
            Map<String, Object> context = matching.get(0);
            if (!"EXACT_FATAL_BRANCH_OCCURRENCE_PREFIX_V1".equals(
                    stringValue(context.get("authority")))) {
                throw new IllegalArgumentException(
                        "FATAL_PREFIX_AUTHORITY_MISSING");
            }
            int ordinal = number(context.get("occurrence"), -1);
            long eventSeq = longNumber(context.get("eventSeq"), -1L);
            if (ordinal < 1 || eventSeq < 0L) {
                throw new IllegalArgumentException(
                        "FATAL_PREFIX_OCCURRENCE_INVALID");
            }
            int selectedOrdinal = number(branch.get(
                    "selectedOccurrence"), -1);
            long selectedEventSeq = longNumber(branch.get(
                    "selectedRuntimeEventSeq"), -1L);
            if (selectedOrdinal > 0 && selectedOrdinal != ordinal
                    || selectedEventSeq >= 0L
                    && selectedEventSeq != eventSeq) {
                throw new IllegalArgumentException(
                        "FATAL_PREFIX_BRANCH_MISMATCH");
            }
            return eventSeq;
        }
        int ordinal = number(branch.get("selectedOccurrence"), -1);
        long eventSeq = longNumber(branch.get(
                "selectedRuntimeEventSeq"), -1L);
        if (ordinal < 1 || eventSeq < 0L) {
            throw new IllegalArgumentException(
                    "FATAL_PREFIX_BOUNDARY_MISSING");
        }
        return eventSeq;
    }

    /** Whether this activation plans a target-reach closure. */
    private static boolean observedFailureTargetActivation(
            List<Map<String, Object>> branches) {
        boolean declared = false;
        for (Map<String, Object> branch : branches) {
            if (!Boolean.TRUE.equals(branch.get("failureTarget"))) continue;
            declared = true;
            if (Boolean.TRUE.equals(branch.get("observed"))) return true;
        }
        return !declared;
    }

    private static boolean eligibleTargetSite(Map<String, Object> branch) {
        return Boolean.TRUE.equals(branch.get("failureTarget"))
                && !Boolean.TRUE.equals(branch.get("loopControlGuard"))
                && Boolean.TRUE.equals(branch.get("observed"))
                && branch.get("requiredOutcome") instanceof Boolean
                && !stringValue(branch.get("siteId")).isEmpty();
    }

    /** Fails closed when the identity this planner minted disagrees with the
     * one the region finalizer already minted for the same activation. */
    private static void requireFinalizedOccurrence(Map<String, Object> seed,
                                                   String occurrenceId) {
        String finalized = stringValue(seed.get("occurrenceId"));
        if (!finalized.isEmpty() && !finalized.equals(occurrenceId)) {
            throw new IllegalArgumentException("runtime activation occurrence "
                    + "disagrees with the finalized identity: " + finalized
                    + " != " + occurrenceId);
        }
    }

    /** True when this row is bound to the occurrence, comparing occurrence
     * identity only. */
    private static boolean boundTo(Map<String, Object> row,
                                   String occurrenceId) {
        return occurrenceId.equals(stringValue(row.get("occurrenceId")));
    }

    /** True when this row is the named occurrence's input-side port.
     *
     * <p>{@link OccurrenceMinter#bindPorts} is the only thing that stamps an
     * {@code occurrenceId} on a port row, and it keys on the recorded {@code
     * rootCallId} of the access that produced the port - which a declaration
     * does not have and must not have: README section 2's {@code
     * exchangeSiteKey} is pure static identity, and a cut port is a fact
     * about the region , stated before any activation of it ran.</p> */
    private static boolean boundToInput(Map<String, Object> port,
                                        String occurrenceId) {
        if (declaredCutPort(port)) {
            String owned = stringValue(port.get("occurrenceId"));
            return owned.isEmpty() || owned.equals(occurrenceId);
        }
        return occurrenceId.equals(stringValue(port.get("occurrenceId")));
    }

    /** The declared communication ports this region hands to the VM, and the
     * site each is handed at. */
    private static List<Map<String, Object>> communicationHandoffSites(
            StaticProgram.RegionRow region) {
        Map<String, Map<String, Object>> byRole = new LinkedHashMap<>();
        for (boolean inbound : new boolean[]{true, false}) {
            String regionSide = inbound ? "IN" : "OUT";
            for (Map<String, Object> port : inbound
                    ? region.symbolicInputs : region.outputs) {
                if (!declaredCutPort(port)
                        || !DependencyRole.VALUE_FRONTIER.equals(
                        effectiveDependencyRole(port,
                                stringValue(port.get("javaType"))))) {
                    continue;
                }
                Map<String, Object> site = communicationHandoffSite(
                        port, regionSide);
                if (site != null) {
                    byRole.putIfAbsent(stringValue(site.get(
                            CommunicationHandoffSpec.SIDE)) + "\n"
                            + stringValue(site.get(
                            CommunicationCatalogContract.PORT_ID)), site);
                }
            }
        }
        return new ArrayList<>(byRole.values());
    }

    /** One declared port's handoff site, or {@code null}. */
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
                CommunicationCatalogContract.PORT_DIRECTION,
                CommunicationCatalogContract.PORT_JAVA_TYPE,
                CommunicationCatalogContract.PORT_DEFINITION_METHOD,
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

    /** True for a port row {@link SymbolicRegionPlanner} declared at a cut. */
    private static boolean declaredCutPort(Map<String, Object> port) {
        return port != null
                && RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT
                .equals(stringValue(port.get("sourceKind")))
                && CommunicationCatalogContract.declaredPortId(
                stringValue(port.get("portId")));
    }

    /** True when this row is the named occurrence's output-side port. */
    private static void copyBindingContext(Map<String, Object> binding,
                                           Map<String, Object> edge,
                                           Map<String, Object> fromPlan,
                                           Map<String, Object> toPlan) {
        copyContextLong(binding, "fromLaneId", edge, fromPlan, "laneId");
        copyContextLong(binding, "toLaneId", edge, toPlan, "laneId");
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
        putTraceContext(target, event, source(event));
    }

    private static void putTraceContext(Map<String, Object> target,
                                        MethodEvent event,
                                        SourceRef resolved) {
        SourceRef source = sourceOf(resolved);
        target.put("sourceKey", source.key());
        target.put("sourceKind", source.kind());
        target.put("sourceRole", source.role());
        target.put("sourceId", source.id());
        target.put("sourceEpoch", source.epoch());
        if (!event.requestKey.isEmpty()) {
            target.put("requestKey", event.requestKey);
        }
        if (!event.requestApi.isEmpty()) {
            target.put("requestApi", event.requestApi);
        }
        if (event.laneId > 0L) target.put("laneId", event.laneId);
        if (event.spanId > 0L) target.put("spanId", event.spanId);
        if (event.parentSpanId > 0L) {
            target.put("parentSpanId", event.parentSpanId);
        }
        if (event.remoteParentSpanId > 0L) {
            target.put("remoteParentSpanId", event.remoteParentSpanId);
        }
    }

    /** The symbolic inputs one activation of a region is planned over.
     *
     * <p>A heap port is an observed access and its site comes from what the
     * run recorded; a declared cut port is a static statement about the cut -
     * README section 3's {@code Req_in}, {@code Resp_in}, {@code Live_in} -
     * and its site comes from the capture the declaration carries.</p> */
    private static List<Map<String, Object>> symbolize(
            List<Map<String, Object>> ports, String occurrenceId,
            TraceIndex trace) {
        // A declared cut port can appear twice: the region-level declaration
        // and, once a recorded delivery named it, this occurrence's own
        // stamped copy of it.
        Set<String> occurrenceOwnedCutPorts =
                occurrenceOwnedCutPortIds(ports, occurrenceId);
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> port : ports) {
            if (!boundToInput(port, occurrenceId)) {
                continue;
            }
            Map<String, Object> seedIdentity = trace.seedFieldIdentity(port);
            if (!seedIdentity.isEmpty()) {
                port.put(RuntimePlanArtifact.SEED_FIELD_IDENTITY,
                        seedIdentity);
            }
            if (declaredCutPort(port)) {
                if (stringValue(port.get("occurrenceId")).isEmpty()
                        && occurrenceOwnedCutPorts.contains(
                        stringValue(port.get("portId")))) {
                    continue;
                }
                // A declared cut port is not a heap access.
                Map<String, Object> declared = declaredCutPortAction(port);
                if (declared != null) {
                    result.add(declared);
                }
                continue;
            }
            List<String> path = strings(port.get("fieldPath"));
            Map<String, Object> action = new LinkedHashMap<>(port);
            MaterializationSpec materialization = accessor(port);
            action.put("symbol", port.get("portId"));
            action.put("observed", true);
            action.put("objectId", port.get("rootObjectId"));
            String javaType = leafType(
                    strings(port.get("fieldPathDeclarations")));
            String sourceKind = stringValue(port.get("sourceKind"));
            if (RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT.equals(
                    sourceKind)) {
                javaType = "boolean";
            } else if (RuntimeSelectedRegionFinalizer.EXTERNAL_CALL_RETURN
                    .equals(sourceKind)) {
                javaType = stringValue(port.get("javaType"));
            }
            // A projected container carries the exact static transport type.
            if ("BOUNDED_CONTAINER_STATE".equals(
                    stringValue(port.get("symbolicDemand")))
                    && !stringValue(port.get("javaType")).isEmpty()) {
                javaType = stringValue(port.get("javaType"));
            }
            action.put("javaType", javaType);
            if (RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT.equals(
                    sourceKind)
                    || RuntimeSelectedRegionFinalizer.EXTERNAL_CALL_RETURN
                    .equals(sourceKind)) {
                action.put("location", "CALL_RETURN");
            } else if ("PARAMETER".equals(stringValue(port.get("rootKind")))) {
                action.put("argumentIndex", port.get("rootParameterIndex"));
                action.put("location", path.isEmpty()
                        ? "ARGUMENT" : "ARGUMENT_FIELD_PATH");
            } else if ("OBSERVED_FIELD_RECEIVER".equals(
                    stringValue(port.get("rootKind")))) {
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
            action.put("dependencyRole",
                    effectiveDependencyRole(action,
                            stringValue(action.get("javaType"))));
            result.add(action);
        }
        return result;
    }

    /** Names the value cell of every declared cut port of one region, once. */
    private static void declareCutPortCells(StaticProgram.RegionRow region) {
        List<Map<String, Object>> ports =
                new ArrayList<>(region.symbolicInputs);
        ports.addAll(region.outputs);
        for (Map<String, Object> port : ports) {
            if (declaredCutPort(port) && stringValue(port.get("cell")).isEmpty(
                    )) {
                String cell = declaredCutPortCell(port);
                if (!cell.isEmpty()) port.put("cell", cell);
            }
        }
    }

    /** The value cell a declared cut port's capture names, or {@code ""}. */
    private static String declaredCutPortCell(Map<String, Object> port) {
        String capture = stringValue(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        String definitionMethod = stringValue(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        String javaType = stringValue(port.get("javaType"));
        if (CommunicationCatalogContract.CAPTURE_METHOD_PARAMETER.equals(
                capture)) {
            int argumentIndex = number(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1);
            // The project-wide parameter cell, so "parameter n of the server
            // entry" is one string a consumer reads rather than two fields it
            // has to join.
            return definitionMethod.isEmpty() || javaType.isEmpty()
                    || argumentIndex < 0 ? ""
                    : definitionMethod + ".param" + argumentIndex + ":"
                    + javaType;
        }
        if (CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(capture)
                || CommunicationCatalogContract.CAPTURE_METHOD_RETURN.equals(
                capture)) {
            // The project-wide call-return cell: what the cut call handed
            // back, named by the callee whose frame produced it.
            String callee = CommunicationCatalogContract.CAPTURE_CALL_RETURN
                    .equals(capture) ? stringValue(port.get("declaredCallee"))
                    : definitionMethod;
            return callee.isEmpty() ? "" : callee + ".return";
        }
        return "";
    }

    /** Declared cut port ids this occurrence holds its own stamped copy of. */
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

    /** The symbolize action of one declared cut port, or {@code null}. */
    private static Map<String, Object> declaredCutPortAction(
            Map<String, Object> port) {
        String portId = stringValue(port.get("portId"));
        String capture = stringValue(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        String definitionMethod = stringValue(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        String javaType = stringValue(port.get("javaType"));
        if (capture.isEmpty()) {
            return null;
        }
        if (javaType.isEmpty()) {
            return null;
        }
        if (definitionMethod.isEmpty()) {
            return null;
        }
        Map<String, Object> action = new LinkedHashMap<>(port);
        action.put("symbol", portId);
        action.put("observed", true);
        action.put("javaType", javaType);
        // Both names for the same fact, because the two readers differ: an
        // action's defining frame is "method", while a root-entry action reads
        // "rootMethod".
        action.put("method", definitionMethod);
        action.put("rootMethod", definitionMethod);
        if (CommunicationCatalogContract.CAPTURE_METHOD_PARAMETER.equals(
                capture)) {
            int argumentIndex = number(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1);
            if (argumentIndex < 0) {
                return null;
            }
            // Req_in is parameter <n> of the resolved server entry, one frame
            // above the delivery and inside the server fragment by
            // construction.
            action.put("location", "ARGUMENT");
            action.put(CommunicationCatalogContract.PORT_ARGUMENT_INDEX,
                    argumentIndex);
            action.put("index", argumentIndex);
            action.put("cell", declaredCutPortCell(port));
        } else if (CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(
                capture)) {
            String declaredCallee = stringValue(port.get("declaredCallee"));
            int unitIndex = number(port.get(CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX), -1);
            if (declaredCallee.isEmpty() || unitIndex < 0) {
                return null;
            }
            // Resp_in is the value the cut call returned, read at the cut
            // unit in the client's own frame - one frame above the transport
            // and inside the client region by construction.
            action.put("location", "CALL_RETURN");
            action.put("cell", declaredCutPortCell(port));
            action.put("unitIndex", unitIndex);
        } else {
            // CALL_ARGUMENT and METHOD_RETURN describe where a fragment
            // *writes* a value at its boundary.
            return null;
        }
        action.put("dependencyRole",
                effectiveDependencyRole(action, javaType));
        return action;
    }


    /** Separates semantic solver leaves from the object graph needed only to
     * replay a region. */
    static String effectiveDependencyRole(Map<String, Object> port,
                                          String javaType) {
        String demand = stringValue(port.get("symbolicDemand"));
        if ("BOUNDED_CONTAINER_STATE".equals(demand)) {
            return DependencyRole.VALUE_FRONTIER;
        }
        String declared = stringValue(port.get("dependencyRole"));
        if (DependencyRole.CONCRETE_STRUCTURE_CARRIER.equals(declared)
                || demand.startsWith("CONCRETE_")
                || Boolean.TRUE.equals(port.get("captureRootOnly"))
                || Boolean.TRUE.equals(port.get("loopControlOnly"))
                || Boolean.TRUE.equals(port.get("controlOnly"))
                || Boolean.TRUE.equals(port.get("pathAssumptionOnly"))) {
            return DependencyRole.CONCRETE_STRUCTURE_CARRIER;
        }
        return symbolicLeafType(javaType)
                ? DependencyRole.VALUE_FRONTIER
                : DependencyRole.CONCRETE_STRUCTURE_CARRIER;
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

    private static void addMaterializationMethods(
            Set<String> methods, List<Map<String, Object>> actions,
            Set<String> allowedMethods) {
        for (Map<String, Object> action : actions) {
            addIfAllowed(methods, allowedMethods,
                    stringValue(action.get("rootMethod")));
            addIfAllowed(methods, allowedMethods,
                    stringValue(action.get("accessorCallerMethod")));
            addIfAllowed(methods, allowedMethods,
                    stringValue(action.get("accessorImplementationMethod")));
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
        String site = stringValue(port.get("siteId"));
        if (!site.isEmpty()) {
            action.put("accessSites", Collections.singletonList(site));
        }
        action.put("fieldPath", path);
    }

    /** Binds the exact ports of one region occurrence. */
    private static void registerExactPorts(
            StaticProgram.RegionRow region, String occurrenceId,
            Map<String, String> exactPorts) {
        registerExactPorts(region.symbolicInputs, occurrenceId, "IN",
                exactPorts);
        registerExactPorts(region.outputs, occurrenceId, "OUT", exactPorts);
    }

    private static void registerExactPorts(
            List<Map<String, Object>> ports,
            String occurrenceId, String direction,
            Map<String, String> exactPorts) {
        for (Map<String, Object> port : ports) {
            if (!("IN".equals(direction)
                    ? boundToInput(port, occurrenceId)
                    : boundTo(port, occurrenceId))) {
                continue;
            }
            String id = stringValue(port.get("portId"));
            if (id.isEmpty()) continue;
            String key = exactPortKey(occurrenceId, direction, id);
            String previous = exactPorts.putIfAbsent(key, id);
            if (previous != null && !previous.equals(id)) {
                throw new IllegalArgumentException(
                        "conflicting exact runtime port binding: " + key);
            }
        }
    }

    private static String exactPort(
            Map<String, String> exactPorts, String occurrenceId,
            String direction, String portId, Map<String, Object> edge) {
        String selected = exactPorts.get(exactPortKey(occurrenceId,
                direction, portId));
        if (selected == null) {
            throw new IllegalArgumentException("runtime flow "
                    + stringValue(edge.get("edgeId")) + " has no exact "
                    + direction.toLowerCase() + " port for "
                    + occurrenceId + ": " + portId);
        }
        return selected;
    }

    private static String exactPortKey(String occurrenceId,
                                       String direction, String portId) {
        return occurrenceId + "\n" + direction + "\n" + portId;
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
            String site = stringValue(policy.get("siteId"));
            List<RuntimeEvent> occurrences = bySite.getOrDefault(site,
                    Collections.emptyList());
            List<Map<String, Object>> encoded = new ArrayList<>();
            for (int index = 0; index < occurrences.size(); index++) {
                RuntimeEvent event = occurrences.get(index);
                Map<String, Object> occurrence = object(
                        "occurrence", index + 1,
                        "outcome", event.outcome,
                        "eventSeq", event.seq);
                addExactSwitchDecision(occurrence, event);
                encoded.add(occurrence);
            }
            int selectedIndex = 0;
            Object required = policy.get("requiredOutcome");
            if (required instanceof Boolean) {
                for (int index = 0; index < occurrences.size(); index++) {
                    if (required.equals(occurrences.get(index).outcome)) {
                        selectedIndex = index;
                        break;
                    }
                }
            }
            RuntimeEvent selected = occurrences.isEmpty() ? null
                    : occurrences.get(selectedIndex);
            Map<String, Object> branch = new LinkedHashMap<>(policy);
            branch.put("observed", selected != null);
            branch.put("observedOutcome",
                    selected == null ? null : selected.outcome);
            branch.put("selectedOccurrence", selected == null
                    ? 0 : selectedIndex + 1);
            if (selected != null) {
                branch.put("selectedRuntimeEventSeq", selected.seq);
                branch.put("selectedCallId", selected.callId);
            }
            branch.put("occurrences", encoded);
            result.add(branch);
        }
        return result;
    }

    /** Copies a complete switch successor authority into a task occurrence. */
    private static void addExactSwitchDecision(
            Map<String, Object> occurrence, RuntimeEvent event) {
        boolean statesSwitch = event != null
                && (!event.branchKind.isEmpty()
                || !event.switchCaseKeys.isEmpty()
                || event.successorIndex != null);
        if (!statesSwitch) return;
        if (event.branchKind.isEmpty() || event.switchCaseKeys.isEmpty()
                || event.successorIndex == null) {
            throw new IllegalArgumentException(
                    "incomplete exact switch decision at " + event.siteId);
        }
        List<Integer> keys = parseSwitchCaseKeys(event.switchCaseKeys);
        // One validation owner for runtime summaries and seed tasks.
        ExactConcreteBranchObservation.switchDecisionToken(
                event.branchKind, keys, event.successorIndex);
        boolean outcome = event.successorIndex < keys.size();
        if (event.outcome == null || event.outcome != outcome) {
            throw new IllegalArgumentException(
                    "switch outcome differs from exact successor at "
                            + event.siteId);
        }
        occurrence.put("branchKind", event.branchKind);
        occurrence.put("caseKeys", keys);
        occurrence.put("observedSuccessorIndex", event.successorIndex);
    }

    private static List<Integer> parseSwitchCaseKeys(String encoded) {
        List<Integer> result = new ArrayList<>();
        for (String token : safe(encoded).split(",", -1)) {
            if (!token.matches("-?(?:0|[1-9][0-9]*)")) {
                throw new IllegalArgumentException(
                        "malformed switch case key " + token);
            }
            try {
                result.add(Integer.valueOf(token));
            } catch (NumberFormatException malformed) {
                throw new IllegalArgumentException(
                        "switch case key outside int domain " + token,
                        malformed);
            }
        }
        return result;
    }

    /** The replay address of one activation: its stable selected source and
     * region root, plus the causal anchor that activation was entered under.
     */
    private static Map<String, Object> rootSelector(
            MethodEvent root, SourceRef source, String requestApi) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("method", root.method);
        if (root.receiverType.isEmpty()) {
            result.put("kind", "GLOBAL_INVOCATION");
        } else {
            result.put("kind", "RECEIVER_CONTEXT");
            result.put("receiverClass", root.receiverType);
        }
        result.put(CAUSAL_ANCHOR,
                causalAnchor(root, source, requestApi));
        return result;
    }


    /** Selector member holding the incoming causal anchor. */
    static final String CAUSAL_ANCHOR = "causalAnchor";
    /** The activation ran on a source the application registered. */
    static final String ANCHOR_REGISTERED_SOURCE = "REGISTERED_SOURCE";
    /** The activation registered no source and ran under the default. */
    static final String ANCHOR_UNREGISTERED_SOURCE = "UNREGISTERED_SOURCE";
    /**
     * The activation ran on a registered source its own receiver never named:
     * the thread it ran on inherited that source from the thread that created
     * it, which is how a workload's own short-lived worker objects -- the
     * balancer's {@code Dispatcher$1} and {@code KeyManager$BlockKeyUpdater},
     * created under the test thread's registered client source -- are
     * attributed.  Replay reproduces this anchor from the thread's context and
     * not from an alias the receiver does not have.
     */
    static final String ANCHOR_INHERITED_CONTEXT = "INHERITED_CONTEXT";

    /** What causally produced this activation, named rather than counted. */
    private static Map<String, Object> causalAnchor(MethodEvent root,
                                                    SourceRef source,
                                                    String requestApi) {
        Map<String, Object> anchor = new LinkedHashMap<>();
        anchor.put("sourceKey", source.key());
        anchor.put("kind", UNREGISTERED_SOURCE.key().equals(source.key())
                ? ANCHOR_UNREGISTERED_SOURCE
                // Only the receiver's own registration may be re-checked by
                // object identity at replay.  Claiming it for a source the
                // context named would address an occurrence replay can never
                // answer -- and claiming the context for a registered receiver
                // would stop distinguishing dn0 from dn1, or epoch0 from
                // epoch1, on objects that do carry an alias.
                : root != null && root.receiverAttributed
                ? ANCHOR_REGISTERED_SOURCE : ANCHOR_INHERITED_CONTEXT);
        if (requestApi != null && !requestApi.isEmpty()) {
            anchor.put("requestApi", requestApi);
        }
        return anchor;
    }

    private static SourceRef source(MethodEvent event) {
        return sourceOf(event.source);
    }

    /** Authority of a source taken from the first stamped frame inside the
     * activation rather than from its root frame. */
    static final String UPGRADED_SOURCE_AUTHORITY =
            "FIRST_STAMPED_FRAME_INSIDE_ACTIVATION";
    /** Every distinct logical source the frames of one activation carry, in
     * recorded order.
     *
     * <p>Taking the region root's stamp therefore published {@code
     * workload/unregistered} for an activation whose very next frame names
     * its node - which is a fallback presented as an attribution, the thing
     * README Step 4 replaces with direct stamping.</p> */
    private static List<SourceRef> stampedSources(Set<Long> calls,
                                                  TraceIndex trace) {
        List<MethodEvent> frames = new ArrayList<>();
        for (Long call : calls) {
            MethodEvent frame = trace.methodByCall.get(call);
            if (frame != null && frame.source != null) frames.add(frame);
        }
        frames.sort(Comparator.comparingLong(frame -> frame.seq));
        List<SourceRef> sources = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        for (MethodEvent frame : frames) {
            if (seen.add(frame.source.key())) sources.add(frame.source);
        }
        return sources;
    }

    /** The source that owns one activation: its root frame's stamp, or the
     * unique stamp its own frames carry when the root has none. */
    private static SourceRef activationSource(MethodEvent root,
                                              List<SourceRef> stamped) {
        if (root.source != null) return root.source;
        return stamped.size() == 1 ? stamped.get(0) : UNREGISTERED_SOURCE;
    }

    /** Total logical scope of one traced event. A workload that never
     * registered a stable source is one logical source: correlation must
     * never merge two registered sources, and must never split a baseline run
     * that carries no source registration at all. */
    static SourceRef sourceOf(SourceRef source) {
        return source == null ? UNREGISTERED_SOURCE : source;
    }


    /** One region occurrence's relation identity on one source. */
    private static String relationKey(SourceRef source, String regionId) {
        return source.id() + "/relation/" + regionId;
    }

    /** Task member carrying the retained loops of one occurrence. */
    static final String RETAINED_LOOPS_FIELD =
            edu.uva.liftlab.graphchecker.concolic.BoundedLoopComposition
                    .PLAN_FIELD;

    /** The recorded root call of this plan's activation. */
    private static long traceEvidenceRootCall(Map<String, Object> plan) {
        return longNumber(row(plan.get("traceEvidence")).get("rootCallId"),
                -1L);
    }

    /** Which path assumptions a backward slice may keep. */
    private enum GuardAdmission {
        /** Only a guard reaching a declared runtime fault marker. */
        EXPLICIT_FAULT_ONLY,
        /** Also a guard reaching this occurrence's own declared input. */
        RELATION_INPUT_PORT
    }

    static final class RefinedFlowIndex {
        private final Map<String, Map<String, List<FlowEdge>>>
                incomingByRegion =
                new LinkedHashMap<>();
        /** region\nmethod\nsite -> cells guarded by that exact branch. */
        private final Map<String, Set<String>> guardedCellsBySite =
                new LinkedHashMap<>();
        /** declaration\nmethod\nsite -> regions with that HEAP_WRITE. */
        private final Map<String, Set<String>> heapWriteRegionsBySite =
                new LinkedHashMap<>();
        /** region\nmethod\nsite\ncallee\nargumentIndex -&gt; the caller-side
         * value cells bound into that exact argument. */
        private final Map<String, Set<String>> argumentCellsBySite =
                new LinkedHashMap<>();

        private void addEdge(FlowEdge edge) {
            for (String region : edge.regions) {
                incomingByRegion.computeIfAbsent(region,
                        ignored -> new LinkedHashMap<>())
                        .computeIfAbsent(edge.toCell,
                                ignored -> new ArrayList<>()).add(edge);
            }
            if ("IDENTITY_BINDING".equals(edge.transferKind)
                    && !edge.method.isEmpty() && !edge.siteId.isEmpty()) {
                Matcher parameter = METHOD_PARAMETER_CELL.matcher(
                        edge.toCell);
                if (parameter.matches()) {
                    for (String region : edge.regions) {
                        argumentCellsBySite.computeIfAbsent(region + "\n"
                                + edge.method + "\n" + edge.siteId + "\n"
                                + parameter.group(1) + "\n"
                                + parameter.group(2),
                                ignored -> new LinkedHashSet<>())
                                .add(edge.fromCell);
                    }
                }
            }
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

        /** Admits one row of the runtime-refined graph, refusing any other
         * graph the caller may have handed over. */
        private void admitRefinedRow(
                Map<String, Object> row, File graph) {
            if (row == null
                    || number(row.get("schemaVersion"), -1) != 3
                    || number(row.get("refinementSchemaVersion"), -1) != 1
                    || !"RUNTIME_REFINED_DATAFLOW".equals(
                    stringValue(row.get("graphKind")))) {
                throw new IllegalArgumentException(
                        "concolic planning requires the "
                                + "runtime-refined graph: " + graph);
            }
            FlowEdge edge = FlowEdge.decode(row);
            if (edge != null) {
                addEdge(edge);
            }
        }

        private static RefinedFlowIndex build(
                List<Map<String, Object>> rows, File graph) {
            RefinedFlowIndex result = new RefinedFlowIndex();
            int count = 0;
            for (Map<String, Object> row : rows == null
                    ? Collections.<Map<String, Object>>emptyList() : rows) {
                count++;
                result.admitRefinedRow(row, graph);
            }
            if (count == 0) {
                throw new IllegalArgumentException(
                        "refined graph is empty: " + graph);
            }
            return result;
        }

        static RefinedFlowIndex read(File graph) {
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
                    rows++;
                    result.admitRefinedRow(GSON.fromJson(line, ROW), graph);
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

        /** The caller-side value cell handed to one declared cut argument. */
        private String cutArgumentCell(String regionId, String method,
                                       String siteId, String declaredCallee,
                                       int argumentIndex) {
            if (regionId.isEmpty() || method.isEmpty() || siteId.isEmpty()
                    || declaredCallee.isEmpty() || argumentIndex < 0) {
                return "";
            }
            Set<String> cells = argumentCellsBySite.get(regionId + "\n"
                    + method + "\n" + siteId + "\n" + declaredCallee + "\n"
                    + argumentIndex);
            return cells == null || cells.size() != 1 ? ""
                    : cells.iterator().next();
        }

        /** The caller-side local assigned by one declared call return. */
        private String callReturnCell(String regionId, String method,
                                      String siteId, String callee) {
            Map<String, List<FlowEdge>> incoming =
                    incomingByRegion.get(regionId);
            if (incoming == null) return "";
            Set<String> cells = new LinkedHashSet<>();
            for (List<FlowEdge> edges : incoming.values()) {
                for (FlowEdge edge : edges) {
                    if ("FUNCTION_RETURN".equals(edge.transferKind)
                            && method.equals(edge.method)
                            && siteId.equals(edge.siteId)
                            && (callee + ".return").equals(edge.fromCell)) {
                        cells.add(edge.toCell);
                    }
                }
            }
            return cells.size() == 1 ? cells.iterator().next() : "";
        }

        /** Builds one failure-sliced relation frontier. Runtime fixes the
         * activation and the concrete heap access sites; static value/control
         * flow may then prove an alternate callee relevant even when the
         * baseline did not execute it. */
        private ReturnSlice dependencySlice(
                String regionId, String occurrenceId,
                String outputCell,
                Map<String, Object> exactHeapOutput,
                Set<String> allowedMethods,
                List<Map<String, Object>> inputs,
                List<Map<String, Object>> outputs,
                List<Map<String, Object>> branchPolicies,
                Set<String> seedMethods,
                long boundaryUpperSeq, GuardAdmission guardAdmission) {
            ReturnSlice result = backwardSlice(regionId, occurrenceId,
                    outputCell, exactHeapOutput, allowedMethods, inputs,
                    outputs, boundaryUpperSeq);
            Set<String> valueInputPorts = new LinkedHashSet<>(
                    result.inputPorts);
            for (String method : seedMethods) {
                if (!method.isEmpty() && allowedMethods.contains(method)) {
                    result.methods.add(method);
                }
            }

            // A relation whose value slice reached no declared input at all is
            // the shape {@link GuardAdmission#RELATION_INPUT_PORT} exists for:
            // its output is assigned literals, its value provenance is
            // therefore empty, no guard can be found to control it, and it
            // publishes a constant on every path.
            GuardAdmission admission =
                    guardAdmission != GuardAdmission.RELATION_INPUT_PORT
                            && valueInputPorts.isEmpty()
                            ? GuardAdmission.RELATION_INPUT_PORT
                            : guardAdmission;

            boolean changed;
            do {
                changed = false;
                Set<String> selectedMethods = new LinkedHashSet<>(
                        result.methods);
                Set<String> controlled =
                        admission == GuardAdmission.RELATION_INPUT_PORT
                                ? unionCells(result) : result.cells;
                for (Map<String, Object> branch : branchPolicies) {
                    String method = stringValue(branch.get("method"));
                    String site = stringValue(branch.get("siteId"));
                    List<String> operands = strings(
                            branch.get("operandCells"));
                    String policy = stringValue(branch.get("policy"));
                    if ((!selectedMethods.contains(method)
                            && !allowedMethods.contains(method))
                            || !"EXPLORE".equals(policy)
                            && !"PATH_ASSUMPTION".equals(policy)
                            || Boolean.TRUE.equals(
                            branch.get("loopControlGuard"))
                            || site.isEmpty()
                            || !controlsSelectedCell(regionId, method, site,
                            controlled, result.methods)) {
                        continue;
                    }
                    ReturnSlice guardSlice = new ReturnSlice();
                    for (String operand : operands) {
                        guardSlice.merge(backwardSlice(regionId,
                                occurrenceId,
                                operand, null, allowedMethods, inputs,
                                outputs, boundaryUpperSeq));
                    }
                    // A path assumption is outside the original failure
                    // frontier, but it is still part of an output relation
                    // when static GUARD evidence proves that it controls the
                    // selected write and its operand reaches a real runtime
                    // explicit-fault input.
                    if ("PATH_ASSUMPTION".equals(policy)
                            && !reachesExplicitSymbolicFault(
                            guardSlice.inputPorts, inputs,
                            occurrenceId)
                            && !(admission
                            == GuardAdmission.RELATION_INPUT_PORT
                            && reachesBoundSymbolicInput(
                            guardSlice.inputPorts, inputs, occurrenceId))) {
                        continue;
                    }
                    if (!result.branchSites.add(site)) continue;
                    // A retained guard executes in its helper method even if
                    // all value-flow predecessors terminate at an input
                    // boundary.
                    result.methods.add(method);
                    int before = controlled.size();
                    result.merge(guardSlice);
                    controlled = admission
                            == GuardAdmission.RELATION_INPUT_PORT
                            ? unionCells(result) : result.cells;
                    changed |= controlled.size() != before;
                }
            } while (changed);
            result.guardOnlyInputPorts.addAll(result.inputPorts);
            result.guardOnlyInputPorts.removeAll(valueInputPorts);
            return result;
        }

        /** Whether a guard operand terminates at this occurrence's own
         * declared symbolic input.
         *
         * <p>README section 3 writes a region relation as {@code
         * OR_i(pathGuard_i(IN) AND OUT = expr_i(IN))}: the guard is part of
         * the relation, not context around it.</p> */
        private static Set<String> unionCells(ReturnSlice slice) {
            Set<String> result = new LinkedHashSet<>(slice.cells);
            result.addAll(slice.visitedCells);
            return result;
        }

        private static boolean reachesBoundSymbolicInput(
                Set<String> ports, List<Map<String, Object>> inputs,
                String occurrenceId) {
            if (ports.isEmpty()) return false;
            for (Map<String, Object> input : inputs) {
                if (boundToInput(input, occurrenceId)
                        && ports.contains(stringValue(input.get("portId")))) {
                    return true;
                }
            }
            return false;
        }

        private static boolean reachesExplicitSymbolicFault(
                Set<String> ports, List<Map<String, Object>> inputs,
                String occurrenceId) {
            if (ports.isEmpty()) return false;
            for (Map<String, Object> input : inputs) {
                if (boundTo(input, occurrenceId)
                        && ports.contains(stringValue(input.get("portId")))
                        && RuntimeSelectedRegionFinalizer
                        .EXPLICIT_SYMBOLIC_FAULT.equals(
                        stringValue(input.get("sourceKind")))) {
                    return true;
                }
            }
            return false;
        }

        /** Uses the exact exception guard as a sink instead of inheriting the
         * whole execution-context region. */
        private ReturnSlice targetReachSlice(
                String regionId, String occurrenceId,
                Set<String> allowedMethods,
                List<Map<String, Object>> inputs,
                List<Map<String, Object>> outputs,
                List<Map<String, Object>> branchPolicies,
                String rootMethod, long boundaryUpperSeq) {
            ReturnSlice result = new ReturnSlice();
            boolean targetFound = false;
            for (Map<String, Object> branch : branchPolicies) {
                if (!Boolean.TRUE.equals(branch.get("failureTarget"))
                        || Boolean.TRUE.equals(
                        branch.get("loopControlGuard"))) {
                    continue;
                }
                String site = stringValue(branch.get("siteId"));
                String method = stringValue(branch.get("method"));
                if (site.isEmpty() || method.isEmpty()
                        || !allowedMethods.contains(method)) {
                    continue;
                }
                targetFound = true;
                ReturnSlice siteSlice = new ReturnSlice();
                siteSlice.branchSites.add(site);
                siteSlice.methods.add(method);
                for (String operand : strings(branch.get("operandCells"))) {
                    siteSlice.merge(dependencySlice(regionId, occurrenceId,
                            operand, null, allowedMethods, inputs, outputs,
                            branchPolicies, Collections.<String>emptySet(),
                            boundaryUpperSeq,
                            GuardAdmission.EXPLICIT_FAULT_ONLY));
                }
                result.merge(siteSlice);
            }
            if (!targetFound) return null;
            addIfAllowed(result.methods, allowedMethods, rootMethod);
            return result;
        }

        private boolean controlsSelectedCell(String regionId, String method,
                                             String site,
                                             Set<String> selectedCells,
                                             Set<String> selectedMethods) {
            // Index form of: exists GUARD edge at (regionId, method, site)
            // whose guarded cell is currently selected.
            Set<String> guarded = guardedCellsBySite.get(regionId + "\n"
                    + method + "\n" + site);
            if (guarded == null) return false;
            // A control dependency can guard the call that creates a selected
            // helper activation rather than one of the helper's internal value
            // cells.
            for (String selectedMethod : selectedMethods) {
                if (guarded.contains(selectedMethod + ".activation")) {
                    return true;
                }
            }
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

        /** Input boundary maps depend only on the (immutable) region input
         * list and the bound occurrence; they were previously rebuilt on
         * every backward slice, which dominated planning time. */
        private final Map<List<Map<String, Object>>, Map<String, Boundaries>>
                boundariesByInputs = new java.util.IdentityHashMap<>();

        private static final class Boundaries {
            private final Map<String, List<Map<String, Object>>> direct =
                    new LinkedHashMap<>();
            private final Map<String, List<Map<String, Object>>> heap =
                    new LinkedHashMap<>();
        }

        /** Synchronized: plans are finalized on a pool sharing this index. */
        private synchronized Boundaries boundaries(
                List<Map<String, Object>> inputs, String occurrenceId) {
            Map<String, Boundaries> byOccurrence = boundariesByInputs
                    .computeIfAbsent(inputs,
                            ignored -> new LinkedHashMap<>());
            Boundaries cached = byOccurrence.get(occurrenceId);
            if (cached != null) return cached;
            Boundaries result = new Boundaries();
            for (Map<String, Object> input : inputs) {
                String port = stringValue(input.get("portId"));
                if (!boundToInput(input, occurrenceId)
                        || port.isEmpty()) {
                    continue;
                }
                registerBoundary(result.direct, stringValue(input.get("cell")),
                        input);
                List<String> declarations = strings(
                        input.get("fieldPathDeclarations"));
                if (!declarations.isEmpty()) {
                    registerBoundary(result.heap,
                            stringValue(input.get("siteId")) + "\n"
                                    + declarations.get(
                                    declarations.size() - 1), input);
                }
            }
            byOccurrence.put(occurrenceId, result);
            return result;
        }

        private ReturnSlice backwardSlice(
                String regionId, String occurrenceId,
                String sinkCell,
                Map<String, Object> exactHeapOutput,
                Set<String> allowedMethods,
                List<Map<String, Object>> inputs,
                List<Map<String, Object>> outputs,
                long boundaryUpperSeq) {
            ReturnSlice result = new ReturnSlice();
            if (sinkCell.isEmpty()) return result;
            result.cells.add(sinkCell);

            Boundaries bounds = boundaries(inputs, occurrenceId);
            Map<String, List<Map<String, Object>>> directInputs =
                    bounds.direct;
            Map<String, List<Map<String, Object>>> heapInputs =
                    bounds.heap;

            String forcedMethod = exactHeapOutput == null ? ""
                    : stringValue(exactHeapOutput.get("rootMethod"));
            String forcedSite = exactHeapOutput == null ? ""
                    : stringValue(exactHeapOutput.get("siteId"));
            SliceNode sink = new SliceNode(sinkCell, forcedMethod,
                    forcedSite);
            Map<SliceNode, SliceStep> towardSink = new LinkedHashMap<>();
            Set<SliceNode> visited = new LinkedHashSet<>();
            Deque<SliceNode> queue = new ArrayDeque<>();
            Map<String, List<FlowEdge>> regionIncoming =
                    incomingByRegion.getOrDefault(regionId,
                            Collections.<String, List<FlowEdge>>emptyMap());
            visited.add(sink);
            queue.add(sink);
            while (!queue.isEmpty()) {
                SliceNode current = queue.removeFirst();
                result.visitedCells.add(current.cell);
                List<Map<String, Object>> direct = current.forcedWrite()
                        ? Collections.emptyList() : selectBoundaries(
                        directInputs.get(current.cell), boundaryUpperSeq);
                if (!direct.isEmpty()) {
                    for (Map<String, Object> input : direct) {
                        result.inputPorts.add(stringValue(input.get("portId")));
                    }
                    addSlicePath(result, current, sink, towardSink, null);
                    continue;
                }

                for (FlowEdge edge : regionIncoming.getOrDefault(current.cell,
                        Collections.<FlowEdge>emptyList())) {
                    if (edge.method.isEmpty()
                            || !allowedMethods.contains(edge.method)) {
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
                        List<Map<String, Object>> selectedInputs =
                                selectBoundaries(heapInputs.get(key),
                                        boundaryUpperSeq);
                        boolean unresolvedBoundary =
                                selectedInputs.isEmpty();
                        for (Map<String, Object> input : selectedInputs) {
                            Map<String, Object> writer = precedingWrite(
                                    regionId, occurrenceId, input,
                                    edge.fromCell, outputs, allowedMethods);
                            if (writer != null) {
                                SliceNode predecessor = new SliceNode(
                                        edge.fromCell,
                                        stringValue(writer.get("rootMethod")),
                                        stringValue(writer.get("siteId")));
                                enqueueSlice(predecessor, current, edge,
                                        visited, queue, towardSink);
                            } else {
                                unresolvedBoundary = true;
                                result.inputPorts.add(stringValue(
                                        input.get("portId")));
                                addSlicePath(result, current, sink,
                                        towardSink, edge);
                            }
                        }
                        if (unresolvedBoundary) {
                            result.demandedHeapDeclarations.add(
                                    edge.fromCell);
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
                String regionId, String occurrenceId,
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
                String method = stringValue(output.get("rootMethod"));
                String site = stringValue(output.get("siteId"));
                if (!boundTo(output, occurrenceId)
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
                        && (!method.equals(stringValue(selected.get(
                                "rootMethod")))
                        || !site.equals(stringValue(selected.get("siteId"))))) {
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

        /** A configured boundary array may contribute several independently
         * replayable scalar occurrences at one static read site. */
        private static List<Map<String, Object>> selectBoundaries(
                List<Map<String, Object>> candidates, long upperSeq) {
            if (candidates == null || candidates.isEmpty()) {
                return Collections.emptyList();
            }
            List<Map<String, Object>> boundedCandidates = new ArrayList<>();
            boolean allConcreteResidual = true;
            for (Map<String, Object> candidate : candidates) {
                boolean concreteResidual =
                        "CONCRETE_UNPROJECTED_BOUNDARY_ACCESS".equals(
                                stringValue(candidate.get("symbolicDemand")));
                allConcreteResidual &= concreteResidual;
                if (upperSeq >= 0L && concreteResidual
                        && longNumber(candidate.get("eventSeq"), -1L)
                        > upperSeq) {
                    continue;
                }
                boundedCandidates.add(candidate);
            }
            // A boundary access the slice left concrete demands nothing, so
            // a candidate set made only of those selects no boundary at all.
            if (boundedCandidates.isEmpty() || allConcreteResidual) {
                return Collections.emptyList();
            }
            return boundedCandidates;
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
            String from = stringValue(row.get("fromCell"));
            String to = stringValue(row.get("toCell"));
            String transfer = stringValue(row.get("transferKind"));
            if (from.isEmpty() || to.isEmpty()) {
                return null;
            }
            return new FlowEdge(stringValue(row.get("id")), from, to,
                    stringValue(row.get("method")),
                    stringValue(row.get("siteId")), transfer,
                    new LinkedHashSet<>(strings(row.get("regionIds"))));
        }
    }

    private static final class ReturnSlice {
        private final Set<String> inputPorts = new LinkedHashSet<>();
        private final Set<String> guardOnlyInputPorts =
                new LinkedHashSet<>();
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<String> staticSites = new LinkedHashSet<>();
        private final Set<String> branchSites = new LinkedHashSet<>();
        private final Set<String> edges = new LinkedHashSet<>();
        private final Set<String> cells = new LinkedHashSet<>();
        /** Every cell the backward walk reached, boundary or not. */
        private final Set<String> visitedCells = new LinkedHashSet<>();
        private final Set<String> demandedHeapDeclarations =
                new LinkedHashSet<>();

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
            guardOnlyInputPorts.addAll(other.guardOnlyInputPorts);
            methods.addAll(other.methods);
            staticSites.addAll(other.staticSites);
            branchSites.addAll(other.branchSites);
            edges.addAll(other.edges);
            cells.addAll(other.cells);
            visitedCells.addAll(other.visitedCells);
            demandedHeapDeclarations.addAll(
                    other.demandedHeapDeclarations);
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

    static List<Map<String, Object>> read(File file) {
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
                + root.sourceKey + "\n" + root.tid + "\n" + root.callId)
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
        final List<Map<String, Object>> regionCatalog = new ArrayList<>();
        final List<Map<String, Object>> runtimeInstances = new ArrayList<>();
        /** Recorded exchange and shared-location links across occurrences. */
        final List<Map<String, Object>> occurrenceLinks = new ArrayList<>();
        int staticRegionCount;

        String runtimePlanJsonl() {
            List<JsonObject> plans = new ArrayList<>();
            for (Map<String, Object> plan : regionPlans) {
                plans.add(toJsonTreeFast(plan).getAsJsonObject());
            }
            List<JsonObject> edges = new ArrayList<>();
            for (Map<String, Object> edge : edgeValidations) {
                edges.add(toJsonTreeFast(edge).getAsJsonObject());
            }
            List<JsonObject> regions = new ArrayList<>();
            for (Map<String, Object> region : regionCatalog) {
                regions.add(toJsonTreeFast(region).getAsJsonObject());
            }
            return RuntimePlanArtifact.encode(plans, edges, regions);
        }

    }

    static final class MethodEvent {
        final long seq;
        final String test;
        final String threadName;
        final long tid;
        final String method;
        final int objectId;
        final String receiverType;
        final long callId;
        final long parentCallId;
        final long parentSiteId;
        final long laneId;
        final long spanId;
        final long parentSpanId;
        final long remoteParentSpanId;
        /** Owner of this frame. Not final: a frame is stamped when it is
         * entered, and a node builds its service objects before it declares
         * which source they belong to, so a thread started during start-up
         * carries whoever started it. */
        SourceRef source;
        /** Stable logical scope of this event; never a transient trace id. */
        String sourceKey;
        /** Whether {@link #source} is this receiver's own registration.  A
         *  frame the thread's inherited context named carries {@code false},
         *  and replay can only reproduce that one by context.  Not final:
         *  load-time re-attribution may find the alias row for a receiver the
         *  run aliased only after this activation had started. */
        boolean receiverAttributed;
        final String requestKey;
        final String requestApi;
        MethodEvent(long seq, String test, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId,
                    long laneId, long spanId,
                    long parentSpanId, long remoteParentSpanId,
                    SourceRef source, boolean receiverAttributed,
                    String requestKey, String requestApi) {
            this.seq = seq;
            this.test = safe(test);
            this.threadName = safe(threadName);
            this.tid = tid;
            this.method = safe(method);
            this.objectId = objectId;
            this.receiverType = safe(receiverType);
            this.callId = callId;
            this.parentCallId = parentCallId;
            this.parentSiteId = parentSiteId;
            this.laneId = laneId;
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.source = source;
            this.sourceKey = sourceOf(source).key();
            this.receiverAttributed = receiverAttributed;
            this.requestKey = safe(requestKey);
            this.requestApi = safe(requestApi);
        }

        /**
         * Applies the owner its receiver registered anywhere in this trace.
         *
         * <p>{@code receiverOwned} says the owner is this receiver's own
         * registration rather than one the calling frame's registration
         * named.  That is the whole difference between an address replay can
         * re-check by object identity and one it can only re-check by the
         * context the thread inherited, so it is recorded rather than
         * re-derived.</p>
         */
        void reattribute(SourceRef owner, boolean receiverOwned) {
            if (owner == null) return;
            if (receiverOwned) {
                this.receiverAttributed = true;
            } else if (!owner.equals(source)) {
                // The calling frame's registration named this frame, so
                // whatever the run knew about this receiver no longer
                // describes the source now recorded for it.
                this.receiverAttributed = false;
            }
            if (owner.equals(source)) return;
            this.source = owner;
            this.sourceKey = owner.key();
        }
    }

    static final class ProtocolEvent {
        final long seq;
        final String direction;
        final String transport;
        final String correlationId;
        /** Retry/attempt identity stated at the application boundary. */
        final String attemptId;
        /** The half of the exchange this leg belongs to, as the application
         * stated it, or {@code ""} when it stated none. */
        final String half;
        final String threadName;
        final long tid;
        final String method;
        final long callId;
        final long invocationId;
        final String declaredCallee;
        final long laneId;
        final long spanId;
        final long parentSpanId;
        final long remoteParentSpanId;
        final SourceRef source;
        /** Stable logical scope of this event; never a transient trace id. */
        final String sourceKey;
        final String requestKey;
        final String requestApi;
        ProtocolEvent(long seq, String direction, String transport,
                      String correlationId, String attemptId, String half,
                      String threadName, long tid, String method, long callId,
                      long invocationId, String declaredCallee,
                      long laneId, long spanId,
                      long parentSpanId, long remoteParentSpanId,
                      SourceRef source, String requestKey, String requestApi) {
            this.seq = seq;
            this.direction = safe(direction);
            this.transport = safe(transport);
            this.correlationId = safe(correlationId);
            this.attemptId = safe(attemptId);
            this.half = safe(half);
            this.threadName = safe(threadName);
            this.tid = tid;
            this.method = safe(method);
            this.callId = callId;
            this.invocationId = invocationId;
            this.declaredCallee = safe(declaredCallee);
            this.laneId = laneId;
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.source = source;
            this.sourceKey = sourceOf(source).key();
            this.requestKey = safe(requestKey);
            this.requestApi = safe(requestApi);
        }

        /** The one half of one exchange this leg is on. */
        String exchangeLeg() {
            return RuntimeRegionPlanner.exchangeLeg(correlationId,
                    attemptId, half);
        }
    }

    static String exchangeLeg(String exchangeId, String attemptId,
                              String half) {
        String result = safe(exchangeId);
        if (!safe(attemptId).isEmpty()) result += "\n" + safe(attemptId);
        if (!safe(half).isEmpty()) result += "\n" + safe(half);
        return result;
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

    /** Exact identity observation for one reference-array element access. */
    static final class ArrayAccessEvent {
        final long seq;
        final String kind;
        final String method;
        final long callId;
        final int unitIndex;
        final String siteId;
        final int arrayObjectId;
        final int index;
        final int elementObjectId;
        ArrayAccessEvent(long seq, String kind, String method, long callId,
                         int unitIndex, String siteId, int arrayObjectId,
                         int index, int elementObjectId) {
            this.seq = seq;
            this.kind = safe(kind);
            this.method = safe(method);
            this.callId = callId;
            this.unitIndex = unitIndex;
            this.siteId = unitIndex >= 0 && !this.method.isEmpty()
                    ? this.method + "#u" + unitIndex : safe(siteId);
            this.arrayObjectId = arrayObjectId;
            this.index = index;
            this.elementObjectId = elementObjectId;
        }
    }

    /** Runtime proof that one mutation anchor belongs to a complete normal
     * definition invocation.  Completion sequences are local evidence only;
     * replay uses the bounded occurrence within that invocation. */
    private static final class ExactMutationFold {
        private final long definitionCallId;
        private final long normalExitSeq;
        private final int anchorOccurrence;
        private final List<Long> completions;

        private ExactMutationFold(long definitionCallId,
                                  long normalExitSeq,
                                  int anchorOccurrence,
                                  List<Long> completions) {
            this.definitionCallId = definitionCallId;
            this.normalExitSeq = normalExitSeq;
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
        private final List<FieldAccessEvent> fields;
        private final Map<Long, FieldAccessEvent> fieldBySeq =
                new LinkedHashMap<>();
        private final Set<Long> ambiguousFieldEventSeqs =
                new LinkedHashSet<>();
        private final Map<Long, MethodEvent> methodByCall =
                new LinkedHashMap<>();
        private final Map<String, List<MethodEvent>> methodsByName =
                new LinkedHashMap<>();
        private final Map<Long, List<Long>> children = new LinkedHashMap<>();
        private final Map<Long, List<RuntimeEvent>> runtimeByCall =
                new LinkedHashMap<>();
        private final Map<Long, ProtocolEvent> protocolBySeq =
                new LinkedHashMap<>();
        private final Set<Long> ambiguousProtocolSeqs =
                new LinkedHashSet<>();
        /** seq -> unique owning callId, or the ambiguity sentinel when two
         * events registered different call ids for one sequence number. */
        private final LongLongMap eventCallIdBySeq = new LongLongMap();

        private TraceIndex(Collection<MethodEvent> methodEvents,
                           Collection<RuntimeEvent> runtimeEvents,
                           Collection<FieldAccessEvent> fieldEvents,
                           Collection<ProtocolEvent> protocolEvents) {
            methods = sorted(methodEvents, value -> value.seq);
            fields = sorted(fieldEvents, value -> value.seq);
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
            for (ProtocolEvent event : sorted(protocolEvents,
                    value -> value.seq)) {
                registerEventCall(event.seq, event.callId);
                if (!ambiguousProtocolSeqs.contains(event.seq)
                        && protocolBySeq.put(event.seq, event) != null) {
                    protocolBySeq.remove(event.seq);
                    ambiguousProtocolSeqs.add(event.seq);
                }
            }
            for (FieldAccessEvent event : fields) {
                registerEventCall(event.seq, event.callId);
                if (!ambiguousFieldEventSeqs.contains(event.seq)
                        && fieldBySeq.put(event.seq, event) != null) {
                    // Sequence numbers are the runtime occurrence authority;
                    // an ambiguous duplicate can never select a carrier.
                    fieldBySeq.remove(event.seq);
                    ambiguousFieldEventSeqs.add(event.seq);
                }
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

        /** Calls in one subtree that had begun by the selected output. */
        private Set<Long> subtreeThrough(long root, long boundarySeq) {
            Set<Long> result = new LinkedHashSet<>();
            Deque<Long> work = new ArrayDeque<>();
            work.add(root);
            while (!work.isEmpty()) {
                long call = work.removeFirst();
                MethodEvent method = methodByCall.get(call);
                if (method == null || method.seq > boundarySeq
                        || !result.add(call)) {
                    continue;
                }
                work.addAll(children.getOrDefault(call,
                        Collections.emptyList()));
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

        /** Every recorded frame one call is inside, itself included. */
        private Set<Long> enclosingCalls(long callId) {
            Set<Long> result = new LinkedHashSet<>();
            MethodEvent current = methodByCall.get(callId);
            while (current != null && result.add(current.callId)) {
                current = methodByCall.get(current.parentCallId);
            }
            return result;
        }

        /** The static site of one recorded call-site invocation inside one
         * frame, or {@code ""} when this run recorded none. */
        private String callSiteId(long callId, long invocationId) {
            if (invocationId <= 0L) return "";
            for (RuntimeEvent event : runtimeByCall.getOrDefault(callId,
                    Collections.<RuntimeEvent>emptyList())) {
                if (event.invocationId == invocationId
                        && "CALL_SITE_ENTER".equals(event.kind)) {
                    return event.siteId;
                }
            }
            return "";
        }

        /** Exact static site through which this recorded frame was entered. */
        private String entrySiteId(long callId) {
            MethodEvent current = methodByCall.get(callId);
            return current == null ? ""
                    : callSiteId(current.parentCallId,
                    current.parentSiteId);
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

        private ProtocolEvent protocol(long seq) {
            return protocolBySeq.get(seq);
        }

        /** Exact seed field version observed by an accessor materialization.
         * Concrete values deliberately do not participate in this identity. */
        private Map<String, Object> seedFieldIdentity(
                Map<String, Object> port) {
            if (!"ACCESSOR_RETURN".equals(stringValue(
                    port.get("sourceKind")))) {
                return Collections.emptyMap();
            }
            String sourceKey = stringValue(port.get("sourceKey"));
            long receiver = longNumber(port.get("fieldReceiverObjectId"),
                    longNumber(port.get("receiverObjectId"), 0L));
            List<String> declarations = strings(
                    port.get("fieldPathDeclarations"));
            String leaf = declarations.isEmpty()
                    ? stringValue(port.get("declaredFieldSignature"))
                    : declarations.get(declarations.size() - 1);
            long readSeq = longNumber(port.get("eventSeq"), -1L);
            long readCall = eventCallIdBySeq.uniqueValue(readSeq);
            MethodEvent reader = methodByCall.get(readCall);
            if (sourceKey.isEmpty() || receiver <= 0L || leaf.isEmpty()
                    || readSeq < 0L || reader == null
                    || !sourceKey.equals(reader.sourceKey)) {
                return Collections.emptyMap();
            }
            long lastWriter = -1L;
            for (FieldAccessEvent field : fields) {
                if (field.seq >= readSeq) break;
                MethodEvent owner = methodByCall.get(field.callId);
                if ("FIELD_WRITE".equals(field.kind)
                        && field.receiverObjectId == receiver
                        && leaf.equals(field.field) && owner != null
                        && sourceKey.equals(owner.sourceKey)) {
                    lastWriter = field.seq;
                }
            }
            Map<String, Object> identity = new LinkedHashMap<>();
            identity.put("schemaVersion", 1);
            identity.put("authority",
                    RuntimePlanArtifact.SEED_FIELD_IDENTITY_AUTHORITY);
            identity.put("sourceKey", sourceKey);
            identity.put("receiverObjectId", receiver);
            identity.put("leafFieldSignature", leaf);
            identity.put("lastWriterEventSeq", lastWriter);
            return identity;
        }

        /** Remote request span carried by an event's nearest recorded frame. */
        private long remoteParentSpanAt(long eventSeq) {
            long callId = eventCallIdBySeq.uniqueValue(eventSeq);
            MethodEvent current = methodByCall.get(callId);
            Set<Long> seen = new LinkedHashSet<>();
            while (current != null && seen.add(current.callId)) {
                if (current.remoteParentSpanId > 0L) {
                    return current.remoteParentSpanId;
                }
                current = methodByCall.get(current.parentCallId);
            }
            return 0L;
        }

        /** Every recorded evaluation of one exact call argument inside one
         * activation, in recorded order. */
        private List<RuntimeEvent> callEvents(
                Set<Long> calls, String siteId, String declaredCallee,
                String kind, int argumentIndex) {
            List<RuntimeEvent> result = new ArrayList<>();
            if (calls == null || siteId.isEmpty()
                    || declaredCallee.isEmpty()) {
                return result;
            }
            for (RuntimeEvent event : runtime(calls)) {
                if (kind.equals(event.kind)
                        && siteId.equals(event.siteId)
                        && declaredCallee.equals(event.declaredCallee)
                        && (argumentIndex < 0
                        || event.argumentIndex == argumentIndex)) {
                    result.add(event);
                }
            }
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

        /** The call chain from an ancestor down to one descendant call. */
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

        /** Narrows a long-lived root to the invocation that produced one exact
         * runtime output. */
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
            MethodEvent outputCall = methodByCall.get(caller);
            if (CausynthStaticFacts.constructor(outputCall.method)) {
                for (MethodEvent candidate : methodByCall.values()) {
                    if (candidate.objectId == outputCall.objectId
                            && candidate.parentCallId
                            == outputCall.parentCallId
                            && candidate.parentSiteId
                            == outputCall.parentSiteId
                            && CausynthStaticFacts.constructor(
                            candidate.method)) {
                        corridor.add(candidate.callId);
                    }
                }
            }
            corridor.addAll(subtreeThrough(caller, outputEventSeq));
            return corridor;
        }

        /** The unique normal exit of one method invocation below a selected
         * activation. */
        private RuntimeEvent uniqueNormalMethodExit(
                long rootCallId, String definitionMethod) {
            if (rootCallId <= 0L || definitionMethod == null
                    || definitionMethod.isEmpty()
                    || !methodByCall.containsKey(rootCallId)) {
                return null;
            }
            RuntimeEvent selected = null;
            long selectedCall = -1L;
            for (Long call : subtree(rootCallId)) {
                MethodEvent method = methodByCall.get(call);
                if (method == null || !definitionMethod.equals(
                        method.method)) {
                    continue;
                }
                RuntimeEvent exit = null;
                for (RuntimeEvent event : runtimeByCall.getOrDefault(call,
                        Collections.<RuntimeEvent>emptyList())) {
                    if (!"METHOD_EXIT_NORMAL".equals(event.kind)) continue;
                    if (exit != null) return null;
                    exit = event;
                }
                if (exit == null) continue;
                if (selected != null && selectedCall != call) return null;
                selected = exit;
                selectedCall = call;
            }
            return selected;
        }

        /** Finds every completed execution of the selected mutator on the same
         * concrete container in the exact definition invocation and extends
         * its relation boundary to that invocation's normal exit. */
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
            for (Map.Entry<Long, RuntimeEvent> entry : enters.entrySet()) {
                RuntimeEvent completion = returns.get(entry.getKey());
                if (completion == null || completion.seq
                        < entry.getValue().seq
                        || completion.seq > normalExitSeq) {
                    return null;
                }
                completions.add(completion.seq);
            }
            completions.sort(Long::compareTo);
            int anchor = completions.indexOf(anchorCompletionSeq);
            if (anchor < 0 || completions.isEmpty()) return null;
            return new ExactMutationFold(definitionCallId, normalExitSeq,
                    anchor + 1, completions);
        }

    }
}
