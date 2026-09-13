package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.ToNumberPolicy;
import edu.uva.liftlab.graphchecker.causynth.MapFields;
import edu.uva.liftlab.graphchecker.causynth.CausynthStaticFacts;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import edu.uva.liftlab.graphchecker.concolic.AutomaticRegionEdge;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.concolic.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.contract.SiteId;

import java.io.File;
import java.nio.charset.StandardCharsets;
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
import java.util.TreeMap;
import java.util.UUID;
import java.util.function.ToLongFunction;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.firstNonEmpty;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.longNumber;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.object;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.number;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.rows;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.stringValue;

/** Binds region skeletons and refined region state to concrete activations. */
final class RuntimeRegionPlanner {
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();
    private static final Pattern FIELD = Pattern.compile(
            "^<[^:]+:\\s+([^()<>]+)\\s+[^\\s()>]+>$");
    /** Logical source of a workload whose tracing never registered one. */
    static final SourceRef UNREGISTERED_SOURCE = new SourceRef(
            "TEST_DRIVER", "WORKLOAD", "workload/unregistered", 0L);
    /** Authority of one recorded exchange link between two occurrences. */
    static final String DELIVERY_LINK_AUTHORITY =
            "RECORDED_EXCHANGE_OCCURRENCE_LINK_V1";
    /** A recorded activation this stage could not attribute to a source. */
    static final String GAP_RUNTIME_SOURCE_UNSTAMPED =
            "RUNTIME_ACTIVATION_SOURCE_UNSTAMPED";
    /** Authority of a source taken from the first stamped frame inside the
     * activation rather than from its root frame. */
    static final String UPGRADED_SOURCE_AUTHORITY =
            "FIRST_STAMPED_FRAME_INSIDE_ACTIVATION";
    /** The protocol server stub a run entered as its own region root. */
    static final String COMMUNICATION_ENTRY = "COMMUNICATION_ENTRY";
    private RuntimeRegionPlanner() {
    }

    /** Binds static region skeletons to the activations a run performed. */
    static Result planSkeletonGraph(List<StaticProgram.RegionRow> skeletons,
                                    List<MethodEvent> methods,
                                    List<RuntimeEvent> runtimeEvents,
                                    List<ProtocolEvent> protocolEvents) {
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
        retainInnermostCommunicationCaptureOwners(result.runtimeInstances);

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
        activation.put("activationId", recordedActivationKey(root));
        activation.put("regionId", skeleton.regionId);
        activation.put("rootCallId", root.callId);
        activation.put("rootMethod", root.method);
        activation.put("rootAuthority", skeleton.rootAuthority);
        activation.put("anchorMethod", observedAnchors.get(0));
        activation.put("anchorMethods", observedAnchors);
        activation.put("selection", skeleton.selection);
        activation.put("test", root.test);
        activation.put("thread", root.threadName);
        activation.put("threadId", root.tid);
        putTraceContext(activation, root,
                activationSource(root, stampedSources(calls, trace)));
        putRecordedTraceIds(activation, root);
        activation.put("callIds", new ArrayList<>(calls));
        activation.put("observedMethods", new ArrayList<>(observed));
        activationByCall.put(root.callId, activation);
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

    /**
     * A capture executed inside every enclosing region, but the propagated
     * value belongs to the smallest selected activation that contains the
     * exact capture event. Keeping an enclosing activation as a second owner
     * would give one receive two producers for the same transport event.
     */
    private static void retainInnermostCommunicationCaptureOwners(
            Collection<Map<String, Object>> activations) {
        Map<String, List<Map<String, Object>>> ownersByCapture =
                new LinkedHashMap<>();
        for (Map<String, Object> activation : activations) {
            for (Map<String, Object> capture : rows(activation.get(
                    RuntimeSelectedRegionFinalizer
                            .OBSERVED_COMMUNICATION_CAPTURES))) {
                String key = communicationCaptureIdentity(capture);
                if (!key.isEmpty()) {
                    ownersByCapture.computeIfAbsent(key,
                            ignored -> new ArrayList<>()).add(activation);
                }
            }
        }
        Map<String, Set<String>> shadowedByCapture = new LinkedHashMap<>();
        for (Map.Entry<String, List<Map<String, Object>>> entry
                : ownersByCapture.entrySet()) {
            Set<String> candidateIds = new LinkedHashSet<>();
            for (Map<String, Object> activation : entry.getValue()) {
                candidateIds.add(stringValue(activation.get("activationId")));
            }
            Set<String> shadowed = new LinkedHashSet<>();
            for (Map<String, Object> activation : entry.getValue()) {
                for (String enclosing : strings(
                        activation.get("enclosingActivationIds"))) {
                    if (candidateIds.contains(enclosing)) {
                        shadowed.add(enclosing);
                    }
                }
            }
            if (!shadowed.isEmpty()) {
                shadowedByCapture.put(entry.getKey(), shadowed);
            }
        }
        if (shadowedByCapture.isEmpty()) return;
        for (Map<String, Object> activation : activations) {
            String activationId = stringValue(activation.get("activationId"));
            List<Map<String, Object>> retained = new ArrayList<>();
            for (Map<String, Object> capture : rows(activation.get(
                    RuntimeSelectedRegionFinalizer
                            .OBSERVED_COMMUNICATION_CAPTURES))) {
                Set<String> shadowed = shadowedByCapture.get(
                        communicationCaptureIdentity(capture));
                if (shadowed == null || !shadowed.contains(activationId)) {
                    retained.add(capture);
                }
            }
            activation.put(RuntimeSelectedRegionFinalizer
                    .OBSERVED_COMMUNICATION_CAPTURES, retained);
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

    /**
     * Gives one exact runtime event to the smallest planned activation that
     * contains it.  Region discovery can select both a dynamic child and its
     * enclosing activation, so both goals can otherwise ask the VM to
     * materialize the same value or record the same branch.  Containment is
     * taken from the finalized activation seed; equal static sites in two
     * sequential activations therefore remain independent.
     */
    private static void retainInnermostExactGoalEventOwners(
            List<Map<String, Object>> plans, TraceIndex trace) {
        retainInnermostExactGoalEventOwners(plans, trace,
                "symbolize", false);
        retainInnermostExactGoalEventOwners(plans, trace,
                "branches", true);
    }

    /**
     * Re-spells every row's {@code enclosingActivationIds} in the published
     * namespace.
     *
     * <p>Containment is stamped over the recorded activations, before any
     * retention decision, so it is carried through planning as the recorded
     * correlation key.  The published name of an activation is a function of
     * its own planned occurrence, which only exists for an activation this
     * wave retained: an enclosing activation the wave dropped has no
     * published name at all, and is dropped from the list rather than named
     * in a namespace no other row uses.  That loses nothing -- the only
     * reader, {@link #retainInnermostExactGoalEventOwners}, matches these
     * names against the {@code activationId} of other plan rows, which an
     * unretained activation never has.</p>
     */
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

    private static void retainInnermostExactGoalEventOwners(
            List<Map<String, Object>> plans, TraceIndex trace,
            String goalField, boolean branch) {
        Map<String, Set<String>> ownersByEvent = new LinkedHashMap<>();
        for (Map<String, Object> plan : plans) {
            String activationId = stringValue(plan.get("activationId"));
            if (activationId.isEmpty()) continue;
            for (Map<String, Object> goal : rows(plan.get("closureGoals"))) {
                for (Map<String, Object> row : rows(goal.get(goalField))) {
                    String identity = branch
                            ? exactBranchEventIdentity(row, trace)
                            : exactMaterializationEventIdentity(row, trace);
                    if (!identity.isEmpty()) {
                        ownersByEvent.computeIfAbsent(identity,
                                ignored -> new LinkedHashSet<>())
                                .add(activationId);
                    }
                }
            }
        }

        Map<String, Set<String>> shadowedByEvent = new LinkedHashMap<>();
        for (Map<String, Object> child : plans) {
            String childId = stringValue(child.get("activationId"));
            List<String> enclosing = strings(child.get(
                    "enclosingActivationIds"));
            if (childId.isEmpty() || enclosing.isEmpty()) continue;
            for (Map<String, Object> goal : rows(child.get("closureGoals"))) {
                for (Map<String, Object> row : rows(goal.get(goalField))) {
                    String identity = branch
                            ? exactBranchEventIdentity(row, trace)
                            : exactMaterializationEventIdentity(row, trace);
                    Set<String> owners = ownersByEvent.get(identity);
                    if (identity.isEmpty() || owners == null
                            || owners.size() < 2
                            || !owners.contains(childId)) {
                        continue;
                    }
                    for (String ancestorId : enclosing) {
                        if (owners.contains(ancestorId)) {
                            shadowedByEvent.computeIfAbsent(identity,
                                    ignored -> new LinkedHashSet<>())
                                    .add(ancestorId);
                        }
                    }
                }
            }
        }
        if (shadowedByEvent.isEmpty()) return;

        for (Map<String, Object> plan : plans) {
            String activationId = stringValue(plan.get("activationId"));
            for (Map<String, Object> goal : rows(plan.get("closureGoals"))) {
                List<Map<String, Object>> retained = new ArrayList<>();
                for (Map<String, Object> row : rows(goal.get(goalField))) {
                    String identity = branch
                            ? exactBranchEventIdentity(row, trace)
                            : exactMaterializationEventIdentity(row, trace);
                    Set<String> shadowed = shadowedByEvent.get(identity);
                    if (shadowed == null
                            || !shadowed.contains(activationId)) {
                        retained.add(row);
                    }
                }
                goal.put(goalField, retained);
            }
        }
    }

    /** Exact branch occurrence, validated against the trace's event owner. */
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

    /**
     * Exact materialization occurrence and the value slot selected at it.
     * The slot excludes region-local port/symbol ids, which are different
     * names for the same value in overlapping regions.
     */
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
                // The annotated target's own activation, planned as a root
                // because no execution-context entry statically reaches it.
                || "FAILURE_TARGET_ENTRY".equals(authority);
    }

    /** Builds the refined-flow index once from already parsed rows. */
    static RefinedFlowIndex buildFlowIndex(
            List<Map<String, Object>> rows, File source) {
        return RefinedFlowIndex.build(rows, source);
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
                       List<ProtocolEvent> protocolEvents,
                       Collection<Map<String, Object>> planGaps) {
        // One loop has one prefix: region rows that disagree on a loop's K_L
        // are refused here, before anything is planned over them.
        declaredLoopBounds(regions);
        TraceIndex trace = new TraceIndex(methods, runtimeEvents,
                fieldEvents, protocolEvents);
        Result result = new Result();
        // The finalizer's own gaps ride the plan artifact: they are about the
        // ports these plans were built from and no later artifact carries the
        // accesses they say were dropped.
        if (planGaps != null) result.planGaps.addAll(planGaps);
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
        // occurrenceId is frozen evidence identity, not a replay address.
        // Replay therefore carries its own ordinal inside the exact stable
        // root/request scope.  Reserve ordinals for every observed activation
        // before retention, just as OccurrenceMinter does for evidence ids.
        Map<String, Integer> replayInvocationOrdinals =
                new LinkedHashMap<>();
        Map<String, String> exactPorts = new LinkedHashMap<>();
        // The recorded correlation key of every planned activation, against
        // the content-addressed name the plan publishes for it.  An
        // activation's own name is spelled from its own occurrence, so the
        // enclosing names a row carries can only be re-spelled once every
        // planned activation has been named -- see
        // republishEnclosingActivationIds below.
        Map<String, String> publishedActivationIds = new LinkedHashMap<>();
        Set<String> publishedActivationNames = new LinkedHashSet<>();
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
            boolean target = region.selection .startsWith("EXCEPTION")
                    && observedFailureTargetActivation(branches);
            MethodEvent semanticContext = target
                    ? trace.selectedTargetContext(root, calls, branches)
                    : root;
            // The same upgrade the activation seed was stamped with,
            // applied to the same call set.
            List<SourceRef> stamped = stampedSources(calls, trace);
            SourceRef rootSource = activationSource(root, stamped);
            SourceRef source = semanticContext.source != null
                    ? semanticContext.source : rootSource;
            int replayInvocationOrdinal = replayInvocationOrdinals.merge(
                    replayInvocationScope(regionId, root, rootSource,
                            semanticContext), 1, Integer::sum);
            // The region finalizer mints the one activation identity of
            // the pipeline and stamps it onto this seed; an activation it
            // did not retain carries none.
            String occurrenceId = stringValue(seed.get("occurrenceId"));
            if (occurrenceId.isEmpty()) continue;
            // planSkeletonGraph mints the recorded call identity once and
            // stamps it on the seed; this stage reads it rather than
            // spelling a second one to check the first against.
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
            OccurrenceMinter.bindOccurrence(region.json, rootCallId,
                    occurrenceId);
            OccurrenceMinter.bindEdges(regionEdges, regionId, rootCallId,
                    occurrenceId);
            registerExactPorts(region, occurrenceId, exactPorts);
            List<Map<String, Object>> occurrenceSymbolize = symbolize(
                    region.symbolicInputs, occurrenceId, trace);
            List<Map<String, Object>> occurrenceBranches = branches;
            // Static discovery supplies the candidate region; this concrete
            // activation supplies the methods worth slicing in the current
            // wave.
            Set<String> occurrenceMethods =
                    new LinkedHashSet<>(observedMethods);
            if (allowedMethods.contains(root.method)) {
                occurrenceMethods.add(root.method);
            }
            boolean occurrenceTarget = target;
            long targetBoundaryUpperSeq = occurrenceTarget
                    ? targetBoundaryUpperSeq(occurrenceBranches, seed) : -1L;
            ReturnSlice targetSlice = occurrenceTarget
                    ? refinedFlow.targetReachSlice(regionId, occurrenceId,
                    occurrenceMethods, region.symbolicInputs,
                    region.branchPolicies, root.method, targetBoundaryUpperSeq)
                    : null;
            if (targetSlice != null) {
                occurrenceSymbolize = filterByText(occurrenceSymbolize,
                        "symbol", targetSlice.inputPorts);
                occurrenceBranches = filterByText(occurrenceBranches,
                        "siteId", targetSlice.branchSites);
                addMaterializationMethods(targetSlice.methods,
                        occurrenceSymbolize, occurrenceMethods);
                occurrenceMethods = new LinkedHashSet<>(targetSlice.methods);
            }
            List<String> targetPathBlockers =
                    occurrenceTarget && targetSlice != null
                            ? targetPathBlockers(
                            occurrenceBranches, seed)
                            : Collections.emptyList();
            Map<String, Object> goal = new LinkedHashMap<>();
            goal.put("goalId", (occurrenceTarget ? "GOAL.TARGET_REACH."
                    : "GOAL.REGION_PATH.")
                    + UUID.nameUUIDFromBytes(occurrenceId.getBytes(
                    StandardCharsets.UTF_8)));
            goal.put("kind", occurrenceTarget ? "TARGET_REACH_CLOSURE"
                    : "REGION_PATH_CLOSURE");
            goal.put("runtimeDefinitionMethods",
                    new ArrayList<>(occurrenceMethods));
            goal.put("admission", object("state", occurrenceTarget
                            && !targetPathBlockers.isEmpty()
                            ? "BLOCKED" : "READY",
                    "mode", "RUNTIME_FAILURE_CLOSURE", "blockers",
                    occurrenceTarget ? targetPathBlockers
                            : Collections.emptyList()));
            goal.put("symbolize", occurrenceSymbolize);
            goal.put("branches", occurrenceBranches);
            goal.put("edgeBindings", new ArrayList<>());

            Map<String, Object> plan = new LinkedHashMap<>();
            plan.put("schemaVersion", 3);
            plan.put("kind", "CONCOLIC_REGION_PLAN");
            // The semantic source of this activation - sourceKey, sourceKind,
            // sourceRole, sourceId and sourceEpoch - is published once, by
            // putTraceContext below.  Where that source came FROM is this
            // row's own diagnostic: an activation the pipeline could not
            // attribute to any source is a named gap, never an authority.
            plan.put("sourceAuthority",
                    occurrenceTarget && semanticContext != root
                            && semanticContext.source != null
                            ? "SELECTED_TARGET_EVENT_SOURCE"
                            : semanticContext.source != null
                            ? "EXPLICIT_TRACE_SOURCE"
                            : stamped.size() == 1 ? UPGRADED_SOURCE_AUTHORITY
                            : GAP_RUNTIME_SOURCE_UNSTAMPED);
            plan.put("occurrenceId", occurrenceId);
            plan.put("regionId", region.regionId);
            // The once-only-root rule (README "Loops"): a region rooted on a
            // service loop is one occurrence per iteration, addressed by the
            // per-iteration source epoch, and replay enters the loop BODY at
            // headerUnitIndex rather than the entry frame above it.  Both
            // names travel only when the rule fired.
            if (!region.rootAuthority.isEmpty()) {
                plan.put(LoopBoundPolicy.ROOT_AUTHORITY, region.rootAuthority);
            }
            if (region.rootLoop != null) {
                plan.put(LoopBoundPolicy.ROOT_LOOP, region.rootLoop);
            }
            // The selector is minted once: it is both this row's replay
            // address and half of the content the published activation name
            // is taken over.
            Map<String, Object> plannedRootSelector = rootSelector(root,
                    rootSource, semanticContext.requestKey,
                    semanticContext.requestApi, replayInvocationOrdinal);
            String plannedActivationId = activationId(occurrenceId,
                    plannedRootSelector);
            // One occurrence is one activation, so one published name is
            // too.  Two activations answering to one name would silently
            // merge two occurrences downstream, which fails closed here.
            if (!publishedActivationNames.add(plannedActivationId)) {
                throw new IllegalStateException("two planned activations "
                        + "claimed one published activation identity: "
                        + plannedActivationId + " at " + occurrenceId);
            }
            publishedActivationIds.put(exactActivationId,
                    plannedActivationId);
            plan.put("activationId", plannedActivationId);
            // Still the recorded keys; re-spelled after the loop, once every
            // enclosing activation has a published name of its own.
            if (!enclosingActivationIds.isEmpty()) {
                plan.put("enclosingActivationIds",
                        new ArrayList<>(enclosingActivationIds));
            }
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
            plan.put("rootSelector", plannedRootSelector);
            // A region with no anchor states no target method rather than
            // an empty one.
            if (!region.anchorMethod.isEmpty()) {
                plan.put("targetMethod", region.anchorMethod);
            }
            // Why this activation was admitted, when it was admitted by
            // anything other than reaching the target, and how many
            // shared-location demand hops that took.  The region finalizer
            // stamps both on the seed; neither is derivable from the
            // retained edges, which carry port demand and protocol closure
            // in the same rows.
            if (seed.containsKey(ADMISSION_BASIS)) {
                plan.put(ADMISSION_BASIS, seed.get(ADMISSION_BASIS));
                if (seed.containsKey(DEMAND_DEPTH)) {
                    plan.put(DEMAND_DEPTH, seed.get(DEMAND_DEPTH));
                }
            }
            plan.put("closureGoals", Collections.singletonList(goal));
            result.regionPlans.add(plan);
            goalByOccurrence.put(occurrenceId, goal);
            planByOccurrence.put(occurrenceId, plan);
        }
        republishEnclosingActivationIds(result.regionPlans,
                publishedActivationIds);
        retainInnermostExactGoalEventOwners(result.regionPlans, trace);
        for (Map<String, Object> edge : regionEdges) {
            String edgeKind = stringValue(edge.get("kind"));
            if (!"RUNTIME_FIELD_FLOW".equals(edgeKind)
                    && !"RUNTIME_PROTOCOL_FLOW".equals(edgeKind)
                    && !AutomaticRegionEdge
                    .RUNTIME_REQUEST_CONTROL_EDGE_KIND.equals(edgeKind)) {
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
            boolean requestControl = AutomaticRegionEdge
                    .RUNTIME_REQUEST_CONTROL_EDGE_KIND.equals(edgeKind);
            // A protocol row names one observed exchange delivery. Its VM
            // handoff carries the value; the graph row only links replays.
            if (protocol && !AutomaticRegionEdge.tracedExchangeCandidate(
                    candidateExchangeRow(edge, fromOccurrence,
                            toOccurrence))) {
                throw new IllegalArgumentException(
                        "runtime protocol flow lacks a correlated exchange, "
                                + "attempt and delivery: "
                                + stringValue(edge.get("edgeId")));
            }
            if (requestControl) {
                JsonObject encoded = GSON.toJsonTree(edge).getAsJsonObject();
                if (!AutomaticRegionEdge.trustedRequestFaultControl(
                        encoded)) {
                    throw new IllegalArgumentException(
                            "runtime request control lacks an exact fault, "
                                    + "request and ordered response: "
                                    + stringValue(edge.get("edgeId")));
                }
                Map<String, Object> evidence = edgeEvidenceRow(edge,
                        fromOccurrence, toOccurrence);
                evidence.put("evidenceKind", AutomaticRegionEdge
                        .EXACT_REQUEST_FAULT_CONTROL_AUTHORITY);
                evidence.put("correlationAuthority", AutomaticRegionEdge
                        .EXACT_REQUEST_FAULT_CONTROL_AUTHORITY);
                evidence.put("state", "CONFIRMED_REQUEST_CONTROL");
                recordEdgeEvidence(result, goalByOccurrence, evidence,
                        fromOccurrence, toOccurrence);
                continue;
            }
            String fromPort = exactPort(exactPorts, fromOccurrence,
                    "OUT", stringValue(edge.get("fromPort")), edge);
            String toPort = exactPort(exactPorts, toOccurrence,
                    "IN", stringValue(edge.get("toPort")), edge);
            Map<String, Object> evidence = edgeEvidenceRow(edge,
                    fromOccurrence, toOccurrence);
            evidence.remove("fromPort");
            evidence.remove("toPort");
            evidence.remove("bindings");
            evidence.put("fromOutputPort", fromPort);
            evidence.put("toInputPort", toPort);
            evidence.put("evidenceKind", protocol
                    ? AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY
                    : SharedFieldFlow.LOCATION_MATCH_AUTHORITY);
            evidence.put("correlationAuthority", protocol
                    ? AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY
                    : SharedFieldFlow.LOCATION_MATCH_AUTHORITY);
            if (protocol) {
                evidence.put("protocolDirection", edge.get("direction"));
            }
            evidence.put("state", protocol
                    ? "CANDIDATE_TRACED_RPC_EXCHANGE"
                    : "CANDIDATE_SHARED_LOCATION");
            JsonObject encodedEvidence = GSON.toJsonTree(evidence)
                    .getAsJsonObject();
            if (!protocol && !AutomaticRegionEdge.sharedLocationCandidate(
                    encodedEvidence)) {
                throw new IllegalArgumentException(
                        "runtime field flow lacks a declared shared location: "
                                + stringValue(edge.get("edgeId")));
            }
            recordEdgeEvidence(result, goalByOccurrence, evidence,
                    fromOccurrence, toOccurrence);
        }
        // The plan catalog names the planned regions and the static
        // symbolic sources a scheduler admits inside them.  Ports, methods,
        // branch policies and access history stay in the refined graph,
        // which is the artifact that owns them.
        for (StaticProgram.RegionRow region : regionById.values()) {
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("schemaVersion", 3);
            row.put("kind", "SYMBOLIC_REGION");
            row.put("regionId", region.regionId);
            // Copied, not aliased: the catalog row is published on its own
            // and must not share mutable structure with the graph row that
            // later passes normalize in place.
            Object declaredSources = region.json.get(
                    StaticSymbolicSourceDeclaration.FIELD);
            if (declaredSources != null) {
                row.put(StaticSymbolicSourceDeclaration.FIELD,
                        deepCopyValue(declaredSources));
            }
            result.regionCatalog.add(row);
        }
        declareSharedCarriers(result, regionById);
        return result;
    }

    /** Declares every retained occurrence-local shared location. */
    private static void declareSharedCarriers(
            Result result,
            Map<String, StaticProgram.RegionRow> regionById) {
        for (Map<String, Object> plan : result.regionPlans) {
            StaticProgram.RegionRow region = regionById.get(
                    stringValue(plan.get("regionId")));
            String occurrence = stringValue(plan.get("occurrenceId"));
            if (region == null || occurrence.isEmpty()) continue;
            List<Map<String, Object>> carriers = declaredSharedCarriers(
                    region, occurrence);
            if (carriers.isEmpty()) continue;
            for (Map<String, Object> goal : rows(plan.get("closureGoals"))) {
                goal.put(ExecutionTask.SHARED_CARRIERS, carriers);
            }
        }
    }

    /** One declaration per shared field selected at its exact runtime access. */
    private static List<Map<String, Object>> declaredSharedCarriers(
            StaticProgram.RegionRow region, String occurrence) {
        List<Map<String, Object>> ports = new ArrayList<>();
        ports.addAll(region.symbolicInputs);
        ports.addAll(region.outputs);
        Map<String, Map<String, Object>> carriers = new LinkedHashMap<>();
        for (Map<String, Object> port : ports) {
            String owner = stringValue(port.get("occurrenceId"));
            if (!owner.isEmpty() && !occurrence.equals(owner)) continue;
            addAccessOwnedCarriers(carriers, port, port);
            for (Map<String, Object> access : rows(
                    port.get("runtimeAccesses"))) {
                addAccessOwnedCarriers(carriers, port, access);
            }
        }
        return new ArrayList<>(carriers.values());
    }

    /** Declares the field and any VM-modeled Atomic leaf named by this access. */
    static void addAccessOwnedCarriers(
            Map<String, Map<String, Object>> carriers,
            Map<String, Object> port, Map<String, Object> access) {
        List<String> declarations = strings(access.containsKey(
                "fieldPathDeclarations")
                ? access.get("fieldPathDeclarations")
                : port.get("fieldPathDeclarations"));
        FieldPathSpec.DeclaredField field = declarations.isEmpty()
                ? null : FieldPathSpec.declaredField(
                declarations.get(declarations.size() - 1));
        if (field == null
                || SharedFieldFlow.compilerSwitchDispatchField(
                field.name())) return;

        String atomic = SharedFieldFlow.atomicValueField(field.signature(),
                firstNonEmpty(stringValue(access.get("mutatorDeclaredCallee")),
                        stringValue(port.get("mutatorDeclaredCallee"))));
        FieldPathSpec.DeclaredField atomicField =
                FieldPathSpec.declaredField(atomic);
        if (atomicField != null) {
            addAccessOwnedCarrier(carriers, atomicField);
        }

        // The runtime access is the final authority for whether a field is a
        // solver value or replay structure.  A static port can conservatively
        // carry VALUE_FRONTIER before its exact access has been classified;
        // that broad label must not turn an object-routing map into shared
        // symbolic map state.  effectiveDependencyRole deliberately derives
        // the answer from explicit bounded-container demand and the semantic
        // leaf type, while retaining an explicit concrete runtime role.
        if (DependencyRole.VALUE_FRONTIER.equals(
                sharedCarrierRuntimeRole(port, access, field.type()))
                // An Atomic wrapper is not an identity to arm over: its
                // own value leaf, declared just above, is the shared state,
                // and versioning the holder as well would put one location
                // in the formula twice.
                || atomicField == null
                && referenceIdentityCarrier(port, access, field.type())) {
            addAccessOwnedCarrier(carriers, field);
        }
    }

    /**
     * Whether this access names a plain object reference whose writers a
     * later read must be able to choose between.
     *
     * <p>The role above answers VALUE_FRONTIER for a semantic leaf and
     * CONCRETE_STRUCTURE_CARRIER for everything else, which puts an object
     * reference on the concrete side -- correct for the object graph a
     * replay walks, and wrong for a reference that is itself shared state.
     * {@code BlockTokenSecretManager#currentKey} is the second kind: the
     * wire key id is {@code currentKey.keyId}, and which {@code BlockKey}
     * {@code currentKey} holds is exactly what the failing refresh decides.
     * Without a version here the read resolves against whichever object the
     * run happened to leave in the field, and the writer's object is lost.
     * </p>
     *
     * <p>This is a declaration, not a selection: the scheduler's root slice
     * ({@code SharedCarrierSlice}) drops every location no root reaches, so
     * a reference declared here and never moved by a root costs nothing
     * beyond one decision row.  An explicitly concrete access is still
     * concrete -- a capture root, a loop control or a path assumption names
     * structure the replay walks and not state a writer competes for.</p>
     */
    private static boolean referenceIdentityCarrier(
            Map<String, Object> port, Map<String, Object> access,
            String javaType) {
        if (!JavaPrimitiveSmtSemantics.referenceIdentityCarrier(javaType)) {
            return false;
        }
        Map<String, Object> semantic = new LinkedHashMap<>();
        for (String key : new String[]{"symbolicDemand", "captureRootOnly",
                "loopControlOnly", "controlOnly", "pathAssumptionOnly"}) {
            if (access.containsKey(key)) {
                semantic.put(key, access.get(key));
            } else if (port.containsKey(key)) {
                semantic.put(key, port.get(key));
            }
        }
        return !concreteStructureCarrier(semantic);
    }

    /** Final semantic role of one access, with exact runtime facts winning. */
    private static String sharedCarrierRuntimeRole(
            Map<String, Object> port, Map<String, Object> access,
            String javaType) {
        Map<String, Object> semantic = new LinkedHashMap<>();
        for (String key : new String[]{"symbolicDemand", "dependencyRole"}) {
            String value = firstNonEmpty(stringValue(access.get(key)),
                    stringValue(port.get(key)));
            if (!value.isEmpty()) semantic.put(key, value);
        }
        for (String key : new String[]{"captureRootOnly", "loopControlOnly",
                "controlOnly", "pathAssumptionOnly"}) {
            if (access.containsKey(key)) {
                semantic.put(key, access.get(key));
            } else if (port.containsKey(key)) {
                semantic.put(key, port.get(key));
            }
        }
        return effectiveDependencyRole(semantic, javaType);
    }

    private static void addAccessOwnedCarrier(
            Map<String, Map<String, Object>> carriers,
            FieldPathSpec.DeclaredField field) {
        String descriptor = JavaPrimitiveSmtSemantics
                .javaTypeDescriptor(field.type());
        if (descriptor.isEmpty()) return;
        Map<String, Object> carrier = object(
                "kind", SharedFieldFlow.wholeStateCarrierField(
                        field.owner(), field.name(), field.type())
                        ? SharedStateEvidence.LOCATION_KIND_MAP_STATE
                        : "DECLARED_FIELD",
                "declaringClass", field.owner(),
                "fieldName", field.name(),
                "descriptor", descriptor,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "fieldPath", Collections.emptyList());
        carriers.putIfAbsent(sharedCarrierKey(carrier), carrier);
    }

    private static String sharedCarrierKey(Map<String, Object> carrier) {
        String field = SharedFieldFlow.fieldKey(
                stringValue(carrier.get("declaringClass")),
                stringValue(carrier.get("fieldName")));
        if (field.isEmpty()) return "";
        return stringValue(carrier.get("kind")) + "\n" + field + ":"
                + stringValue(carrier.get("descriptor"));
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

    /** One edge validation row, stamped with the two selected activations. */
    private static Map<String, Object> edgeEvidenceRow(
            Map<String, Object> edge, String fromOccurrence,
            String toOccurrence) {
        Map<String, Object> evidence = new LinkedHashMap<>(edge);
        evidence.put("schemaVersion", 3);
        evidence.put("fromOccurrenceId", fromOccurrence);
        evidence.put("toOccurrenceId", toOccurrence);
        return evidence;
    }

    /** Publishes one edge validation and binds it to both endpoint goals.
     *
     * <p>The binding selects linked-replay membership. Runtime VM evidence
     * supplies the propagated expression.</p> */
    private static void recordEdgeEvidence(
            Result result,
            Map<String, Map<String, Object>> goalByOccurrence,
            Map<String, Object> evidence, String fromOccurrence,
            String toOccurrence) {
        result.edgeValidations.add(evidence);
        Map<String, Object> producerGoal =
                goalByOccurrence.get(fromOccurrence);
        if (producerGoal != null) {
            appendGoalBinding(producerGoal, evidence);
        }
        Map<String, Object> consumerGoal =
                goalByOccurrence.get(toOccurrence);
        if (consumerGoal != null && consumerGoal != producerGoal) {
            appendGoalBinding(consumerGoal, evidence);
        }
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

    /** Structural copy with the value domain of the JSONL round trip:
     * null-valued map entries are dropped, integral numbers become Long,
     * list nulls survive. */
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

    /** Adds one statically admitted method to the selected dependency scope. */
    private static void addIfAllowed(Collection<String> methods,
                                     Set<String> allowed, String method) {
        if (!method.isEmpty() && allowed.contains(method)
                && !CausynthStaticFacts.constructor(method)
                && !methods.contains(method)) {
            methods.add(method);
        }
    }

    private static List<Map<String, Object>> filterByText(
            List<Map<String, Object>> rows, String field,
            Set<String> accepted) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> candidate : rows) {
            if (accepted.contains(stringValue(candidate.get(field)))) {
                result.add(candidate);
            }
        }
        return result;
    }

    private static List<String> targetPathBlockers(
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
                CommunicationCatalogContract.PORT_FRAME_METHOD,
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

    /** The semantic source and request this row belongs to. */
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
    }

    /**
     * The recorded lane and span this frame ran in.
     *
     * <p>These are one recording's own trace ids: consecutive tickets from
     * {@code RuntimeTraceContext}'s process-global counter, so their values
     * depend on how many requests, spans and threads happened to be
     * allocated first.  They address a row of {@code runtime_trace.jsonl} in
     * the recording that minted them, which is exactly the scope the
     * activation seeds need them in -- {@link
     * #bindObservedCommunicationCaptures} pairs a protocol event with its
     * activation by lane.  They say nothing outside it, so a frozen plan,
     * which is compared across recordings, does not carry them.</p>
     */
    private static void putRecordedTraceIds(Map<String, Object> target,
                                            MethodEvent event) {
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
                String cell = RuntimeSelectedRegionFinalizer
                        .declaredCutPortCell(port);
                if (!cell.isEmpty()) port.put("cell", cell);
            }
        }
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
            action.put("cell", RuntimeSelectedRegionFinalizer
                    .declaredCutPortCell(port));
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
            action.put("cell", RuntimeSelectedRegionFinalizer
                    .declaredCutPortCell(port));
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
        if (concreteStructureCarrier(port)) {
            return DependencyRole.CONCRETE_STRUCTURE_CARRIER;
        }
        return symbolicLeafType(javaType)
                ? DependencyRole.VALUE_FRONTIER
                : DependencyRole.CONCRETE_STRUCTURE_CARRIER;
    }

    /** Structure retained only to replay control is not shared symbolic
     * state and therefore has no writer-version carrier. */
    private static boolean concreteStructureCarrier(
            Map<String, Object> port) {
        if (port == null || port.isEmpty()) return false;
        String demand = stringValue(port.get("symbolicDemand"));
        return DependencyRole.CONCRETE_STRUCTURE_CARRIER.equals(
                stringValue(port.get("dependencyRole")))
                || demand.startsWith("CONCRETE_")
                || Boolean.TRUE.equals(port.get("captureRootOnly"))
                || Boolean.TRUE.equals(port.get("loopControlOnly"))
                || Boolean.TRUE.equals(port.get("controlOnly"))
                || Boolean.TRUE.equals(port.get("pathAssumptionOnly"));
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

    /** Package-visible for the required-outcome selection contract test. */
    static List<Map<String, Object>> branches(
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
            boolean requiredDeclared = required instanceof Boolean;
            boolean requiredObserved = false;
            if (requiredDeclared) {
                for (int index = 0; index < occurrences.size(); index++) {
                    if (required.equals(occurrences.get(index).outcome)) {
                        selectedIndex = index;
                        requiredObserved = true;
                        break;
                    }
                }
            }
            RuntimeEvent selected = occurrences.isEmpty() ? null
                    : occurrences.get(selectedIndex);
            Map<String, Object> branch = new LinkedHashMap<>(policy);
            // "observed" is, and stays, "this site executed in the
            // recording".  It is not "it took the required outcome": a
            // required outcome the recording never took is the normal state
            // of a guard the search intends to flip, and reading the two as
            // one answer would make every flip target ineligible.
            branch.put("observed", selected != null);
            branch.put("observedOutcome",
                    selected == null ? null : selected.outcome);
            branch.put("selectedOccurrence", selected == null
                    ? 0 : selectedIndex + 1);
            if (selected != null) {
                branch.put("selectedRuntimeEventSeq", selected.seq);
                branch.put("selectedCallId", selected.callId);
            }
            if (requiredDeclared) {
                stateRequiredOutcomeSelection(branch, requiredObserved,
                        occurrences.size(), site);
            }
            branch.put("occurrences", encoded);
            result.add(branch);
        }
        return result;
    }

    /**
     * States how the occurrence of a required-outcome policy was chosen.
     *
     * <p>The loop above searches the recorded occurrences for one that took
     * the required outcome.  When the search fails, {@code selectedIndex} is
     * still 0 -- and the row used to say nothing at all about that, so a
     * policy whose required outcome no occurrence took was published
     * indistinguishably from one whose first occurrence took it.  Downstream
     * that reads as "occurrence #1 is the one the policy means", which for a
     * failure target is the fatal cutoff being supplied by a guard that never
     * took the failing arm.</p>
     *
     * <p>So the row now states the fact:
     * {@code requiredOutcomeObserved} answers the question the search asked,
     * and {@code selectedOccurrenceAuthority} says which of three things the
     * published ordinal is -- the occurrence that took the required outcome,
     * the only occurrence there was, or a choice among several that nothing
     * in the recording decides.  The third is the invented one, and it is
     * named as {@link ConcolicRegionRuntime#TARGET_REACH_NOT_OBSERVED} on the
     * row so a consumer can refuse it.</p>
     *
     * <p>The ordinal itself is left in place.  Withholding it would take the
     * fatal-prefix boundary out from under a replay that is otherwise sound
     * ({@code FATAL_PREFIX_BOUNDARY_MISSING}), and the blocking answer to an
     * unwitnessed target belongs at replay time, where {@code
     * ConcolicResultPublisher.targetReachedByActivation} requires the
     * declared occurrence to have actually been decided.</p>
     */
    private static void stateRequiredOutcomeSelection(
            Map<String, Object> branch, boolean requiredObserved,
            int occurrenceCount, String site) {
        branch.put("requiredOutcomeObserved", requiredObserved);
        if (requiredObserved) {
            branch.put("selectedOccurrenceAuthority", "REQUIRED_OUTCOME");
            return;
        }
        if (occurrenceCount <= 1) {
            branch.put("selectedOccurrenceAuthority",
                    "SOLE_RECORDED_OCCURRENCE");
            return;
        }
        branch.put("selectedOccurrenceAuthority",
                ConcolicRegionRuntime.TARGET_REACH_NOT_OBSERVED);
        branch.put("selectedOccurrenceGap",
                ConcolicRegionRuntime.TARGET_REACH_NOT_OBSERVED
                + ": none of the " + occurrenceCount + " recorded "
                + "occurrences of " + site + " took the required outcome, so "
                + "which one this policy names is not decided by the "
                + "recording");
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
    static Map<String, Object> rootSelector(
            MethodEvent root, SourceRef source, String requestKey,
            String requestApi, int invocationOrdinal) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("method", root.method);
        if (root.receiverType.isEmpty()) {
            result.put("kind", "GLOBAL_INVOCATION");
        } else {
            result.put("kind", "RECEIVER_CONTEXT");
            result.put("receiverClass", root.receiverType);
        }
        result.put(CAUSAL_ANCHOR,
                causalAnchor(root, source, requestKey, requestApi));
        result.put(ROOT_INVOCATION_ORDINAL, invocationOrdinal);
        return result;
    }


    /** Selector member holding the incoming causal anchor. */
    static final String CAUSAL_ANCHOR = "causalAnchor";
    /** Ordinal inside this selector's source/region/request scope. */
    static final String ROOT_INVOCATION_ORDINAL = "invocationOrdinal";
    /** The activation ran on a source the application registered. */
    static final String ANCHOR_REGISTERED_SOURCE = "REGISTERED_SOURCE";
    /** The activation registered no source and ran under the default. */
    static final String ANCHOR_UNREGISTERED_SOURCE = "UNREGISTERED_SOURCE";
    /**
     * The activation inherited a registered source from its creating thread,
     * while its own receiver had no source alias. Replay therefore uses the
     * thread context as the anchor.
     */
    static final String ANCHOR_INHERITED_CONTEXT = "INHERITED_CONTEXT";

    /** What causally produced this activation, named rather than counted. */
    private static Map<String, Object> causalAnchor(MethodEvent root,
                                                    SourceRef source,
                                                    String requestKey,
                                                    String requestApi) {
        Map<String, Object> anchor = new LinkedHashMap<>();
        anchor.put("sourceKey", source.key());
        anchor.put("kind", UNREGISTERED_SOURCE.key().equals(source.key())
                ? ANCHOR_UNREGISTERED_SOURCE
                // Only the receiver's own registration may be re-checked by
                // object identity at replay.  Claiming it for a source the
                // context named would address an occurrence replay can never
                // answer -- and claiming the context for a registered receiver
                // would collapse distinct source or epoch aliases.
                : root != null && root.receiverAttributed
                ? ANCHOR_REGISTERED_SOURCE : ANCHOR_INHERITED_CONTEXT);
        if (requestKey != null && !requestKey.isEmpty()) {
            anchor.put("requestKey", requestKey);
        }
        if (requestApi != null && !requestApi.isEmpty()) {
            anchor.put("requestApi", requestApi);
        }
        return anchor;
    }

    /** Stable counter scope used to address the same invocation at replay. */
    private static String replayInvocationScope(
            String regionId, MethodEvent root, SourceRef source,
            MethodEvent semanticContext) {
        return source.key() + "\u0000" + safe(regionId) + "\u0000"
                + safe(root == null ? "" : root.method) + "\u0000"
                + safe(semanticContext == null
                ? "" : semanticContext.requestKey) + "\u0000"
                + safe(semanticContext == null
                ? "" : semanticContext.requestApi);
    }

    private static SourceRef source(MethodEvent event) {
        return sourceOf(event.source);
    }

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

    /**
     * Plan-row fields naming why the admission half selected this region and
     * how far from the fatal target that demand travelled.  One spelling,
     * owned by the finalizer that writes them onto the seed.
     */
    static final String ADMISSION_BASIS =
            RuntimeSelectedRegionFinalizer.ADMISSION_BASIS;
    static final String DEMAND_DEPTH =
            RuntimeSelectedRegionFinalizer.DEMAND_DEPTH;

    /** Task member carrying the retained loops of one occurrence. */
    static final String RETAINED_LOOPS_FIELD =
            edu.uva.liftlab.graphchecker.concolic.BoundedLoopComposition
                    .PLAN_FIELD;

    static final class RefinedFlowIndex {
        private final Map<String, Map<String, List<FlowEdge>>>
                incomingByRegion =
                new LinkedHashMap<>();
        /** region\nmethod\nsite -> cells guarded by that exact branch. */
        private final Map<String, Set<String>> guardedCellsBySite =
                new LinkedHashMap<>();

        private void addEdge(FlowEdge edge) {
            for (String region : edge.regions) {
                incomingByRegion.computeIfAbsent(region,
                        ignored -> new LinkedHashMap<>())
                        .computeIfAbsent(edge.toCell,
                                ignored -> new ArrayList<>()).add(edge);
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
        }

        /** Indexes the rows the graph refiner produced.  The refiner stamps
         * the refined schema on every row it emits, so this stage indexes
         * that output rather than re-checking the stamp row by row. */
        private static RefinedFlowIndex build(
                List<Map<String, Object>> rows, File graph) {
            RefinedFlowIndex result = new RefinedFlowIndex();
            int count = 0;
            for (Map<String, Object> row : rows == null
                    ? Collections.<Map<String, Object>>emptyList() : rows) {
                count++;
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

        /** Builds one failure-sliced local path frontier. Runtime fixes the
         * activation and the concrete heap access sites; static value/control
         * flow may then prove an alternate callee relevant even when the
         * baseline did not execute it. */
        private ReturnSlice dependencySlice(
                String regionId, String occurrenceId,
                String sinkCell,
                Set<String> allowedMethods,
                List<Map<String, Object>> inputs,
                List<Map<String, Object>> branchPolicies,
                Set<String> seedMethods,
                long boundaryUpperSeq) {
            ReturnSlice result = backwardSlice(regionId, occurrenceId,
                    sinkCell, allowedMethods, inputs,
                    boundaryUpperSeq);
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
                Set<String> controlled = result.cells;
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
                                operand, allowedMethods, inputs,
                                boundaryUpperSeq));
                    }
                    // A path assumption is retained only when its operand
                    // reaches a declared runtime fault input.
                    if ("PATH_ASSUMPTION".equals(policy)
                            && !reachesExplicitSymbolicFault(
                            guardSlice.inputPorts, inputs,
                            occurrenceId)) {
                        continue;
                    }
                    if (!result.branchSites.add(site)) continue;
                    // A retained guard executes in its helper method even if
                    // all value-flow predecessors terminate at an input
                    // boundary.
                    result.methods.add(method);
                    int before = controlled.size();
                    result.merge(guardSlice);
                    controlled = result.cells;
                    changed |= controlled.size() != before;
                }
            } while (changed);
            return result;
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
                            operand, allowedMethods, inputs,
                            branchPolicies, Collections.<String>emptySet(),
                            boundaryUpperSeq));
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
                Set<String> allowedMethods,
                List<Map<String, Object>> inputs,
                long boundaryUpperSeq) {
            ReturnSlice result = new ReturnSlice();
            if (sinkCell.isEmpty()) return result;
            result.cells.add(sinkCell);

            Boundaries bounds = boundaries(inputs, occurrenceId);
            Map<String, List<Map<String, Object>>> directInputs =
                    bounds.direct;
            Map<String, List<Map<String, Object>>> heapInputs =
                    bounds.heap;

            SliceNode sink = new SliceNode(sinkCell);
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
                List<Map<String, Object>> direct = selectBoundaries(
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
                    if ("HEAP_READ".equals(edge.transferKind)) {
                        String key = edge.siteId + "\n" + edge.fromCell;
                        List<Map<String, Object>> selectedInputs =
                                selectBoundaries(heapInputs.get(key),
                                        boundaryUpperSeq);
                        for (Map<String, Object> input : selectedInputs) {
                            result.inputPorts.add(stringValue(
                                    input.get("portId")));
                            addSlicePath(result, current, sink,
                                    towardSink, edge);
                        }
                        continue;
                    }
                    if ("HEAP_WRITE".equals(edge.transferKind)
                            || !returnValueTransfer(edge.transferKind)) {
                        continue;
                    }
                    SliceNode predecessor = new SliceNode(edge.fromCell);
                    enqueueSlice(predecessor, current, edge, visited, queue,
                            towardSink);
                }
            }
            return result;
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
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<String> branchSites = new LinkedHashSet<>();
        private final Set<String> edges = new LinkedHashSet<>();
        private final Set<String> cells = new LinkedHashSet<>();

        private void add(FlowEdge edge) {
            String identity = edge.id.isEmpty()
                    ? edge.fromCell + "\n" + edge.toCell + "\n"
                    + edge.transferKind : edge.id;
            if (!edges.add(identity)) return;
            methods.add(edge.method);
            cells.add(edge.fromCell);
            cells.add(edge.toCell);
        }

        private void merge(ReturnSlice other) {
            inputPorts.addAll(other.inputPorts);
            methods.addAll(other.methods);
            branchSites.addAll(other.branchSites);
            edges.addAll(other.edges);
            cells.addAll(other.cells);
        }
    }

    private static final class SliceNode {
        private final String cell;

        private SliceNode(String cell) {
            this.cell = safe(cell);
        }

        @Override
        public boolean equals(Object value) {
            if (this == value) return true;
            if (!(value instanceof SliceNode)) return false;
            SliceNode other = (SliceNode) value;
            return cell.equals(other.cell);
        }

        @Override
        public int hashCode() {
            return cell.hashCode();
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

    /**
     * The recorded call one activation seed names.
     *
     * <p>This is an aggregation-internal key, not published identity: {@code
     * tid} is the recording JVM's thread id and {@code callId} the recorder's
     * global event counter, so both address one frame of one recording and
     * neither means anything in the next.  It is the correlation key the
     * activation seeds, their {@code enclosingActivationIds} and the recorded
     * occurrence links share inside a single aggregation, and it never leaves
     * it; the name the plan publishes is spelled from content by {@link
     * #activationId(String, Map)}.</p>
     */
    static String recordedActivationKey(MethodEvent root) {
        return "ACT." + UUID.nameUUIDFromBytes((root.test + "\n"
                + root.sourceKey + "\n" + root.tid + "\n" + root.callId)
                .getBytes(StandardCharsets.UTF_8));
    }

    /**
     * The published identity of one planned activation, spelled from the
     * content that names it.
     *
     * <p>Both inputs are already content-addressed.  {@code occurrenceId} is
     * {@code <semantic source>/region/<regionId>#<ordinal>}, whose ordinal
     * counts the observed activations of that source and region in recorded
     * order ({@link OccurrenceMinter}).  {@code rootSelector} is the address
     * replay itself uses: the root method, its receiver context, the causal
     * anchor and the invocation ordinal inside that anchor's scope.  Neither
     * carries a per-run address, so two independent recordings of one
     * workload publish the same name for the same activation.</p>
     *
     * <p>The {@code ACT.} prefix and the UUID shape are the ones consumers
     * already parse; only what the UUID is taken over changes.</p>
     */
    static String activationId(String occurrenceId,
                               Map<String, Object> rootSelector) {
        return "ACT." + UUID.nameUUIDFromBytes((safe(occurrenceId) + "\n"
                + canonicalIdentity(rootSelector))
                .getBytes(StandardCharsets.UTF_8));
    }

    /**
     * Order-independent spelling of one identity-bearing plan value.
     *
     * <p>A selector is a map of maps and lists whose emission order is a
     * presentation choice.  Sorting the members here keeps the published name
     * a function of what the selector says rather than of the order a later
     * refactor happens to write it in.</p>
     */
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

    private static String leafType(List<String> declarations) {
        if (declarations.isEmpty()) {
            return "java.lang.Object";
        }
        Matcher matcher = FIELD.matcher(
                declarations.get(declarations.size() - 1));
        return matcher.matches() ? matcher.group(1) : "java.lang.Object";
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
        /** Gaps the region finalizer raised while building these ports. */
        final List<Map<String, Object>> planGaps = new ArrayList<>();
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
            List<JsonObject> gaps = new ArrayList<>();
            for (Map<String, Object> gap : planGaps) {
                gaps.add(toJsonTreeFast(gap).getAsJsonObject());
            }
            return RuntimePlanArtifact.encode(plans, edges, regions, gaps);
        }

    }

    static final class MethodEvent {
        final long seq;
        final String test;
        final String threadName;
        final long tid;
        final String method;
        /** Not final: the recorded identity counter is renamed to its
         * content-addressed name once the trace has loaded, so that no
         * published artifact carries a per-run object number. */
        int objectId;
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
        final String siteId;
        final String declaredCallee;
        final int argumentIndex;
        final String runtimeType;
        /** Not final: renamed to its content-addressed name at load. */
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
            this.kind = safe(kind);
            this.method = safe(method);
            this.callId = callId;
            this.invocationId = invocationId;
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
        /** Not final: renamed to its content-addressed name at load. */
        int receiverObjectId;
        /** Not final: renamed to its content-addressed name at load. */
        int valueObjectId;
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
                    ? SiteId.of(this.method, unitIndex) : safe(siteId);
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
                    ? SiteId.of(this.method, unitIndex) : safe(siteId);
            this.arrayObjectId = arrayObjectId;
            this.index = index;
            this.elementObjectId = elementObjectId;
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
        /** seq -> unique owning callId, or the ambiguity sentinel when two
         * events registered different call ids for one sequence number. */
        private final LongLongMap eventCallIdBySeq = new LongLongMap();

        private TraceIndex(Collection<MethodEvent> methodEvents,
                           Collection<RuntimeEvent> runtimeEvents,
                           Collection<FieldAccessEvent> fieldEvents,
                           Collection<ProtocolEvent> protocolEvents) {
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
            for (ProtocolEvent event : sorted(protocolEvents,
                    value -> value.seq)) {
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
                if (method != null) result.add(method.method);
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
