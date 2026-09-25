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
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.DeclaredSiteCapture;
import edu.uva.liftlab.graphchecker.plan.DeclaredSymbolicInputs;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.RuntimePlanArtifact;
import edu.uva.liftlab.graphchecker.plan.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.plan.SiteId;

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

import static edu.uva.liftlab.graphchecker.causynth.MapFields.longNumber;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.object;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.number;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.rows;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.stringValue;

/** Binds region skeletons and refined region state to concrete activations. */
public final class RuntimeRegionPlanner {
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();
    /** Logical source of a workload whose tracing never registered one. */
    public static final SourceRef UNREGISTERED_SOURCE = new SourceRef(
            "TEST_DRIVER", "WORKLOAD", "workload/unregistered", 0L);
    /** The protocol server stub a run entered as its own region root. */
    static final String COMMUNICATION_ENTRY = "COMMUNICATION_ENTRY";
    private RuntimeRegionPlanner() {
    }

    /** Binds static region skeletons to the activations a run performed. */
    static Result planSkeletonGraph(List<StaticProgram.RegionRow> skeletons,
                                    List<MethodEvent> methods,
                                    List<RuntimeEvent> runtimeEvents,
                                    List<ProtocolEvent> protocolEvents,
                                    Set<String> declaredSites) {
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
        // The region entries this run FOLDED, in recorded order: they are no
        // activations, and the occurrence each of them belongs to is only
        // known once every activation has been planned, so they are held
        // here and named below (#stampFoldedRegionEntries).
        Map<Long, StaticProgram.RegionRow> foldedRoots =
                new LinkedHashMap<>();
        // The roots this run publishes an activation for, chosen before any
        // of them is built: which occurrence owns a folded entry is a
        // question about the whole set, and an activation has to own its
        // folded calls from the moment its call set is computed.
        List<PlannedRoot> plannedRoots = new ArrayList<>();
        // The communication endpoints are bound after the execution-context
        // roots, so a receiver nested in one of them sees its owner already
        // claimed.
        for (boolean endpoints : new boolean[]{false, true}) {
            for (StaticProgram.RegionRow skeleton : skeletons) {
                if (endpoints != COMMUNICATION_ENTRY.equals(
                        skeleton.rootAuthority)) {
                    continue;
                }
                for (MethodEvent root : trace.methods(skeleton.rootMethod)) {
                    // F1: an entry FOLDED into the occurrence already
                    // running on its thread opened none of its own, so it is
                    // a method call inside that occurrence and not an
                    // activation of this region.  One activation per
                    // occurrence, which is what lets
                    // RuntimeSelectedRegionFinalizer#readOccurrences keep
                    // reading a shared address as the identity failure it
                    // names.
                    //
                    // Skipped as an activation, NOT dropped as an event: the
                    // declared method was entered, and the occurrence it
                    // folded into owns its sites.  That fact is the plan's
                    // to state, and it is stated below rather than left for
                    // a later stage to read back out of the trace.
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
        // Which occurrence each folded entry belongs to: the INNERMOST
        // planned root it is inside, by the recorded call stack and nothing
        // else -- the same stack the fold itself was taken on.
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
        stampFoldedRegionEntries(result, foldedRoots, foldOwners,
                activationByCall, trace);
        result.runtimeInstances.addAll(activationByCall.values());
        stampRecordedExchanges(result, trace, protocolEvents);
        return result;
    }

    /** One recorded entry that opens an occurrence of one region. */
    private static final class PlannedRoot {
        private final StaticProgram.RegionRow skeleton;
        private final MethodEvent root;

        private PlannedRoot(StaticProgram.RegionRow skeleton,
                            MethodEvent root) {
            this.skeleton = skeleton;
            this.root = root;
        }
    }

    /**
     * Names the occurrence every FOLDED region entry belongs to.
     *
     * <p>A folded entry opened no occurrence ({@code Identity#fold}), so it
     * is no activation and this plan carries no row for it.  What it IS, is
     * a call inside the occurrence already running on its thread -- and that
     * occurrence performed its reads, its decisions, its writes and its
     * mints.  One {@link RuntimeSelectedRegionFinalizer#REGION_FOLD_KIND}
     * row per folded entry says so, and the enclosing occurrence carries the
     * same statement as {@link
     * RuntimeSelectedRegionFinalizer#FOLDED_REGION_IDS}, so a reader of
     * either side of the plan can answer "where did this declared region
     * run" without going back to the trace.</p>
     *
     * <p>The enclosing occurrence is the INNERMOST planned activation this
     * entry is inside: the recorded call stack and nothing else, which is
     * the same rule the fold itself was taken by.  An entry whose enclosing
     * frames were all skipped -- an activation the anchor test dropped --
     * gets a row with no occurrence on it: the entry still happened, and
     * saying nothing about where would be the silence this row exists to
     * remove.</p>
     */
    private static void stampFoldedRegionEntries(
            Result result, Map<Long, StaticProgram.RegionRow> foldedRoots,
            Map<Long, Long> foldOwners,
            Map<Long, Map<String, Object>> activationByCall,
            TraceIndex trace) {
        List<Long> ordered = new ArrayList<>(foldedRoots.keySet());
        Collections.sort(ordered);
        for (Long folded : ordered) {
            long rootCallId = folded;
            StaticProgram.RegionRow skeleton = foldedRoots.get(folded);
            MethodEvent root = trace.methodByCall.get(rootCallId);
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("schemaVersion", 3);
            row.put("kind", RuntimeSelectedRegionFinalizer.REGION_FOLD_KIND);
            row.put("regionId", skeleton.regionId);
            row.put("rootMethod", skeleton.rootMethod);
            row.put("rootCallId", rootCallId);
            if (root != null) row.put("test", root.test);
            Long owner = foldOwners.get(folded);
            Map<String, Object> enclosing = owner == null ? null
                    : activationByCall.get(owner);
            if (enclosing != null) {
                row.put("enclosingRegionId",
                        stringValue(enclosing.get("regionId")));
                row.put("enclosingActivationId",
                        stringValue(enclosing.get("activationId")));
                row.put("occurrenceAddress",
                        stringValue(enclosing.get("occurrenceAddress")));
                List<String> held = new ArrayList<>(strings(enclosing.get(
                        RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS)));
                if (!held.contains(skeleton.regionId)) {
                    held.add(skeleton.regionId);
                }
                enclosing.put(
                        RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS,
                        held);
            }
            result.regionFolds.add(row);
        }
    }



    /** Stamps every planned activation with the exchanges its own transport
     * hooks recorded. */
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

    /**
     * Exact executions of configured-source hook sites inside one occurrence.
     *
     * <p>Evidence of where the recording observed each declared site, in
     * event order.  It numbers nothing: a declared source is ONE symbol, so
     * the rows say WHERE the sites are and how often the recording reached
     * them, never how often a replay may.</p>
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
                    declaration, occurrenceId, event.seq,
                    event.invocationId,
                    event.declaredCallee, enclosingCallIds));
        }
        return result;
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
            TraceIndex trace, Set<String> declaredSites,
            Map<Long, StaticProgram.RegionRow> foldedRoots,
            Map<Long, Long> foldOwners) {
        Set<Long> subtree = trace.subtree(root.callId);
        Set<String> allowed = new LinkedHashSet<>(skeleton.methods);
        // F1, forwards: a region entry FOLDED inside this occurrence opened
        // none of its own, so EVERY site executed below it -- its decisions,
        // its reads, its writes, its declared-site captures -- is an event
        // of this occurrence and belongs in this call set.  Without it the
        // frames of a folded region belong to no occurrence at all: on
        // hdfs-11741 the annotated target's region folds into the DataNode's
        // SASL handler, whose skeleton does not list the target method, and
        // the fatal branch the recording decided was bound to nothing.
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
        // Identity v3: the address the recording computed at this entry,
        // carried verbatim.  Nothing offline re-derives it.
        activation.put("occurrenceAddress", root.occurrenceAddress);
        putTraceContext(activation, root,
                activationSource(root, stampedSources(calls, trace)));
        putRecordedTraceIds(activation, root);
        activation.put("callIds", new ArrayList<>(calls));
        activation.put("observedMethods", new ArrayList<>(observed));
        activation.put(
                RuntimeSelectedRegionFinalizer
                        .OBSERVED_COMMUNICATION_CAPTURES,
                observedCommunicationCaptures(skeleton, foldedHere, calls,
                        trace));
        // What the recording states at the sites the scope map named
        // DECLARED_SITE.  Computed once, here, where the activation's call
        // set is first known: the region finalizer reads it to learn which
        // activations hold a declared input, and the plan republishes these
        // same rows.
        List<Map<String, Object>> declared = declaredSiteCaptures(
                declaredSites, trace, calls, root);
        if (!declared.isEmpty()) {
            activation.put(DeclaredSiteCapture.PLAN_FIELD, declared);
        }
        activationByCall.put(root.callId, activation);
    }

    /** Exact configured cut captures that executed in this activation. */
    private static List<Map<String, Object>> observedCommunicationCaptures(
            StaticProgram.RegionRow skeleton,
            List<StaticProgram.RegionRow> folded, Set<Long> calls,
            TraceIndex trace) {
        List<RuntimeEvent> events = trace.runtime(calls);
        List<Map<String, Object>> observed = new ArrayList<>();
        // The cuts this occurrence DECLARES: its own region's and those of
        // every region folded into it.  The capture happened here either
        // way -- the folded entry opened no occurrence to record it in.
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
    /**
     * Declares each IN capture site on exactly one consumer region.
     *
     * <p>A capture site inside a helper lies inside every selected region
     * whose code reaches it, and each of them declared the port.  The value
     * crosses the wire once, so the attach can only file it on one of them
     * -- {@code ConcolicRegionRuntime.attachConsumerRegion} names the
     * innermost live occurrence that declares it -- and every other
     * declaring occurrence was then reported at IMPORT as
     * PLANNED_HANDOFF_NOT_REPRODUCED.  On hdfs-17899 bug2 that is
     * resp.block-key-id and resp.block-key-expiry-date, declared both by
     * the per-call region rooted at
     * {@code PBHelper.convert(BlockKeyProto)} and by the loop-body region
     * rooted at the enclosing {@code convert(ExportedBlockKeysProto)}: 18
     * handoff events, all naming the per-call region, and 12
     * not-reproduced rows, all on the loop-body one.</p>
     *
     * <p>The plan now states the same rule the attach applies: the site
     * belongs to the innermost selected region containing it, which is the
     * region whose own root method IS the capture's method when one is
     * selected.  H is (portId, consumer occurrence, k-th attach, element
     * path), so two consumers for one wire value would be two variables for
     * one value; this keeps it one.</p>
     */
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

    /** The method a region's root selector names, or {@code ""}. */
    private static String rootSelectorMethod(Map<String, Object> plan) {
        Object selector = plan.get("rootSelector");
        return selector instanceof Map
                ? stringValue(((Map<?, ?>) selector).get("method")) : "";
    }

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
                LoopBoundPolicy.declaredDefault(), declared);
    }

    /** In-memory planning entry point. {@code regionSource} and {@code
     * regionEdgeSource} only label diagnostics; rows must already be in the
     * exact JSONL value domain the file readers would produce. */
    static Result plan(List<Map<String, Object>> regions,
                       String regionSource,
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
        // before retention, just as OccurrenceBinding does for evidence ids.
        Map<String, Integer> replayInvocationOrdinals =
                new LinkedHashMap<>();
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
            // The occurrence the case's failure happened in, as the region
            // finalizer decided it (README TARGET-1: target existence binds
            // to a selected concrete branch event).  Read off the seed
            // first, because under the fold rule the region whose static
            // selection says EXCEPTION is not always the region this
            // occurrence is an activation of -- hdfs-11741's annotated
            // target region folds into the DataNode's SASL handler, which
            // is a STATE_CONTEXT region and is where the fatal branch was
            // decided.  The static test stands behind it for every caller
            // that builds a plan without that closure.
            boolean target = Boolean.TRUE.equals(MapFields.booleanValue(
                    seed.get(RuntimeSelectedRegionFinalizer
                            .FAILURE_TARGET_OCCURRENCE)))
                    || (region.selection.startsWith("EXCEPTION")
                    && observedFailureTargetActivation(branches));
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
                    replayInvocationScope(regionId, root, rootSource),
                    1, Integer::sum);
            // The region finalizer mints the one activation identity of
            // the pipeline and stamps it onto this seed; an activation it
            // did not retain carries none.
            String occurrenceId = stringValue(seed.get("occurrenceId"));
            if (occurrenceId.isEmpty()) continue;
            // One coarse occurrence is one row (README REGION-1).  A second
            // activation that landed on this address is refused where the
            // address is minted -- RuntimeSelectedRegionFinalizer states
            // OCCURRENCE_ADDRESS_SHARED as a BLOCKING plan gap and retains
            // the first -- so publishing it here would put the same
            // contradiction in the artifact, where PLAN meets it as
            // "duplicate region occurrence" and says nothing about why.
            if (planByOccurrence.containsKey(occurrenceId)) continue;
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
            OccurrenceBinding.bindOccurrence(region.json, rootCallId,
                    occurrenceId);
            List<Map<String, Object>> occurrenceSymbolize = symbolize(
                    region.symbolicInputs, occurrenceId);
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
            Map<String, Object> goal = new LinkedHashMap<>();
            goal.put("goalId", (occurrenceTarget ? "GOAL.TARGET_REACH."
                    : "GOAL.REGION_PATH.")
                    + UUID.nameUUIDFromBytes(occurrenceId.getBytes(
                    StandardCharsets.UTF_8)));
            goal.put("kind", occurrenceTarget ? "TARGET_REACH_CLOSURE"
                    : "REGION_PATH_CLOSURE");
            goal.put("runtimeDefinitionMethods",
                    new ArrayList<>(occurrenceMethods));
            // A planned occurrence is ready: which of its reads and
            // branches the failure needs is EXPLORE's frontier, not a cut
            // this stage may take, so there is no state here but READY and
            // no blocker for this stage to raise.
            goal.put("admission", object("state", "READY",
                    "mode", "RUNTIME_FAILURE_CLOSURE",
                    "blockers", Collections.emptyList()));
            goal.put("symbolize", occurrenceSymbolize);
            goal.put("branches", occurrenceBranches);
            Map<String, Object> plan = new LinkedHashMap<>();
            plan.put("schemaVersion", 3);
            plan.put("kind", "CONCOLIC_REGION_PLAN");
            // The semantic source of this activation - sourceKey, sourceKind,
            // sourceRole, sourceId and sourceEpoch - is published once, by
            // putTraceContext below.
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
            // The regions this occurrence RAN without opening an occurrence
            // for them (F1).  Published so a reader of the frozen plan can
            // answer "where did region R run" for a region the plan carries
            // no row for at all -- the only place that question is answered
            // once the trace is gone.
            List<String> folded = strings(seed.get(
                    RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS));
            if (!folded.isEmpty()) {
                plan.put(RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS,
                        new ArrayList<>(folded));
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
            // What the recording states at the sites the static scope map
            // named DECLARED_SITE: the dynamic half of every port a
            // declaration could mint in this occurrence.  Stamped on the
            // activation seed by planSkeletonGraph, republished here.
            List<Map<String, Object>> captures = rows(
                    seed.get(DeclaredSiteCapture.PLAN_FIELD));
            if (!captures.isEmpty()) {
                plan.put(DeclaredSiteCapture.PLAN_FIELD, captures);
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
        retainInnermostDeclaredSiteCaptures(result.regionPlans);
        retainInnermostExactGoalEventOwners(result.regionPlans, trace);
        retainInnermostCommunicationConsumers(result.regionPlans);
        // The plan catalog names the planned regions, the static symbolic
        // sources a scheduler admits inside them, and the declared roots
        // this plan honoured.  Ports, methods, branch policies and access
        // history stay in the refined graph, which is the artifact that
        // owns them.
        for (StaticProgram.RegionRow region : regionById.values()) {
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("schemaVersion", 3);
            row.put("kind", "SYMBOLIC_REGION");
            row.put("regionId", region.regionId);
            // A declared symbolic input's method is a region root by
            // declaration, so the scheduler resolves the case's rows
            // against these two members; without them it could not tell a
            // declaration this plan never saw from a site the recording
            // never entered.
            if (region.declaredInputRoot) {
                row.put("rootMethod", region.rootMethod);
                row.put(DeclaredSymbolicInputs.ROOT_FIELD, true);
            }
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
        return result;
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
        return normalizeScalar(value);
    }

    /** The JSONL round-trip domain of one scalar: whole numbers as long. */
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

    /** The declared communication ports this region hands to the VM, and the
     * site each is handed at. */
    public static List<Map<String, Object>> communicationHandoffSites(
            StaticProgram.RegionRow region) {
        Map<String, Map<String, Object>> byRole = new LinkedHashMap<>();
        for (boolean inbound : new boolean[]{true, false}) {
            String regionSide = inbound ? "IN" : "OUT";
            for (Map<String, Object> port : inbound
                    ? region.symbolicInputs : region.outputs) {
                if (!declaredCutPort(port) || !symbolicLeafPort(port,
                        stringValue(port.get("javaType")))) {
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
        // sourceKey, and nothing that re-spells it.  The row carried
        // sourceKind, sourceRole, sourceId and sourceEpoch beside it: the
        // node and its epoch are already in sourceKey, which
        // OccurrenceAddress parses both out of, and no reader of a plan or
        // activation row ever asked for the other three -- the readers of
        // those member NAMES are port, edge and mint rows, which are other
        // shapes entirely.
        target.put("sourceKey", sourceOf(resolved).key());
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
        // The lane, and only the lane.  It is read back off a published row
        // (the shadowing pass asks which activations share one lane); the
        // three span ids were published beside it and read by nothing -- the
        // span correlation they serve happens over the TRACE rows, inside
        // this planner, before any row is published.
        if (event.laneId > 0L) target.put("laneId", event.laneId);
    }

    /**
     * One recorded call is ONE occurrence's read: the innermost planned
     * activation that ran it.
     *
     * <p>Every planned activation enclosing the call holds it in its own
     * call subtree, so the pass above states the capture on each of them.
     * An enclosing activation's copy is the same recorded return under a
     * second name, and a port minted from it would give one value two
     * authorities -- the same rule {@link
     * #retainInnermostExactGoalEventOwners} applies to the goals, applied
     * to the evidence they are built from, and keyed on the recorded
     * invocation, which is exactly one call site invocation of one
     * frame.</p>
     */
    private static void retainInnermostDeclaredSiteCaptures(
            List<Map<String, Object>> plans) {
        Map<Long, Set<String>> ownersByInvocation = new LinkedHashMap<>();
        for (Map<String, Object> plan : plans) {
            String activationId = stringValue(plan.get("activationId"));
            if (activationId.isEmpty()) continue;
            for (Map<String, Object> capture
                    : rows(plan.get(DeclaredSiteCapture.PLAN_FIELD))) {
                ownersByInvocation.computeIfAbsent(longNumber(capture.get(
                        DeclaredSiteCapture.INVOCATION_ID), -1L),
                        ignored -> new LinkedHashSet<>()).add(activationId);
            }
        }
        Set<String> shadowed = new LinkedHashSet<>();
        for (Map<String, Object> child : plans) {
            List<String> enclosing = strings(child.get(
                    "enclosingActivationIds"));
            if (enclosing.isEmpty()) continue;
            for (Map<String, Object> capture
                    : rows(child.get(DeclaredSiteCapture.PLAN_FIELD))) {
                long invocation = longNumber(capture.get(
                        DeclaredSiteCapture.INVOCATION_ID), -1L);
                Set<String> owners = ownersByInvocation.get(invocation);
                if (owners == null || owners.size() < 2) continue;
                for (String ancestor : enclosing) {
                    if (owners.contains(ancestor)) {
                        shadowed.add(ancestor + "\n" + invocation);
                    }
                }
            }
        }
        if (shadowed.isEmpty()) return;
        for (Map<String, Object> plan : plans) {
            String activationId = stringValue(plan.get("activationId"));
            List<Map<String, Object>> retained = new ArrayList<>();
            for (Map<String, Object> capture
                    : rows(plan.get(DeclaredSiteCapture.PLAN_FIELD))) {
                if (!shadowed.contains(activationId + "\n" + longNumber(
                        capture.get(DeclaredSiteCapture.INVOCATION_ID),
                        -1L))) {
                    retained.add(capture);
                }
            }
            if (retained.isEmpty()) {
                plan.remove(DeclaredSiteCapture.PLAN_FIELD);
            } else {
                plan.put(DeclaredSiteCapture.PLAN_FIELD, retained);
            }
        }
    }

    /**
     * What the recording states at the sites the scope map named
     * DECLARED_SITE, for ONE occurrence: one row per completed call there,
     * with the value it returned and the receiver it ran on.
     *
     * <p>The ordinal counts every completed call of the occurrence at that
     * (site, callee), whether or not the site is declared, so a declared
     * site's ordinal is the same number whichever sites a later declaration
     * adds or drops.  It is the port's replay address, so it is counted from
     * the recording's own order and never from a per-run call id.</p>
     *
     * <p>No admission is taken here.  A capture is published for every
     * declared site this occurrence entered; whether any of them mints is
     * {@code ConcolicScheduler.SymbolicInputSelection}'s decision, and the
     * value a capture states is evidence either way.</p>
     */
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

    /**
     * The symbolic inputs one activation of a region is planned over: its
     * declared cut ports -- README section 3's {@code Req_in}, {@code
     * Resp_in}, {@code Live_in} -- whose site the declaration carries.  A
     * region row holds nothing else ({@code RuntimeSelectedRegionFinalizer
     * #declareCommunicationPorts}); every other root is minted at PLAN from
     * the scope map's DECLARED_SITE rows.
     *
     * <p>A declared cut port can appear twice: the region-level declaration
     * and, once a recorded delivery named it, this occurrence's own stamped
     * copy of it.  The copy wins.</p>
     */
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

    /** Names the value cell of every declared cut port of one region, once. */
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
        return action;
    }


    /**
     * Whether the VM can present this port's value as a symbol at all.
     *
     * <p>A type question and a statement the port already carries, not a
     * role: a value whose type the SMT layer has no term for cannot be a
     * solver leaf however it is declared, and a port the plan has already
     * marked concrete says so about itself.</p>
     */
    static boolean symbolicLeafPort(Map<String, Object> port,
                                    String javaType) {
        if (port != null && !port.isEmpty()) {
            String demand = stringValue(port.get("symbolicDemand"));
            if (demand.startsWith("CONCRETE_")
                    || Boolean.TRUE.equals(port.get("captureRootOnly"))
                    || Boolean.TRUE.equals(port.get("loopControlOnly"))
                    || Boolean.TRUE.equals(port.get("controlOnly"))
                    || Boolean.TRUE.equals(port.get("pathAssumptionOnly"))) {
                return false;
            }
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
                encoded.add(object(
                        "occurrence", index + 1,
                        "outcome", event.outcome,
                        "eventSeq", event.seq));
            }
            // The FIRST decision the recording made at this site in this
            // activation.  It used to be the first one whose outcome equalled
            // a required outcome the region plan carried -- an election over
            // recorded evidence, and the polarity it elected on is now stated
            // once, by the static scope map's TARGET_SITE row.
            int selectedIndex = 0;
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
            branch.put("occurrences", encoded);
            result.add(branch);
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
    public static final String ANCHOR_UNREGISTERED_SOURCE = "UNREGISTERED_SOURCE";
    /**
     * The activation inherited a registered source from its creating thread,
     * while its own receiver had no source alias. Replay therefore uses the
     * thread context as the anchor.
     */
    public static final String ANCHOR_INHERITED_CONTEXT = "INHERITED_CONTEXT";

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

    /**
     * The bucket this region's activations are counted in.
     *
     * <p>An occurrence is the k-th activation of this region on this node
     * and epoch, over every activation the recording holds.  Counting and
     * matching have to use one scope or the ordinal means one thing when it
     * is written and another when it is checked, so this is not merely the
     * same shape as the replay's bucket -- it is literally the same
     * function, which {@code
     * ConcolicTaskPlan.RuntimeTask.invocationCounterKey} also calls.  Two
     * spellings of one rule is how the ordinal drifted before.</p>
     *
     * <p>A grouping key for a local count, not an identity: an occurrence is
     * its address, and the address is minted from where the activation was.
     * This only says which invocations of one region on one component and
     * one root method are being numbered together, for the selector the
     * replay matches its root call on.</p>
     */
    private static String replayInvocationScope(
            String regionId, MethodEvent root, SourceRef source) {
        return source.key() + "\n" + safe(regionId) + "\n"
                + safe(root == null ? "" : root.method);
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
    /**
     * One activation's source, by the rule both ends run.
     *
     * <p>{@link RuntimeTraceContext#attributedActivationSource} is that rule:
     * the activation's own stamp, else the unique stamp among its frames,
     * else the unregistered source.  The replay evaluates the same function
     * over the same three inputs, so a population counted here is the
     * population counted there.</p>
     */
    private static SourceRef activationSource(MethodEvent root,
                                              List<SourceRef> stamped) {
        return RuntimeTraceContext.attributedActivationSource(
                root == null ? null : root.source, stamped);
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
            edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy.PLAN_FIELD;

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
     * order ({@link OccurrenceBinding}).  {@code rootSelector} is the address
     * replay itself uses: the root method, its receiver context, the causal
     * anchor and the invocation ordinal inside that anchor's scope.  Neither
     * carries a per-run address, so two independent recordings of one
     * workload publish the same name for the same activation.</p>
     *
     * <p>The {@code ACT.} prefix and the UUID shape are the ones consumers
     * already parse; only what the UUID is taken over changes.</p>
     */
    public static String activationId(String occurrenceId,
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
        final List<Map<String, Object>> regionCatalog = new ArrayList<>();
        /** Gaps the region finalizer raised while building these ports. */
        final List<Map<String, Object>> planGaps = new ArrayList<>();
        final List<Map<String, Object>> runtimeInstances = new ArrayList<>();
        /**
         * The region entries this recording FOLDED: one row per entry that
         * opened no occurrence of its own, naming the occurrence it folded
         * into ({@link #stampFoldedRegionEntries}).  They are deliberately
         * not activations and are kept out of {@link #runtimeInstances},
         * which is the one list "one occurrence, one activation" is counted
         * over.
         */
        final List<Map<String, Object>> regionFolds = new ArrayList<>();
        int staticRegionCount;

        String runtimePlanJsonl() {
            List<JsonObject> plans = new ArrayList<>();
            for (Map<String, Object> plan : regionPlans) {
                plans.add(toJsonTreeFast(plan).getAsJsonObject());
            }
            List<JsonObject> regions = new ArrayList<>();
            for (Map<String, Object> region : regionCatalog) {
                regions.add(toJsonTreeFast(region).getAsJsonObject());
            }
            List<JsonObject> gaps = new ArrayList<>();
            for (Map<String, Object> gap : planGaps) {
                gaps.add(toJsonTreeFast(gap).getAsJsonObject());
            }
            return RuntimePlanArtifact.encode(plans, regions, gaps);
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
        /**
         * The occurrence address the RECORDING computed, or {@code ""}.
         *
         * <p>Identity v3, stated once, where the activation ran: {@code
         * Identity.occurrence} on the recording's own frame stack and scope
         * (IDENTITY-IMPL B).  Non-empty exactly on the entry of a method
         * that opens a region.  PLAN reads it; PLAN does not re-derive it,
         * because a second derivation is a second identity and the two
         * disagreed -- the plan addressed {@code loadInternal} at a
         * seven-frame path and the replay at {@code loadInternal@1}
         * (REPORT-M2 §5).</p>
         */
        final String occurrenceAddress;
        /**
         * Whether this entry was FOLDED into the occurrence already running
         * on its thread (F1).
         *
         * <p>Told apart from an empty {@link #occurrenceAddress} on purpose,
         * because the two are different facts with different owners: a fold
         * is an entry that IS no occurrence -- a method call inside one, and
         * PLAN records no activation for it -- while an address the
         * recording could not compute is a hole the finalizer refuses
         * ({@code RuntimeSelectedRegionFinalizer#readOccurrences}).</p>
         */
        final boolean regionFolded;
        MethodEvent(long seq, String test, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId,
                    long laneId, long spanId, long remoteParentSpanId,
                    SourceRef source, boolean receiverAttributed,
                    String requestKey, String requestApi) {
            this(seq, test, threadName, tid, method, objectId, receiverType,
                    callId, parentCallId, parentSiteId, laneId, spanId,
                    remoteParentSpanId, source,
                    receiverAttributed, requestKey, requestApi, "");
        }

        MethodEvent(long seq, String test, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId,
                    long laneId, long spanId, long remoteParentSpanId,
                    SourceRef source, boolean receiverAttributed,
                    String requestKey, String requestApi,
                    String occurrenceAddress) {
            this(seq, test, threadName, tid, method, objectId, receiverType,
                    callId, parentCallId, parentSiteId, laneId, spanId,
                    remoteParentSpanId, source, receiverAttributed,
                    requestKey, requestApi, occurrenceAddress, false);
        }

        MethodEvent(long seq, String test, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId,
                    long laneId, long spanId, long remoteParentSpanId,
                    SourceRef source, boolean receiverAttributed,
                    String requestKey, String requestApi,
                    String occurrenceAddress, boolean regionFolded) {
            this.occurrenceAddress = safe(occurrenceAddress);
            this.regionFolded = regionFolded;
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
            this.remoteParentSpanId = remoteParentSpanId;
            this.source = source;
            this.sourceKey = sourceOf(source).key();
            this.receiverAttributed = receiverAttributed;
            this.requestKey = safe(requestKey);
            this.requestApi = safe(requestApi);
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
        final long remoteParentSpanId;
        final SourceRef source;
        final String requestKey;
        final String requestApi;
        /**
         * The {@link edu.uva.liftlab.graphchecker.contract.Endpoint} id this
         * leg's sender minted, or {@code ""} on a delivery.  This is the
         * digest an occurrence downstream of the message carries as its
         * causal anchor.
         */
        final String producerEndpointId;
        /**
         * The components behind that digest, as the sender stated them:
         * which occurrence sent the message, at which transport site, the
         * k-th event of that occurrence there, and the attempt.  Two
         * anchors are told apart on these; the digest only says they
         * differ.
         */
        final String producerEndpoint;
        ProtocolEvent(long seq, String direction, String transport,
                      String correlationId, String attemptId, String half,
                      String threadName, long tid, String method, long callId,
                      long invocationId, String declaredCallee,
                      long laneId, long spanId, long remoteParentSpanId,
                      SourceRef source, String requestKey, String requestApi,
                      String producerEndpointId, String producerEndpoint) {
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
            this.remoteParentSpanId = remoteParentSpanId;
            this.source = source;
            this.requestKey = safe(requestKey);
            this.requestApi = safe(requestApi);
            this.producerEndpointId = safe(producerEndpointId);
            this.producerEndpoint = safe(producerEndpoint);
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
