package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.ToNumberPolicy;
import com.google.gson.reflect.TypeToken;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.concolic.AutomaticRegionEdge;
import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.concolic.RecordedReadFrom;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
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
    /**
     * Logical source of a workload whose tracing never registered one.  It
     * is a declared default, not an inferred role: nothing is guessed from
     * method names, thread names, or stack frames.
     */
    static final SourceRef UNREGISTERED_SOURCE = new SourceRef(
            "TEST_DRIVER", "WORKLOAD", "workload/unregistered", 0L);
    /**
     * A declared cut port this planner cannot address at runtime.
     *
     * <p>The declaration is real - the cut carries this value - but the port
     * row names no capture, no erased type or no defining method, so there is
     * no site to symbolize it at.  Named rather than dropped, because the
     * missing half is a property of the declaration and a consumer that saw
     * only "no input" would read it as "no such port".</p>
     */
    private static final String GAP_COMMUNICATION_PORT_CAPTURE_UNDECLARED =
            "COMMUNICATION_PORT_CAPTURE_UNDECLARED";
    /** Authority of one recorded exchange link between two occurrences. */
    static final String DELIVERY_LINK_AUTHORITY =
            "RECORDED_EXCHANGE_OCCURRENCE_LINK_V1";
    /** An exported exchange no other occurrence recorded receiving. */
    static final String GAP_LINK_DELIVERY_UNOBSERVED =
            "RUNTIME_EXCHANGE_DELIVERY_UNOBSERVED";
    /** A recorded activation this stage could not attribute to a source. */
    static final String GAP_RUNTIME_SOURCE_UNSTAMPED =
            "RUNTIME_ACTIVATION_SOURCE_UNSTAMPED";
    /**
     * A dependency an output closure dropped while still succeeding.
     *
     * <p>A refusal that makes the closure {@code null} already reaches the
     * artifact as a blocker.  A reason recorded on the way to a
     * <em>successful</em> closure used to be discarded, so a slice input the
     * closure decided to leave out disappeared with the reason it was left
     * out for.  This names that loss without blocking the goal: the relation
     * is still admitted, and what it no longer depends on is stated.</p>
     */
    static final String GAP_OUTPUT_CLOSURE_INPUT_DROPPED =
            "RUNTIME_OUTPUT_CLOSURE_INPUT_DROPPED";
    /** Per-goal record {@link #publishClosureDropGaps} publishes. */
    private static final String ADMITTED_CLOSURE_DROPS =
            "admittedOutputClosureDrops";

    /** One named gap row of this stage, in the shared discovery shape. */
    static Map<String, Object> gap(String kind, String reason,
                                   String activationId, String method,
                                   String siteId, String detail) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", 1);
        row.put("kind", "RUNTIME_REGION_GAP");
        row.put("gapKind", kind);
        row.put("reason", reason);
        row.put("activationId", text(activationId));
        row.put("method", text(method));
        row.put("siteId", text(siteId));
        row.put("detail", text(detail));
        return row;
    }

    /**
     * A recorded touch of a selected shared location that no relation holds.
     *
     * <p>README section 4 states a read as
     * {@code exactlyOne(rf_W1, ..., rf_unknown)} over the writers of its
     * location, with each arm guarded by {@code exists(Wk) AND guard(Wk)}.
     * An arm exists only for a writer some relation of the model contains,
     * and the reader only asks the question if a relation contains it too.
     * So an activation the trace records reading or writing a selected
     * location, which this stage region-ifies with nothing, is a missing arm
     * or a missing question - and it used to be neither a plan row, nor a
     * link, nor a gap.  It was absent.</p>
     *
     * <p>That silence is a defect on its own, before any admission decision:
     * a stage that models a recorded touch with nothing and says nothing is
     * indistinguishable from one that had nothing to model.  In HDFS-11741
     * the read is on the lookup side while the writes are on the rotation
     * side and on each node's own expiry pass, so the arms most likely to
     * vanish are exactly the ones the target depends on.</p>
     */
    static final String GAP_SHARED_LOCATION_TOUCH_UNREGIONED =
            "RUNTIME_SHARED_LOCATION_TOUCH_UNREGIONED";
    /**
     * The census this stage publishes whether or not it lost anything.
     *
     * <p>Unconditional on purpose.  A stage that publishes its losses only
     * when it has some leaves an empty file meaning two different things -
     * "nothing was lost" and "nothing was examined" - and the second is what
     * a silently unenumerated location looks like.</p>
     */
    static final String SHARED_LOCATION_TOUCH_CENSUS =
            "RUNTIME_SHARED_LOCATION_TOUCH_CENSUS";
    /** Authority of every row the shared-location touch audit publishes. */
    static final String SHARED_LOCATION_TOUCH_AUTHORITY =
            "RECORDED_SHARED_LOCATION_TOUCH_V1";
    /** No planned activation's recorded frame chain contains the touch. */
    static final String TOUCH_ACTIVATION_UNPLANNED =
            "RECORDED_TOUCH_ACTIVATION_UNPLANNED";
    /** The touching activation seeded this stage under an unselected region. */
    static final String TOUCH_REGION_UNSELECTED =
            "RECORDED_TOUCH_ACTIVATION_REGION_UNSELECTED";
    /** The touching activation's occurrence is not one the region retained. */
    static final String TOUCH_OCCURRENCE_UNRETAINED =
            "RECORDED_TOUCH_ACTIVATION_OCCURRENCE_UNRETAINED";
    /** How the gap's {@code activationId} was resolved. */
    static final String TOUCH_ACTIVATION_AUTHORITY =
            "activationAuthority";
    /** From the outermost frame of the touch's recorded caller chain. */
    static final String TOUCH_ROOT_FROM_RECORDED_CHAIN =
            "OUTERMOST_RECORDED_FRAME_V1";
    /** From an activation seed this stage was handed and did not plan. */
    static final String TOUCH_ROOT_FROM_SEED =
            "PLANNER_ACTIVATION_SEED_V1";
    /** Whether every recorded touch of this goal's locations reached one. */
    static final String SHARED_LOCATION_UNIVERSE_CLOSED =
            "sharedLocationUniverseClosed";
    /** How many recorded touches of this goal's locations nothing models. */
    static final String UNREGIONED_TOUCH_COUNT = "unregionedTouchCount";
    /** One planned activation touching another's selected location. */
    static final String SHARED_LOCATION_TOUCH_LINK = "SHARED_LOCATION_TOUCH";

    /**
     * A selected region root that ran without reaching its own anchor.
     *
     * <p>This used to be a bare {@code continue}, which is the same silence
     * as {@link #GAP_SHARED_LOCATION_TOUCH_UNREGIONED} one stage earlier: the
     * activation ran, the trace holds every frame of it, and nothing recorded
     * that it was considered and dropped.  It is also exactly the shape an
     * activation admitted by a shared-location demand has - it touches the
     * location and never reaches the target - so leaving it silent would hide
     * the admission half's own failures as well as this stage's.</p>
     */
    static final String GAP_ACTIVATION_ANCHOR_UNOBSERVED =
            "RUNTIME_ACTIVATION_ANCHOR_UNOBSERVED";
    /** Reason of {@link #GAP_ACTIVATION_ANCHOR_UNOBSERVED}. */
    static final String ANCHOR_UNOBSERVED_REASON =
            "SELECTED_REGION_ROOT_RAN_WITHOUT_ANCHOR";
    /**
     * Skeleton field naming why the admission half selected this region.
     *
     * <p>Absent on every region admitted by target reachability, so a run
     * that declares nothing produces exactly the rows it produced before.</p>
     */
    static final String ADMISSION_BASIS = "admissionBasis";
    /**
     * Admission by the recorded version store of an enumerated location.
     *
     * <p>The key the sibling design settled on: not static may-touch, which
     * is far too large in HDFS and whose admitted regions dominate Zero-VM
     * wall time, and not a hand-written case list, which can only fail by
     * omission - the exact failure that leaves {@code rf_unknown}.</p>
     */
    static final String SHARED_LOCATION_DEMAND_ADMISSION =
            "SHARED_LOCATION_DEMAND_V1";
    /** Skeleton field: the region whose demand admitted this one. */
    static final String DEMANDED_BY_REGIONS = "demandedByRegionIds";
    /** Skeleton field: the enumerated locations that demand covers. */
    static final String DEMANDED_SHARED_LOCATIONS =
            "demandedSharedLocations";
    /** A shared-location demand naming a region this run never planned. */
    static final String GAP_SHARED_LOCATION_DEMAND_UNPLANNED =
            "RUNTIME_SHARED_LOCATION_DEMAND_CONSUMER_UNPLANNED";

    /**
     * Demanded output occurrences one plan's epoch bound leaves unmodelled.
     *
     * <p>Its own kind rather than a writer-universe row: these are epochs of
     * one producer's own output, not alternative writers of one read, and
     * folding the two would present a bounded history as an open read-from
     * choice.</p>
     */
    static final String GAP_OUTPUT_ALTERNATIVE_UNMODELLED =
            "RUNTIME_OUTPUT_ALTERNATIVE_UNMODELLED";
    /** Authority of {@link #GAP_OUTPUT_ALTERNATIVE_UNMODELLED}. */
    static final String OUTPUT_ALTERNATIVE_AUTHORITY =
            "RUNTIME_OUTPUT_ALTERNATIVE_UNMODELLED_V1";
    /** Reason of {@link #GAP_OUTPUT_ALTERNATIVE_UNMODELLED}. */
    static final String OUTPUT_ALTERNATIVE_REASON =
            "DEMANDED_OUTPUT_OCCURRENCES_BEYOND_DECLARED_LOOP_BODY_BOUND";
    /** Plan member the unmodelled epoch counts travel in. */
    static final String UNMODELLED_OUTPUT_ALTERNATIVES =
            "unmodelledOutputAlternatives";

    private RuntimeRegionPlanner() {
    }

    static Result planSkeletonGraph(File skeletonFile,
                                    List<MethodEvent> methods) {
        return planSkeletonGraph(skeletonFile, methods,
                Collections.<RuntimeEvent>emptyList(),
                Collections.<ProtocolEvent>emptyList());
    }

    /**
     * Binds static region skeletons to the activations a run performed.
     *
     * <p>A region is coarse: one activation is one region occurrence, and a
     * synchronous call inside it does not split it. A discovered communication
     * entry is itself an observed receiver occurrence, independent of the Java
     * framework caller chain.  Cross-occurrence communication is linked later
     * only from a recorded exchange; no Java parent is an RPC identity.</p>
     */
    static Result planSkeletonGraph(File skeletonFile,
                                    List<MethodEvent> methods,
                                    List<RuntimeEvent> runtimeEvents,
                                    List<ProtocolEvent> protocolEvents) {
        List<Map<String, Object>> skeletons = read(skeletonFile);
        for (Map<String, Object> row : skeletons) {
            require(row, 3, "REGION_SKELETON", skeletonFile);
        }
        // The recorded call sites are part of this index, not an extra: the
        // across-cut attribution below asks which call site opened a frame,
        // and that answer lives in the CALL_SITE_ENTER events.  Built without
        // them the index answered "" for every frame, so no method was ever
        // on the far side of a cut at this stage while the later planning
        // pass - holding the same events - said several were.
        TraceIndex trace = new TraceIndex(methods, runtimeEvents == null
                ? Collections.<RuntimeEvent>emptyList() : runtimeEvents,
                Collections.emptyList(), protocolEvents);
        Result result = new Result();
        result.staticRegionCount = skeletons.size();
        Set<String> skeletonRoots = new LinkedHashSet<>();
        for (Map<String, Object> skeleton : skeletons) {
            String root = text(skeleton.get("rootMethod"));
            String authority = text(skeleton.get("rootAuthority"));
            if ((!validRootAuthority(authority)
                    && !"COMMUNICATION_ENTRY".equals(authority))
                    || constructor(root)) {
                throw new IllegalArgumentException(
                        "region skeleton has no authoritative execution "
                                + "context root: " + root);
            }
            if (!skeletonRoots.add(root)) {
                throw new IllegalArgumentException(
                        "duplicate region skeleton root: " + root);
            }
        }
        Map<Long, Map<String, Object>> activationByCall =
                new LinkedHashMap<>();
        for (Map<String, Object> skeleton : skeletons) {
            if ("COMMUNICATION_ENTRY".equals(text(skeleton.get(
                    "rootAuthority")))) {
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
                    addAnchorUnobservedGap(result, skeleton, root, anchors);
                    continue;
                }
                addSkeletonActivation(activationByCall, skeleton,
                        root, trace);
            }
        }
        for (Map<String, Object> fragment : skeletons) {
            if (!"COMMUNICATION_ENTRY".equals(text(fragment.get(
                    "rootAuthority")))) {
                continue;
            }
            String endpoint = text(fragment.get("rootMethod"));
            List<String> anchors = anchors(fragment);
            for (MethodEvent receiver : trace.methods(endpoint)) {
                Set<String> observed = trace.methodNames(
                        trace.subtree(receiver.callId));
                if (Collections.disjoint(observed, anchors)) {
                    addAnchorUnobservedGap(result, fragment, receiver, anchors);
                    continue;
                }
                addSkeletonActivation(activationByCall, fragment, receiver,
                        trace);
            }
        }
        stampActivationContainment(activationByCall, trace);
        result.runtimeInstances.addAll(activationByCall.values());
        linkSharedLocationDemands(result);
        stampRecordedExchanges(result, trace, protocolEvents);
        return result;
    }

    /**
     * Names a selected region root that ran and reached none of its anchors.
     *
     * <p>Target-reachability is this stage's admission test, and it is a
     * filter and not an invariant: the root really ran, so refusing it is a
     * decision about this activation, not about the skeleton.  What was
     * missing is that the decision was recorded nowhere.  An activation
     * admitted by a shared-location demand is exactly the shape that lands
     * here - it touches the location and never reaches the target - so the
     * admission half needs this row to see its own declaration take
     * effect.</p>
     */
    private static void addAnchorUnobservedGap(
            Result result, Map<String, Object> skeleton, MethodEvent root,
            List<String> anchors) {
        Map<String, Object> gap = gap(
                GAP_ACTIVATION_ANCHOR_UNOBSERVED, ANCHOR_UNOBSERVED_REASON,
                activationId(root), root.method, "",
                text(skeleton.get("regionId")) + " anchors=" + anchors.size());
        gap.put("authority", SHARED_LOCATION_TOUCH_AUTHORITY);
        gap.put("sourceKey", root.sourceKey);
        gap.put("regionId", text(skeleton.get("regionId")));
        gap.put("rootMethod", root.method);
        gap.put("rootCallId", Long.valueOf(root.callId));
        gap.put("thread", root.threadName);
        gap.put("threadId", Long.valueOf(root.tid));
        gap.put("anchorMethods", new ArrayList<>(anchors));
        String basis = text(skeleton.get(ADMISSION_BASIS));
        if (!basis.isEmpty()) gap.put(ADMISSION_BASIS, basis);
        result.gaps.add(gap);
    }

    /**
     * Links each activation a shared-location demand admitted to the
     * activations whose demand admitted it.
     *
     * <p>README section 4 states a read as
     * {@code exactlyOne(rf_W1, ..., rf_unknown)}, so what an admitted writer
     * needs from this stage is not a delivery but membership: the arm exists
     * and the model may choose it.  Every planned activation of the demanding
     * region is therefore linked, and none of them is preferred - selecting
     * one here would be exactly the order-based resolution README section 1
     * forbids, and the choice belongs to the solver in any case.</p>
     *
     * <p>A demand naming a region this run planned nothing for is a named
     * gap.  It is the admission half's own failure mode - a location was
     * enumerated for a consumer that never ran - and it must not read as an
     * admitted writer with nobody to write for.</p>
     */
    private static void linkSharedLocationDemands(Result result) {
        Map<String, List<Map<String, Object>>> byRegion =
                new LinkedHashMap<>();
        for (Map<String, Object> activation : result.runtimeInstances) {
            byRegion.computeIfAbsent(text(activation.get("regionId")),
                    ignored -> new ArrayList<>()).add(activation);
        }
        for (Map<String, Object> activation : result.runtimeInstances) {
            if (!SHARED_LOCATION_DEMAND_ADMISSION.equals(
                    text(activation.get(ADMISSION_BASIS)))) {
                continue;
            }
            List<String> consumerRegions = strings(
                    activation.get(DEMANDED_BY_REGIONS));
            for (String consumerRegion : consumerRegions) {
                List<Map<String, Object>> consumers = byRegion.getOrDefault(
                        consumerRegion, Collections.<Map<String,
                                Object>>emptyList());
                if (consumers.isEmpty()) {
                    Map<String, Object> gap = gap(
                            GAP_SHARED_LOCATION_DEMAND_UNPLANNED,
                            TOUCH_ACTIVATION_UNPLANNED,
                            text(activation.get("activationId")),
                            text(activation.get("rootMethod")), "",
                            consumerRegion);
                    gap.put("authority", SHARED_LOCATION_TOUCH_AUTHORITY);
                    gap.put(DEMANDED_BY_REGIONS,
                            new ArrayList<>(consumerRegions));
                    gap.put(DEMANDED_SHARED_LOCATIONS, new ArrayList<>(
                            strings(activation.get(
                                    DEMANDED_SHARED_LOCATIONS))));
                    result.gaps.add(gap);
                    continue;
                }
                for (Map<String, Object> consumer : consumers) {
                    Map<String, Object> link = new LinkedHashMap<>();
                    link.put("schemaVersion", 3);
                    link.put("kind", "RUNTIME_OCCURRENCE_LINK");
                    link.put("linkKind", SHARED_LOCATION_TOUCH_LINK);
                    link.put("fromActivationId",
                            text(activation.get("activationId")));
                    link.put("fromRegionId",
                            text(activation.get("regionId")));
                    link.put("fromRootCallId", activation.get("rootCallId"));
                    link.put("toActivationId",
                            text(consumer.get("activationId")));
                    link.put("toRegionId", text(consumer.get("regionId")));
                    link.put("toRootCallId", consumer.get("rootCallId"));
                    link.put(DEMANDED_SHARED_LOCATIONS, new ArrayList<>(
                            strings(activation.get(
                                    DEMANDED_SHARED_LOCATIONS))));
                    link.put(ADMISSION_BASIS,
                            SHARED_LOCATION_DEMAND_ADMISSION);
                    link.put("authority", SHARED_LOCATION_TOUCH_AUTHORITY);
                    result.occurrenceLinks.add(link);
                }
            }
        }
    }

    /**
     * Stamps every planned activation with the exchanges its own transport
     * hooks recorded, and links an exporting occurrence to the occurrence
     * that received the same exchange.
     *
     * <p>This is the tracing control plane's own record and nothing more: it
     * says a message crossed this boundary between these two occurrences.  It
     * proves no value relation - that is the VM's export/attach handoff and
     * its {@code VALUE_HANDOFF} ledger edge - so nothing here narrows a
     * delivery by ordinal, by leg, by port shape or by arrival order.  Two
     * occurrences claiming one exchange, or none claiming it, is a named gap
     * rather than a chosen answer.</p>
     */
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
            // A transport hook runs inside the transport (and commonly inside
            // Method.invoke), while the application call that entered it is
            // the site the catalog names.  Preserve the exact recorded nesting
            // relation rather than guessing by method name, payload or event
            // order.
            event.enclosingInvocationIds =
                    trace.enclosingInvocationIds(event.callId);
            event.enclosingCallIds = trace.enclosingCalls(event.callId);
            long ownerRoot = trace.nearestEnclosingCall(event.callId,
                    activationRoots);
            if (ownerRoot > 0L) {
                protocolByActivationRoot.computeIfAbsent(ownerRoot,
                        ignored -> new ArrayList<ProtocolEvent>()).add(event);
            }
        }
        stampSynchronousServerTransactions(result.runtimeInstances, trace,
                protocolEvents, protocolByActivationRoot);

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
                row.put("requestApi", event.requestApi);
                // The hook runs inside the transport.  Its immediate caller
                // is the application-side communication call recorded by the
                // static catalog, so keep that exact site rather than the
                // hook method (which is not a call-site identity at all).
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
            exportedByActivation.put(text(activation.get("activationId")),
                    exported);
        }
        for (Map<String, Object> activation : result.runtimeInstances) {
            for (Map<String, Object> exported
                    : exportedByActivation.getOrDefault(
                    text(activation.get("activationId")),
                    Collections.<Map<String, Object>>emptyList())) {
                linkOneDelivery(result, activation, exported, receivedBy);
            }
        }
    }

    /**
     * The retained loops of one occurrence: the region's declared rows whose
     * enclosing method this occurrence actually holds.  Loop identity is
     * independent of communication, so the filter is by method membership
     * and nothing else.
     */
    private static List<Map<String, Object>> retainedLoops(
            Map<String, Object> region, Set<String> occurrenceMethods) {
        List<Map<String, Object>> retained = new ArrayList<>();
        for (Map<String, Object> loop
                : rows(region.get(RETAINED_LOOPS_FIELD))) {
            if (occurrenceMethods.contains(
                    text(loop.get("enclosingMethod")))) {
                retained.add(new LinkedHashMap<>(loop));
            }
        }
        return retained;
    }

    private static void linkOneDelivery(
            Result result, Map<String, Object> activation,
            Map<String, Object> exported,
            Map<String, List<Map<String, Object>>> receivedBy) {
        String activationId = text(activation.get("activationId"));
        List<Map<String, Object>> deliveries = new ArrayList<>();
        for (Map<String, Object> delivery : receivedBy.getOrDefault(
                text(exported.get("exchangeLeg")),
                Collections.<Map<String, Object>>emptyList())) {
            Map<String, Object> candidate = (Map<String, Object>)
                    delivery.get("activation");
            if (candidate != null && !activationId.equals(
                    text(candidate.get("activationId")))) {
                deliveries.add(delivery);
            }
        }
        if (deliveries.isEmpty()) {
            result.gaps.add(gap(GAP_LINK_DELIVERY_UNOBSERVED,
                    "NO_OCCURRENCE_RECORDED_THE_DELIVERY",
                    activationId, text(activation.get("rootMethod")),
                    text(exported.get("callSiteId")),
                    text(exported.get("exchangeLeg"))));
            return;
        }
        // Replay is distributed and therefore not required to reproduce one
        // receiver instance.  Every observed delivery is a bounded causal
        // alternative; later failure slicing keeps only alternatives that can
        // reach the target.  The VM handle, not this occurrence edge, remains
        // the value-propagation authority.
        Set<String> emitted = new LinkedHashSet<>();
        for (Map<String, Object> delivery : deliveries) {
            Map<String, Object> toActivation = (Map<String, Object>)
                    delivery.get("activation");
            String identity = activationId + "\n"
                    + text(toActivation.get("activationId")) + "\n"
                    + text(exported.get("exchangeLeg")) + "\n"
                    + text(exported.get("callSiteId"));
            if (!emitted.add(identity)) continue;
            Map<String, Object> link = new LinkedHashMap<>();
            link.put("schemaVersion", 3);
            link.put("kind", "RUNTIME_OCCURRENCE_LINK");
            link.put("linkKind", "SERVER_ENTRY");
            link.put("fromActivationId", activationId);
            link.put("fromRegionId", text(activation.get("regionId")));
            link.put("fromRootCallId", activation.get("rootCallId"));
            link.put("callSiteId", text(exported.get("callSiteId")));
            link.put("toActivationId",
                    text(toActivation.get("activationId")));
            link.put("toRegionId", text(toActivation.get("regionId")));
            link.put("toRootCallId", toActivation.get("rootCallId"));
            link.put("exchangeLeg", text(exported.get("exchangeLeg")));
            link.put("senderEventSeq", exported.get("eventSeq"));
            link.put("receiverEventSeq", delivery.get("eventSeq"));
            link.put("attemptId", text(exported.get("attemptId")));
            link.put("direction", text(exported.get("half")));
            link.put("transport", text(exported.get("transport")));
            link.put("requestApi", text(exported.get("requestApi")));
            link.put("crossThread",
                    !String.valueOf(activation.get("threadId")).equals(
                            String.valueOf(toActivation.get("threadId"))));
            link.put("authority", DELIVERY_LINK_AUTHORITY);
            result.occurrenceLinks.add(link);
        }
    }

    /**
     * Attributes the two transport hooks bracketing one synchronous server
     * invocation to the exact planned handler activation between them.
     *
     * <p>The request RECEIVE is emitted after decode and before the protocol
     * handler; the response SEND is emitted after that handler returns.  They
     * are siblings of the handler rather than callers of it, so caller-chain
     * ownership cannot apply.  The application adapter nevertheless records
     * a closed transaction: both hooks state the same correlation, lane,
     * span and remote parent, and static discovery states the bounded handler
     * entry set. Replay may materialize several compatible hooks or roots;
     * every finite compatible attribution is retained as an alternative
     * instead of using uniqueness as a rejection rule.</p>
     */
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
        // Its recorded caller chain therefore need not contain the static
        // cut any more. Attach every compatible response receive to each
        // activation that already owns the corresponding request send.
        for (Map.Entry<String, List<ProtocolEvent>> transaction
                : requestSends.entrySet()) {
            List<ProtocolEvent> responses = responseReceives.getOrDefault(
                    transaction.getKey(), Collections.<ProtocolEvent>emptyList());
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
                    enclosing.add(text(owner.get("activationId")));
                }
            }
            if (!enclosing.isEmpty()) {
                entry.getValue().put("enclosingActivationIds", enclosing);
            }
        }
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
        activation.put("rootCallId", root.callId);
        activation.put("rootMethod", root.method);
        activation.put("rootAuthority", skeleton.get("rootAuthority"));
        activation.put("anchorMethod", observedAnchors.get(0));
        activation.put("anchorMethods", observedAnchors);
        activation.put("selection", skeleton.get("selection"));
        // Present only when the admission half declared one, so a region
        // admitted by target reachability - every region this tree plans
        // today - produces exactly the seed it produced before.
        copyIfPresent(activation, skeleton, ADMISSION_BASIS);
        copyIfPresent(activation, skeleton, DEMANDED_BY_REGIONS);
        copyIfPresent(activation, skeleton, DEMANDED_SHARED_LOCATIONS);
        activation.put("test", root.test);
        activation.put("thread", root.threadName);
        activation.put("threadId", root.tid);
        putTraceContext(activation, root,
                activationSource(root, stampedSources(calls, trace)));
        activation.put("callIds", new ArrayList<>(calls));
        activation.put("observedMethods", new ArrayList<>(observed));
        activationByCall.put(root.callId, activation);
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
                || "RPC_HANDLER".equals(authority)
                // The annotated target's own activation, planned as a root
                // because no execution-context entry statically reaches it.
                || "FAILURE_TARGET_ENTRY".equals(authority);
    }

    static Result plan(File regionFile, File regionEdgeFile,
                       File refinedGraphFile,
                       Collection<Map<String, Object>> runtimeSeeds,
                       List<MethodEvent> methods,
                       List<RuntimeEvent> runtimeEvents,
                       List<FieldAccessEvent> fieldEvents) {
        return plan(read(regionFile), read(regionEdgeFile),
                RefinedFlowIndex.read(refinedGraphFile),
                String.valueOf(regionFile), String.valueOf(regionEdgeFile),
                runtimeSeeds, methods, runtimeEvents, fieldEvents);
    }

    /** Builds the refined-flow index once from already parsed rows. */
    static RefinedFlowIndex buildFlowIndex(
            List<Map<String, Object>> rows, File source) {
        return RefinedFlowIndex.build(rows, source);
    }

    /**
     * In-memory planning entry point.  {@code regionSource} and
     * {@code regionEdgeSource} only label diagnostics; rows must already be
     * in the exact JSONL value domain the file readers would produce.
     *
     * <p>The campaign's own {@link LoopBoundPolicy} is the bound every
     * demanded replay stream of this stage is measured against.  This
     * overload derives it from the declarations the planned rows already
     * carry rather than passing {@code null}: {@code null} states that this
     * run bounded no loop, and a run whose regions carry retained-loop
     * declarations has bounded loops, so asserting it here would be stating
     * a fact contradicted by the very rows being planned.  A run that
     * genuinely declares nothing derives {@link
     * LoopBoundPolicy#MAX_LOOP_BODY_ITERATIONS} and is what it was before.
     * </p>
     */
    static Result plan(List<Map<String, Object>> regions,
                       List<Map<String, Object>> regionEdges,
                       RefinedFlowIndex refinedFlow,
                       String regionSource, String regionEdgeSource,
                       Collection<Map<String, Object>> runtimeSeeds,
                       List<MethodEvent> methods,
                       List<RuntimeEvent> runtimeEvents,
                       List<FieldAccessEvent> fieldEvents) {
        return plan(regions, regionEdges, refinedFlow, regionSource,
                regionEdgeSource, runtimeSeeds, methods, runtimeEvents,
                fieldEvents, Collections.<ProtocolEvent>emptyList(),
                declaredLoopBounds(regions));
    }

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

    /**
     * The campaign policy the planned rows themselves declare.
     *
     * <p>Derived the same way {@link
     * LoopBoundPolicy#maxBackedgeTraversals()} derives the executor's limit,
     * from the same {@code retainedLoops} declarations {@link
     * #retainedLoops} republishes onto every plan row - so the bound a
     * demanded replay stream is measured against at this stage is the bound
     * the campaign declared, not the inherited default a run with no
     * declarations would get.  Nothing is raised: a site declares its own
     * {@code K_L} or inherits, exactly as before.</p>
     *
     * <p>Two rows declaring different bounds for one loop site are refused
     * rather than resolved - one loop has one prefix, and taking either
     * would settle a declaration by which row was walked first.</p>
     */
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
        declared.values().removeIf(
                bound -> bound.intValue()
                        == LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS);
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
                       LoopBoundPolicy loopBound) {
        return plan(regions, regionEdges, refinedFlow, regionSource,
                regionEdgeSource, runtimeSeeds, methods, runtimeEvents,
                fieldEvents, Collections.<ProtocolEvent>emptyList(),
                loopBound);
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
        Map<String, Map<String, Object>> regionById = new LinkedHashMap<>();
        for (Map<String, Object> region : regions) {
            require(region, 3, "SYMBOLIC_REGION", regionSource);
            if (!"RUNTIME_REFINED_DATAFLOW".equals(
                    text(region.get("graphKind")))) {
                throw new IllegalArgumentException(
                        "region was not planned from the refined graph: "
                                + regionSource);
            }
            declareCutPortCells(region);
            regionById.put(text(region.get("regionId")), region);
        }
        // The entry activation's goal - an activation planned as one
        // relation has one answer, so nothing is chosen there.
        Map<String, Map<String, Object>> goalByOccurrence =
                new LinkedHashMap<>();
        Map<String, Map<String, Object>> planByOccurrence =
                new LinkedHashMap<>();
        OccurrenceMinter minter = new OccurrenceMinter();
        Map<String, String> exactPorts = new LinkedHashMap<>();
        // Every seed this loop is handed and does not turn into a plan row.
        // Both drops below used to be bare `continue`s; keeping the seed lets
        // the shared-location audit at the end of this method say which of
        // the two happened to an activation that touched a selected location,
        // instead of reporting only that nothing modelled it.
        List<UnplannedSeed> unplannedSeeds = new ArrayList<>();
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
            if (region == null) {
                unplannedSeeds.add(new UnplannedSeed(seed,
                        TOUCH_REGION_UNSELECTED, ""));
                continue;
            }
            long rootCallId = longNumber(seed.get("rootCallId"), -1L);
            MethodEvent root = trace.methodByCall.get(rootCallId);
            if (root == null) {
                throw new IllegalArgumentException("runtime activation seed "
                        + "references an unknown root call: " + regionId
                        + "#call" + rootCallId);
            }
            Set<String> allowedMethods = new LinkedHashSet<>(
                    strings(region.get("methods")));
            Set<Long> calls = longNumbers(seed.get("callIds"));
            if (calls.isEmpty()) calls = trace.subtree(rootCallId);
            Set<String> observedMethods = new LinkedHashSet<>(
                    strings(seed.get("observedMethods")));
            if (observedMethods.isEmpty()) {
                observedMethods.addAll(trace.methodNames(calls));
            }
            observedMethods.retainAll(allowedMethods);
            List<Map<String, Object>> branches = branches(
                    rows(region.get("branchPolicies")),
                    trace.runtime(calls));
            boolean target = text(region.get("selection"))
                    .startsWith("EXCEPTION")
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
            // retention decision of this activation is read.  The recorded
            // root call is resolved exactly here and stamped onto the rows it
            // named; every later decision compares occurrence identity only.
            // The ordinal is reserved over the root source, before retention
            // is consulted: a discarded activation still occurs at replay,
            // and the region finalizer reserved over the same seed order one
            // stage earlier.  Source and region are the whole counter scope,
            // because they are exactly what the minted identity names: one
            // activation of one region on one source, with no request layer
            // beneath it.  A source whose activations span two request scopes
            // would otherwise restart the count and mint one identity twice.
            int occurrenceIndex = minter.reserveOrdinal(rootSource.key(),
                    regionId);
            String occurrenceId = minter.mint(regionId, rootCallId,
                    source.key(), occurrenceIndex);
            requireFinalizedOccurrence(seed, occurrenceId);
            Set<String> retainedOccurrences = new LinkedHashSet<>(
                    strings(region.get("runtimeOccurrenceIds")));
            if (retainedOccurrences.isEmpty()) {
                throw new IllegalArgumentException("runtime-refined region "
                        + "has no retained activation seeds: " + regionId);
            }
            if (!retainedOccurrences.contains(occurrenceId)) {
                unplannedSeeds.add(new UnplannedSeed(seed,
                        TOUCH_OCCURRENCE_UNRETAINED, occurrenceId));
                continue;
            }
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
            activation.put("occurrenceId", occurrenceId);
            activation.put("rootCallId", root.callId);
            activation.put("rootMethod", root.method);
            activation.put("selection", region.get("selection"));
            activation.put("test", root.test);
            activation.put("thread", root.threadName);
            activation.put("threadId", root.tid);
            putTraceContext(activation, root);
            activation.put("callIds", new ArrayList<>(calls));
            activation.put("observedMethods",
                    new ArrayList<>(observedMethods));
            result.runtimeInstances.add(activation);
            // A run that registered no source is a named gap, not an
            // authority.  It is a property of the activation, so it is stated
            // once for it and not repeated per goal.  An activation whose
            // root frame carries no stamp but whose own frames carry exactly
            // one is stamped from those frames instead, so it is neither a
            // gap nor a fallback; two different stamps inside one activation
            // stay a refusal by name.
            String stampedAuthority = semanticContext.source != null
                    ? "EXPLICIT_TRACE_SOURCE"
                    : stamped.size() == 1 ? UPGRADED_SOURCE_AUTHORITY
                    : GAP_RUNTIME_SOURCE_UNSTAMPED;
            if (GAP_RUNTIME_SOURCE_UNSTAMPED.equals(
                    stampedAuthority)) {
                result.gaps.add(gap(
                        GAP_RUNTIME_SOURCE_UNSTAMPED,
                        stamped.isEmpty() ? "NO_REGISTERED_TRACE_SOURCE"
                                : AMBIGUOUS_SOURCE_REASON,
                        text(activation.get("activationId")), root.method, "",
                        occurrenceId));
            }

            OccurrenceMinter.bindOccurrence(region, rootCallId, occurrenceId);
            OccurrenceMinter.bindEdges(regionEdges, regionId, rootCallId,
                    occurrenceId);
            registerExactPorts(region, occurrenceId, exactPorts);
            List<Map<String, Object>> activationSymbolize = symbolize(
                    rows(region.get("symbolicInputs")), occurrenceId,
                    text(activation.get("activationId")), result);
            List<Map<String, Object>> occurrenceBranches = branches;
            Set<String> occurrenceObserved =
                    new LinkedHashSet<>(observedMethods);
            occurrenceObserved.retainAll(allowedMethods);
            // Static discovery supplies the candidate region; this concrete
            // activation supplies the methods worth slicing in the current
            // wave.  A flipped wave that reaches a new helper records it and
            // expands its own next-wave scope.
            Set<String> occurrenceMethods =
                    new LinkedHashSet<>(occurrenceObserved);
            if (allowedMethods.contains(root.method)) {
                occurrenceMethods.add(root.method);
            }
            List<Map<String, Object>> occurrenceSymbolize =
                    activationSymbolize;
            boolean occurrenceTarget = target;
            long targetBoundaryUpperSeq = occurrenceTarget
                    ? targetBoundaryUpperSeq(occurrenceBranches, seed) : -1L;
            ReturnSlice targetSlice = occurrenceTarget
                    ? refinedFlow.targetReachSlice(regionId, occurrenceId,
                    occurrenceMethods, rows(region.get("symbolicInputs")),
                    rows(region.get("outputs")),
                    rows(region.get("branchPolicies")), root.method,
                    targetBoundaryUpperSeq)
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
                            ? targetProjectionBlockers(region,
                            occurrenceId, targetSlice, occurrenceSymbolize,
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
            plan.put("regionId", region.get("regionId"));
            plan.put("rootAuthority", region.get("rootAuthority"));
            plan.put("activationId", activation.get("activationId"));
            // The retained loops this occurrence's selected methods hold,
            // with their kind and K_L.  Loop identity is independent of
            // communication; the composition unrolls one contiguous prefix
            // per (occurrence, loopSiteId) from exactly these rows.
            List<Map<String, Object>> retainedLoops =
                    retainedLoops(region, occurrenceMethods);
            if (!retainedLoops.isEmpty()) {
                plan.put(RETAINED_LOOPS_FIELD, retainedLoops);
            }
            // Where this occurrence hands a declared communication port to
            // the VM, or takes one from it.  Both sites are the static
            // declaration's own; the replay's export/attach is the only
            // thing that relates the two sides of a cut.
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
            String rootAuthority = text(region.get("rootAuthority"));
            plan.put("rootSelector", rootSelector(root, rootSource,
                    occurrenceTarget
                            && !"COMMUNICATION_ENTRY".equals(rootAuthority)
                            ? semanticContext.requestApi : ""));
            plan.put("targetMethod", region.get("anchorMethod"));
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
            String edgeKind = text(edge.get("kind"));
            if (!"RUNTIME_FIELD_FLOW".equals(edgeKind)
                    && !"RUNTIME_PROTOCOL_FLOW".equals(edgeKind)
                    && !"RUNTIME_COORDINATED_STATE_FLOW".equals(edgeKind)) {
                throw new IllegalArgumentException("invalid runtime region "
                        + "flow row in " + regionEdgeSource);
            }
            String fromOccurrence = text(edge.get("fromOccurrenceId"));
            String toOccurrence = text(edge.get("toOccurrenceId"));
            if (fromOccurrence.isEmpty() || toOccurrence.isEmpty()) {
                throw new IllegalArgumentException(
                        "runtime field flow has no selected activation: "
                                + text(edge.get("edgeId")));
            }
            boolean protocol = "RUNTIME_PROTOCOL_FLOW".equals(edgeKind);
            boolean coordinated =
                    "RUNTIME_COORDINATED_STATE_FLOW".equals(edgeKind);
            boolean containerMutation = "CONTAINER_MUTATION".equals(
                    text(edge.get("bindingKind")));
            // A protocol row must be a correlated delivery: one named
            // exchange, one attempt of it, and a send the receive followed.
            // That is all aggregation can prove, and demanding a configured
            // mapping here would refuse every exchange a workload names for
            // itself.  The test is the same one the composition gate applies,
            // so the two can never disagree about what a candidate is.
            if (protocol && !AutomaticRegionEdge.tracedExchangeCandidate(
                    candidateExchangeRow(edge, fromOccurrence,
                            toOccurrence))) {
                throw new IllegalArgumentException(
                        "runtime protocol flow lacks a correlated exchange, "
                                + "attempt and ordered send/receive: "
                                + text(edge.get("edgeId")));
            }
            String fromPort = exactPort(exactPorts, fromOccurrence,
                    "OUT", text(edge.get("fromPort")), edge);
            String toPort = exactPort(exactPorts, toOccurrence,
                    "IN", text(edge.get("toPort")), edge);
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
            evidence.put("evidenceState", coordinated || protocol
                    ? "APPROXIMATE" : "OBSERVED_BASELINE");
            evidence.put("alignment", "ALIGNED");
            evidence.put("evidenceIds", Collections.singletonList(
                    text(edge.get("edgeId"))));
            result.edgeValidations.add(evidence);
            Map<String, Object> producerGoal =
                    goalByOccurrence.get(fromOccurrence);
            if (producerGoal != null && "OUTPUT_RELATION_CLOSURE".equals(
                    text(producerGoal.get("kind")))) {
                appendGoalBinding(producerGoal, evidence);
            }
            Map<String, Object> consumerGoal =
                    goalByOccurrence.get(toOccurrence);
            if (consumerGoal != null && consumerGoal != producerGoal) {
                // Consumer protocol arguments are symbolic expressions only
                // when this exact trusted incoming edge is present.  They are
                // not fresh independent leaves.
                appendGoalBinding(consumerGoal, evidence);
            }
        }
        // The catalog is published after activation binding so that every
        // emitted port names the occurrence that owns it.  A reader of the
        // artifact therefore never has to join a port to a plan through a
        // recorded call id.
        for (Map<String, Object> region : regions) {
            result.regionCatalog.add(deepCopy(region));
        }
        finalizeProducerGoals(result.regionPlans, regionById, refinedFlow,
                trace, loopBound);
        publishOutputAlternativeGaps(result);
        publishClosureDropGaps(result);
        declareSharedCarriers(result.regionPlans, regionById, trace);
        // Last, because it is stated over the locations the step above
        // enumerated: a location nothing demands is versioned by nothing, so
        // there is no relation for a touch of it to be missing from.
        auditSharedLocationTouches(result, trace, unplannedSeeds);
        return result;
    }

    /**
     * Declares the shared locations each planned activation must select.
     *
     * <p>A candidate writer edge says the run made this writer possible for
     * this read and that nothing has decided between the candidates.  What
     * decides is the session's own read-from answer, and the session answers
     * only about a location a task selected: an unselected field publishes no
     * versions, so its read resolves to nothing and every candidate stays a
     * candidate under its gap.  This step closes that circle, and it is why
     * both ends of the edge declare the carrier - the reader is who asks the
     * question, but the versions it resolves against exist only because the
     * writers published them.</p>
     *
     * <p>Selection stays bounded because the demand does: the goal's own
     * bindings are the reads this activation is planned for, so a location
     * nothing demands is never versioned.</p>
     */
    private static void declareSharedCarriers(
            List<Map<String, Object>> plans,
            Map<String, Map<String, Object>> regionById,
            TraceIndex trace) {
        for (Map<String, Object> plan : plans) {
            Map<String, Object> region = regionById.get(
                    text(plan.get("regionId")));
            String occurrence = text(plan.get("occurrenceId"));
            if (region == null || occurrence.isEmpty()) continue;
            for (Map<String, Object> goal : rows(plan.get("closureGoals"))) {
                List<Map<String, Object>> carriers = declaredSharedCarriers(
                        rows(goal.get("edgeBindings")), region, occurrence);
                carriers = mergeSharedCarriers(carriers,
                        demandedSharedCarriers(plan, region, occurrence));
                carriers = mergeSharedCarriers(carriers,
                        handoffProducerCarriers(plan, goal, regionById,
                                trace));
                if (!carriers.isEmpty()) {
                    goal.put(ExecutionTask.SHARED_CARRIERS, carriers);
                }
            }
        }
    }

    /**
     * Shared values read on the concrete path that produced a selected
     * communication leaf.
     *
     * <p>A communication output has no Java input port of its own: the live
     * expression may have been computed several calls below the occurrence
     * entry.  Replaying the entry without selecting the shared fields that
     * exact call tree read leaves the VM nothing symbolic to export.  The
     * selection here is deliberately the intersection of two existing
     * authorities: a field must be in the failure-selected region catalog
     * and it must have been read below this replay entry before this output's
     * recorded send event.  It neither scans the heap nor admits an
     * application-wide field merely because its declaration has the same
     * name.</p>
     */
    private static List<Map<String, Object>> handoffProducerCarriers(
            Map<String, Object> plan, Map<String, Object> goal,
            Map<String, Map<String, Object>> regionById,
            TraceIndex trace) {
        if (trace == null || plan == null || goal == null) {
            return Collections.emptyList();
        }
        Map<String, Object> replay = row(goal.get(ExecutionTask.REPLAY_ENTRY));
        String replayMethod = text(replay.get("method"));
        String receiverClass = text(replay.get("receiverClass"));
        long rootCall = traceEvidenceRootCall(plan);
        if (rootCall <= 0L || replayMethod.isEmpty()
                || receiverClass.isEmpty()) {
            return Collections.emptyList();
        }

        Set<Long> boundaries = new LinkedHashSet<>();
        Map<String, Object> closure = row(goal.get(
                OutputClosureContract.FIELD));
        for (Map<String, Object> member : rows(closure.get("members"))) {
            Map<String, Object> slice = row(member.get("slice"));
            boolean handoff = false;
            for (Map<String, Object> capture
                    : rows(slice.get("captureBindings"))) {
                if (OutputCaptureSpec.HANDOFF_BOUND_LEAF.equals(
                        text(capture.get("captureKind")))) {
                    handoff = true;
                    break;
                }
            }
            long boundary = longNumber(slice.get(
                    "selectedRuntimeEventSeq"), -1L);
            if (handoff && boundary >= 0L) boundaries.add(boundary);
        }
        if (boundaries.isEmpty()) return Collections.emptyList();

        Map<String, FieldPathSpec.DeclaredField> selected =
                selectedSharedFieldDeclarations(regionById.values());
        if (selected.isEmpty()) return Collections.emptyList();

        Map<String, Map<String, Object>> carriers = new LinkedHashMap<>();
        for (Long boundary : boundaries) {
            for (FieldAccessEvent access : trace.fieldsThroughReplayEntry(
                    rootCall, replayMethod, receiverClass, boundary)) {
                FieldPathSpec.DeclaredField field = selected.get(access.field);
                if (field == null) continue;
                String descriptor = JavaPrimitiveSmtSemantics
                        .javaTypeDescriptor(field.type());
                if (descriptor.isEmpty()) continue;
                String location = RecordedReadFrom.fieldKey(field.owner(),
                        field.name());
                Map<String, Object> carrier = object(
                        "kind", mapCarrierType(field.type())
                                ? SharedStateEvidence.LOCATION_KIND_MAP_STATE
                                : "DECLARED_FIELD",
                        "declaringClass", field.owner(),
                        "fieldName", field.name(),
                        "descriptor", descriptor,
                        "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                        "fieldPath", Collections.emptyList());
                carriers.putIfAbsent(location, carrier);
            }
        }
        carriers.remove("");
        return new ArrayList<>(carriers.values());
    }

    /** Failure-selected declared fields available to exact replay corridors. */
    private static Map<String, FieldPathSpec.DeclaredField>
    selectedSharedFieldDeclarations(
            Collection<Map<String, Object>> regions) {
        Map<String, FieldPathSpec.DeclaredField> selected =
                new LinkedHashMap<>();
        for (Map<String, Object> region : regions) {
            List<Map<String, Object>> ports = new ArrayList<>();
            ports.addAll(rows(region.get("symbolicInputs")));
            ports.addAll(rows(region.get("outputs")));
            for (Map<String, Object> port : ports) {
                if (!DependencyRole.valueFrontier(
                        port.get("dependencyRole"))) {
                    continue;
                }
                List<String> declarations = strings(
                        port.get("fieldPathDeclarations"));
                if (declarations.isEmpty()) continue;
                String signature = declarations.get(
                        declarations.size() - 1);
                FieldPathSpec.DeclaredField field =
                        FieldPathSpec.declaredField(signature);
                if (field != null) selected.putIfAbsent(signature, field);
            }
        }
        return selected;
    }

    /**
     * Existing shared-location admission applied to this exact production
     * occurrence.  Unlike ordinary carrier discovery it does not require a
     * selected read-from binding: this replay is being run to materialize a
     * possible later writer, so no such binding may be claimed yet.
     */
    private static List<Map<String, Object>> demandedSharedCarriers(
            Map<String, Object> plan, Map<String, Object> region,
            String occurrence) {
        if (!SHARED_LOCATION_DEMAND_ADMISSION.equals(
                text(plan.get(ADMISSION_BASIS)))) {
            return Collections.emptyList();
        }
        Set<String> demanded = new LinkedHashSet<>(strings(
                plan.get(DEMANDED_SHARED_LOCATIONS)));
        if (demanded.isEmpty()) return Collections.emptyList();

        List<Map<String, Object>> ports = new ArrayList<>();
        ports.addAll(rows(region.get("symbolicInputs")));
        ports.addAll(rows(region.get("outputs")));
        Map<String, Map<String, Object>> carriers = new LinkedHashMap<>();
        for (Map<String, Object> port : ports) {
            String portOccurrence = text(port.get("occurrenceId"));
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
            if (!demanded.contains(location)
                    || carriers.containsKey(location)) {
                continue;
            }
            String descriptor = JavaPrimitiveSmtSemantics
                    .javaTypeDescriptor(field.type());
            if (descriptor.isEmpty()) continue;
            String sourceKind = text(port.get("sourceKind"));
            Map<String, Object> carrier = object(
                    "kind", mapCarrierType(field.type())
                            ? SharedStateEvidence.LOCATION_KIND_MAP_STATE
                            : "DECLARED_FIELD",
                    "declaringClass", field.owner(),
                    "fieldName", field.name(),
                    "descriptor", descriptor,
                    // Reuses the exact access-owner binding the input/output
                    // port already carries.  The runtime resolves this only
                    // when that declared field is accessed in the admitted
                    // occurrence; it never searches the heap for a same-named
                    // owner.
                    "sourceKind", sourceKind);
            if ("ACTIVATION_FIELD_RECEIVER".equals(sourceKind)) {
                carrier.put("fieldPath", Collections.emptyList());
            } else {
                List<String> path = carrierPath(field,
                        Collections.singletonList(port));
                if (path.isEmpty()) continue;
                carrier.put("fieldPath", path);
            }
            carriers.put(location, carrier);
        }
        return new ArrayList<>(carriers.values());
    }

    private static boolean mapCarrierType(String javaType) {
        String type = text(javaType);
        return "java.util.Map".equals(type)
                || "java.util.HashMap".equals(type)
                || "java.util.LinkedHashMap".equals(type);
    }

    private static List<Map<String, Object>> mergeSharedCarriers(
            Collection<Map<String, Object>> left,
            Collection<Map<String, Object>> right) {
        Map<String, Map<String, Object>> byLocation = new LinkedHashMap<>();
        for (Map<String, Object> carrier : left) {
            byLocation.put(RecordedReadFrom.fieldKey(
                    text(carrier.get("declaringClass")),
                    text(carrier.get("fieldName"))), carrier);
        }
        for (Map<String, Object> carrier : right) {
            byLocation.putIfAbsent(RecordedReadFrom.fieldKey(
                    text(carrier.get("declaringClass")),
                    text(carrier.get("fieldName"))), carrier);
        }
        byLocation.remove("");
        return new ArrayList<>(byLocation.values());
    }

    /** One activation seed this stage was handed and did not plan. */
    private static final class UnplannedSeed {
        private final String reason;
        private final String activationId;
        private final String regionId;
        private final String occurrenceId;
        private final String rootMethod;
        private final long rootCallId;

        private UnplannedSeed(Map<String, Object> seed, String reason,
                              String occurrenceId) {
            this.reason = reason;
            this.activationId = text(seed.get("activationId"));
            this.regionId = text(seed.get("regionId"));
            this.occurrenceId = occurrenceId;
            this.rootMethod = text(seed.get("rootMethod"));
            this.rootCallId = longNumber(seed.get("rootCallId"), -1L);
        }
    }

    /** One recorded read or write of one selected shared location. */
    private static final class SharedLocationTouch {
        private final String location;
        private final String declaringClass;
        private final String fieldName;
        private final boolean write;
        private final List<FieldAccessEvent> events = new ArrayList<>();

        private SharedLocationTouch(String location, String declaringClass,
                                    String fieldName, boolean write) {
            this.location = location;
            this.declaringClass = declaringClass;
            this.fieldName = fieldName;
            this.write = write;
        }

        private String touchKind() {
            return write ? "WRITE" : "READ";
        }
    }

    /**
     * Names every recorded touch of a selected shared location that this
     * stage modelled with nothing, and counts what it did model.
     *
     * <p>The location set is exactly the one {@link #declareSharedCarriers}
     * enumerated one step earlier - the locations a planned goal declares it
     * must select - because those are the only locations the session ever
     * versions.  A field nothing demands publishes no versions, so a touch of
     * it is not a missing arm and is not counted as one.</p>
     *
     * <p>A touch belongs to the innermost planned activation whose root frame
     * is on its own <em>recorded caller chain</em>.  That chain is the
     * recorded {@code parentCallId} relation and nothing else: README section
     * 1 forbids resolving this by call order, by equal payloads or by span
     * ancestry, and none of the three is read here.  A touch with no planned
     * root on its chain is what vanished, and it is what this publishes.</p>
     *
     * <p>The census row is emitted whether or not anything was lost.  Losses
     * published only when they exist leave one silence meaning both "nothing
     * was lost" and "no location was ever enumerated", and the second is
     * precisely the failure that ends in {@code rf_unknown}.</p>
     */
    private static void auditSharedLocationTouches(
            Result result, TraceIndex trace,
            List<UnplannedSeed> unplannedSeeds) {
        // The enumerated locations, and the goals that demand each of them.
        // Demanding plans are held by index, never by row equality: two plan
        // rows of one activation differ only in fields a deep comparison
        // would still call distinct, and a set keyed on the row itself would
        // pay a full map compare per carrier for the privilege.
        Map<String, List<Map<String, Object>>> goalsByLocation =
                new LinkedHashMap<>();
        Map<String, Set<Integer>> planIndicesByLocation =
                new LinkedHashMap<>();
        for (int index = 0; index < result.regionPlans.size(); index++) {
            Map<String, Object> plan = result.regionPlans.get(index);
            for (Map<String, Object> goal : rows(plan.get("closureGoals"))) {
                for (Map<String, Object> carrier
                        : rows(goal.get(ExecutionTask.SHARED_CARRIERS))) {
                    String location = RecordedReadFrom.fieldKey(
                            text(carrier.get("declaringClass")),
                            text(carrier.get("fieldName")));
                    if (location.isEmpty()) continue;
                    goalsByLocation.computeIfAbsent(location,
                            ignored -> new ArrayList<>()).add(goal);
                    planIndicesByLocation.computeIfAbsent(location,
                            ignored -> new LinkedHashSet<>())
                            .add(Integer.valueOf(index));
                }
            }
        }
        Map<String, List<Map<String, Object>>> plansByLocation =
                new LinkedHashMap<>();
        for (Map.Entry<String, Set<Integer>> entry
                : planIndicesByLocation.entrySet()) {
            List<Map<String, Object>> owners = new ArrayList<>();
            for (Integer index : entry.getValue()) {
                owners.add(result.regionPlans.get(index.intValue()));
            }
            plansByLocation.put(entry.getKey(), owners);
        }
        // Planned activations, addressed by the root call each one names.
        Map<Long, Map<String, Object>> plannedByRootCall =
                new LinkedHashMap<>();
        for (Map<String, Object> activation : result.runtimeInstances) {
            long rootCallId = longNumber(activation.get("rootCallId"), -1L);
            if (rootCallId > 0L) {
                plannedByRootCall.put(rootCallId, activation);
            }
        }
        Map<Long, UnplannedSeed> unplannedByRootCall = new LinkedHashMap<>();
        for (UnplannedSeed seed : unplannedSeeds) {
            if (seed.rootCallId > 0L) {
                unplannedByRootCall.putIfAbsent(seed.rootCallId, seed);
            }
        }

        int recordedTouches = 0;
        // Touches a planned activation holds, keyed by that activation's root
        // call and the location, so one link row states one relation.
        Map<String, SharedLocationTouch> regioned = new LinkedHashMap<>();
        Map<String, Long> regionedRootCall = new LinkedHashMap<>();
        // Touches nothing holds, keyed by the root frame this stage could
        // resolve for them and the location.
        Map<String, SharedLocationTouch> unregioned = new LinkedHashMap<>();
        Map<String, MethodEvent> unregionedRoot = new LinkedHashMap<>();
        Map<String, UnplannedSeed> unregionedSeed = new LinkedHashMap<>();
        // One regex per distinct recorded field signature rather than one per
        // recorded access: a production trace holds millions of the second
        // and a handful of the first.
        Map<String, String> locationBySignature = new LinkedHashMap<>();
        for (FieldAccessEvent event : goalsByLocation.isEmpty()
                ? Collections.<FieldAccessEvent>emptyList() : trace.fields) {
            final boolean write = "FIELD_WRITE".equals(event.kind);
            if (!write && !"FIELD_READ".equals(event.kind)) continue;
            String resolved = locationBySignature.get(event.field);
            if (resolved == null) {
                FieldPathSpec.DeclaredField parsed =
                        FieldPathSpec.declaredField(event.field);
                resolved = parsed == null ? "" : RecordedReadFrom.fieldKey(
                        parsed.owner(), parsed.name());
                locationBySignature.put(event.field, resolved);
            }
            final String location = resolved;
            if (location.isEmpty()
                    || !goalsByLocation.containsKey(location)) {
                continue;
            }
            final FieldPathSpec.DeclaredField declared =
                    FieldPathSpec.declaredField(event.field);
            recordedTouches++;
            long plannedRoot = -1L;
            UnplannedSeed seed = null;
            MethodEvent outermost = null;
            for (Long call : trace.enclosingCalls(event.callId)) {
                MethodEvent frame = trace.methodByCall.get(call);
                if (frame != null) outermost = frame;
                if (plannedRoot < 0L && seed == null) {
                    if (plannedByRootCall.containsKey(call)) {
                        plannedRoot = call.longValue();
                    } else if (unplannedByRootCall.containsKey(call)) {
                        seed = unplannedByRootCall.get(call);
                    }
                }
            }
            if (plannedRoot > 0L) {
                String key = plannedRoot + "\n" + location + "\n"
                        + (write ? "W" : "R");
                regioned.computeIfAbsent(key, ignored ->
                        new SharedLocationTouch(location, declared.owner(),
                                declared.name(), write)).events.add(event);
                regionedRootCall.put(key, Long.valueOf(plannedRoot));
                continue;
            }
            String rootKey = seed != null ? "SEED:" + seed.rootCallId
                    : outermost != null ? "FRAME:" + outermost.callId
                    : "FRAME:none";
            String key = rootKey + "\n" + location + "\n"
                    + (write ? "W" : "R");
            unregioned.computeIfAbsent(key, ignored ->
                    new SharedLocationTouch(location, declared.owner(),
                            declared.name(), write)).events.add(event);
            if (seed != null) {
                unregionedSeed.put(key, seed);
            } else if (outermost != null) {
                unregionedRoot.put(key, outermost);
            }
        }

        int unregionedTouchCount = 0;
        Map<String, Integer> unregionedByLocation = new LinkedHashMap<>();
        for (Map.Entry<String, SharedLocationTouch> entry
                : unregioned.entrySet()) {
            SharedLocationTouch touch = entry.getValue();
            UnplannedSeed seed = unregionedSeed.get(entry.getKey());
            MethodEvent root = unregionedRoot.get(entry.getKey());
            unregionedTouchCount += touch.events.size();
            unregionedByLocation.merge(touch.location,
                    Integer.valueOf(touch.events.size()), Integer::sum);
            result.gaps.add(unregionedTouchGap(touch, seed, root,
                    plansByLocation.get(touch.location)));
        }
        // What survived, stated on the goals whose read-from choice it is
        // about.  A goal whose location lost nothing says so too, because
        // "closed" and "never asked" are different answers.
        for (Map.Entry<String, List<Map<String, Object>>> entry
                : goalsByLocation.entrySet()) {
            int lost = unregionedByLocation.getOrDefault(entry.getKey(),
                    Integer.valueOf(0)).intValue();
            for (Map<String, Object> goal : entry.getValue()) {
                boolean closed = lost == 0
                        && !Boolean.FALSE.equals(goal.get(
                        SHARED_LOCATION_UNIVERSE_CLOSED));
                goal.put(SHARED_LOCATION_UNIVERSE_CLOSED,
                        Boolean.valueOf(closed));
                if (lost > 0) {
                    goal.put(UNREGIONED_TOUCH_COUNT, Integer.valueOf(
                            integer(goal.get(UNREGIONED_TOUCH_COUNT), 0)
                                    + lost));
                }
            }
        }
        // One planned activation touching a location another planned
        // activation's read-from choice is stated over.  This is the link an
        // activation admitted by a shared-location demand needs: it never
        // reaches the target, so no target-reach closure names it, and
        // without this row nothing states that it belongs to the writer
        // universe at all.  Which arm a read resolves to stays the model's
        // exactlyOne choice; this only says the arm exists.
        for (Map.Entry<String, SharedLocationTouch> entry
                : regioned.entrySet()) {
            SharedLocationTouch touch = entry.getValue();
            Map<String, Object> owner = plannedByRootCall.get(
                    regionedRootCall.get(entry.getKey()));
            if (owner == null) continue;
            for (Map<String, Object> demanding
                    : plansByLocation.getOrDefault(touch.location,
                    Collections.<Map<String, Object>>emptyList())) {
                if (text(demanding.get("occurrenceId")).equals(
                        text(owner.get("occurrenceId")))) {
                    continue;
                }
                result.occurrenceLinks.add(sharedLocationTouchLink(owner,
                        demanding, touch));
            }
        }
        result.gaps.add(sharedLocationCensus(goalsByLocation.keySet(),
                recordedTouches, unregionedTouchCount, unregioned.size()));
    }

    /** One named, counted loss of a recorded shared-location touch. */
    private static Map<String, Object> unregionedTouchGap(
            SharedLocationTouch touch, UnplannedSeed seed, MethodEvent root,
            List<Map<String, Object>> demanding) {
        FieldAccessEvent first = touch.events.get(0);
        String siteId = first.siteId;
        for (FieldAccessEvent event : touch.events) {
            if (!siteId.equals(event.siteId)) {
                siteId = "";
                break;
            }
        }
        String activationId = seed != null ? seed.activationId
                : root != null ? activationId(root) : "";
        Map<String, Object> gap = gap(
                GAP_SHARED_LOCATION_TOUCH_UNREGIONED,
                seed != null ? seed.reason : TOUCH_ACTIVATION_UNPLANNED,
                activationId, first.method, siteId,
                touch.touchKind() + " " + touch.location + " x"
                        + touch.events.size());
        gap.put("authority", SHARED_LOCATION_TOUCH_AUTHORITY);
        gap.put(TOUCH_ACTIVATION_AUTHORITY, seed != null
                ? TOUCH_ROOT_FROM_SEED : TOUCH_ROOT_FROM_RECORDED_CHAIN);
        // Each identity class in its own field, never standing in for
        // another.
        gap.put("sourceKey", seed != null ? "" : root != null
                ? root.sourceKey : "");
        gap.put("occurrenceAttribution", "NO_PLANNED_REGION_OCCURRENCE");
        gap.put("rootMethod", seed != null ? seed.rootMethod
                : root != null ? root.method : "");
        gap.put("rootCallId", Long.valueOf(seed != null ? seed.rootCallId
                : root != null ? root.callId : -1L));
        gap.put("thread", root != null ? root.threadName : "");
        gap.put("threadId", Long.valueOf(root != null ? root.tid : -1L));
        if (seed != null) {
            gap.put("regionId", seed.regionId);
            if (!seed.occurrenceId.isEmpty()) {
                gap.put("occurrenceId", seed.occurrenceId);
            }
        }
        gap.put("sharedLocation", touch.location);
        gap.put("declaringClass", touch.declaringClass);
        gap.put("fieldName", touch.fieldName);
        gap.put("touchKind", touch.touchKind());
        gap.put("touchCount", Integer.valueOf(touch.events.size()));
        List<String> consumers = new ArrayList<>();
        for (Map<String, Object> plan : demanding == null
                ? Collections.<Map<String, Object>>emptyList() : demanding) {
            String occurrence = text(plan.get("occurrenceId"));
            if (!occurrence.isEmpty() && !consumers.contains(occurrence)) {
                consumers.add(occurrence);
            }
        }
        // Indexed by the activations whose read-from choice loses an arm to
        // this, so a consumer of the model can join the loss to the formula
        // it belongs to without re-deriving the location.
        gap.put("demandingOccurrenceIds", consumers);
        // The recorded rows that establish the touch.  Complete, never a
        // sample: a truncated evidence list is the same defect one level
        // down.
        List<Map<String, Object>> evidence = new ArrayList<>();
        for (FieldAccessEvent event : touch.events) {
            evidence.add(object("seq", Long.valueOf(event.seq),
                    "kind", event.kind,
                    "method", event.method,
                    "siteId", event.siteId,
                    "callId", Long.valueOf(event.callId),
                    "receiverObjectId",
                    Integer.valueOf(event.receiverObjectId)));
        }
        gap.put("evidence", evidence);
        return gap;
    }

    /** The link one recorded shared-location touch states between two plans. */
    private static Map<String, Object> sharedLocationTouchLink(
            Map<String, Object> owner, Map<String, Object> demanding,
            SharedLocationTouch touch) {
        Map<String, Object> link = new LinkedHashMap<>();
        link.put("schemaVersion", 3);
        link.put("kind", "RUNTIME_OCCURRENCE_LINK");
        link.put("linkKind", SHARED_LOCATION_TOUCH_LINK);
        link.put("fromActivationId", text(owner.get("activationId")));
        link.put("fromRegionId", text(owner.get("regionId")));
        link.put("fromOccurrenceId", text(owner.get("occurrenceId")));
        link.put("fromRootCallId", owner.get("rootCallId"));
        // README section 2's activationId, taken from the only field of a
        // plan row that holds one.  The row's own "activationId" member is
        // present only on a fragment of a cut, so reading it here would give
        // a communication-free consumer an empty end.
        link.put("toActivationId", text(row(demanding.get("traceEvidence"))
                .get("activationId")));
        link.put("toRegionId", text(demanding.get("regionId")));
        link.put("toOccurrenceId", text(demanding.get("occurrenceId")));
        link.put("sharedLocation", touch.location);
        link.put("touchKind", touch.touchKind());
        link.put("touchCount", Integer.valueOf(touch.events.size()));
        List<Long> seqs = new ArrayList<>();
        for (FieldAccessEvent event : touch.events) {
            seqs.add(Long.valueOf(event.seq));
        }
        link.put("evidenceSeqs", seqs);
        link.put("authority", SHARED_LOCATION_TOUCH_AUTHORITY);
        return link;
    }

    /** What the shared-location audit examined, whatever it found. */
    private static Map<String, Object> sharedLocationCensus(
            Collection<String> locations, int recordedTouches,
            int unregionedTouches, int unregionedActivations) {
        Map<String, Object> census = gap(
                SHARED_LOCATION_TOUCH_CENSUS,
                "SELECTED_SHARED_LOCATION_TOUCH_AUDIT", "", "", "",
                "locations=" + locations.size()
                        + " touches=" + recordedTouches
                        + " unregioned=" + unregionedTouches);
        census.put("authority", SHARED_LOCATION_TOUCH_AUTHORITY);
        census.put("selectedLocationCount",
                Integer.valueOf(locations.size()));
        census.put("selectedLocations", new ArrayList<>(locations));
        census.put("recordedTouchCount", Integer.valueOf(recordedTouches));
        census.put("regionedTouchCount",
                Integer.valueOf(recordedTouches - unregionedTouches));
        census.put("unregionedTouchCount",
                Integer.valueOf(unregionedTouches));
        census.put("unregionedActivationCount",
                Integer.valueOf(unregionedActivations));
        return census;
    }

    /**
     * {@code K_L} this plan's relations are closed under.
     *
     * <p>Derived exactly the way {@link
     * LoopBoundPolicy#maxBackedgeTraversals()} derives the executor's own
     * limit - the largest bound the campaign and this plan's own occurrence
     * state between them - so it can never be below a bound the
     * model holds.  A campaign that declared nothing passes {@code null},
     * which states that this run bounded no loop; the inherited bound then
     * applies and every row of such a run is what it was before.</p>
     */
    private static int loopBodyBound(Map<String, Object> plan,
                                     LoopBoundPolicy loopBound) {
        int campaign = loopBound == null
                ? LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS
                : loopBound.maxBackedgeTraversals();
        int declared = LoopBoundPolicy.bodyBound(plan == null ? null
                : plan.get(LoopBoundPolicy.LOOP_BODY_BOUND));
        return Math.max(campaign, declared);
    }

    /** Records the demanded output epochs one plan's bound left unmodelled. */
    private static void recordOutputAlternativeLoss(
            Map<String, Object> plan, Map<String, Integer> unmodelled,
            int loopBodyBound) {
        if (unmodelled == null || unmodelled.isEmpty()) return;
        List<Map<String, Object>> rows = new ArrayList<>();
        for (Map.Entry<String, Integer> entry : unmodelled.entrySet()) {
            rows.add(object("outputPort", entry.getKey(),
                    "unmodelledOccurrenceCount", entry.getValue(),
                    "loopBodyBound", Integer.valueOf(loopBodyBound)));
        }
        plan.put(UNMODELLED_OUTPUT_ALTERNATIVES, rows);
    }

    /**
     * Publishes the losses {@link #recordOutputAlternativeLoss} recorded.
     *
     * <p>Separate from the recording because the goal pass runs on a pool:
     * a row written straight into the shared gap ledger from several plans
     * at once would be a data race, and one written per plan would report
     * the same loss under whichever order the pool happened to finish in.</p>
     */
    private static void publishOutputAlternativeGaps(Result result) {
        for (Map<String, Object> plan : result.regionPlans) {
            for (Map<String, Object> lost
                    : rows(plan.get(UNMODELLED_OUTPUT_ALTERNATIVES))) {
                Map<String, Object> gap = gap(
                        GAP_OUTPUT_ALTERNATIVE_UNMODELLED,
                        OUTPUT_ALTERNATIVE_REASON,
                        text(row(plan.get("traceEvidence"))
                                .get("activationId")),
                        text(plan.get("targetMethod")),
                        text(lost.get("outputPort")),
                        "unmodelled=" + text(lost.get(
                                "unmodelledOccurrenceCount"))
                                + " bound=" + text(lost.get(
                                        "loopBodyBound")));
                gap.put("authority", OUTPUT_ALTERNATIVE_AUTHORITY);
                gap.put("occurrenceId", text(plan.get("occurrenceId")));
                gap.put("regionId", text(plan.get("regionId")));
                gap.put("outputPort", lost.get("outputPort"));
                gap.put("unmodelledOccurrenceCount",
                        lost.get("unmodelledOccurrenceCount"));
                gap.put("loopBodyBound", lost.get("loopBodyBound"));
                result.gaps.add(gap);
            }
        }
    }

    /**
     * Publishes the dependencies an admitted output closure dropped.
     *
     * <p>Same shape as {@link #publishOutputAlternativeGaps}: the goal pass
     * runs on a pool, so each goal records its own drops and one later pass
     * turns them into gap rows in plan order.</p>
     */
    private static void publishClosureDropGaps(Result result) {
        for (Map<String, Object> plan : result.regionPlans) {
            for (Map<String, Object> goal : rows(plan.get("closureGoals"))) {
                List<String> dropped = new ArrayList<>(
                        strings(goal.get(ADMITTED_CLOSURE_DROPS)));
                // An endpoint the admitted closure left out is the same kind
                // of loss.  A refused goal already carries its blockers in
                // its own admission, so only an admitted one is named here.
                if ("READY".equals(text(row(goal.get("admission"))
                        .get("state")))) {
                    dropped.addAll(strings(
                            goal.get("excludedOutputBlockers")));
                }
                for (String reason : dropped) {
                    Map<String, Object> row = gap(
                            GAP_OUTPUT_CLOSURE_INPUT_DROPPED, reason,
                            text(row(plan.get("traceEvidence"))
                                    .get("activationId")),
                            text(plan.get("targetMethod")), "",
                            text(goal.get("goalId")));
                    row.put("occurrenceId", text(plan.get("occurrenceId")));
                    row.put("regionId", text(plan.get("regionId")));
                    result.gaps.add(row);
                }
            }
        }
    }

    /**
     * One carrier declaration per declared field this goal still carries
     * undecided candidate writers for.
     *
     * <p>Nothing is configured and nothing is searched for.  The location is
     * the field the candidate edge already names, under the same
     * {@code owner#name} address the recorded index will resolve it by, and
     * its descriptor comes from the same declaration.  A field the edge and
     * its leaf declaration do not agree on is skipped rather than
     * reconciled.</p>
     */
    private static List<Map<String, Object>> declaredSharedCarriers(
            List<Map<String, Object>> bindings, Map<String, Object> region,
            String occurrence) {
        List<Map<String, Object>> receiverPorts = receiverRootedPorts(
                bindings, region, occurrence);
        Map<String, Map<String, Object>> byField = new LinkedHashMap<>();
        for (Map<String, Object> binding : bindings) {
            if (!RecordedReadFrom.PROVENANCE_CANDIDATE.equals(text(
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
            if (field.isEmpty() || byField.containsKey(field)
                    || !field.equals(text(binding.get(
                    RecordedReadFrom.EDGE_FIELD)))) {
                continue;
            }
            List<String> path = carrierPath(carrier, receiverPorts);
            String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                    carrier.type());
            if (path.isEmpty() || descriptor.isEmpty()) continue;
            byField.put(field, object(
                    "kind", "DECLARED_FIELD",
                    "declaringClass", carrier.owner(),
                    "fieldName", carrier.name(),
                    "descriptor", descriptor,
                    "fieldPath", path));
        }
        return new ArrayList<>(byField.values());
    }

    /**
     * The receiver-rooted path to the object that declares {@code carrier}.
     *
     * <p>Two shapes reach it, and both are already recorded on a port of this
     * activation: a path that ends at the field itself, and a path that ends
     * at an object of the declaring class, which the field name extends by
     * one step.  Where the ports disagree about which object the field is
     * on, this answers nothing: two paths are two locations, and versioning
     * the wrong one records provenance for a field the target never read.</p>
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

    /**
     * Ports this goal's bindings name for this activation whose field path
     * the replay walks from the region receiver.
     */
    private static List<Map<String, Object>> receiverRootedPorts(
            List<Map<String, Object>> bindings, Map<String, Object> region,
            String occurrence) {
        List<Map<String, Object>> inputs = rows(region.get("symbolicInputs"));
        List<Map<String, Object>> outputs = rows(region.get("outputs"));
        Map<String, Map<String, Object>> inputByPort =
                uniquePorts(inputs, occurrence, true);
        Map<String, Map<String, Object>> outputByPort =
                uniquePorts(outputs, occurrence, false);
        List<Map<String, Object>> result = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        for (Map<String, Object> binding : bindings) {
            if (occurrence.equals(text(binding.get("toOccurrenceId")))) {
                addReceiverRootedPort(result, seen, inputByPort.get(
                        text(binding.get("toInputPort"))));
            }
            if (occurrence.equals(text(binding.get("fromOccurrenceId")))) {
                addReceiverRootedPort(result, seen, outputByPort.get(
                        text(binding.get("fromOutputPort"))));
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
                    : boundToOutput(port, occurrenceId))) {
                continue;
            }
            String portId = text(port.get("portId"));
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
        // from.  A path rooted anywhere else - a parameter, an observed field
        // receiver - is walked from an object the carrier request never
        // holds, so it addresses a different location or none at all.
        if (port == null || !"RECEIVER".equals(text(port.get("rootKind")))
                || !seen.add(text(port.get("portId")))) {
            return;
        }
        result.add(port);
    }

    private static boolean endpointOf(Map<String, Object> binding,
                                      String occurrence) {
        return occurrence.equals(text(binding.get("fromOccurrenceId")))
                || occurrence.equals(text(binding.get("toOccurrenceId")));
    }

    /**
     * The refined protocol row as the composition gate reads it, before the
     * port ids the planner is about to mint exist.  Only the two endpoint
     * ports are stood in for; every fact the gate actually tests is the
     * row's own.
     */
    private static JsonObject candidateExchangeRow(
            Map<String, Object> edge, String fromOccurrence,
            String toOccurrence) {
        Map<String, Object> row = new LinkedHashMap<>(edge);
        row.put("fromOccurrenceId", fromOccurrence);
        row.put("toOccurrenceId", toOccurrence);
        row.put("fromOutputPort", text(edge.get("fromPort")));
        row.put("toInputPort", text(edge.get("toPort")));
        return toJsonTreeFast(row).getAsJsonObject();
    }

    private static void appendGoalBinding(
            Map<String, Object> goal, Map<String, Object> binding) {
        List<Map<String, Object>> bindings = rows(goal.get("edgeBindings"));
        String edgeId = text(binding.get("edgeId"));
        for (Map<String, Object> prior : bindings) {
            if (!edgeId.isEmpty()
                    && edgeId.equals(text(prior.get("edgeId")))
                    && text(binding.get("fromOccurrenceId")).equals(
                    text(prior.get("fromOccurrenceId")))
                    && text(binding.get("toOccurrenceId")).equals(
                    text(prior.get("toOccurrenceId")))) {
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
            RefinedFlowIndex refinedFlow, TraceIndex trace,
            LoopBoundPolicy loopBound) {
        int configured = Integer.getInteger(
                "causynth.aggregate.threads", 0);
        int threads = configured > 0 ? Math.min(configured, 32)
                : Math.max(1, Math.min(8,
                Runtime.getRuntime().availableProcessors() - 2));
        if (threads <= 1 || plans.size() <= 1) {
            for (Map<String, Object> plan : plans) {
                finalizeProducerGoalsForPlan(plan, regionById, refinedFlow,
                        trace, loopBound);
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
                                refinedFlow, trace, loopBound)));
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
            RefinedFlowIndex refinedFlow, TraceIndex trace,
            LoopBoundPolicy loopBound) {
        int loopBodyBound = loopBodyBound(plan, loopBound);
        {
            List<Map<String, Object>> goals = rows(plan.get("closureGoals"));
            if (goals.size() != 1 || !"OUTPUT_RELATION_CLOSURE".equals(
                    text(goals.get(0).get("kind")))) {
                return;
            }
            Map<String, Object> base = goals.get(0);
            Map<String, Object> producerRegion = regionById.get(
                    text(plan.get("regionId")));
            String producerOccurrence = text(plan.get("occurrenceId"));
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
                        text(binding.get("fromOccurrenceId")));
                boolean incoming = producerOccurrence.equals(
                        text(binding.get("toOccurrenceId")));
                String output = outgoing
                        ? text(binding.get("fromOutputPort")) : "";
                if (outgoing && !output.isEmpty()) {
                    output = canonicalOutputPort.getOrDefault(output, output);
                    binding.put("fromOutputPort", output);
                    String endpoint = semanticOutputEndpoint(binding,
                            producerRegion, producerOccurrence);
                    // Missing endpoint metadata must not merge unrelated
                    // ports. The later closure construction will fail this
                    // unresolved endpoint closed.
                    if (endpoint.isEmpty()) endpoint = "UNRESOLVED:" + output;
                    byEndpoint.computeIfAbsent(endpoint,
                            ignored -> new ArrayList<>()).add(binding);
                    if (exactResponseDeliveryBinding(plan, binding,
                            producerRegion, producerOccurrence, output)) {
                        exactResponseDeliveryEndpoints.add(endpoint);
                    }
                }
                if (incoming && !outgoing) incomingBindings.add(binding);
            }
            // A server occurrence selected by one exact response delivery
            // states its relation on that response. Other heap writes in
            // the same handler activation are different relations merely
            // consumed elsewhere; merging them here makes replay satisfy
            // every side effect before it may deliver this response. The
            // response's own backward slice still retains any write that
            // actually constructs the returned value.
            if (!exactResponseDeliveryEndpoints.isEmpty()) {
                byEndpoint.keySet().retainAll(
                        exactResponseDeliveryEndpoints);
            }
            List<String> demandedEndpoints = new ArrayList<>(
                    byEndpoint.keySet());
            Collections.sort(demandedEndpoints);
            // Every demanded output occurrence this bound leaves unmodelled
            // is recorded on the plan here and published as a named row once
            // the parallel pass above has joined; a plan that silently
            // produced fewer epochs than the run has occurrences reads as a
            // complete history of the output and is not one.
            Map<String, Integer> unmodelledAlternatives =
                    new LinkedHashMap<>();
            List<Map<String, List<Map<String, Object>>>> alternatives =
                    demandedBindingAlternatives(demandedEndpoints,
                            byEndpoint, loopBodyBound,
                            unmodelledAlternatives);
            recordOutputAlternativeLoss(plan, unmodelledAlternatives,
                    loopBodyBound);
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
                String identity = text(plan.get("occurrenceId"))
                        + "\n" + demandedEndpoints + "\n" + alternative
                        + "\n" + bindingAlternativeIdentity(selected);
                goal.put("goalId", "GOAL.OUTPUT_RELATION."
                        + UUID.nameUUIDFromBytes(identity.getBytes(
                        StandardCharsets.UTF_8)));

                List<OutputClosureContract> members = new ArrayList<>();
                List<String> blockers = new ArrayList<>();
                List<String> admittedDrops = new ArrayList<>();
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
                    boolean handoffComponent = handoffBoundComponentPort(
                            producerRegion, output, producerOccurrence);
                    boolean cutArgument = crossesCommunicationCut(
                            producerRegion, output, producerOccurrence);
                    boolean symbolicCutArgument = cutArgument
                            && symbolicCutArgumentPort(producerRegion,
                            output, producerOccurrence);
                    boolean communicationEffect = communicationEffectOutput(
                            producerRegion, output, producerOccurrence);
                    OutputClosureContract closure;
                    if (handoffComponent) {
                        // A structured leaf has no argument or heap boundary
                        // of its own.  It closes only on the exact VM export
                        // named by its component declaration and this
                        // occurrence's protocol edge.
                        closure = handoffComponentOutputClosure(plan, goal,
                                producerRegion, output, outputBindings,
                                refinedFlow, trace, loopBodyBound,
                                heapBlockers);
                    } else if (cutArgument && !symbolicCutArgument) {
                        // A structured request object is a concrete carrier
                        // for the interaction, not one symbolic value.  Its
                        // selected component leaves, if any, are handled by
                        // the handoff-component branch above.  Backward
                        // slicing the whole parent object turns unrelated
                        // identity/configuration fields into solver roots and
                        // keeps their String/container expressions alive for
                        // the full service activation.
                        admittedDrops.add(
                                "CONCRETE_COMMUNICATION_CARRIER:" + output);
                        continue;
                    } else if (cutArgument) {
                        // The demanded output is the cut's own argument, so
                        // the relation is closed one frame before the
                        // transport instead of on a heap cell the transport
                        // owns. Communication ports are not heap outputs, so
                        // no whole-graph heap slice applies here.
                        closure = cutArgumentOutputClosure(plan, goal,
                                producerRegion, output, outputBindings,
                                refinedFlow, trace, loopBodyBound,
                                heapBlockers);
                    } else if (communicationEffect) {
                        // The return is an interaction site, not a symbolic
                        // whole-object value.  Its actual leaves cross only
                        // through the VM handoff broker.
                        closure = communicationEffectOutputClosure(plan, goal,
                                producerRegion, output, outputBindings,
                                refinedFlow, trace, loopBodyBound,
                                heapBlockers);
                    } else {
                        closure = directHeapOutputClosure(plan, goal,
                                producerRegion, output, outputBindings,
                                refinedFlow, trace, loopBodyBound,
                                heapBlockers);
                    }
                    if (closure == null) {
                        if (!heapBlockers.isEmpty()) {
                            blockers.addAll(heapBlockers);
                        } else if (handoffComponent || cutArgument
                                || communicationEffect) {
                            // Not "pending".  README section 3 sends this
                            // value across the cut through the VM broker, so
                            // it is not a heap output and no heap closure is
                            // on its way; saying "pending" would promise one.
                            // The demand is real and the refusal is final
                            // until a cut relation exists, which is exactly
                            // what OUTPUT_DEMAND_SET_EMPTY used to hide on a
                            // client region before its ports were named.
                            blockers.add("OUTPUT_CLOSURE_CROSSES_CUT:"
                                    + output);
                        } else {
                            blockers.add("OUTPUT_CLOSURE_PENDING:" + output);
                        }
                    } else {
                        // The closure succeeded, and a reason it recorded on
                        // the way is still a real loss: the relation it
                        // publishes no longer depends on what that reason
                        // named.  It is stated as a non-fatal gap instead of
                        // being discarded with the successful return.
                        admittedDrops.addAll(heapBlockers);
                        members.add(closure);
                        successfulOutgoingBindings.addAll(outputBindings);
                    }
                }
                if (!admittedDrops.isEmpty()) {
                    goal.put(ADMITTED_CLOSURE_DROPS, admittedDrops);
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
                    Set<String> causalEdges = new LinkedHashSet<>(
                            closure.executionScope().causalEdgeIds());
                    Set<String> exactProtocolInputs = new LinkedHashSet<>();
                    for (Map<String, Object> incoming : incomingBindings) {
                        if ("RUNTIME_PROTOCOL_FLOW".equals(
                                text(incoming.get("kind")))
                                && causalEdges.contains(
                                text(incoming.get("edgeId")))) {
                            exactProtocolInputs.add(
                                    text(incoming.get("toInputPort")));
                        }
                    }
                    List<Map<String, Object>> executableBindings =
                            new ArrayList<>();
                    for (Map<String, Object> incoming : incomingBindings) {
                        String input = text(incoming.get("toInputPort"));
                        boolean exactProtocol = "RUNTIME_PROTOCOL_FLOW".equals(
                                text(incoming.get("kind")))
                                && exactProtocolInputs.contains(input);
                        if (inputs.contains(input)
                                && (!exactProtocol || causalEdges.contains(
                                text(incoming.get("edgeId"))))) {
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
                completeSet.add(goal);
                alternative++;
            }
            assignOutputOccurrenceIdentity(completeSet);
            // A port can be written in several bounded phases of one coarse
            // occurrence.  Target-first discovery selects the exact dynamic
            // version by causal edge, so keep each version's own slice and
            // replay continuation instead of merging them by port id.
            plan.put("closureGoals", completeSet);
            bindSelectedEffectCausalAnchor(plan, completeSet);
        }
    }

    /**
     * Binds a producer occurrence to the unique named request scope carried
     * by its selected communication effect.
     *
     * <p>A worker root can begin before the request it serves is known.  The
     * exact selected send is then the first stable causal context available.
     * Only the application-declared API name is retained; session ids and
     * counted request ordinals remain provenance.</p>
     */
    private static void bindSelectedEffectCausalAnchor(
            Map<String, Object> plan, List<Map<String, Object>> goals) {
        if (plan == null
                || "COMMUNICATION_ENTRY".equals(
                text(plan.get("rootAuthority")))
                || !selectedEffectsBeginAtRoot(plan, goals)) {
            return;
        }
        Set<String> requestApis = new LinkedHashSet<>();
        for (Map<String, Object> goal : goals) {
            for (Map<String, Object> binding
                    : rows(goal.get("edgeBindings"))) {
                String requestApi = text(binding.get("requestApi"));
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

    /**
     * Whether every selected effect starts in the coarse occurrence root.
     *
     * <p>A request API is useful replay identity only when it is already the
     * root's entry context.  A continuation inside a long-lived service may
     * observe the request much later; copying that effect-local label onto the
     * root selector would reject or mis-select otherwise valid replays.</p>
     */
    private static boolean selectedEffectsBeginAtRoot(
            Map<String, Object> plan, List<Map<String, Object>> goals) {
        String rootMethod = text(row(plan.get("rootSelector")).get("method"));
        if (rootMethod.isEmpty()) return false;
        boolean sawMember = false;
        for (Map<String, Object> goal : goals) {
            Map<String, Object> closure = row(goal.get("outputClosure"));
            for (Map<String, Object> member : rows(closure.get("members"))) {
                sawMember = true;
                Map<String, Object> replayEntry = row(
                        row(member.get("slice")).get("replayEntry"));
                String replayMethod = text(replayEntry.get("method"));
                if (!replayMethod.isEmpty()
                        && !rootMethod.equals(replayMethod)) {
                    return false;
                }
            }
        }
        return sawMember;
    }

    /**
     * Whether this binding is the response delivery that scopes this exact
     * server plan.
     *
     * <p>Every component is required: a response-shaped port alone is only a
     * declaration, an exchange alone may name a sibling delivery, and an
     * activation occurrence alone may hold several cut sites. The
     * already-validated protocol binding supplies the recorded delivery; the
     * plan supplies the exchange and occurrence it is replaying.</p>
     */
    private static boolean exactResponseDeliveryBinding(
            Map<String, Object> plan, Map<String, Object> binding,
            Map<String, Object> region, String occurrenceId,
            String outputPort) {
        if (!"RUNTIME_PROTOCOL_FLOW".equals(text(binding.get("kind")))
                || !CommunicationCatalogContract.DIRECTION_RESPONSE.equals(
                text(binding.get("protocolDirection")))
                || !communicationEffectOutput(region, outputPort,
                occurrenceId)) {
            return false;
        }
        return occurrenceId.equals(text(binding.get("fromOccurrenceId")));
    }


    /**
     * Whether a demanded output is the request port of a declared cut.
     *
     * <p>Both halves are read, because either alone would be a guess.  The
     * port has to be one the communication contract declared for a cut, and
     * its capture has to be the cut's own {@code CALL_ARGUMENT} - the value
     * handed to the callee at the cut site.  A heap output of the same
     * fragment answers neither.</p>
     */
    private static boolean crossesCommunicationCut(Map<String, Object> region,
                                                   String outputPort,
                                                   String occurrenceId) {
        if (region == null) return false;
        Map<String, Object> port = uniquePort(rows(region.get("outputs")),
                outputPort, occurrenceId);
        return port != null
                && RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT
                .equals(text(port.get("sourceKind")))
                && CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT.equals(
                text(port.get(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND)));
    }

    /** True only for a cut leaf carrying its complete static declaration. */
    private static boolean handoffBoundComponentPort(
            Map<String, Object> region, String outputPort,
            String occurrenceId) {
        if (region == null) return false;
        Map<String, Object> port = uniquePort(rows(region.get("outputs")),
                outputPort, occurrenceId);
        return port != null
                && RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT
                .equals(text(port.get("sourceKind")))
                && !text(port.get(CommunicationCatalogContract.PORT_COMPONENT_OF)).isEmpty()
                && !text(port.get(CommunicationCatalogContract.PORT_ENCODING_AUTHORITY)).isEmpty();
    }

    /** Whether a demanded output is Resp_out at a server-entry return. */
    private static boolean communicationEffectOutput(
            Map<String, Object> region, String outputPort,
            String occurrenceId) {
        if (region == null) return false;
        Map<String, Object> port = uniquePort(rows(region.get("outputs")),
                outputPort, occurrenceId);
        return port != null
                && RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT
                .equals(text(port.get("sourceKind")))
                && CommunicationCatalogContract.CAPTURE_ENTRY_RETURN.equals(
                text(port.get(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND)));
    }


    /**
     * Identifies a semantic output endpoint independently of the runtime
     * port id. Repeated ports at this endpoint are bounded occurrences, while
     * different endpoint keys are members of one producer relation.
     */
    static String semanticOutputEndpoint(
            Map<String, Object> binding, Map<String, Object> region,
            String occurrenceId) {
        if (region == null) return "";
        String portId = text(binding.get("fromOutputPort"));
        Map<String, Object> port = uniquePort(rows(region.get("outputs")),
                portId, occurrenceId);
        if (port == null) return "";
        String cell = text(port.get("cell"));
        if (CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT.equals(
                text(port.get(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND)))) {
            // A declared cut argument is a static endpoint in its own right:
            // the unit, the callee and the argument position name it exactly,
            // and repeated deliveries of that one cut are occurrences of this
            // endpoint rather than separate outputs.
            return "CUT\n" + text(port.get(
                    CommunicationCatalogContract.CALL_SITE_ID))
                    + "\n" + text(port.get("declaredCallee"))
                    + "\narg" + integer(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1)
                    + "\n" + text(port.get(
                    CommunicationCatalogContract.PORT_DIRECTION));
        }
        if (!text(port.get(CommunicationCatalogContract.PORT_COMPONENT_OF)).isEmpty()
                && !text(port.get(CommunicationCatalogContract.PORT_ENCODING_AUTHORITY)).isEmpty()) {
            // A structured leaf is a declared communication endpoint, not a
            // heap endpoint to rediscover from an access history.  Test this
            // before ENTRY_RETURN: a configured response component shares
            // the server return boundary with its concrete parent but is a
            // different typed output.  Grouping both as one communication
            // effect makes the otherwise exact output port ambiguous.
            return "HANDOFF_COMPONENT\n" + text(port.get(
                    CommunicationCatalogContract.EXCHANGE_SITE_KEY))
                    + "\n" + text(port.get(
                    CommunicationCatalogContract.PORT_DIRECTION))
                    + "\n" + text(port.get(
                    CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH));
        }
        if (CommunicationCatalogContract.CAPTURE_ENTRY_RETURN.equals(
                text(port.get(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND)))) {
            return "COMMUNICATION_EFFECT\n" + text(port.get(
                    CommunicationCatalogContract.PORT_DEFINITION_METHOD))
                    + "\n" + text(port.get(
                    CommunicationCatalogContract.PORT_DIRECTION));
        }
        Map<String, Object> access = exactDemandedHeapOutput(port,
                Collections.singletonList(binding), occurrenceId);
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

    /**
     * Folds output ports that observed one write through different access
     * paths onto one canonical port.
     *
     * <p>A heap cell an activation can reach by more than one path is
     * captured once per path, so a single write becomes several ports that
     * differ only in how the region navigated to it.  The demanded endpoint
     * then never converges on a port and the whole producer relation is
     * refused, although the recording proves one write to one cell.  These
     * are alias observations, not versions: versions differ in the write
     * they publish and keep their own ports and their own guarded case.
     * The path with the fewest indirections is the canonical observation,
     * which makes the choice deterministic and reads no name.</p>
     */
    private static Map<String, String> canonicalAliasedOutputPorts(
            Map<String, Object> region, String occurrenceId) {
        Map<String, String> result = new LinkedHashMap<>();
        if (region == null) return result;
        Map<String, Map<String, Object>> canonical = new LinkedHashMap<>();
        List<Map<String, Object>> observed = new ArrayList<>();
        for (Map<String, Object> port : rows(region.get("outputs"))) {
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
            result.put(text(port.get("portId")),
                    text(best.get("portId")));
        }
        return result;
    }

    /**
     * Identity of the single write a heap output port observed.  Access
     * path aside, two ports naming the same declared cell of the same
     * object at the same recorded write are one output.
     */
    private static String observedWriteIdentity(Map<String, Object> port) {
        List<String> declarations = strings(
                port.get("fieldPathDeclarations"));
        long owner = longNumber(port.get("fieldReceiverObjectId"), -1L);
        long event = longNumber(port.get("eventSeq"), -1L);
        if (declarations.isEmpty() || owner < 0L || event < 0L) return "";
        return text(port.get("bindingKind")) + "\n"
                + text(port.get("siteId")) + "\n"
                + text(port.get("mutatorDeclaredCallee")) + "\n"
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
                : text(port.get("portId")).compareTo(
                        text(other.get("portId"))) < 0;
    }

    /**
     * The demanded output occurrences of this goal, as replayable epochs.
     *
     * <p>{@code loopBodyBound} really does bound this: each epoch is a whole
     * producer goal that is finalized, replayed and composed, so the count
     * is the campaign's own {@code K_L} rather than an unbounded fan-out.
     * What it must never be is silent.  The bound used to be applied with a
     * bare {@code Math.min}, so an output the run produced twelve
     * occurrences of was modelled with eight epochs and the last four
     * vanished - a history that reads as complete and is not.  Every
     * occurrence beyond the bound is now counted into
     * {@code unmodelledByOutput} for its caller to name.</p>
     */
    private static List<Map<String, List<Map<String, Object>>>>
            demandedBindingAlternatives(
            List<String> outputs,
            Map<String, List<Map<String, Object>>> byOutput,
            int loopBodyBound,
            Map<String, Integer> unmodelledByOutput) {
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
                    Math.min(choices.size(), loopBodyBound));
        }
        for (String output : outputs) {
            int occurrences = choicesByOutput.get(output).size();
            if (occurrences > alternativeCount
                    && unmodelledByOutput != null) {
                unmodelledByOutput.put(output,
                        Integer.valueOf(occurrences - alternativeCount));
            }
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
        return Long.MIN_VALUE;
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
                List<Map<String, Object>> captures = rows(
                        slice.get("captureBindings"));
                boolean regionExitField = !captures.isEmpty()
                        && captures.stream().allMatch(capture ->
                        OutputCaptureSpec.REGION_EXIT_FIELD.equals(text(
                                capture.get("captureKind"))));
                if (regionExitField) {
                    // A region-exit field snapshot is selected by its binding
                    // and tracked owner, not by a dynamic write occurrence.
                    // Adding an occurrence here would turn it back into an
                    // exact-write request and make the retained-state side of
                    // a fault-controlled merge impossible to observe.
                    continue;
                }
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
            String captureKind = text(capture.get("captureKind"));
            if (OutputCaptureSpec.CALL_ARGUMENT.equals(captureKind)) {
                endpoints.add("CALL_ARGUMENT:"
                        + text(capture.get("definitionMethod")) + "#u"
                        + integer(capture.get("definitionUnitIndex"), -1)
                        + ":" + text(capture.get("declaredCallee"))
                        + "#arg"
                        + integer(capture.get("argumentIndex"), -1));
            } else if (OutputCaptureSpec.COMMUNICATION_EFFECT.equals(
                    captureKind)) {
                endpoints.add(OutputCaptureSpec.COMMUNICATION_EFFECT + ":"
                        + text(capture.get("definitionMethod")));
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
            } else if (OutputCaptureSpec.REGION_EXIT_FIELD.equals(
                    captureKind)) {
                List<String> path = strings(capture.get("fieldPath"));
                endpoints.add("REGION_EXIT_FIELD:"
                        + text(capture.get("fieldSignature")) + ":"
                        + path);
            } else if (OutputCaptureSpec.HANDOFF_BOUND_LEAF.equals(
                    captureKind)) {
                // The exchange site and the leaf the handoff bound are the
                // whole static address of a cut leaf: no definition unit,
                // because the value leaves through the cut rather than at a
                // unit of this method.  This restates the endpoint the
                // binding itself already published, so a producer the
                // closure reaches through a recorded delivery is numbered
                // like every other output instead of refused outright.
                endpoints.add(OutputCaptureSpec.HANDOFF_BOUND_LEAF + ":"
                        + text(capture.get(CommunicationCatalogContract.EXCHANGE_SITE_KEY)) + ":"
                        + text(capture.get("leafPath")));
            } else {
                throw new IllegalArgumentException(
                        "unsupported output capture kind: " + captureKind);
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
            int loopBodyBound, List<String> rejectionReasons) {
        if (region == null) return null;
        List<Map<String, Object>> trusted = new ArrayList<>();
        boolean allReadFrom = true;
        for (Map<String, Object> binding : bindings) {
            JsonObject encoded = toJsonTreeFast(binding).getAsJsonObject();
            allReadFrom &= AutomaticRegionEdge
                    .trustedRuntimeReadFromBinding(encoded);
            trusted.add(binding);
        }
        if (trusted.isEmpty() || !allReadFrom) {
            return null;
        }

        String occurrenceId = text(plan.get("occurrenceId"));
        Map<String, Object> outputPortRow = uniquePort(
                rows(region.get("outputs")), outputPort, occurrenceId);
        Map<String, Object> output = exactDemandedHeapOutput(
                outputPortRow, trusted, occurrenceId);
        if (output == null) return null;
        String staticAccessSiteId = text(output.get("staticAccessSiteId"));
        Matcher staticSite = STATIC_SITE.matcher(staticAccessSiteId);
        int recordedOutputOccurrence = integer(output.get(
                "activationLocalStaticSiteOccurrence"), -1);
        String bindingKind = text(output.get("bindingKind"));
        // The recorded ordinal is trace provenance only.  Replay captures at
        // the semantic output boundary selected below; it must not depend on
        // how many times this site happened to execute in the seed trace.
        if (!staticSite.matches()) {
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
                bindingKind) || exactFieldAssignment;
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
        String javaType = leafType(declarations);
        String owner = fieldOwner(declaration);
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
        // interactions before this output.  Those earlier observed sibling
        // invocations are prior causal state, not local code that this
        // interaction must replay.  Keep the exact root-to-output corridor
        // and its completed helper subtree.  Statically reachable methods
        // that were not observed remain eligible so a branch flip can still
        // discover a new case; a later topology change is replanned from its
        // own runtime evidence.
        allowed.removeIf(method -> baselineMethods.contains(method)
                && !corridorMethods.contains(method));
        allowed.addAll(corridorMethods);
        ExactMutationFold mutationFold = null;
        long relationBoundarySeq = Math.max(outputEventSeq,
                longNumber(output.get("mutationCompletionSeq"), -1L));
        if (mutation) {
            mutationFold = trace.exactMutationFold(outputEventSeq,
                    definitionMethod, staticAccessSiteId, declaredCallee,
                    integer(output.get("valueObjectId"), 0));
            // A mutation relation denotes the state at the definition
            // invocation's normal exit.  An anchor in the middle of a loop
            // is not a complete output relation: every later mutation of the
            // same receiver at the statically selected mutator must be
            // observed and stay within the configured bound.
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
                text(outputPortRow.get("symbolicDemand")))
                && JavaContainerTypes.shape(javaType)
                != JavaContainerTypes.Shape.NONE;
        if (!boundedMutation) {
            priorStateInput = matchingFieldInputBeforeOutput(regionInputs,
                    occurrenceId, output, path, declarations);
        }
        // The corridor is the call chain that performed the store.  It is
        // added, never subtracted.
            //
            // Subtracting it answered "which methods may define this output"
            // with "the ones on the stack when it was stored", and those are
            // different questions.  A produced value is computed *before* the
            // call that stores it - `x = compute(...); publish(x)` is the
            // ordinary shape - so the definition chain is a sibling of the
            // storing call and every observed method of it was removed.  The
            // backward slice then could not leave the storing method, the
            // relation closed over a parameter with no reachable root, and
            // the producer published one case with guard `true` and a
            // constant.  Which *invocation* produced this output is a real
            // question, and it is answered where it belongs: by the output's
            // own event boundary below, which bounds the slice in time the
            // same way the target slice is bounded, and by the exact branch
            // replay that reads this corridor directly.
        if (!allowed.contains(definitionMethod)) return null;
        String planRootMethod = text(
                row(plan.get("rootSelector")).get("method"));
        Set<String> seedMethods = new LinkedHashSet<>();
        seedMethods.add(planRootMethod);
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
        ReturnSlice stateSlice = refinedFlow.dependencySlice(
                text(plan.get("regionId")), occurrenceId, declaration,
                sliceOutput, allowed, regionInputs, regionOutputs,
                rows(region.get("branchPolicies")), seedMethods);
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
            addIfAllowed(methods, allowed, planRootMethod);
        }
        if (methods.isEmpty()) return null;
        // A communication component can be delivered before the helper that
        // writes this output.  Its declared receiver frame is part of the
        // executable slice even when the heap-only backward slice begins in
        // the nested writer.  Otherwise replay starts after the VM attach and
        // the live handoff expression can never reach the selected output.
        for (Map<String, Object> input : regionInputs) {
            if (!exactCommunicationInputs.containsKey(
                    text(input.get("portId")))) {
                continue;
            }
            addIfAllowed(methods, allowed,
                    text(input.get("definitionMethod")));
        }
        Set<String> methodSet = new LinkedHashSet<>(methods);
        methodSet.add(definitionMethod);
        methods = new ArrayList<>(methodSet);
        long definitionCallId = mutationFold == null
                ? trace.callAt(outputEventSeq)
                : mutationFold.definitionCallId;
        long evidenceRootCall = traceEvidenceRootCall(plan);
        MethodEvent replayContinuation = rootOwnsSelectedCommunicationInput(
                planRootMethod, exactCommunicationInputs,
                regionInputs)
                ? trace.methodByCall.get(evidenceRootCall)
                : trace.exactReplayContinuation(
                evidenceRootCall, definitionCallId, methodSet);
        if (!addReachingAccessorMaterializations(inputPorts, regionInputs,
                occurrenceId, methodSet, relationBoundarySeq,
                invocationCalls, rejectionReasons, outputPort)) {
            return null;
        }
        List<Map<String, Object>> exactBranches = exactBranchReplay(
                rows(region.get("branchPolicies")), stateSlice.branchSites,
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

        // A repeated semantic output site needs one causal observation that
        // says which dynamic state transition this member belongs to.  The
        // latest exact accessor read in the member's own backward slice is
        // that observation.  It is deliberately not an output occurrence or
        // version selector: replay may execute a different number of earlier
        // updates, while this exact input slot still identifies the relation
        // that reached the output boundary.
        String captureAnchorPort = latestAccessorInputPort(
                inputPorts, regionInputs);

        List<String> staticSites = new ArrayList<>(stateSlice.staticSites);
        if (!staticSites.contains(staticAccessSiteId)) {
            staticSites.add(staticAccessSiteId);
        }
        List<String> sites = new ArrayList<>(stateSlice.branchSites);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", outputPort);
        slice.addProperty("outputCell", semanticDeclaration);
        slice.add("inputPorts", stringsJson(inputPorts));
        if (!captureAnchorPort.isEmpty()) {
            slice.addProperty("captureAnchorPort", captureAnchorPort);
        }
        slice.add("demandedHeapDeclarations", stringsJson(
                stateSlice.demandedHeapDeclarations));
        slice.add("sites", stringsJson(sites));
        slice.add("staticSites", stringsJson(staticSites));
        slice.add("methods", stringsJson(methods));
        if (replayContinuation != null) {
            slice.add(ExecutionTask.REPLAY_ENTRY, toJsonTreeFast(object(
                    "method", replayContinuation.method,
                    "receiverClass", replayContinuation.receiverType)));
        }
        int replayOccurrence = mutation
                ? mutationFold == null ? recordedOutputOccurrence
                : mutationFold.anchorOccurrence
                : recordedOutputOccurrence;
        if (replayOccurrence < 1) {
            rejectionReasons.add("OUTPUT_OCCURRENCE_UNRESOLVED:"
                    + outputPort);
            return null;
        }
        if (!explicitFaultExitSnapshot) {
            slice.addProperty("activationLocalOccurrence", replayOccurrence);
        }
        slice.addProperty("selectedRuntimeEventSeq", longNumber(
                output.get("eventSeq"), -1L));
        long selectedFieldReceiver = longNumber(
                output.get("fieldReceiverObjectId"), 0L);
        if (!mutation && selectedFieldReceiver != 0L) {
            // Exact trace identity used later to connect a field value
            // produced by one helper invocation to a read of that same
            // object in a later helper invocation of this region.  This is
            // not a replay selector: it only publishes the observed
            // write/read relation for atomic task construction.
            slice.addProperty("selectedFieldReceiverObjectId",
                    selectedFieldReceiver);
        }
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
        } else if (explicitFaultExitSnapshot) {
            slice.addProperty("outputBoundaryKind",
                    "REGION_EXIT_FIELD_SNAPSHOT");
        } else {
            slice.addProperty("outputBoundaryKind",
                    "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT");
        }
        addConcretePrimitiveCallReturns(slice, trace, invocationCalls,
                stateSlice.staticSites, inputPorts, regionInputs,
                relationBoundarySeq);

        JsonArray edgeIds = new JsonArray();
        Set<String> seenEdges = new LinkedHashSet<>();
        for (Map<String, Object> binding : trusted) {
            String edgeId = text(binding.get("edgeId"));
            if (edgeId.isEmpty() || !seenEdges.add(edgeId)) continue;
            edgeIds.add(edgeId);
        }
        for (String edgeId : exactCommunicationInputs.values()) {
            if (!edgeId.isEmpty() && seenEdges.add(edgeId)) {
                edgeIds.add(edgeId);
            }
        }
        if (edgeIds.size() == 0) return null;
        slice.add("causalEdgeIds", edgeIds);

        JsonObject capture = new JsonObject();
        String captureId = "CAPTURE." + UUID.nameUUIDFromBytes((
                text(plan.get("occurrenceId")) + "\n" + outputPort
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
        String captureDefinition = semanticDeclaration;
        String captureMethod = definitionMethod;
        int captureUnit = definitionUnitIndex;
        String captureStaticSite = staticAccessSiteId;
        if (!atomicValueField.isEmpty()) {
            capturePath.add(path.get(path.size() - 1));
            capturePath.add(FieldPathSpec.declaredField(
                    atomicValueField).name());
        } else {
            capturePath.add(path.get(path.size() - 1));
        }
        capture.add("fieldPath", stringsJson(capturePath));
        capture.addProperty("fieldSignature", semanticDeclaration);
        capture.addProperty("javaType", semanticJavaType);
        if (explicitFaultExitSnapshot) {
            capture.addProperty("accessRootInputPort",
                    text(priorStateInput.get("portId")));
        }
        capture.addProperty("definitionMethod", captureMethod);
        capture.addProperty("definitionUnitIndex", captureUnit);
        String recordedPrimitiveValue = text(output.get("primitiveValue"));
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
                + captureStaticSite + ":"
                + captureDefinition;
        if (!explicitFaultExitSnapshot) {
            capture.addProperty("outputSiteId", captureSiteId);
            capture.addProperty("outputOccurrence", replayOccurrence);
            capture.addProperty("replayOccurrence", replayOccurrence);
        }
        if (mutationFold != null) {
            capture.addProperty("occurrenceScope",
                    "DEFINITION_INVOCATION");
            capture.addProperty("outputBoundaryKind",
                    "DEFINITION_INVOCATION_NORMAL_EXIT");
            capture.addProperty("definitionCompletionSeq",
                    mutationFold.normalExitSeq);
            capture.addProperty("foldedMutationCount",
                    mutationFold.completions.size());
        } else if (explicitFaultExitSnapshot) {
            capture.addProperty("outputBoundaryKind",
                    "REGION_EXIT_FIELD_SNAPSHOT");
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
                text(plan.get("relationKey")),
                text(plan.get("regionId")),
                outputPort, semanticDeclaration, "HEAP_STATE",
                semanticJavaType, slice);
    }

    /**
     * The concrete interaction that supplied a heap output's structured
     * live-in.  A coarse service occurrence can receive many messages before
     * it publishes one state update, so the declaration alone is not enough:
     * select the recorded delivery that belongs to the same remote span as
     * this exact output event.  When the transport did not publish a span,
     * the latest prior delivery is the bounded best-effort topology.
     *
     * <p>This is scheduling topology only.  It never equates the serialized
     * object with a heap field and never supplies a symbolic value; replay's VM
     * {@code VALUE_HANDOFF} remains the value authority.</p>
     */
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
                    text(input.get("sourceKind")))) {
                continue;
            }
            String portId = text(input.get("portId"));
            if (!portId.isEmpty()) communicationPorts.add(portId);
        }
        if (communicationPorts.isEmpty()) return Collections.emptyMap();

        long outputRemoteSpan = trace.remoteParentSpanAt(outputEventSeq);
        List<Map<String, Object>> prior = new ArrayList<>();
        List<Map<String, Object>> sameSpan = new ArrayList<>();
        for (Map<String, Object> binding : rows(goal.get("edgeBindings"))) {
            if (!"RUNTIME_PROTOCOL_FLOW".equals(text(binding.get("kind")))
                    || !occurrenceId.equals(
                    text(binding.get("toOccurrenceId")))) {
                continue;
            }
            String portId = text(binding.get("toInputPort"));
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
        return exactProtocolDeliveryInputs(candidates, regionInputs);
    }

    /**
     * Selects one observed delivery and retains every semantic port carried by
     * that delivery.  Parent response structure and configured component
     * leaves are siblings, not competing observations.
     */
    static Map<String, String> exactProtocolDeliveryInputs(
            List<Map<String, Object>> candidates,
            List<Map<String, Object>> declaredInputs) {
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

        String selectedPort = text(selected.get("toInputPort"));
        String parentPort = selectedPort;
        for (Map<String, Object> input : declaredInputs) {
            if (!selectedPort.equals(text(input.get("portId")))) continue;
            String configuredParent = text(input.get("componentOfPortId"));
            if (!configuredParent.isEmpty()) parentPort = configuredParent;
            break;
        }
        Set<String> deliveryPorts = new LinkedHashSet<>();
        deliveryPorts.add(parentPort);
        deliveryPorts.add(selectedPort);
        for (Map<String, Object> input : declaredInputs) {
            if (parentPort.equals(text(input.get("componentOfPortId")))) {
                String portId = text(input.get("portId"));
                if (!portId.isEmpty()) deliveryPorts.add(portId);
            }
        }

        // A structured delivery owns several semantic ports: its concrete
        // parent response and each configured component leaf.  They are not
        // alternative deliveries.  Select one exact delivery first, then
        // retain every port declared on that delivery so the consumer output
        // slice keeps both its replay structure and its value-frontier VM
        // handoff.  The old single-edge choice happened to keep the parent's
        // lexically earlier edge id and silently dropped every component.
        Map<String, String> result = new LinkedHashMap<>();
        for (Map<String, Object> candidate : candidates) {
            if (!sameProtocolDelivery(selected, candidate)) continue;
            String portId = text(candidate.get("toInputPort"));
            if (!deliveryPorts.contains(portId)) continue;
            String edgeId = text(candidate.get("edgeId"));
            if (portId.isEmpty() || edgeId.isEmpty()) {
                return Collections.emptyMap();
            }
            String priorEdge = result.putIfAbsent(portId, edgeId);
            if (priorEdge != null && !priorEdge.equals(edgeId)) {
                return Collections.emptyMap();
            }
        }
        return result;
    }

    /** Stable identity of one observed protocol delivery, excluding port. */
    private static String protocolDeliveryIdentity(
            Map<String, Object> binding) {
        String direction = text(binding.get("direction"));
        if (direction.isEmpty()) {
            direction = text(binding.get("protocolDirection"));
        }
        return text(binding.get("fromOccurrenceId")) + "\n"
                + text(binding.get("toOccurrenceId")) + "\n"
                + text(binding.get(
                CommunicationCatalogContract.EXCHANGE_SITE_KEY)) + "\n"
                + text(binding.get("attemptId")) + "\n"
                + direction + "\n"
                + longNumber(binding.get("senderEventSeq"), -1L) + "\n"
                + longNumber(binding.get("receiverEventSeq"), -1L);
    }

    private static boolean sameProtocolDelivery(
            Map<String, Object> left, Map<String, Object> right) {
        return protocolDeliveryIdentity(left).equals(
                protocolDeliveryIdentity(right));
    }

    /** True when a demanded delivery is attached in the occurrence root. */
    private static boolean rootOwnsSelectedCommunicationInput(
            String rootMethod, Map<String, String> selected,
            List<Map<String, Object>> regionInputs) {
        if (rootMethod.isEmpty() || selected.isEmpty()) return false;
        for (Map<String, Object> input : regionInputs) {
            if (selected.containsKey(text(input.get("portId")))
                    && rootMethod.equals(
                    text(input.get("definitionMethod")))) {
                return true;
            }
        }
        return false;
    }

    /** Boundary label of a structured leaf exported by the VM broker. */
    private static final String HANDOFF_COMPONENT_BOUNDARY =
            "EXACT_HANDOFF_BOUND_COMPONENT_LEAF";

    /**
     * Closes a component port on one exact VM expression export.
     *
     * <p>A component has no Java argument index: static discovery declares
     * that it crosses inside {@code componentOfPortId}, while the VM exports
     * the component field as its own named leaf.  The relation is therefore
     * the identity from the exact activation field input to that exact leaf.
     * It is admitted only when the declaration, field access and occurrence-
     * scoped protocol edge all agree.  No parent-argument or heap fallback is
     * attempted.</p>
     */
    private static OutputClosureContract handoffComponentOutputClosure(
            Map<String, Object> plan, Map<String, Object> goal,
            Map<String, Object> region, String outputPort,
            List<Map<String, Object>> bindings,
            RefinedFlowIndex refinedFlow, TraceIndex trace,
            int loopBodyBound, List<String> rejectionReasons) {
        if (region == null) return null;
        String occurrenceId = text(plan.get("occurrenceId"));
        String regionId = text(plan.get("regionId"));
        Map<String, Object> port = uniquePort(rows(region.get("outputs")),
                outputPort, occurrenceId);
        if (port == null) return null;

        String parentPortId = text(port.get(
                CommunicationCatalogContract.PORT_COMPONENT_OF));
        String encodingAuthority = text(port.get(
                CommunicationCatalogContract.PORT_ENCODING_AUTHORITY));
        String exchangeSiteKey = text(port.get(
                CommunicationCatalogContract.EXCHANGE_SITE_KEY));
        String componentName = text(port.get(
                CommunicationCatalogContract.PORT_NAME));
        String leafPath = text(port.get(
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH));
        String direction = text(port.get(
                CommunicationCatalogContract.PORT_DIRECTION));
        String javaType = text(port.get("javaType"));
        // A request component uses its static call-argument declaration.  A
        // response component has an occurrence-owned sibling response whose
        // return slice bounds this leaf's live-ins below.
        Map<String, Object> parent =
                CommunicationCatalogContract.DIRECTION_RESPONSE.equals(
                        direction)
                        ? uniquePort(rows(region.get("outputs")),
                        parentPortId, occurrenceId)
                        : uniqueDeclaredPort(rows(region.get("outputs")),
                        parentPortId);
        String expectedParentCapture =
                CommunicationCatalogContract.DIRECTION_RESPONSE.equals(
                        direction)
                        ? CommunicationCatalogContract.CAPTURE_ENTRY_RETURN
                        : CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT;
        if (parentPortId.isEmpty() || encodingAuthority.isEmpty()
                || exchangeSiteKey.isEmpty() || componentName.isEmpty()
                || leafPath.isEmpty()
                || javaType.isEmpty() || parent == null
                || !expectedParentCapture.equals(text(parent.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND)))
                || !exchangeSiteKey.equals(text(parent.get(
                CommunicationCatalogContract.EXCHANGE_SITE_KEY)))
                || !direction.equals(text(parent.get(
                CommunicationCatalogContract.PORT_DIRECTION)))) {
            rejectionReasons.add("HANDOFF_COMPONENT_DECLARATION_INCOMPLETE:"
                    + outputPort);
            return null;
        }

        Map<String, Object> exactBinding = null;
        for (Map<String, Object> binding : bindings) {
            boolean exact = occurrenceId.equals(text(binding.get(
                    "fromOccurrenceId")))
                    && outputPort.equals(text(binding.get(
                    "fromOutputPort")))
                    && outputPort.equals(text(binding.get("toInputPort")))
                    && exchangeSiteKey.equals(text(binding.get(
                    CommunicationCatalogContract.EXCHANGE_SITE_KEY)))
                    && leafPath.equals(text(binding.get(
                    CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH)))
                    && direction.equals(text(binding.get("direction"))
                    .isEmpty()
                    ? text(binding.get("protocolDirection"))
                    : text(binding.get("direction")))
                    && !text(binding.get("edgeId")).isEmpty();
            if (!exact) continue;
            if (exactBinding != null) {
                rejectionReasons.add(
                        "HANDOFF_COMPONENT_EDGE_AMBIGUOUS:" + outputPort
                                + ":" + text(binding.get("edgeId")));
                return null;
            }
            exactBinding = binding;
        }
        if (exactBinding == null) {
            rejectionReasons.add("HANDOFF_COMPONENT_EDGE_MISSING:"
                    + outputPort);
            return null;
        }

        long sentAt = longNumber(exactBinding.get("senderEventSeq"), -1L);
        if (sentAt < 0L) {
            rejectionReasons.add("HANDOFF_COMPONENT_SEND_ORDER_MISSING:"
                    + outputPort);
            return null;
        }
        List<Map<String, Object>> priorHeapInputs =
                preHandoffHeapInputs(region, goal, occurrenceId, sentAt);

        // A response component is one leaf of its sibling response, not a
        // summary of every heap read the long-lived handler happened to make
        // before sending.  The sibling's return slice is the code-level
        // authority for which of those observed reads can construct or guard
        // this response.  Intersecting the two retains the exact runtime
        // roots (including guard roots) while excluding prior, unrelated
        // interactions in the same coarse occurrence.
        if (CommunicationCatalogContract.DIRECTION_RESPONSE.equals(
                direction)) {
            List<Map<String, Object>> parentBindings =
                    exactSiblingResponseBindings(goal, parentPortId,
                            exactBinding);
            OutputClosureContract parentClosure =
                    communicationEffectOutputClosure(plan, goal, region,
                            parentPortId, parentBindings, refinedFlow, trace,
                            loopBodyBound, new ArrayList<>());
            if (parentClosure == null) {
                rejectionReasons.add(
                        "HANDOFF_COMPONENT_PARENT_RETURN_SLICE_UNRESOLVED:"
                                + outputPort);
                return null;
            }
            priorHeapInputs = retainParentReturnInputs(priorHeapInputs,
                    parentClosure.executionScope().inputPorts());
        }

        MethodEvent replayEntry = trace.methodByCall.get(
                traceEvidenceRootCall(plan));
        if (replayEntry == null) {
            rejectionReasons.add(
                    "HANDOFF_COMPONENT_REPLAY_ENTRY_UNRESOLVED:"
                            + outputPort);
            return null;
        }

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", outputPort);
        slice.addProperty("outputCell", outputPort);
        // The expression is already live at the VM export, so these inputs do
        // not assert a Java-side projection or value equality.  They are the
        // exact heap value frontier this occurrence read before the observed
        // export, which is the bounded seed needed to replay the producer.
        // The replay's VM VALUE_HANDOFF ledger remains the sole authority for
        // which of those values actually reaches the receiver expression.
        JsonArray inputPorts = new JsonArray();
        Set<String> demandedHeap = new LinkedHashSet<>();
        for (Map<String, Object> input : priorHeapInputs) {
            inputPorts.add(text(input.get("portId")));
            demandedHeap.addAll(strings(
                    input.get("fieldPathDeclarations")));
            String leaf = text(input.get("leafFieldSignature"));
            if (!leaf.isEmpty()) demandedHeap.add(leaf);
            String access = text(input.get("accessFieldSignature"));
            if (!access.isEmpty()) demandedHeap.add(access);
        }
        // The exact configured component path is itself part of the leaf's
        // demand.  In particular, a response slice may read the parent
        // reference without containing a separate heap-read input for the
        // terminal primitive field.  Keeping every FIELD declaration lets a
        // configured source bind to that exact leaf without inventing a
        // Java-side projection or widening to the parent response.
        demandedHeap.addAll(handoffPathFieldDeclarations(port));
        slice.add("inputPorts", inputPorts);
        slice.add("demandedHeapDeclarations", stringsJson(demandedHeap));
        slice.add("sites", new JsonArray());
        slice.add("staticSites", stringsJson(Collections.singleton(
                text(port.get(CommunicationCatalogContract.CALL_SITE_ID)))));
        slice.add("methods", stringsJson(Collections.singleton(
                text(parent.get(
                        CommunicationCatalogContract.PORT_DEFINITION_METHOD)))));
        slice.addProperty("activationLocalOccurrence", 1);
        slice.addProperty("outputBoundaryKind", HANDOFF_COMPONENT_BOUNDARY);
        JsonArray edgeIds = new JsonArray();
        Set<String> retainedInputPorts = new LinkedHashSet<>();
        for (Map<String, Object> input : priorHeapInputs) {
            retainedInputPorts.add(text(input.get("portId")));
        }
        Set<String> selectedEdgeIds = componentCausalEdgeIds(goal,
                occurrenceId, sentAt, retainedInputPorts,
                text(exactBinding.get("edgeId")));
        for (String edgeId : selectedEdgeIds) edgeIds.add(edgeId);
        slice.add("causalEdgeIds", edgeIds);

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE."
                + UUID.nameUUIDFromBytes((occurrenceId + "\n" + outputPort
                + "\n" + text(exactBinding.get("edgeId")))
                .getBytes(StandardCharsets.UTF_8)));
        capture.addProperty("captureKind",
                OutputCaptureSpec.HANDOFF_BOUND_LEAF);
        capture.addProperty("outputPort", outputPort);
        capture.addProperty("outputCell", outputPort);
        capture.addProperty("javaType", javaType);
        capture.addProperty(CommunicationCatalogContract.PORT_COMPONENT_OF,
                parentPortId);
        capture.addProperty(
                CommunicationCatalogContract.PORT_ENCODING_AUTHORITY,
                encodingAuthority);
        capture.addProperty(CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                exchangeSiteKey);
        capture.addProperty("leafPath", leafPath);
        capture.addProperty(CommunicationCatalogContract.PORT_DIRECTION,
                direction);
        capture.addProperty("edgeId", text(exactBinding.get("edgeId")));
        capture.addProperty("occurrenceScope",
                OutputCaptureSpec.REGION_ACTIVATION_SCOPE);
        capture.addProperty("outputBoundaryKind",
                HANDOFF_COMPONENT_BOUNDARY);
        capture.addProperty("outputSiteId",
                OutputCaptureSpec.HANDOFF_BOUND_LEAF + ":"
                        + exchangeSiteKey + ":" + leafPath);
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("replayOccurrence", 1);
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());

        try {
            OutputClosureContract contract = OutputClosureCodec.singleton(
                    text(plan.get("relationKey")), regionId,
                    declaredOutputPortIds(rows(region.get("outputs"))),
                    outputPort, outputPort, "REGION_OUTPUT",
                    javaType, slice);
            if (!declareReplayEntry(goal, replayEntry)) {
                rejectionReasons.add(
                        "HANDOFF_COMPONENT_REPLAY_ENTRY_CONFLICT:"
                                + outputPort);
                return null;
            }
            return contract;
        } catch (IllegalArgumentException refused) {
            rejectionReasons.add("HANDOFF_COMPONENT_CONTRACT_REFUSED:"
                    + outputPort + ":" + refused.getMessage());
            return null;
        }
    }

    /** Keeps the observed heap roots admitted by the sibling return slice. */
    static List<Map<String, Object>> retainParentReturnInputs(
            List<Map<String, Object>> priorHeapInputs,
            Set<String> parentReturnInputPorts) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> input : priorHeapInputs) {
            if (parentReturnInputPorts.contains(text(input.get("portId")))) {
                result.add(input);
            }
        }
        return result;
    }

    /** Exact FIELD declarations traversed by one configured component. */
    static Set<String> handoffPathFieldDeclarations(
            Map<String, Object> port) {
        Set<String> result = new LinkedHashSet<>();
        if (port == null) return result;
        for (Map<String, Object> step : rows(port.get(
                CommunicationCatalogContract.PORT_HANDOFF_PATH))) {
            if (!"FIELD".equals(text(step.get("kind")))) continue;
            String declaration = text(step.get("declaration"));
            if (!declaration.isEmpty()) result.add(declaration);
        }
        return result;
    }

    /** The outgoing handoff plus exact inbound RF edges of its live-ins. */
    static Set<String> componentCausalEdgeIds(
            Map<String, Object> goal, String occurrenceId, long sentAt,
            Set<String> retainedInputPorts, String outgoingEdgeId) {
        Set<String> result = new LinkedHashSet<>();
        if (!outgoingEdgeId.isEmpty()) result.add(outgoingEdgeId);
        result.addAll(exactInboundReadFromEdgeIds(goal, occurrenceId,
                sentAt, retainedInputPorts));
        return result;
    }

    /** Exact parent edge from the same recorded response delivery. */
    private static List<Map<String, Object>> exactSiblingResponseBindings(
            Map<String, Object> goal, String parentPortId,
            Map<String, Object> componentBinding) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> binding : rows(goal.get("edgeBindings"))) {
            if (parentPortId.equals(text(binding.get("fromOutputPort")))
                    && sameProtocolDelivery(componentBinding, binding)) {
                result.add(binding);
            }
        }
        return result;
    }

    /** Exact trusted inbound RF edges for the retained component inputs. */
    private static Set<String> exactInboundReadFromEdgeIds(
            Map<String, Object> goal, String occurrenceId, long sentAt,
            Set<String> retainedInputPorts) {
        Set<String> result = new LinkedHashSet<>();
        if (retainedInputPorts.isEmpty()) return result;
        for (Map<String, Object> binding : rows(goal.get("edgeBindings"))) {
            if (!"RUNTIME_FIELD_FLOW".equals(text(binding.get("kind")))
                    || !occurrenceId.equals(text(
                    binding.get("toOccurrenceId")))
                    || !retainedInputPorts.contains(text(
                    binding.get("toInputPort")))) {
                continue;
            }
            long read = longNumber(binding.get("readerEventSeq"), -1L);
            if (read < 0L || read >= sentAt
                    || !AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                    toJsonTreeFast(binding).getAsJsonObject())) {
                continue;
            }
            String edgeId = text(binding.get("edgeId"));
            if (!edgeId.isEmpty()) result.add(edgeId);
        }
        return result;
    }

    /**
     * Exact heap value inputs read by one occurrence before a VM handoff.
     *
     * <p>This is deliberately occurrence- and event-scoped.  A coarse region
     * may touch many fields in other executions; none of those belong to this
     * handoff seed.  Conversely, the first replay has no VM expression ledger
     * yet, so it cannot discover the symbolic heap roots that compute the
     * export unless the roots actually observed before this send are present
     * in the task.  Later composition uses only the VM lineage, never this
     * ordering fact, as value authority.</p>
     */
    private static List<Map<String, Object>> preHandoffHeapInputs(
            Map<String, Object> region, Map<String, Object> goal,
            String occurrenceId, long sentAt) {
        Set<String> exactPriorPorts = new LinkedHashSet<>();
        for (Map<String, Object> binding
                : rows(goal.get("edgeBindings"))) {
            if (!"RUNTIME_FIELD_FLOW".equals(text(binding.get("kind")))
                    || !occurrenceId.equals(text(
                    binding.get("toOccurrenceId")))
                    || !DependencyRole.valueFrontier(
                    binding.get("dependencyRole"))) {
                continue;
            }
            long read = longNumber(binding.get("readerEventSeq"), -1L);
            if (read < 0L || read >= sentAt) continue;
            JsonObject encoded = toJsonTreeFast(binding).getAsJsonObject();
            if (!AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                    encoded)) {
                continue;
            }
            String port = text(binding.get("toInputPort"));
            if (!port.isEmpty()) exactPriorPorts.add(port);
        }
        List<Map<String, Object>> result = new ArrayList<>();
        Set<String> ports = new LinkedHashSet<>();
        for (Map<String, Object> input
                : rows(region.get("symbolicInputs"))) {
            if (!boundToInput(input, occurrenceId)
                    || !exactPriorPorts.contains(text(input.get("portId")))) {
                continue;
            }
            boolean observedBefore = false;
            for (Map<String, Object> access
                    : rows(input.get("runtimeAccesses"))) {
                long event = longNumber(access.get("eventSeq"), -1L);
                if (event >= 0L && event < sentAt) {
                    observedBefore = true;
                    break;
                }
            }
            if (!observedBefore) {
                long event = longNumber(input.get("eventSeq"), -1L);
                observedBefore = event >= 0L && event < sentAt;
            }
            String port = text(input.get("portId"));
            if (observedBefore && !port.isEmpty() && ports.add(port)) {
                result.add(input);
            }
        }
        result.sort(Comparator.comparing(value -> text(value.get("portId"))));
        return result;
    }

    /**
     * Publishes the one function entry shared by every selected output in a
     * goal.  A goal spanning two receiver objects cannot be executed by one
     * region frame and is therefore left for the existing endpoint split.
     */
    private static boolean declareReplayEntry(
            Map<String, Object> goal, MethodEvent entry) {
        if (goal == null || entry == null || entry.method.isEmpty()
                || entry.receiverType.isEmpty()) {
            return false;
        }
        Map<String, Object> declared = row(goal.get(
                edu.uva.liftlab.graphchecker.contract.ExecutionTask
                        .REPLAY_ENTRY));
        if (!declared.isEmpty()) {
            return entry.method.equals(text(declared.get("method")))
                    && entry.receiverType.equals(text(
                    declared.get("receiverClass")));
        }
        goal.put(edu.uva.liftlab.graphchecker.contract.ExecutionTask
                        .REPLAY_ENTRY,
                object("method", entry.method,
                        "receiverClass", entry.receiverType));
        return true;
    }

    /**
     * Boundary label of a relation whose output is a value handed to a cut.
     *
     * <p>It is not a heap write and not a return: the relation ends at the
     * instant the client presents the argument at the declared cut unit, one
     * frame before any transport runs.</p>
     */
    private static final String CUT_ARGUMENT_BOUNDARY =
            "EXACT_CALL_ARGUMENT_AT_CUT";

    /**
     * Closes {@code T_C0}'s request half on the cut argument itself.
     *
     * <p>README section 3 gives a client prefix the shape
     * {@code T_C0(Input, Live_out, Req_out)} and sends {@code Req_out} across
     * the cut through the VM broker.  {@link #directHeapOutputClosure} cannot
     * state that: it is heap-specific by construction, and the only heap cell
     * this value ever reaches is written <em>inside</em> the cut's own callee,
     * which is exactly the merge README's core invariants forbid.  So the
     * demand was real, the refusal was correct, and no closure was on its way
     * - {@code OUTPUT_CLOSURE_CROSSES_CUT} said so by name.</p>
     *
     * <p>This is the closure that was missing.  Everything it reads is
     * already declared on the port by static discovery: the capture is a
     * {@code CALL_ARGUMENT}, at a named argument position, of a named callee,
     * at a named unit of the client's own method.  The relation is the
     * backward slice of the value bound into that argument, and it stops at
     * this occurrence's own declared input ports - the {@code Input} of the same
     * README shape.  Nothing follows the value into the callee, so no
     * transport frame enters the relation and no local case merges across the
     * cut.</p>
     *
     * <p>Scheduling evidence and value evidence stay apart.  The bindings are
     * admitted by {@link AutomaticRegionEdge#schedulableProducerBinding},
     * which a trace-correlated delivery satisfies: it says this
     * fragment has to run before the receiving one can be given anything.  It
     * does not say what value crossed, and this closure never claims one -
     * the value relation is the VM's own export/attach handoff and its
     * {@code VALUE_HANDOFF} ledger edge.</p>
     */
    private static OutputClosureContract cutArgumentOutputClosure(
            Map<String, Object> plan, Map<String, Object> goal,
            Map<String, Object> region, String outputPort,
            List<Map<String, Object>> bindings,
            RefinedFlowIndex refinedFlow, TraceIndex trace,
            int loopBodyBound, List<String> rejectionReasons) {
        if (region == null) return null;
        String occurrenceId = text(plan.get("occurrenceId"));
        String regionId = text(plan.get("regionId"));
        Map<String, Object> port = uniquePort(rows(region.get("outputs")),
                outputPort, occurrenceId);
        if (port == null
                || !CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT.equals(
                text(port.get(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND)))) {
            return null;
        }
        String definitionMethod = text(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        int definitionUnitIndex = integer(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX), -1);
        int argumentIndex = integer(port.get(
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1);
        String declaredCallee = text(port.get("declaredCallee"));
        String javaType = text(port.get("javaType"));
        String cutSiteId = text(port.get(
                CommunicationCatalogContract.CALL_SITE_ID));
        // Both halves of the site have to agree.  The declared cut site and
        // the declared definition unit are written independently, and a port
        // whose capture points at a different unit than its cut names no
        // single site at all.
        if (definitionMethod.isEmpty() || definitionUnitIndex < 0
                || argumentIndex < 0 || declaredCallee.isEmpty()
                || javaType.isEmpty()
                || !symbolicLeafType(javaType)
                || !cutSiteId.equals(definitionMethod + "#u"
                + definitionUnitIndex)) {
            rejectionReasons.add("CUT_ARGUMENT_PORT_INCOMPLETE:"
                    + outputPort);
            return null;
        }

        List<Map<String, Object>> trusted = new ArrayList<>();
        for (Map<String, Object> binding : bindings) {
            if (!occurrenceId.equals(text(binding.get("fromOccurrenceId")))
                    || !AutomaticRegionEdge.schedulableProducerBinding(
                    toJsonTreeFast(binding).getAsJsonObject())) {
                rejectionReasons.add("CUT_ARGUMENT_BINDING_UNSCHEDULABLE:"
                        + outputPort + ":" + text(binding.get("edgeId")));
                return null;
            }
            trusted.add(binding);
        }
        if (trusted.isEmpty()) return null;

        String argumentCell = refinedFlow.cutArgumentCell(regionId,
                definitionMethod, cutSiteId, declaredCallee, argumentIndex);
        if (argumentCell.isEmpty()) {
            rejectionReasons.add("CUT_ARGUMENT_VALUE_CELL_UNRESOLVED:"
                    + outputPort);
            return null;
        }

        long rootCallId = traceEvidenceRootCall(plan);
        List<RuntimeEvent> evaluations = trace.callArgumentEvents(
                trace.subtree(rootCallId), cutSiteId, declaredCallee,
                argumentIndex);
        if (evaluations.isEmpty()) {
            rejectionReasons.add("CUT_ARGUMENT_UNOBSERVED:" + outputPort);
            return null;
        }
        if (evaluations.size() != 1) {
            // Several evaluations of one cut argument inside one activation
            // are several deliveries of one exchange.  Nothing on the
            // delivery row names the caller invocation it belongs to, and
            // README section 1 forbids closing that gap with call order, so
            // the relation is refused by name until the row carries it.
            addBoundInsufficient(rejectionReasons, "CUT_ARGUMENT_OCCURRENCE",
                    outputPort, evaluations.size(), 1);
            return null;
        }
        RuntimeEvent evaluation = evaluations.get(0);

        Set<Long> invocationCalls = trace.exactOutputInvocationCalls(
                rootCallId, evaluation.seq);
        if (invocationCalls == null) {
            rejectionReasons.add("CUT_ARGUMENT_INVOCATION_UNRESOLVED:"
                    + outputPort);
            return null;
        }
        Set<String> corridorMethods = trace.methodNames(invocationCalls);
        Set<String> allowed = new LinkedHashSet<>(
                strings(goal.get("runtimeDefinitionMethods")));
        Set<String> baselineMethods = new LinkedHashSet<>(strings(
                goal.get("baselineObservedMethods")));
        allowed.removeIf(method -> baselineMethods.contains(method)
                && !corridorMethods.contains(method));
        allowed.addAll(corridorMethods);
        if (!allowed.contains(definitionMethod)) return null;

        List<Map<String, Object>> regionInputs = rows(
                region.get("symbolicInputs"));
        List<Map<String, Object>> regionOutputs = rows(
                region.get("outputs"));
        List<Map<String, Object>> branchPolicies = rows(
                region.get("branchPolicies"));
        ReturnSlice argumentSlice = refinedFlow.dependencySlice(
                regionId, occurrenceId, argumentCell, null, allowed,
                regionInputs, regionOutputs, branchPolicies,
                Collections.singleton(definitionMethod),
                evaluation.seq, GuardAdmission.RELATION_INPUT_PORT);
        if (argumentSlice == null) return null;

        List<String> inputPorts = new ArrayList<>(argumentSlice.inputPorts);
        Set<String> methodSet = new LinkedHashSet<>(argumentSlice.methods);
        methodSet.add(definitionMethod);
        methodSet.retainAll(allowed);
        if (methodSet.isEmpty()) return null;
        if (!addReachingAccessorMaterializations(inputPorts, regionInputs,
                occurrenceId, methodSet, evaluation.seq, invocationCalls,
                rejectionReasons, outputPort)) {
            return null;
        }
        List<Map<String, Object>> exactBranches = exactBranchReplay(
                branchPolicies, argumentSlice.branchSites, trace,
                invocationCalls, evaluation.seq, loopBodyBound,
                rejectionReasons, outputPort);
        if (exactBranches == null) return null;
        removeGuardOnlyPathEnablers(inputPorts,
                argumentSlice.guardOnlyInputPorts, regionInputs, occurrenceId,
                outputPort, argumentCell, argumentSlice.branchSites,
                exactBranches, rejectionReasons);
        // A relation whose output does not depend on a single declared input
        // is not this occurrence's relation: it says the request is constant,
        // which would let the campaign run a producer that can never answer
        // a different question than the seed already did.
        if (inputPorts.isEmpty()) {
            rejectionReasons.add("CUT_ARGUMENT_RELATION_HAS_NO_INPUT:"
                    + outputPort);
            return null;
        }

        List<String> staticSites = new ArrayList<>(argumentSlice.staticSites);
        if (!staticSites.contains(cutSiteId)) staticSites.add(cutSiteId);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", outputPort);
        slice.addProperty("outputCell", argumentCell);
        slice.add("inputPorts", stringsJson(inputPorts));
        slice.add("demandedHeapDeclarations", stringsJson(
                argumentSlice.demandedHeapDeclarations));
        slice.add("sites", stringsJson(argumentSlice.branchSites));
        slice.add("staticSites", stringsJson(staticSites));
        slice.add("methods", stringsJson(methodSet));
        slice.addProperty("activationLocalOccurrence", 1);
        slice.addProperty("selectedRuntimeEventSeq", evaluation.seq);
        slice.addProperty("outputBoundaryKind", CUT_ARGUMENT_BOUNDARY);
        addConcretePrimitiveCallReturns(slice, trace, invocationCalls,
                argumentSlice.staticSites, inputPorts, regionInputs,
                evaluation.seq);

        JsonArray edgeIds = new JsonArray();
        Set<String> seenEdges = new LinkedHashSet<>();
        for (Map<String, Object> binding : trusted) {
            String edgeId = text(binding.get("edgeId"));
            if (edgeId.isEmpty() || !seenEdges.add(edgeId)) continue;
            edgeIds.add(edgeId);
        }
        if (edgeIds.size() == 0) return null;
        slice.add("causalEdgeIds", edgeIds);

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE."
                + UUID.nameUUIDFromBytes((occurrenceId + "\n" + outputPort
                + "\n" + cutSiteId + "\n" + declaredCallee + "\n"
                + argumentIndex).getBytes(StandardCharsets.UTF_8)));
        capture.addProperty("captureKind", OutputCaptureSpec.CALL_ARGUMENT);
        capture.addProperty("outputPort", outputPort);
        capture.addProperty("outputCell", argumentCell);
        capture.addProperty("javaType", javaType);
        capture.addProperty("definitionMethod", definitionMethod);
        capture.addProperty("definitionUnitIndex", definitionUnitIndex);
        capture.addProperty("declaredCallee", declaredCallee);
        capture.addProperty("argumentIndex", argumentIndex);
        capture.addProperty("occurrenceScope",
                OutputCaptureSpec.REGION_ACTIVATION_SCOPE);
        capture.addProperty("outputBoundaryKind", CUT_ARGUMENT_BOUNDARY);
        // The same static endpoint assignOutputOccurrenceIdentity derives, so
        // the contract sees one answer here and one answer there.
        capture.addProperty("outputSiteId", OutputCaptureSpec.CALL_ARGUMENT
                + ":" + definitionMethod + "#u" + definitionUnitIndex + ":"
                + declaredCallee + "#arg" + argumentIndex);
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("replayOccurrence", 1);
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());

        try {
            return OutputClosureCodec.singleton(
                    text(plan.get("relationKey")), regionId,
                    declaredOutputPortIds(regionOutputs),
                    outputPort, argumentCell, "REGION_OUTPUT", javaType,
                    slice);
        } catch (IllegalArgumentException refused) {
            // The canonical output-closure contract is the authority on what
            // a producer output may be, and it is asked rather than second
            // guessed.  It admits a port the region minted
            // ("<regionId>.out.<id>") or one the region declared by name, so
            // reaching here means this region did not declare this port at
            // all - not that the port is merely named after its exchange
            // site.  Everything else about the relation resolved, so the
            // refusal is published with the port it names and the relation is
            // left out of the plan: a producer the contract will not carry
            // must not become a goal anything can schedule.
            rejectionReasons.add(GAP_CUT_OUTPUT_PORT_REFUSED + ":"
                    + outputPort);
            return null;
        }
    }

    /** A semantic server return reached its declared response event. */
    private static final String COMMUNICATION_EFFECT_BOUNDARY =
            "DECLARED_COMMUNICATION_EFFECT";

    /**
     * Closes the guarded server interaction at its real normal return.
     * No expression is read from the returned object.  Payload leaves are
     * exported and attached by the VM broker and are composed only from its
     * {@code VALUE_HANDOFF} ledger edge.
     */
    private static OutputClosureContract communicationEffectOutputClosure(
            Map<String, Object> plan, Map<String, Object> goal,
            Map<String, Object> region, String outputPort,
            List<Map<String, Object>> bindings,
            RefinedFlowIndex refinedFlow, TraceIndex trace,
            int loopBodyBound, List<String> rejectionReasons) {
        if (region == null) return null;
        String occurrenceId = text(plan.get("occurrenceId"));
        String regionId = text(plan.get("regionId"));
        Map<String, Object> port = uniquePort(rows(region.get("outputs")),
                outputPort, occurrenceId);
        if (port == null || !CommunicationCatalogContract.CAPTURE_ENTRY_RETURN.equals(text(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND)))) {
            return null;
        }
        String definitionMethod = text(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        String javaType = text(port.get("javaType"));
        if (definitionMethod.isEmpty() || javaType.isEmpty()) {
            rejectionReasons.add("COMMUNICATION_EFFECT_PORT_INCOMPLETE:"
                    + outputPort);
            return null;
        }

        List<Map<String, Object>> trusted = new ArrayList<>();
        for (Map<String, Object> binding : bindings) {
            if (!occurrenceId.equals(text(binding.get("fromOccurrenceId")))
                    || !AutomaticRegionEdge.schedulableProducerBinding(
                    toJsonTreeFast(binding).getAsJsonObject())) {
                rejectionReasons.add("COMMUNICATION_EFFECT_BINDING_UNSCHEDULABLE:"
                        + outputPort + ":" + text(binding.get("edgeId")));
                return null;
            }
            trusted.add(binding);
        }
        if (trusted.isEmpty()) return null;

        long rootCallId = traceEvidenceRootCall(plan);
        RuntimeEvent returned = trace.uniqueNormalMethodExit(rootCallId,
                definitionMethod);
        if (returned == null) {
            rejectionReasons.add("COMMUNICATION_EFFECT_UNOBSERVED:" + outputPort);
            return null;
        }
        Set<Long> invocationCalls = trace.exactOutputInvocationCalls(
                rootCallId, returned.seq);
        if (invocationCalls == null) {
            rejectionReasons.add("COMMUNICATION_EFFECT_INVOCATION_UNRESOLVED:"
                    + outputPort);
            return null;
        }

        Set<String> allowed = new LinkedHashSet<>(strings(
                goal.get("runtimeDefinitionMethods")));
        allowed.addAll(trace.methodNames(invocationCalls));
        allowed.add(definitionMethod);

        String returnCell = definitionMethod + ".return";
        List<Map<String, Object>> regionInputs = rows(
                region.get("symbolicInputs"));
        List<Map<String, Object>> regionOutputs = rows(region.get("outputs"));
        List<Map<String, Object>> branchPolicies = rows(
                region.get("branchPolicies"));
        ReturnSlice returnSlice = refinedFlow.dependencySlice(
                regionId, occurrenceId, returnCell, null, allowed,
                regionInputs, regionOutputs, branchPolicies,
                Collections.singleton(definitionMethod),
                returned.seq, GuardAdmission.RELATION_INPUT_PORT);
        if (returnSlice == null) {
            rejectionReasons.add("COMMUNICATION_EFFECT_GUARD_SLICE_UNRESOLVED:"
                    + outputPort);
            return null;
        }

        List<String> inputPorts = new ArrayList<>(returnSlice.inputPorts);
        Set<String> methodSet = new LinkedHashSet<>(returnSlice.methods);
        methodSet.add(definitionMethod);
        methodSet.retainAll(allowed);
        if (methodSet.isEmpty()) return null;
        if (!addReachingAccessorMaterializations(inputPorts, regionInputs,
                occurrenceId, methodSet, returned.seq, invocationCalls,
                rejectionReasons, outputPort)) {
            return null;
        }
        List<Map<String, Object>> exactBranches = exactBranchReplay(
                branchPolicies, returnSlice.branchSites, trace,
                invocationCalls, returned.seq, loopBodyBound,
                rejectionReasons, outputPort);
        if (exactBranches == null) return null;
        removeGuardOnlyPathEnablers(inputPorts,
                returnSlice.guardOnlyInputPorts, regionInputs, occurrenceId,
                outputPort, returnCell, returnSlice.branchSites,
                exactBranches, rejectionReasons);

        String effectCell = definitionMethod + ".communication.response";
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", outputPort);
        slice.addProperty("outputCell", effectCell);
        slice.add("inputPorts", stringsJson(inputPorts));
        slice.add("demandedHeapDeclarations", stringsJson(
                returnSlice.demandedHeapDeclarations));
        slice.add("sites", stringsJson(returnSlice.branchSites));
        slice.add("staticSites", stringsJson(returnSlice.staticSites));
        slice.add("methods", stringsJson(methodSet));
        slice.addProperty("activationLocalOccurrence", 1);
        slice.addProperty("selectedRuntimeEventSeq", returned.seq);
        slice.addProperty("outputBoundaryKind",
                COMMUNICATION_EFFECT_BOUNDARY);
        addConcretePrimitiveCallReturns(slice, trace, invocationCalls,
                returnSlice.staticSites, inputPorts, regionInputs,
                returned.seq);

        JsonArray edgeIds = new JsonArray();
        Set<String> seenEdges = new LinkedHashSet<>();
        for (Map<String, Object> binding : trusted) {
            String edgeId = text(binding.get("edgeId"));
            if (!edgeId.isEmpty() && seenEdges.add(edgeId)) {
                edgeIds.add(edgeId);
            }
        }
        if (edgeIds.size() == 0) return null;
        slice.add("causalEdgeIds", edgeIds);

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE."
                + UUID.nameUUIDFromBytes((occurrenceId + "\n" + outputPort
                + "\n" + definitionMethod + "\nCOMMUNICATION_EFFECT")
                .getBytes(StandardCharsets.UTF_8)));
        capture.addProperty("captureKind",
                OutputCaptureSpec.COMMUNICATION_EFFECT);
        capture.addProperty("outputPort", outputPort);
        capture.addProperty("outputCell", effectCell);
        capture.addProperty("javaType", javaType);
        capture.addProperty("definitionMethod", definitionMethod);
        capture.addProperty("occurrenceScope",
                OutputCaptureSpec.REGION_ACTIVATION_SCOPE);
        capture.addProperty("outputBoundaryKind",
                COMMUNICATION_EFFECT_BOUNDARY);
        capture.addProperty("outputSiteId",
                OutputCaptureSpec.COMMUNICATION_EFFECT
                + ":" + definitionMethod);
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("replayOccurrence", 1);
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());

        try {
            return OutputClosureCodec.singleton(
                    text(plan.get("relationKey")), regionId,
                    declaredOutputPortIds(regionOutputs), outputPort,
                    effectCell, "INTERACTION_EVENT", javaType, slice);
        } catch (IllegalArgumentException refused) {
            rejectionReasons.add(GAP_CUT_OUTPUT_PORT_REFUSED + ":"
                    + outputPort);
            return null;
        }
    }

    /** Every output port id the region declared, exactly as declared. */
    private static List<String> declaredOutputPortIds(
            List<Map<String, Object>> regionOutputs) {
        List<String> ids = new ArrayList<>();
        for (Map<String, Object> port : regionOutputs) {
            String id = text(port.get("portId"));
            if (!id.isEmpty()) ids.add(id);
        }
        return ids;
    }

    /**
     * A declared cut output the canonical closure contract will not carry.
     *
     * <p>Named rather than folded into {@code OUTPUT_CLOSURE_CROSSES_CUT},
     * because the two say different things: that one means no closure exists,
     * this one means the closure exists and the wire contract refuses to
     * state it.</p>
     */
    static final String GAP_CUT_OUTPUT_PORT_REFUSED =
            "CUT_OUTPUT_PORT_OUTSIDE_CLOSURE_CONTRACT";

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
            String occurrenceId, Set<String> selectedMethods,
            long outputBoundarySeq) {
        addReachingAccessorMaterializations(inputPorts, regionInputs,
                occurrenceId, selectedMethods, outputBoundarySeq, null,
                null, "");
    }

    private static boolean addReachingAccessorMaterializations(
            List<String> inputPorts,
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
            if (!boundTo(candidate, occurrenceId)
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
            if (ambiguousEndpoints.contains(selected.getKey())) {
                // Two ports of one endpoint at one event are not one
                // materialization; neither is chosen, and the input the
                // relation therefore does not carry is named.
                rejectionReasons.add("ACCESSOR_MATERIALIZATION_AMBIGUOUS:"
                        + outputPort + ":"
                        + selected.getKey().replace('\n', '|'));
                continue;
            }
            String port = text(selected.getValue().get("portId"));
            if (!port.isEmpty() && !inputPorts.contains(port)) {
                inputPorts.add(port);
            }
        }
        return true;
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
            String port = text(candidate.get("portId"));
            if (!admitted.contains(port)
                    || !"ACCESSOR_RETURN".equals(
                    text(candidate.get("sourceKind")))) {
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
            if (selected.size() > loopBodyBound) {
                // Truncating an exact demanded branch stream changes the
                // state relation.  Let the caller reject this closure so the
                // declared bound can be raised explicitly.
                //
                // The bound is the campaign's own, never {@code
                // LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS}: README section 5
                // makes K_L per loop and that constant is only what a loop
                // declaring none inherits.  Reading it here refused a
                // correct closure the moment a loop legitimately declared
                // more, which is the HDFS-11741 shape - two retained loops
                // measured at 20-29 and 55-59 body executions.
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
                occurrences.add(object("occurrence", index + 1,
                        "outcome", event.outcome,
                        "eventSeq", event.seq,
                        "callId", event.callId));
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
        String site = text(selected.get("staticAccessSiteId"));
        // The static endpoint identifies the relation.  Any recorded
        // occurrence is provenance only; semantic-boundary replay does not
        // require the seed's dynamic count.
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

    /** The one region-level declaration of a cut port, never an instance. */
    private static Map<String, Object> uniqueDeclaredPort(
            List<Map<String, Object>> ports, String portId) {
        Map<String, Object> match = null;
        for (Map<String, Object> port : ports) {
            if (!portId.equals(text(port.get("portId")))
                    || !declaredCutPort(port)
                    || !text(port.get("occurrenceId")).isEmpty()) {
                continue;
            }
            if (match != null) return null;
            match = port;
        }
        return match;
    }

    /**
     * The one port of this activation with {@code portId}, or null when the
     * activation has none or several.  One region can be active on several
     * threads at once, so a port id alone is not an address.
     */
    private static Map<String, Object> uniquePort(
            List<Map<String, Object>> ports, String portId,
            String occurrenceId, boolean input) {
        Map<String, Object> match = null;
        for (Map<String, Object> port : ports) {
            if (!portId.equals(text(port.get("portId")))
                    || !(input ? boundToInput(port, occurrenceId)
                    : boundToOutput(port, occurrenceId))) {
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
                    && !text(match.get("portId")).equals(
                    text(input.get("portId")))) {
                return null;
            }
        }
        return match;
    }

    /**
     * Proves the minimal state-merge shape used by modeled RPC failure:
     * the exact field pre-state is read, an explicit symbolic fault decides
     * whether the update runs, and the recorded write follows that decision.
     * Such a relation is observed once at normal region exit so both the
     * refreshed and retained-state paths expose the same output endpoint.
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
                    && selected.contains(text(input.get("portId")))
                    && RuntimeSelectedRegionFinalizer
                    .EXPLICIT_SYMBOLIC_FAULT.equals(
                    text(input.get("sourceKind")))
                    && seq > preStateSeq && seq < outputEventSeq) {
                faultSeq = Math.min(faultSeq, seq);
            }
        }
        if (faultSeq == Long.MAX_VALUE) return false;
        for (Map<String, Object> branch : branches) {
            long seq = longNumber(branch.get("selectedRuntimeEventSeq"),
                    -1L);
            if ("PATH_ASSUMPTION".equals(text(branch.get("policy")))
                    && seq > faultSeq && seq < outputEventSeq) {
                return true;
            }
        }
        return false;
    }

    private static void addIfAllowed(List<String> methods,
                                     Set<String> allowed, String method) {
        if (!method.isEmpty() && allowed.contains(method)
                && !constructor(method) && !methods.contains(method)) {
            methods.add(method);
        }
    }

    /**
     * Keeps a producer's observed reachability guards concrete when their
     * symbolic-state authority belongs to a different output mutation.
     *
     * <p>The value/control distinction is already available from
     * {@link RefinedFlowIndex#dependencySlice}: the initial backward slice
     * supplies value inputs and the existing guard fixpoint adds control
     * inputs.  This method only consumes that provenance; it performs no new
     * graph search.  The guard and its observed replay outcome remain in the
     * member slice.</p>
     */
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
            String site = text(branch.get("siteId"));
            if (!selectedBranchSites.contains(site)
                    || !"EXPLORE".equals(text(branch.get("policy")))
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
            String port = text(input.get("portId"));
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
        // A dependency this relation no longer has is stated by name.  The
        // removal is deliberate - the guard it enabled is already replayed -
        // but a reader cannot tell a port that was never in the slice from
        // one this pass took out unless the removal says so.
        for (String port : removed) {
            droppedReasons.add("GUARD_ONLY_PATH_ENABLER_REMOVED:"
                    + outputPort + ":" + port);
        }
    }

    private static boolean guardOnlyBoundedFrontier(
            Map<String, Object> input, String outputPort, String outputCell,
            Set<String> observedPrefixGuards) {
        if (!"ACCESSOR_RETURN".equals(text(input.get("sourceKind")))
                || !DependencyRole.VALUE_FRONTIER.equals(
                text(input.get("dependencyRole")))
                || !"BOUNDED_STATE_FRONTIER".equals(
                text(input.get("symbolicDemand")))
                || !"STATIC_ACCESSOR_SEMANTIC_MUTATION_GUARD_V1".equals(
                text(input.get("boundedStateFrontierAuthority")))
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

    private static List<String> targetProjectionBlockers(
            Map<String, Object> region, String occurrenceId,
            ReturnSlice targetSlice, List<Map<String, Object>> symbolize,
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

    /**
     * The observed event that decided this occurrence's target.
     *
     * <p>Several eligible sites guarding <em>one</em> throw are the conjuncts
     * of one predicate - {@code if (p && q) throw} is two conditional sites -
     * so the boundary is the last of them the recording actually reached, not
     * a choice between them.  A conjunct the seed never recorded a fatal
     * prefix for is a conjunct, not a rival target, and is skipped; a target
     * whose recording names no such event at all still fails closed, which is
     * what {@code TARGET-1} requires of missing target evidence.</p>
     */
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

    /**
     * Returns the exact observed failure boundary used to cut target inputs.
     * Ambiguous or incomplete target evidence remains a goal-level blocker in
     * {@link #targetProjectionBlockers}; the negative result here prevents an
     * uncertain occurrence from being mistaken for a usable time bound.
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
        String site = text(branch.get("siteId"));
        List<Map<String, Object>> contexts = rows(
                seed.get("fatalPrefixContexts"));
        if (!contexts.isEmpty()) {
            List<Map<String, Object>> matching = new ArrayList<>();
            for (Map<String, Object> context : contexts) {
                if (site.equals(text(context.get("siteId")))) {
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
                    text(context.get("authority")))) {
                throw new IllegalArgumentException(
                        "FATAL_PREFIX_AUTHORITY_MISSING");
            }
            int ordinal = integer(context.get("occurrence"), -1);
            long eventSeq = longNumber(context.get("eventSeq"), -1L);
            if (ordinal < 1 || eventSeq < 0L) {
                throw new IllegalArgumentException(
                        "FATAL_PREFIX_OCCURRENCE_INVALID");
            }
            int selectedOrdinal = integer(branch.get(
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
        int ordinal = integer(branch.get("selectedOccurrence"), -1);
        long eventSeq = longNumber(branch.get(
                "selectedRuntimeEventSeq"), -1L);
        if (ordinal < 1 || eventSeq < 0L) {
            throw new IllegalArgumentException(
                    "FATAL_PREFIX_BOUNDARY_MISSING");
        }
        return eventSeq;
    }

    /**
     * Whether this activation plans a target-reach closure.
     *
     * <p>{@code selection} belongs to the static region skeleton, so every
     * concurrent activation of an exception-context region inherits it -
     * including the producer threads that only fed the activation that
     * failed.  Reaching the failure site is activation-local evidence, so
     * only the activations whose own trace observed one of the region's
     * {@code failureTarget} sites plan a target-reach closure; the others
     * keep their ordinary output-relation closure and remain composable
     * producers.  A region that declares no failure-target site has nothing
     * to attest and stays exactly as selected.</p>
     */
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
                && !text(branch.get("siteId")).isEmpty();
    }

    /**
     * Fails closed when the identity this planner minted disagrees with the
     * one the region finalizer already minted for the same activation.  Both
     * stages run {@link OccurrenceMinter} over the same ordered seeds, so a
     * mismatch means the two stages disagree about a source or about the
     * observed activation order - never something to reconcile silently.  A
     * seed with no stamp came from a planner-only caller that never ran the
     * finalizer.
     */
    private static void requireFinalizedOccurrence(Map<String, Object> seed,
                                                   String occurrenceId) {
        String finalized = text(seed.get("occurrenceId"));
        if (!finalized.isEmpty() && !finalized.equals(occurrenceId)) {
            throw new IllegalArgumentException("runtime activation occurrence "
                    + "disagrees with the finalized identity: " + finalized
                    + " != " + occurrenceId);
        }
    }

    /**
     * True when this row is bound to the occurrence, comparing occurrence
     * identity only.
     */
    private static boolean boundTo(Map<String, Object> row,
                                   String occurrenceId) {
        return occurrenceId.equals(text(row.get("occurrenceId")));
    }

    /**
     * True when this row is the named occurrence's input-side port.
     *
     * <p>A declared cut port is answered differently from a heap port, and it
     * has to be.  {@link OccurrenceMinter#bindPorts} is the only thing that
     * stamps an {@code occurrenceId} on a port row, and it keys on the
     * recorded {@code rootCallId} of the access that produced the port - which
     * a declaration does not have and must not have: README section 2's
     * {@code exchangeSiteKey} is pure static identity, and a cut port is a
     * fact about the <em>region</em>, stated before any activation of it ran.
     * Comparing its (empty) stamp against an activation's identity therefore
     * answered "no" for every declared port and every occurrence, which is
     * why no {@code Req_in}, {@code Resp_in} or {@code Live_in} ever reached
     * {@link #symbolize} and every communicating relation stood over an
     * empty input set.</p>
     *
     * <p>A region-level declaration belongs to every activation of its
     * region, so it is bound here.  The occurrence-owned copies the delivery
     * finalizer mints under the same declared id name their own activation
     * and are matched exactly, so one activation never reads another's.</p>
     */
    private static boolean boundToInput(Map<String, Object> port,
                                        String occurrenceId) {
        if (declaredCutPort(port)) {
            String owned = text(port.get("occurrenceId"));
            return owned.isEmpty() || owned.equals(occurrenceId);
        }
        return occurrenceId.equals(text(port.get("occurrenceId")));
    }

    /**
     * The declared communication ports this region hands to the VM, and the
     * site each is handed at.
     *
     * <p>Static discovery already stated all four sites - the client's cut
     * argument and cut return, the server entry's parameter and return - as
     * the capture kind of the port it declared.  This restates them as the
     * export/attach obligations of one occurrence so instrumentation has a
     * unit to rewrite and the replay has a port to name.  A port whose
     * declaration is incomplete contributes nothing rather than a site
     * derived from something else.</p>
     */
    private static List<Map<String, Object>> communicationHandoffSites(
            Map<String, Object> region) {
        Map<String, Map<String, Object>> byRole = new LinkedHashMap<>();
        for (String member : new String[]{"symbolicInputs", "outputs"}) {
            String regionSide = "symbolicInputs".equals(member)
                    ? "IN" : "OUT";
            for (Map<String, Object> port : rows(region.get(member))) {
                if (!declaredCutPort(port)
                        || !DependencyRole.VALUE_FRONTIER.equals(
                        effectiveDependencyRole(port,
                                text(port.get("javaType"))))) {
                    continue;
                }
                Map<String, Object> site = communicationHandoffSite(
                        port, regionSide);
                if (site != null) {
                    byRole.putIfAbsent(text(site.get(
                            CommunicationHandoffSpec.ROLE)) + "\n"
                            + text(site.get(
                            CommunicationCatalogContract.PORT_ID)), site);
                }
            }
        }
        return new ArrayList<>(byRole.values());
    }

    /**
     * True only when the cut argument itself is one scalar symbolic value.
     * Structured parents remain topology carriers; their explicitly declared
     * component leaves are recognized separately by
     * {@link #handoffBoundComponentPort}.
     */
    private static boolean symbolicCutArgumentPort(
            Map<String, Object> region, String portId, String occurrenceId) {
        Map<String, Object> port = uniquePort(rows(region.get("outputs")),
                portId, occurrenceId);
        return port != null && symbolicLeafType(text(port.get("javaType")));
    }

    /** One declared port's handoff site, or {@code null}. */
    private static Map<String, Object> communicationHandoffSite(
            Map<String, Object> port, String regionSide) {
        String capture = text(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        boolean manualCarrier = !text(port.get(
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_CLASS))
                .isEmpty();
        String role;
        if (manualCarrier && "OUT".equals(regionSide)) {
            role = CommunicationHandoffSpec.ROLE_EXPORT;
        } else if (manualCarrier && "IN".equals(regionSide)) {
            role = CommunicationHandoffSpec.ROLE_ATTACH;
        } else if (CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT.equals(capture)
                || CommunicationCatalogContract.CAPTURE_ENTRY_RETURN.equals(
                capture)) {
            role = CommunicationHandoffSpec.ROLE_EXPORT;
        } else if (CommunicationCatalogContract.CAPTURE_ENTRY_PARAMETER
                .equals(capture)
                || CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(
                capture)) {
            role = CommunicationHandoffSpec.ROLE_ATTACH;
        } else {
            return null;
        }
        Map<String, Object> site = new LinkedHashMap<>();
        site.put("schemaVersion", CommunicationHandoffSpec.SCHEMA_VERSION);
        site.put("kind", CommunicationHandoffSpec.KIND);
        site.put(CommunicationHandoffSpec.ROLE, role);
        for (String field : new String[]{
                CommunicationCatalogContract.PORT_ID,
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                CommunicationCatalogContract.PORT_DIRECTION,
                CommunicationCatalogContract.PORT_JAVA_TYPE,
                CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                CommunicationCatalogContract.PORT_COMPONENT_OF,
                CommunicationCatalogContract.PORT_ENCODING_AUTHORITY,
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_CLASS,
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_FIELD,
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_DESCRIPTOR,
                CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                CommunicationCatalogContract.DECLARED_CALLEE}) {
            String value = text(port.get(field));
            if (!value.isEmpty()) site.put(field, value);
        }
        Object handoffPath = port.get(
                CommunicationCatalogContract.PORT_HANDOFF_PATH);
        if (handoffPath instanceof List<?>
                && !((List<?>) handoffPath).isEmpty()) {
            site.put(CommunicationCatalogContract.PORT_HANDOFF_PATH,
                    handoffPath);
        }
        int unitIndex = integer(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX), -1);
        int argumentIndex = integer(port.get(
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1);
        // A server-entry site is addressed by its method and position; a cut
        // site by its unit and callee.  Writing an index the capture does not
        // declare would name a unit of another site.
        boolean entrySite =
                CommunicationCatalogContract.CAPTURE_ENTRY_PARAMETER.equals(
                        capture)
                        || CommunicationCatalogContract.CAPTURE_ENTRY_RETURN
                        .equals(capture);
        if (!entrySite && unitIndex >= 0) {
            site.put(CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX,
                    unitIndex);
        }
        if (argumentIndex >= 0
                && !CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(
                capture)
                && !CommunicationCatalogContract.CAPTURE_ENTRY_RETURN.equals(
                capture)) {
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
                .equals(text(port.get("sourceKind")))
                && CommunicationCatalogContract.declaredPortId(
                text(port.get("portId")));
    }

    /**
     * True when this row is the named occurrence's output-side port.
     *
     * <p>Deliberately not widened the way {@link #boundToInput} is.  The
     * output side already has an activation-owned answer:
     * {@code RuntimeSelectedRegionFinalizer.occurrenceOwnedCutPort} mints one
     * stamped copy of a declared cut port per exporting occurrence, and the
     * region-level declaration stays beside it.  Admitting both would give
     * {@link #uniquePort} two matches for one id and turn every exact output
     * closure on a cut argument into a silent null.</p>
     */
    private static boolean boundToOutput(Map<String, Object> port,
                                         String occurrenceId) {
        return occurrenceId.equals(text(port.get("occurrenceId")));
    }

    private static void copyBindingContext(Map<String, Object> binding,
                                           Map<String, Object> edge,
                                           Map<String, Object> fromPlan,
                                           Map<String, Object> toPlan) {
        copyContextLong(binding, "fromLaneId", edge, fromPlan, "laneId");
        copyContextLong(binding, "fromSpanId", edge, fromPlan, "spanId");
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

    /**
     * The symbolic inputs one activation of a region is planned over.
     *
     * <p>Two populations, and they are read differently because they are
     * different things.  A heap port is an observed access and its site comes
     * from what the run recorded; a declared cut port is a static statement
     * about the cut - README section 3's {@code Req_in}, {@code Resp_in},
     * {@code Live_in} - and its site comes from the capture the declaration
     * carries.  Running a declaration through the heap derivations answers
     * about a value it does not describe.</p>
     */
    private static List<Map<String, Object>> symbolize(
            List<Map<String, Object>> ports, String occurrenceId,
            String activationId, Result gaps) {
        // A declared cut port can appear twice: the region-level declaration
        // and, once a recorded delivery named it, this
        // occurrence's own stamped copy of it.  They are one port, and the
        // stamped one is the more specific statement, so it is the one read.
        Set<String> occurrenceOwnedCutPorts =
                occurrenceOwnedCutPortIds(ports, occurrenceId);
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> port : ports) {
            if (!boundToInput(port, occurrenceId)) {
                continue;
            }
            if (declaredCutPort(port)) {
                if (text(port.get("occurrenceId")).isEmpty()
                        && occurrenceOwnedCutPorts.contains(
                        text(port.get("portId")))) {
                    continue;
                }
                // A declared cut port is not a heap access.  It has no field
                // path, no root and no recorded site, so every derivation
                // below would answer about a value it does not describe:
                // leafType([]) is java.lang.Object and no rootKind means
                // RECEIVER_FIELD.  Its own declaration says where it is read.
                Map<String, Object> declared = declaredCutPortAction(port,
                        occurrenceId, activationId, gaps);
                if (declared != null) {
                    result.add(declared);
                }
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
            if (RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT.equals(
                    text(port.get("sourceKind")))) {
                javaType = "boolean";
            }
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
            if (RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT.equals(
                    text(port.get("sourceKind")))) {
                action.put("location", "CALL_RETURN");
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
            action.put("dependencyRole",
                    effectiveDependencyRole(action,
                            text(action.get("javaType"))));
            result.add(action);
        }
        return result;
    }

    /**
     * Names the value cell of every declared cut port of one region, once.
     *
     * <p>A cell is how every other stage refers to a value: the backward
     * slice's boundary map is keyed on it, and so is the definition index the
     * scheduler resolves an action against.  A declared cut port arrives
     * without one, because static discovery names ports and not cells, and a
     * port with no cell is invisible to both - which is why the server
     * fragment's target slice could reach the transport's heap read and never
     * the declaration that supersedes it.</p>
     *
     * <p>The cell is derived from the declaration alone and stamped on the
     * port row itself, so the slice and {@link #symbolize} read one answer
     * rather than two derivations of it.  A declaration that names no
     * addressable site gets none, and stays invisible on purpose.</p>
     */
    private static void declareCutPortCells(Map<String, Object> region) {
        for (String member : new String[]{"symbolicInputs", "outputs"}) {
            for (Map<String, Object> port : rows(region.get(member))) {
                if (!declaredCutPort(port)
                        || !text(port.get("cell")).isEmpty()) {
                    continue;
                }
                String cell = declaredCutPortCell(port);
                if (!cell.isEmpty()) port.put("cell", cell);
            }
        }
    }

    /** The value cell a declared cut port's capture names, or {@code ""}. */
    private static String declaredCutPortCell(Map<String, Object> port) {
        String capture = text(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        String definitionMethod = text(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        String javaType = text(port.get("javaType"));
        if (CommunicationCatalogContract.CAPTURE_ENTRY_PARAMETER.equals(
                capture)) {
            int argumentIndex = integer(port.get(
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
                || CommunicationCatalogContract.CAPTURE_ENTRY_RETURN.equals(
                capture)) {
            // The project-wide call-return cell: what the cut call handed
            // back, named by the callee whose frame produced it.
            String callee = CommunicationCatalogContract.CAPTURE_CALL_RETURN
                    .equals(capture) ? text(port.get("declaredCallee"))
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
                    && occurrenceId.equals(text(port.get("occurrenceId")))) {
                result.add(text(port.get("portId")));
            }
        }
        return result;
    }

    /**
     * The symbolize action of one declared cut port, or {@code null} with a
     * named gap.
     *
     * <p>A relation is asked for its own ports - a server occurrence for its
     * request in and response out, a client for what it sent and received.
     * The declaration alone gives each of them a name; the capture the static
     * planner stamped on it gives it a <em>site</em>, and the site is what
     * decides whether the relation is about this occurrence at all.  Reading
     * a declared port through the heap-port derivations below would answer
     * with the transport's own field instead - the frame a local relation
     * must never contain.</p>
     *
     * <p>Nothing is invented here.  A capture this planner cannot address is
     * refused by name rather than turned into an input, because a relation
     * stated over an input nothing produced reads as complete and is worse
     * than an empty one.</p>
     */
    private static Map<String, Object> declaredCutPortAction(
            Map<String, Object> port, String occurrenceId,
            String activationId, Result gaps) {
        String portId = text(port.get("portId"));
        // A structured transport component has no Java argument/local capture
        // of its own.  The application bridge exports and attaches its exact
        // VM expression by handoff leaf; creating a fresh Java input here
        // would introduce a second, unrelated symbolic authority.
        if (!text(port.get(CommunicationCatalogContract.PORT_COMPONENT_OF))
                .isEmpty()
                && !text(port.get(
                CommunicationCatalogContract.PORT_ENCODING_AUTHORITY))
                .isEmpty()) {
            return null;
        }
        String capture = text(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        String definitionMethod = text(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        String javaType = text(port.get("javaType"));
        if (capture.isEmpty()) {
            addCommunicationPortGap(gaps, GAP_COMMUNICATION_PORT_CAPTURE_UNDECLARED,
                    "PORT_DECLARES_NO_RUNTIME_CAPTURE", activationId,
                    definitionMethod, portId, occurrenceId);
            return null;
        }
        if (javaType.isEmpty()) {
            addCommunicationPortGap(gaps, GAP_COMMUNICATION_PORT_CAPTURE_UNDECLARED,
                    "PORT_DECLARES_NO_ERASED_TYPE", activationId,
                    definitionMethod, portId, occurrenceId);
            return null;
        }
        if (definitionMethod.isEmpty()) {
            addCommunicationPortGap(gaps, GAP_COMMUNICATION_PORT_CAPTURE_UNDECLARED,
                    "CAPTURE_" + capture + "_NAMES_NO_DEFINITION_METHOD",
                    activationId, "", portId, occurrenceId);
            return null;
        }
        Map<String, Object> action = new LinkedHashMap<>(port);
        action.put("symbol", portId);
        action.put("observed", true);
        action.put("javaType", javaType);
        // Both names for the same fact, because the two readers differ: an
        // action's defining frame is "method", while a root-entry action
        // reads "rootMethod".  A declared cut port states one method and
        // states it under both, so neither reader has to guess.
        action.put("method", definitionMethod);
        action.put("rootMethod", definitionMethod);
        if (CommunicationCatalogContract.CAPTURE_ENTRY_PARAMETER.equals(
                capture)) {
            int argumentIndex = integer(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1);
            if (argumentIndex < 0) {
                addCommunicationPortGap(gaps, GAP_COMMUNICATION_PORT_CAPTURE_UNDECLARED,
                        "ENTRY_PARAMETER_NAMES_NO_POSITION", activationId,
                        definitionMethod, portId, occurrenceId);
                return null;
            }
            // Req_in is parameter <n> of the resolved server entry, one frame
            // above the delivery and inside the server fragment by
            // construction.  The cell is the project-wide parameter cell so a
            // consumer reads the method and the position off one string
            // instead of re-deriving either.
            action.put("location", "ARGUMENT");
            action.put(CommunicationCatalogContract.PORT_ARGUMENT_INDEX,
                    argumentIndex);
            action.put("index", argumentIndex);
            action.put("cell", declaredCutPortCell(port));
        } else if (CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(
                capture)) {
            String declaredCallee = text(port.get("declaredCallee"));
            int unitIndex = integer(port.get(CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX), -1);
            if (declaredCallee.isEmpty() || unitIndex < 0) {
                addCommunicationPortGap(gaps, GAP_COMMUNICATION_PORT_CAPTURE_UNDECLARED,
                        "CALL_RETURN_NAMES_NO_CALLEE_OR_UNIT", activationId,
                        definitionMethod, portId, occurrenceId);
                return null;
            }
            // Resp_in is the value the cut call returned, read at the cut
            // unit in the client's own frame - one frame above the transport
            // and inside the client region by construction.
            action.put("location", "CALL_RETURN");
            action.put("cell", declaredCutPortCell(port));
            action.put("unitIndex", unitIndex);
        } else {
            // CALL_ARGUMENT and ENTRY_RETURN describe where a fragment
            // *writes* a value at its boundary.  Neither says where a
            // fragment receives one, so an input-side row carrying one is a
            // declaration this planner must not read as an input.
            addCommunicationPortGap(gaps, GAP_COMMUNICATION_PORT_CAPTURE_UNDECLARED,
                    "CAPTURE_" + capture + "_IS_AN_OUTPUT_SIDE_SITE",
                    activationId, definitionMethod, portId, occurrenceId);
            return null;
        }
        action.put("dependencyRole",
                effectiveDependencyRole(action, javaType));
        return action;
    }

    /** One runtime gap about a declared cut port of one activation. */
    private static void addCommunicationPortGap(Result gaps, String kind,
                                          String reason, String activationId,
                                          String method, String siteId,
                                          String detail) {
        if (gaps == null) return;
        gaps.gaps.add(gap(kind, reason,
                activationId, method, siteId, detail));
    }

    /**
     * Separates semantic solver leaves from the object graph needed only to
     * replay a region.  Static slicing may conservatively label an object
     * read as a value; once its exact Java type is known there is no reason to
     * recursively demand a producer for that reference.  Bounded container
     * state is the deliberate exception: its member relation is a semantic
     * value even though the carrier itself is a reference.
     */
    static String effectiveDependencyRole(Map<String, Object> port,
                                          String javaType) {
        String demand = text(port.get("symbolicDemand"));
        if ("BOUNDED_CONTAINER_STATE".equals(demand)) {
            return DependencyRole.VALUE_FRONTIER;
        }
        String declared = text(port.get("dependencyRole"));
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

    /**
     * Binds the exact ports of one region occurrence.  Both the selection
     * and the binding are scoped by {@code occurrenceId}, so no port table
     * entry is selected or addressed by a trace call id.
     */
    private static void registerExactPorts(
            Map<String, Object> region, String occurrenceId,
            Map<String, String> exactPorts) {
        registerExactPorts(rows(region.get("symbolicInputs")),
                occurrenceId, "IN", exactPorts);
        registerExactPorts(rows(region.get("outputs")),
                occurrenceId, "OUT", exactPorts);
    }

    private static void registerExactPorts(
            List<Map<String, Object>> ports,
            String occurrenceId, String direction,
            Map<String, String> exactPorts) {
        for (Map<String, Object> port : ports) {
            if (!("IN".equals(direction)
                    ? boundToInput(port, occurrenceId)
                    : boundToOutput(port, occurrenceId))) {
                continue;
            }
            String id = text(port.get("portId"));
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
                    + text(edge.get("edgeId")) + " has no exact "
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
            String site = text(policy.get("siteId"));
            List<RuntimeEvent> occurrences = bySite.getOrDefault(site,
                    Collections.emptyList());
            List<Map<String, Object>> encoded = new ArrayList<>();
            for (int index = 0; index < occurrences.size(); index++) {
                encoded.add(object("occurrence", index + 1, "outcome",
                        occurrences.get(index).outcome, "eventSeq",
                        occurrences.get(index).seq));
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
            }
            branch.put("occurrences", encoded);
            result.add(branch);
        }
        return result;
    }

    /**
     * The replay address of one activation: its stable selected source and
     * region root, plus the causal anchor that activation was entered under.
     *
     * <p>There is deliberately no invocation ordinal here.  An ordinal names
     * a <em>position</em> in a sequence of activations, so a replay in which
     * a flipped branch adds or removes an earlier activation of the same root
     * silently re-points every later selector at a different occurrence -
     * which is exactly the mis-selection this address replaces.  Every
     * component below is a name the recording and the replay can both state
     * independently of how many activations preceded them.</p>
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
        result.put(CAUSAL_ANCHOR, causalAnchor(source, requestApi));
        return result;
    }


    @SuppressWarnings("unchecked")

    /** Selector member holding the incoming causal anchor. */
    static final String CAUSAL_ANCHOR = "causalAnchor";
    /** The activation ran on a source the application registered. */
    static final String ANCHOR_REGISTERED_SOURCE = "REGISTERED_SOURCE";
    /** The activation registered no source and ran under the default. */
    static final String ANCHOR_UNREGISTERED_SOURCE = "UNREGISTERED_SOURCE";

    /**
     * What causally produced this activation, named rather than counted.
     *
     * <p>The stable logical node and lifecycle epoch are always present.  A
     * unique application-declared request API is included only when the
     * selected target/effect itself carried it.  This separates two same-root
     * activations serving different causal episodes without relying on a
     * session id or an invocation/request ordinal.  Long-lived background
     * services which declare no such scope retain the source-only address and
     * are selected by their demanded effect evidence.</p>
     */
    private static Map<String, Object> causalAnchor(SourceRef source,
                                                    String requestApi) {
        Map<String, Object> anchor = new LinkedHashMap<>();
        anchor.put("sourceKey", source.key());
        anchor.put("kind", UNREGISTERED_SOURCE.key().equals(source.key())
                ? ANCHOR_UNREGISTERED_SOURCE : ANCHOR_REGISTERED_SOURCE);
        if (requestApi != null && !requestApi.isEmpty()) {
            anchor.put("requestApi", requestApi);
        }
        return anchor;
    }

    private static SourceRef source(MethodEvent event) {
        return sourceOf(event.source);
    }

    /**
     * Authority of a source taken from the first stamped frame inside the
     * activation rather than from its root frame.
     */
    static final String UPGRADED_SOURCE_AUTHORITY =
            "FIRST_STAMPED_FRAME_INSIDE_ACTIVATION";
    /** Reason published when one activation ran under two logical sources. */
    static final String AMBIGUOUS_SOURCE_REASON =
            "SEVERAL_REGISTERED_TRACE_SOURCES_INSIDE_ACTIVATION";

    /**
     * Every distinct logical source the frames of one activation carry, in
     * recorded order.
     *
     * <p>An application registers its source and opens its request scope
     * <em>inside</em> its entry method, so the root frame of a thread-entry
     * activation is entered before either exists and carries no source at
     * all.  Taking the region root's stamp therefore published
     * {@code workload/unregistered} for an activation whose very next frame
     * names its node - which is a fallback presented as an attribution, the
     * thing README Step 4 replaces with direct stamping.  Reading the frames
     * inside the activation is still direct recorded evidence: nothing is
     * inferred from a thread name, a method name or a neighbouring
     * activation.  Two different sources inside one activation are refused by
     * name instead of picking the first.</p>
     */
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

    /**
     * The source that owns one activation: its root frame's stamp, or the
     * unique stamp its own frames carry when the root has none.
     *
     * <p>The stamp is authoritative here because the trace re-attributes
     * every frame to the owner its receiver registered before planning
     * starts.  Resolving it a second time in this method is what the
     * previous attempt did, against an in-process map the load path had
     * already cleared - it never once matched.</p>
     */
    private static SourceRef activationSource(MethodEvent root,
                                              List<SourceRef> stamped) {
        if (root.source != null) return root.source;
        return stamped.size() == 1 ? stamped.get(0) : UNREGISTERED_SOURCE;
    }

    /**
     * Total logical scope of one traced event.  A workload that never
     * registered a stable source is one logical source: correlation must
     * never merge two registered sources, and must never split a baseline
     * run that carries no source registration at all.
     */
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

    /**
     * The recorded root call of this plan's activation.  It is trace
     * evidence used to walk the observed call tree; it never selects,
     * addresses, or distinguishes an activation.
     */
    private static long traceEvidenceRootCall(Map<String, Object> plan) {
        return longNumber(row(plan.get("traceEvidence")).get("rootCallId"),
                -1L);
    }

    /**
     * Which path assumptions a backward slice may keep.
     *
     * <p>A guard classified {@code EXPLORE} is always part of the relation.
     * A {@code PATH_ASSUMPTION} was demoted by the region-wide demand scope,
     * which is computed from the failure anchors before any producer demand
     * exists, so it cannot know that a client prefix now has to state its own
     * cut argument.  The two modes below are the only ways such a guard is
     * readmitted, and each names the evidence that readmits it.</p>
     */
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
        /**
         * region\nmethod\nsite\ncallee\nargumentIndex -&gt; the caller-side
         * value cells bound into that exact argument.
         *
         * <p>A cut argument is the only output of a client prefix that is
         * never written to the heap, so the heap indices above cannot find
         * it.  The parameter-identity edge at the cut unit is what states
         * where the value comes from, and it is attributed to the
         * <em>caller</em>: reading it keeps the relation one frame short of
         * the transport instead of following the value into the callee.</p>
         */
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
         * The caller-side value cell handed to one declared cut argument.
         *
         * <p>The answer has to be unique: two cells bound into one argument
         * position at one unit is either an unmerged alias or a graph the
         * region never disambiguated, and choosing between them by anything
         * available here would be a guess.  An ambiguous or absent argument
         * therefore returns nothing and the caller refuses by name.</p>
         */
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
                String regionId, String occurrenceId,
                String outputCell,
                Map<String, Object> exactHeapOutput,
                Set<String> allowedMethods,
                List<Map<String, Object>> inputs,
                List<Map<String, Object>> outputs,
                List<Map<String, Object>> branchPolicies,
                Set<String> seedMethods) {
            return dependencySlice(regionId, occurrenceId,
                    outputCell,
                    exactHeapOutput, allowedMethods, inputs, outputs,
                    branchPolicies, seedMethods,
                    outputBoundarySeq(exactHeapOutput));
        }

        private ReturnSlice dependencySlice(
                String regionId, String occurrenceId,
                String outputCell,
                Map<String, Object> exactHeapOutput,
                Set<String> allowedMethods,
                List<Map<String, Object>> inputs,
                List<Map<String, Object>> outputs,
                List<Map<String, Object>> branchPolicies,
                Set<String> seedMethods,
                long boundaryUpperSeq) {
            return dependencySlice(regionId, occurrenceId, outputCell,
                    exactHeapOutput, allowedMethods, inputs, outputs,
                    branchPolicies, seedMethods,
                    boundaryUpperSeq, GuardAdmission.EXPLICIT_FAULT_ONLY);
        }

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

            // A relation whose value slice reached no declared input at all
            // is the shape {@link GuardAdmission#RELATION_INPUT_PORT} exists
            // for: its output is assigned literals, its value provenance is
            // therefore empty, no guard can be found to control it, and it
            // publishes a constant on every path.  README section 3 writes a
            // relation as OR_i(pathGuard_i(IN) AND OUT = expr_i(IN)); when
            // expr_i is a literal, pathGuard_i is the whole relation.
            //
            // Only the cut-argument relation asked for this admission, so a
            // heap output built from literals - the ordinary
            // `x = flag ? 1 : -1; publish(x)` producer - could never state its
            // own guard.  Decided once from the value slice alone, so a guard
            // admitted inside the loop can never widen the test that admitted
            // it.  Nothing about the door is relaxed: the branch still needs a
            // static GUARD edge into the walk, and a path assumption still
            // needs an operand reaching a port this occurrence declares.
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
                    String method = text(branch.get("method"));
                    String site = text(branch.get("siteId"));
                    List<String> operands = strings(
                            branch.get("operandCells"));
                    String policy = text(branch.get("policy"));
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
                    // explicit-fault input.  This is the generic shape of a
                    // fault marker deciding whether a state-publishing call
                    // executes, without promoting ordinary queue or
                    // configuration path assumptions into producer variables.
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
                    // boundary.  Omitting the method leaves a branch site in
                    // the task that Soot is not allowed to instrument.
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

        /**
         * Whether a guard operand terminates at this occurrence's own
         * declared symbolic input.
         *
         * <p>README section 3 writes a region relation as
         * {@code OR_i(pathGuard_i(IN) AND OUT = expr_i(IN))}: the guard is
         * part of the relation, not context around it.  A guard whose
         * operand slice ends on a port that is already declared as
         * {@code IN} for this very occurrence is therefore one of those
         * {@code pathGuard_i}, and dropping it publishes a relation whose
         * output is a constant on every path.</p>
         *
         * <p>It stays a strictly narrower door than "any path assumption":
         * the branch must still carry a static {@code GUARD} edge into the
         * selected value slice, and the operand must still reach a port the
         * region declared and the runtime bound to this occurrence.  A guard
         * over a value nothing declares as input is not admitted, which is
         * what keeps ordinary queue and configuration assumptions out.</p>
         */
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
                        && ports.contains(text(input.get("portId")))) {
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
                        && ports.contains(text(input.get("portId")))
                        && RuntimeSelectedRegionFinalizer
                        .EXPLICIT_SYMBOLIC_FAULT.equals(
                        text(input.get("sourceKind")))) {
                    return true;
                }
            }
            return false;
        }

        /**
         * Uses the exact exception guard as a sink instead of inheriting the
         * whole execution-context region.  The target guard is retained even
         * when it is a path assumption; all other branches still require a
         * static GUARD edge into the selected value slice.
         */
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
                String site = text(branch.get("siteId"));
                String method = text(branch.get("method"));
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
            // A control dependency can guard the call that creates a
            // selected helper activation rather than one of the helper's
            // internal value cells.  That guard is part of the relation's
            // existence condition.  In particular, an explicit fault marker
            // controlling whether the state-publishing call is invoked must
            // remain a symbolic input of the produced state relation.
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

        /**
         * Input boundary maps depend only on the (immutable) region input
         * list and the bound occurrence; they were previously rebuilt on
         * every backward slice, which dominated planning time.  The cache
         * preserves construction order exactly.
         */
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
                String port = text(input.get("portId"));
                if (!boundToInput(input, occurrenceId)
                        || port.isEmpty()) {
                    continue;
                }
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
                    : text(exactHeapOutput.get("rootMethod"));
            String forcedSite = exactHeapOutput == null ? ""
                    : text(exactHeapOutput.get("siteId"));
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
                        directInputs.get(current.cell), boundaryUpperSeq,
                        true);
                if (!direct.isEmpty()) {
                    for (Map<String, Object> input : direct) {
                        result.inputPorts.add(text(input.get("portId")));
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
                                        boundaryUpperSeq, false);
                        boolean unresolvedBoundary =
                                selectedInputs.isEmpty();
                        for (Map<String, Object> input : selectedInputs) {
                            Map<String, Object> writer = precedingWrite(
                                    regionId, occurrenceId, input,
                                    edge.fromCell, outputs, allowedMethods);
                            if (writer != null) {
                                SliceNode predecessor = new SliceNode(
                                        edge.fromCell,
                                        text(writer.get("rootMethod")),
                                        text(writer.get("siteId")));
                                enqueueSlice(predecessor, current, edge,
                                        visited, queue, towardSink);
                            } else {
                                unresolvedBoundary = true;
                                result.inputPorts.add(text(
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
                String method = text(output.get("rootMethod"));
                String site = text(output.get("siteId"));
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

        /** Selects one exact boundary port; distinct candidates fail closed. */
        private static Map<String, Object> selectBoundary(
                List<Map<String, Object>> candidates, long upperSeq,
                boolean allowProtocolOccurrence) {
            if (candidates == null || candidates.isEmpty()) return null;
            Map<String, Object> first = candidates.get(0);
            String port = text(first.get("portId"));
            for (Map<String, Object> candidate : candidates) {
                if (!port.equals(text(candidate.get("portId")))) {
                    return null;
                }
            }
            return first;
        }

        /**
         * A configured boundary array may contribute several independently
         * replayable scalar occurrences at one static read site.  Those
         * ports are the only multi-boundary case admitted here; ordinary
         * duplicate inputs retain the exactly-one fail-closed rule.
         */
        private static List<Map<String, Object>> selectBoundaries(
                List<Map<String, Object>> candidates, long upperSeq,
                boolean allowProtocolOccurrence) {
            if (candidates == null || candidates.isEmpty()) {
                return Collections.emptyList();
            }
            List<Map<String, Object>> boundedCandidates = new ArrayList<>();
            boolean allConcreteResidual = true;
            for (Map<String, Object> candidate : candidates) {
                boolean concreteResidual =
                        "CONCRETE_UNPROJECTED_BOUNDARY_ACCESS".equals(
                                text(candidate.get("symbolicDemand")));
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
            Map<String, Object> one = selectBoundary(boundedCandidates,
                    upperSeq, allowProtocolOccurrence);
            return one == null ? Collections.emptyList()
                    : Collections.singletonList(one);
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
        private final Set<String> guardOnlyInputPorts =
                new LinkedHashSet<>();
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<String> staticSites = new LinkedHashSet<>();
        private final Set<String> branchSites = new LinkedHashSet<>();
        private final Set<String> edges = new LinkedHashSet<>();
        private final Set<String> cells = new LinkedHashSet<>();
        /**
         * Every cell the backward walk reached, boundary or not.
         *
         * <p>{@link #cells} records only the cells on a path that ended at a
         * declared input, because it doubles as the provenance of the edges
         * that were retained.  A value chain that ends in constants - which
         * is what a request built from a branch over literals is - therefore
         * leaves it empty, and a control dependence on that chain becomes
         * invisible.  This set is the walk itself, and only the cut-argument
         * relation reads it.</p>
         */
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

    private static void require(Map<String, Object> row, int schema,
                                String kind, Object source) {
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
        final List<Map<String, Object>> regionCatalog = new ArrayList<>();
        final List<Map<String, Object>> runtimeInstances = new ArrayList<>();
        /** Recorded exchange and shared-location links across occurrences. */
        final List<Map<String, Object>> occurrenceLinks = new ArrayList<>();
        /**
         * Named runtime gaps.  Every place this stage cannot stamp an
         * occurrence, an outcome, an exchange or a source publishes one of
         * these instead of substituting a plausible value.
         */
        final List<Map<String, Object>> gaps = new ArrayList<>();
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
        /**
         * Owner of this frame.  Not final: a frame is stamped when it is
         * entered, and a node builds its service objects before it declares
         * which source they belong to, so a thread started during start-up
         * carries whoever started it.  The declaration arrives later in the
         * same trace, and {@code reattribute} applies it once the whole
         * trace is known - see the recorder's re-attribution pass.
         */
        SourceRef source;
        /** Stable logical scope of this event; never a transient trace id. */
        String sourceKey;
        final String requestKey;
        final String requestApi;
        MethodEvent(long seq, String test, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId) {
            this(seq, test, threadName, tid, method, objectId,
                    receiverType, callId, parentCallId, parentSiteId,
                    0L, 0L, 0L, 0L);
        }

        MethodEvent(long seq, String test, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId,
                    long laneId, long spanId,
                    long parentSpanId, long remoteParentSpanId) {
            this(seq, test, threadName, tid, method, objectId,
                    receiverType, callId, parentCallId, parentSiteId,
                    laneId, spanId, parentSpanId,
                    remoteParentSpanId, null);
        }

        MethodEvent(long seq, String test, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId,
                    long laneId, long spanId,
                    long parentSpanId, long remoteParentSpanId,
                    SourceRef source) {
            this(seq, test, threadName, tid, method, objectId,
                    receiverType, callId, parentCallId, parentSiteId,
                    laneId, spanId, parentSpanId,
                    remoteParentSpanId, source, "", "");
        }

        MethodEvent(long seq, String test, String threadName,
                    long tid, String method, int objectId, String receiverType,
                    long callId, long parentCallId, long parentSiteId,
                    long laneId, long spanId,
                    long parentSpanId, long remoteParentSpanId,
                    SourceRef source, String requestKey, String requestApi) {
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
            this.requestKey = safe(requestKey);
            this.requestApi = safe(requestApi);
        }

        /**
         * Applies the owner its receiver registered anywhere in this trace.
         *
         * <p>The entry stamp is the best answer available while the trace is
         * being written; it is not the best answer once it has been read.
         * Correcting it here rather than at each reader is what keeps the
         * occurrence identity, the stamped-source list and the plan's own
         * anchor one answer instead of three.</p>
         */
        void reattribute(SourceRef owner) {
            if (owner == null || owner.equals(source)) return;
            this.source = owner;
            this.sourceKey = owner.key();
        }
    }

    /**
     * Selects a replay continuation from an already proven root-to-output
     * call chain.  Package visibility keeps the policy directly testable;
     * callers must supply dynamic nesting order rather than a method list.
     */
    static MethodEvent firstCompatibleReplayContinuation(
            List<MethodEvent> rootToOutput,
            Collection<String> selectedMethods) {
        if (rootToOutput == null || rootToOutput.size() < 2
                || selectedMethods == null || selectedMethods.isEmpty()) {
            return null;
        }
        Set<String> selected = selectedMethods instanceof Set
                ? (Set<String>) selectedMethods
                : new LinkedHashSet<>(selectedMethods);
        for (int index = 1; index < rootToOutput.size(); index++) {
            MethodEvent event = rootToOutput.get(index);
            if (event != null && selected.contains(event.method)
                    && !event.receiverType.isEmpty()) {
                return event;
            }
        }
        return null;
    }

    static final class ProtocolEvent {
        final long seq;
        final String direction;
        final String transport;
        final String correlationId;
        /** Retry/attempt identity stated at the application boundary. */
        final String attemptId;
        /**
         * The half of the exchange this leg belongs to, as the application
         * stated it, or {@code ""} when it stated none.
         *
         * <p>The correlation names the exchange and only the exchange, so one
         * exchange records a send and a receive on each of its two halves
         * under one correlation.  This member keeps request topology apart
         * from response topology. It is stated, never derived: a direction
         * says whether a leg sent or received, which is not the same fact and
         * cannot stand in for it.</p>
         */
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
        /** Exact call-site invocations on this hook's recorded caller chain. */
        Set<Long> enclosingInvocationIds = Collections.emptySet();
        /** Exact method activations on this hook's recorded caller chain. */
        Set<Long> enclosingCallIds = Collections.emptySet();

        ProtocolEvent(long seq, String direction, String transport,
                      String correlationId,
                      String threadName, long tid, String method, long callId,
                      long invocationId, String declaredCallee) {
            this(seq, direction, transport, correlationId,
                    threadName, tid, method, callId, invocationId,
                    declaredCallee, 0L, 0L, 0L, 0L);
        }

        ProtocolEvent(long seq, String direction, String transport,
                      String correlationId,
                      String threadName, long tid, String method, long callId,
                      long invocationId, String declaredCallee,
                      long laneId, long spanId,
                      long parentSpanId, long remoteParentSpanId) {
            this(seq, direction, transport, correlationId,
                    threadName, tid, method, callId, invocationId,
                    declaredCallee, laneId, spanId, parentSpanId,
                    remoteParentSpanId, null);
        }

        ProtocolEvent(long seq, String direction, String transport,
                      String correlationId,
                      String threadName, long tid, String method, long callId,
                      long invocationId, String declaredCallee,
                      long laneId, long spanId,
                      long parentSpanId, long remoteParentSpanId,
                      SourceRef source) {
            this(seq, direction, transport, correlationId,
                    threadName, tid, method, callId, invocationId,
                    declaredCallee, laneId, spanId, parentSpanId,
                    remoteParentSpanId, source, "", "");
        }

        ProtocolEvent(long seq, String direction, String transport,
                      String correlationId,
                      String threadName, long tid, String method, long callId,
                      long invocationId, String declaredCallee,
                      long laneId, long spanId,
                      long parentSpanId, long remoteParentSpanId,
                      SourceRef source, String requestKey,
                      String requestApi) {
            this(seq, direction, transport, correlationId, "", threadName,
                    tid, method, callId, invocationId, declaredCallee, laneId,
                    spanId, parentSpanId, remoteParentSpanId, source,
                    requestKey, requestApi);
        }

        ProtocolEvent(long seq, String direction, String transport,
                      String correlationId, String half,
                      String threadName, long tid, String method, long callId,
                      long invocationId, String declaredCallee,
                      long laneId, long spanId,
                      long parentSpanId, long remoteParentSpanId,
                      SourceRef source, String requestKey, String requestApi) {
            this(seq, direction, transport, correlationId, "", half,
                    threadName, tid, method, callId, invocationId,
                    declaredCallee, laneId, spanId, parentSpanId,
                    remoteParentSpanId, source, requestKey, requestApi);
        }

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

        /**
         * The one half of one exchange this leg is on.
         *
         * <p>Every place that used to key on the correlation alone keys on
         * this instead, because the correlation stopped carrying the half the
         * moment it became the exchange's own name.  A send and the receive
         * of the <em>same</em> half share it; the opposite half of the same
         * exchange never does.</p>
         */
        String exchangeLeg() {
            return RuntimeRegionPlanner.exchangeLeg(correlationId,
                    attemptId, half);
        }

        boolean isInsideInvocation(long candidateInvocationId) {
            return candidateInvocationId > 0L
                    && (invocationId == candidateInvocationId
                    || enclosingInvocationIds.contains(candidateInvocationId));
        }
    }

    /**
     * The exchange leg a recorded event or a stamped occurrence names.
     *
     * <p>An application that states no half has one leg per exchange, and
     * that leg is addressed by the exchange's own name: adding an empty
     * component would be inventing a distinction the run never stated.  A
     * stated half is appended, so the two halves of one exchange are two
     * addresses and neither is the exchange's bare name.</p>
     */
    static String exchangeLeg(String exchangeId, String half) {
        return exchangeLeg(exchangeId, "", half);
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

    /**
     * Exact identity observation for one reference-array element access.
     *
     * <p>The array and element ids are trace-local evidence only.  The
     * transport layer may use the recorded index when a configured wire
     * contract explicitly preserves element order; neither the element value
     * nor an invocation ordinal participates in the correspondence.</p>
     */
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
            this(methodEvents, runtimeEvents, fieldEvents,
                    Collections.<ProtocolEvent>emptyList());
        }

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

        /**
         * Exact field reads below a planned function entry and before one
         * selected interaction event.
         */
        private List<FieldAccessEvent> fieldsThroughReplayEntry(
                long rootCallId, String replayMethod, String receiverClass,
                long boundarySeq) {
            long eventCall = eventCallIdBySeq.uniqueValue(boundarySeq);
            if (rootCallId <= 0L || eventCall <= 0L
                    || replayMethod == null || replayMethod.isEmpty()
                    || receiverClass == null || receiverClass.isEmpty()) {
                return Collections.emptyList();
            }
            MethodEvent current = methodByCall.get(eventCall);
            MethodEvent entry = null;
            Set<Long> seen = new LinkedHashSet<>();
            while (current != null && seen.add(current.callId)) {
                if (replayMethod.equals(current.method)
                        && receiverClass.equals(current.receiverType)) {
                    entry = current;
                }
                if (current.callId == rootCallId) break;
                current = methodByCall.get(current.parentCallId);
            }
            if (entry == null) return Collections.emptyList();
            Set<Long> calls = subtreeThrough(entry.callId, boundarySeq);
            List<FieldAccessEvent> result = new ArrayList<>();
            for (FieldAccessEvent access : fields) {
                if (access.seq > boundarySeq) break;
                if ("FIELD_READ".equals(access.kind)
                        && calls.contains(access.callId)) {
                    result.add(access);
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

        /**
         * Every recorded frame one call is inside, itself included.  It is
         * the recorded caller chain of this thread, which is what says a
         * mark fired inside one loop turn rather than beside it.
         */
        private Set<Long> enclosingCalls(long callId) {
            Set<Long> result = new LinkedHashSet<>();
            MethodEvent current = methodByCall.get(callId);
            while (current != null && result.add(current.callId)) {
                current = methodByCall.get(current.parentCallId);
            }
            return result;
        }

        /**
         * Nearest planned activation root on one call's exact caller chain.
         * This is the ownership relation for deep communication hooks: the
         * activation's selected call set may intentionally omit transport and
         * reflection frames, while their recorded parent chain still proves
         * which application activation encloses them.
         */
        private long nearestEnclosingCall(long callId,
                                          Set<Long> candidateRoots) {
            if (candidateRoots == null || candidateRoots.isEmpty()) return -1L;
            MethodEvent current = methodByCall.get(callId);
            Set<Long> seenCalls = new LinkedHashSet<>();
            while (current != null && seenCalls.add(current.callId)) {
                if (candidateRoots.contains(current.callId)) {
                    return current.callId;
                }
                current = methodByCall.get(current.parentCallId);
            }
            return -1L;
        }

        /**
         * Exact call-site invocations on the recorded caller chain of one
         * frame.  A transport hook uses this to find the application cut
         * that entered it; every id comes from a METHOD_ENTER parentSiteId,
         * so this is dynamic nesting evidence rather than post-hoc matching.
         */
        private Set<Long> enclosingInvocationIds(long callId) {
            Set<Long> result = new LinkedHashSet<>();
            MethodEvent current = methodByCall.get(callId);
            Set<Long> seenCalls = new LinkedHashSet<>();
            while (current != null && seenCalls.add(current.callId)) {
                if (current.parentSiteId > 0L) {
                    result.add(current.parentSiteId);
                }
                current = methodByCall.get(current.parentCallId);
            }
            return Collections.unmodifiableSet(result);
        }

        /**
         * The static site of one recorded call-site invocation inside one
         * frame, or {@code ""} when this run recorded none.
         */
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

        /**
         * Every recorded evaluation of one exact call argument inside one
         * activation, in recorded order.
         *
         * <p>The endpoint is the static call site, the declared callee and
         * the argument position - the three things the cut port itself
         * declares.  Nothing here reads a value or a payload.</p>
         */
        private List<RuntimeEvent> callArgumentEvents(
                Set<Long> calls, String siteId, String declaredCallee,
                int argumentIndex) {
            List<RuntimeEvent> result = new ArrayList<>();
            if (calls == null || siteId.isEmpty()
                    || declaredCallee.isEmpty() || argumentIndex < 0) {
                return result;
            }
            for (RuntimeEvent event : runtime(calls)) {
                if ("CALL_ARGUMENT".equals(event.kind)
                        && siteId.equals(event.siteId)
                        && declaredCallee.equals(event.declaredCallee)
                        && event.argumentIndex == argumentIndex) {
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

        private long callAt(long eventSeq) {
            return eventCallIdBySeq.uniqueValue(eventSeq);
        }

        /**
         * The earliest selected application continuation on the exact
         * root-to-definition call chain.  A root-owned communication input is
         * handled by the caller before this narrowing policy is applied.
         */
        private MethodEvent exactReplayContinuation(
                long rootCallId, long definitionCallId,
                Set<String> selectedMethods) {
            if (rootCallId <= 0L || definitionCallId <= 0L
                    || selectedMethods == null || selectedMethods.isEmpty()) {
                return null;
            }
            Set<Long> callPath;
            try {
                callPath = path(rootCallId, definitionCallId);
            } catch (IllegalArgumentException ignored) {
                return null;
            }
            List<MethodEvent> chain = new ArrayList<>();
            for (Long callId : callPath) {
                MethodEvent event = methodByCall.get(callId);
                if (event != null) chain.add(event);
            }
            return firstCompatibleReplayContinuation(chain,
                    selectedMethods);
        }

        /**
         * Narrows a long-lived root to the invocation that produced one
         * exact runtime output.  The root-to-caller chain preserves the
         * execution context, while the caller subtree up to the output event
         * preserves helpers that computed the selected value.  Calls begun
         * after publication are consumers of that value, not part of its
         * producer relation; admitting them can pull an entire RPC/server
         * execution into a small call-argument summary.  Earlier sibling
         * invocations under the same service loop are deliberately absent.
         * A missing or ambiguous event mapping returns {@code null}; the
         * caller refuses that output relation rather than widening it.
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
            corridor.addAll(subtreeThrough(caller, outputEventSeq));
            return corridor;
        }

        /**
         * The unique normal exit of one method invocation below a selected
         * activation.
         *
         * <p>A response port names the semantic server method, while the
         * runtime trace names its concrete invocation.  This lookup joins
         * those two facts without using the returned payload.  More than one
         * matching invocation or more than one normal-exit event is
         * ambiguous and therefore has no exact method-return boundary.</p>
         */
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
