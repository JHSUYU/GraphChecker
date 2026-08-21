package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.ToNumberPolicy;
import com.google.gson.reflect.TypeToken;
import edu.uva.liftlab.graphchecker.concolic.AutomaticRegionEdge;
import edu.uva.liftlab.graphchecker.concolic.RecordedReadFrom;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.runtime.OccurrenceMinter;

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
import java.util.TreeSet;
import java.util.UUID;
import java.util.zip.GZIPInputStream;

/** Builds executable region state exclusively from a runtime-refined graph. */
public final class RuntimeSelectedRegionFinalizer {
    private static final Type ROW =
            new TypeToken<Map<String, Object>>() { }.getType();
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();
    private static final String REFINED_KIND = "RUNTIME_REFINED_DATAFLOW";

    /** A boolean returned by the explicit application-side fault marker. */
    public static final String EXPLICIT_SYMBOLIC_FAULT =
            "EXPLICIT_SYMBOLIC_FAULT";
    /**
     * Skeleton field naming the methods reached from the anchors that admitted
     * the region.  Absent or empty means "not decided": every guard in the
     * region stays explorable.
     */
    public static final String DEMAND_SCOPE = "demandScopeMethods";

    /** Existing planner admission vocabulary for a bounded state writer. */
    private static final String ADMISSION_BASIS = "admissionBasis";
    private static final String SHARED_LOCATION_DEMAND_ADMISSION =
            "SHARED_LOCATION_DEMAND_V1";
    private static final String DEMANDED_BY_REGIONS = "demandedByRegionIds";
    private static final String DEMANDED_SHARED_LOCATIONS =
            "demandedSharedLocations";

    /**
     * Skeleton field carrying the communication ports of every cut whose
     * client or server side this region holds.
     *
     * <p>README section 3's composition is a chain of equalities between one
     * region's port and another's, so the composer can only state one over
     * ports a region catalog declares.  {@link SymbolicRegionPlanner} decides
     * which region owns which side of a cut while the static call-site rows
     * are still in memory; this stage copies that decision into the region's
     * own {@code symbolicInputs}/{@code outputs}, which is what the runtime
     * planner publishes and the composer reads.</p>
     */
    public static final String COMMUNICATION_PORTS = "communicationPorts";

    /**
     * A recorded exchange with no typed producer edge for the failure walk.
     *
     * <p>The crossing really happened and both occurrences recorded it; what
     * this stage no longer publishes is a port-level value edge for it,
     * because the value relation across a communication boundary is the VM's
     * own export/attach handoff.  Named so the loss is visible.</p>
     */
    public static final String GAP_RECORDED_EXCHANGE_UNTYPED =
            "RUNTIME_RECORDED_EXCHANGE_NO_TYPED_PRODUCER_EDGE";
    /** {@code IN} or {@code OUT}: which catalog a declared port belongs in. */
    public static final String REGION_PORT_SIDE = "regionPortSide";
    /** {@code sourceKind} of a port that carries a value across a call. */
    public static final String COMMUNICATION_SITE_PORT =
            "COMMUNICATION_SITE_PORT";
    /** Authority of one declared communication-site port. */
    public static final String COMMUNICATION_PORT_AUTHORITY =
            "COMMUNICATION_SITE_PORT_DECLARATION_V1";
    /** Which side of one communication site a declared port belongs to. */
    public static final String PORT_ROLE = "portRole";
    /** The frame that issues the call. */
    public static final String PORT_ROLE_CLIENT = "CLIENT";
    /** The remote handler, which is its own region occurrence. */
    public static final String PORT_ROLE_SERVER = "SERVER";
    /** A discarded region that took its declared communication ports with it. */
    public static final String GAP_COMMUNICATION_PORT_UNRETAINED =
            "COMMUNICATION_PORT_REGION_UNRETAINED";

    /** Region-row member carrying the retained loops of its methods. */
    public static final String RETAINED_LOOPS = "retainedLoops";

    /** {@code kind} of every gap row this stage publishes. */
    public static final String GAP_ROW_KIND = "RUNTIME_COMMUNICATION_GAP";
    /** An activation whose trace carried no registered logical source. */
    public static final String GAP_RUNTIME_SOURCE_UNSTAMPED =
            "RUNTIME_SOURCE_UNSTAMPED";
    /**
     * Authority of one boxed-value leaf restated on its carrier's producer.
     *
     * <p>A JDK wrapper is an immutable value carrier, not state reached
     * through a transferred reference: {@code Boolean.FALSE.value} has no
     * writer because it cannot have one.  The producer of the value is
     * therefore the producer of the reference, and this names that rule.  It
     * is the planning-side mirror of
     * {@code JavaPrimitiveBoxing.deterministicValueOfReturn}, which already
     * says a wrapper {@code valueOf} result is computed by its call rather
     * than being an independent live-in.</p>
     */
    public static final String BOXED_LEAF_PROJECTION_AUTHORITY =
            "IMMUTABLE_BOXED_VALUE_LEAF_V1";
    /** Edge member naming the rule that projected one boxed leaf. */
    public static final String EDGE_BOXED_LEAF_AUTHORITY =
            "boxedLeafAuthority";

    private static Map<String, Object> gap(String kind, String reason,
                                           String activationId,
                                           String method, String siteId,
                                           String detail) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", 1);
        row.put("kind", GAP_ROW_KIND);
        row.put("gapKind", kind);
        row.put("reason", reason);
        row.put("activationId", activationId);
        row.put("method", method);
        row.put("siteId", siteId);
        row.put("detail", detail);
        return row;
    }

    private RuntimeSelectedRegionFinalizer() {
    }

    public static Result finalizeRegions(
            File refinedGraph, File selectedSkeletons,
            Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances)
            throws IOException {
        return finalizeRegions(refinedGraph, selectedSkeletons,
                observedMethods, runtimeInstances,
                Collections.<Map<String, Object>>emptyList());
    }

    /**
     * Finalizes regions using exact branch observations from the same runtime
     * trace that produced {@code runtimeInstances}.  The compact observations
     * keep a fatal target activation tied to the static predicate it actually
     * reached; an exception-context template is not itself runtime evidence
     * that every failure site in that template was reached.
     */
    public static Result finalizeRegions(
            File refinedGraph, File selectedSkeletons,
            Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeBranchObservations)
            throws IOException {
        return finalizeRegions(read(refinedGraph), refinedGraph,
                selectedSkeletons, observedMethods,
                runtimeInstances, runtimeBranchObservations,
                Collections.<Map<String, Object>>emptyList());
    }

    /**
     * In-memory entry point for an already parsed refined graph.  The rows
     * must be in the exact JSONL value domain (integral numbers as Long),
     * which {@code RuntimeRefinedGraphBuilder} guarantees for the rows it
     * returns; behavior is identical to re-reading {@code refinedGraph}.
     *
     * <p>Finalization runs at trace aggregation, before any concolic
     * execution of this workload exists, so no recorded read-from evidence
     * can exist yet either.  Field flow therefore decides no writer here: it
     * retains every writer the trace observed as an explicit candidate and
     * names the gap.  The recorded answer is applied to those candidates at
     * campaign completion, by {@link RecordedReadFrom#resolve}, which is the
     * first point at which both the candidates and the evidence exist.</p>
     */
    public static Result finalizeRegions(
            List<Map<String, Object>> graph, File refinedGraph,
            File selectedSkeletons, Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeBranchObservations)
            throws IOException {
        return finalizeRegions(graph, refinedGraph, selectedSkeletons,
                observedMethods, runtimeInstances, runtimeBranchObservations,
                Collections.<Map<String, Object>>emptyList());
    }

    /**
     * Finalizes the selected runtime graph using the occurrence links already
     * produced by the runtime planner.  Those links are scheduling evidence;
     * symbolic values still cross only through VM VALUE_HANDOFF edges.
     */
    public static Result finalizeRegions(
            List<Map<String, Object>> graph, File refinedGraph,
            File selectedSkeletons, Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeBranchObservations,
            Collection<Map<String, Object>> runtimeOccurrenceLinks)
            throws IOException {
        List<Map<String, Object>> skeletons = read(selectedSkeletons);
        requireRefinedGraph(graph, refinedGraph);
        Set<String> observed = new LinkedHashSet<>();
        if (observedMethods != null) {
            observed.addAll(observedMethods);
        }

        StaticProgram program = new StaticProgram();
        Map<String, Map<String, Object>> skeletonById = new LinkedHashMap<>();
        Map<String, List<Map<String, Object>>> edgesByRegion =
                new LinkedHashMap<>();
        for (Map<String, Object> skeleton : skeletons) {
            requireSkeleton(skeleton, selectedSkeletons);
            skeletonById.put(text(skeleton.get("regionId")), skeleton);
        }
        for (Map<String, Object> edge : graph) {
            for (String region : strings(edge.get("regionIds"))) {
                edgesByRegion.computeIfAbsent(region,
                        ignored -> new ArrayList<>()).add(edge);
            }
        }

        // Activation identity is minted before the first port of a region is
        // built.  The recorded root call is resolved exactly once, at this
        // seed boundary, and every row built afterwards is grouped, selected
        // and addressed by occurrence.  Minting only needs the failure-target
        // guard sites of a region, which the refined graph states directly:
        // the full branch policy is a later, demand-scoped refinement that
        // never adds, removes or re-outcomes a failure target.
        Map<String, List<Map<String, Object>>> targetPoliciesByRegion =
                new LinkedHashMap<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : skeletonById.entrySet()) {
            if (!selectedRegion(entry.getValue(), observed)) continue;
            targetPoliciesByRegion.put(entry.getKey(), failureTargetPolicies(
                    edgesByRegion.getOrDefault(entry.getKey(),
                            Collections.emptyList())));
        }
        List<Map<String, Object>> gaps = new ArrayList<>();
        Map<String, Map<String, Object>> activations = mintOccurrences(
                targetPoliciesByRegion, runtimeInstances,
                runtimeBranchObservations, selectedSkeletons, gaps);
        Map<String, String> occurrenceByRecordedRootCall =
                recordedRootCallIndex(activations);

        Set<String> plannedRegions = new LinkedHashSet<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : skeletonById.entrySet()) {
            String regionId = entry.getKey();
            Map<String, Object> skeleton = entry.getValue();
            List<String> methods = strings(skeleton.get("methods"));
            if (!selectedRegion(skeleton, observed)) {
                continue;
            }
            plannedRegions.add(regionId);
            Map<String, Object> region = new LinkedHashMap<>();
            region.put("schemaVersion", 3);
            region.put("kind", "SYMBOLIC_REGION");
            region.put("graphKind", REFINED_KIND);
            region.put("regionId", regionId);
            region.put("rootMethod", skeleton.get("rootMethod"));
            region.put("anchorMethod", skeleton.get("anchorMethod"));
            if (skeleton.containsKey("anchorMethods")) {
                region.put("anchorMethods", skeleton.get("anchorMethods"));
            }
            region.put("selection", skeleton.get("selection"));
            region.put("methods", methods);
            // The refined row is built fresh, so anything the skeleton
            // carries has to be carried over by name.  The retained loops are
            // where the declared per-loop K_L lives: SymbolicRegionPlanner
            // attaches them to the skeleton from loop-bounds.jsonl, the
            // occurrence plan filters them to the methods one activation ran,
            // and the scheduler turns them into the task's per-site bounds.
            // Dropping them here broke that chain silently at its narrowest
            // point - every declaration was still parsed, claimed and
            // refused-if-unclaimed upstream, so nothing failed, and every
            // task simply inherited the campaign default instead.
            if (skeleton.get(RETAINED_LOOPS) != null) {
                region.put(RETAINED_LOOPS, skeleton.get(RETAINED_LOOPS));
            }

            List<Map<String, Object>> regionGraph = edgesByRegion.getOrDefault(
                    regionId, Collections.emptyList());
            List<Map<String, Object>> outputs = statePorts(regionId,
                    regionGraph, "HEAP_WRITE", "OUT",
                    occurrenceByRecordedRootCall);
            outputs.removeIf(RuntimeSelectedRegionFinalizer
                    ::toolBookkeepingPort);
            List<Map<String, Object>> branchPolicies = branches(regionGraph,
                    demandScope(skeleton, outputs));
            List<Map<String, Object>> inputs = statePorts(regionId,
                    regionGraph, "HEAP_READ", "IN",
                    occurrenceByRecordedRootCall);
            inputs.addAll(accessorPorts(regionId, regionGraph,
                    branchPolicies, occurrenceByRecordedRootCall));
            inputs.removeIf(RuntimeSelectedRegionFinalizer
                    ::toolBookkeepingPort);
            inputs.addAll(explicitFaultPorts(regionId, regionGraph,
                    occurrenceByRecordedRootCall));
            markLoopControlOnlyInputs(inputs, regionGraph, branchPolicies);
            region.put("symbolicInputs", inputs);
            region.put("outputs", outputs);
            region.put("branchPolicies", branchPolicies);
            program.regions.add(region);
        }
        bindObservedFatalTargets(program.regions, graph, runtimeInstances,
                runtimeBranchObservations);
        Set<String> demandedFields = failureRelevantFields(
                program.regions, graph);
        List<Map<String, Object>> runtimeFieldFlows = fieldFlows(
                program.regions, demandedFields);
        program.regionEdges.addAll(runtimeFieldFlows);
        stampEdgeOccurrences(program.regionEdges,
                occurrenceByRecordedRootCall);
        program.regionEdges.addAll(demandedLeafProducerFlows(
                program.regions, program.regionEdges));
        stampEdgeOccurrences(program.regionEdges,
                occurrenceByRecordedRootCall);
        annotateFlowContexts(program.regionEdges, activations);
        markBoundedMutationStateFrontiers(program.regions, graph);
        // The declarations are static and the occurrence-owned copies below
        // are dynamic, so this remains a typed-port join rather than a value
        // or payload guess.  applyClosure removes every declaration and edge
        // not reached by the target-directed walk; the declaration pass after
        // it restores only the region-level catalog rows used downstream.
        declareCommunicationPorts(program.regions, skeletonById,
                Collections.<String>emptySet(), new ArrayList<
                Map<String, Object>>());
        markUnclosedReferenceLeavesConcrete(program.regions,
                program.regionEdges, graph, occurrenceByRecordedRootCall);
        program.regionEdges.addAll(recordedOccurrenceProducerFlows(
                runtimeOccurrenceLinks, activations, program.regions, gaps));
        markTransportedReferenceFrontiers(program.regions,
                program.regionEdges);
        RuntimeClosure closure = failureDirectedClosure(program, graph,
                activations, selectedSkeletons, gaps);
        applyClosure(program, closure);
        // A Map becomes symbolic only when the retained target slice contains
        // its exact declared mutation-to-read flow.  The VM owns container
        // versions and their pre/post/query evidence; this stage only marks
        // the two retained ports as bounded state carriers.
        markBoundedContainerStatePorts(program.regions,
                program.regionEdges);
        // Declared last, and deliberately after the closure filter.  A
        // communication port is not a heap port of one activation: it has no
        // recorded access, no field path and no demand key, so the port
        // filter - which retains a port by exactly those - would drop every
        // one of them.  What declares it is the static cut, which the closure
        // does not decide.
        declareCommunicationPorts(program.regions, skeletonById,
                plannedRegions, gaps);
        canonicalizeRegionEdges(program);
        return new Result(program.regions, program.regionEdges, gaps);
    }

    /**
     * The edge id is the canonical semantic identity. Repeated identical
     * payloads are harmless aggregation duplicates; two different payloads
     * under one id are an ambiguous model and must fail closed.
     */
    static void canonicalizeRegionEdges(StaticProgram program)
            throws IOException {
        Map<String, Map<String, Object>> byId = new LinkedHashMap<>();
        for (Map<String, Object> edge : program.regionEdges) {
            String edgeId = edge.get("edgeId") == null ? ""
                    : String.valueOf(edge.get("edgeId"));
            if (edgeId.isEmpty()) {
                throw new IOException("runtime region edge has no edgeId");
            }
            Map<String, Object> previous = byId.putIfAbsent(edgeId, edge);
            if (previous != null && !previous.equals(edge)) {
                throw new IOException("conflicting runtime region edge "
                        + "payload for edgeId " + edgeId);
            }
        }
        List<Map<String, Object>> canonical = new ArrayList<>(byId.values());
        program.regionEdges.clear();
        program.regionEdges.addAll(canonical);
    }

    /**
     * Publishes the ports of every cut this region holds a side of.
     *
     * <p>A communication port of one region is read by another region's
     * case, so the composer states a term over it only when a region port
     * catalog declares it; without this step every such reference is a model
     * row with no SMT term and an undeclared-port gap, however completely the
     * runtime bound it.  {@link SymbolicRegionPlanner} decided which side of
     * which cut each region owns while the static call-site rows were still
     * in memory; here that decision reaches the catalog the planner
     * publishes.</p>
     *
     * <p>A region the failure closure discarded takes its declarations with
     * it.  That is a coverage statement, not a silent drop, so the ports it
     * would have declared are named.</p>
     */
    private static void declareCommunicationPorts(
            List<Map<String, Object>> regions,
            Map<String, Map<String, Object>> skeletonById,
            Set<String> plannedRegions, List<Map<String, Object>> gaps) {
        Set<String> retained = new LinkedHashSet<>();
        for (Map<String, Object> region : regions) {
            retained.add(text(region.get("regionId")));
        }
        for (Map<String, Object> region : regions) {
            Map<String, Object> skeleton = skeletonById.get(
                    text(region.get("regionId")));
            List<Map<String, Object>> declared = skeleton == null
                    ? Collections.<Map<String, Object>>emptyList()
                    : rows(skeleton.get(COMMUNICATION_PORTS));
            if (declared.isEmpty()) {
                continue;
            }
            List<Map<String, Object>> inputs = rows(
                    region.get("symbolicInputs"));
            List<Map<String, Object>> outputs = rows(region.get("outputs"));
            // A cut has one region-level declaration and zero or more
            // occurrence-owned instances of that declaration.  The
            // speculative pre-closure delivery pass creates the latter so
            // demand propagation can reach the exact activation.  Treating
            // an instance as the declaration merely because both carry the
            // same portId prevents this post-closure pass from restoring the
            // declaration; the final delivery pass then sees zero eligible
            // endpoints.  Deduplicate declarations only against other
            // declarations, never against their instances.
            Set<String> inputIds = declaredPortIds(inputs);
            Set<String> outputIds = declaredPortIds(outputs);
            for (Map<String, Object> port : declared) {
                String portId = text(port.get("portId"));
                String side = text(port.get(REGION_PORT_SIDE));
                if (portId.isEmpty()) {
                    continue;
                }
                Map<String, Object> row = new LinkedHashMap<>(port);
                row.remove(REGION_PORT_SIDE);
                if ("IN".equals(side)) {
                    if (inputIds.add(portId)) inputs.add(row);
                } else if ("OUT".equals(side)) {
                    if (outputIds.add(portId)) outputs.add(row);
                }
            }
            region.put("symbolicInputs", inputs);
            region.put("outputs", outputs);
        }
        for (String regionId : plannedRegions) {
            if (retained.contains(regionId)) {
                continue;
            }
            Map<String, Object> skeleton = skeletonById.get(regionId);
            List<Map<String, Object>> declared = skeleton == null
                    ? Collections.<Map<String, Object>>emptyList()
                    : rows(skeleton.get(COMMUNICATION_PORTS));
            if (declared.isEmpty()) {
                continue;
            }
            Set<String> undeclared = new LinkedHashSet<>();
            for (Map<String, Object> port : declared) {
                undeclared.add(text(port.get("portId")));
            }
            gaps.add(gap(GAP_COMMUNICATION_PORT_UNRETAINED,
                    "REGION_DISCARDED_BY_FAILURE_CLOSURE", "",
                    text(skeleton.get("rootMethod")), regionId,
                    String.join(",", undeclared)));
        }
    }

    /**
     * The value cell one declared cut port's capture names, or {@code ""}.
     *
     * <p>A cell is how every other stage refers to a value, and a declared
     * port arrives without one because static discovery names ports and not
     * cells.  A port with no cell is invisible to the backward walk, which is
     * why a target that reads the server entry's own parameter reached the
     * transport's heap read and never the declaration that supersedes it.
     * The four capture kinds are the four sites of one cut, so each has
     * exactly one cell and a declaration naming no addressable site gets
     * none.</p>
     */
    private static String declaredCutPortCell(Map<String, Object> port) {
        String capture = text(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        String definitionMethod = text(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        String javaType = text(port.get("javaType"));
        if (CommunicationCatalogContract.CAPTURE_ENTRY_PARAMETER.equals(
                capture)) {
            int argumentIndex = (int) longNumber(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1L);
            return definitionMethod.isEmpty() || javaType.isEmpty()
                    || argumentIndex < 0 ? ""
                    : definitionMethod + ".param" + argumentIndex + ":"
                    + javaType;
        }
        if (CommunicationCatalogContract.CAPTURE_ENTRY_RETURN.equals(
                capture)) {
            return definitionMethod.isEmpty() ? ""
                    : definitionMethod + ".return";
        }
        String callee = text(port.get(
                CommunicationCatalogContract.DECLARED_CALLEE));
        if (CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(
                capture)) {
            return callee.isEmpty() ? "" : callee + ".return";
        }
        if (CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT.equals(
                capture)) {
            // The cut argument is the one client output never written to the
            // heap, so the only cell that names it is the callee parameter
            // the value is bound into at the cut unit.  The binding edge is
            // attributed to the caller, so slicing back from this cell stays
            // one frame short of the transport instead of following the
            // value into it.
            int argumentIndex = (int) longNumber(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1L);
            return callee.isEmpty() || javaType.isEmpty()
                    || argumentIndex < 0 ? ""
                    : callee + ".param" + argumentIndex + ":" + javaType;
        }
        return "";
    }

    /** Erased type of a heap port's leaf field, or {@code ""}. */
    private static String leafJavaType(Map<String, Object> port) {
        List<String> declarations = strings(
                port.get("fieldPathDeclarations"));
        if (declarations.isEmpty()) {
            return "";
        }
        FieldPathSpec.DeclaredField leaf = FieldPathSpec.declaredField(
                declarations.get(declarations.size() - 1));
        return leaf == null ? "" : leaf.type();
    }

    /** The method half of a {@code <method>#u<index>} site id. */
    private static String accessMethod(String siteId) {
        int marker = siteId.lastIndexOf("#u");
        return marker <= 0 ? "" : siteId.substring(0, marker);
    }

    /**
     * Names every recorded exchange whose producing occurrence this stage can
     * no longer offer the failure closure as a typed producer edge.
     *
     * <p>The occurrence that exported the exchange and the occurrence that
     * received it are both recorded, and the region plan publishes the link
     * between them.  What this stage does <em>not</em> publish is a typed
     * {@code RUNTIME_PROTOCOL_FLOW} port edge for the crossing: the value
     * relation across a communication boundary is the VM's own export/attach
     * handoff and its {@code VALUE_HANDOFF} ledger edge, and re-deriving a
     * port pair here from the exchange identity is precisely the duplicate
     * pairing this design removes.  Until the coarse runtime publishes the
     * receiving occurrence's own port evidence, a target that depends on a
     * value across such a boundary reaches no producer through it, and that
     * loss is named here rather than left silent.</p>
     */
    private static List<Map<String, Object>> recordedOccurrenceProducerFlows(
            Collection<Map<String, Object>> occurrenceLinks,
            Map<String, Map<String, Object>> activations,
            List<Map<String, Object>> regions,
            List<Map<String, Object>> gaps) {
        Map<String, Map<String, Object>> activationsById =
                new LinkedHashMap<>();
        for (Map<String, Object> activation : activations.values()) {
            activationsById.put(text(activation.get("activationId")),
                    activation);
        }
        Map<String, Map<String, Object>> regionsById = new LinkedHashMap<>();
        for (Map<String, Object> region : regions) {
            regionsById.put(text(region.get("regionId")), region);
        }
        List<Map<String, Object>> flows = new ArrayList<>();
        Set<String> emitted = new LinkedHashSet<>();
        for (Map<String, Object> link : occurrenceLinks == null
                ? Collections.<Map<String, Object>>emptyList()
                : occurrenceLinks) {
            if (!"RECORDED_EXCHANGE_OCCURRENCE_LINK_V1".equals(
                    text(link.get("authority")))) {
                continue;
            }
            Map<String, Object> from = activationsById.get(
                    text(link.get("fromActivationId")));
            Map<String, Object> to = activationsById.get(
                    text(link.get("toActivationId")));
            if (from == null || to == null) {
                continue;
            }
            Map<String, Object> fromRegion = regionsById.get(
                    text(from.get("regionId")));
            if (fromRegion == null) {
                continue;
            }
            String direction = text(link.get("direction")).toUpperCase();
            int before = flows.size();
            List<TypedReceiver> receivers = typedReceivers(to, direction,
                    fromRegion, activationsById, regionsById);
            Set<String> receivingActivations = new LinkedHashSet<>();
            for (TypedReceiver receiver : receivers) {
                receivingActivations.add(text(
                        receiver.activation.get("activationId")));
            }
            if (receivingActivations.size() > 1) {
                gaps.add(gap(GAP_RECORDED_EXCHANGE_UNTYPED,
                        "AMBIGUOUS_NESTED_TYPED_RECEIVER",
                        text(from.get("activationId")),
                        text(from.get("rootMethod")),
                        text(link.get("callSiteId")),
                        text(link.get("exchangeLeg"))));
                continue;
            }
            for (TypedReceiver receiver : receivers) {
                Map<String, Object> exactTo = receiver.activation;
                Map<String, Object> toRegion = receiver.region;
                Map<String, Object> receiving = receiver.port;
                String portId = text(receiving.get("portId"));
                Map<String, Object> sending = declaredOutputPort(fromRegion,
                        portId);
                String identity = text(from.get("occurrenceId")) + "\n"
                        + text(exactTo.get("occurrenceId")) + "\n" + portId;
                if (!emitted.add(identity)) continue;
                stampOccurrenceOwnedPort(fromRegion, "outputs", sending,
                        text(from.get("occurrenceId")),
                        longNumber(link.get("senderEventSeq"), -1L));
                stampOccurrenceOwnedPort(toRegion, "symbolicInputs",
                        receiving, text(exactTo.get("occurrenceId")),
                        longNumber(link.get("receiverEventSeq"), -1L));
                flows.add(exchangeProducerEdge(from, exactTo, link,
                        receiving));
            }
            if (flows.size() == before) {
                gaps.add(gap(GAP_RECORDED_EXCHANGE_UNTYPED,
                        "NO_SHARED_DECLARED_PORT_FOR_OCCURRENCE_LINK",
                        text(from.get("activationId")),
                        text(from.get("rootMethod")),
                        text(link.get("callSiteId")),
                        text(link.get("exchangeId"))));
            }
        }
        return flows;
    }

    /**
     * Resolves a recorded receiver envelope to typed receiving occurrences.
     * A nested occurrence is eligible only through exact dynamic call
     * containment plus a shared declared port.  This is scheduling topology;
     * the VM handoff remains the only value authority.
     */
    private static List<TypedReceiver> typedReceivers(
            Map<String, Object> recordedReceiver, String direction,
            Map<String, Object> fromRegion,
            Map<String, Map<String, Object>> activationsById,
            Map<String, Map<String, Object>> regionsById) {
        List<TypedReceiver> result = new ArrayList<>();
        String envelopeId = text(recordedReceiver.get("activationId"));
        for (Map<String, Object> candidate : activationsById.values()) {
            if (!envelopeId.equals(text(candidate.get("activationId")))
                    && !strings(candidate.get("enclosingActivationIds"))
                    .contains(envelopeId)) {
                continue;
            }
            Map<String, Object> region = regionsById.get(
                    text(candidate.get("regionId")));
            if (region == null) continue;
            for (Map<String, Object> receiving
                    : rows(region.get("symbolicInputs"))) {
                if (!COMMUNICATION_SITE_PORT.equals(
                        text(receiving.get("sourceKind")))
                        || !direction.equals(text(receiving.get(
                        CommunicationCatalogContract.PORT_DIRECTION)))) {
                    continue;
                }
                Map<String, Object> sending = declaredOutputPort(fromRegion,
                        text(receiving.get("portId")));
                if (sending != null && direction.equals(text(sending.get(
                        CommunicationCatalogContract.PORT_DIRECTION)))) {
                    result.add(new TypedReceiver(candidate, region,
                            receiving));
                }
            }
        }
        return result;
    }

    private static final class TypedReceiver {
        private final Map<String, Object> activation;
        private final Map<String, Object> region;
        private final Map<String, Object> port;

        private TypedReceiver(Map<String, Object> activation,
                              Map<String, Object> region,
                              Map<String, Object> port) {
            this.activation = activation;
            this.region = region;
            this.port = port;
        }
    }

    /**
     * Adds the occurrence-owned instance of one declared cut port, so demand
     * propagation can reach the exact activation that used it.  The region
     * keeps its own single declaration; this is an instance of it, stamped
     * with the occurrence that owned the crossing and the recorded order of
     * that crossing.  Re-stamping the same (port, occurrence) keeps the
     * earliest observed crossing; the exact producer edge retains each
     * individual crossing and its full order.
     */
    private static void stampOccurrenceOwnedPort(
            Map<String, Object> region, String listName,
            Map<String, Object> port, String occurrenceId, long eventSeq) {
        List<Map<String, Object>> rows = rows(region.get(listName));
        String portId = text(port.get("portId"));
        if (portId.isEmpty() || occurrenceId.isEmpty()) {
            return;
        }
        for (Map<String, Object> existing : rows) {
            if (portId.equals(text(existing.get("portId")))
                    && occurrenceId.equals(
                    text(existing.get("occurrenceId")))) {
                long previous = longNumber(existing.get("eventSeq"), -1L);
                if (eventSeq >= 0L && (previous < 0L || eventSeq < previous)) {
                    existing.put("eventSeq", eventSeq);
                }
                return;
            }
        }
        Map<String, Object> owned = new LinkedHashMap<>(port);
        owned.put("occurrenceId", occurrenceId);
        if (eventSeq >= 0L) owned.put("eventSeq", eventSeq);
        rows.add(owned);
        region.put(listName, rows);
    }

    /** The exporting region's own declaration of one declared cut port. */
    private static Map<String, Object> declaredOutputPort(
            Map<String, Object> region, String portId) {
        if (portId.isEmpty()) return null;
        for (Map<String, Object> port : rows(region.get("outputs"))) {
            if (COMMUNICATION_SITE_PORT.equals(text(port.get("sourceKind")))
                    && portId.equals(text(port.get("portId")))) {
                return port;
            }
        }
        return null;
    }

    /**
     * One scheduling candidate for a recorded delivery of a declared port.
     *
     * <p>It says a message crossed this boundary between these two
     * occurrences and that the send preceded the receive, so the exporting
     * occurrence has to run before the receiving one can be given anything.
     * It deliberately says nothing about the value: the expression that
     * crossed is the VM's export/attach handoff and its {@code VALUE_HANDOFF}
     * edge. This row remains scheduling evidence and is never upgraded into
     * a symbolic value relation.</p>
     */
    private static Map<String, Object> exchangeProducerEdge(
            Map<String, Object> from, Map<String, Object> to,
            Map<String, Object> link, Map<String, Object> receiving) {
        String portId = text(receiving.get("portId"));
        String identity = text(from.get("occurrenceId")) + "\n"
                + text(to.get("occurrenceId")) + "\n" + portId;
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("schemaVersion", 3);
        edge.put("kind", "RUNTIME_PROTOCOL_FLOW");
        edge.put("transportKind", text(link.get("transport")));
        edge.put("edgeId", "RPC." + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8)));
        edge.put("fromRegion", text(from.get("regionId")));
        edge.put("toRegion", text(to.get("regionId")));
        edge.put("fromPort", portId);
        edge.put("toPort", portId);
        edge.put("fromOccurrenceId", text(from.get("occurrenceId")));
        edge.put("toOccurrenceId", text(to.get("occurrenceId")));
        edge.put("fromRootCallId", from.get("rootCallId"));
        edge.put("toRootCallId", to.get("rootCallId"));
        edge.put("direction", text(link.get("direction")).toUpperCase());
        edge.put("attemptId", text(link.get("attemptId")));
        edge.put("senderEventSeq", link.get("senderEventSeq"));
        edge.put("receiverEventSeq", link.get("receiverEventSeq"));
        edge.put("requestApi", text(link.get("requestApi")));
        for (String field : new String[]{
                CommunicationCatalogContract.CALL_SITE_ID,
                CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                CommunicationCatalogContract.PORT_COMPONENT_OF,
                CommunicationCatalogContract.PORT_ENCODING_AUTHORITY}) {
            Object value = receiving.get(field);
            if (value != null && !text(value).isEmpty()) {
                edge.put(field, value);
            }
        }
        edge.put("dependencyRole", DependencyRole.normalize(
                receiving.get("dependencyRole")));
        edge.put("javaType", text(receiving.get("javaType")));
        edge.put("correlationAuthority",
                AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        edge.put("authority", AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        return edge;
    }

    /** Region-level port declarations, excluding occurrence-owned copies. */
    private static Set<String> declaredPortIds(
            List<Map<String, Object>> ports) {
        Set<String> ids = new LinkedHashSet<>();
        for (Map<String, Object> port : ports) {
            if (!text(port.get("occurrenceId")).isEmpty()) continue;
            String id = text(port.get("portId"));
            if (!id.isEmpty()) ids.add(id);
        }
        return ids;
    }

    /**
     * Mints one {@code occurrenceId} per observed region activation and
     * stamps it onto every row the recorded root call named.
     *
     * <p>This runs before the failure closure, not after it.  An ordinal is
     * therefore reserved for every observed activation, retained or not,
     * which is also what the replay admission counter sees: at replay every
     * observed root entry happens again, so a discarded activation still
     * consumes its position.  The runtime planner reserves over the same
     * ordered seeds one stage later and fails closed on any disagreement.</p>
     *
     * <p>The ordinal is counted over the <em>root</em> source, while the
     * identity prefix is the <em>semantic</em> source: for a target region,
     * the source of the event the selected failure branch was observed on.
     * Those two are deliberately different inputs.</p>
     */
    private static Map<String, Map<String, Object>> mintOccurrences(
            Map<String, List<Map<String, Object>>> targetPoliciesByRegion,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeBranchObservations,
            File source, List<Map<String, Object>> gaps) throws IOException {
        List<Map<String, Object>> observations = orderedBranchObservations(
                runtimeBranchObservations);
        OccurrenceMinter minter = new OccurrenceMinter();
        Map<String, Map<String, Object>> byOccurrence = new LinkedHashMap<>();
        for (Map<String, Object> instance : runtimeInstances == null
                ? Collections.<Map<String, Object>>emptyList()
                : runtimeInstances) {
            if (!"RUNTIME_REGION_ACTIVATION".equals(
                    text(instance.get("kind")))) {
                throw new IOException("invalid runtime region activation: "
                        + source);
            }
            String regionId = text(instance.get("regionId"));
            long rootCallId = longNumber(instance.get("rootCallId"), -1L);
            if (regionId.isEmpty() || rootCallId < 0L) {
                throw new IOException("runtime region activation requires "
                        + "regionId and rootCallId: " + source);
            }
            String rootSourceKey = activationSourceKey(instance);
            if (text(instance.get("sourceKey")).isEmpty()) {
                // The declared unregistered-workload key still scopes the
                // count, but it is not an attribution: publish the gap and
                // say so on the row rather than letting a reader take the
                // default for a stamped source.
                instance.put("sourceAuthority",
                        GAP_RUNTIME_SOURCE_UNSTAMPED);
                gaps.add(gap(GAP_RUNTIME_SOURCE_UNSTAMPED,
                        "NO_REGISTERED_TRACE_SOURCE",
                        text(instance.get("activationId")),
                        text(instance.get("rootMethod")), "", regionId));
            } else {
                instance.put("sourceAuthority", "EXPLICIT_TRACE_SOURCE");
            }
            int ordinal = minter.reserveOrdinal(rootSourceKey, regionId);
            String occurrenceId;
            try {
                occurrenceId = minter.mint(regionId, rootCallId,
                        semanticSourceKey(targetPoliciesByRegion.get(regionId),
                                instance, observations, rootSourceKey),
                        ordinal);
            } catch (IllegalArgumentException duplicate) {
                throw new IOException("duplicate runtime region activation: "
                        + regionId + "\n" + rootCallId);
            }
            instance.put("occurrenceId", occurrenceId);
            instance.put("occurrenceIndex", ordinal);
            byOccurrence.put(occurrenceId, instance);
        }
        return byOccurrence;
    }

    /** True when this skeleton's methods were observed in the trace. */
    private static boolean selectedRegion(Map<String, Object> skeleton,
                                          Set<String> observed) {
        List<String> methods = strings(skeleton.get("methods"));
        return !methods.isEmpty()
                && (observed.isEmpty()
                || !Collections.disjoint(methods, observed));
    }

    /**
     * The failure-target guard sites of one region, in the order
     * {@link #branches} would publish them.
     *
     * <p>A site is a failure target exactly when the refined graph has an
     * exception guard on it, and its required outcome is decided by those
     * exception guards alone.  Neither answer depends on the demanded method
     * scope, which is why the identity of an activation can be minted before
     * the region's ports and its full branch policy exist.</p>
     */
    /** Branch-policy member naming the throw a failure guard controls. */
    public static final String FAILURE_TARGET_CELLS = "failureTargetCells";

    private static List<Map<String, Object>> failureTargetPolicies(
            List<Map<String, Object>> regionGraph) {
        Map<String, List<Map<String, Object>>> failureGuardsBySite =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : regionGraph) {
            if (!"GUARD".equals(text(edge.get("transferKind")))) continue;
            String site = first(text(edge.get("guardSiteId")),
                    text(edge.get("siteId")));
            if (site.isEmpty()) continue;
            failureGuardsBySite.computeIfAbsent(site,
                    ignored -> new ArrayList<>());
            if (isExceptionTargetEdge(edge)) {
                failureGuardsBySite.get(site).add(edge);
            }
        }
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map.Entry<String, List<Map<String, Object>>> entry
                : failureGuardsBySite.entrySet()) {
            if (entry.getValue().isEmpty()) continue;
            Map<String, Object> policy = new LinkedHashMap<>();
            policy.put("siteId", entry.getKey());
            policy.put("failureTarget", true);
            policy.put("requiredOutcome",
                    consistentRequiredOutcome(entry.getValue()));
            result.add(policy);
        }
        return result;
    }

    /**
     * The stable logical scope current when this activation's root method was
     * entered.  An activation recorded without one was traced under the
     * declared unregistered-workload source, never under an inferred one.
     */
    private static String activationSourceKey(Map<String, Object> instance) {
        String sourceKey = text(instance.get("sourceKey"));
        return sourceKey.isEmpty()
                ? OccurrenceMinter.UNREGISTERED_SOURCE_KEY : sourceKey;
    }

    /**
     * The source that owns the relation of this activation.  A target region
     * attributes its relation to the event the selected failure branch was
     * observed on, which may be a different source from the one current at
     * root entry; every other region is its own root's source.
     */
    private static String semanticSourceKey(
            List<Map<String, Object>> targetPolicies,
            Map<String, Object> instance,
            List<Map<String, Object>> observations, String rootSourceKey) {
        if (targetPolicies == null || !text(instance.get("selection"))
                .startsWith("EXCEPTION")) {
            return rootSourceKey;
        }
        Set<Long> calls = longValues(instance.get("callIds"));
        for (Map<String, Object> branch : targetPolicies) {
            Map<String, Object> selected = selectedBranchObservation(branch,
                    calls, observations);
            if (selected == null) continue;
            String selectedSourceKey = text(selected.get("callSourceKey"));
            if (selectedSourceKey.isEmpty()) continue;
            return selectedSourceKey;
        }
        return rootSourceKey;
    }

    /**
     * The exact branch occurrence a replay of this activation would select:
     * the first observation of the site whose outcome equals the required
     * one, or the first observation when the policy demands no outcome.
     */
    private static Map<String, Object> selectedBranchObservation(
            Map<String, Object> branch, Set<Long> calls,
            List<Map<String, Object>> observations) {
        String site = text(branch.get("siteId"));
        if (site.isEmpty()) return null;
        List<Map<String, Object>> occurrences = new ArrayList<>();
        for (Map<String, Object> observation : observations) {
            if (site.equals(text(observation.get("siteId")))
                    && calls.contains(longNumber(
                    observation.get("callId"), -1L))) {
                occurrences.add(observation);
            }
        }
        if (occurrences.isEmpty()) return null;
        Object required = branch.get("requiredOutcome");
        if (required instanceof Boolean) {
            for (Map<String, Object> occurrence : occurrences) {
                if (required.equals(occurrence.get("outcome"))) {
                    return occurrence;
                }
            }
        }
        return occurrences.get(0);
    }

    /** Exact BRANCH observations in observed order. */
    private static List<Map<String, Object>> orderedBranchObservations(
            Collection<Map<String, Object>> runtimeBranchObservations) {
        List<Map<String, Object>> observations = new ArrayList<>();
        if (runtimeBranchObservations != null) {
            for (Map<String, Object> observation
                    : runtimeBranchObservations) {
                if ("BRANCH".equals(text(observation.get("kind")))) {
                    observations.add(observation);
                }
            }
        }
        observations.sort(Comparator.comparingLong(value ->
                longNumber(value.get("eventSeq"), Long.MAX_VALUE)));
        return observations;
    }

    /**
     * Adds activation-local fatal-target evidence by intersecting exact
     * runtime BRANCH sites with static {@code failureTarget} branch policies.
     * The concrete outcome is evidence for replay; it need not already equal
     * the failure outcome because concolic execution is expected to flip it.
     */
    private static void bindObservedFatalTargets(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> graph,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeBranchObservations) {
        Map<String, Map<String, Map<String, Object>>> targets =
                new LinkedHashMap<>();
        for (Map<String, Object> region : regions) {
            String regionId = text(region.get("regionId"));
            for (Map<String, Object> branch
                    : rows(region.get("branchPolicies"))) {
                if (!Boolean.TRUE.equals(booleanValue(
                        branch.get("failureTarget")))) {
                    continue;
                }
                String site = text(branch.get("siteId"));
                if (!site.isEmpty()) {
                    targets.computeIfAbsent(regionId,
                            ignored -> new LinkedHashMap<>()).put(site,
                            branch);
                }
            }
        }
        if (targets.isEmpty() || runtimeInstances == null) return;

        Map<String, List<String>> targetCellsByRegionSite =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : graph) {
            if (!"GUARD".equals(text(edge.get("transferKind")))
                    || !isExceptionTargetEdge(edge)) {
                continue;
            }
            String site = first(text(edge.get("guardSiteId")),
                    text(edge.get("siteId")));
            String targetCell = text(edge.get("toCell"));
            for (String regionId : strings(edge.get("regionIds"))) {
                if (targets.getOrDefault(regionId,
                        Collections.<String, Map<String, Object>>emptyMap())
                        .containsKey(site)) {
                    List<String> cells = targetCellsByRegionSite
                            .computeIfAbsent(contextKey(regionId, site),
                                    ignored -> new ArrayList<>());
                    if (!targetCell.isEmpty()
                            && !cells.contains(targetCell)) {
                        cells.add(targetCell);
                    }
                }
            }
        }

        List<Map<String, Object>> observations = runtimeBranchObservations
                == null ? Collections.<Map<String, Object>>emptyList()
                : new ArrayList<>(runtimeBranchObservations);
        observations.sort(Comparator.comparingLong(value ->
                longNumber(value.get("eventSeq"), Long.MAX_VALUE)));
        for (Map<String, Object> instance : runtimeInstances) {
            String regionId = text(instance.get("regionId"));
            Map<String, Map<String, Object>> regionTargets = targets.get(
                    regionId);
            if (regionTargets == null || regionTargets.isEmpty()) continue;

            Set<Long> calls = longValues(instance.get("callIds"));
            List<Map<String, Object>> bound = rows(
                    instance.get("observedFatalTargets"));
            for (Map<String, Object> observation : observations) {
                if (!"BRANCH".equals(text(observation.get("kind")))) {
                    continue;
                }
                long callId = longNumber(observation.get("callId"), -1L);
                if (!calls.contains(callId)) continue;
                String site = text(observation.get("siteId"));
                Map<String, Object> target = regionTargets.get(site);
                if (target == null
                        || !text(target.get("method")).equals(
                        text(observation.get("method")))
                        || !(observation.get("outcome") instanceof Boolean)) {
                    continue;
                }
                Map<String, Object> evidence = new LinkedHashMap<>();
                evidence.put("schemaVersion", 1);
                evidence.put("kind", "OBSERVED_FATAL_TARGET");
                evidence.put("evidenceAuthority",
                        "EXACT_RUNTIME_BRANCH_SITE_V1");
                evidence.put("siteId", site);
                evidence.put("method", target.get("method"));
                evidence.put("unitIndex", target.get("unitIndex"));
                evidence.put("operandCells", target.get("operandCells"));
                evidence.put("targetCells",
                        targetCellsByRegionSite.getOrDefault(
                                contextKey(regionId, site),
                                Collections.<String>emptyList()));
                evidence.put("requiredOutcome", target.get(
                        "requiredOutcome"));
                evidence.put("observedOutcome", observation.get("outcome"));
                evidence.put("eventSeq", observation.get("eventSeq"));
                evidence.put("callId", callId);
                bound.add(evidence);
            }
            if (!bound.isEmpty()) {
                bound.sort(Comparator.comparingLong(value ->
                        longNumber(value.get("eventSeq"), Long.MAX_VALUE)));
                instance.put("observedFatalTargets", bound);
            }
        }
    }

    private static boolean isExceptionTargetEdge(Map<String, Object> edge) {
        return "exception_guard".equals(text(edge.get("kind")))
                || text(edge.get("toCell")).contains("#exception:");
    }

    private static void addUnique(Map<String, List<String>> target,
                                  String key, String value) {
        List<String> values = target.computeIfAbsent(key,
                ignored -> new ArrayList<String>());
        if (!values.contains(value)) values.add(value);
    }

    private static Set<Long> longValues(Object value) {
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

    /**
     * Retains the concrete producer activations and ports that can reach an
     * observed exception through confirmed heap or protocol flow.  The work
     * list is a demanded input port, not merely a region activation: after a
     * cross-region edge is selected, the producer output is sliced backward
     * to the exact producer inputs on which that output depends.  Multiple
     * demanded outputs of one producer are unioned in the same transition.
     */
    private static RuntimeClosure failureDirectedClosure(
            StaticProgram program,
            List<Map<String, Object>> graph,
            Map<String, Map<String, Object>> activations,
            File source, List<Map<String, Object>> gaps) throws IOException {
        Map<String, Map<String, Object>> instances =
                new LinkedHashMap<>(activations);
        if (instances.isEmpty()) {
            throw new IOException("runtime failure closure requires concrete "
                    + "region activations: " + source);
        }

        RegionDemandIndex demands = new RegionDemandIndex(
                program.regions, graph);
        // `selection` describes the static region skeleton, so every
        // activation of an exception-context region inherits it, including
        // the concurrent activations that only produced inputs for the one
        // that failed.  Being a closure target is an activation-local fact:
        // it requires this activation to have observed one of its region's
        // explicit failureTarget sites.  Activations that did not observe one
        // are ordinary closure participants and are still retained through
        // the producer walk below.
        Set<String> contexts = new LinkedHashSet<>();
        Set<String> targets = new LinkedHashSet<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : activations.entrySet()) {
            if (!text(entry.getValue().get("selection"))
                    .startsWith("EXCEPTION")) {
                continue;
            }
            contexts.add(entry.getKey());
            if (demands.observedExplicitFatalTarget(entry.getValue())) {
                targets.add(entry.getKey());
            }
        }
        if (contexts.isEmpty()) {
            throw new IOException("runtime failure closure found no observed "
                    + "exception-context activation: " + source);
        }
        if (targets.isEmpty()) {
            // A workload that never reached the declared failure site has no
            // failure to explain.  Naming the gap keeps that fail-closed
            // instead of silently emitting an evidence-free target plan.
            throw new IOException("FATAL_TARGET_OBSERVATION_GAP: no "
                    + "exception-context activation observed its explicit "
                    + "fatal target branch: " + source);
        }
        String selectedTarget = System.getProperty(
                "causynth.failure.target.occurrence", "").trim();
        if (!selectedTarget.isEmpty()) {
            if (!targets.contains(selectedTarget)) {
                throw new IOException("selected fatal target occurrence was "
                        + "not observed: " + selectedTarget);
            }
            targets.retainAll(Collections.singleton(selectedTarget));
        }

        Set<String> admittedStateWriters = new LinkedHashSet<>(
                admitSharedLocationWriters(targets, instances, demands,
                        program.regionEdges));

        Map<String, List<Map<String, Object>>> predecessors =
                new LinkedHashMap<>();
        Set<String> targetInteractionInputs = new LinkedHashSet<>();
        for (Map<String, Object> edge : program.regionEdges) {
            if (!causalRegionRetentionEdge(edge)) {
                continue;
            }
            String from = text(edge.get("fromOccurrenceId"));
            String to = text(edge.get("toOccurrenceId"));
            if (!instances.containsKey(from) || !instances.containsKey(to)) {
                throw new IOException("runtime causal edge references an "
                        + "unselected activation: "
                        + text(edge.get("edgeId")));
            }
            String toPort = text(edge.get("toPort"));
            String fromPort = text(edge.get("fromPort"));
            if (toPort.isEmpty() || fromPort.isEmpty()
                    || !demands.hasInput(to, toPort)
                    || !demands.hasOutput(from, fromPort)) {
                throw new IOException("runtime causal edge references an "
                        + "unknown exact port: " + text(edge.get("edgeId")));
            }
            predecessors.computeIfAbsent(portDemandKey(to, toPort),
                    ignored -> new ArrayList<>()).add(edge);
            if ("RUNTIME_PROTOCOL_FLOW".equals(text(edge.get("kind")))
                    && targets.contains(to)
                    && DependencyRole.valueFrontier(
                    edge.get("dependencyRole"))) {
                // The fatal region instance was entered through this exact
                // observed interaction.  Component ports have no Java local
                // cell because the VM attaches their expressions directly,
                // so event-level causality (rather than a synthetic local)
                // is the authority that keeps them in the failure closure.
                targetInteractionInputs.add(portDemandKey(to, toPort));
            }
        }

        ClosureWalk union = walkFailureClosure(targets, instances,
                demands, predecessors, targetInteractionInputs,
                admittedStateWriters,
                gaps);
        // Heap demand is transitive with port demand: each walk may reach a
        // producer that itself reads a written location, so admit the
        // writers of what this walk demanded and walk again.  The loop stops
        // when no new writer is admitted, which it must: every round can only
        // add occurrences, and there are finitely many.
        while (true) {
            Set<String> grown = admitWritersOfDemands(union.reached,
                    union.demandedInputs, instances, program.regionEdges);
            if (!admittedStateWriters.addAll(grown)) break;
            union = walkFailureClosure(targets, instances, demands,
                    predecessors, targetInteractionInputs,
                    admittedStateWriters, gaps);
        }
        return new RuntimeClosure(instances, union.reached,
                union.retainedEdges, union.demandedInputs,
                union.demandedOutputs);
    }

    /**
     * Admits only an observed production writer joined to a fatal input by an
     * exact runtime field-flow edge.  The edge was built from receiver object
     * identity and the declared leaf, so a same-named field in another NN,
     * Balancer or test object cannot enter this set.
     *
     * <p>The admission is stamped on the original activation object.  The
     * runtime planner consumes that same seed after finalization and copies
     * these existing fields to the retained occurrence's plan row.
     * This is membership authority for later writer materialization, not a
     * synthetic read-from edge.</p>
     */
    private static Set<String> admitSharedLocationWriters(
            Set<String> targets,
            Map<String, Map<String, Object>> instances,
            RegionDemandIndex demands,
            List<Map<String, Object>> regionEdges) throws IOException {
        Set<String> fatalInputs = new LinkedHashSet<>();
        for (String target : targets) {
            fatalInputs.addAll(demands.targetInputs(instances.get(target)));
        }
        return admitWritersOfDemands(targets, fatalInputs, instances,
                regionEdges);
    }

    /**
     * Admits the observed writers of the shared locations {@code demanding}
     * occurrences read, joined by exact runtime field-flow edges.
     *
     * <p>Demand through a port is transitive - the walk crosses a call from a
     * demanded input to whichever occurrence declared its output - and demand
     * through the heap has to be transitive with it.  A producer the walk
     * reached may itself read a location some third occurrence wrote, one hop
     * further from the failure than the target; admitting only the target's
     * own writers leaves that hop with no writer at all, and the producer is
     * then retained with an input nothing in the model produces.</p>
     */
    private static Set<String> admitWritersOfDemands(
            Collection<String> demanding,
            Set<String> demandedInputs,
            Map<String, Map<String, Object>> instances,
            List<Map<String, Object>> regionEdges) throws IOException {
        Set<String> targets = new LinkedHashSet<>(demanding);
        Set<String> fatalInputs = demandedInputs;
        Map<String, Set<String>> locationsByWriter = new LinkedHashMap<>();
        Map<String, Set<String>> targetRegionsByWriter =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : regionEdges) {
            if (!"RUNTIME_FIELD_FLOW".equals(text(edge.get("kind")))) {
                continue;
            }
            String consumer = text(edge.get("toOccurrenceId"));
            String writer = text(edge.get("fromOccurrenceId"));
            String input = portDemandKey(consumer,
                    text(edge.get("toPort")));
            if (!targets.contains(consumer) || writer.equals(consumer)
                    || !fatalInputs.contains(input)
                    || !instances.containsKey(writer)) {
                continue;
            }
            String location = text(edge.get(RecordedReadFrom.EDGE_FIELD));
            if (location.isEmpty()) {
                continue;
            }
            locationsByWriter.computeIfAbsent(writer,
                    ignored -> new LinkedHashSet<>()).add(location);
            targetRegionsByWriter.computeIfAbsent(writer,
                    ignored -> new TreeSet<>()).add(text(
                    instances.get(consumer).get("regionId")));
        }

        Set<String> admitted = new LinkedHashSet<>();
        for (Map.Entry<String, Set<String>> entry
                : locationsByWriter.entrySet()) {
            String writer = entry.getKey();
            Set<String> consumerRegions = targetRegionsByWriter.getOrDefault(
                    writer, Collections.<String>emptySet());
            if (consumerRegions.isEmpty()) {
                continue;
            }
            Map<String, Object> activation = instances.get(writer);
            String existingBasis = text(activation.get(ADMISSION_BASIS));
            if (!existingBasis.isEmpty()
                    && !SHARED_LOCATION_DEMAND_ADMISSION.equals(
                    existingBasis)) {
                throw new IOException("conflicting runtime activation "
                        + "admission basis for " + writer + ": "
                        + existingBasis);
            }
            Set<String> demandedBy = new TreeSet<>(strings(
                    activation.get(DEMANDED_BY_REGIONS)));
            demandedBy.addAll(consumerRegions);
            Set<String> locations = new LinkedHashSet<>(strings(
                    activation.get(DEMANDED_SHARED_LOCATIONS)));
            locations.addAll(entry.getValue());
            activation.put(ADMISSION_BASIS,
                    SHARED_LOCATION_DEMAND_ADMISSION);
            activation.put(DEMANDED_BY_REGIONS,
                    new ArrayList<>(demandedBy));
            activation.put(DEMANDED_SHARED_LOCATIONS,
                    new ArrayList<>(locations));
            admitted.add(writer);
        }
        return admitted;
    }

    private static ClosureWalk walkFailureClosure(
            Collection<String> targets,
            Map<String, Map<String, Object>> instances,
            RegionDemandIndex demands,
            Map<String, List<Map<String, Object>>> predecessors,
            Collection<String> targetInteractionInputs,
            Set<String> admittedStateWriters,
            List<Map<String, Object>> gaps)
            throws IOException {
        Set<String> reached = new LinkedHashSet<>(targets);
        Set<String> retainedEdges = new LinkedHashSet<>();
        Set<String> demandedInputs = new LinkedHashSet<>();
        Set<String> expandedInputOccurrences = new LinkedHashSet<>();
        Set<String> demandedOutputs = new LinkedHashSet<>();
        Set<String> expandedOutputOccurrences = new LinkedHashSet<>();
        Deque<InputDemand> work = new ArrayDeque<>();
        for (String target : targets) {
            Map<String, Object> instance = instances.get(target);
            // A target input serves the failure itself and no producer
            // write, so it states no order for its predecessors to precede.
            addDemands(work, demands.targetInputs(instance),
                    InputDemand.NO_ORDER);
        }
        addDemands(work, targetInteractionInputs, InputDemand.NO_ORDER);
        // A selected writer is retained even when nothing demands one of its
        // outputs yet: the bounded NN heartbeat predecessors stay in the
        // closure without any of them becoming a read-from arm before replay
        // records a write/version.
        for (String writer : admittedStateWriters) {
            Map<String, Object> instance = instances.get(writer);
            if (instance == null) continue;
            reached.add(writer);
        }
        // Communication is represented by exact occurrence-owned IN/OUT
        // ports in predecessors, so the walk crosses a call the same way it
        // crosses any other edge: from the demanded input port to the output
        // port some other occurrence declared for it.
        while (!work.isEmpty()) {
            InputDemand demanded = work.removeFirst();
            demandedInputs.add(demanded.key);
            // One coarse occurrence can receive the same port many times
            // and publish several dynamic versions of one output.  The
            // predecessor set is relative to the exact output boundary, so
            // deduplicating only by port permanently keeps the candidates of
            // whichever (usually earliest) version happened to be visited
            // first.  Keep the port-level set for applyClosure, but expand
            // each event-local demand independently.  This is the event
            // instance distinction; it does not split the enclosing region
            // or create another replay task identity.
            String inputOccurrence = demanded.key + "\nORDER\n"
                    + demanded.order;
            if (!expandedInputOccurrences.add(inputOccurrence)) continue;
            for (Map<String, Object> edge : boundedPredecessors(
                    predecessors.getOrDefault(demanded.key,
                            Collections.<Map<String, Object>>emptyList()),
                    demanded.order)) {
                String edgeId = text(edge.get("edgeId"));
                if (edgeId.isEmpty()) {
                    throw new IOException("runtime causal edge has no "
                            + "identity");
                }
                retainedEdges.add(edgeId);
                String fromOccurrence = text(edge.get("fromOccurrenceId"));
                reached.add(fromOccurrence);
                String outputDemand = portDemandKey(fromOccurrence,
                        text(edge.get("fromPort")));
                demandedOutputs.add(outputDemand);
                long writerEventSeq = producerEventSeq(edge);
                String occurrenceDemand = outputOccurrenceDemandKey(
                        outputDemand, writerEventSeq);
                if (expandedOutputOccurrences.add(occurrenceDemand)) {
                    long producedAt = writerEventSeq;
                    addDemands(work, demands.inputsForOutput(fromOccurrence,
                            text(edge.get("fromPort")), writerEventSeq),
                            producedAt);
                    addDemands(work, demands.priorCommunicationInputs(
                            fromOccurrence, producedAt), producedAt);
                    addDemands(work, demands.priorHeapValueInputs(
                            fromOccurrence, producedAt), producedAt);
                }
            }
        }
        return new ClosureWalk(reached, retainedEdges, demandedInputs,
                demandedOutputs);
    }

    /** One demanded input port, and the order its producers precede. */
    private static final class InputDemand {
        /** The demand states no order: nothing is known to follow it. */
        private static final long NO_ORDER = -1L;

        private final String key;
        private final long order;

        private InputDemand(String key, long order) {
            this.key = key;
            this.order = order;
        }
    }

    private static void addDemands(Deque<InputDemand> work,
                                   Collection<String> keys, long order) {
        for (String key : keys) work.add(new InputDemand(key, order));
    }

    /**
     * Materializes only the bounded selection of repeated writer occurrences.
     * Distinct producer channels remain distinct; repeated turns of one
     * service loop share the same structural channel and contribute at most
     * the state-timeline bound used by composition.
     *
     * <p>The bound states how many transitions of a timeline are modelled.
     * It states nothing about <em>which</em> region of that timeline matters,
     * so the selection is made relative to the read being served rather than
     * to the end of the run: a candidate ordered before {@code demandedOrder}
     * can serve that read and is offered nearest-first, and one ordered after
     * it cannot, because the same {@code w &lt; r} relation decides every
     * read-from arm downstream.  Ranking by recency alone spends the bound on
     * the timeline's tail, which for an early read is exactly the part that
     * cannot serve it - the run this rule replaced retained two deliveries
     * that arrived after the write they were selected to produce.</p>
     *
     * <p>A demand that states no order keeps the previous ordering, so a
     * target input - which serves the failure and no producer write - selects
     * exactly as it did.</p>
     */
    private static List<Map<String, Object>> boundedPredecessors(
            Collection<Map<String, Object>> candidates, long demandedOrder) {
        List<Map<String, Object>> eligible = new ArrayList<>();
        for (Map<String, Object> edge : candidates) {
            if (demandedOrder >= 0L) {
                String kind = text(edge.get("kind"));
                long producedAt = "RUNTIME_FIELD_FLOW".equals(kind)
                        ? producerEventSeq(edge)
                        : "RUNTIME_PROTOCOL_FLOW".equals(kind)
                        ? longNumber(edge.get("senderEventSeq"), -1L)
                        : -1L;
                long consumedAt = "RUNTIME_FIELD_FLOW".equals(kind)
                        ? longNumber(edge.get("readerEventSeq"), -1L)
                        : "RUNTIME_PROTOCOL_FLOW".equals(kind)
                        ? longNumber(edge.get("receiverEventSeq"), -1L)
                        : -1L;
                if (("RUNTIME_FIELD_FLOW".equals(kind)
                        || "RUNTIME_PROTOCOL_FLOW".equals(kind))
                        && (producedAt < 0L || consumedAt < 0L
                        || producedAt >= consumedAt
                        || consumedAt >= demandedOrder)) {
                    continue;
                }
            }
            eligible.add(edge);
        }
        if (eligible.size()
                <= LoopBoundPolicy.MAX_STATE_TIMELINE_TRANSITIONS) {
            return eligible;
        }
        List<Map<String, Object>> ordered = new ArrayList<>(eligible);
        ordered.sort((left, right) -> {
            int precedence = Boolean.compare(
                    !precedes(right, demandedOrder),
                    !precedes(left, demandedOrder));
            return precedence != 0 ? precedence : Long.compare(
                    causalEventSeq(right), causalEventSeq(left));
        });
        Map<String, Integer> retainedByChannel = new LinkedHashMap<>();
        List<Map<String, Object>> retained = new ArrayList<>();
        for (Map<String, Object> edge : ordered) {
            String channel = text(edge.get("kind")) + "\n"
                    + text(edge.get("fromRegion")) + "\n"
                    + text(edge.get("fromPort"));
            int count = retainedByChannel.getOrDefault(channel, 0);
            if (count >= LoopBoundPolicy.MAX_STATE_TIMELINE_TRANSITIONS) {
                continue;
            }
            retainedByChannel.put(channel, count + 1);
            retained.add(edge);
        }
        return retained;
    }

    /** Whether one candidate is ordered before the read it would serve. */
    private static boolean precedes(Map<String, Object> edge,
                                    long demandedOrder) {
        long seq = causalEventSeq(edge);
        return demandedOrder >= 0L && seq >= 0L && seq < demandedOrder;
    }

    private static long causalEventSeq(Map<String, Object> edge) {
        if ("RUNTIME_PROTOCOL_FLOW".equals(text(edge.get("kind")))) {
            return longNumber(edge.get("receiverEventSeq"), -1L);
        }
        long result = -1L;
        for (String field : new String[]{"writerEventSeq",
                "mutationCompletionSeq"}) {
            result = Math.max(result, longNumber(edge.get(field), -1L));
        }
        return result;
    }

    /** Exact instant at which one demanded producer published its output. */
    private static long producerEventSeq(Map<String, Object> edge) {
        if ("RUNTIME_PROTOCOL_FLOW".equals(text(edge.get("kind")))) {
            return longNumber(edge.get("senderEventSeq"), -1L);
        }
        return longNumber(edge.get("writerEventSeq"), -1L);
    }

    /**
     * Region retention needs an executable channel, not a same-declaration
     * hint. Exact heap identity and configured runtime RPC lineage are the two
     * channel authorities emitted by this finalizer.
     */
    private static boolean causalRegionRetentionEdge(
            Map<String, Object> edge) {
        String kind = text(edge.get("kind"));
        return "RUNTIME_FIELD_FLOW".equals(kind)
                || "RUNTIME_PROTOCOL_FLOW".equals(kind);
    }

    private static void applyClosure(StaticProgram program,
                                     RuntimeClosure closure)
            throws IOException {
        Set<String> retainedRegions = new LinkedHashSet<>();
        for (String key : closure.reached) {
            retainedRegions.add(text(closure.instances.get(key).get(
                    "regionId")));
        }
        program.regionEdges.removeIf(edge -> !closure.retainedEdges.contains(
                text(edge.get("edgeId"))));
        program.regions.removeIf(region -> !retainedRegions.contains(
                text(region.get("regionId"))));
        Map<String, Set<Long>> demandedAccesses =
                demandedRuntimeAccesses(program.regionEdges);
        // fatalPrefixContexts is the per-site authority.  A multi-site
        // activation is projected by site downstream and must never share one
        // max cutoff, so only an unambiguous single-site activation bounds its
        // own value-frontier ports here.
        Map<String, Long> fatalPrefixCutoffs = new LinkedHashMap<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : closure.instances.entrySet()) {
            List<Map<String, Object>> contexts = rows(
                    entry.getValue().get("fatalPrefixContexts"));
            if (contexts.size() != 1) continue;
            long cutoff = longNumber(contexts.get(0).get("eventSeq"), -1L);
            if (cutoff >= 0L) fatalPrefixCutoffs.put(entry.getKey(), cutoff);
        }

        for (Map<String, Object> region : program.regions) {
            String regionId = text(region.get("regionId"));
            Set<String> occurrences = new LinkedHashSet<>();
            for (String key : closure.reached) {
                Map<String, Object> instance = closure.instances.get(key);
                if (!regionId.equals(text(instance.get("regionId")))) {
                    continue;
                }
                occurrences.add(key);
            }
            // The activations this closure retained, named by identity.  The
            // runtime planner admits a seed by membership here, so nothing
            // downstream ever reads a recorded call id to decide retention.
            region.put("runtimeOccurrenceIds",
                    new ArrayList<>(occurrences));
            region.put("symbolicInputs", filterPorts(
                    rows(region.get("symbolicInputs")), regionId,
                    occurrences, false, closure.demandedInputs,
                    demandedAccesses, fatalPrefixCutoffs));
            region.put("outputs", filterPorts(
                    rows(region.get("outputs")), regionId,
                    occurrences, true, closure.demandedOutputs,
                    demandedAccesses, fatalPrefixCutoffs));
        }
    }

    private static List<Map<String, Object>> filterPorts(
            List<Map<String, Object>> ports, String regionId,
            Set<String> occurrences, boolean output,
            Set<String> demandedPorts,
            Map<String, Set<Long>> demandedAccesses,
            Map<String, Long> fatalPrefixCutoffs)
            throws IOException {
        List<Map<String, Object>> retained = new ArrayList<>();
        for (Map<String, Object> port : ports) {
            String occurrenceId = portOccurrenceId(port, output);
            String demand = portDemandKey(occurrenceId,
                    text(port.get("portId")));
            if (!occurrences.contains(occurrenceId)
                    || !demandedPorts.contains(demand)) {
                continue;
            }
            // Region definitions are shared by all observed target
            // occurrences.  Every retained occurrence gets its own shallow
            // port row so one fatal cutoff cannot trim another occurrence's
            // canonical runtime-access catalog.
            Map<String, Object> selected = new LinkedHashMap<>(port);
            Long cutoff = output ? null
                    : fatalPrefixCutoffs.get(occurrenceId);
            if (cutoff != null && DependencyRole.valueFrontier(
                    selected.get("dependencyRole"))) {
                trimFatalPrefixAccesses(selected, cutoff);
            }
            retainExactRuntimeAccesses(selected, demand, output,
                    demandedAccesses.getOrDefault(demand,
                            Collections.<Long>emptySet()));
            retained.add(selected);
        }
        return retained;
    }

    private static void trimFatalPrefixAccesses(
            Map<String, Object> port, long cutoff) {
        List<Map<String, Object>> accesses = rows(
                port.get("runtimeAccesses"));
        if (!accesses.isEmpty()) {
            List<Map<String, Object>> prefix = new ArrayList<>();
            for (Map<String, Object> access : accesses) {
                long event = longNumber(access.get("eventSeq"), -1L);
                if (event >= 0L && event <= cutoff) prefix.add(access);
            }
            port.put("runtimeAccesses", prefix);
            port.put("fatalPrefixAuthority",
                    "EXACT_RUNTIME_ACCESS_PREFIX_V1");
        } else if ("ACCESSOR_RETURN".equals(
                text(port.get("sourceKind")))) {
            port.put("fatalPrefixAuthority",
                    "EXACT_RUNTIME_ACCESSOR_PREFIX_V1");
        }
    }

    /** Keeps only concrete accesses selected by retained causal edges. */
    private static Map<String, Set<Long>> demandedRuntimeAccesses(
            Collection<Map<String, Object>> edges) {
        Map<String, Set<Long>> result = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"RUNTIME_FIELD_FLOW".equals(text(edge.get("kind")))) {
                continue;
            }
            addDemandedAccess(result, text(edge.get("fromOccurrenceId")),
                    text(edge.get("fromPort")),
                    longNumber(edge.get("writerEventSeq"), -1L));
            addDemandedAccess(result, text(edge.get("toOccurrenceId")),
                    text(edge.get("toPort")),
                    longNumber(edge.get("readerEventSeq"), -1L));
        }
        return result;
    }

    private static void addDemandedAccess(
            Map<String, Set<Long>> target, String occurrenceId,
            String port, long eventSeq) {
        if (occurrenceId.isEmpty() || port.isEmpty() || eventSeq < 0L) {
            return;
        }
        target.computeIfAbsent(portDemandKey(occurrenceId, port),
                ignored -> new LinkedHashSet<>()).add(eventSeq);
    }

    private static void retainExactRuntimeAccesses(
            Map<String, Object> port, String demand, boolean output,
            Set<Long> eventSeqs) throws IOException {
        if (!"HEAP".equals(text(port.get("transportKind")))) return;
        // The retained edges name their occurrences exactly, so those survive
        // the per-site resource cap; anything else stays a bounded default.
        List<Map<String, Object>> accesses = boundedRuntimeAccesses(port,
                (owner, access) -> eventSeqs.contains(longNumber(
                        access.get("eventSeq"), -1L)));
        if (accesses.isEmpty()) {
            throw new IOException("demanded heap port has no runtime access: "
                    + demand);
        }
        accesses.sort(Comparator.comparingLong(access ->
                longNumber(access.get("eventSeq"), Long.MAX_VALUE)));
        List<Map<String, Object>> exact = new ArrayList<>();
        if (!eventSeqs.isEmpty()) {
            for (Map<String, Object> access : accesses) {
                if (eventSeqs.contains(longNumber(
                        access.get("eventSeq"), -1L))) {
                    exact.add(access);
                }
            }
        } else {
            // No edge selected an individual occurrence. Keep the bounded
            // static-site alternatives; never leak an unbounded long-lived
            // loop's aggregate access array into one concolic task.
            exact.addAll(accesses);
        }
        if (exact.isEmpty()) {
            throw new IOException("causal edge occurrence is absent from "
                    + "demanded heap port: " + demand + " events="
                    + eventSeqs);
        }
        port.put("runtimeAccesses", exact);
        if (exact.size() == 1) {
            copyRuntimeOccurrence(exact.get(0), port);
            String site = text(port.get("staticAccessSiteId"));
            if (!site.isEmpty()) port.put("siteId", site);
        }
    }

    /** The activation that owns this port. */
    private static String portOccurrenceId(Map<String, Object> port,
                                           boolean output) {
        return text(port.get("occurrenceId"));
    }

    private static String portDemandKey(String occurrenceId,
                                        String portId) {
        return occurrenceId + "\n" + portId;
    }

    private static String outputOccurrenceDemandKey(
            String outputDemand, long writerEventSeq) {
        return outputDemand + "\nEVENT\n" + writerEventSeq;
    }

    /**
     * Resolves the recorded root call each observed flow endpoint named to
     * the activation identity minted for it.  This and
     * {@link #mintOccurrences} are the only places the finalizer reads a
     * trace call id as identity; every consumer downstream of them compares
     * {@code occurrenceId}.
     */
    private static void stampEdgeOccurrences(
            Collection<Map<String, Object>> edges,
            Map<String, String> byRecordedRootCall) {
        for (Map<String, Object> edge : edges) {
            String from = byRecordedRootCall.get(recordedRootCallKey(
                    text(edge.get("fromRegion")),
                    longNumber(edge.get("fromRootCallId"), -1L)));
            if (from != null) edge.put("fromOccurrenceId", from);
            String to = byRecordedRootCall.get(recordedRootCallKey(
                    text(edge.get("toRegion")),
                    longNumber(edge.get("toRootCallId"), -1L)));
            if (to != null) edge.put("toOccurrenceId", to);
        }
    }

    /**
     * Recorded root call of each activation, mapped to the identity minted
     * for it.  Raw refined-graph rows carry only that trace evidence, so
     * this table is the single place they are resolved to an occurrence.
     */
    private static Map<String, String> recordedRootCallIndex(
            Map<String, Map<String, Object>> activations) {
        Map<String, String> result = new LinkedHashMap<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : activations.entrySet()) {
            result.put(recordedRootCallKey(
                    text(entry.getValue().get("regionId")),
                    longNumber(entry.getValue().get("rootCallId"), -1L)),
                    entry.getKey());
        }
        return result;
    }

    private static String recordedRootCallKey(String regionId,
                                              long rootCallId) {
        return regionId + "\n" + rootCallId;
    }

    private static void annotateFlowContexts(
            List<Map<String, Object>> edges,
            Map<String, Map<String, Object>> activations) {
        for (Map<String, Object> edge : edges) {
            Map<String, Object> from = activations.get(
                    text(edge.get("fromOccurrenceId")));
            Map<String, Object> to = activations.get(
                    text(edge.get("toOccurrenceId")));
            copyContext(edge, "from", from);
            copyContext(edge, "to", to);
            long writerLane = longNumber(edge.get("fromLaneId"), -1L);
            long readerLane = longNumber(edge.get("toLaneId"), -1L);
            if (writerLane > 0L) edge.put("writerLaneId", writerLane);
            if (readerLane > 0L) edge.put("readerLaneId", readerLane);
            edge.put("programOrderRequired",
                    writerLane > 0L && writerLane == readerLane);
        }
    }

    /**
     * Marks only retained, failure-directed container mutation flows as
     * symbolic state.  The exact declared ports select the Map carrier; the
     * VM owns its state versions and mutation/query semantics.
     */
    private static void markBoundedContainerStatePorts(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> fieldEdges) {
        Map<String, Map<String, Object>> regionsById =
                new LinkedHashMap<>();
        for (Map<String, Object> region : regions) {
            regionsById.put(text(region.get("regionId")), region);
        }
        for (Map<String, Object> edge : fieldEdges) {
            if (!"RUNTIME_FIELD_FLOW".equals(text(edge.get("kind")))
                    || !"CONTAINER_MUTATION".equals(
                    text(edge.get("bindingKind")))) {
                continue;
            }
            List<String> declarations = strings(
                    edge.get("fieldPathDeclarations"));
            DeclaredFieldCell leaf = declarations.isEmpty() ? null
                    : DeclaredFieldCell.parse(
                    declarations.get(declarations.size() - 1));
            if (leaf == null || JavaContainerTypes.shape(leaf.type)
                    == JavaContainerTypes.Shape.NONE) {
                continue;
            }

            String fromRegion = text(edge.get("fromRegion"));
            String toRegion = text(edge.get("toRegion"));
            String fromOccurrence = text(edge.get("fromOccurrenceId"));
            String toOccurrence = text(edge.get("toOccurrenceId"));
            Map<String, Object> producerRegion = regionsById.get(fromRegion);
            Map<String, Object> consumerRegion = regionsById.get(toRegion);
            Map<String, Object> output = exactRegionPort(producerRegion,
                    "outputs", text(edge.get("fromPort")), fromOccurrence,
                    true);
            Map<String, Object> consumer = exactRegionPort(consumerRegion,
                    "symbolicInputs", text(edge.get("toPort")), toOccurrence,
                    false);
            if (output == null || consumer == null) continue;
            markBoundedContainerPort(output, leaf.type);
            markBoundedContainerPort(consumer, leaf.type);
        }
    }

    private static Map<String, Object> exactRegionPort(
            Map<String, Object> region, String field, String portId,
            String occurrenceId, boolean output) {
        if (region == null || portId.isEmpty() || occurrenceId.isEmpty()) {
            return null;
        }
        Map<String, Object> selected = null;
        for (Map<String, Object> port : rows(region.get(field))) {
            if (!portId.equals(text(port.get("portId")))
                    || !occurrenceId.equals(portOccurrenceId(port, output))) {
                continue;
            }
            if (selected != null) return null;
            selected = port;
        }
        return selected;
    }

    private static void markBoundedContainerPort(
            Map<String, Object> port, String javaType) {
        port.put("javaType", javaType);
        port.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        port.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
    }

    /**
     * Marks primitive element fields that are part of a demanded container
     * transition rather than unrelated leaves of a transported reference.
     *
     * <p>The proof is deliberately narrow and name agnostic: an observed
     * primitive accessor must flow to an explorable, non-loop branch, and the
     * same branch must guard a mutation of the container output.  Only then
     * is the accessor retained as a bounded symbolic state frontier.  The
     * exact runtime output corridor later chooses which helper activation and
     * at most {@link LoopBoundPolicy#SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY}
     * element occurrences belong to the task.</p>
     */
    private static void markBoundedMutationStateFrontiers(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> refinedGraph) {
        Map<String, List<Map<String, Object>>> edgesByRegion =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : refinedGraph) {
            for (String regionId : strings(edge.get("regionIds"))) {
                edgesByRegion.computeIfAbsent(regionId,
                        ignored -> new ArrayList<>()).add(edge);
            }
        }

        for (Map<String, Object> region : regions) {
            String regionId = text(region.get("regionId"));
            List<Map<String, Object>> edges = edgesByRegion.getOrDefault(
                    regionId, Collections.<Map<String, Object>>emptyList());
            if (edges.isEmpty()) continue;

            Set<String> semanticSites = new LinkedHashSet<>();
            for (Map<String, Object> branch
                    : rows(region.get("branchPolicies"))) {
                if ("EXPLORE".equals(text(branch.get("policy")))
                        && !Boolean.TRUE.equals(booleanValue(
                        branch.get("loopControlGuard")))) {
                    String site = text(branch.get("siteId"));
                    if (!site.isEmpty()) semanticSites.add(site);
                }
            }
            if (semanticSites.isEmpty()) continue;

            Map<String, List<Map<String, Object>>> incoming =
                    new LinkedHashMap<>();
            for (Map<String, Object> edge : edges) {
                String to = text(edge.get("toCell"));
                if (!to.isEmpty()) {
                    incoming.computeIfAbsent(to,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
            Map<String, List<Map<String, Object>>> inputBoundaries =
                    new LinkedHashMap<>();
            for (Map<String, Object> input
                    : rows(region.get("symbolicInputs"))) {
                for (String cell : RegionDemandIndex.boundaryCells(input)) {
                    inputBoundaries.computeIfAbsent(cell,
                            ignored -> new ArrayList<>()).add(input);
                }
            }

            for (Map<String, Object> output : rows(region.get("outputs"))) {
                if (!"CONTAINER_MUTATION".equals(
                        text(output.get("bindingKind")))) {
                    continue;
                }
                String outputPort = text(output.get("portId"));
                for (String outputCell : mutationOutputCells(output)) {
                    for (Map<String, Object> guard : incoming.getOrDefault(
                            outputCell,
                            Collections.<Map<String, Object>>emptyList())) {
                        String guardSite = first(
                                text(guard.get("guardSiteId")),
                                text(guard.get("siteId")));
                        if (!"GUARD".equals(text(guard.get("transferKind")))
                                || !semanticSites.contains(guardSite)) {
                            continue;
                        }
                        markPrimitiveAccessorFrontiers(
                                text(guard.get("fromCell")), incoming,
                                inputBoundaries, outputCell, outputPort,
                                guardSite);
                    }
                }
            }
        }
    }

    private static void markPrimitiveAccessorFrontiers(
            String start,
            Map<String, List<Map<String, Object>>> incoming,
            Map<String, List<Map<String, Object>>> inputBoundaries,
            String outputCell, String outputPort, String guardSite) {
        Set<String> visited = new LinkedHashSet<>();
        Deque<String> work = new ArrayDeque<>();
        if (!start.isEmpty()) work.add(start);
        while (!work.isEmpty()) {
            String cell = work.removeFirst();
            if (!visited.add(cell)) continue;
            boolean foundAccessor = false;
            for (Map<String, Object> input : inputBoundaries.getOrDefault(
                    cell, Collections.<Map<String, Object>>emptyList())) {
                if (!"ACCESSOR_RETURN".equals(text(input.get("sourceKind")))
                        || !primitiveLeaf(input)) {
                    continue;
                }
                foundAccessor = true;
                if (text(input.get("symbolicDemand")).startsWith(
                        "CONCRETE_")
                        || !text(input.get(
                        "rpcConcreteRootAuthority")).isEmpty()) {
                    continue;
                }
                input.put("symbolicDemand", "BOUNDED_STATE_FRONTIER");
                input.put("boundedStateFrontierAuthority",
                        "STATIC_ACCESSOR_SEMANTIC_MUTATION_GUARD_V1");
                addUniqueValue(input, "boundedMutationOutputCells",
                        outputCell);
                addUniqueValue(input, "boundedMutationOutputPorts",
                        outputPort);
                addUniqueValue(input, "boundedMutationGuardSites",
                        guardSite);
            }
            if (foundAccessor) continue;
            for (Map<String, Object> edge : incoming.getOrDefault(cell,
                    Collections.<Map<String, Object>>emptyList())) {
                // Loop/path guards are control context, not value sources for
                // the semantic mutation predicate.
                if ("GUARD".equals(text(edge.get("transferKind")))) {
                    continue;
                }
                String from = text(edge.get("fromCell"));
                if (!from.isEmpty()) work.addLast(from);
            }
        }
    }

    private static void addUniqueValue(Map<String, Object> row, String key,
                                       String value) {
        if (value.isEmpty()) return;
        List<String> values = strings(row.get(key));
        if (!values.contains(value)) values.add(value);
        row.put(key, values);
    }

    private static List<String> mutationOutputCells(
            Map<String, Object> output) {
        Set<String> result = new LinkedHashSet<>();
        String cell = text(output.get("cell"));
        if (!cell.isEmpty()) result.add(cell);
        List<String> declarations = strings(
                output.get("fieldPathDeclarations"));
        if (!declarations.isEmpty()) {
            result.add(declarations.get(declarations.size() - 1));
        }
        result.addAll(RegionDemandIndex.boundaryCells(output));
        return new ArrayList<>(result);
    }

    /**
     * Prevents a primitive reached through a transferred reference from
     * silently becoming a new, unrelated symbolic variable.
     *
     * <p>The runtime object id is used only inside this trace to prove that a
     * primitive receiver descends from the exact reference delivered to this
     * activation.  If an exact region edge already writes that primitive
     * input, the normal symbolic relation is retained.  Otherwise replaying
     * the observed primitive is a deliberate under-approximation: it is more
     * precise than inventing a fresh solver leaf with no producer.</p>
     *
     * <p>Two shapes are exempt, and both for the same reason: the rule rests
     * on "state reached through a transferred reference has a writer this
     * model does not hold", and for these two that premise is false.</p>
     *
     * <p>The leaf of a JDK boxing wrapper has no writer because it
     * <em>cannot</em> have one - {@code Boolean.FALSE.value} is fixed at class
     * initialization and immutable afterwards.  For such a leaf the producer
     * of the value is the producer of the reference, so the carrier's own edge
     * is projected onto the leaf instead of the leaf being demoted.</p>
     *
     * <p>A leaf this very occurrence writes has a writer the model holds: its
     * own.  The reference was transferred, but the state behind it was
     * installed here, and the read is a live-in only because the accessor that
     * performs it lies outside the relation's method scope.  Demoting it
     * publishes a relation whose output is constant on every path - which is
     * exactly what makes a declared cut argument export a concrete value and
     * answer {@code RPC_HANDOFF_NOT_SYMBOLIC}.  Everything else keeps the
     * demotion, and keeps it named.</p>
     */
    static void markUnclosedReferenceLeavesConcrete(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> regionEdges,
            List<Map<String, Object>> refinedGraph,
            Map<String, String> occurrenceByRecordedRootCall) {
        Map<String, Set<Integer>> boundaryObjects = new LinkedHashMap<>();
        // The same deliveries, kept unexpanded and with the edge that made
        // them.  A boxed leaf may only be projected onto the edge that
        // delivered its own receiver, never onto one that delivered an object
        // its receiver was later reached from: the immutability argument is
        // about this wrapper object, and one hop further it is not available.
        Map<String, Map<Integer, List<Map<String, Object>>>> carriers =
                new LinkedHashMap<>();
        Set<String> closedInputs = new LinkedHashSet<>();
        for (Map<String, Object> edge : regionEdges) {
            String toOccurrence = text(edge.get("toOccurrenceId"));
            String toPort = text(edge.get("toPort"));
            if (!toOccurrence.isEmpty() && !toPort.isEmpty()) {
                closedInputs.add(portDemandKey(toOccurrence, toPort));
            }
            // A heap flow delivers an object this trace can name.  A protocol
            // delivery does not: the receiver deserializes its own object, and
            // the reconstructed caller-result identity that used to stand in
            // for it was a value guess about a boundary the trace only ever
            // correlated by exchange.
            int deliveredObject = "RUNTIME_FIELD_FLOW".equals(
                    text(edge.get("kind")))
                    ? number(edge.get("valueObjectId"), 0) : 0;
            if (deliveredObject > 0 && !toOccurrence.isEmpty()) {
                boundaryObjects.computeIfAbsent(toOccurrence,
                        ignored -> new LinkedHashSet<>())
                        .add(deliveredObject);
                if (!toPort.isEmpty()) {
                    carriers.computeIfAbsent(toOccurrence,
                            ignored -> new LinkedHashMap<>())
                            .computeIfAbsent(deliveredObject,
                                    ignored -> new ArrayList<>()).add(edge);
                }
            }
        }
        if (boundaryObjects.isEmpty()) return;

        Map<String, Map<Integer, Set<Integer>>> objectLinks =
                referenceObjectLinks(refinedGraph,
                        occurrenceByRecordedRootCall);
        for (Map.Entry<String, Set<Integer>> entry
                : boundaryObjects.entrySet()) {
            Set<Integer> reachable = entry.getValue();
            Deque<Integer> work = new ArrayDeque<>(reachable);
            Map<Integer, Set<Integer>> links = objectLinks.getOrDefault(
                    entry.getKey(), Collections.<Integer, Set<Integer>>emptyMap());
            while (!work.isEmpty()) {
                for (Integer child : links.getOrDefault(work.removeFirst(),
                        Collections.<Integer>emptySet())) {
                    if (child != null && child > 0
                            && reachable.add(child)) {
                        work.addLast(child);
                    }
                }
            }
        }

        Map<String, Set<String>> writtenLeaves = occurrenceWrittenLeaves(
                refinedGraph, occurrenceByRecordedRootCall);
        List<Map<String, Object>> projections = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            for (Map<String, Object> port
                    : rows(region.get("symbolicInputs"))) {
                String occurrenceId = portOccurrenceId(port, false);
                String demand = portDemandKey(occurrenceId,
                        text(port.get("portId")));
                if (closedInputs.contains(demand)
                        || "BOUNDED_STATE_FRONTIER".equals(
                        text(port.get("symbolicDemand")))
                        || !primitiveLeaf(port)) {
                    continue;
                }
                Set<Integer> receivers = receiverObjects(port);
                Set<Integer> reachable = boundaryObjects.get(occurrenceId);
                if (reachable == null || reachable.isEmpty()
                        || Collections.disjoint(reachable, receivers)
                        || writesLeafItself(writtenLeaves.get(occurrenceId),
                        leafDeclaration(port), receivers)) {
                    continue;
                }
                List<Map<String, Object>> projected = boxedLeafProjections(
                        carriers.getOrDefault(occurrenceId,
                                Collections.<Integer,
                                        List<Map<String, Object>>>emptyMap()),
                        port, receivers);
                if (projected != null) {
                    // The producer of the reference is the producer of the
                    // value, so the leaf is closed rather than replayed.  Every
                    // carrier that delivered this wrapper is projected, because
                    // each is its own undecided candidate writer and choosing
                    // between them here would be the value guess the read-from
                    // model exists to defer.
                    projections.addAll(projected);
                    continue;
                }
                port.put("symbolicDemand",
                        "CONCRETE_REFERENCE_BOUNDARY_REPLAY");
                port.put("replayAuthority",
                        "EXACT_TRACE_REFERENCE_LEAF_UNDER_APPROX_V1");
            }
        }
        regionEdges.addAll(projections);
    }

    /**
     * The exact leaves each occurrence installs itself, as
     * {@code receiverObjectId + declaration}.
     *
     * <p>Recorded writes only: a static write site says which field some frame
     * may install, while the demotion above is about one runtime object of one
     * occurrence, so nothing but the recorded binding answers it.</p>
     */
    private static Map<String, Set<String>> occurrenceWrittenLeaves(
            List<Map<String, Object>> graph,
            Map<String, String> occurrenceByRecordedRootCall) {
        Map<String, Set<String>> result = new LinkedHashMap<>();
        for (Map<String, Object> edge : graph) {
            if (!"HEAP_WRITE".equals(text(edge.get("transferKind")))) {
                continue;
            }
            for (Map<String, Object> binding
                    : rows(edge.get("runtimeFieldBindings"))) {
                String occurrenceId = occurrenceByRecordedRootCall.get(
                        recordedRootCallKey(text(binding.get("regionId")),
                                longNumber(binding.get("rootCallId"), -1L)));
                int receiver = number(
                        binding.get("fieldReceiverObjectId"), 0);
                String declaration = leafDeclaration(binding);
                if (occurrenceId == null || receiver <= 0
                        || declaration.isEmpty()) {
                    continue;
                }
                result.computeIfAbsent(occurrenceId,
                        ignored -> new LinkedHashSet<>())
                        .add(receiver + "\n" + declaration);
            }
        }
        return result;
    }

    /** Whether one of {@code receivers} holds a leaf this occurrence wrote. */
    private static boolean writesLeafItself(Set<String> written,
                                            String declaration,
                                            Set<Integer> receivers) {
        if (written == null || declaration.isEmpty()) return false;
        for (Integer receiver : receivers) {
            if (written.contains(receiver + "\n" + declaration)) return true;
        }
        return false;
    }

    /**
     * The carrier edges of one immutable boxed leaf, or {@code null} when this
     * leaf is not that shape.
     *
     * <p>{@code null} rather than an empty list, deliberately: "not a wrapper
     * leaf" and "a wrapper leaf whose carrier nothing closed" are two
     * different findings, and only the first may fall through to the
     * demotion by default.  A wrapper leaf whose receiver was not itself
     * delivered by a closed edge is also demoted - the exemption rests on the
     * reference having a named producer, and without one it has none.</p>
     */
    private static List<Map<String, Object>> boxedLeafProjections(
            Map<Integer, List<Map<String, Object>>> carriers,
            Map<String, Object> leaf, Set<Integer> receivers) {
        String declaration = leafDeclaration(leaf);
        DeclaredFieldCell field = DeclaredFieldCell.parse(declaration);
        if (field == null
                || !JavaPrimitiveBoxing.wrapperType(field.owner())) {
            return null;
        }
        List<Map<String, Object>> projected = new ArrayList<>();
        for (Integer receiver : receivers) {
            for (Map<String, Object> carrier : carriers.getOrDefault(receiver,
                    Collections.<Map<String, Object>>emptyList())) {
                projected.add(boxedLeafProjection(carrier, leaf,
                        field.owner(), declaration));
            }
        }
        return projected.isEmpty() ? null : projected;
    }

    /**
     * One carrier edge restated as the producer of the boxed value it carried.
     *
     * <p>Everything the carrier proves is kept verbatim - the writer, the two
     * event ordinals, the object identities, the field its read-from is still
     * undecided over, and the candidate provenance that says so.  Only the
     * consuming endpoint moves, from the port that read the reference to the
     * port that reads the value inside it, and the row says which edge it was
     * projected from and under which rule.  Deciding the carrier's writer
     * therefore decides this leaf, which is the whole content of the
     * claim.</p>
     */
    private static Map<String, Object> boxedLeafProjection(
            Map<String, Object> carrier, Map<String, Object> leaf,
            String wrapper, String declaration) {
        String leafPort = text(leaf.get("portId"));
        String identity = text(carrier.get("edgeId")) + "\n" + leafPort;
        Map<String, Object> edge = new LinkedHashMap<>(carrier);
        edge.put("edgeId", "BX." + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8)));
        edge.put("toPort", leafPort);
        String role = text(leaf.get("dependencyRole"));
        if (!role.isEmpty()) {
            edge.put("dependencyRole", role);
        }
        edge.put(EDGE_BOXED_LEAF_AUTHORITY, BOXED_LEAF_PROJECTION_AUTHORITY);
        edge.put("boxedCarrierEdgeId", carrier.get("edgeId"));
        edge.put("boxedCarrierPort", carrier.get("toPort"));
        edge.put("boxedWrapperType", wrapper);
        edge.put("boxedLeafDeclaration", declaration);
        return edge;
    }

    /** The declared field a port's leaf reads, by its own path or its cell. */
    private static String leafDeclaration(Map<String, Object> port) {
        List<String> declarations = strings(
                port.get("fieldPathDeclarations"));
        return declarations.isEmpty() ? text(port.get("cell"))
                : declarations.get(declarations.size() - 1);
    }

    private static Map<String, Map<Integer, Set<Integer>>>
            referenceObjectLinks(List<Map<String, Object>> graph,
            Map<String, String> occurrenceByRecordedRootCall) {
        Map<String, Map<Integer, Set<Integer>>> result =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : graph) {
            List<Map<String, Object>> bindings = new ArrayList<>();
            bindings.addAll(rows(edge.get("runtimeAccessorBindings")));
            if ("HEAP_READ".equals(text(edge.get("transferKind")))) {
                bindings.addAll(rows(edge.get("runtimeFieldBindings")));
            }
            for (Map<String, Object> binding : bindings) {
                int receiver = number(binding.containsKey("receiverObjectId")
                        ? binding.get("receiverObjectId")
                        : binding.get("fieldReceiverObjectId"), 0);
                int value = number(binding.get("valueObjectId"), 0);
                String occurrenceId = occurrenceByRecordedRootCall.getOrDefault(
                        recordedRootCallKey(text(binding.get("regionId")),
                                longNumber(binding.get("rootCallId"), -1L)),
                        "");
                if (receiver <= 0 || value <= 0 || occurrenceId.isEmpty()) {
                    continue;
                }
                result.computeIfAbsent(occurrenceId,
                        ignored -> new LinkedHashMap<>())
                        .computeIfAbsent(receiver,
                                ignored -> new LinkedHashSet<>()).add(value);
            }
        }
        return result;
    }

    private static boolean primitiveLeaf(Map<String, Object> port) {
        DeclaredFieldCell field = DeclaredFieldCell.parse(
                leafDeclaration(port));
        return field != null && field.primitive();
    }

    private static Set<Integer> receiverObjects(Map<String, Object> port) {
        Set<Integer> result = new LinkedHashSet<>();
        int receiver = number(port.get("fieldReceiverObjectId"), 0);
        if (receiver > 0) result.add(receiver);
        receiver = number(port.get("rootObjectId"), 0);
        if (receiver > 0 && "OBSERVED_FIELD_RECEIVER".equals(
                text(port.get("rootKind")))) {
            result.add(receiver);
        }
        for (Map<String, Object> access
                : rows(port.get("runtimeAccesses"))) {
            receiver = number(access.get("fieldReceiverObjectId"), 0);
            if (receiver > 0) result.add(receiver);
        }
        return result;
    }

    private static void copyContext(Map<String, Object> edge, String prefix,
                                    Map<String, Object> instance) {
        if (instance == null) return;
        putIfMissing(edge, prefix + "LaneId", instance.get("laneId"));
        putIfMissing(edge, prefix + "SpanId", instance.get("spanId"));
    }

    private static void putIfMissing(Map<String, Object> target, String key,
                                     Object value) {
        if (!target.containsKey(key) && value != null
                && !text(value).isEmpty()) {
            target.put(key, value);
        }
    }

    private static void copyIfPresent(Map<String, Object> target,
                                      Map<String, Object> source,
                                      String key) {
        if (source.containsKey(key) && source.get(key) != null) {
            target.put(key, source.get(key));
        }
    }

    /** Republishes one recorded access as the port's own replay address. */
    private static void copyRuntimeOccurrence(
            Map<String, Object> access, Map<String, Object> port) {
        for (String key : new String[]{"eventSeq", "staticAccessSiteId",
                "activationLocalStaticSiteOccurrence",
                "accessorOccurrence", "helperActivationBoundedOccurrence",
                "fieldReceiverObjectId", "rootCallId", "callId"}) {
            copyIfPresent(port, access, key);
        }
        int occurrence = number(access.get(
                "activationLocalStaticSiteOccurrence"),
                number(access.get("accessorOccurrence"), -1));
        if (occurrence > 0) {
            port.put("replayOccurrence", occurrence);
            port.put("activationLocalStaticSiteOccurrence", occurrence);
        }
    }

    private static List<Map<String, Object>> statePorts(
            String regionId, List<Map<String, Object>> edges,
            String transfer, String prefix,
            Map<String, String> occurrenceByRecordedRootCall) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        Map<String, Set<String>> seenAccesses = new LinkedHashMap<>();
        DependencyRoleClassifier roles = new DependencyRoleClassifier(edges);
        for (Map<String, Object> edge : edges) {
            if (!transfer.equals(text(edge.get("transferKind")))) {
                continue;
            }
            String dependencyRole = "HEAP_READ".equals(transfer)
                    ? roles.heapReadRole(edge)
                    : DependencyRole.VALUE_FRONTIER;
            for (Map<String, Object> binding
                    : rows(edge.get("runtimeFieldBindings"))) {
                if (!regionId.equals(text(binding.get("regionId")))) {
                    continue;
                }
                String occurrenceId = occurrenceByRecordedRootCall.get(
                        recordedRootCallKey(regionId, longNumber(
                                binding.get("rootCallId"), -1L)));
                if (occurrenceId == null) continue;
                String key = occurrenceId + "\n"
                        + text(binding.get("rootCell")) + "\n"
                        + strings(binding.get("fieldPath"));
                Map<String, Object> port = unique.get(key);
                if (port == null) {
                    port = new LinkedHashMap<>(binding);
                    String direction = "IN".equals(prefix)
                            ? ".in." : ".out.";
                    port.put("portId", regionId + direction
                            + UUID.nameUUIDFromBytes(
                            (regionId + "\n" + key).getBytes(
                                    StandardCharsets.UTF_8)));
                    port.put("occurrenceId", occurrenceId);
                    port.put("cell", binding.get("rootCell"));
                    port.put("transportKind", "HEAP");
                    String rootKind = text(binding.get("rootKind"));
                    port.put("sourceKind", "PARAMETER".equals(rootKind)
                            ? "ROOT_ARGUMENT"
                            : "OBSERVED_FIELD_RECEIVER".equals(rootKind)
                            ? "ACTIVATION_FIELD_RECEIVER"
                            : "RECEIVER_FIELD");
                    port.put("runtimeAccesses", new ArrayList<>());
                    port.put("dependencyCells", new ArrayList<String>());
                    unique.put(key, port);
                }
                if (!port.containsKey("dependencyRole")) {
                    port.put("dependencyRole", dependencyRole);
                } else {
                    port.put("dependencyRole", DependencyRole.merge(
                            port.get("dependencyRole"), dependencyRole));
                }
                addRuntimeAccess(port, binding, edge, occurrenceId,
                        seenAccesses.computeIfAbsent(key,
                                ignored -> new LinkedHashSet<>()));
                addUniqueString(port, "dependencyCells",
                        text(edge.get("fromCell")));
            }
        }
        return new ArrayList<>(unique.values());
    }

    @SuppressWarnings("unchecked")
    private static void addRuntimeAccess(Map<String, Object> port,
                                         Map<String, Object> binding,
                                         Map<String, Object> edge,
                                         String occurrenceId,
                                         Set<String> seen) {
        // statePorts installs the list, so the cast is exact; the seen set
        // replaces a quadratic rescan with the same (eventSeq, receiver)
        // dedup identity and the same append order.
        List<Map<String, Object>> accesses = (List<Map<String, Object>>)
                port.get("runtimeAccesses");
        long seq = longNumber(binding.get("eventSeq"), 0L);
        int receiver = number(binding.get("fieldReceiverObjectId"), 0);
        if (!seen.add(seq + "\n" + receiver)) {
            return;
        }
        Map<String, Object> access = new LinkedHashMap<>();
        access.put("eventSeq", binding.get("eventSeq"));
        access.put("callId", binding.get("callId"));
        access.put("sourceKey", binding.get("sourceKey"));
        access.put("occurrenceId", occurrenceId);
        // Recorded trace evidence for the observed access.
        access.put("rootCallId", binding.get("rootCallId"));
        access.put("fieldReceiverObjectId",
                binding.get("fieldReceiverObjectId"));
        access.put("valueObjectId", binding.get("valueObjectId"));
        access.put("primitiveValue", binding.get("primitiveValue"));
        access.put("fieldPathDeclarations",
                binding.get("fieldPathDeclarations"));
        access.put("bindingKind", binding.get("bindingKind"));
        access.put("writerFieldReadSeq", binding.get("writerFieldReadSeq"));
        access.put("mutatorEnterSeq", binding.get("mutatorEnterSeq"));
        access.put("mutationCompletionSeq",
                binding.get("mutationCompletionSeq"));
        access.put("mutationInvocationId",
                binding.get("mutationInvocationId"));
        access.put("mutatorDeclaredCallee",
                binding.get("mutatorDeclaredCallee"));
        access.put("containerMemberToken",
                binding.get("containerMemberToken"));
        access.put("containerMemberIdentityAuthority",
                binding.get("containerMemberIdentityAuthority"));
        access.put("containerObjectId", binding.get("containerObjectId"));
        access.put("containerKeyObjectId",
                binding.get("containerKeyObjectId"));
        access.put("containerValueObjectId",
                binding.get("containerValueObjectId"));
        access.put("containerMemberFieldBindings",
                binding.get("containerMemberFieldBindings"));
        access.put("staticAccessSiteId", first(
                text(binding.get("siteId")), staticAccessSiteId(edge)));
        accesses.add(access);
    }

    private static String staticAccessSiteId(Map<String, Object> edge) {
        String site = text(edge.get("siteId"));
        if (!site.isEmpty()) return site;
        String method = text(edge.get("method"));
        int unit = number(edge.get("unitIndex"), -1);
        if (!method.isEmpty() && unit >= 0) return method + "#u" + unit;
        return text(edge.get("id"));
    }

    private static List<Map<String, Object>> accessorPorts(
            String regionId, List<Map<String, Object>> edges,
            List<Map<String, Object>> branchPolicies,
            Map<String, String> occurrenceByRecordedRootCall) {
        Set<String> demandedEdges = semanticAccessorEdges(edges,
                branchPolicies);
        if (demandedEdges.isEmpty()) return Collections.emptyList();
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        Map<String, Integer> retainedByActivationStream =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!demandedEdges.contains(text(edge.get("id")))) continue;
            String field = first(text(edge.get("declaredFieldSignature")),
                    text(edge.get("fromCell")));
            DeclaredFieldCell declaration = DeclaredFieldCell.parse(field);
            if (declaration == null || !declaration.primitive()) continue;
            String caller = text(edge.get("method"));
            int unitIndex = number(edge.get("unitIndex"), -1);
            String declaredCallee = text(edge.get("invoke"));
            String implementation = text(
                    edge.get("accessorImplementationMethod"));
            if (caller.isEmpty() || unitIndex < 0
                    || declaredCallee.isEmpty() || implementation.isEmpty()) {
                continue;
            }
            List<Map<String, Object>> bindings = new ArrayList<>(
                    rows(edge.get("runtimeAccessorBindings")));
            bindings.sort(Comparator
                    .comparingLong((Map<String, Object> binding) ->
                            longNumber(binding.get("rootCallId"),
                                    Long.MAX_VALUE))
                    .thenComparingLong(binding -> longNumber(
                            binding.get("eventSeq"), Long.MAX_VALUE)));
            for (Map<String, Object> binding : bindings) {
                if (!regionId.equals(text(binding.get("regionId")))) continue;
                int occurrence = number(binding.get("accessorOccurrence"), -1);
                long callId = longNumber(binding.get("callId"), -1L);
                String occurrenceId = occurrenceByRecordedRootCall.get(
                        recordedRootCallKey(regionId, longNumber(
                                binding.get("rootCallId"), -1L)));
                if (occurrence < 1 || occurrenceId == null || callId < 0L) {
                    continue;
                }
                String key = occurrenceId + "\n" + text(edge.get("id"))
                        + "\n" + callId + "\n" + occurrence;
                if (unique.containsKey(key)) continue;
                // The root can be a long-lived service loop.  Capacity is a
                // bound on one concrete helper activation, not on every use
                // of this accessor during the lifetime of the root thread.
                // Keep the trace call id only as discovery evidence; runtime
                // planning later selects the exact output-invocation corridor
                // and emits the replay-stable accessor occurrence.
                String stream = occurrenceId + "\n" + callId
                        + "\nACCESSOR_RETURN\n"
                        + caller + "#u" + unitIndex + "\n" + field + "\n"
                        + declaredCallee + "\n" + implementation;
                int retained = retainedByActivationStream.getOrDefault(
                        stream, 0);
                if (retained >= LoopBoundPolicy
                        .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY) {
                    continue;
                }
                retainedByActivationStream.put(stream, retained + 1);
                Map<String, Object> port = new LinkedHashMap<>(binding);
                port.put("occurrenceId", occurrenceId);
                port.put("portId", regionId + ".in."
                        + UUID.nameUUIDFromBytes((regionId + "\n" + key)
                        .getBytes(StandardCharsets.UTF_8)));
                port.put("cell", field);
                port.put("sourceKind", "ACCESSOR_RETURN");
                // An accessor port is emitted only after the exact primitive
                // field return reaches a semantic branch operand.  Declare
                // that leaf explicitly; DependencyRole intentionally rejects
                // missing roles instead of turning owners into symbolic data.
                port.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
                port.put("transportKind", "ACTIVATION_LOCAL");
                port.put("rootKind", "OBSERVED_FIELD_RECEIVER");
                port.put("rootObjectId", binding.get("receiverObjectId"));
                port.put("fieldReceiverObjectId",
                        binding.get("receiverObjectId"));
                port.put("fieldPath",
                        Collections.singletonList(declaration.name));
                port.put("fieldPathDeclarations",
                        Collections.singletonList(field));
                port.put("javaType", declaration.type);
                port.put("callerMethod", caller);
                port.put("unitIndex", unitIndex);
                port.put("declaredCallee", declaredCallee);
                port.put("declaredFieldSignature", field);
                port.put("accessorImplementationMethod", implementation);
                port.put("dependencyCells",
                        Collections.singletonList(text(edge.get("fromCell"))));
                port.put("replayOccurrence", occurrence);
                port.put("helperActivationBoundedOccurrence", retained + 1);
                unique.put(key, port);
            }
        }
        return new ArrayList<>(unique.values());
    }

    private static List<Map<String, Object>> explicitFaultPorts(
            String regionId, List<Map<String, Object>> edges,
            Map<String, String> occurrenceByRecordedRootCall) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!Boolean.TRUE.equals(booleanValue(
                    edge.get("explicitSymbolicFault")))) {
                continue;
            }
            String returnCell = text(edge.get("fromCell"));
            String caller = text(edge.get("method"));
            int unitIndex = number(edge.get("unitIndex"), -1);
            if (returnCell.isEmpty() || caller.isEmpty() || unitIndex < 0) {
                continue;
            }
            for (Map<String, Object> binding
                    : rows(edge.get("runtimeExplicitFaultBindings"))) {
                if (!regionId.equals(text(binding.get("regionId")))
                        || !"EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1".equals(
                        text(binding.get("authority")))) {
                    continue;
                }
                long eventSeq = longNumber(binding.get("eventSeq"), -1L);
                int occurrence = number(binding.get("accessorOccurrence"), -1);
                String occurrenceId = occurrenceByRecordedRootCall.get(
                        recordedRootCallKey(regionId, longNumber(
                                binding.get("rootCallId"), -1L)));
                if (occurrenceId == null || eventSeq < 0L || occurrence < 1) {
                    continue;
                }
                String key = occurrenceId + "\n" + caller + "#u"
                        + unitIndex + "\n" + occurrence;
                Map<String, Object> port = new LinkedHashMap<>(binding);
                port.put("occurrenceId", occurrenceId);
                port.put("portId", regionId + ".in."
                        + UUID.nameUUIDFromBytes((regionId + "\n" + key)
                        .getBytes(StandardCharsets.UTF_8)));
                port.put("cell", returnCell);
                port.put("sourceKind", EXPLICIT_SYMBOLIC_FAULT);
                port.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
                port.put("transportKind", "ACTIVATION_LOCAL");
                port.put("rootKind", "ACTIVATION_LOCAL");
                port.put("javaType", "boolean");
                port.put("callerMethod", caller);
                port.put("unitIndex", unitIndex);
                port.put("siteId", caller + "#u" + unitIndex);
                port.put("declaredCallee", edge.get("invoke"));
                port.put("symbolicName", edge.get("symbolicName"));
                port.put("dependencyCells",
                        Collections.singletonList(returnCell));
                port.put("replayOccurrence", occurrence);
                unique.put(key, port);
            }
        }
        return new ArrayList<>(unique.values());
    }

    private static Set<String> semanticAccessorEdges(
            List<Map<String, Object>> edges,
            List<Map<String, Object>> branchPolicies) {
        Map<String, List<Map<String, Object>>> incoming = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            String to = text(edge.get("toCell"));
            if (!to.isEmpty()) {
                incoming.computeIfAbsent(to,
                        ignored -> new ArrayList<>()).add(edge);
            }
        }
        Deque<String> work = new ArrayDeque<>();
        for (Map<String, Object> branch : branchPolicies) {
            if ("EXPLORE".equals(text(branch.get("policy")))) {
                work.addAll(strings(branch.get("operandCells")));
            }
        }
        Set<String> visited = new LinkedHashSet<>();
        Set<String> selected = new LinkedHashSet<>();
        while (!work.isEmpty()) {
            String cell = work.removeFirst();
            if (!visited.add(cell)) continue;
            List<Map<String, Object>> predecessors = incoming.getOrDefault(
                    cell, Collections.emptyList());
            boolean accessorLeaf = false;
            for (Map<String, Object> edge : predecessors) {
                if (!"accessor_field_return".equals(text(edge.get("kind")))
                        || !Boolean.TRUE.equals(booleanValue(
                        edge.get("runtimeObserved")))) {
                    continue;
                }
                String id = text(edge.get("id"));
                if (!id.isEmpty()) selected.add(id);
                accessorLeaf = true;
            }
            // An observed structural getter is the exact symbolic boundary.
            // Following its receiver/container history would pull unrelated
            // writers and Map keys into the symbolic input set.
            if (accessorLeaf) continue;
            for (Map<String, Object> edge : predecessors) {
                if ("GUARD".equals(text(edge.get("transferKind")))) continue;
                String from = text(edge.get("fromCell"));
                if (!from.isEmpty()) work.addLast(from);
            }
        }
        return selected;
    }

    /**
     * A live-in used only to replay a bounded loop's continuation decision is
     * retained in the task, but must not become a symbolic search dimension.
     * Any flow to a non-loop branch wins and keeps the value symbolic.
     */
    private static void markLoopControlOnlyInputs(
            List<Map<String, Object>> inputs,
            List<Map<String, Object>> edges,
            List<Map<String, Object>> branchPolicies) {
        Set<String> loopOperands = new LinkedHashSet<>();
        Set<String> semanticOperands = new LinkedHashSet<>();
        for (Map<String, Object> branch : branchPolicies) {
            Set<String> target = Boolean.TRUE.equals(booleanValue(
                    branch.get("loopControlGuard")))
                    ? loopOperands : semanticOperands;
            target.addAll(strings(branch.get("operandCells")));
        }
        if (loopOperands.isEmpty()) return;

        Map<String, List<String>> outgoing = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if ("GUARD".equals(text(edge.get("transferKind")))) continue;
            String from = text(edge.get("fromCell"));
            String to = text(edge.get("toCell"));
            if (!from.isEmpty() && !to.isEmpty()) {
                outgoing.computeIfAbsent(from,
                        ignored -> new ArrayList<>()).add(to);
            }
        }
        for (Map<String, Object> input : inputs) {
            Set<String> starts = new LinkedHashSet<>(
                    strings(input.get("dependencyCells")));
            String cell = text(input.get("cell"));
            if (!cell.isEmpty()) starts.add(cell);
            if (reachesAny(starts, loopOperands, outgoing)
                    && !reachesAny(starts, semanticOperands, outgoing)) {
                input.put("loopControlOnly", true);
                input.put("symbolicDemand", "CONCRETE_LOOP_CONTROL");
            }
        }
    }

    private static boolean reachesAny(
            Collection<String> starts, Set<String> targets,
            Map<String, List<String>> outgoing) {
        if (targets.isEmpty()) return false;
        Set<String> visited = new LinkedHashSet<>();
        Deque<String> work = new ArrayDeque<>(starts);
        while (!work.isEmpty()) {
            String cell = work.removeFirst();
            if (!visited.add(cell)) continue;
            if (targets.contains(cell)) return true;
            work.addAll(outgoing.getOrDefault(cell,
                    Collections.<String>emptyList()));
        }
        return false;
    }

    private static void addUniqueString(Map<String, Object> row,
                                        String field, String value) {
        if (value.isEmpty()) return;
        List<String> values = strings(row.get(field));
        if (!values.contains(value)) values.add(value);
        row.put(field, values);
    }

    /**
     * The methods whose guards decide the region's demanded behaviour: what the
     * admitting anchors reach, widened by the methods that define this
     * region's own outputs.  A region can carry more than one demand, and a
     * guard inside an output definition is about how that output comes about
     * whichever anchor admitted the region.  An unknown scope stays unknown.
     */
    private static Set<String> demandScope(
            Map<String, Object> skeleton,
            List<Map<String, Object>> outputs) {
        Set<String> result = new LinkedHashSet<>(
                strings(skeleton.get(DEMAND_SCOPE)));
        if (result.isEmpty()) {
            return result;
        }
        for (Map<String, Object> output : outputs) {
            String site = text(output.get("siteId"));
            int marker = site.indexOf('#');
            if (marker > 0) {
                result.add(site.substring(0, marker));
            }
            String owner = text(output.get("rootMethod"));
            if (!owner.isEmpty()) {
                result.add(owner);
            }
        }
        return result;
    }

    /**
     * Builds the region's branch policies.  {@code demandScope} names the
     * methods reached from the anchors that admitted the region; a guard
     * outside it decides something the execution context does for its own
     * reasons, not how this region's outputs come about, so it is replayed as
     * observed instead of explored.  An empty scope decides nothing and leaves
     * every guard explorable, and a guard that dominates the failure target is
     * never demoted -- that one is the goal.
     */
    private static List<Map<String, Object>> branches(
            List<Map<String, Object>> edges, Set<String> demandScope) {
        Map<String, List<Map<String, Object>>> bySite =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"GUARD".equals(text(edge.get("transferKind")))) {
                continue;
            }
            String site = first(text(edge.get("guardSiteId")),
                    text(edge.get("siteId")));
            if (!site.isEmpty()) {
                bySite.computeIfAbsent(site,
                        ignored -> new ArrayList<>()).add(edge);
            }
        }

        BranchPolicyClassifier classifier =
                new BranchPolicyClassifier(edges);
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map.Entry<String, List<Map<String, Object>>> entry
                : bySite.entrySet()) {
            String site = entry.getKey();
            List<Map<String, Object>> guards = entry.getValue();
            Map<String, Object> representative = guards.get(0);
            Map<String, Object> branch = new LinkedHashMap<>();
            branch.put("siteId", site);
            branch.put("method", representative.get("method"));
            branch.put("unitIndex", number(
                    representative.get("unitIndex"), -1));
            List<Map<String, Object>> failureGuards = new ArrayList<>();
            for (Map<String, Object> guard : guards) {
                if ("exception_guard".equals(text(guard.get("kind")))
                        || text(guard.get("toCell")).contains(
                        "#exception:")) {
                    failureGuards.add(guard);
                }
            }
            Collection<Map<String, Object>> decisiveGuards =
                    failureGuards.isEmpty() ? guards : failureGuards;
            branch.put("failureTarget", !failureGuards.isEmpty());
            // Which throw this guard controls, not merely that it controls
            // one.  A source-level `if (p && q) throw` lowers to two
            // conditional sites and both carry an exception guard into the
            // same throw: they are the conjuncts of one target predicate, not
            // two targets.  Naming the guarded throw is what lets a later
            // stage tell those apart; without it the only available test is
            // counting sites, and counting reads every short-circuit target
            // as an ambiguity it has no way to resolve.
            List<String> guardedTargets = new ArrayList<>();
            for (Map<String, Object> guard : failureGuards) {
                String cell = text(guard.get("toCell"));
                if (!cell.isEmpty() && !guardedTargets.contains(cell)) {
                    guardedTargets.add(cell);
                }
            }
            if (!guardedTargets.isEmpty()) {
                branch.put(FAILURE_TARGET_CELLS, guardedTargets);
            }
            branch.put("operandCells", operandCells(decisiveGuards));
            Boolean required = consistentRequiredOutcome(decisiveGuards);
            branch.put("requiredOutcome", required);
            branch.put("guardedSiteOutcomes", guardedSiteOutcomes(guards));

            boolean conflicting = required == null
                    && hasConflictingRequiredOutcomes(decisiveGuards);
            boolean cfgLoopControl = classifier.cfgLoopControlGuard(guards);
            boolean loopStructure = cfgLoopControl
                    || classifier.structuralLoopGuard(site, guards);
            boolean carrierStructure = classifier.structureCarrierGuard(
                    guards);
            boolean outsideDemand = !demandScope.isEmpty()
                    && failureGuards.isEmpty()
                    && !demandScope.contains(text(
                    representative.get("method")));
            branch.put("loopControlGuard", loopStructure);
            branch.put("policy", conflicting || loopStructure
                    || carrierStructure || outsideDemand
                    ? "PATH_ASSUMPTION" : "EXPLORE");
            branch.put("policyReason", conflicting
                    ? "CONFLICTING_REQUIRED_OUTCOMES"
                    : loopStructure ? "BOUND_LOOP_CONTROL_GUARD"
                    : carrierStructure ? "STRUCTURE_CARRIER_GUARD"
                    : outsideDemand ? "OUTSIDE_DEMANDED_SCOPE"
                    : "FAILURE_DIRECTED_SEMANTIC_GUARD");
            result.add(branch);
        }
        return result;
    }

    private static List<String> operandCells(
            Collection<Map<String, Object>> guards) {
        Set<String> cells = new LinkedHashSet<>();
        for (Map<String, Object> guard : guards) {
            String cell = text(guard.get("fromCell"));
            if (!cell.isEmpty()) cells.add(cell);
        }
        List<String> result = new ArrayList<>(cells);
        Collections.sort(result);
        return result;
    }

    /**
     * Names, per site this branch decides, the Jimple outcome the analyzer
     * proved is required to reach that site.  The analyzer already ran the
     * CFG reachability; keeping only the aggregate answer threw away which
     * site each answer was about, which is the part a consumer needs to ask
     * whether one exact position survives a flip.  A site two rows disagree
     * about, or that no row proves an outcome for, is left out: a reader may
     * conclude unreachability only from a proof.
     */
    private static List<Map<String, Object>> guardedSiteOutcomes(
            Collection<Map<String, Object>> guards) {
        Map<String, Boolean> proved = new TreeMap<>();
        Set<String> unproved = new TreeSet<>();
        for (Map<String, Object> guard : guards) {
            List<Map<String, Object>> controlled = new ArrayList<>();
            controlled.addAll(rows(guard.get("guardedMutations")));
            controlled.addAll(rows(guard.get("controlledDefinitions")));
            controlled.addAll(rows(guard.get("guardedEffects")));
            for (Map<String, Object> row : controlled) {
                String site = first(first(
                        text(row.get("guardedMutationSiteId")),
                        text(row.get("controlledDefinitionSiteId"))),
                        text(row.get("effectSiteId")));
                if (site.isEmpty()) continue;
                Boolean outcome = booleanValue(row.get("requiredOutcome"));
                if (outcome == null) {
                    unproved.add(site);
                    continue;
                }
                Boolean prior = proved.putIfAbsent(site, outcome);
                if (prior != null && !prior.equals(outcome)) {
                    unproved.add(site);
                }
            }
        }
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map.Entry<String, Boolean> entry : proved.entrySet()) {
            if (unproved.contains(entry.getKey())) continue;
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("siteId", entry.getKey());
            row.put("requiredOutcome", entry.getValue());
            result.add(row);
        }
        return result;
    }

    private static Boolean consistentRequiredOutcome(
            Collection<Map<String, Object>> guards) {
        Boolean selected = null;
        for (Map<String, Object> guard : guards) {
            Boolean value = booleanValue(guard.get("requiredOutcome"));
            if (value == null) continue;
            if (selected != null && !selected.equals(value)) return null;
            selected = value;
        }
        return selected;
    }

    private static boolean hasConflictingRequiredOutcomes(
            Collection<Map<String, Object>> guards) {
        Set<Boolean> values = new LinkedHashSet<>();
        for (Map<String, Object> guard : guards) {
            Boolean value = booleanValue(guard.get("requiredOutcome"));
            if (value != null) values.add(value);
        }
        return values.size() > 1;
    }

    private static Boolean booleanValue(Object value) {
        if (value instanceof Boolean) return (Boolean) value;
        if ("true".equalsIgnoreCase(text(value))) return Boolean.TRUE;
        if ("false".equalsIgnoreCase(text(value))) return Boolean.FALSE;
        return null;
    }

    /**
     * Classifies only positively proven structural traversal guards.  The
     * runtime-refined graph is already failure-directed, so every remaining
     * ambiguous guard stays explorable instead of being discarded by a name
     * heuristic.  A size/isEmpty/array-length value is structural only when
     * the same guard also has loop recurrence evidence; semantic cardinality
     * checks outside a loop remain explorable.
     */
    private static final class BranchPolicyClassifier {
        private final Map<String, List<Map<String, Object>>> incoming =
                new LinkedHashMap<>();

        private BranchPolicyClassifier(
                Collection<Map<String, Object>> edges) {
            for (Map<String, Object> edge : edges) {
                String target = text(edge.get("toCell"));
                if (!target.isEmpty()) {
                    incoming.computeIfAbsent(target,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
        }

        private boolean structuralLoopGuard(
                String site, Collection<Map<String, Object>> guards) {
            if (!loopRecurrence(site, guards)) return false;
            for (String operand : operandCells(guards)) {
                if (hasStructuralSource(operand)) return true;
            }
            return false;
        }

        private boolean cfgLoopControlGuard(
                Collection<Map<String, Object>> guards) {
            for (Map<String, Object> guard : guards) {
                if (Boolean.TRUE.equals(booleanValue(
                        guard.get("loopControlGuard")))) {
                    return true;
                }
            }
            return false;
        }

        private boolean structureCarrierGuard(
                Collection<Map<String, Object>> guards) {
            for (String operand : operandCells(guards)) {
                if (nearestContainerRole(operand).equals(
                        DependencyRole.CONCRETE_STRUCTURE_CARRIER)) {
                    return true;
                }
            }
            return false;
        }

        private String nearestContainerRole(String start) {
            Set<String> visited = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>();
            work.add(start);
            boolean carrier = false;
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (!visited.add(cell)) continue;
                for (Map<String, Object> edge : incoming.getOrDefault(
                        cell, Collections.<Map<String, Object>>emptyList())) {
                    if ("container_receiver".equals(text(edge.get("kind")))) {
                        String role = DependencyRole.normalize(
                                edge.get("dependencyRole"));
                        if (DependencyRole.VALUE_FRONTIER.equals(role)) {
                            return DependencyRole.VALUE_FRONTIER;
                        }
                        carrier = true;
                        continue;
                    }
                    if (exactLocalPass(edge)) {
                        String predecessor = text(edge.get("fromCell"));
                        if (!predecessor.isEmpty()) work.addLast(predecessor);
                    }
                }
            }
            return carrier ? DependencyRole.CONCRETE_STRUCTURE_CARRIER
                    : DependencyRole.VALUE_FRONTIER;
        }

        private boolean loopRecurrence(
                String site, Collection<Map<String, Object>> guards) {
            for (Map<String, Object> guard : guards) {
                String guardSite = first(text(guard.get("guardSiteId")),
                        text(guard.get("siteId")));
                if (!site.equals(guardSite)) continue;
                if (Boolean.TRUE.equals(booleanValue(
                        guard.get("sameCellRedefinition")))) {
                    return true;
                }
                for (Map<String, Object> definition
                        : rows(guard.get("controlledDefinitions"))) {
                    if (Boolean.TRUE.equals(booleanValue(
                            definition.get("sameCellRedefinition")))) {
                        return true;
                    }
                }
            }
            return false;
        }

        private boolean hasStructuralSource(String start) {
            Set<String> visitedCells = new LinkedHashSet<>();
            Set<String> visitedEdges = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>();
            work.add(start);
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (!visitedCells.add(cell)) continue;
                for (Map<String, Object> edge : incoming.getOrDefault(
                        cell, Collections.<Map<String, Object>>emptyList())) {
                    String identity = first(text(edge.get("id")),
                            text(edge.get("siteId")) + "\n"
                                    + text(edge.get("fromCell")) + "\n"
                                    + text(edge.get("toCell")));
                    if (!visitedEdges.add(identity)
                            || "GUARD".equals(text(
                            edge.get("transferKind")))) {
                        continue;
                    }
                    String invoke = text(edge.get("invoke"));
                    if (JavaContainerTypes
                            .structuralIterationPredicate(invoke)
                            || JavaContainerTypes
                            .structuralCardinalityOperation(invoke)
                            || Boolean.TRUE.equals(booleanValue(
                            edge.get("arrayLengthOperation")))) {
                        return true;
                    }
                    String predecessor = text(edge.get("fromCell"));
                    if (!predecessor.isEmpty()) work.addLast(predecessor);
                }
            }
            return false;
        }
    }

    /** Projects a proved lookup-result role back to its exact heap port. */
    private static final class DependencyRoleClassifier {
        private final Map<String, List<Map<String, Object>>> outgoing =
                new LinkedHashMap<>();

        private DependencyRoleClassifier(
                Collection<Map<String, Object>> edges) {
            for (Map<String, Object> edge : edges) {
                String source = text(edge.get("fromCell"));
                if (!source.isEmpty()) {
                    outgoing.computeIfAbsent(source,
                            ignored -> new ArrayList<>()).add(edge);
                }
            }
        }

        private String heapReadRole(Map<String, Object> heapRead) {
            String start = text(heapRead.get("toCell"));
            if (start.isEmpty()) return DependencyRole.VALUE_FRONTIER;
            Set<String> visited = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>();
            work.add(start);
            boolean carrier = false;
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (!visited.add(cell)) continue;
                for (Map<String, Object> edge : outgoing.getOrDefault(
                        cell, Collections.<Map<String, Object>>emptyList())) {
                    if ("container_receiver".equals(text(edge.get("kind")))) {
                        String role = DependencyRole.normalize(
                                edge.get("dependencyRole"));
                        if (DependencyRole.VALUE_FRONTIER.equals(role)) {
                            return DependencyRole.VALUE_FRONTIER;
                        }
                        carrier = true;
                        continue;
                    }
                    if (exactLocalPass(edge)) {
                        String next = text(edge.get("toCell"));
                        if (!next.isEmpty()) work.addLast(next);
                    }
                }
            }
            return carrier ? DependencyRole.CONCRETE_STRUCTURE_CARRIER
                    : DependencyRole.VALUE_FRONTIER;
        }
    }

    private static boolean exactLocalPass(Map<String, Object> edge) {
        return "local_def_use".equals(text(edge.get("kind")))
                && ("VALUE_PASS".equals(text(edge.get("transferKind")))
                || !text(edge.get("valueFlowAuthority")).isEmpty());
    }

    /**
     * Every writer the trace observed for each demanded shared-field read.
     *
     * <p>The pairing is deliberately not a decision.  A writer is retained
     * when the run makes it <em>possible</em>: same receiver object, same
     * declared leaf, and ordered before the read in this trace.
     * Logical source is deliberately not part of this test.  In a shared-JVM
     * distributed test, a background task and an RPC handler can execute under
     * different source contexts while accessing the same Java object; exact
     * receiver identity is the heap authority that joins them.  Which of the
     * retained writers the read actually took
     * is a question only the session can answer, and it answers it later; a
     * concrete value cannot answer it at all, because two writers of one value
     * are indistinguishable by exactly the test that would have to separate
     * them.  Retaining all of them is what keeps the failure-directed closure
     * able to reach every producer the target may depend on.</p>
     */
    private static List<Map<String, Object>> fieldFlows(
            List<Map<String, Object>> regions,
            Set<String> demandedFields) throws IOException {
        // Reads state the demand, so they are collected first under the plain
        // resource default; the writes are then filtered relative to each
        // read and the latest preceding access of each writer port is kept.
        List<BoundPort> reads = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            collectPorts(reads, text(region.get("regionId")),
                    rows(region.get("symbolicInputs")), NO_ACCESS_DEMAND);
        }
        reads.removeIf(port -> !demandedFields.contains(
                port.leafDeclaration()));
        RuntimeAccessDemand demand = leafReceiverDemand(reads);
        List<BoundPort> writes = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            collectPorts(writes, text(region.get("regionId")),
                    rows(region.get("outputs")), demand);
        }
        writes.removeIf(port -> !demandedFields.contains(
                port.leafDeclaration()));
        Map<String, List<BoundPort>> writesByReceiverAndField =
                new LinkedHashMap<>();
        for (BoundPort write : writes) {
            if (write.receiver == 0) continue;
            writesByReceiverAndField.computeIfAbsent(
                    write.receiver + "\n" + write.leafDeclaration(),
                    ignored -> new ArrayList<>()).add(write);
        }
        List<Map<String, Object>> result = new ArrayList<>();
        for (BoundPort read : reads) {
            String readField = read.leafDeclaration();
            Map<String, BoundPort> selectedByPort =
                    new LinkedHashMap<>();
            for (BoundPort write : writesByReceiverAndField.getOrDefault(
                    read.receiver + "\n" + readField,
                    Collections.<BoundPort>emptyList())) {
                if (sameActivation(write, read)
                        || write.seq >= read.seq
                        || (read.valueObject > 0 || write.valueObject > 0)
                        && read.valueObject != write.valueObject
                        || DependencyRole.CONCRETE_STRUCTURE_CARRIER.equals(
                        read.dependencyRole)
                        && !"CONTAINER_MUTATION".equals(write.bindingKind)
                        && read.valueObject <= 0) {
                    continue;
                }
                String writerPort = portDemandKey(write.occurrenceId,
                        write.port);
                BoundPort selected = selectedByPort.get(writerPort);
                if (selected == null || write.seq > selected.seq) {
                    selectedByPort.put(writerPort, write);
                }
            }
            for (BoundPort write : selectedByPort.values()) {
                Map<String, Object> edge = fieldFlowEdge(write, read,
                        "", "RF.");
                if ("CONTAINER_MUTATION".equals(write.bindingKind)) {
                    edge.put("writerFieldReadSeq",
                            write.writerFieldReadSeq);
                    edge.put("mutatorEnterSeq", write.mutatorEnterSeq);
                    edge.put("mutationCompletionSeq",
                            write.mutationCompletionSeq);
                    edge.put("mutationInvocationId",
                            write.mutationInvocationId);
                    edge.put("mutatorDeclaredCallee",
                            write.mutatorDeclaredCallee);
                    edge.put("readerValueObjectId", read.valueObject);
                }
                result.add(edge);
            }
        }
        return result;
    }

    /**
     * Keeps an exact reference-field conduit when its writer occurrence had
     * already received a configured symbolic component.
     *
     * <p>This is deliberately scheduling metadata, not a value relation.  A
     * reference carrier remains concrete and the field edge must still name
     * the same runtime receiver, the same stored object and an ordered
     * write/read pair.  The marker only lets the failure walk retain the
     * writer and the configured component delivery that preceded it; replay's
     * VM live-handle handoff is still the only component-value authority.</p>
     */
    private static void markTransportedReferenceFrontiers(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> edges) {
        Map<String, List<Long>> componentReceipts = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"RUNTIME_PROTOCOL_FLOW".equals(text(edge.get("kind")))
                    || !DependencyRole.VALUE_FRONTIER.equals(
                    DependencyRole.normalize(edge.get("dependencyRole")))
                    || text(edge.get(CommunicationCatalogContract
                    .PORT_COMPONENT_OF)).isEmpty()
                    || text(edge.get(CommunicationCatalogContract
                    .PORT_HANDOFF_LEAF_PATH)).isEmpty()
                    || text(edge.get(CommunicationCatalogContract
                    .PORT_ENCODING_AUTHORITY)).isEmpty()) {
                continue;
            }
            long receivedAt = longNumber(edge.get("receiverEventSeq"), -1L);
            String occurrence = text(edge.get("toOccurrenceId"));
            if (receivedAt >= 0L && !occurrence.isEmpty()) {
                componentReceipts.computeIfAbsent(occurrence,
                        ignored -> new ArrayList<>()).add(receivedAt);
            }
        }
        if (componentReceipts.isEmpty()) return;

        Map<String, Map<String, Object>> inputs = new LinkedHashMap<>();
        for (Map<String, Object> region : regions) {
            for (Map<String, Object> input
                    : rows(region.get("symbolicInputs"))) {
                String occurrence = text(input.get("occurrenceId"));
                String port = text(input.get("portId"));
                if (!occurrence.isEmpty() && !port.isEmpty()) {
                    inputs.put(portDemandKey(occurrence, port), input);
                }
            }
        }
        for (Map<String, Object> edge : edges) {
            if (!"RUNTIME_FIELD_FLOW".equals(text(edge.get("kind")))
                    || longNumber(edge.get("valueObjectId"), 0L) <= 0L) {
                continue;
            }
            String writer = text(edge.get("fromOccurrenceId"));
            long writtenAt = longNumber(edge.get("writerEventSeq"), -1L);
            boolean precededByComponent = false;
            for (Long receivedAt : componentReceipts.getOrDefault(writer,
                    Collections.<Long>emptyList())) {
                if (writtenAt >= 0L && receivedAt < writtenAt) {
                    precededByComponent = true;
                    break;
                }
            }
            if (!precededByComponent) continue;
            edge.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
            edge.put(AutomaticRegionEdge.TRANSPORTED_VALUE_FRONTIER_FIELD,
                    AutomaticRegionEdge
                            .TRANSPORTED_VALUE_FRONTIER_AUTHORITY);
            Map<String, Object> input = inputs.get(portDemandKey(
                    text(edge.get("toOccurrenceId")),
                    text(edge.get("toPort"))));
            if (input != null) {
                input.put(AutomaticRegionEdge
                                .TRANSPORTED_VALUE_FRONTIER_FIELD,
                        AutomaticRegionEdge
                                .TRANSPORTED_VALUE_FRONTIER_AUTHORITY);
            }
        }
    }

    /**
     * Binds a still-unclosed demanded leaf to the region that actually wrote
     * it.
     *
     * <p>A leaf reached through a reference another region handed over is
     * demanded on the reading side, but the write that produced it is
     * activation-local to the producer: the object is built there and only
     * later escapes through a carrier field.  The failure-relevant field set
     * is stated over carriers, so the ordinary field flow never pairs the two
     * and the leaf is left to be replayed as a concrete observation.</p>
     *
     * <p>Runtime object identity settles it exactly.  A write to the same
     * object and the same declaration, in another activation, before this
     * read, is that read's producer.  Only an unambiguous writer counts: if
     * several distinct writer ports could have produced the value, the leaf
     * keeps its concrete under-approximation rather than inventing a
     * relation the trace does not prove.</p>
     */
    static List<Map<String, Object>> demandedLeafProducerFlows(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> regionEdges) throws IOException {
        Set<String> closedInputs = new LinkedHashSet<>();
        for (Map<String, Object> edge : regionEdges) {
            String toOccurrence = text(edge.get("toOccurrenceId"));
            String toPort = text(edge.get("toPort"));
            if (!toOccurrence.isEmpty() && !toPort.isEmpty()) {
                closedInputs.add(portDemandKey(toOccurrence, toPort));
            }
        }
        List<BoundPort> reads = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            String regionId = text(region.get("regionId"));
            // Only a semantic scalar leaf is at stake here.  A carrier read
            // is answered by the ordinary field flow over demanded fields,
            // and widening this pass to carriers would invent relations the
            // failure never asked for.
            List<Map<String, Object>> leaves = new ArrayList<>();
            for (Map<String, Object> port
                    : rows(region.get("symbolicInputs"))) {
                if (primitiveLeaf(port)) leaves.add(port);
            }
            collectPorts(reads, regionId, leaves, NO_ACCESS_DEMAND);
        }
        reads.removeIf(read -> read.receiver == 0
                || read.leafDeclaration().isEmpty()
                || DependencyRole.CONCRETE_STRUCTURE_CARRIER.equals(
                read.dependencyRole)
                || closedInputs.contains(portDemandKey(read.occurrenceId,
                read.port)));
        // The producing write is activation-local to a long-lived root, so
        // the trace may record it far past the resource default; demanding it
        // by receiver and leaf is what keeps it visible here.
        RuntimeAccessDemand demand = leafReceiverDemand(reads);
        List<BoundPort> writes = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            collectPorts(writes, text(region.get("regionId")),
                    rows(region.get("outputs")), demand);
        }
        Map<String, List<BoundPort>> writesByReceiverAndField =
                new LinkedHashMap<>();
        for (BoundPort write : writes) {
            if (write.receiver == 0) continue;
            writesByReceiverAndField.computeIfAbsent(
                    write.receiver + "\n" + write.leafDeclaration(),
                    ignored -> new ArrayList<>()).add(write);
        }
        List<Map<String, Object>> result = new ArrayList<>();
        for (BoundPort read : reads) {
            String readField = read.leafDeclaration();
            Map<String, BoundPort> byWriterPort = new LinkedHashMap<>();
            for (BoundPort write : writesByReceiverAndField.getOrDefault(
                    read.receiver + "\n" + readField,
                    Collections.<BoundPort>emptyList())) {
                if (sameActivation(write, read)
                        || write.seq >= read.seq) {
                    continue;
                }
                String writerPort = portDemandKey(write.occurrenceId,
                        write.port);
                BoundPort selected = byWriterPort.get(writerPort);
                if (selected == null || write.seq > selected.seq) {
                    byWriterPort.put(writerPort, write);
                }
            }
            for (BoundPort write : byWriterPort.values()) {
                result.add(fieldFlowEdge(write, read,
                        LEAF_PRODUCER_AUTHORITY, "RF.LEAF."));
            }
        }
        return result;
    }

    /** The cross-run identity of the read leaf: its owner and its name. */
    private static String recordedFieldKey(BoundPort read) {
        DeclaredFieldCell field = DeclaredFieldCell.parse(
                read.leafDeclaration());
        return field == null ? ""
                : RecordedReadFrom.fieldKey(field.owner(), field.name);
    }

    /**
     * Renders one write/read pair as a runtime field-flow candidate edge.
     *
     * <p>Both field-flow rules publish the same edge schema; only the
     * authority that retained the pair and the edge-id prefix differ.  A
     * field added to one rule and not the other would silently make the two
     * kinds of edge un-mergeable downstream.</p>
     *
     * <p>The provenance an edge leaves here is always
     * {@link RecordedReadFrom#PROVENANCE_CANDIDATE}, with the gap that says
     * why.  Nothing at trace aggregation may stamp an edge as observed
     * provenance: the observation that would justify it belongs to a symbolic
     * session that has not run yet.</p>
     */
    private static Map<String, Object> fieldFlowEdge(
            BoundPort write, BoundPort read, String authority,
            String edgeIdPrefix) {
        String alternative = write.occurrenceId + "\n" + write.port
                + "\n" + write.site
                + "\n" + write.occurrence + "\n" + read.occurrenceId
                + "\n" + read.port
                + "\n" + read.site + "\n" + read.occurrence;
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("schemaVersion", 3);
        edge.put("kind", "RUNTIME_FIELD_FLOW");
        edge.put("transportKind", "HEAP");
        if (!authority.isEmpty()) {
            edge.put("authority", authority);
        }
        edge.put("edgeId", edgeIdPrefix + UUID.nameUUIDFromBytes(
                alternative.getBytes(StandardCharsets.UTF_8)));
        edge.put("fromRegion", write.region);
        edge.put("toRegion", read.region);
        edge.put("fromPort", write.port);
        edge.put("toPort", read.port);
        edge.put("fromOccurrenceId", write.occurrenceId);
        edge.put("toOccurrenceId", read.occurrenceId);
        // Recorded trace evidence for the observed endpoints; selection and
        // identity above are by occurrence only.
        edge.put("fromRootCallId", write.rootCallId);
        edge.put("toRootCallId", read.rootCallId);
        edge.put("receiverObjectId", write.receiver);
        edge.put("valueObjectId", write.valueObject);
        edge.put("primitiveValue", write.primitiveValue);
        edge.put("writerEventSeq", write.seq);
        edge.put("readerEventSeq", read.seq);
        edge.put("writerOccurrence", write.occurrence);
        edge.put("bindingKind", write.bindingKind);
        edge.put("dependencyRole", read.dependencyRole);
        edge.put("fieldPathDeclarations", Collections.singletonList(
                write.leafDeclaration()));
        // The join address this candidate will be resolved under, and the
        // state it is in.  A downstream reader that could not tell a retained
        // candidate from a proven edge would report the first with the
        // confidence of the second.
        edge.put(RecordedReadFrom.EDGE_FIELD, recordedFieldKey(read));
        edge.put(RecordedReadFrom.EDGE_SOURCE_KEY, read.sourceKey);
        edge.put(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        edge.put(RecordedReadFrom.EDGE_PROVENANCE_GAP,
                SharedStateEvidence.reason(
                        SharedStateEvidence.NOT_SELECTED));
        return edge;
    }

    /** Names the leaf-producer binding for downstream manifest tracing. */
    static final String LEAF_PRODUCER_AUTHORITY =
            "RUNTIME_FIELD_FLOW_LEAF_PRODUCER_V1";

    private static Set<String> failureRelevantFields(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> graph) {
        Set<String> targetRegions = new LinkedHashSet<>();
        Set<String> selectedRegions = new LinkedHashSet<>();
        for (Map<String, Object> region : regions) {
            selectedRegions.add(text(region.get("regionId")));
            if (text(region.get("selection")).startsWith("EXCEPTION")) {
                targetRegions.add(text(region.get("regionId")));
            }
        }
        Map<String, List<Map<String, Object>>> localIncoming =
                new LinkedHashMap<>();
        Set<String> observedSelectedReads = new LinkedHashSet<>();
        Deque<ContextCell> work = new ArrayDeque<>();
        for (Map<String, Object> edge : graph) {
            String from = text(edge.get("fromCell"));
            if ("HEAP_READ".equals(text(edge.get("transferKind")))
                    && declaredField(from)) {
                for (Map<String, Object> binding
                        : rows(edge.get("runtimeFieldBindings"))) {
                    if (selectedRegions.contains(
                            text(binding.get("regionId")))) {
                        observedSelectedReads.add(from);
                        break;
                    }
                }
            }
            String to = text(edge.get("toCell"));
            if (to.isEmpty()) continue;
            for (String region : strings(edge.get("regionIds"))) {
                if (!selectedRegions.contains(region)) continue;
                localIncoming.computeIfAbsent(contextKey(region, to),
                        ignored -> new ArrayList<>()).add(edge);
                if (targetRegions.contains(region)
                        && to.contains("#exception:")) {
                    work.add(new ContextCell(region, to));
                }
            }
        }
        Set<String> visited = new LinkedHashSet<>();
        Set<String> fields = new LinkedHashSet<>();
        while (!work.isEmpty()) {
            ContextCell current = work.removeFirst();
            String key = contextKey(current.region, current.cell);
            if (!visited.add(key)) continue;
            for (Map<String, Object> edge : localIncoming.getOrDefault(key,
                    Collections.emptyList())) {
                String from = text(edge.get("fromCell"));
                if ("HEAP_READ".equals(text(edge.get("transferKind")))
                        && declaredField(from)) {
                    fields.add(from);
                }
                if (!from.isEmpty()) {
                    work.addLast(new ContextCell(current.region, from));
                }
            }
        }
        // Communication output components deliberately carry no static
        // inputPorts: their live expression is a VM handoff, not a Java
        // equality.  Prebuild exact observed heap candidates for every
        // selected production occurrence; the failure closure activates only
        // those reads ordered before an output it actually demands.
        fields.addAll(observedSelectedReads);
        Set<String> dynamicallyDefined = new LinkedHashSet<>();
        for (Map<String, Object> edge : graph) {
            String field = text(edge.get("toCell"));
            if ("HEAP_WRITE".equals(text(edge.get("transferKind")))
                    && declaredField(field)) {
                // Constructor writes are ordinary definitions of the
                // constructed object's scalar leaves.  They become a region
                // boundary only when the failure-directed slice demands that
                // exact field and runtime evidence later reads the same
                // receiver in another activation.  Keeping them here does
                // not turn constructors into regions or expand arbitrary
                // objects; fieldFlows performs the exact receiver/leaf join.
                dynamicallyDefined.add(field);
            }
        }
        fields.retainAll(dynamicallyDefined);
        fields.removeIf(RuntimeSelectedRegionFinalizer
                ::toolBookkeepingField);
        return fields;
    }

    /**
     * Heap owned by an injected Causynth support class is tracing metadata,
     * never application shared state.
     *
     * <p>The source adapters intentionally reserve the {@code Causynth*}
     * class prefix for exchange tables, pending handoffs, source registries,
     * and other observation state.  Those tables may sit directly on a
     * target's concrete call path, but composing their {@code Map.put/remove}
     * operations creates causal edges between independent RPC attempts.  The
     * application value already crosses through the declared communication
     * port and the VM expression handoff, so admitting the helper heap as a
     * second channel is both redundant and wrong.</p>
     *
     * <p>This is a tool ownership rule, not an HDFS field list: every system
     * adapter uses the same reserved prefix, while ordinary application
     * fields and containers remain eligible for the bounded writer model.</p>
     */
    private static boolean toolBookkeepingPort(Map<String, Object> port) {
        List<String> declarations = strings(
                port.get("fieldPathDeclarations"));
        if (declarations.isEmpty()) {
            String cell = text(port.get("cell"));
            if (declaredField(cell)) declarations.add(cell);
        }
        if (declarations.isEmpty()) return false;
        for (String declaration : declarations) {
            if (!toolBookkeepingField(declaration)) return false;
        }
        return true;
    }

    private static boolean toolBookkeepingField(String declaration) {
        DeclaredFieldCell field = DeclaredFieldCell.parse(declaration);
        if (field == null) return false;
        String owner = field.owner();
        int packageEnd = owner.lastIndexOf('.');
        String simple = packageEnd < 0 ? owner
                : owner.substring(packageEnd + 1);
        return simple.startsWith("Causynth");
    }

    private static String contextKey(String region, String cell) {
        return region + "\n" + cell;
    }

    private static boolean declaredField(String cell) {
        return cell.startsWith("<") && cell.endsWith(">")
                && cell.contains(":") && !cell.contains("(");
    }

    private static boolean sameActivation(BoundPort left,
                                          BoundPort right) {
        return left.occurrenceId.equals(right.occurrenceId);
    }

    /**
     * Ports that read or write one declared field of one observed object.
     *
     * <p>An exact accessor return is such a read: it names the same declared
     * leaf and the same receiver object as a direct {@code getfield}.  Only
     * its transport label differs, so excluding it would leave a demanded
     * scalar leaf below a shared reference carrier without any producer even
     * though the exact writer is present in this trace.</p>
     */
    private static boolean causalHeapPort(Map<String, Object> port) {
        if ("HEAP".equals(text(port.get("transportKind")))) return true;
        return "ACCESSOR_RETURN".equals(text(port.get("sourceKind")))
                && number(port.get("fieldReceiverObjectId"), 0) > 0
                && !strings(port.get("fieldPathDeclarations")).isEmpty();
    }

    private static void collectPorts(List<BoundPort> target, String region,
                                     List<Map<String, Object>> ports,
                                     RuntimeAccessDemand demand)
            throws IOException {
        for (Map<String, Object> port : ports) {
            if (!causalHeapPort(port)) {
                continue;
            }
            List<Map<String, Object>> accesses = boundedRuntimeAccesses(
                    port, demand);
            if (accesses.isEmpty()) {
                accesses = Collections.singletonList(port);
            }
            for (Map<String, Object> access : accesses) {
                target.add(new BoundPort(region, text(port.get("portId")),
                        first(text(access.get("sourceKey")),
                                text(port.get("sourceKey"))),
                        first(text(access.get("occurrenceId")),
                                text(port.get("occurrenceId"))),
                        longNumber(access.get("rootCallId"),
                                longNumber(port.get("rootCallId"), 0L)),
                        number(access.get("fieldReceiverObjectId"),
                                number(port.get("fieldReceiverObjectId"), 0)),
                        longNumber(access.get("eventSeq"),
                                longNumber(port.get("eventSeq"), 0L)),
                        strings(access.containsKey("fieldPathDeclarations")
                                ? access.get("fieldPathDeclarations")
                                : port.get("fieldPathDeclarations")),
                        number(access.get("valueObjectId"),
                                number(port.get("valueObjectId"), 0)),
                        first(text(access.get("primitiveValue")),
                                text(port.get("primitiveValue"))),
                        first(text(access.get("bindingKind")),
                                text(port.get("bindingKind"))),
                        longNumber(access.get("writerFieldReadSeq"), -1L),
                        longNumber(access.get("mutatorEnterSeq"), -1L),
                        longNumber(access.get("mutationCompletionSeq"), -1L),
                        longNumber(access.get("mutationInvocationId"), -1L),
                        first(text(access.get("mutatorDeclaredCallee")),
                                text(port.get("mutatorDeclaredCallee"))),
                        DependencyRole.normalize(
                                port.get("dependencyRole")),
                        first(text(access.get("staticAccessSiteId")),
                                text(port.get("portId"))),
                        number(access.get(
                                "activationLocalStaticSiteOccurrence"),
                                1)));
            }
        }
    }

    /**
     * Assigns a replay-stable occurrence within one activation and static
     * access site. Raw trace sequence numbers remain evidence only; the
     * bounded occurrence is the cross-run identity used by causal edges.
     */
    /**
     * Decides whether the closure names one recorded access exactly, so that
     * the per-site resource cap must not drop it.
     */
    private interface RuntimeAccessDemand {
        boolean required(Map<String, Object> port, Map<String, Object> access);
    }

    /** Nothing is demanded yet; only the resource default applies. */
    private static final RuntimeAccessDemand NO_ACCESS_DEMAND =
            (port, access) -> false;

    /**
     * Resource ceiling on the accesses one static site may contribute to one
     * port.  Unlike the loop bound this states no execution semantics: it
     * exists so that a long-lived thread root cannot materialise an unbounded
     * access array, and a port that cannot be served within it says so on the
     * port rather than silently keeping an arbitrary subset.
     */
    static final int MAX_RETAINED_SITE_ACCESSES = 64;

    /** Names a port whose demand exceeded the retained-access ceiling. */
    static final String DEMAND_RETENTION_REFUSAL = "demandRetentionRefusal";

    /**
     * Keeps a bounded, demand-aware view of one port's recorded accesses.
     *
     * <p>The occurrence index counts every activation-local execution of the
     * site, including the ones nested calls contribute; it is not a loop body
     * counter.  Capping it is therefore a resource default, never the loop
     * bound, and an access the closure names exactly is retained however late
     * in the activation the trace recorded it.</p>
     *
     * <p>A site whose demand exceeds the resource ceiling cannot be served
     * honestly: keeping some arbitrary 64 of its demanded accesses would be
     * the silent truncation this pass exists to remove.  Such a port keeps
     * only the plain resource default and carries the refusal by name, so the
     * leaves below it stay under-approximated and the reason travels with the
     * artifact instead of ending the whole refinement over one hot site.</p>
     */
    private static List<Map<String, Object>> boundedRuntimeAccesses(
            Map<String, Object> port, RuntimeAccessDemand demand)
            throws IOException {
        List<Map<String, Object>> accesses = new ArrayList<>(
                rows(port.get("runtimeAccesses")));
        accesses.sort(Comparator.comparingLong(access ->
                longNumber(access.get("eventSeq"), Long.MAX_VALUE)));
        Map<String, Integer> occurrences = new LinkedHashMap<>();
        Map<String, Integer> retained = new LinkedHashMap<>();
        List<Map<String, Object>> bounded = new ArrayList<>();
        List<Map<String, Object>> resourceDefault = new ArrayList<>();
        String refusal = "";
        for (Map<String, Object> access : accesses) {
            String site = first(text(access.get("staticAccessSiteId")),
                    text(port.get("portId")));
            int occurrence = occurrences.getOrDefault(site, 0) + 1;
            occurrences.put(site, occurrence);
            access.put("staticAccessSiteId", site);
            access.put("activationLocalStaticSiteOccurrence", occurrence);
            boolean withinDefault =
                    occurrence <= LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS;
            if (withinDefault) resourceDefault.add(access);
            if (!withinDefault && !demand.required(port, access)) continue;
            int kept = retained.getOrDefault(site, 0) + 1;
            retained.put(site, kept);
            if (kept > MAX_RETAINED_SITE_ACCESSES) {
                if (refusal.isEmpty()) {
                    refusal = "BOUND_INSUFFICIENT: static site " + site
                            + " demands more than " + MAX_RETAINED_SITE_ACCESSES
                            + " activation-local accesses";
                }
                continue;
            }
            bounded.add(access);
        }
        if (!refusal.isEmpty()) {
            port.put(DEMAND_RETENTION_REFUSAL, refusal);
            return resourceDefault;
        }
        return bounded;
    }

    /**
     * Demands exactly the writes that could answer a collected read: the same
     * receiver object and the same declared leaf.  That is a necessary
     * condition of every pairing below, so a write this excludes could never
     * have been chosen, while a write it admits survives the resource cap.
     */
    private static RuntimeAccessDemand leafReceiverDemand(
            List<BoundPort> reads) {
        Set<String> demanded = new LinkedHashSet<>();
        Set<String> demandedReferenceValues = new LinkedHashSet<>();
        for (BoundPort read : reads) {
            if (read.receiver != 0 && !read.leafDeclaration().isEmpty()) {
                String location = read.receiver + "\n"
                        + read.leafDeclaration();
                demanded.add(location);
                if (read.valueObject > 0) {
                    demandedReferenceValues.add(location + "\n"
                            + read.valueObject);
                }
            }
        }
        return (port, access) -> {
            int receiver = number(access.get("fieldReceiverObjectId"),
                    number(port.get("fieldReceiverObjectId"), 0));
            List<String> declarations = strings(
                    access.containsKey("fieldPathDeclarations")
                            ? access.get("fieldPathDeclarations")
                            : port.get("fieldPathDeclarations"));
            if (receiver == 0 || declarations.isEmpty()) return false;
            String location = receiver + "\n"
                    + declarations.get(declarations.size() - 1);
            int valueObject = number(access.get("valueObjectId"),
                    number(port.get("valueObjectId"), 0));
            return valueObject > 0
                    ? demandedReferenceValues.contains(location + "\n"
                    + valueObject)
                    : demanded.contains(location);
        };
    }

    private static void requireRefinedGraph(
            List<Map<String, Object>> rows, File source) throws IOException {
        if (rows.isEmpty()) {
            throw new IOException("refined graph is empty: " + source);
        }
        for (Map<String, Object> row : rows) {
            if (number(row.get("schemaVersion"), -1) != 3
                    || number(row.get("refinementSchemaVersion"), -1) != 1
                    || !REFINED_KIND.equals(text(row.get("graphKind")))) {
                throw new IOException("full region planning requires a "
                        + "schema-3 runtime-refined graph: " + source);
            }
        }
    }

    private static void requireSkeleton(Map<String, Object> row, File source)
            throws IOException {
        if (number(row.get("schemaVersion"), -1) != 3
                || !"REGION_SKELETON".equals(text(row.get("kind")))) {
            throw new IOException("invalid selected skeleton: " + source);
        }
    }

    private static List<Map<String, Object>> read(File file)
            throws IOException {
        List<Map<String, Object>> result = new ArrayList<>();
        try (BufferedReader reader = reader(file)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (!line.trim().isEmpty()) {
                    Map<String, Object> row = GSON.fromJson(line, ROW);
                    if (row == null) {
                        throw new IOException("null row in " + file);
                    }
                    result.add(row);
                }
            }
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

    @SuppressWarnings("unchecked")
    private static Map<String, Object> row(Object value) {
        return value instanceof Map<?, ?>
                ? (Map<String, Object>) value
                : Collections.<String, Object>emptyMap();
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
                String text = text(item);
                if (!text.isEmpty()) {
                    result.add(text);
                }
            }
        }
        return result;
    }

    private static int number(Object value, int fallback) {
        return value instanceof Number ? ((Number) value).intValue()
                : fallback;
    }

    private static long longNumber(Object value, long fallback) {
        return value instanceof Number ? ((Number) value).longValue()
                : fallback;
    }

    private static String first(String left, String right) {
        return left.isEmpty() ? right : left;
    }

    private static String text(Object value) {
        return value == null ? "" : String.valueOf(value);
    }

    /**
     * Activation-local backward slices from demanded outputs (or a fatal
     * branch) to exact boundary input ports.  Static cells establish the
     * dependency relation; runtime root call ids select the concrete port
     * occurrence to which that relation applies.
     */
    private static final class RegionDemandIndex {
        private final Map<String, Map<String, Object>> inputs =
                new LinkedHashMap<>();
        private final Map<String, Map<String, Object>> outputs =
                new LinkedHashMap<>();
        private final Map<String, List<String>> inputsByInstance =
                new LinkedHashMap<>();
        /** Static region scope of each indexed activation occurrence. */
        private final Map<String, String> regionByOccurrence =
                new LinkedHashMap<>();
        private final Map<String, List<String>> inputsByBoundary =
                new LinkedHashMap<>();
        private final Map<String, List<String>>
                boundedMutationFrontiersByOutput = new LinkedHashMap<>();
        private final Map<String, List<String>> localIncoming =
                new LinkedHashMap<>();
        private final Map<String, Map<String, List<String>>>
                explicitFatalSeedsBySite = new LinkedHashMap<>();
        private final Map<String, List<String>> fatalSeeds =
                new LinkedHashMap<>();
        /**
         * inputsForOutput is a pure function of the frozen index; the union
         * walk and every per-target closure walk repeat the same demands, so
         * each backward walk is computed once.  Cached lists are read-only
         * by contract of the callers.
         */
        private final Map<String, List<String>> inputsForOutputCache =
                new LinkedHashMap<>();
        private final Map<Map<String, Object>, List<String>>
                targetInputsCache = new java.util.IdentityHashMap<>();

        private RegionDemandIndex(
                List<Map<String, Object>> regions,
                List<Map<String, Object>> graph) {
            Set<String> selectedRegions = new LinkedHashSet<>();
            for (Map<String, Object> region : regions) {
                String regionId = text(region.get("regionId"));
                selectedRegions.add(regionId);
                for (Map<String, Object> input
                        : rows(region.get("symbolicInputs"))) {
                    indexPort(regionId, input, false);
                }
                for (Map<String, Object> output
                        : rows(region.get("outputs"))) {
                    indexPort(regionId, output, true);
                }
                for (Map<String, Object> branch
                        : rows(region.get("branchPolicies"))) {
                    if (Boolean.TRUE.equals(booleanValue(
                            branch.get("failureTarget")))) {
                        String site = text(branch.get("siteId"));
                        if (!site.isEmpty()) {
                            Map<String, List<String>> bySite =
                                    explicitFatalSeedsBySite.computeIfAbsent(
                                            regionId,
                                            ignored -> new LinkedHashMap<>());
                            List<String> seeds = bySite.computeIfAbsent(site,
                                    ignored -> new ArrayList<>());
                            for (String operand : strings(
                                    branch.get("operandCells"))) {
                                if (!seeds.contains(operand)) {
                                    seeds.add(operand);
                                }
                            }
                        }
                    }
                }
            }
            for (Map<String, Object> edge : graph) {
                String from = text(edge.get("fromCell"));
                String to = text(edge.get("toCell"));
                if (from.isEmpty() || to.isEmpty()) continue;
                for (String regionId : strings(edge.get("regionIds"))) {
                    if (!selectedRegions.contains(regionId)) continue;
                    addUnique(localIncoming, contextKey(regionId, to),
                            from);
                    // A generic exception cell is only a fallback for a
                    // region without an explicit failureTarget policy.  Once
                    // a target predicate is known, adding every exception in
                    // the template recreates the whole-region union that the
                    // runtime fatal-site evidence is meant to eliminate.
                    if (to.contains("#exception:")
                            && !explicitFatalSeedsBySite.containsKey(
                            regionId)) {
                        addUnique(fatalSeeds, regionId, to);
                    }
                }
            }
        }

        private void indexPort(String regionId, Map<String, Object> port,
                               boolean output) {
            String occurrenceId = portOccurrenceId(port, output);
            String portId = text(port.get("portId"));
            if (occurrenceId.isEmpty() || portId.isEmpty()) return;
            regionByOccurrence.putIfAbsent(occurrenceId, regionId);
            String demand = portDemandKey(occurrenceId, portId);
            (output ? outputs : inputs).put(demand, port);
            if (output) return;
            addUnique(inputsByInstance, occurrenceId, demand);
            boolean structuredCommunicationParent =
                    COMMUNICATION_SITE_PORT.equals(
                            text(port.get("sourceKind")))
                            && !DependencyRole.valueFrontier(
                            port.get("dependencyRole"));
            if (!structuredCommunicationParent) {
                for (String cell : boundaryCells(port)) {
                    addUnique(inputsByBoundary,
                            instanceCellKey(occurrenceId, cell), demand);
                }
            }
            for (String outputCell : strings(
                    port.get("boundedMutationOutputCells"))) {
                addUnique(boundedMutationFrontiersByOutput,
                        instanceCellKey(occurrenceId, outputCell), demand);
            }
        }

        private boolean hasInput(String occurrenceId, String portId) {
            return inputs.containsKey(portDemandKey(occurrenceId, portId));
        }

        private boolean hasOutput(String occurrenceId, String portId) {
            return outputs.containsKey(portDemandKey(occurrenceId, portId));
        }

        /**
         * Every declared communication input observed before one demanded
         * production in the same occurrence.  A distributed replay may
         * materialize several receiver instances or call sites; they remain
         * bounded guarded alternatives until the failure slice or a later
         * replay removes them.  No unique-cut inference is performed here.
         */
        private List<String> priorCommunicationInputs(
                String occurrenceId, long producedAt) {
            List<String> result = new ArrayList<>();
            for (String demand : inputsByInstance.getOrDefault(occurrenceId,
                    Collections.<String>emptyList())) {
                Map<String, Object> port = inputs.get(demand);
                if (port == null || !COMMUNICATION_SITE_PORT.equals(
                        text(port.get("sourceKind")))) {
                    continue;
                }
                long receivedAt = longNumber(port.get("eventSeq"), -1L);
                if (producedAt >= 0L && receivedAt >= producedAt) {
                    continue;
                }
                result.add(demand);
            }
            return result;
        }

        /**
         * Exact observed heap reads in this occurrence before one demanded
         * output was published.  A VM handoff component intentionally has no
         * static input projection; this occurrence-local ordering is what
         * lets the coarse producer retain the state it actually consulted
         * without claiming that the heap value equals the handed-off value.
         */
        private List<String> priorHeapValueInputs(
                String occurrenceId, long producedAt) {
            if (producedAt < 0L) return Collections.emptyList();
            List<String> result = new ArrayList<>();
            for (String demand : inputsByInstance.getOrDefault(occurrenceId,
                    Collections.<String>emptyList())) {
                Map<String, Object> port = inputs.get(demand);
                if (port == null
                        || !"HEAP".equals(text(port.get("transportKind")))
                        || !DependencyRole.valueFrontier(
                        port.get("dependencyRole"))
                        && !AutomaticRegionEdge
                        .TRANSPORTED_VALUE_FRONTIER_AUTHORITY.equals(text(
                        port.get(AutomaticRegionEdge
                                .TRANSPORTED_VALUE_FRONTIER_FIELD)))) {
                    continue;
                }
                boolean observedBefore = false;
                for (Map<String, Object> access
                        : rows(port.get("runtimeAccesses"))) {
                    long event = longNumber(access.get("eventSeq"), -1L);
                    if (event >= 0L && event < producedAt) {
                        observedBefore = true;
                        break;
                    }
                }
                if (observedBefore) result.add(demand);
            }
            return result;
        }

        private List<String> targetInputs(Map<String, Object> instance)
                throws IOException {
            List<String> cached = targetInputsCache.get(instance);
            if (cached != null) {
                return cached;
            }
            List<String> computed = computeTargetInputs(instance);
            targetInputsCache.put(instance, computed);
            return computed;
        }

        /**
         * Activation-local evidence that this activation reached one of the
         * explicit {@code failureTarget} sites of its region, grouped by site.
         *
         * <p>Returns an empty map when the region declares explicit failure
         * targets and this activation observed none of them.  The region's
         * static selection is deliberately not consulted: several concurrent
         * activations share one skeleton, but a branch site executes in the
         * activation that executed it.</p>
         */
        private Map<String, List<Map<String, Object>>> observedFatalEvidence(
                Map<String, Object> instance) {
            Map<String, List<Map<String, Object>>> evidenceBySite =
                    new LinkedHashMap<>();
            Map<String, List<String>> explicit = explicitFatalSeedsBySite.get(
                    text(instance.get("regionId")));
            if (explicit == null || explicit.isEmpty()) {
                return evidenceBySite;
            }
            for (Map<String, Object> evidence
                    : rows(instance.get("observedFatalTargets"))) {
                if (!"OBSERVED_FATAL_TARGET".equals(
                        text(evidence.get("kind")))
                        || !"EXACT_RUNTIME_BRANCH_SITE_V1".equals(
                        text(evidence.get("evidenceAuthority")))
                        || !(evidence.get("observedOutcome")
                        instanceof Boolean)) {
                    continue;
                }
                String site = text(evidence.get("siteId"));
                if (explicit.containsKey(site)) {
                    evidenceBySite.computeIfAbsent(site,
                            ignored -> new ArrayList<>()).add(evidence);
                }
            }
            return evidenceBySite;
        }

        /**
         * Whether this activation qualifies as an exception-context closure
         * target.  A region without an explicit {@code failureTarget} policy
         * has no per-activation site to attest, so its exception-context
         * activations stay targets under the generic exception-cell seeds
         * {@link #computeTargetInputs} falls back to.
         */
        private boolean observedExplicitFatalTarget(
                Map<String, Object> instance) {
            Map<String, List<String>> explicit = explicitFatalSeedsBySite.get(
                    text(instance.get("regionId")));
            return explicit == null || explicit.isEmpty()
                    || !observedFatalEvidence(instance).isEmpty();
        }

        private List<String> computeTargetInputs(
                Map<String, Object> instance) throws IOException {
            String regionId = text(instance.get("regionId"));
            String occurrenceId = text(instance.get("occurrenceId"));
            Map<String, List<String>> explicit =
                    explicitFatalSeedsBySite.get(regionId);
            if (explicit != null && !explicit.isEmpty()) {
                // Selection above already required this evidence; keeping the
                // check here keeps the slice fail-closed for any other caller.
                Map<String, List<Map<String, Object>>> evidenceBySite =
                        observedFatalEvidence(instance);
                if (evidenceBySite.isEmpty()) {
                    throw new IOException("exception-context activation did "
                            + "not observe its explicit fatal target branch: "
                            + occurrenceId);
                }
                Set<String> retained = new LinkedHashSet<>();
                List<Map<String, Object>> contexts = new ArrayList<>();
                for (Map.Entry<String, List<Map<String, Object>>> entry
                        : evidenceBySite.entrySet()) {
                    List<Map<String, Object>> occurrences = entry.getValue();
                    occurrences.sort(Comparator.comparingLong(value ->
                            longNumber(value.get("eventSeq"),
                                    Long.MAX_VALUE)));
                    int selectedIndex = selectedFatalOccurrence(occurrences);
                    Map<String, Object> selected = occurrences.get(
                            selectedIndex);
                    long cutoff = longNumber(selected.get("eventSeq"), -1L);
                    if (cutoff < 0L) {
                        throw new IOException("FATAL_PREFIX_EVIDENCE_GAP: "
                                + "observed fatal target has no eventSeq: "
                                + occurrenceId + " " + entry.getKey());
                    }
                    List<String> inputs = retainFatalPrefixInputs(instance,
                            backwardInputs(occurrenceId,
                                    explicit.get(entry.getKey())), cutoff);
                    retained.addAll(inputs);
                    Map<String, Object> context = new LinkedHashMap<>();
                    context.put("schemaVersion", 1);
                    context.put("authority",
                            "EXACT_FATAL_BRANCH_OCCURRENCE_PREFIX_V1");
                    context.put("siteId", entry.getKey());
                    context.put("occurrence", selectedIndex + 1);
                    context.put("eventSeq", cutoff);
                    context.put("observedOutcome",
                            selected.get("observedOutcome"));
                    if (selected.get("requiredOutcome") instanceof Boolean) {
                        context.put("requiredOutcome",
                                selected.get("requiredOutcome"));
                    }
                    List<String> ports = new ArrayList<>();
                    for (String demand : inputs) {
                        Map<String, Object> port = this.inputs.get(demand);
                        String portId = port == null ? ""
                                : text(port.get("portId"));
                        if (!portId.isEmpty()) ports.add(portId);
                    }
                    context.put("inputPorts", ports);
                    contexts.add(context);
                }
                instance.put("fatalPrefixContexts", contexts);
                return new ArrayList<>(retained);
            }
            List<String> seeds = fatalSeeds.getOrDefault(regionId,
                    Collections.<String>emptyList());
            if (seeds.isEmpty()) {
                // Small fixtures and locally terminal failures may not have
                // an explicit exception edge.  In that case the target is
                // still the analysis seed, so preserve its observed inputs.
                return new ArrayList<>(inputsByInstance.getOrDefault(
                        occurrenceId, Collections.<String>emptyList()));
            }
            return backwardInputs(occurrenceId, seeds);
        }

        /** Same occurrence rule as Scheduler.TargetBranch.select. */
        private int selectedFatalOccurrence(
                List<Map<String, Object>> occurrences) {
            int fallback = 0;
            for (int index = 0; index < occurrences.size(); index++) {
                Map<String, Object> occurrence = occurrences.get(index);
                Object required = occurrence.get("requiredOutcome");
                Object observed = occurrence.get("observedOutcome");
                if (required instanceof Boolean
                        && observed instanceof Boolean
                        && required.equals(observed)) {
                    return index;
                }
            }
            return fallback;
        }

        /**
         * A static backward slice says which boundary ports may feed the
         * fatal predicate; the exact trace says which of those ports existed
         * when that predicate was reached.  A value observed only after the
         * fatal branch cannot be one of its inputs and is therefore removed.
         * Missing ordering evidence is different: admitting that port would
         * create a free symbolic leaf, so it is a named, fail-closed gap.
         */
        private List<String> retainFatalPrefixInputs(
                Map<String, Object> instance, List<String> candidates,
                long fatalEventSeq) throws IOException {
            List<String> retained = new ArrayList<>();
            List<String> missingEvidence = new ArrayList<>();
            for (String demand : candidates) {
                Map<String, Object> port = inputs.get(demand);
                if (port == null) continue;
                // Structural owners remain concrete replay support.  They do
                // not become causal/symbolic leaves merely because their
                // construction has no independently timestamped value.
                if (!DependencyRole.valueFrontier(
                        port.get("dependencyRole"))) {
                    retained.add(demand);
                    continue;
                }
                FatalPrefixEvidence evidence = fatalPrefixEvidence(
                        port, fatalEventSeq);
                if (evidence.atOrBefore) {
                    retained.add(demand);
                } else if (!evidence.observedAfter) {
                    missingEvidence.add(text(port.get("portId")));
                }
            }
            if (!missingEvidence.isEmpty()) {
                throw new IOException("FATAL_PREFIX_EVIDENCE_GAP: target "
                        + text(instance.get("occurrenceId"))
                        + " has demanded ports without exact runtime order: "
                        + missingEvidence);
            }
            return retained;
        }

        private FatalPrefixEvidence fatalPrefixEvidence(
                Map<String, Object> port, long fatalEventSeq) {
            List<Map<String, Object>> accesses = rows(
                    port.get("runtimeAccesses"));
            if (!accesses.isEmpty()) {
                List<Map<String, Object>> prefix = new ArrayList<>();
                boolean observed = false;
                boolean after = false;
                for (Map<String, Object> access : accesses) {
                    long event = longNumber(access.get("eventSeq"), -1L);
                    if (event < 0L) continue;
                    observed = true;
                    if (event <= fatalEventSeq) {
                        prefix.add(access);
                    } else {
                        after = true;
                    }
                }
                if (!prefix.isEmpty()) {
                    return FatalPrefixEvidence.before();
                }
                if (observed && after) {
                    return FatalPrefixEvidence.after();
                }
                return FatalPrefixEvidence.missing();
            }
            // Accessor-return ports are emitted only from an exact runtime
            // binding and carry that occurrence directly on the port.  So do
            // the occurrence-owned copies of a declared cut port: their
            // order is the recorded leg that carried the value.
            if ("ACCESSOR_RETURN".equals(text(port.get("sourceKind")))
                    || COMMUNICATION_SITE_PORT.equals(
                    text(port.get("sourceKind")))) {
                long event = longNumber(port.get("eventSeq"), -1L);
                if (event < 0L) return FatalPrefixEvidence.missing();
                return event <= fatalEventSeq
                        ? FatalPrefixEvidence.before()
                        : FatalPrefixEvidence.after();
            }
            if (EXPLICIT_SYMBOLIC_FAULT.equals(
                    text(port.get("sourceKind")))) {
                long event = longNumber(port.get("eventSeq"), -1L);
                if (event < 0L) return FatalPrefixEvidence.missing();
                return event <= fatalEventSeq
                        ? FatalPrefixEvidence.before()
                        : FatalPrefixEvidence.after();
            }
            return FatalPrefixEvidence.missing();
        }

        private List<String> inputsForOutput(String occurrenceId,
                                             String portId,
                                             long writerEventSeq) {
            String demand = portDemandKey(occurrenceId, portId);
            String occurrenceDemand = outputOccurrenceDemandKey(demand,
                    writerEventSeq);
            List<String> cached = inputsForOutputCache.get(
                    occurrenceDemand);
            if (cached != null) {
                return cached;
            }
            List<String> computed = computeInputsForOutput(occurrenceId,
                    portId);
            inputsForOutputCache.put(occurrenceDemand, computed);
            return computed;
        }

        private List<String> computeInputsForOutput(String occurrenceId,
                                             String portId) {
            String demand = portDemandKey(occurrenceId, portId);
            Map<String, Object> output = outputs.get(demand);
            if (output == null) return Collections.emptyList();
            Set<String> result = new LinkedHashSet<>(backwardInputs(
                    occurrenceId, boundaryCells(output)));
            if ("CONTAINER_MUTATION".equals(
                    text(output.get("bindingKind")))) {
                for (String cell : mutationOutputCells(output)) {
                    result.addAll(boundedMutationFrontiersByOutput
                            .getOrDefault(instanceCellKey(occurrenceId, cell),
                                    Collections.<String>emptyList()));
                }
            }
            return new ArrayList<>(result);
        }

        /**
         * Walks the region's local dataflow backward from {@code seeds} to
         * the boundary ports of one activation.  The static region scope and
         * the dynamic occurrence are separate inputs: the incoming-cell graph
         * is shared by every activation of the region, while the boundary
         * index is occurrence-local.
         */
        private List<String> backwardInputs(String occurrenceId,
                                            Collection<String> seeds) {
            return backwardInputs(occurrenceId,
                    regionByOccurrence.getOrDefault(occurrenceId, ""), seeds);
        }

        /**
         * The same walk with the static scope named directly, for a caller
         * that knows the activation's region without needing it to have
         * already contributed a port to the index.
         */
        private List<String> backwardInputs(String occurrenceId,
                                            String regionId,
                                            Collection<String> seeds) {
            Set<String> result = new LinkedHashSet<>();
            Set<String> visited = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>(seeds);
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (cell.isEmpty() || !visited.add(cell)) continue;
                List<String> boundary = inputsByBoundary.getOrDefault(
                        instanceCellKey(occurrenceId, cell),
                        Collections.<String>emptyList());
                if (!boundary.isEmpty()) {
                    result.addAll(boundary);
                    continue;
                }
                work.addAll(localIncoming.getOrDefault(
                        contextKey(regionId, cell),
                        Collections.<String>emptyList()));
            }
            return new ArrayList<>(result);
        }

        private static List<String> boundaryCells(
                Map<String, Object> port) {
            List<String> result = strings(port.get("dependencyCells"));
            if (result.isEmpty()) {
                String cell = text(port.get("cell"));
                if (!cell.isEmpty()) result.add(cell);
            }
            // A declared server response is captured at the semantic
            // handler's normal return.  Communication-port declarations do
            // not duplicate that return in dependencyCells: the capture kind
            // and definition method are the canonical description of the
            // boundary.  Seed the ordinary local backward slice from that
            // cell so Resp_out retains the shared/container inputs that
            // actually built the response.  This is transport-generic; the
            // adapter only declares where the server boundary is.
            if (result.isEmpty()
                    && COMMUNICATION_SITE_PORT.equals(
                    text(port.get("sourceKind")))) {
                String cell = declaredCutPortCell(port);
                if (!cell.isEmpty()) result.add(cell);
            }
            return result;
        }

        private static String instanceCellKey(String occurrenceId,
                                              String cell) {
            return occurrenceId + "\nCELL\n" + cell;
        }

        private static void addUnique(Map<String, List<String>> target,
                                      String key, String value) {
            if (value.isEmpty()) return;
            List<String> values = target.computeIfAbsent(key,
                    ignored -> new ArrayList<>());
            if (!values.contains(value)) values.add(value);
        }

        private static final class FatalPrefixEvidence {
            private final boolean atOrBefore;
            private final boolean observedAfter;

            private FatalPrefixEvidence(boolean atOrBefore,
                                        boolean observedAfter) {
                this.atOrBefore = atOrBefore;
                this.observedAfter = observedAfter;
            }

            private static FatalPrefixEvidence before() {
                return new FatalPrefixEvidence(true, false);
            }

            private static FatalPrefixEvidence after() {
                return new FatalPrefixEvidence(false, true);
            }

            private static FatalPrefixEvidence missing() {
                return new FatalPrefixEvidence(false, false);
            }
        }
    }

    private static final class ContextCell {
        private final String region;
        private final String cell;

        private ContextCell(String region, String cell) {
            this.region = region;
            this.cell = cell;
        }
    }




    private static final class BoundPort {
        private final String region;
        private final String port;
        private final String sourceKey;
        /** Activation identity; the only activation discriminator here. */
        private final String occurrenceId;
        /** Recorded trace evidence republished on the emitted edge. */
        private final long rootCallId;
        private final int receiver;
        private final long seq;
        private final List<String> declarations;
        private final int valueObject;
        private final String primitiveValue;
        private final String bindingKind;
        private final long writerFieldReadSeq;
        private final long mutatorEnterSeq;
        private final long mutationCompletionSeq;
        private final long mutationInvocationId;
        private final String mutatorDeclaredCallee;
        private final String dependencyRole;
        private final String site;
        private final int occurrence;

        private BoundPort(String region, String port, String sourceKey,
                          String occurrenceId,
                          long rootCallId, int receiver, long seq,
                          List<String> declarations, int valueObject,
                          String primitiveValue, String bindingKind,
                          long writerFieldReadSeq, long mutatorEnterSeq,
                          long mutationCompletionSeq,
                          long mutationInvocationId,
                          String mutatorDeclaredCallee,
                          String dependencyRole, String site,
                          int occurrence) {
            this.region = region;
            this.port = port;
            this.sourceKey = sourceKey;
            this.occurrenceId = occurrenceId;
            this.rootCallId = rootCallId;
            this.receiver = receiver;
            this.seq = seq;
            this.declarations = declarations;
            this.valueObject = valueObject;
            this.primitiveValue = primitiveValue;
            this.bindingKind = bindingKind;
            this.writerFieldReadSeq = writerFieldReadSeq;
            this.mutatorEnterSeq = mutatorEnterSeq;
            this.mutationCompletionSeq = mutationCompletionSeq;
            this.mutationInvocationId = mutationInvocationId;
            this.mutatorDeclaredCallee = mutatorDeclaredCallee;
            this.dependencyRole = dependencyRole;
            this.site = site;
            this.occurrence = occurrence;
        }

        private String leafDeclaration() {
            return declarations.isEmpty() ? ""
                    : declarations.get(declarations.size() - 1);
        }
    }

    private static final class DeclaredFieldCell {
        private static final Set<String> PRIMITIVES = new LinkedHashSet<>(
                java.util.Arrays.asList("boolean", "byte", "short", "char",
                        "int", "long", "float", "double"));
        private final String owner;
        private final String type;
        private final String name;

        private DeclaredFieldCell(String owner, String type, String name) {
            this.owner = owner;
            this.type = type;
            this.name = name;
        }

        private boolean primitive() {
            return PRIMITIVES.contains(type);
        }

        /** Declaring class, which with the name is the cross-run identity. */
        private String owner() {
            return owner;
        }

        private static DeclaredFieldCell parse(String cell) {
            String value = text(cell).trim();
            if (!declaredField(value)) return null;
            int colon = value.indexOf(':');
            int separator = value.lastIndexOf(' ', value.length() - 2);
            if (colon < 1 || separator <= colon + 1) return null;
            String owner = value.substring(1, colon).trim();
            String type = value.substring(colon + 1, separator).trim();
            String name = value.substring(separator + 1,
                    value.length() - 1).trim();
            return type.isEmpty() || name.isEmpty() ? null
                    : new DeclaredFieldCell(owner, type, name);
        }
    }

    private static final class ClosureWalk {
        private final Set<String> reached;
        private final Set<String> retainedEdges;
        private final Set<String> demandedInputs;
        private final Set<String> demandedOutputs;

        private ClosureWalk(Set<String> reached, Set<String> retainedEdges,
                            Set<String> demandedInputs,
                            Set<String> demandedOutputs) {
            this.reached = reached;
            this.retainedEdges = retainedEdges;
            this.demandedInputs = demandedInputs;
            this.demandedOutputs = demandedOutputs;
        }
    }

    private static final class RuntimeClosure {
        private final Map<String, Map<String, Object>> instances;
        private final Set<String> reached;
        private final Set<String> retainedEdges;
        private final Set<String> demandedInputs;
        private final Set<String> demandedOutputs;

        private RuntimeClosure(
                Map<String, Map<String, Object>> instances,
                Set<String> reached,
                Set<String> retainedEdges,
                Set<String> demandedInputs,
                Set<String> demandedOutputs) {
            this.instances = instances;
            this.reached = reached;
            this.retainedEdges = retainedEdges;
            this.demandedInputs = demandedInputs;
            this.demandedOutputs = demandedOutputs;
        }
    }

    public static final class Result {
        /** Finalized region rows exactly as written to the artifact. */
        public final List<Map<String, Object>> regions;
        /** Canonicalized region edges exactly as written to the artifact. */
        public final List<Map<String, Object>> regionEdges;
        /**
         * Named gaps this stage could not stamp: an activation that carries
         * no registered logical source, and an observed protocol endpoint
         * whose activation identity did not resolve.  Both used to be silent
         * - a declared default source, and a dropped binding - which is the
         * implicit fallback README Step 4 replaces.
         */
        public final List<Map<String, Object>> gaps;

        private Result(List<Map<String, Object>> regions,
                       List<Map<String, Object>> regionEdges,
                       List<Map<String, Object>> gaps) {
            this.regions = regions;
            this.regionEdges = regionEdges;
            this.gaps = gaps;
        }
    }
}
