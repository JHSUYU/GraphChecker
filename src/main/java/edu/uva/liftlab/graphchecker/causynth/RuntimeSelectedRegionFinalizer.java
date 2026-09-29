package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.annotation.Debug;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.DeclaredSiteCapture;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.booleanValue;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.longNumber;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.number;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.firstNonEmpty;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.rows;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.strings;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

/** Builds executable region state exclusively from a runtime-refined graph. */
public final class RuntimeSelectedRegionFinalizer {
    private static final String REFINED_KIND = "RUNTIME_REFINED_DATAFLOW";

    /** A boolean returned by the explicit application-side fault marker. */
    public static final String EXPLICIT_SYMBOLIC_FAULT =
            "EXPLICIT_SYMBOLIC_FAULT";
    /** An unanalyzed primitive call return that reaches an explored branch. */
    public static final String EXTERNAL_CALL_RETURN =
            "EXTERNAL_CALL_RETURN";

    /**
     * Plan-row member: why a bounded state writer is in the plan when it is
     * there for anything other than reaching the fatal target.
     */
    public static final String ADMISSION_BASIS = "admissionBasis";
    private static final String SHARED_LOCATION_DEMAND_ADMISSION =
            "SHARED_LOCATION_DEMAND_V1";
    /**
     * Shared-location demand hops between this admission and the fatal target
     * (a writer the failure closure's own port demand asked for is one hop).
     * Published on the plan row because the retained edges cannot rebuild it.
     * It is the shortest chain that reached the admission, not the configured
     * bound: only {@code transitiveSharedLocationDemand} refuses a hop, so a
     * row deeper than the bound is a first-order admission, not a leak.
     */
    public static final String DEMAND_DEPTH = "demandDepth";
    /** The fatal target is the origin of every shared-location demand. */
    private static final int TARGET_DEMAND_DEPTH = 0;
    /**
     * {@code admissionBasis} of an activation carried because it read a
     * root ({@link StaticScopeMap#clockCallees}, a fault marker).
     */
    private static final String ROOT_READ_ADMISSION = "ROOT_READ_V1";
    /**
     * {@code admissionBasis} of an activation carried because its region
     * declares a communication capture.  Same rule as {@link
     * #ROOT_READ_ADMISSION}: nothing on this node demands an
     * export's outputs, so no demand-directed closure arrives on it, and an
     * export outside every instrumented activation has no decision prefix,
     * so its arm can never be attested.
     */
    private static final String DECLARED_COMMUNICATION_ADMISSION =
            "DECLARED_COMMUNICATION_CAPTURE_V1";
    /** Communication ports whose exact export/attach sites need hooks. */
    public static final String COMMUNICATION_PORTS = "communicationPorts";

    /** {@code IN} or {@code OUT}: which catalog a declared port belongs in. */
    public static final String REGION_PORT_SIDE = "regionPortSide";
    /** {@code sourceKind} of a port that carries a value across a call. */
    public static final String COMMUNICATION_SITE_PORT =
            "COMMUNICATION_SITE_PORT";
    /** Exact IN/OUT cut captures observed inside one runtime activation. */
    public static final String OBSERVED_COMMUNICATION_CAPTURES =
            "observedCommunicationCaptures";
    /** Region-row member carrying the retained loops of its methods. */
    public static final String RETAINED_LOOPS = "retainedLoops";
    /** Schema every region skeleton row and its refined row are stated in. */
    public static final int REGION_SCHEMA_VERSION = 3;
    /** {@code kind} of one planned region skeleton row. */
    public static final String SKELETON_KIND = "REGION_SKELETON";
    /** Activation member listing the root calls that share its address. */
    public static final String SHARED_ADDRESS_ROOT_CALLS =
            "sharedAddressRootCallIds";
    /**
     * Activation member: the regions whose roots FOLDED into this occurrence;
     * a region named here has no occurrence of its own in this plan.
     */
    public static final String FOLDED_REGION_IDS = "foldedRegionIds";
    /**
     * Activation member: this occurrence is the failure the case is about
     * (README TARGET-1).  Stated on the row because under the fold rule the
     * static {@code selection} names the region the failure is in, not the
     * occurrence that ran it.
     */
    public static final String FAILURE_TARGET_OCCURRENCE =
            "failureTargetOccurrence";

    private RuntimeSelectedRegionFinalizer() {
    }

    /**
     * Finalizes the selected runtime graph.  Symbolic values cross
     * occurrences only through VM VALUE_HANDOFF edges.
     */
    public static Result finalizeRegions(
            List<Map<String, Object>> graph,
            List<StaticProgram.RegionRow> selectedSkeletons,
            String skeletonSource, Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeObservations,
            StaticScopeMap scopeMap)
            throws IOException {
        Set<String> observed = new LinkedHashSet<>();
        if (observedMethods != null) {
            observed.addAll(observedMethods);
        }
        StaticProgram program = new StaticProgram();
        program.graph = graph;
        for (StaticProgram.RegionRow skeleton : selectedSkeletons) {
            program.skeletons.put(skeleton.regionId, skeleton);
        }

        List<Map<String, Object>> branchOrder = orderedBranchObservations(
                runtimeObservations);
        // Addresses several activations share; classed after the closure
        // (see #stateSharedAddressClasses).
        List<Map<String, Object>> sharedAddresses = new ArrayList<>();
        readOccurrences(program, runtimeInstances, skeletonSource,
                sharedAddresses);
        // The fold rule lifted to the region row: branch policies are stated
        // per region row, and a folded region has none of its own.
        Map<String, List<String>> foldedIntoRegion = new LinkedHashMap<>();
        for (Map<String, Object> activation : program.activations.values()) {
            List<String> held = foldedIntoRegion.computeIfAbsent(
                    text(activation.get("regionId")),
                    ignored -> new ArrayList<String>());
            for (String folded : strings(activation.get(FOLDED_REGION_IDS))) {
                if (!held.contains(folded)) held.add(folded);
            }
        }

        for (Map.Entry<String, StaticProgram.RegionRow> entry
                : program.skeletons.entrySet()) {
            String regionId = entry.getKey();
            StaticProgram.RegionRow skeleton = entry.getValue();
            if (!selectedRegion(skeleton, observed)) {
                continue;
            }
            Map<String, Object> region = new LinkedHashMap<>();
            region.put("schemaVersion", REGION_SCHEMA_VERSION);
            region.put("kind", "SYMBOLIC_REGION");
            region.put("graphKind", REFINED_KIND);
            region.put("regionId", regionId);
            region.put("rootMethod", skeleton.rootMethod);
            if (!skeleton.rootAuthority.isEmpty()) {
                region.put("rootAuthority", skeleton.rootAuthority);
            }
            // The once-only-root rule: a service loop's iteration, not the
            // one entry above it, is the activation this region describes.
            Map<String, Object> rootLoop = program.loopBodyRoot(skeleton,
                    program.regionActivations(regionId), branchOrder);
            if (rootLoop != null) {
                region.put("rootAuthority", LoopBoundPolicy.LOOP_BODY_ROOT);
                region.put(LoopBoundPolicy.ROOT_LOOP, rootLoop);
            }
            region.put("anchorMethod", skeleton.anchorMethod);
            if (skeleton.json.containsKey("anchorMethods")) {
                region.put("anchorMethods",
                        skeleton.json.get("anchorMethods"));
            }
            region.put("selection", skeleton.selection);
            List<String> foldedHere = foldedIntoRegion.getOrDefault(regionId,
                    Collections.<String>emptyList());
            // Declaration union: an occurrence owns the declarations of its
            // own region and of every region folded into it (as
            // ClosurePlanner#holds); every per-occurrence filter downstream
            // asks whether its region holds the site's method.
            region.put("methods", foldedUnion(program, skeleton, foldedHere,
                    row -> row.methods));
            // Carried over by name, unioned.
            for (String carried : new String[]{RETAINED_LOOPS,
                    StaticSymbolicSourceDeclaration.FIELD,
                    ConfiguredSourcePhaseContract.DECLARATION_FIELD}) {
                List<Map<String, Object>> declared = foldedUnion(program,
                        skeleton, foldedHere, row -> rows(row.json.get(
                                carried)));
                if (!declared.isEmpty()) region.put(carried, declared);
            }

            // Ports are the declared ones only: cut ports below, DECLARED_SITE
            // ports minted at PLAN.  Both catalogs are always published.
            region.put("symbolicInputs", new ArrayList<Map<String, Object>>());
            region.put("outputs", new ArrayList<Map<String, Object>>());
            region.put("branchPolicies", branches(foldedUnion(program,
                    skeleton, foldedHere,
                    row -> program.regionGraph(row.regionId))));
            program.regions.add(region);
        }
        bindObservedFatalTargets(program.regions, runtimeInstances,
                branchOrder);
        // applyClosure drops unreached regions; the declaration pass after
        // it restores their catalog rows.
        Map<String, List<CutPort>> cutPorts = declaredCutPorts(program);
        declareCommunicationPorts(program, cutPorts, foldedIntoRegion);
        // One index shared by the fatal-prefix pass and the closure walk.
        RegionDemandIndex demands = new RegionDemandIndex(program, scopeMap);
        applyClosure(program, failureDirectedClosure(program, demands,
                skeletonSource, scopeMap));
        // AFTER the closure: the class of a shared address is whether the
        // kept slice holds its region.
        stateSharedAddressClasses(program, sharedAddresses);
        // Declared last, and deliberately after the closure filter.
        declareCommunicationPorts(program, cutPorts, foldedIntoRegion);
        return new Result(program.regions, program.planGaps);
    }

    /** One declared cut port of one region, built once from its skeleton. */
    private static final class CutPort {
        private final String side;
        private final String portId;
        private final Map<String, Object> row;

        private CutPort(String side, String portId,
                        Map<String, Object> row) {
            this.side = side;
            this.portId = portId;
            this.row = row;
        }
    }

    /**
     * The cut ports every region declares, derived once so the catalog can
     * be republished after the closure filter drops it.
     */
    private static Map<String, List<CutPort>> declaredCutPorts(
            StaticProgram program) {
        Map<String, List<CutPort>> byRegion = new LinkedHashMap<>();
        for (StaticProgram.RegionRow skeleton : program.skeletons.values()) {
            List<CutPort> ports = new ArrayList<>();
            for (Map.Entry<String, List<Map<String, Object>>> side
                    : cutPortRows(skeleton, program.regionGraph(
                            skeleton.regionId)).entrySet()) {
                for (Map<String, Object> row : side.getValue()) {
                    ports.add(new CutPort(side.getKey(),
                            text(row.get("portId")), row));
                }
            }
            if (!ports.isEmpty()) byRegion.put(skeleton.regionId, ports);
        }
        return byRegion;
    }

    /**
     * One skeleton's declared cut-port rows by side ({@code IN}/{@code OUT}),
     * with the value cell the region graph names when it names exactly one.
     * Static, so a replay-exposed occurrence ({@code ExposedRegionPlanMain})
     * holds the same rows as a recorded one.
     */
    public static Map<String, List<Map<String, Object>>> cutPortRows(
            StaticProgram.RegionRow skeleton,
            List<Map<String, Object>> regionGraph) {
        Map<String, List<Map<String, Object>>> bySide = new LinkedHashMap<>();
        bySide.put("IN", new ArrayList<>());
        bySide.put("OUT", new ArrayList<>());
        for (Map<String, Object> port : skeleton.communicationPorts) {
            String portId = text(port.get("portId"));
            String side = text(port.get(REGION_PORT_SIDE));
            if (portId.isEmpty() || !bySide.containsKey(side)) {
                continue;
            }
            Map<String, Object> row = new LinkedHashMap<>(port);
            row.remove(REGION_PORT_SIDE);
            Set<String> cells = callReturnValueCells(regionGraph, row);
            if (cells.size() == 1) {
                row.put("dependencyCells", new ArrayList<>(cells));
            }
            bySide.get(side).add(row);
        }
        return bySide;
    }

    /**
     * Publishes the ports of every cut this region holds a side of: its own
     * and those of every region FOLDED into its occurrences, since a folded
     * region has no plan row and the occurrence that ran its export or attach
     * is the only one that can hold that side.
     */
    private static void declareCommunicationPorts(StaticProgram program,
            Map<String, List<CutPort>> declaredByRegion,
            Map<String, List<String>> foldedIntoRegion) {
        for (Map<String, Object> region : program.regions) {
            String regionId = text(region.get("regionId"));
            List<CutPort> declared = new ArrayList<>();
            for (String performed : performedRegionIds(regionId,
                    foldedIntoRegion.getOrDefault(regionId,
                            Collections.<String>emptyList()))) {
                List<CutPort> held = declaredByRegion.get(performed);
                if (held != null) declared.addAll(held);
            }
            if (declared.isEmpty()) {
                continue;
            }
            List<Map<String, Object>> inputs = rows(
                    region.get("symbolicInputs"));
            List<Map<String, Object>> outputs = rows(region.get("outputs"));
            // A cut has one region-level declaration and zero or more
            // occurrence-owned instances of that declaration.
            Set<String> inputIds = declaredPortIds(inputs);
            Set<String> outputIds = declaredPortIds(outputs);
            for (CutPort port : declared) {
                if ("IN".equals(port.side)) {
                    if (inputIds.add(port.portId)) {
                        inputs.add(new LinkedHashMap<>(port.row));
                    }
                } else if ("OUT".equals(port.side)) {
                    if (outputIds.add(port.portId)) {
                        outputs.add(new LinkedHashMap<>(port.row));
                    }
                }
            }
            region.put("symbolicInputs", inputs);
            region.put("outputs", outputs);
        }
    }

    /** The value cell one declared cut port's capture names, or {@code ""}. */
    public static String declaredCutPortCell(Map<String, Object> port) {
        String capture = text(port.get(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        String definitionMethod = text(port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        String javaType = text(port.get("javaType"));
        if (CommunicationCatalogContract.CAPTURE_METHOD_PARAMETER.equals(
                capture)) {
            int argumentIndex = (int) longNumber(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1L);
            return definitionMethod.isEmpty() || javaType.isEmpty()
                    || argumentIndex < 0 ? ""
                    : definitionMethod + ".param" + argumentIndex + ":"
                    + javaType;
        }
        if (CommunicationCatalogContract.CAPTURE_METHOD_RETURN.equals(
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
            // The cut argument is never written to the heap; only the callee
            // parameter it binds to at the cut unit names it.
            int argumentIndex = (int) longNumber(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1L);
            return callee.isEmpty() || javaType.isEmpty()
                    || argumentIndex < 0 ? ""
                    : callee + ".param" + argumentIndex + ":" + javaType;
        }
        return "";
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
     * The node this activation ran on, read from its occurrence address (not
     * the trace rows).  Every activation has one, so a non-address throws.
     */
    private static String activationSourceKey(Map<String, Object> instance) {
        return OccurrenceAddress.parse(text(instance.get("occurrenceId")))
                .node().render();
    }

    /**
     * Reads the occurrence address of every observed region activation and
     * stamps it onto every row the recorded root call named.
     *
     * <p>READS, never re-derives: the address is {@code Identity.occurrence}'s,
     * computed once at the recording and identically at replay; an offline
     * derivation would be a second identity (REPORT-M2 §5).  Activations
     * IDENTITY-V3 cannot separate may share one address; one occurrence is
     * one plan row (README REGION-1), so only the first is published, and
     * renumbering would reintroduce an ordinal.  The collision is classed
     * after the closure walk ({@link #stateSharedAddressClasses}).</p>
     *
     * @param sharedAddresses collects one row per shared address: its
     *     {@code occurrenceId}, {@code regionId} and root calls
     */
    private static void readOccurrences(
            StaticProgram program,
            Collection<Map<String, Object>> runtimeInstances,
            String source,
            List<Map<String, Object>> sharedAddresses) throws IOException {
        Map<String, List<Long>> rootCallsByAddress = new LinkedHashMap<>();
        for (Map<String, Object> instance : canonicalRuntimeActivations(
                runtimeInstances, source)) {
            String regionId = text(instance.get("regionId"));
            long rootCallId = longNumber(instance.get("rootCallId"), -1L);
            String occurrenceId = text(instance.get("occurrenceAddress"));
            if (occurrenceId.isEmpty()) {
                throw new IOException("runtime region activation states no "
                        + "occurrence address, so the recording computed "
                        + "none for it: " + regionId + "\n" + rootCallId);
            }
            instance.put("occurrenceId", occurrenceId);
            rootCallsByAddress.computeIfAbsent(occurrenceId,
                    ignored -> new ArrayList<>()).add(rootCallId);
            program.activations.putIfAbsent(occurrenceId, instance);
        }
        for (Map.Entry<String, List<Long>> entry
                : rootCallsByAddress.entrySet()) {
            if (entry.getValue().size() < 2) continue;
            Map<String, Object> activation =
                    program.activations.get(entry.getKey());
            activation.put(SHARED_ADDRESS_ROOT_CALLS, entry.getValue());
            Map<String, Object> shared = new LinkedHashMap<>();
            shared.put("occurrenceId", entry.getKey());
            shared.put("regionId", text(activation.get("regionId")));
            shared.put(SHARED_ADDRESS_ROOT_CALLS, entry.getValue());
            sharedAddresses.add(shared);
        }
    }

    /**
     * States the class of every shared occurrence address (CONTRACT-SPEC SS2).
     * BLOCKING when the region is in the closure this plan publishes ({@code
     * program.regions} after {@link #applyClosure}): a task addresses the
     * occurrence.  DIAGNOSTIC otherwise: no plan row, task or session row
     * names it.  Trap: an unstated class reads as BLOCKING downstream
     * ({@code campaign_write_gaps}).
     */
    private static void stateSharedAddressClasses(StaticProgram program,
            List<Map<String, Object>> sharedAddresses) {
        Set<String> kept = new LinkedHashSet<>();
        for (Map<String, Object> region : program.regions) {
            kept.add(text(region.get("regionId")));
        }
        for (Map<String, Object> shared : sharedAddresses) {
            String regionId = text(shared.get("regionId"));
            boolean member = kept.contains(regionId);
            Object rootCalls = shared.get(SHARED_ADDRESS_ROOT_CALLS);
            int count = rootCalls instanceof Collection
                    ? ((Collection<?>) rootCalls).size() : 0;
            planGap(program.planGaps, GapKind.OCCURRENCE_ADDRESS_SHARED,
                    member ? GapClass.BLOCKING : GapClass.DIAGNOSTIC,
                    text(shared.get("occurrenceId")),
                    count + " activations of this region share one address: "
                            + "nothing IDENTITY-V3 names distinguishes them "
                            + "(same node, causal context and execution "
                            + "index); recorded root calls " + rootCalls
                            + "; one occurrence is one plan row, so only the "
                            + "first is published"
                            + (member
                            ? "; BLOCKING: " + regionId + " is a member of "
                            + "the closure this plan publishes, so a task "
                            + "addresses this occurrence and no claim may be "
                            + "made over it"
                            : "; DIAGNOSTIC: " + regionId + " is not a "
                            + "member of the closure this plan publishes, so "
                            + "no plan row, no task and no session row names "
                            + "this occurrence and no composition can rest "
                            + "on it"));
        }
    }

    /** Canonical activation records at the trace-aggregation boundary. */
    private static List<Map<String, Object>> canonicalRuntimeActivations(
            Collection<Map<String, Object>> runtimeInstances, String source)
            throws IOException {
        Map<String, Map<String, Object>> byRecordedActivation =
                new LinkedHashMap<>();
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
            Map<String, Object> previous = byRecordedActivation.putIfAbsent(
                    regionId + "\n" + rootCallId, instance);
            if (previous != null && !previous.equals(instance)) {
                throw new IOException("conflicting runtime region activation "
                        + "payload: " + regionId + "\n" + rootCallId);
            }
        }
        return new ArrayList<>(byRecordedActivation.values());
    }

    /** True when this skeleton's methods were observed in the trace. */
    private static boolean selectedRegion(StaticProgram.RegionRow skeleton,
                                          Set<String> observed) {
        return !skeleton.methods.isEmpty()
                && (observed.isEmpty()
                || !Collections.disjoint(skeleton.methods, observed));
    }

    /** Branch member: the exception cells a failure-target guard controls. */
    public static final String FAILURE_TARGET_CELLS = "failureTargetCells";

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
        sortByEventSeq(observations);
        return observations;
    }

    /**
     * Adds activation-local fatal-target evidence by intersecting exact
     * runtime BRANCH sites with static {@code failureTarget} branch policies.
     */
    private static void bindObservedFatalTargets(
            List<Map<String, Object>> regions,
            Collection<Map<String, Object>> runtimeInstances,
            List<Map<String, Object>> observations) {
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

        for (Map<String, Object> instance : runtimeInstances) {
            // Over every region this occurrence PERFORMED: a folded region's
            // target site was reached here and only here.
            Map<String, Map<String, Object>> regionTargets =
                    new LinkedHashMap<>();
            for (String regionId : performedRegionIds(instance)) {
                Map<String, Map<String, Object>> held = targets.get(regionId);
                if (held != null) regionTargets.putAll(held);
            }
            if (regionTargets.isEmpty()) continue;

            Set<Long> calls = MapFields.longValues(
                    instance.get("callIds"));
            List<Map<String, Object>> bound = rows(
                    instance.get("observedFatalTargets"));
            for (Map<String, Object> observation : observations) {
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
                evidence.put("observedOutcome", observation.get("outcome"));
                evidence.put("eventSeq", observation.get("eventSeq"));
                evidence.put("callId", callId);
                bound.add(evidence);
            }
            if (!bound.isEmpty()) {
                sortByEventSeq(bound);
                instance.put("observedFatalTargets", bound);
            }
        }
    }

    private static boolean isExceptionTargetEdge(Map<String, Object> edge) {
        return "exception_guard".equals(text(edge.get("kind")))
                || text(edge.get("toCell")).contains("#exception:");
    }

    /**
     * The regions performed under one region: its own first, then those
     * folded into it ({@code Identity#fold}), whose text ran there.  A list:
     * plan order.
     */
    private static List<String> performedRegionIds(
            String own, Collection<String> folded) {
        List<String> performed = new ArrayList<>();
        if (!own.isEmpty()) performed.add(own);
        for (String regionId : folded) {
            if (!regionId.isEmpty() && !performed.contains(regionId)) {
                performed.add(regionId);
            }
        }
        return performed;
    }

    /** The regions one occurrence PERFORMED. */
    private static List<String> performedRegionIds(
            Map<String, Object> activation) {
        return performedRegionIds(text(activation.get("regionId")),
                strings(activation.get(FOLDED_REGION_IDS)));
    }

    /**
     * The activations the failure's demand reaches, from two authorities
     * only: the DECLARATIONS (symbolic inputs, communication mappings, the
     * annotated target) and the static scope map, which names the regions
     * storing a location, never the writer ({@link
     * StaticScopeMap#writerRegionsByCell}, CLOSURE-V2 SS4).  Nothing is
     * discovered from recorded field accesses: an undeclared read mints no
     * symbol ({@code ConcolicScheduler.SymbolicInputSelection}).
     *
     * @return the occurrences the demand reached
     */
    private static Set<String> failureDirectedClosure(
            StaticProgram program, RegionDemandIndex demands, String source,
            StaticScopeMap scopeMap)
            throws IOException {
        Map<String, Map<String, Object>> instances = program.activations;
        if (instances.isEmpty()) {
            throw new IOException("runtime failure closure requires concrete "
                    + "region activations: " + source);
        }
        // Every activation of an exception-context region inherits its
        // skeleton's `selection`, and so does every occurrence such a region
        // FOLDED into: the failure happened there and nowhere else.
        Set<String> contexts = new LinkedHashSet<>();
        Set<String> targets = new LinkedHashSet<>();
        Set<String> policylessRegions = new LinkedHashSet<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : program.activations.entrySet()) {
            String context = exceptionContextRegion(program,
                    entry.getValue());
            if (context.isEmpty()) {
                continue;
            }
            contexts.add(entry.getKey());
            if (!demands.declaresExplicitFatalTarget(entry.getValue())) {
                policylessRegions.add(context);
            } else if (demands.observedExplicitFatalTarget(
                    entry.getValue())) {
                targets.add(entry.getKey());
            }
        }
        if (contexts.isEmpty()) {
            throw new IOException("runtime failure closure found no observed "
                    + "exception-context activation: " + source);
        }
        if (targets.isEmpty() && !policylessRegions.isEmpty()) {
            // README TARGET-1: target existence binds to a selected concrete
            // branch event.
            throw new IOException("FATAL_TARGET_POLICY_ABSENT: "
                    + "exception-context region declares no failure target "
                    + "site to bind the target to: " + policylessRegions
                    + " " + source);
        }
        if (targets.isEmpty()) {
            // A workload that never reached the declared failure site has no
            // failure to explain.
            throw new IOException("FATAL_TARGET_OBSERVATION_GAP: no "
                    + "exception-context activation observed its explicit "
                    + "fatal target branch: " + source);
        }
        // Hop count per admitted occurrence, seeded on the fatal target(s).
        Map<String, Integer> demandDepths = new LinkedHashMap<>();
        for (String target : targets) {
            demandDepths.put(target, TARGET_DEMAND_DEPTH);
            // Stated once here; the plan builder publishes TARGET_REACH for
            // exactly these and does not re-ask the static selection.
            instances.get(target).put(FAILURE_TARGET_OCCURRENCE, true);
        }
        // Occurrences that read a root (a clock, a fault marker), admitted
        // although nothing demands their outputs: a root often decides an arm
        // that writes nothing (an expiry check that removes nothing), and a
        // clock's value may leave by a wire the walk does not follow back
        // (hdfs-11741's key-rotation tick).  Their DECLARED_SITE captures
        // seed the walk.
        Set<String> clockCallees = scopeMap.clockCallees();
        Set<String> declaredInputOccurrences = new LinkedHashSet<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : instances.entrySet()) {
            if (readsARoot(entry.getValue(), clockCallees)) {
                declaredInputOccurrences.add(entry.getKey());
            }
        }
        // A target is already the walk's origin and states no admissionBasis.
        declaredInputOccurrences.removeAll(targets);
        // Occurrences that PERFORMED a declared communication capture (see
        // DECLARED_COMMUNICATION_ADMISSION), over every region they
        // performed.  Only those whose recording states a capture or attach:
        // admitting every activation of a port-declaring region blows the
        // task cap.
        Set<String> declaredCaptureOccurrences = new LinkedHashSet<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : instances.entrySet()) {
            boolean declaresACut = false;
            boolean attached = false;
            for (String regionId : performedRegionIds(entry.getValue())) {
                StaticProgram.RegionRow skeleton = program.skeletons.get(
                        regionId);
                if (skeleton == null
                        || skeleton.communicationPorts.isEmpty()) {
                    continue;
                }
                declaresACut = true;
                attached = attached || attachedADeclaredPort(skeleton,
                        entry.getValue());
            }
            if (!declaresACut) {
                continue;
            }
            if (rows(entry.getValue().get(
                    OBSERVED_COMMUNICATION_CAPTURES)).isEmpty()
                    && !attached) {
                continue;
            }
            declaredCaptureOccurrences.add(entry.getKey());
        }
        declaredCaptureOccurrences.removeAll(targets);

        Set<String> declaredOccurrences =
                new LinkedHashSet<>(declaredInputOccurrences);
        declaredOccurrences.addAll(declaredCaptureOccurrences);
        for (String occurrence : declaredOccurrences) {
            recordDemandDepth(demandDepths, occurrence, 1);
        }

        Set<String> reached = walkFailureClosure(targets, program, demands,
                scopeMap, declaredOccurrences, demandDepths);
        // Restated after the walk, so a writer the walk reached twice
        // publishes the shortest chain that reached it.
        for (String occurrence : reached) {
            Map<String, Object> activation = instances.get(occurrence);
            if (SHARED_LOCATION_DEMAND_ADMISSION.equals(
                    text(activation.get(ADMISSION_BASIS)))) {
                activation.put(DEMAND_DEPTH,
                        demandDepth(demandDepths, occurrence));
            }
        }
        // Stated after the walk, and only where no rule above has stated
        // one: a declared occurrence the location demand also reached keeps
        // that basis, which carries the demand depth the scheduler reads.
        stateAdmissionBasis(instances, declaredInputOccurrences,
                ROOT_READ_ADMISSION);
        stateAdmissionBasis(instances, declaredCaptureOccurrences,
                DECLARED_COMMUNICATION_ADMISSION);
        return reached;
    }

    /** States {@code basis} on each occurrence that states none yet. */
    private static void stateAdmissionBasis(
            Map<String, Map<String, Object>> instances,
            Collection<String> occurrences, String basis) {
        for (String occurrence : occurrences) {
            Map<String, Object> activation = instances.get(occurrence);
            if (text(activation.get(ADMISSION_BASIS)).isEmpty()) {
                activation.put(ADMISSION_BASIS, basis);
            }
        }
    }

    /**
     * Hop count of one admitted occurrence.  An unknown one was reached on the
     * closure's own authority (fault, communication, protocol producer) and
     * counts as one hop.
     */
    private static int demandDepth(Map<String, Integer> demandDepths,
                                   String occurrenceId) {
        Integer known = demandDepths.get(occurrenceId);
        return known == null ? 1 : known;
    }

    /** Records the shortest demand chain that reached one admission. */
    private static void recordDemandDepth(
            Map<String, Integer> demandDepths, String occurrenceId,
            int depth) {
        Integer known = demandDepths.get(occurrenceId);
        if (known == null || depth < known) {
            demandDepths.put(occurrenceId, depth);
        }
    }

    /**
     * One backward walk over the candidate graph from the failure's demand
     * and every declaration; a demand is one cell of one occurrence.  Inside
     * an occurrence the walk follows the candidate graph; at a cell the scope
     * map names as stored it crosses to the activations of the storing
     * regions on the same node (heap is node-private), while the read's
     * guards still travel locally.  Which of them wrote the value is not
     * decided here: each is a replay arm, and the VM's GuardedRead chooses.
     */
    private static Set<String> walkFailureClosure(
            Collection<String> targets,
            StaticProgram program,
            RegionDemandIndex demands,
            StaticScopeMap scopeMap,
            Set<String> declaredOccurrences,
            Map<String, Integer> demandDepths)
            throws IOException {
        Map<String, Map<String, Object>> instances = program.activations;
        Map<String, List<StaticScopeMap.Site>> writeSites =
                scopeMap.writeSitesByCell();
        Set<String> reached = new LinkedHashSet<>(targets);
        reached.addAll(declaredOccurrences);
        List<String> seeds = new ArrayList<>();
        for (String target : targets) {
            for (String cell : demands.targetSeedCells(instances.get(target))) {
                seeds.add(cellDemand(target, cell));
            }
        }
        for (String occurrence : declaredOccurrences) {
            for (String cell : declaredCells(instances.get(occurrence),
                    scopeMap)) {
                seeds.add(cellDemand(occurrence, cell));
            }
        }
        List<IOException> refused = new ArrayList<>();
        StaticProgram.closure(seeds, demand -> {
            int split = demand.indexOf('\n');
            String occurrenceId = demand.substring(0, split);
            String cell = demand.substring(split + 1);
            List<String> next = new ArrayList<>();
            List<StaticScopeMap.Site> writers = writeSites.get(cell);
            if (writers == null || writers.isEmpty()) {
                for (String from : demands.incomingCells(occurrenceId, cell)) {
                    next.add(cellDemand(occurrenceId, from));
                }
                return next;
            }
            String node = activationSourceKey(instances.get(occurrenceId));
            for (StaticScopeMap.Site site : writers) {
                String storingMethod = SiteId.methodOf(site.siteId);
                for (Map<String, Object> writer
                        : program.regionActivations(site.regionId)) {
                    String writerOccurrence = text(
                            writer.get("occurrenceId"));
                    if (writerOccurrence.isEmpty()
                            || writerOccurrence.equals(occurrenceId)
                            || !node.equals(activationSourceKey(writer))
                            || !strings(writer.get("observedMethods"))
                            .contains(storingMethod)) {
                        continue;
                    }
                    recordDemandDepth(demandDepths, writerOccurrence,
                            demandDepth(demandDepths, occurrenceId) + 1);
                    if (reached.add(writerOccurrence)) {
                        String basis = text(writer.get(ADMISSION_BASIS));
                        if (!basis.isEmpty() && !SHARED_LOCATION_DEMAND_ADMISSION
                                .equals(basis)) {
                            refused.add(new IOException("conflicting runtime "
                                    + "activation admission basis for "
                                    + writerOccurrence + ": " + basis));
                            return null;
                        }
                        writer.put(ADMISSION_BASIS,
                                SHARED_LOCATION_DEMAND_ADMISSION);
                    }
                    next.add(cellDemand(writerOccurrence, cell));
                }
            }
            // A stored location stops value provenance inside this
            // occurrence, but not the guard deciding whether the read runs.
            for (String guard : demands.guardCells(occurrenceId, cell)) {
                next.add(cellDemand(occurrenceId, guard));
            }
            return next;
        });
        if (!refused.isEmpty()) throw refused.get(0);
        return reached;
    }

    /**
     * Whether this activation read a root: called a clock, or the {@code
     * Debug.makeSymbolicBoolean} marker.  A root's every read is an input,
     * so the reading activation holds it whatever the demand reaches.
     */
    private static boolean readsARoot(
            Map<String, Object> activation, Set<String> clockCallees) {
        for (Map<String, Object> capture
                : rows(activation.get(DeclaredSiteCapture.PLAN_FIELD))) {
            String callee = text(capture.get(
                    DeclaredSiteCapture.DECLARED_CALLEE));
            if (clockCallees.contains(callee)
                    || Debug.isBooleanMarkerSignature(callee)) {
                return true;
            }
        }
        return false;
    }

    /**
     * One catalog of this region unioned with its folded regions', own first
     * and deduplicated whole: a folded region's text ran in this region's
     * occurrences, and the enclosing skeleton does not name it (the weave
     * stops at a nested root).
     */
    private static <T> List<T> foldedUnion(
            StaticProgram program, StaticProgram.RegionRow skeleton,
            List<String> foldedRegionIds,
            Function<StaticProgram.RegionRow, Collection<T>> catalog) {
        List<T> union = new ArrayList<>(catalog.apply(skeleton));
        for (String folded : foldedRegionIds) {
            StaticProgram.RegionRow row = program.skeletons.get(folded);
            if (row == null) continue;
            for (T item : catalog.apply(row)) {
                if (!union.contains(item)) union.add(item);
            }
        }
        return union;
    }

    /**
     * The EXCEPTION-context region this occurrence ran, or {@code ""}: its
     * own, else the first folded one (read off its SKELETON, a fold having
     * no activation to inherit the selection onto).
     */
    private static String exceptionContextRegion(
            StaticProgram program, Map<String, Object> activation) {
        if (text(activation.get("selection")).startsWith("EXCEPTION")) {
            return text(activation.get("regionId"));
        }
        for (String regionId : strings(activation.get(FOLDED_REGION_IDS))) {
            StaticProgram.RegionRow folded = program.skeletons.get(regionId);
            if (folded != null && folded.selection.startsWith("EXCEPTION")) {
                return regionId;
            }
        }
        return "";
    }

    /**
     * Whether this activation TOOK a declared IN cut value its region
     * attaches.  {@link #OBSERVED_COMMUNICATION_CAPTURES} covers the capture
     * site's own frame; the declared consumer frame ({@code frameMethod}) is
     * a region one level out that attaches the value into the object it
     * returns, so it is asked whether it holds a DECLARED_SITE capture at
     * the port's call site and callee.
     */
    private static boolean attachedADeclaredPort(
            StaticProgram.RegionRow skeleton,
            Map<String, Object> activation) {
        List<Map<String, Object>> captures = rows(
                activation.get(DeclaredSiteCapture.PLAN_FIELD));
        if (captures.isEmpty()) return false;
        for (Map<String, Object> port : skeleton.communicationPorts) {
            if (!"IN".equals(text(port.get(REGION_PORT_SIDE)))
                    || !CommunicationCatalogContract.CAPTURE_CALL_RETURN
                    .equals(text(port.get(CommunicationCatalogContract
                            .PORT_OUTPUT_CAPTURE_KIND)))) {
                continue;
            }
            String site = text(port.get(
                    CommunicationCatalogContract.CALL_SITE_ID));
            String callee = text(port.get(
                    CommunicationCatalogContract.DECLARED_CALLEE));
            if (site.isEmpty() || callee.isEmpty()) continue;
            for (Map<String, Object> capture : captures) {
                if (site.equals(text(capture.get(SiteId.MEMBER)))
                        && callee.equals(text(capture.get(
                        DeclaredSiteCapture.DECLARED_CALLEE)))) {
                    return true;
                }
            }
        }
        return false;
    }

    /** One demand: the cell, inside the occurrence that reads it. */
    private static String cellDemand(String occurrenceId, String cell) {
        return occurrenceId + "\n" + cell;
    }

    /**
     * The cells one activation's DECLARED sites name: the scope map's
     * {@code DECLARED_SITE#cell}, for the sites the recording captured.
     */
    private static List<String> declaredCells(Map<String, Object> activation,
                                              StaticScopeMap scopeMap) {
        List<String> cells = new ArrayList<>();
        for (Map<String, Object> capture
                : rows(activation.get(DeclaredSiteCapture.PLAN_FIELD))) {
            for (StaticScopeMap.Site site : scopeMap.declaredSitesAt(
                    text(capture.get(SiteId.MEMBER)),
                    text(capture.get(DeclaredSiteCapture.DECLARED_CALLEE)))) {
                if (!site.cell.isEmpty() && !cells.contains(site.cell)) {
                    cells.add(site.cell);
                }
            }
        }
        return cells;
    }

    /**
     * Keeps the regions the walk reached and names their retained
     * activations.  Port catalogs are cleared here and re-declared after.
     */
    private static void applyClosure(StaticProgram program,
                                     Set<String> reached) {
        Set<String> retainedRegions = new LinkedHashSet<>();
        for (String key : reached) {
            retainedRegions.add(text(program.activations.get(key).get(
                    "regionId")));
        }
        program.regions.removeIf(region -> !retainedRegions.contains(
                text(region.get("regionId"))));
        for (Map<String, Object> region : program.regions) {
            String regionId = text(region.get("regionId"));
            Set<String> occurrences = new LinkedHashSet<>();
            for (String key : reached) {
                Map<String, Object> instance = program.activations.get(key);
                if (!regionId.equals(text(instance.get("regionId")))) {
                    continue;
                }
                occurrences.add(key);
            }
            // The activations this closure retained, named by identity.
            region.put("runtimeOccurrenceIds",
                    new ArrayList<>(occurrences));
            region.put("symbolicInputs", new ArrayList<Map<String, Object>>());
            region.put("outputs", new ArrayList<Map<String, Object>>());
        }
    }

    /** Caller locals assigned by one declared application call return. */
    private static Set<String> callReturnValueCells(
            Collection<Map<String, Object>> edges,
            Map<String, Object> port) {
        Set<String> cells = new LinkedHashSet<>();
        if (!CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(
                text(port.get(CommunicationCatalogContract
                        .PORT_OUTPUT_CAPTURE_KIND)))) return cells;
        String returned = text(port.get(CommunicationCatalogContract
                .DECLARED_CALLEE)) + ".return";
        for (Map<String, Object> edge : edges) {
            if ("call_return".equals(text(edge.get("kind")))
                    && text(port.get(CommunicationCatalogContract
                    .PORT_DEFINITION_METHOD)).equals(text(edge.get("method")))
                    && text(port.get(CommunicationCatalogContract
                    .CALL_SITE_ID)).equals(text(edge.get("siteId")))
                    && returned.equals(text(edge.get("fromCell")))) {
                cells.add(text(edge.get("toCell")));
            }
        }
        cells.remove("");
        return cells;
    }

    /**
     * The region's branch catalog: which conditional sites the slice reaches
     * and which cells decide them, over its own text and that of every region
     * folded into its occurrences (a folded region has no row of its own).
     * No policy and no guard set: every decision with a symbolic operand is
     * recorded (LEAN section 1), and guard sets are {@code
     * static_scope_map}'s ({@link SiteControlDependence}).
     */
    private static List<Map<String, Object>> branches(
            List<Map<String, Object>> edges) {
        Map<String, List<Map<String, Object>>> bySite = guardsBySite(edges);
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
                if (isExceptionTargetEdge(guard)) failureGuards.add(guard);
            }
            Collection<Map<String, Object>> decisiveGuards =
                    failureGuards.isEmpty() ? guards : failureGuards;
            branch.put("failureTarget", !failureGuards.isEmpty());
            // Which throw this guard controls, not merely that it controls one.
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
            result.add(branch);
        }
        return result;
    }

    /** Guard rows by the site they decide, in first-seen order. */
    private static Map<String, List<Map<String, Object>>> guardsBySite(
            Collection<Map<String, Object>> edges) {
        Map<String, List<Map<String, Object>>> bySite = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"GUARD".equals(text(edge.get("transferKind")))) continue;
            String site = firstNonEmpty(text(edge.get("guardSiteId")),
                    text(edge.get("siteId")));
            if (site.isEmpty()) continue;
            bySite.computeIfAbsent(site, ignored -> new ArrayList<>())
                    .add(edge);
        }
        return bySite;
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

    private static String contextKey(String region, String cell) {
        return region + "\n" + cell;
    }

    /**
     * Records one finalizer gap once per (kind, subject), stating its own
     * class like a {@link edu.uva.liftlab.graphchecker.contract.GapRow}.
     */
    private static void planGap(List<Map<String, Object>> gaps, GapKind kind,
                                GapClass cls, String subject, String detail) {
        for (Map<String, Object> existing : gaps) {
            if (kind.name().equals(text(existing.get("kind")))
                    && subject.equals(text(existing.get("subject")))) {
                return;
            }
        }
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", 1);
        row.put("kind", kind.name());
        row.put("cls", cls.name());
        row.put("subject", subject);
        row.put("detail", detail);
        gaps.add(row);
    }

    /** Recorded rows in observed order; unstamped rows sort last. */
    private static void sortByEventSeq(List<Map<String, Object>> rows) {
        rows.sort(Comparator.comparingLong(value ->
                longNumber(value.get("eventSeq"), Long.MAX_VALUE)));
    }

    /**
     * The one index the demand walk reads: each region's failure-target
     * cells, the branches each activation was observed to take, and the
     * candidate graph's backward adjacency inside a region.  No ports: which
     * declared port mints is SymbolicInputSelection's decision at PLAN.
     */
    private static final class RegionDemandIndex {
        /** Every observed occurrence's performed regions, own first. */
        private final Map<String, List<String>> regionsByOccurrence =
                new LinkedHashMap<>();
        private final Map<String, List<String>> localIncoming =
                new LinkedHashMap<>();
        /** Control predecessors remain live when value flow hits a store. */
        private final Map<String, List<String>> guardIncoming =
                new LinkedHashMap<>();
        private final Map<String, Map<String, List<String>>>
                explicitFatalSeedsBySite = new LinkedHashMap<>();
        /** The decisions on the way to the annotated throw (the scope map's
         *  TARGET_SITE rows, {@link StaticScopeMap.Site#pathSites}): an
         *  activation that took one is an occurrence the failure is about,
         *  whether or not it went on to the throw.  A {@code failureTarget}
         *  branch the rows do not name is none of these. */
        private final Set<String> pathSites = new LinkedHashSet<>();

        private RegionDemandIndex(StaticProgram program,
                                  StaticScopeMap scopeMap) {
            for (StaticScopeMap.Site target : scopeMap.targetSites()) {
                pathSites.addAll(target.pathSites());
            }
            // Every observed activation, not only port holders: the walk
            // needs each occurrence's text.
            for (Map.Entry<String, Map<String, Object>> entry
                    : program.activations.entrySet()) {
                regionsByOccurrence.put(entry.getKey(),
                        performedRegionIds(entry.getValue()));
            }
            Set<String> selectedRegions = new LinkedHashSet<>();
            for (Map<String, Object> region : program.regions) {
                String regionId = text(region.get("regionId"));
                selectedRegions.add(regionId);
                for (Map<String, Object> branch
                        : rows(region.get("branchPolicies"))) {
                    String site = text(branch.get("siteId"));
                    if (site.isEmpty() || !Boolean.TRUE.equals(booleanValue(
                            branch.get("failureTarget")))) {
                        continue;
                    }
                    List<String> seeds = explicitFatalSeedsBySite
                            .computeIfAbsent(regionId,
                                    ignored -> new LinkedHashMap<>())
                            .computeIfAbsent(site,
                                    ignored -> new ArrayList<>());
                    for (String operand : strings(
                            branch.get("operandCells"))) {
                        if (!seeds.contains(operand)) seeds.add(operand);
                    }
                }
            }
            for (Map<String, Object> edge : program.graph) {
                String from = text(edge.get("fromCell"));
                String to = text(edge.get("toCell"));
                if (from.isEmpty() || to.isEmpty()) continue;
                for (String regionId : program.skeletonRegionsHolding(
                        text(edge.get("method")))) {
                    if (!selectedRegions.contains(regionId)) continue;
                    addUnique(localIncoming, contextKey(regionId, to),
                            from);
                    if ("GUARD".equals(text(edge.get("transferKind")))) {
                        addUnique(guardIncoming, contextKey(regionId, to),
                                from);
                    }
                }
            }
        }

        /**
         * Activation-local evidence for the explicit {@code failureTarget}
         * sites of its performed regions, grouped by site.
         */
        private Map<String, List<Map<String, Object>>> observedFatalEvidence(
                Map<String, Object> instance) {
            Map<String, List<Map<String, Object>>> evidenceBySite =
                    new LinkedHashMap<>();
            Map<String, List<String>> explicit =
                    explicitFatalSeeds(instance);
            if (explicit.isEmpty()) {
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
                if (explicit.containsKey(site)
                        && pathSites.contains(site)) {
                    evidenceBySite.computeIfAbsent(site,
                            ignored -> new ArrayList<>()).add(evidence);
                }
            }
            return evidenceBySite;
        }

        /**
         * Whether this activation observed an explicit failure-target branch
         * (README TARGET-1): a region with no {@code failureTarget} site has
         * nothing to attest, so it never yields a freely-true target.
         */
        private boolean observedExplicitFatalTarget(
                Map<String, Object> instance) {
            return !observedFatalEvidence(instance).isEmpty();
        }

        /** Whether this activation's region declares a fatal target site. */
        private boolean declaresExplicitFatalTarget(
                Map<String, Object> instance) {
            return !explicitFatalSeeds(instance).isEmpty();
        }

        /**
         * The explicit {@code failureTarget} sites of every region this
         * occurrence PERFORMED, by site.
         */
        private Map<String, List<String>> explicitFatalSeeds(
                Map<String, Object> instance) {
            Map<String, List<String>> explicit = new LinkedHashMap<>();
            for (String regionId : performedRegionIds(instance)) {
                Map<String, List<String>> held =
                        explicitFatalSeedsBySite.get(regionId);
                if (held != null) explicit.putAll(held);
            }
            return explicit;
        }

        /**
         * The cells the failure's own decision reads: operand cells of the
         * {@code failureTarget} sites this target activation was OBSERVED to
         * decide (a target declares and observed one, see
         * failureDirectedClosure).  The first observation at a site must
         * carry an eventSeq.
         */
        private List<String> targetSeedCells(Map<String, Object> instance)
                throws IOException {
            String occurrenceId = text(instance.get("occurrenceId"));
            Map<String, List<String>> explicit =
                    explicitFatalSeeds(instance);
            List<String> cells = new ArrayList<>();
            for (Map.Entry<String, List<Map<String, Object>>> entry
                    : observedFatalEvidence(instance).entrySet()) {
                List<Map<String, Object>> occurrences = entry.getValue();
                sortByEventSeq(occurrences);
                if (longNumber(occurrences.get(0).get("eventSeq"), -1L) < 0L) {
                    throw new IOException("FATAL_PREFIX_EVIDENCE_GAP: "
                            + "observed fatal target has no eventSeq: "
                            + occurrenceId + " " + entry.getKey());
                }
                for (String cell : explicit.getOrDefault(entry.getKey(),
                        Collections.<String>emptyList())) {
                    if (!cells.contains(cell)) cells.add(cell);
                }
            }
            return cells;
        }

        /** The candidate graph's incoming cells of one cell in one region. */
        private List<String> incomingCells(String occurrenceId, String cell) {
            return edgesInto(localIncoming, occurrenceId, cell);
        }

        /** The same, restricted to the guards that decide the read. */
        private List<String> guardCells(String occurrenceId, String cell) {
            return edgesInto(guardIncoming, occurrenceId, cell);
        }

        /**
         * One occurrence's incoming cells over every region it performed:
         * folded text ran here, so the walk crosses it here or nowhere.
         */
        private List<String> edgesInto(Map<String, List<String>> edges,
                                       String occurrenceId, String cell) {
            List<String> incoming = new ArrayList<>();
            for (String regionId : regionsByOccurrence.getOrDefault(
                    occurrenceId, Collections.<String>emptyList())) {
                for (String from : edges.getOrDefault(
                        contextKey(regionId, cell),
                        Collections.<String>emptyList())) {
                    if (!incoming.contains(from)) incoming.add(from);
                }
            }
            return incoming;
        }

        private static void addUnique(Map<String, List<String>> target,
                                      String key, String value) {
            if (value.isEmpty()) return;
            List<String> values = target.computeIfAbsent(key,
                    ignored -> new ArrayList<>());
            if (!values.contains(value)) values.add(value);
        }
    }

    public static final class Result {
        /** Finalized region rows exactly as written to the artifact. */
        public final List<Map<String, Object>> regions;
        /**
         * Gaps this pass raised; no later stage can see what they report, so
         * they travel into the runtime plan artifact with their own class.
         */
        public final List<Map<String, Object>> gaps;
        private Result(List<Map<String, Object>> regions,
                       List<Map<String, Object>> gaps) {
            this.regions = regions;
            this.gaps = gaps;
        }
    }
}
