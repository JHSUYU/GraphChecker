package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.DeclaredSiteCapture;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.RuntimeWorkflowDiscovery;
import edu.uva.liftlab.graphchecker.plan.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
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
     * (a writer an admission on a rule's own authority asked for is two).
     * Published on the plan row because the retained edges cannot rebuild it;
     * it is the shortest chain that reached the admission.
     */
    public static final String DEMAND_DEPTH = "demandDepth";
    /** The fatal target is the origin of every shared-location demand. */
    private static final int TARGET_DEMAND_DEPTH = 0;
    /**
     * {@code admissionBasis} of an activation carried because a root it read
     * reaches what the walk demanded ({@link RootRelevance#influence}).
     */
    private static final String ROOT_RELEVANT_ADMISSION = "ROOT_RELEVANT_V1";
    /**
     * {@code admissionBasis} of an activation carried because it read a
     * fault marker at a door of the message that started an admitted
     * occurrence ({@link RecordedMessages#doorsOf}).
     */
    private static final String CONTROL_PRODUCER_ADMISSION =
            "CONTROL_PRODUCER_V1";
    /**
     * {@code admissionBasis} of an activation carried because it exported a
     * value the walk demanded on the other side of a message: the recording
     * bound its OUT capture of a port to the exchange leg the demanding
     * occurrence's IN capture of that port was bound to
     * ({@code RuntimeRegionPlanner#bindObservedCommunicationCaptures}).
     */
    private static final String WIRE_PRODUCER_ADMISSION = "WIRE_PRODUCER_V1";
    /**
     * Activation member, in memory only: per field the recording saw it read
     * or write, the objects it did so on ({@code
     * RuntimeRegionPlanner#stampFieldOwners}).  A heap location is one
     * object's field (Writers_W(l), SYMBOL-SCOPE §4.4), so the demand walk
     * crosses a stored field only to writers that may hold an object it was
     * demanded on ({@link DemandWalk#holdsOthersOnly}, {@link Demanded}).
     */
    public static final String FIELD_OWNERS = "fieldOwners";
    /**
     * Activation member, in memory only: per reference field, the objects
     * the recording saw it hold.  A mutation through the field writes its
     * referent's state, so there a shared referent is a shared location; a
     * store writes the holder's field, whatever it held (a40s
     * ReindexCollectionCmd-369: 189 lambdas capturing one ZooKeeper client
     * and 146 DocCollections holding one cached Integer box were one
     * location each, all writers of the field the target read).
     */
    public static final String FIELD_REFERENTS = "fieldReferents";
    /**
     * Activation member, in memory only: a digest of what a flip query of
     * the occurrence reads -- its events in recorded order, every input it
     * decided on with them ({@code RuntimeRegionPlanner#stampSignatures}).
     */
    public static final String SIGNATURE = "signature";
    /** Activation member, in memory only: the seq of its first event. */
    public static final String FIRST_SEQ = "firstSeq";
    /** Activation member, in memory only: the seq of its last event. */
    public static final String LAST_SEQ = "lastSeq";
    /**
     * Activation and plan-row member of an occurrence planned for a class of
     * equivalent deciders ({@link DemandWalk#classDeciders}): {@code
     * members}, the class's size, and its {@code first} (this occurrence)
     * and {@code last} addresses.
     */
    public static final String DECIDER_CLASS = "deciderClass";
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
     * Activation member: for each region entry folded into this occurrence,
     * the methods it was called under, up to and with the occurrence's root.
     */
    public static final String FOLDED_ENTRY_CALLERS = "foldedEntryCallers";
    /**
     * Activation member: this occurrence is the failure the case is about,
     * an occurrence of the declared target site under the question's own
     * {@code (r,c)}.  Stated on the row because under the fold rule the
     * static {@code selection} names the region the failure is in, not the
     * occurrence that ran it.
     */
    public static final String FAILURE_TARGET_OCCURRENCE =
            "failureTargetOccurrence";
    /**
     * Activation and plan-row member: this occurrence is the one the case
     * declared, resolved once here ({@link
     * RuntimeWorkflowDiscovery#declaredOccurrence}); PLAN reads it.
     */
    public static final String DECLARED_OCCURRENCE = "declaredOccurrence";
    /**
     * Plan-row member of every planned occurrence: its context's shape over
     * the recording's senders ({@link RecordedMessages#shape}), which a
     * replay's activation answers it by when the planned address does not
     * recur ({@code runtime.ConcolicTaskPlan#select}, IDENTITY §9).
     */
    public static final String CONTEXT_SHAPE = "contextShape";
    /**
     * Plan-row member of every planned occurrence: the ids of the other
     * occurrences the recording opened in its region on its node under a
     * context of its shape.  A replay's activation at one of them is that
     * occurrence, and answers no task by shape ({@code
     * runtime.ConcolicTaskPlan#select}, IDENTITY §9).
     */
    public static final String RECORDED_BESIDE = "recordedBeside";

    private RuntimeSelectedRegionFinalizer() {
    }

    /**
     * Finalizes the selected runtime graph.  Symbolic values cross
     * occurrences only through VM VALUE_HANDOFF edges.
     *
     * @param declaredOccurrence the case's declaration ({@code
     *     declared_target_occurrence}: an address, a selector, or {@link
     *     RuntimeWorkflowDiscovery#FIRST})
     * @param recordedSchedule the recording's schedule: who sent and who took
     *     in each message ({@link RecordedMessages})
     * @param accesses every field access the recording states
     */
    public static Result finalizeRegions(
            List<Map<String, Object>> graph,
            List<StaticProgram.RegionRow> selectedSkeletons,
            String skeletonSource, Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> branchObservations,
            StaticScopeMap scopeMap, String declaredOccurrence,
            Collection<ScheduleEvent> recordedSchedule,
            RecordedAccesses accesses)
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
                branchObservations);
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
        RegionDemandIndex demands = new RegionDemandIndex(program, scopeMap,
                branchOrder);
        applyClosure(program, failureDirectedClosure(program, demands,
                skeletonSource, scopeMap, cutPorts, declaredOccurrence,
                new RecordedMessages(recordedSchedule), accesses));
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
        private final Map<String, Object> row;
        /** The cells its capture names: an IN call return's, the locals
         *  it assigns at its site (its callee's return cell is every call's);
         *  any other, the cut cell. */
        private final Set<String> cells = new LinkedHashSet<>();

        private CutPort(String side, Map<String, Object> row,
                        List<Map<String, Object>> regionGraph) {
            this.side = side;
            this.row = row;
            if ("IN".equals(side) && CommunicationCatalogContract
                    .CAPTURE_CALL_RETURN.equals(text(row.get(
                            CommunicationCatalogContract
                                    .PORT_OUTPUT_CAPTURE_KIND)))) {
                cells.addAll(callReturnValueCells(regionGraph, row));
            } else {
                cells.add(declaredCutPortCell(row));
            }
            cells.remove("");
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
            List<Map<String, Object>> regionGraph = program.regionGraph(
                    skeleton.regionId);
            for (Map.Entry<String, List<Map<String, Object>>> side
                    : cutPortRows(skeleton, regionGraph).entrySet()) {
                for (Map<String, Object> row : side.getValue()) {
                    ports.add(new CutPort(side.getKey(), row, regionGraph));
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
            // A capture has one region-level declaration and zero or more
            // occurrence-owned instances of that declaration.
            Set<String> held = declaredCaptures(inputs, "IN");
            held.addAll(declaredCaptures(outputs, "OUT"));
            for (CutPort port : declared) {
                if (!held.add(CommunicationCatalogContract.captureKey(
                        port.side, port.row))) {
                    continue;
                }
                ("IN".equals(port.side) ? inputs : outputs).add(
                        new LinkedHashMap<>(port.row));
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

    /**
     * The call sites whose call accesses a field of the object it is called
     * on, each with that field, whose owner the call's receiver is ({@link
     * #FIELD_OWNERS}): a call that returns one (an accessor the slice does
     * not expand, {@code accessor_field_return}), and a mutation of one the
     * store was reached through a holder of (a WRITE_SITE's {@code
     * declaredCallee} whose cell is not its carrier: an atomic's {@code
     * value}, one cell for every AtomicInteger of the slice -- a40s
     * UpdateLog-928's 534 incrementAndGet/decrementAndGet occurrences were
     * writers of whichever atomic a reader read, until their receivers
     * named the one they wrote).
     */
    public static Map<String, String> fieldAccessingCalls(
            Collection<Map<String, Object>> graph, StaticScopeMap scopeMap) {
        Map<String, String> sites = new HashMap<>();
        for (Map<String, Object> edge : graph) {
            if ("accessor_field_return".equals(text(edge.get("kind")))) {
                sites.put(text(edge.get("siteId")),
                        text(edge.get("fromCell")));
            }
        }
        for (List<StaticScopeMap.Site> stores
                : scopeMap.writeSitesByCell().values()) {
            for (StaticScopeMap.Site store : stores) {
                if (!store.declaredCallee.isEmpty()
                        && !store.cell.equals(store.carrier)) {
                    sites.put(store.siteId, store.cell);
                }
            }
        }
        return sites;
    }

    /** The call sites whose call stores a cell the scope map names: a
     *  WRITE_SITE that stores through a call ({@code declaredCallee}: a
     *  container's or an atomic's mutator), each with its cell. */
    public static Map<String, String> storingCalls(StaticScopeMap scopeMap) {
        Map<String, String> sites = new HashMap<>();
        for (List<StaticScopeMap.Site> stores
                : scopeMap.writeSitesByCell().values()) {
            for (StaticScopeMap.Site store : stores) {
                if (!store.declaredCallee.isEmpty()) {
                    sites.put(store.siteId, store.cell);
                }
            }
        }
        return sites;
    }

    /** Region-level capture declarations on one side, excluding
     *  occurrence-owned copies. */
    private static Set<String> declaredCaptures(
            List<Map<String, Object>> ports, String side) {
        Set<String> captures = new LinkedHashSet<>();
        for (Map<String, Object> port : ports) {
            if (!text(port.get("occurrenceId")).isEmpty()
                    || text(port.get("portId")).isEmpty()) {
                continue;
            }
            captures.add(CommunicationCatalogContract.captureKey(side, port));
        }
        return captures;
    }

    /**
     * Reads the occurrence address of every observed region activation and
     * stamps it onto every row the recorded root call named.
     *
     * <p>READS, never re-derives: the address is {@code Identity.occurrence}'s,
     * computed once at the recording and identically at replay; an offline
     * derivation would be a second identity (IDENTITY §1).  Activations
     * IDENTITY §1 cannot separate may share one address; one occurrence is
     * one plan row (IDENTITY §5), so only the first is published, and
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
     * States the class of every shared occurrence address (IDENTITY §5,
     * CONTRACT-SPEC §2.5).
     * BLOCKING when the closure this plan publishes retains the occurrence
     * ({@code runtimeOccurrenceIds} of {@code program.regions} after {@link
     * #applyClosure}): a task addresses it.  DIAGNOSTIC otherwise: no plan
     * row, task or session row names it, whatever else of its region is
     * planned.  Trap: an unstated class reads as BLOCKING downstream
     * ({@code campaign_write_gaps}).
     */
    private static void stateSharedAddressClasses(StaticProgram program,
            List<Map<String, Object>> sharedAddresses) {
        Set<String> kept = new LinkedHashSet<>();
        for (Map<String, Object> region : program.regions) {
            kept.addAll(strings(region.get("runtimeOccurrenceIds")));
        }
        for (Map<String, Object> shared : sharedAddresses) {
            String regionId = text(shared.get("regionId"));
            boolean member = kept.contains(text(shared.get("occurrenceId")));
            Object rootCalls = shared.get(SHARED_ADDRESS_ROOT_CALLS);
            int count = rootCalls instanceof Collection
                    ? ((Collection<?>) rootCalls).size() : 0;
            planGap(program.planGaps, GapKind.OCCURRENCE_ADDRESS_SHARED,
                    member ? GapClass.BLOCKING : GapClass.DIAGNOSTIC,
                    text(shared.get("occurrenceId")),
                    count + " activations of this region share one address: "
                            + "nothing the address names distinguishes them "
                            + "(same node, causal context and execution "
                            + "index); recorded root calls " + rootCalls
                            + "; one occurrence is one plan row, so only the "
                            + "first is published"
                            + (member
                            ? "; BLOCKING: the closure this plan publishes "
                            + "retains this occurrence of " + regionId
                            + ", so a task addresses it and no claim may be "
                            + "made over it"
                            : "; DIAGNOSTIC: the closure this plan publishes "
                            + "does not retain this occurrence of " + regionId
                            + ", so no plan row, no task and no session row "
                            + "names it and no composition can rest on it"));
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
     * The activations the failure's demand reaches, from three authorities
     * only: the DECLARATIONS (communication mappings, the declared target),
     * the static scope map, which names the regions storing a location,
     * never the writer ({@link StaticScopeMap#writeSitesByCell}, SYMBOL-SCOPE
     * §3), and the roots read where the demand leads ({@link
     * #admitRelevantRoots}).  Nothing is discovered from recorded field
     * accesses: an undeclared read mints no symbol ({@code
     * ConcolicScheduler.SymbolicInputSelection}).
     *
     * @return the occurrences the demand reached
     */
    private static Set<String> failureDirectedClosure(
            StaticProgram program, RegionDemandIndex demands, String source,
            StaticScopeMap scopeMap, Map<String, List<CutPort>> cutPorts,
            String declaredOccurrence, RecordedMessages messages,
            RecordedAccesses accesses)
            throws IOException {
        Map<String, Map<String, Object>> instances = program.activations;
        if (instances.isEmpty()) {
            throw new IOException("NO_REGION_ACTIVATION: runtime failure "
                    + "closure requires concrete region activations: "
                    + source);
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
            throw new IOException("FATAL_TARGET_NOT_IN_WINDOW: runtime "
                    + "failure closure found no observed exception-context "
                    + "activation: " + source);
        }
        if (targets.isEmpty() && !policylessRegions.isEmpty()) {
            // Target existence binds to a selected concrete branch event.
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
        // The question is the declared occurrence's (r,c), at any index i
        // (explore.Branches asks the same of every replay): only the target
        // occurrences of its region, node and context shape are the walk's
        // origins.  Another target occurrence -- the same throw reached
        // under another request -- is not the question's: no rule plans it,
        // so nothing only it would demand is planned either.  The declared
        // occurrence is one the window holds back to its root; any other
        // target stays a walk origin when its shape is the question's (an
        // unknown hop is no known difference).
        Map<CausalContext, List<String>> shapes = new HashMap<>();
        String declared = RuntimeWorkflowDiscovery.declaredOccurrence(
                new ArrayList<>(targets), declaredOccurrence.isEmpty()
                        ? RuntimeWorkflowDiscovery.FIRST : declaredOccurrence,
                target -> shapes.computeIfAbsent(
                        OccurrenceAddress.parse(target).context(),
                        messages::shape));
        OccurrenceAddress question = OccurrenceAddress.parse(declared);
        Set<String> otherTargets = new LinkedHashSet<>();
        for (String target : targets) {
            if (!ContextShape.sameQuestion(OccurrenceAddress.parse(target),
                    question, context -> shapes.computeIfAbsent(context,
                            messages::shape))) {
                otherTargets.add(target);
            }
        }
        targets.removeAll(otherTargets);
        instances.get(declared).put(DECLARED_OCCURRENCE, true);
        // An occurrence the recording threw at asks nothing: the run as
        // recorded is the failure, and a claim that moves no root is never a
        // finding (owner 2026-10-04).
        // A guard of the declared target that reaches it on both arms states
        // no fatal arm to judge the recording by: the declaration is refused
        // by name (BLOCKING, a RUN_DEFECT at EMIT), never a stack trace.
        try {
            if (demands.recordedFatal(instances.get(declared), scopeMap)) {
                planGap(program.planGaps,
                        GapKind.TARGET_FATAL_IN_RECORDING, GapClass.BLOCKING,
                        declared, "the recording took the fatal arm at the "
                                + "declared occurrence: the case declares an "
                                + "occurrence that throws as recorded, so no "
                                + "counterfactual is asked of it; declare one "
                                + "the recording ran healthy");
            }
        } catch (StaticScopeMap.AmbiguousFatalArm ambiguous) {
            planGap(program.planGaps, GapKind.AMBIGUOUS_FATAL_ARM,
                    GapClass.BLOCKING, declared, ambiguous.getMessage()
                            + ", so no arm the recording took there is the "
                            + "fatal one by the scope map: the declaration "
                            + "names no question; declare the throw one "
                            + "guard arm reaches");
        }
        DemandWalk walk = new DemandWalk(program, demands, scopeMap,
                cutPorts, otherTargets);
        List<Demand> seeds = new ArrayList<>();
        for (String target : targets) {
            // Stated once here; the plan builder publishes TARGET_REACH for
            // exactly these and does not re-ask the static selection.
            instances.get(target).put(FAILURE_TARGET_OCCURRENCE, true);
            walk.admit(target, TARGET_DEMAND_DEPTH);
            for (String cell : demands.targetSeedCells(instances.get(target))) {
                seeds.add(new Demand(target, cell));
            }
        }
        walk.walk(seeds);
        admitRelevantRoots(program, walk, scopeMap, messages);
        walk.stateUnpairedWires(program.planGaps);
        walk.stateFixedDeciders(program.planGaps);
        walk.classDeciders(accesses, context -> shapes.computeIfAbsent(
                context, messages::shape));
        // Restated after the walk, so an occurrence the walk reached twice
        // publishes the shortest chain that reached it.
        for (String occurrence : walk.reached) {
            Map<String, Object> activation = instances.get(occurrence);
            if (activation.containsKey(ADMISSION_BASIS)) {
                activation.put(DEMAND_DEPTH, walk.depth(occurrence));
            }
        }
        stateShapes(instances, walk.reached, context -> shapes.computeIfAbsent(
                context, messages::shape));
        return walk.reached;
    }

    /**
     * States on every planned occurrence what a replay answers it by where
     * its address does not recur (IDENTITY §9): its context's shape over the
     * recording's senders ({@link #CONTEXT_SHAPE}), and the ids of the
     * other occurrences the recording opened in its region on its node
     * under that shape ({@link #RECORDED_BESIDE}), each of which a replay's
     * activation at its address is.
     */
    static void stateShapes(Map<String, Map<String, Object>> instances,
                            Collection<String> planned,
                            Function<CausalContext, List<String>> shapes) {
        Map<String, List<OccurrenceAddress>> recorded = new HashMap<>();
        for (String activation : instances.keySet()) {
            OccurrenceAddress address = OccurrenceAddress.parse(activation);
            recorded.computeIfAbsent(address.regionId() + "|"
                    + address.node().render(), key -> new ArrayList<>())
                    .add(address);
        }
        for (String occurrence : planned) {
            OccurrenceAddress address = OccurrenceAddress.parse(occurrence);
            List<String> shape = shapes.apply(address.context());
            List<String> beside = new ArrayList<>();
            for (OccurrenceAddress other : recorded.get(address.regionId()
                    + "|" + address.node().render())) {
                if (!other.id().equals(address.id())
                        && shapes.apply(other.context()).equals(shape)) {
                    beside.add(other.id());
                }
            }
            instances.get(occurrence).put(CONTEXT_SHAPE, shape);
            instances.get(occurrence).put(RECORDED_BESIDE, beside);
        }
    }

    /** One root an occurrence read: a captured DECLARED_SITE of a root's
     *  input kind. */
    private static final class RootRead {
        private final String dependencyCell;
        private final boolean fault;

        private RootRead(StaticScopeMap.Site site) {
            this.dependencyCell = site.declared.dependencyCell;
            this.fault = StaticScopeMap.FAULT_INPUT.equals(
                    site.declared.inputKind);
        }
    }

    /** One IN capture the recording bound to a message: its port and the
     *  exchange leg (correlation, attempt and half) it took the value from. */
    private static final class Attach {
        private final String port;
        private final String leg;

        private Attach(String port, String leg) {
            this.port = port;
            this.leg = leg;
        }
    }

    /**
     * The roots one activation read: its captures of a clock, a fault
     * marker or a configuration getter's return.  A READ placeholder is no
     * root: it stands for its writers' value.  A configuration field's read
     * is a configured-source phase, no capture: the plan states it of
     * whichever occurrence another rule admits.
     */
    private static List<RootRead> rootReads(Map<String, Object> activation,
                                            StaticScopeMap scopeMap) {
        List<RootRead> reads = new ArrayList<>();
        for (Map<String, Object> capture
                : rows(activation.get(DeclaredSiteCapture.PLAN_FIELD))) {
            for (StaticScopeMap.Site site : scopeMap.declaredSitesAt(
                    text(capture.get(SiteId.MEMBER)),
                    text(capture.get(DeclaredSiteCapture.DECLARED_CALLEE)))) {
                String kind = site.declared.inputKind;
                if (StaticScopeMap.CLOCK_INPUT.equals(kind)
                        || StaticScopeMap.FAULT_INPUT.equals(kind)
                        || StaticScopeMap.CONFIG_INPUT.equals(kind)) {
                    reads.add(new RootRead(site));
                }
            }
        }
        return reads;
    }

    /**
     * Admits each occurrence that read a root the failure can depend on
     * ({@link RootRelevance}), to a fixed point with the demand walk.
     *
     * <p>{@link #ROOT_RELEVANT_ADMISSION}: the root's influence in its
     * occurrence reaches a location the walk demanded on its node -- unless
     * the recording saw the occurrence hold only other objects of it
     * ({@link Demanded#heldBy}) -- or a wire whose consumer the walk
     * demanded on any node.  The influence is static, so an arm the root
     * decides counts whether or not the recording took it (an expiry check
     * that removed nothing), and so does a value that leaves by a wire the
     * walk does not follow back (hdfs-11741's key-rotation tick).  Every
     * occurrence a root of which reaches what is demanded -- admitted on this
     * rule or on any other -- seeds the walk with the cells on the root's way
     * there, so the values the root meets (the reservation a clock is
     * compared with, solr-18406) are demanded in turn.</p>
     *
     * <p>{@link #WIRE_PRODUCER_ADMISSION}: a value an admitted occurrence
     * attached is an input like a root.  The walk stops value provenance at
     * a stored location, so it reaches an attach only where the attached
     * value is itself demanded ({@link DemandWalk#crossWire}); an attach
     * whose influence reaches what is demanded (hdfs-11741's DataNode
     * converting the KeyUpdateCommand's keys into the map its handshake
     * reads) crosses its message the same way ({@link
     * DemandWalk#crossMessage}), and seeds the cells on its way.</p>
     *
     * <p>{@link #CONTROL_PRODUCER_ADMISSION}: the occurrence read a fault
     * marker and holds a door of the message that started an admitted
     * occurrence; it contributes no value.</p>
     *
     * <p>A root read nothing demanded is left out, its occurrence unplanned
     * unless another rule admits it.</p>
     */
    private static void admitRelevantRoots(StaticProgram program,
            DemandWalk walk, StaticScopeMap scopeMap,
            RecordedMessages messages) throws IOException {
        Map<String, List<RootRead>> reading = new LinkedHashMap<>();
        Map<String, String> occurrenceById = new LinkedHashMap<>();
        Map<String, List<String>> methodsByRegion = new LinkedHashMap<>();
        for (StaticProgram.RegionRow skeleton : program.skeletons.values()) {
            methodsByRegion.put(skeleton.regionId, skeleton.methods);
        }
        for (Map.Entry<String, Map<String, Object>> entry
                : program.activations.entrySet()) {
            occurrenceById.put(OccurrenceAddress.parse(entry.getKey()).id(),
                    entry.getKey());
            List<RootRead> reads = rootReads(entry.getValue(), scopeMap);
            if (!reads.isEmpty()) reading.put(entry.getKey(), reads);
        }
        RootRelevance relevance = new RootRelevance(program.graph,
                walk.writeSites.keySet(), methodsByRegion);
        Set<String> served = new HashSet<>();
        Set<String> crossed = new HashSet<>();
        boolean progressed;
        do {
            progressed = false;
            List<Demand> seeds = new ArrayList<>();
            for (Map.Entry<String, List<RootRead>> entry
                    : reading.entrySet()) {
                String occurrence = entry.getKey();
                if (walk.excluded.contains(occurrence)) continue;
                List<String> regions = performedRegionIds(
                        program.activations.get(occurrence));
                Set<String> through = new LinkedHashSet<>();
                for (RootRead read : entry.getValue()) {
                    RootRelevance.Influence influence = relevance.influence(
                            regions, read.dependencyCell);
                    through.addAll(influence.through(
                            walk.demandedOf(occurrence, influence)));
                }
                if (through.isEmpty()) continue;
                if (!walk.reached.contains(occurrence)) {
                    walk.admit(occurrence, 1, ROOT_RELEVANT_ADMISSION);
                    progressed = true;
                }
                for (String cell : through) {
                    Demand demand = new Demand(occurrence, cell);
                    if (!walk.visited.contains(demand)) seeds.add(demand);
                }
            }
            // An attached value is an input like a root: one whose
            // influence reaches what is demanded crosses its message.
            for (String occurrence : new ArrayList<>(walk.reached)) {
                List<String> regions = performedRegionIds(
                        program.activations.get(occurrence));
                for (Attach attach : walk.attaches(occurrence)) {
                    String key = occurrence + "\n" + attach.port + "\n"
                            + attach.leg;
                    if (crossed.contains(key)) continue;
                    Set<String> through = new LinkedHashSet<>();
                    for (String cell : walk.attachCells.getOrDefault(
                            attach.port, Collections.<String>emptySet())) {
                        RootRelevance.Influence influence =
                                relevance.influence(regions, cell);
                        through.addAll(influence.through(
                                walk.demandedOf(occurrence, influence)));
                    }
                    if (through.isEmpty()) continue;
                    crossed.add(key);
                    walk.crossMessage(occurrence, attach, seeds::add);
                    for (String cell : through) {
                        Demand demand = new Demand(occurrence, cell);
                        if (!walk.visited.contains(demand)) seeds.add(demand);
                    }
                }
            }
            for (String occurrence : new ArrayList<>(walk.reached)) {
                if (!served.add(occurrence)) continue;
                for (String door : messages.doorsOf(
                        OccurrenceAddress.parse(occurrence))) {
                    String held = occurrenceById.get(door);
                    if (held == null || walk.reached.contains(held)
                            || walk.excluded.contains(held)
                            || !readsAFault(reading.get(held))) {
                        continue;
                    }
                    walk.admit(held, walk.depth(occurrence) + 1,
                            CONTROL_PRODUCER_ADMISSION);
                    progressed = true;
                }
            }
            progressed |= !seeds.isEmpty();
            walk.walk(seeds);
        } while (progressed);
    }

    private static boolean readsAFault(List<RootRead> reads) {
        if (reads == null) return false;
        for (RootRead read : reads) {
            if (read.fault) return true;
        }
        return false;
    }

    /** One activation's objects of one field ({@link #FIELD_OWNERS}), and
     *  the objects it held when {@code referents} ({@link
     *  #FIELD_REFERENTS}); none when the recording saw it access the field
     *  on none. */
    private static Set<Integer> objectsOf(Map<String, Object> activation,
                                          String cell, boolean referents) {
        Set<Integer> objects = new HashSet<>(field(activation, FIELD_OWNERS,
                cell));
        if (referents) {
            objects.addAll(field(activation, FIELD_REFERENTS, cell));
        }
        return objects;
    }

    @SuppressWarnings("unchecked")
    private static Set<Integer> field(Map<String, Object> activation,
                                      String member, String cell) {
        Object byField = activation.get(member);
        if (!(byField instanceof Map)) return Collections.emptySet();
        Object held = ((Map<String, Object>) byField).get(cell);
        return held instanceof Set ? (Set<Integer>) held
                : Collections.<Integer>emptySet();
    }

    /** The objects one stored location was demanded on, on one node: the
     *  holders and what they held, since a root's influence may reach it by
     *  a store or a mutation. */
    private static final class Demanded {
        private final Set<Integer> objects = new HashSet<>();
        /** A demand of it whose reader the recording saw access it on no
         *  object: any object's. */
        private boolean any;

        private void add(Set<Integer> owners) {
            if (owners.isEmpty()) {
                any = true;
            } else {
                objects.addAll(owners);
            }
        }

        /** Whether an activation may hold a demanded object of this field:
         *  unless the recording saw it access the field on others only. */
        private boolean heldBy(Map<String, Object> activation, String cell) {
            Set<Integer> held = objectsOf(activation, cell, true);
            return any || held.isEmpty()
                    || !Collections.disjoint(held, objects);
        }
    }

    /**
     * The backward walk over the candidate graph from the failure's demand,
     * resumed with every admission's seeds; a demand is one cell of one
     * occurrence.  Inside an occurrence the walk follows the candidate graph;
     * at a cell the scope map names as stored it crosses to the activations
     * on the same node (heap is node-private) that ran the storing method or
     * took the arm of one of the store's guards away from it at a decision a
     * movable value reaches there, a store on the arm they did not take
     * being one flip away ({@link RegionDemandIndex#deciders}, {@link
     * #movable}),
     * unless the recording saw it hold only
     * other objects of the field than the reader read ({@link
     * #holdsOthersOnly}); there it demands the guards of the store, while
     * the read's guards still travel locally.  Which of them wrote the value
     * is not decided here: each is a replay arm, and the VM's GuardedRead
     * chooses.  At the cell a declared
     * IN port's capture names it crosses the message: to the occurrences
     * that exported that port on the exchange leg the recording bound this
     * occurrence's capture to ({@link #crossWire}).  It records what it
     * demanded for {@link RootRelevance}: the stored locations per node, and
     * the consumer cells of wires.
     */
    private static final class DemandWalk {
        private final StaticProgram program;
        private final StaticScopeMap scopeMap;
        private final RegionDemandIndex demands;
        private final Map<String, List<StaticScopeMap.Site>> writeSites;
        private final Set<String> wireConsumers = new HashSet<>();
        /** Occurrence -> the node it ran on, read once off its address,
         *  never off the trace rows (a non-address throws). */
        private final Map<String, String> nodes = new HashMap<>();
        /** The occurrences admitted, in admission order. */
        private final Set<String> reached = new LinkedHashSet<>();
        /** The occurrences no rule may plan: targets not the question's. */
        private final Set<String> excluded;
        /** Hop count of each admission: the shortest chain that reached it. */
        private final Map<String, Integer> depths = new HashMap<>();
        /** Every demand ever queued: each is walked once, at its first
         *  queueing (the queue holds no demand twice). */
        private final Set<Demand> visited = new HashSet<>();
        /** (writer, stored cell) pairs whose store guards were demanded. */
        private final Set<Demand> writersCrossed = new HashSet<>();
        /** Per store site: its storers and deciders, read once. */
        private final Map<StaticScopeMap.Site, SiteWriters> siteWriters =
                new IdentityHashMap<>();
        /** Node -> stored location -> the objects it was demanded on. */
        private final Map<String, Map<String, Demanded>> carriers =
                new HashMap<>();
        private final Set<String> consumers = new HashSet<>();
        /** Region -> the cut ports it declares. */
        private final Map<String, List<CutPort>> cutPorts;
        /** IN port -> the cells its capture names. */
        private final Map<String, Set<String>> attachCells = new HashMap<>();
        /** OUT port -> the cells its capture hands on. */
        private final Map<String, Set<String>> exportCells = new HashMap<>();
        /** OUT port and exchange leg ({@link #wireKey}) -> the occurrences
         *  whose capture of that port the recording bound to that leg. */
        private final Map<String, List<String>> exporters = new HashMap<>();
        /** Consumer cell -> the ports of the occurrences it was demanded in
         *  whose recording paired no export with it. */
        private final Map<String, Set<String>> unpaired =
                new LinkedHashMap<>();
        /**
         * The cells a value can move from under a world the engine expresses
         * ({@link #movable}): a tracked read (the replay versions it, so
         * another writer re-pairs it), a root's dependency cell, a declared
         * IN port's capture.  An untracked stored read stays the value it
         * read in every replay.
         */
        private final Set<String> sources = new HashSet<>();
        /** Occurrences that left a demanded store at guards no source
         *  reaches in them ({@link #movable}), so no writer was planned. */
        private final Set<String> fixedDeciders = new LinkedHashSet<>();
        /** Occurrences reached as writers of a demanded store: they ran
         *  its method or left it at a guard. */
        private final Set<String> storeWriters = new HashSet<>();
        /** Occurrences reached in any other role: a target, a wire
         *  producer, a root's or a control producer's admission. */
        private final Set<String> heldApart = new HashSet<>();

        private DemandWalk(StaticProgram program, RegionDemandIndex demands,
                           StaticScopeMap scopeMap,
                           Map<String, List<CutPort>> cutPorts,
                           Set<String> excluded) {
            this.program = program;
            this.scopeMap = scopeMap;
            this.demands = demands;
            this.cutPorts = cutPorts;
            this.excluded = excluded;
            this.writeSites = scopeMap.writeSitesByCell();
            sources.addAll(scopeMap.trackedCells());
            for (StaticScopeMap.Site declared : scopeMap.declaredSites()) {
                if (!declared.declared.inputKind.isEmpty()) {
                    sources.add(declared.declared.dependencyCell);
                }
            }
            for (Map<String, Object> edge : program.graph) {
                if ("wire_handoff".equals(text(edge.get("kind")))) {
                    wireConsumers.add(text(edge.get("toCell")));
                }
            }
            for (List<CutPort> ports : cutPorts.values()) {
                for (CutPort port : ports) {
                    String portId = text(port.row.get("portId"));
                    if (!"IN".equals(port.side)) {
                        exportCells.computeIfAbsent(portId,
                                ignored -> new LinkedHashSet<>())
                                .addAll(port.cells);
                        continue;
                    }
                    attachCells.computeIfAbsent(portId,
                            ignored -> new LinkedHashSet<>())
                            .addAll(port.cells);
                    sources.addAll(port.cells);
                }
            }
            for (Map.Entry<String, Map<String, Object>> entry
                    : program.activations.entrySet()) {
                nodes.put(entry.getKey(), OccurrenceAddress.parse(
                        entry.getKey()).node().render());
                for (Map<String, Object> capture : rows(entry.getValue().get(
                        OBSERVED_COMMUNICATION_CAPTURES))) {
                    String leg = text(capture.get("exchangeLeg"));
                    if ("OUT".equals(text(capture.get("side")))
                            && !leg.isEmpty()) {
                        exporters.computeIfAbsent(wireKey(text(capture.get(
                                "portId")), leg), ignored -> new ArrayList<>())
                                .add(entry.getKey());
                    }
                }
            }
        }

        /** One port on one exchange leg (a leg is one message: correlation,
         *  attempt and half, {@code RuntimeRegionPlanner.ProtocolEvent}). */
        private static String wireKey(String portId, String leg) {
            return portId + "\n" + leg;
        }

        /** Admits one occurrence on a rule's authority; a target states no
         *  basis. */
        private void admit(String occurrence, int depth, String basis) {
            admit(occurrence, depth);
            program.activations.get(occurrence).put(ADMISSION_BASIS, basis);
        }

        private void admit(String occurrence, int depth) {
            reached.add(occurrence);
            heldApart.add(occurrence);
            recordDepth(occurrence, depth);
        }

        /** Reaches one occurrence by a demand of the walk: the shortest
         *  chain is kept, the basis stated once. */
        private void reach(String occurrence, int depth, String basis)
                throws IOException {
            recordDepth(occurrence, depth);
            if (!reached.add(occurrence)) return;
            Map<String, Object> activation = program.activations.get(
                    occurrence);
            String held = text(activation.get(ADMISSION_BASIS));
            if (!held.isEmpty()) {
                throw new IOException("conflicting runtime activation "
                        + "admission basis for " + occurrence + ": " + held);
            }
            activation.put(ADMISSION_BASIS, basis);
        }

        /** Hop count of one admission; one reached on a rule's own authority
         *  (a root) counts as one hop. */
        private int depth(String occurrence) {
            Integer known = depths.get(occurrence);
            return known == null ? 1 : known;
        }

        private void recordDepth(String occurrence, int depth) {
            Integer known = depths.get(occurrence);
            if (known == null || depth < known) depths.put(occurrence, depth);
        }

        /** What of {@code influence} the walk demanded: the locations on the
         *  occurrence's node, unless it holds others only of their objects
         *  ({@link Demanded#heldBy}), and the wire consumer cells. */
        private Set<String> demandedOf(String occurrence,
                                       RootRelevance.Influence influence) {
            Map<String, Object> activation = program.activations.get(
                    occurrence);
            Map<String, Demanded> onNode = carriers.getOrDefault(
                    nodes.get(occurrence),
                    Collections.<String, Demanded>emptyMap());
            Set<String> ends = new LinkedHashSet<>();
            for (String carrier : influence.carriers) {
                Demanded demanded = onNode.get(carrier);
                if (demanded != null && demanded.heldBy(activation, carrier)) {
                    ends.add(carrier);
                }
            }
            for (String consumer : influence.consumers) {
                if (consumers.contains(consumer)) ends.add(consumer);
            }
            return ends;
        }

        /**
         * Walks every demand queued from {@code seeds} on, each once, in the
         * order it was first queued.  A demand is visited when queued, not
         * when taken: a cell read by N occurrences and stored by M queued
         * the M writers' guards N times over (hdfs-adhoc-42, round HS1:
         * 0.8 M duplicate demands of 2-4 KB each over 124 K distinct ones,
         * out of an 8 GB heap).
         */
        private void walk(Collection<Demand> seeds) throws IOException {
            Map<String, Map<String, Object>> instances = program.activations;
            Deque<Demand> work = new ArrayDeque<>();
            Consumer<Demand> queue = demand -> {
                if (visited.add(demand)) work.add(demand);
            };
            seeds.forEach(queue);
            while (!work.isEmpty()) {
                Demand demand = work.removeFirst();
                String occurrenceId = demand.occurrence;
                String cell = demand.cell;
                if (wireConsumers.contains(cell)) consumers.add(cell);
                crossWire(occurrenceId, cell, queue);
                List<StaticScopeMap.Site> writers = writeSites.get(cell);
                if (writers == null || writers.isEmpty()) {
                    for (String from
                            : demands.incomingCells(occurrenceId, cell)) {
                        queue.accept(new Demand(occurrenceId, from));
                    }
                    continue;
                }
                String node = nodes.get(occurrenceId);
                Map<String, Object> reader = instances.get(occurrenceId);
                carriers.computeIfAbsent(node, ignored -> new HashMap<>())
                        .computeIfAbsent(cell, ignored -> new Demanded())
                        .add(objectsOf(reader, cell, true));
                for (StaticScopeMap.Site site : writers) {
                    SiteWriters held = siteWriters.computeIfAbsent(site,
                            SiteWriters::new);
                    for (String writerOccurrence : held.candidates) {
                        if (writerOccurrence.equals(occurrenceId)
                                || excluded.contains(writerOccurrence)
                                || !node.equals(nodes.get(writerOccurrence))
                                || holdsOthersOnly(instances.get(
                                        writerOccurrence), reader, cell,
                                        site)) {
                            continue;
                        }
                        if (!held.storers.contains(writerOccurrence)
                                && !held.movable(writerOccurrence)) {
                            fixedDeciders.add(writerOccurrence);
                            continue;
                        }
                        storeWriters.add(writerOccurrence);
                        reach(writerOccurrence, depth(occurrenceId) + 1,
                                SHARED_LOCATION_DEMAND_ADMISSION);
                        // Whether it stores: its guards, demanded once per
                        // writer and cell.  Not a read of the cell: its
                        // other writers write what this read did not read,
                        // or were reached from it already.
                        if (!writersCrossed.add(new Demand(writerOccurrence,
                                cell))) {
                            continue;
                        }
                        for (String guard : demands.guardCells(
                                writerOccurrence, cell)) {
                            queue.accept(new Demand(writerOccurrence, guard));
                        }
                    }
                }
                // A stored location stops value provenance inside this
                // occurrence, but not the guard deciding whether the read
                // runs.
                for (String guard : demands.guardCells(occurrenceId, cell)) {
                    queue.accept(new Demand(occurrenceId, guard));
                }
            }
        }

        /** One store site's writer candidates, read once off the index:
         *  the occurrences that ran its storing method, then those that left
         *  it at a guard ({@link RegionDemandIndex#deciders}), each
         *  decider's {@link #movable} verdict asked once. */
        private final class SiteWriters {
            private final Set<String> storers;
            private final Map<String, List<String>> deciders;
            private final List<String> candidates;
            private final Map<String, Boolean> movable = new HashMap<>();

            private SiteWriters(StaticScopeMap.Site site) {
                List<String> stored = demands.storers(site);
                storers = new HashSet<>(stored);
                deciders = demands.deciders(site);
                Set<String> all = new LinkedHashSet<>(stored);
                all.addAll(deciders.keySet());
                candidates = new ArrayList<>(all);
            }

            private boolean movable(String decider) {
                return movable.computeIfAbsent(decider, ignored ->
                        DemandWalk.this.movable(decider,
                                deciders.get(decider)));
            }
        }

        /**
         * Whether the recording saw {@code writer} access the field {@code
         * cell} only on objects {@code reader} never accessed it on: a
         * store reaches only an object its occurrence holds, so it cannot
         * have written, nor on another arm write, what the reader read.  The
         * objects are the field's holders, and for a mutation through the
         * field ({@code declaredCallee}) what they held too, whose state it
         * writes ({@link #FIELD_REFERENTS}).  A side the recording saw no
         * access of the field on says nothing either way (an unwoven
         * accessor, an atomic's or a container's state, a store on an arm it
         * did not take).
         */
        private static boolean holdsOthersOnly(Map<String, Object> writer,
                                               Map<String, Object> reader,
                                               String cell,
                                               StaticScopeMap.Site site) {
            boolean mutation = !site.declaredCallee.isEmpty();
            Set<Integer> wroteOn = field(writer, FIELD_OWNERS, cell);
            Set<Integer> readOn = field(reader, FIELD_OWNERS, cell);
            Set<Integer> wroteHeld = mutation
                    ? field(writer, FIELD_REFERENTS, cell)
                    : Collections.<Integer>emptySet();
            Set<Integer> readHeld = mutation
                    ? field(reader, FIELD_REFERENTS, cell)
                    : Collections.<Integer>emptySet();
            // objectsOf's unions, compared without building them: asked
            // once per reader and writer of every demanded store.
            return (!wroteOn.isEmpty() || !wroteHeld.isEmpty())
                    && (!readOn.isEmpty() || !readHeld.isEmpty())
                    && Collections.disjoint(wroteOn, readOn)
                    && Collections.disjoint(wroteOn, readHeld)
                    && Collections.disjoint(wroteHeld, readOn)
                    && Collections.disjoint(wroteHeld, readHeld);
        }

        /**
         * The other side of the message a demanded consumer cell took its
         * value from: for each capture the recording bound to an exchange
         * leg in this occurrence, of an IN port a region it performed
         * declares and whose capture names the cell, every occurrence that
         * captured the port's export on the same leg, whose handed-on cells
         * are demanded there.  A consumer no export is paired with is stated
         * after the walk ({@link #stateUnpairedWires}).
         */
        private void crossWire(String occurrence, String cell,
                               Consumer<Demand> work) throws IOException {
            Set<String> ports = new LinkedHashSet<>();
            for (String regionId : performedRegionIds(
                    program.activations.get(occurrence))) {
                for (CutPort port : cutPorts.getOrDefault(regionId,
                        Collections.<CutPort>emptyList())) {
                    if ("IN".equals(port.side) && port.cells.contains(cell)) {
                        ports.add(text(port.row.get("portId")));
                    }
                }
            }
            if (ports.isEmpty()) return;
            boolean paired = false;
            for (Attach attach : attaches(occurrence)) {
                if (ports.contains(attach.port)) {
                    paired |= crossMessage(occurrence, attach, work);
                }
            }
            if (!paired) {
                unpaired.computeIfAbsent(cell,
                        ignored -> new LinkedHashSet<>()).addAll(ports);
            }
        }

        /** The IN captures the recording bound to a message in one
         *  occurrence. */
        private List<Attach> attaches(String occurrence) {
            List<Attach> held = new ArrayList<>();
            for (Map<String, Object> capture : rows(program.activations.get(
                    occurrence).get(OBSERVED_COMMUNICATION_CAPTURES))) {
                String leg = text(capture.get("exchangeLeg"));
                if ("IN".equals(text(capture.get("side")))
                        && !leg.isEmpty()) {
                    held.add(new Attach(text(capture.get("portId")), leg));
                }
            }
            return held;
        }

        /**
         * Admits the occurrences that exported {@code attach}'s port on its
         * leg -- the sending side of the message -- and demands there the
         * cells the export handed on; whether there was one.
         */
        private boolean crossMessage(String occurrence, Attach attach,
                                     Consumer<Demand> work)
                throws IOException {
            boolean paired = false;
            for (String producer : exporters.getOrDefault(wireKey(
                    attach.port, attach.leg),
                    Collections.<String>emptyList())) {
                if (producer.equals(occurrence)
                        || excluded.contains(producer)) {
                    continue;
                }
                paired = true;
                heldApart.add(producer);
                reach(producer, depth(occurrence) + 1,
                        WIRE_PRODUCER_ADMISSION);
                for (String handed : exportCells.getOrDefault(attach.port,
                        Collections.<String>emptySet())) {
                    work.accept(new Demand(producer, handed));
                }
            }
            return paired;
        }

        /**
         * Whether one of {@code guards} can decide otherwise in {@code
         * occurrence} under a world the engine expresses: a source reaches
         * the cells its decision reads, backwards over the edges of the
         * methods that ran there.  A decision no root, no tracked read and
         * no attach reaches carries no expression in any replay, so the
         * store it left is no flip away.
         */
        private boolean movable(String occurrence, List<String> guards) {
            Set<String> seen = new HashSet<>();
            Deque<String> work = new ArrayDeque<>();
            for (String guard : guards) work.addAll(demands.operandsOf(guard));
            // A decision the slice states no operand of says nothing: kept.
            if (work.isEmpty()) return true;
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (!seen.add(cell)) continue;
                if (sources.contains(cell)) return true;
                work.addAll(demands.incomingCells(occurrence, cell));
            }
            return false;
        }

        /**
         * Plans one occurrence per class of equivalent deciders: occurrences
         * the walk reached only as writers of a demanded store ({@link
         * #storeWriters}) that stored no cell demanded on their node in the
         * recording -- each left every such store at a guard, or ran its
         * method on another arm --, on one node, in one region, under one
         * context shape and call path, that did the same on the same state
         * ({@link #SIGNATURE}: their decisions in order with every input
         * they decided on, each field read's version and value, each
         * argument and return), with no access of a demanded cell by anyone
         * else between the first and the last ({@link RecordedAccesses}).  A
         * flip query is a function of what its occurrence read and decided,
         * so the members ask one query; the store a flip enables lands where
         * its member ran, and with nothing else touching a demanded cell
         * between them every reader and writer meets it in the same order,
         * so COMPOSE pairs any member's store as it pairs another's.  The
         * first member is planned and states the class ({@link
         * #DECIDER_CLASS}); the others are not.  Never merged: a recorded
         * store of a demanded cell (its write is a version a reader may have
         * read), an occurrence reached in any other role ({@link
         * #heldApart}), one that minted a root ({@link #mintsRoot}: a clock
         * read included), or attached or exported a message value: its
         * inputs are its own.  hdfs-adhoc-16:
         * 1218 to 1520 polling turns of the block scrubber, each leaving
         * removeBlock's store at its guard and running {@code run()}, the
         * method of the iterator's store, past it, planned one job each and
         * cut at PLAN.
         */
        private void classDeciders(RecordedAccesses accesses,
                Function<CausalContext, List<String>> shapes) {
            Map<String, List<String>> groups = new LinkedHashMap<>();
            for (String occurrence : reached) {
                Map<String, Object> activation = program.activations.get(
                        occurrence);
                String signature = text(activation.get(SIGNATURE));
                if (!storeWriters.contains(occurrence)
                        || heldApart.contains(occurrence)
                        || signature.isEmpty()
                        || mintsRoot(activation)
                        || !rows(activation.get(
                                OBSERVED_COMMUNICATION_CAPTURES)).isEmpty()
                        || accesses.stored(demandedOn(occurrence),
                                seq(occurrence, FIRST_SEQ),
                                seq(occurrence, LAST_SEQ),
                                callsOf(occurrence))) {
                    continue;
                }
                OccurrenceAddress address = OccurrenceAddress.parse(
                        occurrence);
                List<String> path = new ArrayList<>();
                for (Frame frame : address.index().frames()) {
                    path.add(frame.callSite());
                }
                groups.computeIfAbsent(nodes.get(occurrence) + "\n"
                        + address.regionId() + "\n"
                        + shapes.apply(address.context()) + "\n" + path
                        + "\n" + signature, ignored -> new ArrayList<>())
                        .add(occurrence);
            }
            for (List<String> group : groups.values()) {
                if (group.size() < 2) continue;
                group.sort(Comparator.comparingLong(occurrence -> seq(
                        occurrence, FIRST_SEQ)));
                Set<String> cells = demandedOn(group.get(0));
                List<String> members = new ArrayList<>();
                for (String occurrence : group) {
                    if (!members.isEmpty()) {
                        String previous = members.get(members.size() - 1);
                        Set<Long> own = callsOf(previous);
                        own.addAll(callsOf(occurrence));
                        if (accesses.touched(cells, seq(previous, FIRST_SEQ),
                                seq(occurrence, LAST_SEQ), own)) {
                            planOnce(members);
                            members = new ArrayList<>();
                        }
                    }
                    members.add(occurrence);
                }
                planOnce(members);
            }
        }

        /** Whether an occurrence captured a DECLARED_SITE that mints a root
         *  in a replay: a clock's, a fault marker's, a configuration
         *  getter's or a READ placeholder's ({@code inputKind}). */
        private boolean mintsRoot(Map<String, Object> activation) {
            for (Map<String, Object> capture
                    : rows(activation.get(DeclaredSiteCapture.PLAN_FIELD))) {
                for (StaticScopeMap.Site site : scopeMap.declaredSitesAt(
                        text(capture.get(SiteId.MEMBER)),
                        text(capture.get(
                                DeclaredSiteCapture.DECLARED_CALLEE)))) {
                    if (!site.declared.inputKind.isEmpty()) return true;
                }
            }
            return false;
        }

        /** The cells the walk demanded on an occurrence's node. */
        private Set<String> demandedOn(String occurrence) {
            return carriers.getOrDefault(nodes.get(occurrence),
                    Collections.<String, Demanded>emptyMap()).keySet();
        }

        private Set<Long> callsOf(String occurrence) {
            return new HashSet<>(MapFields.longValues(program.activations
                    .get(occurrence).get("callIds")));
        }

        private long seq(String occurrence, String member) {
            return longNumber(program.activations.get(occurrence).get(member),
                    -1L);
        }

        /** Keeps the first of one class planned, at the class's shortest
         *  chain, and the rest out. */
        private void planOnce(List<String> members) {
            if (members.size() < 2) return;
            String first = members.get(0);
            for (String member : members.subList(1, members.size())) {
                recordDepth(first, depth(member));
                reached.remove(member);
                program.activations.get(member).remove(ADMISSION_BASIS);
            }
            Map<String, Object> deciderClass = new LinkedHashMap<>();
            deciderClass.put("members", members.size());
            deciderClass.put("first", first);
            deciderClass.put("last", members.get(members.size() - 1));
            program.activations.get(first).put(DECIDER_CLASS, deciderClass);
        }

        /** One DIAGNOSTIC row per region whose occurrences left a demanded
         *  store at guards nothing the engine moves reaches ({@link
         *  #movable}), and the walk planned none of them otherwise. */
        private void stateFixedDeciders(List<Map<String, Object>> gaps) {
            Map<String, Integer> byRegion = new LinkedHashMap<>();
            for (String occurrence : fixedDeciders) {
                if (reached.contains(occurrence)) continue;
                byRegion.merge(text(program.activations.get(occurrence)
                        .get("regionId")), 1, Integer::sum);
            }
            for (Map.Entry<String, Integer> region : byRegion.entrySet()) {
                planGap(gaps, GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        region.getKey(), region.getValue() + " occurrence(s)"
                                + " of this region took the arm of a guard of"
                                + " a demanded store away from it, at a"
                                + " decision no root, tracked read or"
                                + " attach reaches there, so no world the"
                                + " engine expresses makes them store: none"
                                + " is planned as its writer");
            }
        }

        /** One DIAGNOSTIC row per demanded consumer cell the recording paired
         *  with no export: no producer of it is planned, so the value it
         *  took stays the attach as recorded. */
        private void stateUnpairedWires(List<Map<String, Object>> gaps) {
            for (Map.Entry<String, Set<String>> entry : unpaired.entrySet()) {
                planGap(gaps, GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        entry.getKey(), "the failure's demand reached this "
                                + "consumer cell of ports " + entry.getValue()
                                + " where the recording bound no capture of "
                                + "them to a message an export of them was "
                                + "bound to, so no producer of the value is "
                                + "planned and it stays the value the "
                                + "recording attached");
            }
        }
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

    /** One demand: the cell, inside the occurrence that reads it.  Holds
     *  the activation's own id and the graph's own cell, never a copy: a
     *  walk holds one per (occurrence, cell) it demanded. */
    private static final class Demand {
        private final String occurrence;
        private final String cell;
        private final int hash;

        private Demand(String occurrence, String cell) {
            this.occurrence = occurrence;
            this.cell = cell;
            this.hash = 31 * occurrence.hashCode() + cell.hashCode();
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof Demand)) return false;
            Demand that = (Demand) other;
            return hash == that.hash && occurrence.equals(that.occurrence)
                    && cell.equals(that.cell);
        }

        @Override
        public int hashCode() {
            return hash;
        }
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
     * recorded, and guard sets are {@code
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
     * Records one plan gap once per (kind, subject), stating its own class
     * like a {@link edu.uva.liftlab.graphchecker.contract.GapRow}; the one
     * spelling of a runtime plan's gap rows, the finalizer's and PLAN's.
     */
    public static void planGap(List<Map<String, Object>> gaps, GapKind kind,
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
     * candidate graph's backward adjacency inside a region, each edge with
     * the methods it lies in.  No ports: which declared port mints is
     * SymbolicInputSelection's decision at PLAN.
     */
    private static final class RegionDemandIndex {
        /** Every observed occurrence's performed regions, own first. */
        private final Map<String, List<String>> regionsByOccurrence =
                new LinkedHashMap<>();
        /** Every observed occurrence's methods that ran in it. */
        private final Map<String, Set<String>> methodsByOccurrence =
                new HashMap<>();
        /** Method -> the observed occurrences it ran in. */
        private final Map<String, List<String>> occurrencesByMethod =
                new HashMap<>();
        /** Decision site and outcome ({@link #decision}) -> the observed
         *  occurrences that took that decision there. */
        private final Map<String, Set<String>> occurrencesByDecision =
                new HashMap<>();
        /** Decision site -> the cells its decision reads: its GUARD edges
         *  into the site. */
        private final Map<String, Set<String>> guardOperands =
                new HashMap<>();
        /** (region, cell) -> incoming cell -> the methods of its edges. */
        private final Map<String, Map<String, Set<String>>> localIncoming =
                new LinkedHashMap<>();
        /** Control predecessors remain live when value flow hits a store. */
        private final Map<String, Map<String, Set<String>>> guardIncoming =
                new LinkedHashMap<>();
        private final Map<String, Map<String, List<String>>>
                explicitFatalSeedsBySite = new LinkedHashMap<>();
        /** The decisions on the way to the declared throw (the scope map's
         *  TARGET_SITE rows, {@link StaticScopeMap.Site#pathSites}): an
         *  activation that took one is an occurrence the failure is about,
         *  whether or not it went on to the throw.  A {@code failureTarget}
         *  branch the rows do not name is none of these. */
        private final Set<String> pathSites = new LinkedHashSet<>();

        private RegionDemandIndex(StaticProgram program,
                                  StaticScopeMap scopeMap,
                                  List<Map<String, Object>> branches) {
            for (StaticScopeMap.Site target : scopeMap.targetSites()) {
                pathSites.addAll(target.pathSites());
            }
            // Every observed activation, not only port holders: the walk
            // needs each occurrence's text.
            Map<Long, List<String>> occurrencesByCall = new HashMap<>();
            for (Map.Entry<String, Map<String, Object>> entry
                    : program.activations.entrySet()) {
                regionsByOccurrence.put(entry.getKey(),
                        performedRegionIds(entry.getValue()));
                methodsByOccurrence.put(entry.getKey(), new HashSet<>(
                        strings(entry.getValue().get("observedMethods"))));
                for (String method : methodsByOccurrence.get(entry.getKey())) {
                    occurrencesByMethod.computeIfAbsent(method,
                            ignored -> new ArrayList<>()).add(entry.getKey());
                }
                for (Long call : MapFields.longValues(
                        entry.getValue().get("callIds"))) {
                    occurrencesByCall.computeIfAbsent(call,
                            ignored -> new ArrayList<>()).add(entry.getKey());
                }
            }
            for (Map<String, Object> branch : branches) {
                String site = text(branch.get("siteId"));
                Object outcome = branch.get("outcome");
                for (String occurrence : occurrencesByCall.getOrDefault(
                        longNumber(branch.get("callId"), -1L),
                        Collections.<String>emptyList())) {
                    for (String key : new String[] {decision(site, null),
                            decision(site, outcome instanceof Boolean
                                    ? (Boolean) outcome : null)}) {
                        occurrencesByDecision.computeIfAbsent(key,
                                ignored -> new LinkedHashSet<>())
                                .add(occurrence);
                    }
                }
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
                String method = text(edge.get("method"));
                if (from.isEmpty() || to.isEmpty()) continue;
                if ("GUARD".equals(text(edge.get("transferKind")))
                        && to.equals(text(edge.get("siteId")))) {
                    guardOperands.computeIfAbsent(to,
                            ignored -> new LinkedHashSet<>()).add(from);
                }
                for (String regionId
                        : program.skeletonRegionsHolding(method)) {
                    if (!selectedRegions.contains(regionId)) continue;
                    add(localIncoming, contextKey(regionId, to), from,
                            method);
                    if ("GUARD".equals(text(edge.get("transferKind")))) {
                        add(guardIncoming, contextKey(regionId, to), from,
                                method);
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
         * Whether this activation took the fatal arm in the recording: an
         * outcome it observed at an explicit failure-target site is the arm
         * the scope map says reaches the throw ({@link
         * StaticScopeMap#fatalArm}).
         */
        private boolean recordedFatal(Map<String, Object> instance,
                                      StaticScopeMap scopeMap) {
            for (Map.Entry<String, List<Map<String, Object>>> site
                    : observedFatalEvidence(instance).entrySet()) {
                Boolean arm = scopeMap.fatalArm(site.getKey());
                if (arm == null) continue;
                for (Map<String, Object> evidence : site.getValue()) {
                    if (arm.equals(evidence.get("observedOutcome"))) {
                        return true;
                    }
                }
            }
            return false;
        }

        /**
         * Whether this activation observed an explicit failure-target branch:
         * a region with no {@code failureTarget} site has
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

        /** The observed occurrences that ran the store at {@code site}: its
         *  storing method ran in them, under whatever region. */
        private List<String> storers(StaticScopeMap.Site site) {
            return occurrencesByMethod.getOrDefault(SiteId.methodOf(
                    site.siteId), Collections.<String>emptyList());
        }

        /**
         * The observed occurrences that left the store at {@code site} at one
         * of its guards, each with the guards it left there: they took the
         * guard's arm away from the store (any decision at a guard that is
         * not binary), under whatever region.  A store on the arm the
         * recording did not take is one flip away (owner, 2026-10-02: the
         * closure keeps every static writer); a method that ran without
         * reaching the guard, or took its arm toward the store, is not.
         */
        private Map<String, List<String>> deciders(StaticScopeMap.Site site) {
            Map<String, List<String>> found = new LinkedHashMap<>();
            for (int index = 0; index < site.guards.size(); index++) {
                String guard = site.guards.get(index);
                Boolean toward = site.guardOutcomes == null
                        || index >= site.guardOutcomes.size() ? null
                        : site.guardOutcomes.get(index);
                for (String occurrence : occurrencesByDecision.getOrDefault(
                        decision(guard, toward == null ? null : !toward),
                        Collections.<String>emptySet())) {
                    found.computeIfAbsent(occurrence,
                            ignored -> new ArrayList<>()).add(guard);
                }
            }
            return found;
        }

        /** The cells the decision at {@code site} reads. */
        private Set<String> operandsOf(String site) {
            return guardOperands.getOrDefault(site,
                    Collections.<String>emptySet());
        }

        /** The key of a decision at {@code site}: its outcome, or null for
         *  any decision there. */
        private static String decision(String site, Boolean outcome) {
            return site + "\n" + (outcome == null ? "any" : outcome);
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
         * One occurrence's incoming cells over every region it performed --
         * folded text ran here, so the walk crosses it here or nowhere --
         * along the edges of the methods that ran in it: an edge of a method
         * this occurrence never entered carried nothing in it (a40s
         * ReindexCollectionCmd-369: walked along every method of their
         * regions, its target's 923 writers demanded 5134 more; along the
         * methods that ran in them, 244).
         */
        private List<String> edgesInto(
                Map<String, Map<String, Set<String>>> edges,
                String occurrenceId, String cell) {
            Set<String> ran = methodsByOccurrence.getOrDefault(occurrenceId,
                    Collections.<String>emptySet());
            List<String> incoming = new ArrayList<>();
            for (String regionId : regionsByOccurrence.getOrDefault(
                    occurrenceId, Collections.<String>emptyList())) {
                for (Map.Entry<String, Set<String>> from : edges.getOrDefault(
                        contextKey(regionId, cell),
                        Collections.<String, Set<String>>emptyMap())
                        .entrySet()) {
                    if (!incoming.contains(from.getKey())
                            && !Collections.disjoint(from.getValue(), ran)) {
                        incoming.add(from.getKey());
                    }
                }
            }
            return incoming;
        }

        private static void add(Map<String, Map<String, Set<String>>> target,
                                String key, String from, String method) {
            target.computeIfAbsent(key, ignored -> new LinkedHashMap<>())
                    .computeIfAbsent(from, ignored -> new HashSet<>())
                    .add(method);
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
