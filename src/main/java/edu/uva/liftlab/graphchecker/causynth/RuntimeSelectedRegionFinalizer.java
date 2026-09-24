package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.annotation.Debug;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.DeclaredSiteCapture;
import edu.uva.liftlab.graphchecker.plan.DeclaredSymbolicInputs;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.runtime.OccurrenceBinding;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
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
     * Skeleton field naming the methods reached from the anchors that admitted
     * the region.
     */

    /**
     * Existing planner admission vocabulary for a bounded state writer.  Why
     * this activation is in the plan at all, when it is there for anything
     * other than reaching the fatal target: the planner publishes it on the
     * occurrence's plan row so a reader of the frozen artifact can tell a
     * demanded state writer from a target-reachable region.
     */
    public static final String ADMISSION_BASIS = "admissionBasis";
    private static final String SHARED_LOCATION_DEMAND_ADMISSION =
            "SHARED_LOCATION_DEMAND_V1";
    /**
     * Which shared locations a demand admission was asked for.  Published on
     * the plan row beside {@link #ADMISSION_BASIS} so a reader of the frozen
     * artifact can tell which location bought each admission, rather than
     * having to re-derive it from the retained edges.
     */
    /**
     * How many shared-location demand hops separate this admission from the
     * fatal target.  A writer the failure closure's own port demand asked for
     * is one hop; a writer asked for only because an already admitted
     * occurrence reads the location is one hop further out.  Published on
     * the plan row beside {@link #ADMISSION_BASIS}: it is the only place the
     * frozen artifact records how far a demand travelled, and it cannot be
     * reconstructed from the retained edges, which carry port demand and
     * protocol closure as well as this rule's hops.
     *
     * <p>It is the shortest demand chain that reached the admission, not a
     * statement about the configured bound, and it can exceed that bound: an
     * admission the failure closure's own port demand asked for is made
     * whatever the bound says, and is then labelled with the chain it sits
     * on.  Only {@code transitiveSharedLocationDemand} refuses a hop, so a
     * row deeper than the bound is a first-order admission and not evidence
     * that the bound leaked.
     */
    public static final String DEMAND_DEPTH = "demandDepth";
    /** The fatal target is the origin of every shared-location demand. */
    private static final int TARGET_DEMAND_DEPTH = 0;
    /**
     * {@code admissionBasis} of an activation the plan carries because its
     * region declares a communication capture.
     *
     * <p>Same rule, same reason, as {@link DeclaredSymbolicInputs#ADMISSION}
     * one authority further out: a capture site the case DECLARED in
     * {@code communication-mappings.jsonl} is where a value leaves one
     * component and arrives in another, and an export that runs outside
     * every instrumented activation has no decision prefix, so its arm can
     * never be attested -- which is how hdfs-11741 campaign #4 published
     * all 13 arms of the key-id family as {@code attested:false} with the
     * producing side {@code instrumented:false} in every session.  Nothing
     * demands an export's outputs (the value's consumer is on another node,
     * and the walk is over this node's recorded flows), so a demand-directed
     * closure cannot arrive on it.  The declaration is what puts it in the
     * plan.</p>
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
    /** Gap code: several activations, one occurrence address. */
    /** Activation member listing the root calls that share its address. */
    public static final String SHARED_ADDRESS_ROOT_CALLS =
            "sharedAddressRootCallIds";
    /**
     * {@code kind} of one recorded region entry the run FOLDED.
     *
     * <p>F1 (paper SS3.1.2, {@code Identity#fold}): a declared region entered
     * synchronously inside an occurrence already running opens NONE of its
     * own, so the recording writes its entry with no occurrence address and
     * {@code regionFolded}, and PLAN records no activation for it.  A row of
     * this kind is what remains: the entry HAPPENED, and the occurrence it
     * folded into is the one that performed everything below it.  The
     * planner mints one per folded entry and names the enclosing occurrence
     * on it; nothing offline re-derives either half.</p>
     */
    public static final String REGION_FOLD_KIND = "RUNTIME_REGION_FOLD";
    /**
     * Activation member: the regions whose roots FOLDED into this occurrence.
     *
     * <p>The region→occurrence table of the fold rule, published where the
     * occurrence is: a declared region named here has no occurrence of its
     * own anywhere in this plan, and this is the occurrence its mints, its
     * sites and its tasks belong to.</p>
     */
    public static final String FOLDED_REGION_IDS = "foldedRegionIds";
    /**
     * Activation member: this occurrence is the failure the case is about.
     *
     * <p>README TARGET-1 binds target existence to a selected concrete
     * branch event, and this closure is where that binding is made -- over
     * the regions the occurrence PERFORMED, which since the fold rule is no
     * longer the same question as which region it is an activation of.  So
     * the answer is stated on the row rather than re-derived by the plan
     * builder from a static {@code selection} that names the region the
     * failure is IN and not the occurrence that ran it.</p>
     */
    public static final String FAILURE_TARGET_OCCURRENCE =
            "failureTargetOccurrence";

    private RuntimeSelectedRegionFinalizer() {
    }

    /**
     * Finalizes the selected runtime graph.  Symbolic values cross
     * occurrences only through VM VALUE_HANDOFF edges; no offline pairing
     * is read here.
     */
    public static Result finalizeRegions(
            List<Map<String, Object>> graph,
            List<StaticProgram.RegionRow> selectedSkeletons,
            String skeletonSource, Collection<String> observedMethods,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeRegionFolds,
            Collection<Map<String, Object>> runtimeObservations,
            StaticScopeMap scopeMap)
            throws IOException {
        Set<String> observed = new LinkedHashSet<>();
        if (observedMethods != null) {
            observed.addAll(observedMethods);
        }
        refuseUnactivatedDeclaredInputs(selectedSkeletons, runtimeInstances,
                runtimeRegionFolds);

        StaticProgram program = new StaticProgram();
        program.refinedGraph = graph;
        for (StaticProgram.RegionRow skeleton : selectedSkeletons) {
            program.skeletons.put(skeleton.regionId, skeleton);
        }

        // Activation identity is read off the trace before the first port of
        // a region is built.
        Map<String, List<Map<String, Object>>> targetPoliciesByRegion =
                new LinkedHashMap<>();
        for (Map.Entry<String, StaticProgram.RegionRow> entry
                : program.skeletons.entrySet()) {
            if (!selectedRegion(entry.getValue(), observed)) continue;
            targetPoliciesByRegion.put(entry.getKey(), failureTargetPolicies(
                    program.regionGraph(entry.getKey())));
        }
        List<Map<String, Object>> branchOrder = orderedBranchObservations(
                runtimeObservations);
        // The addresses several activations landed on, held until the closure
        // is known: whether that ambiguity blocks is whether the region is
        // inside it (see #stateSharedAddressClasses).
        List<Map<String, Object>> sharedAddresses = new ArrayList<>();
        Map<String, String> occurrenceByRecordedRootCall =
                readOccurrences(program, runtimeInstances, skeletonSource,
                        sharedAddresses);
        // The regions whose text this region's occurrences ran without
        // opening an occurrence for it: the fold rule, lifted from one
        // occurrence to the region row, because a region row is what the
        // plan states branch policies on and a folded region has no row of
        // its own to state them.
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
            region.put("schemaVersion", 3);
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
            // THE DECLARATION UNION: an occurrence declares its own region's
            // declarations and those of every region folded into it.  Same
            // rule as the fold, same rule as ClosurePlanner#holds -- the
            // occurrence RAN those sites, so it owns what they declare, and
            // a folded region has no row of its own left to own them.  The
            // methods first, because every per-occurrence filter downstream
            // (runtimeDefinitionMethods, retained loops, the scheduler's
            // declared ports) asks whether this occurrence's region holds
            // the site's method, and the enclosing skeleton need not name a
            // folded region's methods at all.
            region.put("methods", declaredMethodUnion(program, skeleton,
                    foldedHere));
            // The refined row is built fresh, so anything the skeleton carries
            // has to be carried over by name.  The catalogs are unioned; the
            // declared-root flag is not, because it pairs with THIS row's
            // rootMethod and a folded declaration does not rename a root.
            Object declaredRoot = skeleton.json.get(
                    DeclaredSymbolicInputs.ROOT_FIELD);
            if (declaredRoot != null) {
                region.put(DeclaredSymbolicInputs.ROOT_FIELD, declaredRoot);
            }
            for (String carried : new String[]{RETAINED_LOOPS,
                    StaticSymbolicSourceDeclaration.FIELD,
                    ConfiguredSourcePhaseContract.DECLARATION_FIELD}) {
                List<Map<String, Object>> declared = declaredRowUnion(
                        program, skeleton, foldedHere, carried);
                if (!declared.isEmpty()) region.put(carried, declared);
            }

            // The region's PORTS are its declared ones and nothing else:
            // the cut ports its case declared, added below, and -- at PLAN
            // -- the ports SymbolicInputSelection mints from the scope map's
            // DECLARED_SITE rows and the recording's own captures.  Both
            // catalogs are published, so every stage after this one reads
            // one shape whether or not the region declares anything.
            region.put("symbolicInputs", new ArrayList<Map<String, Object>>());
            region.put("outputs", new ArrayList<Map<String, Object>>());
            region.put("branchPolicies", branches(program, regionId,
                    foldedIntoRegion.getOrDefault(regionId,
                            Collections.<String>emptyList())));
            program.regions.add(region);
        }
        bindObservedFatalTargets(program.regions, runtimeInstances,
                branchOrder);
        // applyClosure drops every region the target-directed walk did not
        // reach; the declaration pass after it restores the region-level
        // catalog rows used downstream.
        Map<String, List<CutPort>> cutPorts = declaredCutPorts(program);
        declareCommunicationPorts(program, cutPorts, foldedIntoRegion);
        // One index over the region catalog, so the fatal-prefix pass and
        // the closure walk read the same declaration table.
        RegionDemandIndex demands = new RegionDemandIndex(program.regions,
                program.activations, program.refinedGraph);
        ClosureWalk closure = failureDirectedClosure(program, demands,
                skeletonSource, scopeMap);
        applyClosure(program, closure);
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
     * The cut ports every region declares, derived once.  The closure filter
     * drops the region-level declarations it cannot reach, so the catalog is
     * published again after it from this same table rather than rebuilt.
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
     * The region-level rows of one skeleton's declared cut ports, by side
     * ({@code IN} / {@code OUT}): the port as the mappings declare it, with
     * the one value cell the region graph names for it when it names
     * exactly one.  The static statement about the cut, so an occurrence a
     * replay exposed ({@code ExposedRegionPlanMain}) holds the same rows a
     * recorded one does.
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
     * Publishes the ports of every cut this region holds a side of.
     *
     * <p>Its own cuts and those of every region FOLDED into one of its
     * occurrences.  A folded region opens no occurrence, so it has no plan
     * row to hold its side of the cut, and the occurrence that ran its
     * export or its attach is the only one that can: on hdfs-11741 the IN
     * side of the data-encryption-key-id exchange is declared by {@code
     * retrieveDataEncryptionKey}'s region alone, which folds into the
     * DataNode's SASL handler, and without this the consumer side of the
     * target's own exchange is in no plan at all.</p>
     */
    private static void declareCommunicationPorts(StaticProgram program,
            Map<String, List<CutPort>> declaredByRegion,
            Map<String, List<String>> foldedIntoRegion) {
        for (Map<String, Object> region : program.regions) {
            String regionId = text(region.get("regionId"));
            List<CutPort> declared = new ArrayList<>();
            for (String performed : performedRegionIds(regionId,
                    foldedIntoRegion)) {
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
            // The cut argument is the one client output never written to the
            // heap, so the only cell that names it is the callee parameter the
            // value is bound into at the cut unit.
            int argumentIndex = (int) longNumber(port.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX), -1L);
            return callee.isEmpty() || javaType.isEmpty()
                    || argumentIndex < 0 ? ""
                    : callee + ".param" + argumentIndex + ":" + javaType;
        }
        return "";
    }

    /**
     * Adds the occurrence-owned instance of one declared cut port, so demand
     * propagation can reach the exact activation that used it.
     */
    /**
     * The structural key of one planned occurrence, or {@code ""} for none.
     *
     * <p>These joins decide which rows belong to one occurrence, and they did
     * it by string equality on {@code occurrenceId}.  That is correct exactly
     * while every id they see is a planned address; it silently merges two
     * activations the moment one carries an {@code #a<n>} suffix, because the
     * address deliberately drops the suffix and the string does not.  So the
     * key is now parsed and re-rendered, and a value that does not spell one
     * planned address is refused rather than joined on.</p>
     *
     * <p>Byte-neutral today: every {@code occurrenceId} the region graph
     * carries is a planned address (505 of 505 in lane BC's
     * {@code concolic_region_plan.jsonl}), so the rendered key is the string
     * it parsed.  The value is that the two can no longer drift apart in
     * silence.</p>
     */
    static String occurrenceKey(Object encoded) {
        String occurrenceId = text(encoded);
        if (occurrenceId.isEmpty()) return "";
        String rendered;
        try {
            rendered = OccurrenceAddress.parse(occurrenceId).render();
        } catch (RuntimeException notAnAddress) {
            throw new IllegalArgumentException("region graph occurrence id "
                    + "is not one planned address: " + occurrenceId,
                    notAnAddress);
        }
        if (!rendered.equals(occurrenceId)) {
            throw new IllegalArgumentException("region graph occurrence id "
                    + "is not one planned address: " + occurrenceId);
        }
        return rendered;
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
     * The node this activation ran on, as its own ADDRESS states it.
     *
     * <p>A component of the occurrence address the recording computed, read
     * back out of it -- not a second reading of the trace rows.  Every
     * activation in the program has an address ({@link #readOccurrences}
     * refuses one that has none), so a string here that is not an address is
     * a corrupt seed and says so by throwing.</p>
     */
    private static String activationSourceKey(Map<String, Object> instance) {
        return instance == null
                ? OccurrenceBinding.UNREGISTERED_SOURCE_KEY
                : edu.uva.liftlab.graphchecker.contract.OccurrenceAddress
                        .parse(text(instance.get("occurrenceId")))
                        .node().render();
    }

    /**
     * Reads the occurrence address of every observed region activation and
     * stamps it onto every row the recorded root call named.
     *
     * <p>READS.  The address was computed once, by {@code
     * Identity.occurrence}, at the entry the recording woved it at, and a
     * replay of the same occurrence computes the same string with the same
     * function; an offline re-derivation here would be a second identity,
     * and the two disagreed on 44 activations of hdfs-17960 (REPORT-M2
     * §5).</p>
     *
     * <p>Two activations may still land on one address -- nothing IDENTITY-V3
     * names separates them (same node, same region, same context, same
     * index).  One occurrence is one plan row (README REGION-1): the first
     * activation is published and the rest are not, so the artifact never
     * states the contradiction and PLAN never meets it as a schema complaint
     * (RuntimePlanArtifact.read, whose duplicate check stays as the second
     * line).  Renumbering them would be an ordinal, which is what v3 exists
     * to remove; the rule that separates them is the entry count of {@code
     * Identity.enterFrame}, and a residual collision means that count could
     * not.  The address is recorded here and CLASSED after the closure walk
     * ({@link #stateSharedAddressClasses}), because whether the ambiguity
     * can reach a claim is whether the kept slice holds its region.</p>
     *
     * @param sharedAddresses collects one row per address several activations
     *     landed on: its {@code occurrenceId}, its {@code regionId} and the
     *     recorded root calls that shared it
     * @return every recorded root call, by the occurrence it belongs to
     */
    private static Map<String, String> readOccurrences(
            StaticProgram program,
            Collection<Map<String, Object>> runtimeInstances,
            String source,
            List<Map<String, Object>> sharedAddresses) throws IOException {
        Map<String, String> occurrenceByRecordedRootCall =
                new LinkedHashMap<>();
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
            occurrenceByRecordedRootCall.put(
                    recordedRootCallKey(regionId, rootCallId), occurrenceId);
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
        return occurrenceByRecordedRootCall;
    }

    /**
     * States the class of every shared occurrence address, once.
     *
     * <p>A row states its own class (CONTRACT-SPEC SS2) and no later stage
     * overrules it, so the class has to be the answer to the question the
     * claim would ask: can this ambiguity reach the formula?  It can exactly
     * when the region is a member of the closure this plan publishes -- the
     * target-directed walk's own answer, {@code program.regions} after
     * {@link #applyClosure}, which is the ONE closure notion this engine has
     * and is not re-decided here.  Inside it, the shared address is an
     * occurrence a task addresses and a session publishes rows for, and
     * withholding is the only safe answer.  Outside it there is no plan row,
     * no task and no session row that names the occurrence, so nothing the
     * composer reads can rest on it: the row is DIAGNOSTIC and says so.</p>
     *
     * <p>Three rows of the reviewed hdfs-17960 run were the second case --
     * {@code FSDirectory$InitQuotaTask} ForkJoin siblings, whose fork site is
     * in the JDK and cannot be woven -- and they were published with no
     * stated class, which {@code campaign_write_gaps} reads as BLOCKING.
     * They withheld nothing that could be withheld and appeared in
     * {@code result.json blockingGapCodes} beside a claim of
     * SAT_CANDIDATE with zero blockers.</p>
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
            String identity = recordedRootCallKey(regionId, rootCallId);
            Map<String, Object> previous = byRecordedActivation.putIfAbsent(
                    identity, instance);
            if (previous != null && !previous.equals(instance)) {
                throw new IOException("conflicting runtime region activation "
                        + "payload: " + regionId + "\n" + rootCallId);
            }
        }
        return new ArrayList<>(byRecordedActivation.values());
    }

    /**
     * Refuses a declared symbolic input whose method the recording never
     * entered.
     *
     * <p>THE RECORDING ACTIVATED IT means: the recording ENTERED the
     * declared method.  Either way of entering counts, because the fold rule
     * says they are the same event seen from two stacks --
     * <ul>
     *   <li>as an occurrence of its own: a {@code
     *   RUNTIME_REGION_ACTIVATION} of the declared region, the entry that
     *   found no occurrence running on its thread; or</li>
     *   <li>as a FOLDED entry inside another occurrence: a {@code
     *   RUNTIME_REGION_FOLD} of the declared region ({@code Identity#fold},
     *   {@code regionFolded} on the recorded entry), the entry that was
     *   called synchronously inside an occurrence already running and so
     *   opened none of its own.  Its mints, its sites and its tasks belong
     *   to the occurrence it folded into, which is exactly what the fold
     *   means; the declaration is untouched by it -- the declared method's
     *   sites are still roots by declaration, planned at that enclosing
     *   occurrence.</li>
     * </ul>
     * A count of zero across BOTH is the one thing this refuses.</p>
     *
     * <p>Roots are manual, and every other stage of PLAN honours that: the
     * static slice holds the declared method, the skeleton weave roots a
     * region at it, the runtime selection keeps that region whether or not
     * pass 1 entered it, and this closure retains its activations whether or
     * not anything demands their outputs.  The one thing none of them will
     * do is invent an entry.  So a declared method the recording entered
     * nowhere is the workload's statement that it never reached the site --
     * the case's rotation count, its clock flips or its test body, not the
     * engine -- and it is named here, with the count, rather than reported
     * downstream as a site the plan does not cover.</p>
     *
     * <p>Campaign #5 of hdfs-11741 is why the fold half is written down: on
     * that recording every entry of {@code updateKeys()} (and of {@code
     * removeExpiredKeys()}) ran inside the NameNode's key-manager tick, so
     * the declared methods had entries, no activation, and this guard read
     * "never activated" over a workload that had reached the site twice.</p>
     *
     * @param runtimeRegionFolds the {@link #REGION_FOLD_KIND} rows of this
     *     recording: one per region entry that opened no occurrence
     */
    public static void refuseUnactivatedDeclaredInputs(
            List<StaticProgram.RegionRow> selectedSkeletons,
            Collection<Map<String, Object>> runtimeInstances,
            Collection<Map<String, Object>> runtimeRegionFolds)
            throws IOException {
        Map<String, Integer> activations = new LinkedHashMap<>();
        Map<String, Integer> folds = new LinkedHashMap<>();
        for (Map<String, Object> instance : runtimeInstances == null
                ? Collections.<Map<String, Object>>emptyList()
                : runtimeInstances) {
            activations.merge(text(instance.get("regionId")), 1,
                    Integer::sum);
        }
        for (Map<String, Object> fold : runtimeRegionFolds == null
                ? Collections.<Map<String, Object>>emptyList()
                : runtimeRegionFolds) {
            folds.merge(text(fold.get("regionId")), 1, Integer::sum);
        }
        for (StaticProgram.RegionRow skeleton : selectedSkeletons) {
            if (!skeleton.declaredInputRoot
                    || activations.getOrDefault(skeleton.regionId, 0) > 0
                    || folds.getOrDefault(skeleton.regionId, 0) > 0) {
                continue;
            }
            throw new IOException("DECLARED_INPUT_NEVER_ACTIVATED: the case "
                    + "declares a symbolic input in "
                    + skeleton.rootMethod + ", planned as region "
                    + skeleton.regionId + ", and the recording entered it "
                    + "0 times -- no occurrence of its own and no entry "
                    + "folded into one; the workload never reached the "
                    + "declared site, so no engine rule can carry it");
        }
    }

    /** True when this skeleton's methods were observed in the trace. */
    private static boolean selectedRegion(StaticProgram.RegionRow skeleton,
                                          Set<String> observed) {
        return !skeleton.methods.isEmpty()
                && (observed.isEmpty()
                || !Collections.disjoint(skeleton.methods, observed));
    }

    /**
     * The failure-target guard sites of one region, in the order {@link
     * #branches} would publish them.
     */
    public static final String FAILURE_TARGET_CELLS = "failureTargetCells";

    private static List<Map<String, Object>> failureTargetPolicies(
            List<Map<String, Object>> regionGraph) {
        Map<String, List<Map<String, Object>>> failureGuardsBySite =
                guardsBySite(regionGraph, RuntimeSelectedRegionFinalizer
                        ::isExceptionTargetEdge);
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map.Entry<String, List<Map<String, Object>>> entry
                : failureGuardsBySite.entrySet()) {
            if (entry.getValue().isEmpty()) continue;
            Map<String, Object> policy = new LinkedHashMap<>();
            policy.put("siteId", entry.getKey());
            policy.put("failureTarget", true);
            result.add(policy);
        }
        return result;
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
            // Of every region this occurrence PERFORMED: a target site
            // inside a region that folded into this one was reached HERE,
            // and this occurrence is the only one that can attest it.
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
     * The regions one occurrence PERFORMED: its own, and every region that
     * folded into it.
     *
     * <p>The fold rule read forwards ({@code Identity#fold}).  A region
     * entered synchronously inside this occurrence opened none of its own,
     * so its text ran here: its decisions were decided here, its reads were
     * read here, its failure target -- if it has one -- was reached here.
     * Every rule of this closure that used to ask "which region is this
     * activation of" asks this instead, because under the fold rule the two
     * questions stopped having one answer.  Own region first, so a rule that
     * takes the first answer takes the occurrence's own.</p>
     *
     * <p>It is a list and not a set on purpose: the order is the order the
     * plan states, and the plan states the occurrence before the calls it
     * made.</p>
     */
    /**
     * The same union read off the region table: this region and the ones
     * folded into its occurrences, own first.
     */
    private static List<String> performedRegionIds(
            String regionId, Map<String, List<String>> foldedIntoRegion) {
        List<String> performed = new ArrayList<>();
        if (!regionId.isEmpty()) performed.add(regionId);
        for (String folded : foldedIntoRegion.getOrDefault(regionId,
                Collections.<String>emptyList())) {
            if (!folded.isEmpty() && !performed.contains(folded)) {
                performed.add(folded);
            }
        }
        return performed;
    }

    private static List<String> performedRegionIds(
            Map<String, Object> activation) {
        List<String> performed = new ArrayList<>();
        if (activation == null) return performed;
        String own = text(activation.get("regionId"));
        if (!own.isEmpty()) performed.add(own);
        for (String folded : strings(activation.get(FOLDED_REGION_IDS))) {
            if (!folded.isEmpty() && !performed.contains(folded)) {
                performed.add(folded);
            }
        }
        return performed;
    }

    /**
     * The activations the failure's demand reaches, from the DECLARATIONS and
     * the static scope map.
     *
     * <p>Two authorities and no third.  The declarations say where a value
     * may enter the replay: the case's symbolic inputs (a declared region
     * root, and every {@code DECLARED_SITE} the recording states a capture
     * at), its communication mappings (the declared cut ports, with the
     * captures an activation performed), and the annotated target itself.
     * The static scope map says, for one location, WHICH regions' text
     * stores into it -- scope, never a writer: which activation of such a
     * region actually ran is the recording's answer, and this walk joins the
     * two ({@link StaticScopeMap#writerRegionsByCell}, CLOSURE-V2 SS4).</p>
     *
     * <p>Nothing is discovered from the recording's field accesses.  A read
     * the campaign never declared mints no symbol -- {@code
     * ConcolicScheduler.SymbolicInputSelection} is the one admission rule --
     * so an occurrence retained only because such a read paired with some
     * recorded write bought the plan a task that can publish no arm.</p>
     */
    private static ClosureWalk failureDirectedClosure(
            StaticProgram program, RegionDemandIndex demands, String source,
            StaticScopeMap scopeMap)
            throws IOException {
        Map<String, Map<String, Object>> instances = program.activations;
        if (instances.isEmpty()) {
            throw new IOException("runtime failure closure requires concrete "
                    + "region activations: " + source);
        }
        // `selection` describes the static region skeleton, so every
        // activation of an exception-context region inherits it, including the
        // concurrent activations that only produced inputs for the one that
        // failed.
        //
        // And so does every occurrence an exception-context region FOLDED
        // into, for the reason the fold rule states: that region opened no
        // occurrence, so the failure it is the context of happened in THIS
        // one, and no other occurrence can attest the target branch.  On
        // hdfs-11741 the annotated target region (retrieveDataEncryptionKey)
        // is entered only inside the DataNode's SASL handler occurrence, so
        // the handler is the exception context -- which is exactly what the
        // case's declared target occurrence names.
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
            // Stated on the row, once, by the rule that decided it: the
            // plan builder publishes a TARGET_REACH goal for exactly these
            // occurrences and does not ask the static selection a second
            // time -- under the fold rule the region whose selection says
            // EXCEPTION need not be the region this occurrence is an
            // activation of.
            Map<String, Object> activation = instances.get(target);
            if (activation != null) {
                activation.put(FAILURE_TARGET_OCCURRENCE, true);
            }
        }
        // Every activation of a declared symbolic input's method, admitted
        // by declaration.  It is an occurrence retained although nothing
        // demands one of its outputs, and it has to be, because a declared
        // site typically has no output to demand: hdfs-11741's
        // removeExpiredKeys reads the clock, decides an expiry, and in a
        // healthy recording removes nothing, so it writes no field, exports
        // no value, and no demand-directed walk can ever arrive on it.  The
        // case declared it precisely because the arm it did not take is the
        // failure.
        //
        // The DECLARED_SITE captures such an activation holds are what it
        // READS, not why it is here: they seed the walk below, and an
        // activation that holds one but was declared by nothing is left to
        // the demand like any other.
        //
        // An occurrence a declared region FOLDED into is admitted by the
        // same declaration, for the same reason one hop in: the fold rule
        // says the declared method's entry opened no occurrence of its own,
        // so this occurrence is the one that performed its reads, its
        // decisions and its mints.  Refusing it would drop the declaration
        // on the floor exactly where the recording honoured it -- hdfs-11741
        // enters updateKeys() only inside the NameNode's key-manager tick,
        // and the tick is where its clock read has to be planned.
        Set<String> declaredCallees =
                DeclaredSymbolicInputs.configuredCallees().keySet();
        Set<String> declaredInputOccurrences = new LinkedHashSet<>();
        for (Map.Entry<String, Map<String, Object>> entry
                : instances.entrySet()) {
            StaticProgram.RegionRow skeleton = program.skeletons.get(
                    text(entry.getValue().get("regionId")));
            if ((skeleton != null && skeleton.declaredInputRoot)
                    || declaresACapturedCallee(entry.getValue(),
                    declaredCallees)
                    || foldedADeclaredInputRoot(program,
                    entry.getValue())) {
                declaredInputOccurrences.add(entry.getKey());
            }
        }
        // A fatal target is already the origin of the walk, and
        // admissionBasis means "why this activation is in the plan at all,
        // when it is there for anything other than reaching the fatal
        // target" -- so a declared method that is itself the annotated
        // target (hdfs-17960's serializeSnapshotSection) states nothing
        // here and this rule leaves its rows untouched.
        declaredInputOccurrences.removeAll(targets);
        // Every activation that PERFORMED a declared communication capture,
        // admitted the same way and for the reason
        // DECLARED_COMMUNICATION_ADMISSION states: the export or attach the
        // declaration names happened in this activation, so the activation
        // has to be one the replay instrumented.
        //
        // The recording's own statement, not the declaration's scope: a
        // region that declares a port is entered once per value the workload
        // converts, and admitting every one of those activations put 146 of
        // hdfs-11741's occurrences in the plan (202 tasks against a declared
        // cap of 128) for the 22 that carried a capture.  An activation
        // states its own captures, so that is what is read.
        //
        // Over the regions the occurrence PERFORMED, for the same reason the
        // ports themselves are: a cut declared by a region that folded into
        // this occurrence is a cut this occurrence ran, and no other
        // occurrence carries it.
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

        ClosureWalk walk = walkFailureClosure(targets, instances, program,
                demands, scopeMap, scopeMap.writeSitesByCell(),
                declaredOccurrences, demandDepths);
        // Restated after the walk, so a writer the walk reached twice
        // publishes the shortest chain that reached it.
        for (String occurrence : walk.reached) {
            Map<String, Object> activation = instances.get(occurrence);
            if (activation == null || !SHARED_LOCATION_DEMAND_ADMISSION
                    .equals(text(activation.get(ADMISSION_BASIS)))) {
                continue;
            }
            activation.put(DEMAND_DEPTH,
                    demandDepth(demandDepths, occurrence));
        }
        // Stated after the walk, and only where no rule above has stated
        // one: a declared occurrence the location demand also reached keeps
        // that basis, which carries the demand depth the scheduler reads.
        for (String occurrence : declaredInputOccurrences) {
            Map<String, Object> activation = instances.get(occurrence);
            if (activation == null
                    || !text(activation.get(ADMISSION_BASIS)).isEmpty()) {
                continue;
            }
            activation.put(ADMISSION_BASIS, DeclaredSymbolicInputs.ADMISSION);
        }
        for (String occurrence : declaredCaptureOccurrences) {
            Map<String, Object> activation = instances.get(occurrence);
            if (activation == null
                    || !text(activation.get(ADMISSION_BASIS)).isEmpty()) {
                continue;
            }
            activation.put(ADMISSION_BASIS,
                    DECLARED_COMMUNICATION_ADMISSION);
        }
        return walk;
    }

    /**
     * The hop count of one admitted occurrence.  A target is the origin.  An
     * occurrence the closure reached on its own authority -- a fault entry, a
     * communication entry, a protocol producer -- is a demand origin of the
     * same standing as the target's own reads, and counts as one hop rather
     * than zero.
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
     * One backward walk over the candidate graph, from the failure's own
     * demand and from every declaration, crossing between activations only
     * where the scope map says a location is stored.
     *
     * <p>A demand is one cell of one occurrence.  Inside the occurrence the
     * walk moves on the candidate graph's own rows -- the static slice, whose
     * region scope the skeletons decide -- and it stops at a cell the scope
     * map names as stored: the value of such a cell did not come from this
     * occurrence's text, so what is upstream of it are the activations of
     * the regions that store it.  Those are reached on the node that holds
     * the object, because a heap location is private to the node and epoch
     * that holds it, and the walk continues from the same cell inside each
     * of them.  Its guard still travels: whether the read runs at all is
     * decided by this occurrence's own branches.</p>
     *
     * <p>Which of the reached activations actually wrote the value is not
     * asked and is not this stage's to answer: every one of them is a replay
     * arm of the read, and the VM's own GuardedRead expression carries the
     * choice.</p>
     */
    private static ClosureWalk walkFailureClosure(
            Collection<String> targets,
            Map<String, Map<String, Object>> instances,
            StaticProgram program,
            RegionDemandIndex demands,
            StaticScopeMap scopeMap,
            Map<String, List<StaticScopeMap.Site>> writeSites,
            Set<String> declaredOccurrences,
            Map<String, Integer> demandDepths)
            throws IOException {
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
        return new ClosureWalk(reached);
    }

    /**
     * Whether the case DECLARED one of the calls this activation made.
     *
     * <p>A callee declaration names no site of its own -- it is about every
     * call of that method in the application scope -- so the activation that
     * made the call is the one that holds the declared input, and the plan
     * has to carry it whatever the failure's demand reaches.  That is
     * hdfs-11741's three clock declarations: the value a replay would move
     * is read in {@code PBHelper.convert} and in {@code generateKeys}, in
     * activations no shared-location demand arrives on.</p>
     *
     * <p>The recording's half is the capture ({@code DeclaredSiteCapture}),
     * the declaration's half is the case file or, for a fault marker, the
     * workload's own text ({@code Debug.makeSymbolicBoolean}), and neither
     * is re-decided here: a callee nothing declared admits nothing.</p>
     */
    private static boolean declaresACapturedCallee(
            Map<String, Object> activation, Set<String> declaredCallees) {
        for (Map<String, Object> capture
                : rows(activation.get(DeclaredSiteCapture.PLAN_FIELD))) {
            String callee = text(capture.get(
                    DeclaredSiteCapture.DECLARED_CALLEE));
            if (declaredCallees.contains(callee)
                    || Debug.isBooleanMarkerSignature(callee)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The methods this region's occurrences ran: its own, and those of every
     * region folded into one of them.
     *
     * <p>A folded region's methods are not in the enclosing skeleton -- the
     * weave stops where a region roots another one, and hdfs-11741's SASL
     * handler names the pool wrapper and not {@code
     * retrieveDataEncryptionKey} itself.  Every per-occurrence filter
     * downstream asks "does this occurrence's region hold the site's
     * method", and under the fold rule the honest answer includes what it
     * ran inside a folded entry.  The recording still decides which of these
     * a given occurrence actually entered: the plan intersects this set with
     * the methods that occurrence was observed in.</p>
     */
    private static List<String> declaredMethodUnion(
            StaticProgram program, StaticProgram.RegionRow skeleton,
            List<String> foldedRegionIds) {
        List<String> methods = new ArrayList<>(skeleton.methods);
        for (String folded : foldedRegionIds) {
            StaticProgram.RegionRow row = program.skeletons.get(folded);
            if (row == null) continue;
            for (String method : row.methods) {
                if (!methods.contains(method)) methods.add(method);
            }
        }
        return methods;
    }

    /**
     * One declaration catalog of this region, unioned with the catalogs of
     * the regions folded into its occurrences.
     *
     * <p>Rows are carried verbatim and deduplicated whole: a declaration is
     * the case's statement, and two regions naming one site state one
     * declaration, not two.  Order is this region's own first, then the
     * folded ones in the order the plan names them.</p>
     */
    private static List<Map<String, Object>> declaredRowUnion(
            StaticProgram program, StaticProgram.RegionRow skeleton,
            List<String> foldedRegionIds, String field) {
        List<Map<String, Object>> declared = new ArrayList<>(
                rows(skeleton.json.get(field)));
        for (String folded : foldedRegionIds) {
            StaticProgram.RegionRow row = program.skeletons.get(folded);
            if (row == null) continue;
            for (Map<String, Object> declaration : rows(row.json.get(field))) {
                if (!declared.contains(declaration)) {
                    declared.add(declaration);
                }
            }
        }
        return declared;
    }

    /**
     * The EXCEPTION-context region this occurrence ran, or {@code ""}.
     *
     * <p>Its own when its own skeleton is one, and otherwise the first
     * exception-context region that folded into it: the selection is a
     * statement about the static region, and the fold rule says which
     * occurrence ran that region's text.  A folded region's own {@code
     * selection} is read off the SKELETON, because the fold has no
     * activation to inherit it onto.</p>
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
     * Whether a region the case DECLARED folded into this occurrence.
     *
     * <p>The other half of the declared-input admission, and the same rule:
     * a declared method entered synchronously inside a running occurrence
     * opens none of its own ({@code Identity#fold}), so THIS occurrence is
     * where its sites ran and there is no other occurrence the declaration
     * could be honoured at.  Read off {@link #FOLDED_REGION_IDS}, which the
     * planner stamped from the recording's own {@code regionFolded} entries;
     * nothing is re-derived here.</p>
     */
    private static boolean foldedADeclaredInputRoot(
            StaticProgram program, Map<String, Object> activation) {
        for (String regionId : strings(activation.get(FOLDED_REGION_IDS))) {
            StaticProgram.RegionRow folded = program.skeletons.get(regionId);
            if (folded != null && folded.declaredInputRoot) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether the recording states this activation TOOK one of the declared
     * cut values its region attaches.
     *
     * <p>{@link #OBSERVED_COMMUNICATION_CAPTURES} answers this for the
     * activation the capture site's own frame belongs to.  The declaration
     * also names the FRAME the attached value is built in -- {@code
     * consumerFrameMethod} in the case's communication mapping, published on
     * the port as {@code frameMethod} -- and that frame is a region of its
     * own, one level out, holding the capture site in its method set.  It
     * attaches the value as surely as the inner frame reads it: the leaf the
     * producer minted is installed into the object the frame returns, and
     * hdfs-11741's ten declared wire attaches are published on exactly that
     * frame region and on no other.</p>
     *
     * <p>So the same question is asked of the frame, against the same
     * recording: does it hold a DECLARED_SITE capture at the port's own call
     * site and callee?  A frame activation that converted nothing states
     * none and is not admitted.  Only the IN side is asked -- an export
     * writes its value outward, and the capture rule above already names the
     * activation that performed it.</p>
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
     * The cells one activation's DECLARED sites name.
     *
     * <p>The static half is the scope map's ({@code DECLARED_SITE#cell} --
     * the field a structural accessor reads, or the callee's own return) and
     * the dynamic half is the recording's: a site this activation never
     * entered states no capture, so it names no cell here.</p>
     */
    private static List<String> declaredCells(Map<String, Object> activation,
                                              StaticScopeMap scopeMap) {
        List<String> cells = new ArrayList<>();
        if (activation == null) return cells;
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
     * Keeps the regions the walk reached, and names the activations of each
     * that it retained.
     *
     * <p>The port catalogs are cleared here and re-declared after: a port is
     * a declaration, and a region the closure kept states the ones its case
     * declared, not the ones some earlier pass proposed for it.</p>
     */
    private static void applyClosure(StaticProgram program,
                                     ClosureWalk walk) {
        Set<String> retainedRegions = new LinkedHashSet<>();
        for (String key : walk.reached) {
            retainedRegions.add(text(program.activations.get(key).get(
                    "regionId")));
        }
        program.regions.removeIf(region -> !retainedRegions.contains(
                text(region.get("regionId"))));
        for (Map<String, Object> region : program.regions) {
            String regionId = text(region.get("regionId"));
            Set<String> occurrences = new LinkedHashSet<>();
            for (String key : walk.reached) {
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

    /**
     * Recorded root call of each activation, mapped to the identity minted
     * for it: the one place a raw trace endpoint is resolved to an
     * occurrence.
     */
    private static String recordedRootCallKey(String regionId,
                                              long rootCallId) {
        return regionId + "\n" + rootCallId;
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
     * and which cells decide them.
     *
     * <p>No policy and no guard set.  Every decision whose term has a
     * symbolic operand is recorded (LEAN section 1), so a branch the slice
     * names is a branch the replay records; and the guard set of a site is
     * {@code static_scope_map}'s, computed once by
     * {@link SiteControlDependence}.  This used to classify each site
     * EXPLORE or PATH_ASSUMPTION from a second, may-reach control-dependence
     * relation carried on the graph, and to re-derive the fatal polarity
     * from it.</p>
     *
     * <p>Over the region's own text AND the text of every region that
     * folded into one of its occurrences ({@code foldedRegionIds}).  A
     * folded region opens no occurrence, so this plan publishes no row for
     * it and there is no other row its decisions could be stated on -- and
     * they have to be stated somewhere, because the decision the case is
     * about can be one of them: on hdfs-11741 the annotated target's guard
     * lives in {@code retrieveDataEncryptionKey}, which folds into the
     * DataNode's SASL handler occurrence.</p>
     */
    private static List<Map<String, Object>> branches(
            StaticProgram program, String regionId,
            List<String> foldedRegionIds) {
        List<Map<String, Object>> edges = new ArrayList<>(
                program.regionGraph(regionId));
        for (String folded : foldedRegionIds) {
            for (Map<String, Object> edge : program.regionGraph(folded)) {
                if (!edges.contains(edge)) edges.add(edge);
            }
        }
        Map<String, List<Map<String, Object>>> bySite = guardsBySite(
                edges, edge -> true);
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
            // Which throw this guard controls, not merely that it controls
            // one.
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
            Collection<Map<String, Object>> edges,
            Predicate<Map<String, Object>> retained) {
        Map<String, List<Map<String, Object>>> bySite = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"GUARD".equals(text(edge.get("transferKind")))) continue;
            String site = firstNonEmpty(text(edge.get("guardSiteId")),
                    text(edge.get("siteId")));
            if (site.isEmpty()) continue;
            List<Map<String, Object>> guards = bySite.computeIfAbsent(site,
                    ignored -> new ArrayList<>());
            if (retained.test(edge)) guards.add(edge);
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
     * Records one finalizer gap, once per (kind, subject), stating its own
     * class exactly like a {@link
     * edu.uva.liftlab.graphchecker.contract.GapRow}.
     *
     * <p>{@code gaps} may be null where a caller builds ports outside a
     * finalize pass; the truncation below runs inside one.</p>
     */
    private static void planGap(List<Map<String, Object>> gaps, GapKind kind,
                                GapClass cls, String subject, String detail) {
        if (gaps == null) return;
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
     * The one index the demand walk reads: which cells decide each region's
     * failure target, which of its branches this activation was observed to
     * take, and the candidate graph's own backward adjacency inside a region.
     *
     * <p>No ports.  A region's ports are its DECLARED ones, and which of
     * them mints is {@code ConcolicScheduler.SymbolicInputSelection}'s
     * decision at PLAN; this stage decides only which occurrences the
     * failure's demand reaches.</p>
     */
    private static final class RegionDemandIndex {
        /**
         * Static region scope of every observed activation occurrence: the
         * regions it PERFORMED ({@link #performedRegionIds}), own first.
         *
         * <p>More than one since the fold rule: a region that folded into an
         * occurrence has no occurrence of its own, and its text was walked
         * where it ran.  An occurrence that folded nothing has exactly one,
         * which is what every rule here used to assume.</p>
         */
        private final Map<String, List<String>> regionsByOccurrence =
                new LinkedHashMap<>();
        private final Map<String, List<String>> localIncoming =
                new LinkedHashMap<>();
        /** Control predecessors remain live when value flow hits a store. */
        private final Map<String, List<String>> guardIncoming =
                new LinkedHashMap<>();
        private final Map<String, Map<String, List<String>>>
                explicitFatalSeedsBySite = new LinkedHashMap<>();
        private final Map<String, List<String>> fatalSeeds =
                new LinkedHashMap<>();

        private RegionDemandIndex(
                List<Map<String, Object>> regions,
                Map<String, Map<String, Object>> activations,
                List<Map<String, Object>> graph) {
            // The region scope of EVERY observed activation, not only of the
            // ones that hold a port: the demand walk moves on the candidate
            // graph inside an occurrence, and an occurrence whose region it
            // could not name would have no text to walk.
            for (Map.Entry<String, Map<String, Object>> entry
                    : activations.entrySet()) {
                regionsByOccurrence.put(entry.getKey(),
                        performedRegionIds(entry.getValue()));
            }
            Set<String> selectedRegions = new LinkedHashSet<>();
            for (Map<String, Object> region : regions) {
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
            for (Map<String, Object> edge : graph) {
                String from = text(edge.get("fromCell"));
                String to = text(edge.get("toCell"));
                if (from.isEmpty() || to.isEmpty()) continue;
                for (String regionId : strings(edge.get("regionIds"))) {
                    if (!selectedRegions.contains(regionId)) continue;
                    addUnique(localIncoming, contextKey(regionId, to),
                            from);
                    if ("GUARD".equals(text(edge.get("transferKind")))) {
                        addUnique(guardIncoming, contextKey(regionId, to),
                                from);
                    }
                    // A generic exception cell is only a fallback for a region
                    // without an explicit failureTarget policy.
                    if (to.contains("#exception:")
                            && !explicitFatalSeedsBySite.containsKey(
                            regionId)) {
                        addUnique(fatalSeeds, regionId, to);
                    }
                }
            }
        }

        /**
         * Activation-local evidence that this activation reached one of the
         * explicit {@code failureTarget} sites of its region, grouped by site.
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
                if (explicit.containsKey(site)) {
                    evidenceBySite.computeIfAbsent(site,
                            ignored -> new ArrayList<>()).add(evidence);
                }
            }
            return evidenceBySite;
        }

        /**
         * Whether this activation qualifies as an exception-context closure
         * target. README {@code TARGET-1} binds target existence to the
         * selected concrete branch event, so this is one question about
         * observed evidence and never about the shape of the plan: a region
         * without an explicit {@code failureTarget} policy declares no site to
         * attest, which makes every one of its activations a target with no
         * branch evidence at all - exactly the freely-true target the item
         * forbids.
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
         * The explicit {@code failureTarget} sites this occurrence could
         * have reached, by site: the ones declared by every region it
         * PERFORMED.
         *
         * <p>A target site inside a region that folded into this occurrence
         * is a site this occurrence executed -- the fold gave it no
         * occurrence of its own to be attested at.</p>
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
         * The cells the failure's own decision reads: the operand cells of
         * the {@code failureTarget} sites this activation was OBSERVED to
         * decide, or -- for a region that names no explicit target site --
         * the exception cell the slice ends at.
         *
         * <p>The observed decision is the FIRST the recording made at that
         * site in this activation, and it has to carry an event sequence:
         * an observation with none is a target the walk cannot order its
         * demand against, and it is refused by name rather than walked.</p>
         */
        private List<String> targetSeedCells(Map<String, Object> instance)
                throws IOException {
            List<String> performed = performedRegionIds(instance);
            String occurrenceId = text(instance.get("occurrenceId"));
            Map<String, List<String>> explicit =
                    explicitFatalSeeds(instance);
            if (explicit.isEmpty()) {
                List<String> seeds = new ArrayList<>();
                for (String regionId : performed) {
                    for (String seed : fatalSeeds.getOrDefault(regionId,
                            Collections.<String>emptyList())) {
                        if (!seeds.contains(seed)) seeds.add(seed);
                    }
                }
                if (seeds.isEmpty()) {
                    // Returning every observed input of the activation
                    // instead made the target slice the whole occurrence,
                    // which is the free target README TARGET-1 forbids:
                    // nothing in it is bound to a decided branch event.
                    throw new IOException("FATAL_TARGET_SEED_GAP: region "
                            + "names no failure target site and no exception "
                            + "cell: " + performed + " " + occurrenceId);
                }
                return seeds;
            }
            Map<String, List<Map<String, Object>>> evidenceBySite =
                    observedFatalEvidence(instance);
            if (evidenceBySite.isEmpty()) {
                // Selection already required this evidence; keeping the check
                // here keeps the slice fail-closed for any other caller.
                throw new IOException("exception-context activation did not "
                        + "observe its explicit fatal target branch: "
                        + occurrenceId);
            }
            List<String> cells = new ArrayList<>();
            for (Map.Entry<String, List<Map<String, Object>>> entry
                    : evidenceBySite.entrySet()) {
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
         * One occurrence's incoming cells, over the text of every region it
         * performed.
         *
         * <p>The text of a region that folded into this occurrence is text
         * this occurrence executed, so the demand walk crosses it here or
         * nowhere: no other occurrence holds those cells.  The union is
         * taken in the order {@link #performedRegionIds} states.</p>
         */
        private List<String> edgesInto(Map<String, List<String>> edges,
                                       String occurrenceId, String cell) {
            List<String> performed = regionsByOccurrence.getOrDefault(
                    occurrenceId, Collections.<String>emptyList());
            if (performed.size() == 1) {
                return edges.getOrDefault(contextKey(performed.get(0), cell),
                        Collections.<String>emptyList());
            }
            List<String> incoming = new ArrayList<>();
            for (String regionId : performed) {
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

    /** The occurrences one finalization's demand reached. */
    private static final class ClosureWalk {
        private final Set<String> reached;

        private ClosureWalk(Set<String> reached) {
            this.reached = reached;
        }
    }

    public static final class Result {
        /** Finalized region rows exactly as written to the artifact. */
        public final List<Map<String, Object>> regions;
        /**
         * Gaps this pass raised about its own ports: every one of them
         * says a recorded access or a recorded container observation was
         * dropped, which no later stage can see, so they travel into the
         * runtime plan artifact stating their own kind and class.
         */
        public final List<Map<String, Object>> gaps;
        private Result(List<Map<String, Object>> regions,
                       List<Map<String, Object>> gaps) {
            this.regions = regions;
            this.gaps = gaps;
        }
    }
}
