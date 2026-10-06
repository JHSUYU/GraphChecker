package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ObservedSite;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.AccessorCallTarget;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ConcolicMaterializationSelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.InstrumentationPlan;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.WorkStartSites;
import edu.uva.liftlab.graphchecker.plan.ScopeFrontier;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.option.GraphCheckerOptions;
import edu.uva.liftlab.graphchecker.runtime.RuntimeRegionPlanner;
import edu.uva.liftlab.graphchecker.runtime.RuntimeTraceMode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.options.Options;
import soot.ArrayType;
import soot.Body;
import soot.BooleanType;
import soot.ByteType;
import soot.CharType;
import soot.DoubleType;
import soot.FloatType;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.ShortType;
import soot.SootClass;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.UnitBox;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.PrimType;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.ClassConstant;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.LongConstant;
import soot.jimple.NullConstant;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.SwitchStmt;
import soot.tagkit.Tag;
import soot.validation.BodyValidator;
import soot.validation.CheckInitValidator;
import soot.validation.LocalsValidator;
import soot.validation.TrapsValidator;
import soot.validation.UnitBoxesValidator;
import soot.validation.ValidationException;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.Collection;
import java.util.Collections;
import java.util.EnumMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.function.Predicate;


/** Target-directed static backward data-flow analysis. */
public final class CausynthPipeline {
    private static final Logger LOG = LoggerFactory.getLogger(CausynthPipeline.class);
    private static final String TRACE_RECORDER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder";
    private static final String CONCOLIC_REGION_RUNTIME_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime";
    /** Every local a weave adds is named for the weave that added it. */
    private static final String TRACE_LOCAL_PREFIX = "$causynth";
    /**
     * Soot body rules run on every woven body ({@link #validateWovenBodies});
     * {@code CheckInitValidator} enforces {@link #afterWovenPrologue}.
     */
    private static final BodyValidator[] WOVEN_BODY_RULES = {
        CheckInitValidator.v(),
        LocalsValidator.v(),
        TrapsValidator.v(),
        UnitBoxesValidator.v(),
    };
    private final GraphCheckerOptions options;
    public CausynthPipeline(GraphCheckerOptions options) {
        this.options = options;
    }

    public void run() throws IOException {
        try {
            // Program text for every pass, so unit indices agree across them.
            DoorWeave.apply();
            analyze();
            // Before Soot writes any class file.
            validateWovenBodies();
        } finally {
            // The loop CFGs are this run's, not this JVM's.
            CfgLoopControl.forget();
        }
    }

    private void analyze() throws IOException {
        if (ConcolicInstrumentationSelections.instrumentationRequested()) {
            instrumentConcolicCampaign(ConcolicInstrumentationSelections
                    .instrumentationCampaignFromEnvironment());
            LOG.info("Instrumented the runtime-selected concolic task");
            return;
        }

        RuntimeTraceMode traceMode = RuntimeTraceMode.configured();
        if (traceMode == RuntimeTraceMode.REGION_STATE) {
            StaticProgram selected = new StaticProgram();
            selected.traceMethods.addAll(
                    RegionSkeletonInstrumentationSelection
                            .methodsFromEnvironment());
            instrumentRuntimeState(selected);
            LOG.info("REGION_STATE wove the candidate skeletons; "
                    + "static seed analysis was not rerun");
            return;
        }

        CausynthTargetContext target =
                CausynthTargetResolver.resolve(options.getInputList());
        LOG.info("Seed backward analysis starts at exception target {}: {}",
                target.exceptionTargetSite.id,
                target.exceptionTargetSite.stableIdentity());
        long seedAnalysisStart = System.nanoTime();
        StaticProgram result =
                new SeedBackwardStaticAnalyzer(target).analyze();
        long seedAnalysisMillis = elapsedMillis(seedAnalysisStart);
        long skeletonPlanningStart = System.nanoTime();
        List<DemandedDoors.Site> woven = DemandedDoors.woven();
        SymbolicRegionPlanner.planSelectedSkeleton(result,
                result.traceMethods, woven);
        // SYMBOL-SCOPE §2.3: over the door-woven bodies, before any hook is
        // woven, so site and guard ids are the unit indices a replay decides
        // at.
        Map<String, Clock> clocks = RootCatalog.clocks(result.edges);
        ConfigRoots recognized = ConfigRoots.of(result.edges,
                result.fieldWriters);
        Predicate<String> systemClass = systemClass();
        RootDemand demand = RootDemand.of(result.edges, result.regions,
                clocks, recognized,
                targetPathSites(result.edges,
                        result.executionContextAuthorities::containsKey),
                CausynthStaticFacts::trackedKind, systemClass,
                new LatentFaults(systemClass,
                        method -> !result.regionsHolding(method).isEmpty()),
                woven);
        ConfigRoots config = recognized.limitedTo(demand.configSources());
        Set<String> plantedConfigReads =
                StaticSymbolicSourceDiscovery.discover(result, config);
        long skeletonPlanningMillis = elapsedMillis(skeletonPlanningStart);
        List<StaticScopeMap.Site> scopeSites = StaticScopeMap.sites(
                result.edges, result.regions, clocks,
                (method, unitIndex, callee) -> {
                    ConfigRoots.Source source = config.call(method,
                            unitIndex, callee);
                    return source == null ? null
                            : new StaticScopeMap.ConfigCall(source.sourceId,
                                    source.domainMin, source.domainMax);
                },
                demand.marks(),
                method -> !CausynthStaticFacts.applicationMethod(method),
                CausynthStaticFacts::trackedKind,
                CausynthStaticFacts::staticField,
                CausynthStaticFacts::constructionOnly);
        List<JsonObject> scopeMap = StaticScopeMap.rows(scopeSites,
                SiteControlDependence.over(
                        StaticScopeMap.siteIds(scopeSites)),
                result.executionContextAuthorities::containsKey);
        scopeMap.addAll(recognized.keyRows(demand.configSources(),
                plantedConfigReads));
        Set<String> rootCallees = new LinkedHashSet<>(clocks.keySet());
        rootCallees.addAll(recognized.callees());
        List<JsonObject> frontier = ScopeFrontier.rows(result.edges,
                CausynthStaticFacts::analysedMethod, rootCallees,
                demand.frontier());
        long artifactWriteStart = System.nanoTime();
        CausynthArtifactWriter.writeDiscoveryArtifacts(
                target.outputDir, result, scopeMap, frontier, demand.rows());
        DemandedDoors.write(target.outputDir.resolve(DemandedDoors.FILE),
                demand.doors());
        long artifactWriteMillis = elapsedMillis(artifactWriteStart);
        LOG.info("Discovery phase timing: seedAnalysis={} ms, "
                        + "skeletonPlanning={} ms, artifactWrite={} ms",
                seedAnalysisMillis, skeletonPlanningMillis,
                artifactWriteMillis);
        LOG.info("Seed backward analysis wrote the frozen graph to {}; "
                + "symbolic regions will be finalized from the runtime trace",
                target.outputDir);
    }

    private static long elapsedMillis(long startNanos) {
        return (System.nanoTime() - startNanos) / 1_000_000L;
    }

    /**
     * The decisions an occurrence the declared throw is about takes on its
     * way there ({@code StaticScopeMap.Site#pathSites}): the throw's guards,
     * their chain -- the calls into its method up to its execution context's
     * entry included -- and the chain's deciders.
     */
    private static Set<String> targetPathSites(
            List<Map<String, Object>> edges, Predicate<String> entry) {
        Set<String> sites = new LinkedHashSet<>();
        for (Map<String, Object> edge : edges) {
            if (!"exception_throw".equals(MapFields.text(edge.get("kind")))) {
                continue;
            }
            String target = SiteId.of(MapFields.text(edge.get("method")),
                    MapFields.number(edge.get("unitIndex"), -1));
            StaticScopeMap.Guards control = SiteControlDependence.over(
                    Collections.singleton(target));
            for (StaticScopeMap.Guard guard : control.of(target)) {
                sites.add(guard.siteId());
            }
            for (StaticScopeMap.Guard guard
                    : StaticScopeMap.targetChain(control, target, entry)) {
                sites.add(guard.siteId());
            }
            sites.addAll(StaticScopeMap.Guard.decidingSites(
                    control.chainOf(target)));
        }
        return sites;
    }

    /** Whether a class is the system's own (LibraryReceivers), asked of the
     *  campaign's lineage roots at the first class it is asked of. */
    private static Predicate<String> systemClass() {
        return new Predicate<String>() {
            private Predicate<String> roots;

            @Override
            public boolean test(String owner) {
                if (roots == null) {
                    roots = LibraryReceivers.systemClasses(
                            System.getProperty(LibraryReceivers.ROOTS));
                }
                return roots.test(owner);
            }
        };
    }

    /**
     * Verifier gate: every woven body obeys {@link #WOVEN_BODY_RULES} before
     * any class file is written, rather than a {@code VerifyError} deep in a
     * replay (Soot validates only under {@code -validate}).
     */
    private void validateWovenBodies() {
        List<ValidationException> failures = new ArrayList<>();
        int validated = 0;
        for (SootClass type : Scene.v().getApplicationClasses()) {
            for (SootMethod method : type.getMethods()) {
                if (!method.hasActiveBody()) continue;
                Body body = method.getActiveBody();
                if (!wovenBody(body)) continue;
                validated++;
                for (BodyValidator rule : WOVEN_BODY_RULES) {
                    rule.validate(body, failures);
                }
                if (!failures.isEmpty()) {
                    ValidationException failure = failures.get(0);
                    throw new IllegalStateException(
                            "WOVEN_BODY_IS_UNVERIFIABLE: "
                                    + method.getSignature() + ": "
                                    + failure.getRawMessage() + " [at "
                                    + failure.getConcerned() + "]");
                }
            }
        }
        LOG.info("Woven-body verifier gate: {} woven body(ies) satisfy "
                + "definite assignment over exception edges, declared "
                + "locals, trap units and branch targets", validated);
    }

    /** Whether this body carries units a weave of this run put in it. */
    private static boolean wovenBody(Body body) {
        for (Local local : body.getLocals()) {
            if (local.getName().startsWith(TRACE_LOCAL_PREFIX)) return true;
        }
        for (Unit unit : body.getUnits()) {
            if (unit instanceof Stmt && ((Stmt) unit).containsInvokeExpr()
                    && isHookInvoke(((Stmt) unit).getInvokeExpr())) {
                return true;
            }
        }
        return false;
    }

    /** Whether one invocation is a call of a woven hook. */
    private static boolean isHookInvoke(InvokeExpr invoke) {
        return isRecorderInvoke(invoke)
                || (invoke != null && CONCOLIC_REGION_RUNTIME_CLASS.equals(
                        invoke.getMethodRef().declaringClass().getName()));
    }

    /**
     * The one method walk of every mode: resolve, gate, freeze original
     * indices, find the safe entry, emit.  A {@link #namedRefusal} is
     * rethrown; any other failure leaves that method unwoven.
     * @param scopeFailure refusal prefix for an out-of-scope signature;
     *                     empty skips it instead
     * @return the signatures rewritten, in walk order
     */
    private Set<String> instrumentMethods(Collection<String> signatures,
                                          String scopeFailure,
                                          MethodEmitter emitter) {
        Set<String> rewritten = new LinkedHashSet<>();
        for (String signature : signatures) {
            SootMethod method = CausynthStaticFacts.method(signature);
            boolean selectable = method != null && method.isConcrete();
            if (!scopeFailure.isEmpty() && (!selectable
                    || !method.getDeclaringClass().isApplicationClass())) {
                throw new IllegalStateException(scopeFailure + signature);
            }
            if (!selectable) continue;
            try {
                Body body = method.retrieveActiveBody();
                List<Unit> originalUnits = snapshotUnits(body);
                tagOriginalUnits(originalUnits);
                Unit entry = safeInstrumentationEntry(body, method);
                // A constructor without a safe entry has no site at all.
                if (method.isConstructor() && entry == null) continue;
                emitter.emit(body, method, originalUnits, entry,
                        method.isConstructor() ? entry : null,
                        receiverOrNull(body, method));
                rewritten.add(signature);
            } catch (RuntimeException exception) {
                if (namedRefusal(exception)) throw exception;
                LOG.warn("Skipping instrumentation for {}", signature,
                        exception);
            }
        }
        return rewritten;
    }

    /** Whether one failure is a refusal code an emitter deliberately raised. */
    private static boolean namedRefusal(RuntimeException exception) {
        if (!(exception instanceof IllegalStateException)) return false;
        String message = String.valueOf(exception.getMessage());
        int colon = message.indexOf(':');
        return colon > 3
                && message.substring(0, colon).matches("[A-Z][A-Z0-9_]+");
    }

    /** What one mode writes into a walked method's frame. */
    private interface MethodEmitter {
        void emit(Body body, SootMethod method, List<Unit> originalUnits,
                  Unit entry, Unit lowerBound, Value receiver);
    }

    /** First original index a rewrite may touch (after init), or -1. */
    private static int instrumentableFrom(List<Unit> originalUnits,
                                          Unit lowerBound) {
        if (lowerBound == null) return 0;
        for (int index = 0; index < originalUnits.size(); index++) {
            if (originalUnits.get(index) == lowerBound) return index;
        }
        return -1;
    }

    /** Second pass: rich evidence for only runtime-selected region methods. */
    private void instrumentRuntimeState(StaticProgram result)
            throws IOException {
        HookCatalog refs = HookCatalog.trace();
        SootMethodRef recordFieldRef = refs.ref(Hook.RECORD_FIELD);
        // Same skeleton file as the concolic pass (IDENTITY §10).
        Map<String, String> regionRoots =
                RegionSkeletonInstrumentationSelection
                        .regionRootsFromEnvironment();
        // Only the rows the aggregation reads are written (PIPELINE §2).
        TracedRows traced = TracedRows.of(
                RegionSkeletonInstrumentationSelection
                        .skeletonsFromEnvironment(),
                RegionSkeletonInstrumentationSelection.skeletonFile());
        // Beside the woven classes, on the recording's classpath: the
        // recorder states it in its manifest, the aggregation checks it.
        Files.write(Paths.get(Options.v().output_dir(),
                TracedRows.DIGEST_RESOURCE),
                traced.digest.getBytes(StandardCharsets.UTF_8));
        Set<String> rewritten = instrumentMethods(result.traceMethods,
                "REGION_STATE method is outside production application "
                        + "scope: ",
                (body, method, units, entry, lowerBound, receiver) -> {
                    instrumentRichMethod(body, method, units, entry,
                            lowerBound, receiver, refs,
                            regionRoots.getOrDefault(method.getSignature(),
                                    ""), traced);
                    instrumentFieldTrace(body, method, recordFieldRef,
                            units, lowerBound);
                });
        // Same scope as the replay, woven last.
        instrumentApplicationScope(refs);
        LOG.info("Instrumented {} of {} candidate methods for "
                + "REGION_STATE trace; {} of them open a region",
                rewritten.size(), result.traceMethods.size(),
                regionRoots.size());
    }

    /** The campaign's one deduplicated instrumentation envelope. */
    private final class CampaignEnvelope {
        private final List<InstrumentationPlan> campaign;
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<String> loopBoundMethods = new LinkedHashSet<>();
        private final Set<String> fixedCountLoopSites =
                new LinkedHashSet<>();
        /** Exact configured-source call sites, deduplicated across tasks. */
        private final Map<String, ConfiguredSourcePhaseContract.Occurrence>
                configuredSourcePhaseSites = new LinkedHashMap<>();
        private final ConcolicMaterializationSelection materializations =
                new ConcolicMaterializationSelection();
        // By plan identity: tasks (path flips) may share one root method.
        private final Map<InstrumentationPlan, SootMethod> replayEntries =
                new IdentityHashMap<>();
        /** Loop proofs frozen before any symbolic-region bridge is inserted. */
        private final Map<String, CfgLoopControl.NaturalLoop> rootLoops =
                new LinkedHashMap<>();
        /** ONE plan per root hook group, the entry woven for all of them. */
        private final Map<String, InstrumentationPlan> rootHooks =
                new LinkedHashMap<>();
        /** Every skeleton's exports: woven whatever the plan
         *  ({@link RuntimeRegionPlanner#exportSites}). */
        private final List<CommunicationHandoffSpec> exports;
        private LoopBoundPolicy loopBound;

        private CampaignEnvelope(List<InstrumentationPlan> campaign) {
            this.campaign = campaign;
            exports = RuntimeRegionPlanner.exportSites(
                    RegionSkeletonInstrumentationSelection
                            .skeletonsFromEnvironment());
            // An export's method and frame are woven as a planned
            // region's are: its leaves are addressed within them.
            for (CommunicationHandoffSpec export : exports) {
                methods.add(export.method());
                loopBoundMethods.add(export.method());
                if (!export.frameMethod().isEmpty()) {
                    methods.add(export.frameMethod());
                    loopBoundMethods.add(export.frameMethod());
                }
            }
            for (InstrumentationPlan plan : campaign) {
                materializations.mergeFrom(plan.materializations());
                methods.addAll(plan.envelopeMethods());
                for (ConfiguredSourcePhaseContract.Occurrence phase
                        : plan.configuredSourcePhases()) {
                    ConfiguredSourcePhaseContract.Occurrence prior =
                            configuredSourcePhaseSites.putIfAbsent(
                                    phase.siteId(), phase);
                    if (prior != null && (!prior.declarationMethod().equals(
                            phase.declarationMethod())
                            || prior.declarationUnitIndex()
                            != phase.declarationUnitIndex()
                            || !prior.sourceId().equals(phase.sourceId())
                            || !prior.fieldSignature().equals(
                            phase.fieldSignature())
                            || !prior.runtimeDeclaredCallee().equals(
                            phase.runtimeDeclaredCallee()))) {
                        throw new IllegalStateException(
                                "CONFIGURED_SOURCE_PHASE_SITE_CONFLICT: "
                                        + phase.siteId());
                    }
                }
                Set<String> bounded = new LinkedHashSet<>(
                        plan.instrumentationMethods());
                SootMethod replayEntry = declaredReplayEntry(plan);
                replayEntries.put(plan, replayEntry);
                // The logical region remains rooted at the plan's root.
                bounded.add(replayEntry.getSignature());
                methods.add(replayEntry.getSignature());
                loopBoundMethods.addAll(bounded);
                fixedCountLoopSites.addAll(plan.fixedCountLoopSites());
                // One union tree admits one policy: the union of the plans'.
                loopBound = loopBound == null ? plan.loopBound()
                        : loopBound.union(plan.loopBound());
                InstrumentationPlan hook = rootHooks.putIfAbsent(
                        plan.rootHookGroup(), plan);
                if (hook != null && (hook.rootLoopDemandedUnitIndex()
                        != plan.rootLoopDemandedUnitIndex()
                        || !hook.rootLoopControlSites().equals(
                        plan.rootLoopControlSites()))) {
                    throw new IllegalStateException(
                            "ROOT_HOOK_GROUP_DISAGREES: "
                                    + plan.rootHookGroup().replace('\n', ' ')
                                    + " is one woven entry, and two of its "
                                    + "rows place it differently (demanded "
                                    + "unit, loop controls)");
                }
            }
        }

        private SootMethod declaredReplayEntry(InstrumentationPlan plan) {
            try {
                return Scene.v().getMethod(plan.rootMethod());
            } catch (RuntimeException missing) {
                throw new IllegalStateException(
                        "Selected concolic root is unavailable: "
                                + plan.rootMethod(), missing);
            }
        }

        /**
         * Numbers original units of every body woven here, before any rewrite.
         * The numbering IS the site vocabulary, so a tagging failure is fatal.
         */
        private void tagSelectedBodies() {
            Set<String> tagged = new LinkedHashSet<>(methods);
            tagged.addAll(loopBoundMethods);
            for (String signature : tagged) {
                // No body: every later pass skips it too.
                Body body = CausynthStaticFacts.activeBody(
                        CausynthStaticFacts.method(signature));
                if (body == null) continue;
                try {
                    tagOriginalUnits(snapshotUnits(body));
                } catch (RuntimeException failed) {
                    throw new IllegalStateException(
                            "ORIGINAL_UNIT_TAGGING_FAILED: " + signature
                                    + " is woven by this campaign and its "
                                    + "original units could not be numbered,"
                                    + " so no site of it names the same unit"
                                    + " the plan does", failed);
                }
            }
        }

        /** Freezes each LOOP_BODY_ROOT once, before tasks' bridges alter it. */
        private void freezeRootLoops() {
            for (InstrumentationPlan plan : campaign) {
                if (!plan.loopBodyRoot()) continue;
                String key = loopRootKey(plan);
                if (rootLoops.containsKey(key)) continue;
                SootMethod method = CausynthStaticFacts.method(
                        plan.rootLoopMethod());
                if (method == null || !method.isConcrete()) {
                    throw new IllegalStateException(
                            "Selected loop root is not a concrete method: "
                                    + plan.rootLoopMethod());
                }
                Body body = method.retrieveActiveBody();
                rootLoops.put(key, rootedLoop(body, method, plan));
            }
        }

        private CfgLoopControl.NaturalLoop rootLoop(
                InstrumentationPlan plan) {
            CfgLoopControl.NaturalLoop loop = rootLoops.get(loopRootKey(plan));
            if (loop == null) {
                throw new IllegalStateException(
                        "LOOP_BODY_ROOT_HEADER_UNAVAILABLE: "
                                + loopRootKey(plan));
            }
            return loop;
        }

        private String loopRootKey(InstrumentationPlan plan) {
            return SiteId.of(plan.rootLoopMethod(),
                    plan.rootLoopHeaderUnitIndex());
        }

    }

    /** Rewrites one campaign's deduplicated envelope once (PIPELINE §4). */
    private void instrumentConcolicCampaign(
            List<InstrumentationPlan> campaign) {
        HookCatalog refs = HookCatalog.concolic();
        CampaignEnvelope envelope = new CampaignEnvelope(campaign);
        envelope.tagSelectedBodies();
        // The campaign's loops, bounded once under its one policy.
        instrumentConcolicLoopBounds(envelope.loopBoundMethods,
                envelope.loopBound, envelope.fixedCountLoopSites, refs);
        instrumentConcolicCommunicationHandoffs(campaign, envelope.exports,
                refs);
        envelope.freezeRootLoops();
        // ONE entry per root hook group, however many planned occurrences
        // share it, and one enclosing entry per loop root: the replay offers
        // each invocation to every task of the group.
        Set<String> loopRoots = new LinkedHashSet<>();
        for (InstrumentationPlan plan : envelope.rootHooks.values()) {
            instrumentConcolicRegion(plan, refs, envelope,
                    plan.loopBodyRoot()
                            && loopRoots.add(plan.loopRootHookGroup()));
        }
        // ONE entry hook per skeleton root owns the index frame.
        instrumentSkeletonRegions(refs);
        instrumentConcolicConfiguredSourceCallContexts(
                envelope.configuredSourcePhaseSites.values(), refs);
        instrumentConcolicAccessorCallContexts(envelope.materializations,
                refs);
        instrumentConcolicObservedSites(envelope.materializations,
                refs);
        instrumentConcolicMethodArguments(envelope.materializations, refs);
        instrumentConcolicMaterializations(envelope, refs);
        instrumentConcolicBranches(envelope.methods, refs);
        // Same scope as the recording; LAST, to bracket every inner hook.
        instrumentApplicationScope(refs);
    }

    /** Opens every skeleton root's index region, as the recording does. */
    private void instrumentSkeletonRegions(HookCatalog refs) {
        Map<String, String> roots = RegionSkeletonInstrumentationSelection
                .regionRootsFromEnvironment();
        Set<SootMethod> entered = new LinkedHashSet<>();
        Set<String> rewritten = instrumentMethods(
                new ArrayList<>(roots.keySet()), "",
                (body, method, units, entry, lowerBound, receiver) -> {
                    // A second entry hook pushes a frame the recording lacks.
                    if (!entered.add(method)) {
                        throw new IllegalStateException(
                                "one method would receive two region entry "
                                        + "hooks: " + method.getSignature());
                    }
                    instrumentRegionEntry(body, method, units, entry,
                            lowerBound, receiver, refs,
                            roots.get(method.getSignature()));
                });
        LOG.info("Opened {} of {} skeleton region root(s) for the execution "
                + "index, one entry hook each; the one-entry-one-frame check "
                + "passed", rewritten.size(), roots.size());
    }

    /**
     * One region activation's index frame, owned by a local token so each
     * entry (recursion included) closes its own frame.
     */
    private void instrumentRegionEntry(Body body, SootMethod method,
                                       List<Unit> originalUnits,
                                       Unit insertionPoint, Unit lowerBound,
                                       Value receiver, HookCatalog refs,
                                       String regionId) {
        Local entryToken = newTraceLocal(body, LongType.v(),
                "$causynthRegionEntry");
        // The entry hook IS the token's store; no `= 0L` pre-store.
        List<Unit> entry = new ArrayList<>();
        refs.bracket(entry, entryToken, Hook.ENTER_REGION_ENTRY,
                StringConstant.v(regionId),
                StringConstant.v(method.getSignature()), receiver);
        insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);
        bracketReturns(body, originalUnits,
                instrumentableFrom(originalUnits, lowerBound), refs,
                Hook.EXIT_REGION_ENTRY, entryToken);
        // The handler reads the token: the trap opens after its store.
        addThrowHandler(body, afterWovenPrologue(body, entry), refs,
                Hook.THROW_REGION_ENTRY, "$causynthRegionEntryThrown",
                entryToken);
    }

    /**
     * Inserts the region hooks of one root hook group at its selected root,
     * and, with {@code enclosingInvocation}, its loop root's enclosing entry.
     */
    private void instrumentConcolicRegion(InstrumentationPlan plan,
                                          HookCatalog refs,
                                          CampaignEnvelope envelope,
                                          boolean enclosingInvocation) {
        String signature = plan.rootMethod();
        SootMethod replayEntry = envelope.replayEntries.get(plan);
        String replayEntrySignature = replayEntry.getSignature();
        try {
            // Once-only-root: a loop-rooted region's frame is one iteration.
            SootMethod method = plan.loopBodyRoot()
                    ? CausynthStaticFacts.method(plan.rootLoopMethod())
                    : replayEntry;
            if (method == null || !method.isConcrete()) {
                throw new IllegalStateException(
                        "Selected concolic root is not a concrete method: "
                                + (plan.loopBodyRoot()
                                ? plan.rootLoopMethod()
                                : replayEntrySignature));
            }
            Body body = method.retrieveActiveBody();
            List<Unit> originalUnits = snapshotUnits(body);
            tagOriginalUnits(originalUnits);
            CfgLoopControl.NaturalLoop rootLoop = plan.loopBodyRoot()
                    ? envelope.rootLoop(plan) : null;
            CfgLoopControl.BodyEntry loopBodyEntry = rootLoop == null
                    ? null : loopBodyEntry(body, rootLoop,
                    plan.rootLoopControlSites(),
                    plan.rootLoopDemandedUnitIndex());
            Unit insertionPoint = rootLoop == null
                    ? safeInstrumentationEntry(body, method)
                    : loopBodyEntry.target;
            if (method.isConstructor() && insertionPoint == null) {
                throw new IllegalStateException(
                        "Selected constructor root has no initialized-this "
                                + "instrumentation point: "
                                + replayEntrySignature);
            }
            Value receiver = receiverOrNull(body, method);
            Local token = newTraceLocal(body, LongType.v(),
                    "$causynthRegionToken");
            List<Unit> entry = new ArrayList<>();
            entry.add(Jimple.v().newAssignStmt(token, LongConstant.v(0L)));
            // A loop body binds no parameters: empty argument array.
            int rootArgumentCount = rootLoop == null
                    ? method.getParameterCount() : 0;
            Local rootArguments = rootArguments(body, method,
                    rootArgumentCount, "$causynthRootArguments", entry);
            // Admission compares workload objects: not observed.
            Unit regionStart = refs.bracket(entry, token,
                    Hook.ENTER_REGION_FRAME,
                    StringConstant.v(plan.rootHookGroup()),
                    StringConstant.v(signature), receiver, rootArguments);
            for (int index = 0; index < rootArgumentCount; index++) {
                Value parameter = parameterLocal(body, index);
                if (parameter == null) continue;
                materializeParameter(body, parameter, index, entry,
                        token, "$causynthArgument",
                        Hook.MATERIALIZE_ARGUMENT, Hook.SYMBOLIZE_ARGUMENT,
                        refs);
            }
            if (rootLoop == null) {
                insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);
                bracketReturns(body, originalUnits, 0, refs,
                        Hook.EXIT_REGION_FRAME,
                        StringConstant.v(plan.rootHookGroup()),
                        StringConstant.v(signature));
            } else {
                insertLoopBodyEntry(body, method,
                        rootLoop, loopBodyEntry, entry,
                        rootLoop.identity(method));
                // One iteration is one activation; backedges close it too.
                insertLoopBodyRegionExits(body, method, rootLoop, plan,
                        signature, refs);
            }
            addThrowHandler(body, regionStart, refs,
                    Hook.THROW_REGION_FRAME, "$causynthRegionThrown",
                    StringConstant.v(plan.rootHookGroup()),
                    StringConstant.v(signature));
            if (enclosingInvocation) {
                instrumentLoopRootInvocationContext(plan, replayEntry, refs);
            }
        } catch (RuntimeException exception) {
            throw new IllegalStateException(
                    "Could not instrument selected concolic region root "
                            + signature + " at replay entry "
                            + replayEntrySignature, exception);
        }
        LOG.info("Instrumented symbolic-region root {} at replay entry {} "
                        + "for concolic replay; loop bodies bounded at {} "
                        + "iterations",
                signature, replayEntrySignature,
                plan.loopBound().maxBackedgeTraversals());
    }

    /**
     * Frames the enclosing invocation of a LOOP_BODY_ROOT, whose ordinal is
     * stable when replay changes the iteration count; per-iteration
     * activations open only inside this call.
     */
    private void instrumentLoopRootInvocationContext(
            InstrumentationPlan plan, SootMethod method, HookCatalog refs) {
        if (!method.isConcrete()) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT enclosing method is unavailable: "
                            + plan.rootMethod());
        }
        Body body = method.retrieveActiveBody();
        Unit insertionPoint = safeInstrumentationEntry(body, method);
        if (insertionPoint == null) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT enclosing method has no safe entry: "
                            + plan.rootMethod());
        }
        List<Unit> originalUnits = snapshotUnits(body);
        Local contextToken = newTraceLocal(body, LongType.v(),
                "$causynthLoopRootContext");
        List<Unit> entry = new ArrayList<>();
        entry.add(Jimple.v().newAssignStmt(contextToken,
                LongConstant.v(0L)));
        Local rootArguments = rootArguments(body, method,
                method.getParameterCount(), "$causynthLoopRootArguments",
                entry);
        Unit enter = refs.bracket(entry, contextToken,
                Hook.ENTER_LOOP_ROOT_INVOCATION_FRAME,
                StringConstant.v(plan.loopRootHookGroup()),
                StringConstant.v(plan.rootMethod()),
                receiverOrNull(body, method), rootArguments);
        insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);
        bracketReturns(body, originalUnits, 0, refs,
                Hook.EXIT_LOOP_ROOT_INVOCATION_FRAME, contextToken);
        addThrowHandler(body, enter, refs,
                Hook.THROW_LOOP_ROOT_INVOCATION_FRAME,
                "$causynthLoopRootThrown", contextToken);
    }

    /**
     * The natural loop whose header is the plan's {@code headerUnitIndex}.
     * A missing header is a refusal, never a fall back to the method entry
     * (one frame too high).
     */
    private static CfgLoopControl.NaturalLoop rootedLoop(
            Body body, SootMethod method, InstrumentationPlan plan) {
        int headerIndex = plan.rootLoopHeaderUnitIndex();
        // An inserted loop counter may now be the dominance header, so take
        // the innermost loop whose members hold the original header unit.
        Unit original = originalUnit(body, headerIndex);
        CfgLoopControl.NaturalLoop found = null;
        int foundPosition = -1;
        if (original != null) {
            List<Unit> order = snapshotUnits(body);
            // Proved on the CURRENT body: bridged backedges have no original
            // index, so units are matched by identity, not index.
            final Map<Unit, Integer> positions = new IdentityHashMap<>();
            for (int i = 0; i < order.size(); i++) {
                positions.put(order.get(i), i);
            }
            for (CfgLoopControl.NaturalLoop loop : CfgLoopControl.naturalLoops(
                    CfgLoopControl.loopCfg(body),
                    unit -> positions.getOrDefault(unit, -1))) {
                if (loop.header != original
                        && !loop.members().contains(original)) {
                    continue;
                }
                int position = positions.get(loop.header);
                if (position <= positions.get(original)
                        && position > foundPosition) {
                    found = loop;
                    foundPosition = position;
                }
            }
        }
        if (found == null) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_HEADER_UNAVAILABLE: "
                            + SiteId.of(method.getSignature(), headerIndex));
        }
        return found;
    }

    /**
     * Where a loop-body frame opens: {@link CfgLoopControl#bodyEntry} on the
     * frozen loop, the one placement SEED asked when it chose the loop
     * (StaticProgram#loopBodyRoot), its control edges mapped to the body's
     * current ones.  A unit it cannot place is refused by name.
     */
    private static CfgLoopControl.BodyEntry loopBodyEntry(
            Body body, CfgLoopControl.NaturalLoop loop,
            Set<String> controlSites, int demandedUnitIndex) {
        String loopId = loop.identity(body.getMethod());
        if (controlSites.isEmpty() || demandedUnitIndex < 0) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: " + loopId
                            + " has no declared control sites and demanded "
                            + "unit");
        }
        ResolvedLoopControls controls = resolveLoopControls(body, loop,
                controlSites, "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: ");
        Unit demanded = stableLoopUnit(body, demandedUnitIndex,
                controls.plannedIndices, controls.units);
        CfgLoopControl.BodyEntry entry = CfgLoopControl.bodyEntry(loop,
                controls.units, demanded);
        if (entry == null) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: " + loopId
                            + " places no iteration frame at demanded unit u"
                            + demandedUnitIndex + ", which SEED's "
                            + "bodyEntryCallUnits stated it could");
        }
        if (entry.target == loop.header) return entry;
        List<CfgLoopControl.Edge> current = new ArrayList<>();
        for (CfgLoopControl.Edge edge : entry.edges) {
            current.add(currentLoopBoundaryEdge(body, edge, loopId, false));
        }
        return new CfgLoopControl.BodyEntry(entry.target, current);
    }

    /** Maps a planned unit through stable loop-control ordinals. */
    private static Unit stableLoopUnit(
            Body body, int plannedIndex, List<Integer> plannedControls,
            List<Unit> currentControls) {
        int nearestDistance = Integer.MAX_VALUE;
        int shift = 0;
        for (int index = 0; index < plannedControls.size(); index++) {
            int plannedControl = plannedControls.get(index);
            int distance = Math.abs(plannedControl - plannedIndex);
            if (distance >= nearestDistance) continue;
            nearestDistance = distance;
            shift = originalUnitIndex(currentControls.get(index))
                    - plannedControl;
        }
        return originalUnit(body, plannedIndex + shift);
    }

    /** Current CFG identities for a frozen loop's ordered control branches. */
    private static ResolvedLoopControls resolveLoopControls(
            Body body, CfgLoopControl.NaturalLoop loop,
            Set<String> controlSites, String refusal) {
        String loopId = loop.identity(body.getMethod());
        List<Integer> planned = new ArrayList<>();
        String sitePrefix = body.getMethod().getSignature() + "#u";
        for (String site : controlSites) {
            if (site == null || !site.startsWith(sitePrefix)) {
                throw new IllegalStateException(refusal + loopId
                        + " has a control site outside its method: " + site);
            }
            try {
                planned.add(Integer.parseInt(
                        site.substring(sitePrefix.length())));
            } catch (NumberFormatException malformed) {
                throw new IllegalStateException(refusal + loopId
                        + " has malformed control site " + site, malformed);
            }
        }
        Collections.sort(planned);

        // Unit indices can shift between Soot lowerings of one class; branch
        // order and CFG role are the durable anchors.  A control is any
        // branch leaving the loop, as the catalog's guards are
        // (CfgLoopControl#retainedLoops): an if, or a switch whose default
        // throws (PBHelperClient.convertEditsResponse, sweep a40h2).
        Set<Unit> exits = Collections.newSetFromMap(
                new IdentityHashMap<Unit, Boolean>());
        for (CfgLoopControl.Edge edge : loop.exitEdges()) {
            if (CausynthBranchShape.from(body, edge.source) != null
                    && originalUnitIndex(edge.source) >= 0) {
                exits.add(edge.source);
            }
        }
        List<Unit> current = new ArrayList<>();
        for (Unit unit : body.getUnits()) {
            if (exits.contains(unit)) current.add(unit);
        }
        if (current.size() != planned.size()) {
            List<Integer> currentIndices = new ArrayList<>();
            for (Unit unit : current) {
                currentIndices.add(originalUnitIndex(unit));
            }
            throw new IllegalStateException(refusal + loopId + " declares "
                    + planned.size() + " controls but its current CFG proves "
                    + current.size() + " exit controls; planned=" + planned
                    + ", current=" + currentIndices);
        }
        return new ResolvedLoopControls(planned, current);
    }

    private static final class ResolvedLoopControls {
        private final List<Integer> plannedIndices;
        private final List<Unit> units;

        private ResolvedLoopControls(List<Integer> plannedIndices,
                                     List<Unit> units) {
            this.plannedIndices = plannedIndices;
            this.units = units;
        }
    }

    /**
     * Finds the current first or last physical edge on one frozen CFG edge.
     * Region bridges may split it repeatedly, but may not branch, detach, or
     * change its original endpoint.
     */
    private static CfgLoopControl.Edge currentLoopBoundaryEdge(
            Body body, CfgLoopControl.Edge edge, String loopId,
            boolean first) {
        if (!body.getUnits().contains(edge.source)
                || !body.getUnits().contains(edge.target)) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_EDGE_UNAVAILABLE: " + loopId
                            + " has a detached frozen control edge");
        }
        List<CfgLoopControl.Edge> matches = new ArrayList<>();
        for (Unit successor : normalSuccessors(body, edge.source)) {
            Unit prior = edge.source;
            Unit current = successor;
            Unit firstTarget = successor;
            Set<Unit> visited = Collections.newSetFromMap(
                    new IdentityHashMap<Unit, Boolean>());
            while (current != edge.target) {
                if (!body.getUnits().contains(current)
                        || !visited.add(current)
                        || originalUnitIndex(current) >= 0) {
                    current = null;
                    break;
                }
                List<Unit> successors = normalSuccessors(body, current);
                if (successors.size() != 1) {
                    current = null;
                    break;
                }
                prior = current;
                current = successors.get(0);
            }
            if (current == edge.target) {
                matches.add(first
                        ? new CfgLoopControl.Edge(edge.source, firstTarget)
                        : new CfgLoopControl.Edge(prior, current));
            }
        }
        matches = deduplicateEdges(matches);
        if (matches.size() != 1) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_EDGE_UNAVAILABLE: " + loopId
                            + " no longer has exactly one transparent path "
                            + "for its frozen control edge");
        }
        return matches.get(0);
    }

    /**
     * Inserts a straight-line bridge before the entry's unit, entered by
     * each of its control edges (every edge into a header, preheader and
     * latches alike); any other edge into a body unit keeps its old path.
     */
    private static void insertLoopBodyEntry(
            Body body, SootMethod method, CfgLoopControl.NaturalLoop loop,
            CfgLoopControl.BodyEntry selected, List<Unit> entry,
            String loopId) {
        Unit target = selected.target;
        boolean headerEntry = target == loop.header;
        List<UnitBox> matchingTargets = new ArrayList<>();
        Unit fallThroughSource = null;
        for (CfgLoopControl.Edge edge : selected.edges) {
            for (UnitBox targetBox : edge.source.getUnitBoxes()) {
                if (targetBox.getUnit() == target) {
                    matchingTargets.add(targetBox);
                }
            }
            if (edge.source.fallsThrough()
                    && body.getUnits().getSuccOf(edge.source) == target) {
                fallThroughSource = edge.source;
            }
        }
        // A header entry takes every edge into the header, whichever one
        // the selection named.
        if (!headerEntry && matchingTargets.isEmpty()
                && fallThroughSource == null) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: " + loopId
                            + " no longer has its selected body edges in "
                            + method.getSignature());
        }

        Unit first = entry.get(0);
        if (headerEntry) {
            // Preheader and latches all enter the header: every normal entry
            // opens an activation; trap UnitBoxes are not rewritten.
            matchingTargets.clear();
            for (Unit source : body.getUnits()) {
                for (UnitBox targetBox : source.getUnitBoxes()) {
                    if (targetBox.getUnit() == target) {
                        matchingTargets.add(targetBox);
                    }
                }
            }
        } else if (fallThroughSource == null) {
            Unit lexicalPredecessor = body.getUnits().getPredOf(target);
            if (lexicalPredecessor != null
                    && lexicalPredecessor.fallsThrough()
                    && body.getUnits().getSuccOf(lexicalPredecessor)
                    == target) {
                // Only the selected UnitBoxes enter the activation; an
                // unrelated fallthrough keeps its old path.
                body.getUnits().insertBeforeNoRedirect(
                        Jimple.v().newGotoStmt(target), target);
            }
        }
        insertBeforeOrAppendNoRedirect(body, target, entry);
        for (UnitBox targetBox : matchingTargets) {
            targetBox.setUnit(first);
        }
        if (fallThroughSource != null
                && body.getUnits().getSuccOf(fallThroughSource) != first) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: " + loopId
                            + " could not preserve its body fallthrough in "
                            + method.getSignature());
        }
    }

    /** Normal successors only; trap-handler edges never identify loop entry. */
    private static List<Unit> normalSuccessors(Body body, Unit source) {
        Set<Unit> successors = Collections.newSetFromMap(
                new IdentityHashMap<Unit, Boolean>());
        if (source.fallsThrough()) {
            Unit fallThrough = body.getUnits().getSuccOf(source);
            if (fallThrough != null) successors.add(fallThrough);
        }
        for (UnitBox target : source.getUnitBoxes()) {
            if (target.getUnit() != null) successors.add(target.getUnit());
        }
        return new ArrayList<>(successors);
    }

    /**
     * Every edge ending one iteration: all backedges, plus the normal exits
     * the control sites select.  A dropped backedge yields one activation
     * per thread, not one per iteration (IDENTITY §1).
     */
    private static List<CfgLoopControl.Edge> loopBodyClosingEdges(
            SootMethod method, CfgLoopControl.NaturalLoop loop,
            Set<String> controlSites) {
        Body body = method.retrieveActiveBody();
        List<CfgLoopControl.Edge> closing = new ArrayList<>();
        for (CfgLoopControl.Backedge backedge : loop.backedges) {
            closing.add(currentLoopBoundaryEdge(body,
                    new CfgLoopControl.Edge(backedge.source,
                            backedge.target), loop.identity(method), true));
        }
        if (controlSites.isEmpty()) {
            for (CfgLoopControl.Edge exit
                    : deduplicateEdges(loop.exitEdges())) {
                closing.add(currentLoopBoundaryEdge(body, exit,
                        loop.identity(method), true));
            }
            return deduplicateEdges(closing);
        }

        // Each control's exits: an if's one, a switch's every case leaving
        // the loop (resolveLoopControls proved each control has one).
        ResolvedLoopControls controls = resolveLoopControls(body, loop,
                controlSites, "LOOP_BODY_ROOT_EXIT_UNAVAILABLE: ");
        for (CfgLoopControl.Edge exit : loop.exitEdges()) {
            if (controls.units.contains(exit.source)) {
                closing.add(currentLoopBoundaryEdge(body, exit,
                        loop.identity(method), true));
            }
        }
        return deduplicateEdges(closing);
    }

    /** Closes a loop-body region on every edge that ends one iteration. */
    private void insertLoopBodyRegionExits(
            Body body, SootMethod method, CfgLoopControl.NaturalLoop loop,
            InstrumentationPlan plan, String rootMethod, HookCatalog refs) {
        String loopId = loop.identity(method);
        int installed = 0;
        for (CfgLoopControl.Edge edge : loopBodyClosingEdges(method, loop,
                plan.rootLoopControlSites())) {
            List<Unit> bridge = new ArrayList<>();
            refs.bracket(bridge, Hook.EXIT_REGION_FRAME,
                    StringConstant.v(plan.rootHookGroup()),
                    StringConstant.v(rootMethod));
            // On the current FIRST edge of the frozen boundary, so later
            // tasks' closes prepend and the activation stack stays LIFO.
            redirectEdge(body, method, edge.source, edge.target, bridge,
                    "Could not close loop-body region on ", loopId);
            installed++;
        }
        if (installed == 0) {
            throw new IllegalStateException("LOOP_BODY_ROOT_EXIT_UNAVAILABLE: "
                    + loopId);
        }
    }

    /**
     * A new {@code Object[count]} holding the first {@code count} parameters
     * that are references: the argument array a frame hook takes.
     */
    private static Local rootArguments(Body body, SootMethod method,
                                       int count, String localName,
                                       List<Unit> units) {
        Local arguments = newTraceLocal(body,
                ArrayType.v(RefType.v("java.lang.Object"), 1), localName);
        units.add(Jimple.v().newAssignStmt(arguments,
                Jimple.v().newNewArrayExpr(RefType.v("java.lang.Object"),
                        IntConstant.v(count))));
        for (int index = 0; index < count; index++) {
            Type parameterType = method.getParameterType(index);
            if (!(parameterType instanceof RefType)
                    && !(parameterType instanceof ArrayType)) {
                continue;
            }
            Value parameter = parameterLocal(body, index);
            if (parameter == null) continue;
            units.add(Jimple.v().newAssignStmt(
                    Jimple.v().newArrayRef(arguments, IntConstant.v(index)),
                    objectArg(body, parameter, units)));
        }
        return arguments;
    }

    /**
     * Inserts {@code hook(args)}, bracketed, before every return among the
     * original units from index {@code from} on (none when it is -1).
     */
    private static void bracketReturns(Body body, List<Unit> originalUnits,
                                       int from, HookCatalog refs,
                                       Hook hook, Value... args) {
        for (Unit unit : originalReturns(originalUnits, from)) {
            List<Unit> exit = new ArrayList<>();
            refs.bracket(exit, hook, args);
            insertBeforeSequence(body, unit, exit);
        }
    }

    /** The original returns from index {@code from} on (none when -1). */
    static List<Unit> originalReturns(List<Unit> originalUnits,
                                              int from) {
        List<Unit> returns = new ArrayList<>();
        for (int index = from; index >= 0 && index < originalUnits.size();
                index++) {
            Unit unit = originalUnits.get(index);
            if (unit instanceof ReturnStmt || unit instanceof ReturnVoidStmt) {
                returns.add(unit);
            }
        }
        return returns;
    }

    /** Materializes and symbolizes one parameter local where it is bound. */
    private static void materializeParameter(
            Body body, Value parameter, int index, List<Unit> units,
            Value owner, String localPrefix, Hook materialize, Hook symbolize,
            HookCatalog refs) {
        Value primitiveValue = primitiveValueString(body, parameter, units);
        if (PrimitiveWrapper.forType(parameter.getType()) != null) {
            addPrimitiveRoundTrip(body, parameter, units, localPrefix, refs,
                    materialize, boxed -> new Value[]{owner,
                            IntConstant.v(index), boxed, primitiveValue});
            return;
        }
        Value objectValue = objectArg(body, parameter, units);
        Local modeled = newTraceLocal(body, RefType.v("java.lang.Object"),
                localPrefix + "Model");
        refs.bracket(units, modeled, materialize, owner,
                IntConstant.v(index), objectValue, primitiveValue);
        Value converted = parameter.getType() instanceof RefType
                && "java.lang.Object".equals(((RefType)
                parameter.getType()).getClassName())
                ? modeled : Jimple.v().newCastExpr(modeled,
                parameter.getType());
        units.add(Jimple.v().newAssignStmt(parameter, converted));
        refs.bracket(units, symbolize, owner, IntConstant.v(index),
                parameter, primitiveValue);
    }

    /**
     * The wire's captures: each attach a planned consumer declares, and
     * every export of the program ({@code exports}), so a producer no task
     * plans still states the endpoint its delivery pairs with.
     */
    private void instrumentConcolicCommunicationHandoffs(
            List<InstrumentationPlan> campaign,
            List<CommunicationHandoffSpec> exports, HookCatalog refs) {
        Map<String, CommunicationHandoffSpec> sites = new LinkedHashMap<>();
        List<CommunicationHandoffSpec> declared = new ArrayList<>(exports);
        for (InstrumentationPlan plan : campaign) {
            declared.addAll(plan.communicationHandoffs());
        }
        for (CommunicationHandoffSpec site : declared) {
            sites.putIfAbsent(site.side() + "\n" + site.portId()
                    + "\n" + site.siteId() + "\n"
                    + site.captureKind() + "\n" + site.argumentIndex(),
                    site);
        }
        int exported = 0;
        for (CommunicationHandoffSpec site : sites.values()) {
            instrumentCommunicationHandoff(site, refs);
            if (site.outgoing()) exported++;
        }
        LOG.info("Wove {} export(s), every region skeleton's, and {} "
                + "attach(es) the plan declares", exported,
                sites.size() - exported);
        Map<String, Boolean> frames = new LinkedHashMap<>();
        for (CommunicationHandoffSpec site : sites.values()) {
            if (site.frameMethod().isEmpty()) continue;
            Boolean outgoing = frames.get(site.frameMethod());
            if (outgoing != null && outgoing != site.outgoing()) {
                throw new IllegalStateException(
                        "COMMUNICATION_FRAME_SIDE_CONFLICT: "
                                + site.frameMethod());
            }
            frames.put(site.frameMethod(), site.outgoing());
        }
        for (Map.Entry<String, Boolean> frame : frames.entrySet()) {
            instrumentCommunicationFrame(frame.getKey(), frame.getValue(),
                    refs);
        }
    }

    /**
     * Brackets the one call that builds (or, mirrored, decodes) one message
     * instance, so the k-th frame means the same on both sides and
     * same-shaped groups do not run together.
     */
    private void instrumentCommunicationFrame(String frameMethod,
                                              boolean outgoing,
                                              HookCatalog refs) {
        Body body = selectedBody(frameMethod, "COMMUNICATION_FRAME_METHOD",
                frameMethod);
        SootMethod method = body.getMethod();
        Unit insertionPoint = safeInstrumentationEntry(body, method);
        if (insertionPoint == null) {
            throw new IllegalStateException(
                    "COMMUNICATION_FRAME_METHOD_HAS_NO_SAFE_ENTRY: "
                            + frameMethod);
        }
        Hook open = outgoing ? Hook.PUSH_OUTBOUND_MESSAGE_FRAME
                : Hook.PUSH_INBOUND_MESSAGE_FRAME;
        Hook close = outgoing ? Hook.POP_OUTBOUND_MESSAGE_FRAME
                : Hook.POP_INBOUND_MESSAGE_FRAME;
        List<Unit> originalUnits = snapshotUnits(body);
        Unit opened = invoke(refs.ref(open));
        insertBeforeOrAppendNoRedirect(body, insertionPoint,
                Collections.singletonList(opened));
        for (Unit unit : originalReturns(originalUnits, 0)) {
            body.getUnits().insertBefore(invoke(refs.ref(close)), unit);
        }
        // Close on throw too, or the frame swallows later messages.
        appendCatchAll(body, opened, "$causynthMessageFrameThrown",
                (units, caught) -> emit(units, refs.ref(close)));
    }

    private void instrumentCommunicationHandoff(
            CommunicationHandoffSpec site, HookCatalog refs) {
        Body body = selectedBody(site.method(),
                "COMMUNICATION_HANDOFF_METHOD", site.portId());
        SootMethod method = body.getMethod();
        String capture = site.captureKind();
        if (CommunicationCatalogContract.CAPTURE_METHOD_PARAMETER.equals(
                capture)) {
            if (site.argumentIndex() >= method.getParameterCount()) {
                throw handoffFailure(site, "PARAMETER_UNAVAILABLE");
            }
            List<Unit> units = new ArrayList<>();
            addCommunicationHandoff(body,
                    body.getParameterLocal(site.argumentIndex()),
                    method.getParameterType(site.argumentIndex()), site,
                    units, refs);
            insertBeforeOrAppendNoRedirect(body,
                    safeInstrumentationEntry(body, method), units);
            return;
        }
        if (CommunicationCatalogContract.CAPTURE_METHOD_RETURN.equals(
                capture)) {
            int returns = 0;
            for (Unit unit : snapshotUnits(body)) {
                if (!(unit instanceof ReturnStmt)) continue;
                returns++;
                ReturnStmt returned = (ReturnStmt) unit;
                List<Unit> units = new ArrayList<>();
                Value value = addCommunicationHandoff(body, returned.getOp(),
                        method.getReturnType(), site, units, refs);
                if (!site.outgoing()) returned.setOp(value);
                insertBeforeSequence(body, unit, units);
            }
            if (returns == 0) throw handoffFailure(site, "RETURN_UNAVAILABLE");
            return;
        }
        Stmt cut = cutInvoke(body, site);
        if (CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT.equals(
                capture)) {
            InvokeExpr invoke = cut.getInvokeExpr();
            if (site.argumentIndex() >= invoke.getArgCount()) {
                throw handoffFailure(site, "ARGUMENT_UNAVAILABLE");
            }
            List<Unit> units = new ArrayList<>();
            Value value = addCommunicationHandoff(body,
                    invoke.getArg(site.argumentIndex()),
                    invoke.getMethodRef().parameterType(site.argumentIndex()),
                    site, units, refs);
            if (!site.outgoing()) invoke.setArg(site.argumentIndex(), value);
            insertBeforeSequence(body, cut, units);
            return;
        }
        if (!(cut instanceof DefinitionStmt)) {
            throw handoffFailure(site, "CALL_RETURN_UNAVAILABLE");
        }
        Value target = ((DefinitionStmt) cut).getLeftOp();
        List<Unit> units = new ArrayList<>();
        Value value = addCommunicationHandoff(body, target,
                cut.getInvokeExpr().getMethodRef().returnType(), site,
                units, refs);
        if (!site.outgoing() && value != target) {
            units.add(Jimple.v().newAssignStmt(target, value));
        }
        insertAfterSequence(body, cut, units);
    }

    private static Stmt cutInvoke(Body body, CommunicationHandoffSpec site) {
        Stmt selected = null;
        for (Unit unit : snapshotUnits(body)) {
            if (originalUnitIndex(unit) != site.unitIndex()
                    || !(unit instanceof Stmt)) continue;
            Stmt candidate = (Stmt) unit;
            if (!candidate.containsInvokeExpr()
                    || !site.declaredCallee().equals(candidate.getInvokeExpr()
                    .getMethodRef().getSignature())) continue;
            if (selected != null) throw handoffFailure(site,
                    "CALL_SITE_NOT_UNIQUE");
            selected = candidate;
        }
        if (selected == null) throw handoffFailure(site,
                "CALL_SITE_UNAVAILABLE");
        return selected;
    }

    private Value addCommunicationHandoff(
            Body body, Value value, Type declaredType,
            CommunicationHandoffSpec site, List<Unit> units,
            HookCatalog refs) {
        if (site.outgoing()) {
            String[] leaf = carrierLeaf(declaredType);
            Local carrier = newCarrierLeaf(body, leaf, value, units);
            emit(units, refs.ref(Hook.EXPORT_COMMUNICATION_LEAF),
                    StringConstant.v(site.portId()), carrier,
                    StringConstant.v(leaf[0]), StringConstant.v(leaf[1]));
            return value;
        }
        Value target = value;
        if (!(target instanceof Local)) {
            Local local = newTraceLocal(body, declaredType,
                    "$causynthHandoffValue");
            units.add(Jimple.v().newAssignStmt(local,
                    immediateValue(body, value, units)));
            target = local;
        }
        addCommunicationLeafAttach(body, target, declaredType, site, units,
                refs);
        return target;
    }

    private static IllegalStateException handoffFailure(
            CommunicationHandoffSpec site, String reason) {
        return new IllegalStateException("COMMUNICATION_HANDOFF_" + reason
                + ": " + site.portId());
    }

    /** Allocates one carrier and stores {@code value} on its typed leaf. */
    private static Local newCarrierLeaf(Body body, String[] leaf,
                                        Value value, List<Unit> units) {
        SootClass owner = carrierClass();
        RefType type = RefType.v(HANDOFF_LEAF_CARRIER_CLASS);
        Local carrier = newTraceLocal(body, type, "$causynthHandoffCarrier");
        units.add(Jimple.v().newAssignStmt(carrier,
                Jimple.v().newNewExpr(type)));
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(carrier,
                        Scene.v().makeMethodRef(owner, "<init>",
                                Collections.<Type>emptyList(),
                                VoidType.v(), false))));
        units.add(Jimple.v().newAssignStmt(
                Jimple.v().newInstanceFieldRef(carrier,
                        Scene.v().makeFieldRef(owner, leaf[0],
                                carrierLeafType(value.getType()), false)),
                immediateValue(body, value, units)));
        return carrier;
    }

    /** Reads one carrier leaf back into the receiving frame's own value. */
    private static Unit readCarrierLeaf(Local carrier, String[] leaf,
                                        Value target) {
        return Jimple.v().newAssignStmt(target,
                Jimple.v().newInstanceFieldRef(carrier,
                        Scene.v().makeFieldRef(carrierClass(), leaf[0],
                                carrierLeafType(target.getType()), false)));
    }

    /** The carrier field and descriptor one Jimple type crosses on. */
    private static String[] carrierLeaf(Type type) {
        PrimitiveWrapper wrapper = PrimitiveWrapper.forType(type);
        return wrapper == null ? new String[]{"o", "Ljava/lang/Object;"}
                : new String[]{wrapper.leafField, wrapper.descriptor};
    }

    /** The carrier's declared field type for one crossing value. */
    private static Type carrierLeafType(Type type) {
        return type instanceof PrimType ? type
                : RefType.v("java.lang.Object");
    }

    private static final String HANDOFF_LEAF_CARRIER_CLASS =
            CONCOLIC_REGION_RUNTIME_CLASS + "$HandoffLeafCarrier";

    private static SootClass carrierClass() {
        return phantomClass(HANDOFF_LEAF_CARRIER_CLASS);
    }

    private void addCommunicationLeafAttach(
            Body body, Value target, Type declaredType,
            CommunicationHandoffSpec site, List<Unit> units,
            HookCatalog refs) {
        Type valueType = target.getType();
        String[] leaf = carrierLeaf(declaredType);
        Local carrier = newCarrierLeaf(body, leaf, target, units);
        emit(units, refs.ref(Hook.ATTACH_COMMUNICATION_LEAF),
                StringConstant.v(site.portId()), carrier,
                StringConstant.v(leaf[0]), StringConstant.v(leaf[1]));
        if (declaredType instanceof PrimType
                || "java.lang.Object".equals(valueType.toString())) {
            units.add(readCarrierLeaf(carrier, leaf, target));
            return;
        }
        Local attached = newTraceLocal(body, RefType.v("java.lang.Object"),
                "$causynthHandoffLeaf");
        units.add(readCarrierLeaf(carrier, leaf, attached));
        units.add(Jimple.v().newAssignStmt(target,
                Jimple.v().newCastExpr(attached, valueType)));
    }

    /**
     * Restores the recording's exact site identity around configured
     * sources (SYMBOL-SCOPE §4.3): a tree's hook call is bracketed as the
     * recording saw it; before the engine's configuration read the weave
     * puts the hook call a tree would have carried, under the same context.
     */
    private void instrumentConcolicConfiguredSourceCallContexts(
            Collection<ConfiguredSourcePhaseContract.Occurrence> phases,
            HookCatalog refs) {
        for (ConfiguredSourcePhaseContract.Occurrence phase : phases) {
            Body body = selectedBody(phase.declarationMethod(),
                    "CONFIGURED_SOURCE_PHASE_METHOD", phase.siteId());
            if (phase.category() == RootCategory.CONFIG) {
                instrumentConfigurationRead(body, phase, refs);
                continue;
            }
            Stmt selected = originalCall(body, phase.declarationUnitIndex(),
                    phase.siteId(), "CONFIGURED_SOURCE_PHASE_SITE_NOT_UNIQUE",
                    "CONFIGURED_SOURCE_PHASE_CALL_NOT_FOUND");
            requireCallee(selected, phase.runtimeDeclaredCallee(),
                    "CONFIGURED_SOURCE_PHASE_CALLEE_MISMATCH", phase.siteId());

            Local invocationId = newTraceLocal(body, LongType.v(),
                    "$causynthSourcePhaseInvocation");
            List<Unit> before = new ArrayList<>();
            before.add(Jimple.v().newAssignStmt(invocationId,
                    LongConstant.v(0L)));
            emit(before, refs.ref(Hook.PAUSE_OBSERVATION));
            emit(before, invocationId,
                    refs.ref(Hook.ENTER_CONFIGURED_SOURCE_PHASE_SITE),
                    StringConstant.v(phase.declarationMethod()),
                    IntConstant.v(phase.declarationUnitIndex()),
                    StringConstant.v(phase.runtimeDeclaredCallee()));
            insertBeforeSequence(body, selected, before);

            List<Unit> after = new ArrayList<>();
            Value returnValue = runtimeCallSiteReturnValue(
                    selected, selected.getInvokeExpr());
            Value returnObject = objectArg(body, returnValue, after);
            Value primitiveReturn = primitiveValueString(
                    body, returnValue, after);
            Unit normalExit = invoke(refs.ref(Hook.EXIT_CONFIGURED_SOURCE_PHASE_SITE),
                    invocationId, returnObject, primitiveReturn);
            after.add(normalExit);
            emit(after, refs.ref(Hook.RESUME_OBSERVATION));
            List<Unit> thrown = new ArrayList<>();
            emit(thrown, refs.ref(Hook.THROW_CONFIGURED_SOURCE_PHASE_SITE),
                    invocationId);
            emit(thrown, refs.ref(Hook.RESUME_OBSERVATION));
            // The source declaration is bookkeeping: its helper branches must
            // not enter the workload path condition.
            guardCall(body, selected, after, normalExit, thrown,
                    "$causynthSourcePhaseThrown");
        }
    }

    /**
     * Before one configuration read ({@code x = owner.field}): the site's
     * context opened, the configuration read on its owner ({@code
     * ConcolicRegionRuntime.readConfiguration}, which plants the world's
     * value and mints), the context closed.  The read then loads what the
     * mint left.  The hooks never throw.
     */
    private static void instrumentConfigurationRead(
            Body body, ConfiguredSourcePhaseContract.Occurrence phase,
            HookCatalog refs) {
        Stmt read = originalRead(body, phase);
        Value owner = ((InstanceFieldRef) ((AssignStmt) read).getRightOp())
                .getBase();
        Local invocationId = newTraceLocal(body, LongType.v(),
                "$causynthSourcePhaseInvocation");
        List<Unit> before = new ArrayList<>();
        before.add(Jimple.v().newAssignStmt(invocationId, LongConstant.v(0L)));
        emit(before, refs.ref(Hook.PAUSE_OBSERVATION));
        emit(before, invocationId,
                refs.ref(Hook.ENTER_CONFIGURED_SOURCE_PHASE_SITE),
                StringConstant.v(phase.declarationMethod()),
                IntConstant.v(phase.declarationUnitIndex()),
                StringConstant.v(phase.runtimeDeclaredCallee()));
        emit(before, refs.ref(Hook.READ_CONFIGURATION),
                StringConstant.v(phase.sourceId()), owner,
                StringConstant.v(phase.fieldSignature()));
        emit(before, refs.ref(Hook.EXIT_CONFIGURED_SOURCE_PHASE_SITE),
                invocationId, NullConstant.v(), StringConstant.v(""));
        emit(before, refs.ref(Hook.RESUME_OBSERVATION));
        insertBeforeSequence(body, read, before);
    }

    /** The one original {@code getfield} of a configuration read site;
     *  refused by name when the unit is no read of the declared field. */
    private static Stmt originalRead(
            Body body, ConfiguredSourcePhaseContract.Occurrence phase) {
        tagOriginalUnits(snapshotUnits(body));
        Stmt selected = null;
        for (Unit unit : snapshotUnits(body)) {
            if (originalUnitIndex(unit) != phase.declarationUnitIndex()) {
                continue;
            }
            if (selected != null) {
                throw new IllegalStateException(
                        "CONFIGURED_SOURCE_PHASE_SITE_NOT_UNIQUE: "
                                + phase.siteId());
            }
            selected = (Stmt) unit;
        }
        if (!(selected instanceof AssignStmt) || !(((AssignStmt) selected)
                .getRightOp() instanceof InstanceFieldRef)
                || !phase.fieldSignature().equals(CausynthStaticFacts
                .declaredFieldSignature(((InstanceFieldRef) ((AssignStmt)
                        selected).getRightOp()).getFieldRef()))) {
            throw new IllegalStateException(
                    "CONFIGURED_SOURCE_PHASE_READ_NOT_FOUND: "
                            + phase.siteId() + " reads no "
                            + phase.fieldSignature());
        }
        return selected;
    }

    /**
     * Wraps {@code call} in a catch-all: {@code normal} follows it, and a
     * throw runs {@code exceptional} then rethrows.  The trap covers the call
     * and the normal units before {@code end}.
     */
    private static void guardCall(Body body, Stmt call, List<Unit> normal,
                                  Unit end, List<Unit> exceptional,
                                  String caughtName) {
        Local caught = newTraceLocal(body, RefType.v("java.lang.Throwable"),
                caughtName);
        Unit handler = Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef());
        Unit continuation = Jimple.v().newNopStmt();
        List<Unit> after = new ArrayList<>(normal);
        after.add(Jimple.v().newGotoStmt(continuation));
        after.add(handler);
        after.addAll(exceptional);
        after.add(Jimple.v().newThrowStmt(caught));
        after.add(continuation);
        insertAfterSequence(body, call, after);
        body.getTraps().addFirst(Jimple.v().newTrap(
                Scene.v().getSootClass("java.lang.Throwable"), call, end,
                handler));
    }

    /**
     * Files the start-site frame of every work start (IDENTITY §3, start
     * frames) and claims it at the work's own entry.
     *
     * <p>A thread inherits its creator's index at construction, not at the
     * start, so the start itself is the frame; without it sibling starts
     * mint one address.  Woven by BOTH passes over the WHOLE application
     * scope (IDENTITY §10), shapes from {@link WorkStartSites}.  The claim
     * sits at {@link WorkStartSites#entersWork}: a pool worker may send before
     * any region entry, and each task needs its own k (IDENTITY §3).</p>
     */
    private void instrumentApplicationScope(HookCatalog refs) {
        int filed = 0;
        int claimed = 0;
        int framed = 0;
        int walked = 0;
        int waited = 0;
        int lineage = 0;
        for (SootClass type : new ArrayList<>(
                Scene.v().getApplicationClasses())) {
            // A lineage-only class gets starts, claims and waits only.
            boolean lineageOnly = LineageScope.lineageOnly(type.getName());
            if (lineageOnly) lineage++;
            for (SootMethod method : new ArrayList<>(type.getMethods())) {
                Body body = CausynthStaticFacts.activeBody(method);
                if (body == null) continue;
                walked++;
                List<Unit> originalUnits = snapshotUnits(body);
                tagOriginalUnits(originalUnits);
                // Constructors: only after initialization.
                int from = 0;
                if (method.isConstructor()) {
                    Unit entry = safeInstrumentationEntry(body, method);
                    from = entry == null ? -1
                            : instrumentableFrom(originalUnits, entry);
                }
                if (from < 0) continue;
                for (Unit unit : snapshotUnits(body)) {
                    int unitIndex = originalUnitIndex(unit);
                    if (unitIndex < from || !(unit instanceof Stmt)) continue;
                    Stmt stmt = (Stmt) unit;
                    if (!stmt.containsInvokeExpr()) continue;
                    String site = SiteId.of(method.getSignature(), unitIndex);
                    List<Unit> before = new ArrayList<>();
                    int started = 0;
                    for (Value carried : startedWork(stmt.getInvokeExpr())) {
                        if (sentinel(body, stmt.getInvokeExpr(), carried)) {
                            continue;
                        }
                        Value carrier = objectArg(body, carried, before);
                        if (carrier instanceof NullConstant) continue;
                        refs.bracket(before, Hook.START_WORK,
                                StringConstant.v(site), carrier);
                        started++;
                    }
                    if (started > 0) {
                        insertBeforeSequence(body, stmt, before);
                        filed += started;
                    }
                    // Queue consumer claims the taken element here: it may
                    // be a lambda whose entry no weave reaches.
                    boolean claims = claimsFromQueue(stmt.getInvokeExpr());
                    Unit last = replaceTimedWait(body, stmt, site);
                    if (last != null) waited++;
                    else last = stmt;
                    replaceRandom(body, stmt, site);
                    replaceListing(stmt);
                    if (claims && last instanceof AssignStmt
                            && ((AssignStmt) last).getLeftOp()
                                    instanceof Local
                            && ((AssignStmt) last).getLeftOp().getType()
                                    instanceof RefType) {
                        List<Unit> claim = new ArrayList<>();
                        refs.bracket(claim, Hook.CLAIM_ITEM,
                                ((AssignStmt) last).getLeftOp());
                        insertAfterSequence(body, last, claim);
                        claimed++;
                    }
                }
                // The claim opens before the level and closes after it:
                // start frame below the work's levels.
                Unit entry = safeInstrumentationEntry(body, method);
                List<Unit> claim = claimWorkEntry(body, method, entry, refs);
                if (claim != null) claimed++;
                if (!lineageOnly && openMethodLevel(body, method,
                        originalUnits, entry, refs)) {
                    framed++;
                }
                if (claim != null) {
                    endWorkEntryClaim(body, originalUnits, claim, refs);
                }
            }
        }
        LOG.info("Instrumented {} calling-context frame(s), {} work start(s),"
                + " {} work claim(s) and {} timed wait(s) across {} method(s)"
                + " of the application scope for the execution index, {} "
                + "class(es) of it for their lineage alone", framed, filed,
                claimed, waited, walked, lineage);
    }

    /**
     * Replaces one timed wait (the schedule's WAKE, {@link
     * WorkStartSites.TimedWait}) with its stand-in, swapping only the invoke
     * expression so branch and trap targets survive.
     *
     * @return the unit the result is final after, or null if no timed wait
     */
    private static Unit replaceTimedWait(Body body, Stmt stmt, String site) {
        InvokeExpr invoke = stmt.getInvokeExpr();
        if (invoke instanceof SpecialInvokeExpr) return null;
        SootMethodRef callee = invoke.getMethodRef();
        List<String> parameters = new ArrayList<>();
        for (Type type : callee.getParameterTypes()) {
            parameters.add(type.toString());
        }
        boolean isStatic = !(invoke instanceof InstanceInvokeExpr);
        WorkStartSites.TimedWait shape = WorkStartSites.timedWait(
                callee.name(), parameters, isStatic,
                hierarchyOf(callee.declaringClass()));
        if (shape == null) return null;
        List<Type> replacementTypes = new ArrayList<>();
        for (String name : shape.replacementParameters()) {
            replacementTypes.add(sootType(name));
        }
        SootMethodRef replacement = Scene.v().makeMethodRef(
                phantomClass(WorkStartSites.TIMED_WAITS_CLASS),
                shape.replacement, replacementTypes, sootType(shape.returns),
                true);
        List<Value> arguments = new ArrayList<>();
        if (!isStatic) arguments.add(((InstanceInvokeExpr) invoke).getBase());
        arguments.addAll(invoke.getArgs());
        arguments.add(StringConstant.v(site));
        stmt.getInvokeExprBox().setValue(
                Jimple.v().newStaticInvokeExpr(replacement, arguments));
        if (!(stmt instanceof AssignStmt)) return stmt;
        AssignStmt assign = (AssignStmt) stmt;
        Type wanted = assign.getLeftOp().getType();
        Type given = sootType(shape.returns);
        if (!(wanted instanceof RefType) || wanted.equals(given)) {
            return stmt;
        }
        Local returned = newTraceLocal(body, given, "$causynthWaited");
        Value target = assign.getLeftOp();
        assign.setLeftOp(returned);
        AssignStmt cast = Jimple.v().newAssignStmt(target,
                Jimple.v().newCastExpr(returned, wanted));
        body.getUnits().insertAfter(cast, stmt);
        return cast;
    }

    /** The runtime's seeded stand-ins for unseeded randomness. */
    private static final String RANDOMS_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.Randoms";

    /**
     * Keys one draw by where it is drawn ({@code runtime.Randoms}), in both
     * passes, so a replay draws what the recording drew whatever the draws
     * before it (IDENTITY §10, SYMBOL-SCOPE §4.5).  A draw on any Random
     * receiver ({@link WorkStartSites#RANDOM_RECEIVERS}: Random,
     * ThreadLocalRandom, SecureRandom) draws from {@code Randoms#at(site)}
     * instead of the receiver's stream, whatever seed it was built with --
     * HDFS's DFSNetworkTopology picks pipelines from one static Random every
     * handler shares, so draw k depended on every draw before it
     * (hdfs-adhoc-01); a bounded draw only ThreadLocalRandom declares
     * becomes the {@code Randoms} helper of its name.  A Random handed to a
     * JDK method ({@link WorkStartSites#handsRandomOut}: {@code
     * Collections.shuffle(list, random)}) is {@code Randoms#at(site)} at that
     * call.  A static draw ({@link WorkStartSites#STATIC_DRAWS}) becomes the
     * {@code Randoms} stand-in of its name, the site its last argument.
     */
    private static void replaceRandom(Body body, Stmt stmt, String site) {
        InvokeExpr invoke = stmt.getInvokeExpr();
        SootMethodRef callee = invoke.getMethodRef();
        String owner = callee.declaringClass().getName();
        String draw = callee.getName()
                + soot.AbstractJasminClass.jasminDescriptorOf(callee);
        SootClass randoms = phantomClass(RANDOMS_CLASS);
        if ((invoke instanceof VirtualInvokeExpr
                || invoke instanceof InterfaceInvokeExpr)
                && WorkStartSites.RANDOM_RECEIVERS.contains(owner)
                && WorkStartSites.drawn(draw)) {
            Local drawn = randomAt(body, stmt, site, randoms);
            if (WorkStartSites.RANDOM_DRAWS.contains(draw)) {
                stmt.getInvokeExprBox().setValue(Jimple.v()
                        .newVirtualInvokeExpr(drawn, Scene.v().makeMethodRef(
                                phantomClass(RANDOM), callee.getName(),
                                callee.getParameterTypes(),
                                callee.getReturnType(), false),
                                invoke.getArgs()));
                return;
            }
            List<Type> parameters = new ArrayList<>();
            parameters.add(drawn.getType());
            parameters.addAll(callee.getParameterTypes());
            List<Value> arguments = new ArrayList<>();
            arguments.add(drawn);
            arguments.addAll(invoke.getArgs());
            stmt.getInvokeExprBox().setValue(Jimple.v().newStaticInvokeExpr(
                    Scene.v().makeMethodRef(randoms, callee.getName(),
                            parameters, callee.getReturnType(), true),
                    arguments));
            return;
        }
        if (WorkStartSites.STATIC_DRAWS.contains(owner.replace('.', '/')
                + "." + draw)) {
            List<Type> parameters = new ArrayList<>(
                    callee.getParameterTypes());
            parameters.add(RefType.v("java.lang.String"));
            List<Value> arguments = new ArrayList<>(invoke.getArgs());
            arguments.add(StringConstant.v(site));
            stmt.getInvokeExprBox().setValue(Jimple.v().newStaticInvokeExpr(
                    Scene.v().makeMethodRef(randoms, callee.getName(),
                            parameters, callee.getReturnType(), true),
                    arguments));
            return;
        }
        if (!WorkStartSites.handsRandomOut(owner.replace('.', '/'),
                soot.AbstractJasminClass.jasminDescriptorOf(callee))) {
            return;
        }
        for (int index = 0; index < invoke.getArgCount(); index++) {
            Type parameter = callee.getParameterType(index);
            if (parameter instanceof RefType && RANDOM.equals(
                    ((RefType) parameter).getClassName())) {
                invoke.setArg(index, randomAt(body, stmt, site, randoms));
            }
        }
    }

    /** The runtime's stand-ins for directory listings, sorted by name. */
    private static final String LISTINGS_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.Listings";

    /**
     * A directory listing on java.io.File ({@link WorkStartSites#LISTINGS})
     * becomes the {@code runtime.Listings} stand-in of its name, the file
     * its first argument, in both passes: the listing comes back sorted by
     * name, so a recording and its replays walk a directory in one order
     * whatever host and file system each runs on (SYMBOL-SCOPE §4.5).
     */
    private static void replaceListing(Stmt stmt) {
        InvokeExpr invoke = stmt.getInvokeExpr();
        if (!(invoke instanceof VirtualInvokeExpr)) return;
        SootMethodRef callee = invoke.getMethodRef();
        if (!WorkStartSites.lists(callee.declaringClass().getName()
                        .replace('.', '/'), callee.getName(),
                soot.AbstractJasminClass.jasminDescriptorOf(callee))) {
            return;
        }
        List<Type> parameters = new ArrayList<>();
        parameters.add(RefType.v("java.io.File"));
        parameters.addAll(callee.getParameterTypes());
        List<Value> arguments = new ArrayList<>();
        arguments.add(((VirtualInvokeExpr) invoke).getBase());
        arguments.addAll(invoke.getArgs());
        stmt.getInvokeExprBox().setValue(Jimple.v().newStaticInvokeExpr(
                Scene.v().makeMethodRef(phantomClass(LISTINGS_CLASS),
                        callee.getName(), parameters, callee.getReturnType(),
                        true),
                arguments));
    }

    /** {@code Randoms#at(site)} in a fresh local, before {@code stmt}. */
    private static Local randomAt(Body body, Stmt stmt, String site,
                                  SootClass randoms) {
        RefType random = RefType.v(RANDOM);
        Local drawn = newTraceLocal(body, random, "$causynthDraw");
        body.getUnits().insertBefore(Jimple.v().newAssignStmt(drawn,
                Jimple.v().newStaticInvokeExpr(Scene.v().makeMethodRef(
                        randoms, "at", Collections.<Type>singletonList(
                                RefType.v("java.lang.String")), random,
                        true), StringConstant.v(site))), stmt);
        return drawn;
    }

    private static final String RANDOM = "java.util.Random";

    /** The Soot type a {@link WorkStartSites.TimedWait} names. */
    private static Type sootType(String name) {
        switch (name) {
            case "void": return VoidType.v();
            case "long": return LongType.v();
            case "int": return IntType.v();
            case "boolean": return BooleanType.v();
            default: return RefType.v(name);
        }
    }

    /**
     * Whether a queue element is a sentinel: the value of a final field, the
     * same object every time it is offered (a poison pill, a wake-up
     * marker).  It names no one piece of work, and how often it is offered
     * is the consumers' timing: Solr's ConcurrentUpdateHttp2SolrClient
     * offers its backdoor element once per runner still alive at close.
     */
    private static boolean sentinel(Body body, InvokeExpr invoke,
                                    Value element) {
        if (!(invoke instanceof InstanceInvokeExpr)
                || !(element instanceof Local)
                || !WorkStartSites.submitsToQueue(
                        invoke.getMethodRef().name(), invoke.getArgCount(),
                        hierarchyOf(invoke.getMethodRef().declaringClass()))) {
            return false;
        }
        boolean defined = false;
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof AssignStmt)
                    || ((AssignStmt) unit).getLeftOp() != element) {
                continue;
            }
            Value source = ((AssignStmt) unit).getRightOp();
            if (!(source instanceof FieldRef)
                    || !((FieldRef) source).getField().isFinal()) {
                return false;
            }
            defined = true;
        }
        return defined;
    }

    /** Whether this invocation takes work a producer put on a queue. */
    private static boolean claimsFromQueue(InvokeExpr invoke) {
        return invoke instanceof InstanceInvokeExpr
                && WorkStartSites.claimsFromQueue(
                        invoke.getMethodRef().name(),
                        hierarchyOf(invoke.getMethodRef().declaringClass()));
    }

    /**
     * Opens the execution-index level of ONE application-scope method.
     *
     * <p>THE frame rule (IDENTITY §3): every application-scope
     * method opens a level at entry and closes it at every exit, in BOTH
     * passes; only region roots push more.  Woven LAST, so it brackets every
     * other woven hook and its trap runs after every inner handler.</p>
     *
     * @return whether this method received a level
     */
    private boolean openMethodLevel(Body body, SootMethod method,
                                    List<Unit> originalUnits, Unit entry,
                                    HookCatalog refs) {
        if (entry == null) return false;
        Local token = newTraceLocal(body, LongType.v(),
                "$causynthFrameToken");
        List<Unit> opening = new ArrayList<>();
        // The entry hook IS the token's store.  Receiver for Attribution
        // rule 2; none for a constructor.
        refs.bracket(opening, token, Hook.ENTER_METHOD_FRAME,
                StringConstant.v(method.getSignature()),
                method.isConstructor() ? NullConstant.v()
                        : receiverOrNull(body, method));
        insertBeforeOrAppendNoRedirect(body, entry, opening);
        bracketReturns(body, originalUnits, 0, refs, Hook.EXIT_METHOD_FRAME,
                token);
        // The handler reads the token: the trap opens after its store.
        addThrowHandler(body, afterWovenPrologue(body, opening), refs,
                Hook.THROW_METHOD_FRAME, "$causynthFrameThrown", token);
        return true;
    }

    /**
     * Claims the start frame filed under {@code this} at the entry of the
     * work it carries ({@code Identity.claimStart}; no claim if none), before
     * every other hook there.  With {@link #endWorkEntryClaim}, woven after
     * the method's level, the claim ends when the work returns, after the
     * work's own frame (IDENTITY §3).
     *
     * @return the claim's prologue, which stores its token, or null when
     *         this method is no work entry
     */
    private static List<Unit> claimWorkEntry(Body body, SootMethod method,
                                             Unit entry, HookCatalog refs) {
        if (entry == null || method.isStatic() || method.isConstructor()
                || !WorkStartSites.entersWork(method.getName(),
                        method.getParameterCount(),
                        hierarchyOf(method.getDeclaringClass()))) {
            return null;
        }
        Value receiver = receiverOrNull(body, method);
        if (receiver instanceof NullConstant) return null;
        Local token = newTraceLocal(body, LongType.v(), "$causynthClaim");
        List<Unit> claim = new ArrayList<>();
        refs.bracket(claim, token, Hook.CLAIM_START, receiver);
        insertBeforeOrAppendNoRedirect(body, entry, claim);
        return claim;
    }

    /** Ends {@link #claimWorkEntry}'s claim at every return and throw. */
    private static void endWorkEntryClaim(Body body, List<Unit> originalUnits,
                                          List<Unit> claim, HookCatalog refs) {
        Value stored = null;
        for (Unit unit : claim) {
            if (unit instanceof AssignStmt) {
                stored = ((AssignStmt) unit).getLeftOp();
            }
        }
        Value token = stored;
        bracketReturns(body, originalUnits, 0, refs, Hook.END_CLAIM, token);
        // The handler reads the token: the trap opens after its store.
        appendCatchAll(body, afterWovenPrologue(body, claim),
                "$causynthClaimThrown",
                (units, caught) -> refs.bracket(units, Hook.END_CLAIM,
                        token));
    }

    /**
     * The work carriers one invocation starts, in call order (the Soot
     * projection of {@link WorkStartSites}).
     */
    private static List<Value> startedWork(InvokeExpr invoke) {
        SootMethodRef callee = invoke.getMethodRef();
        String name = callee.name();
        List<Value> carried = new ArrayList<>();
        Value receiver = invoke instanceof InstanceInvokeExpr
                && !"<init>".equals(name)
                ? ((InstanceInvokeExpr) invoke).getBase() : null;
        if (receiver != null && WorkStartSites.startsReceiver(name,
                invoke.getArgCount(),
                hierarchyOf(callee.declaringClass()))) {
            carried.add(receiver);
            return carried;
        }
        // A queue handoff: the element is the work, whatever its type.
        if (receiver != null && WorkStartSites.submitsToQueue(name,
                invoke.getArgCount(), hierarchyOf(callee.declaringClass()))) {
            Value element = invoke.getArg(0);
            if (element.getType() instanceof RefType
                    || element.getType() instanceof ArrayType) {
                carried.add(element);
            }
            return carried;
        }
        if (!WorkStartSites.submitsArguments(name, invoke.getArgCount())) {
            return carried;
        }
        for (int index = 0; index < invoke.getArgCount(); index++) {
            Value argument = invoke.getArg(index);
            if (WorkStartSites.carriesWork(hierarchyOf(argument.getType()))) {
                carried.add(argument);
            }
        }
        return carried;
    }

    /** {@link WorkStartSites.Types} of a declared type: its hierarchy. */
    private static WorkStartSites.Types hierarchyOf(Type type) {
        return hierarchyOf(type instanceof RefType
                ? ((RefType) type).getSootClass() : null);
    }

    /** {@link WorkStartSites.Types} of a class: its own hierarchy. */
    private static WorkStartSites.Types hierarchyOf(final SootClass type) {
        return new WorkStartSites.Types() {
            @Override
            public boolean is(String typeName) {
                return declares(type, typeName);
            }
        };
    }

    /** Whether this type is, or inherits, the named one. */
    private static boolean declares(SootClass type, String name) {
        Set<String> seen = new LinkedHashSet<>();
        Deque<SootClass> pending = new ArrayDeque<>();
        if (type != null) pending.push(type);
        while (!pending.isEmpty()) {
            SootClass current = pending.pop();
            if (!seen.add(current.getName())) continue;
            if (current.getName().equals(name)) return true;
            if (current.hasSuperclass()) pending.push(current.getSuperclass());
            for (SootClass implemented : current.getInterfaces()) {
                pending.push(implemented);
            }
        }
        return false;
    }

    /** Wraps selected accessor calls in a thread-local call context. */
    private void instrumentConcolicAccessorCallContexts(
            ConcolicMaterializationSelection selection,
            HookCatalog refs) {
        for (AccessorCallTarget target : selection.accessorCalls()) {
            Body body = selectedBody(target.callerMethod,
                    "ACCESSOR_CALLSITE_CALLER", target.callSiteId);
            SootMethod method = body.getMethod();
            Stmt selected = originalCall(body, target.callUnitIndex,
                    target.callSiteId, "ACCESSOR_CALLSITE_NOT_UNIQUE",
                    "ACCESSOR_CALLSITE_INVOKE_NOT_FOUND");
            Unit safeEntry = safeInstrumentationEntry(body, method);
            if (method.isConstructor()
                    && (safeEntry == null
                    || !unitAtOrAfter(body, safeEntry, selected))) {
                throw new IllegalStateException(
                        "ACCESSOR_CALLSITE_BEFORE_CONSTRUCTOR_INITIALIZATION: "
                                + target.callSiteId);
            }
            requireCallee(selected, target.declaredCallee,
                    "ACCESSOR_CALLSITE_DECLARED_CALLEE_MISMATCH",
                    target.callSiteId);
            InvokeExpr invocation = selected.getInvokeExpr();
            if (!(invocation instanceof InstanceInvokeExpr)
                    || "<init>".equals(invocation.getMethodRef().name())) {
                throw new IllegalStateException(
                        "ACCESSOR_CALLSITE_REQUIRES_INSTANCE_RECEIVER: "
                                + target.callSiteId);
            }

            Local contextToken = newTraceLocal(body, LongType.v(),
                    "$causynthAccessorContextToken");
            List<Unit> before = new ArrayList<>();
            before.add(Jimple.v().newAssignStmt(contextToken,
                    LongConstant.v(0L)));
            Value receiver = objectArg(body,
                    ((InstanceInvokeExpr) invocation).getBase(), before);
            emit(before, refs.ref(Hook.PAUSE_OBSERVATION));
            emit(before, contextToken,
                    refs.ref(Hook.ENTER_ACCESSOR_CALL_CONTEXT),
                    StringConstant.v(target.callerMethod),
                    IntConstant.v(target.callUnitIndex),
                    StringConstant.v(target.callSiteId),
                    StringConstant.v(target.declaredCallee), receiver);
            // The accessor may be JDK code no weave reaches: materialize its
            // backing field here, inside the call context.
            emit(before, refs.ref(Hook.MATERIALIZE_FIELD),
                    StringConstant.v(target.implementationMethod),
                    IntConstant.v(-1), receiver,
                    StringConstant.v(target.fieldSignature),
                    StringConstant.v(target.fieldName));
            emit(before, refs.ref(Hook.RESUME_OBSERVATION));
            insertBeforeSequence(body, selected, before);

            List<Unit> exit = new ArrayList<>();
            refs.bracket(exit, Hook.EXIT_ACCESSOR_CALL_CONTEXT, contextToken);
            List<Unit> thrown = new ArrayList<>();
            refs.bracket(thrown, Hook.EXIT_ACCESSOR_CALL_CONTEXT,
                    contextToken);
            guardCall(body, selected, exit, exit.get(0), thrown,
                    "$causynthAccessorThrown");
        }
    }

    /**
     * Observes a tracked cell at each access of it, starting its version log
     * where none stands.  The cell ({@code field}): before the {@code
     * putfield}/{@code putstatic}, before the call when the store is an
     * atomic's RMW (no application {@code putfield}), before the {@code
     * getfield}/{@code getstatic} of a read, and before the call of a read
     * through an accessor (the site names it), on the call's receiver; a
     * static cell's owner is its declaring class's mirror, the key the VM
     * versions it by.  The state of the container the cell holds ({@code
     * container}): after a read, on the referent it returned; before and
     * after a container mutation through the cell, on the call's receiver
     * (before: a region thread starts the log the mutation then versions;
     * after: a thread outside every region marks it).  An
     * instance access before the constructor call that makes its object has
     * no object to observe yet, and a read site that is no field read of its
     * cell, or whose value nothing holds, observes nothing.
     */
    private void instrumentConcolicObservedSites(
            ConcolicMaterializationSelection selection, HookCatalog refs) {
        int unobserved = 0;
        for (ObservedSite target : selection.observedSites()) {
            Body body = selectedBody(target.method,
                    "OBSERVED_SITE_METHOD", target.siteId);
            Stmt selected;
            Value owner;
            if (target.declaredCallee.isEmpty()) {
                selected = originalAccess(body, target);
                if (selected == null) {
                    unobserved++;
                    continue;
                }
                FieldRef field = accessedField((AssignStmt) selected,
                        target.read);
                // A static cell's mirror is the class its signature names, the
                // declaring class the runtime hands the VM with it.
                owner = field instanceof InstanceFieldRef
                        ? ((InstanceFieldRef) field).getBase()
                        : ClassConstant.fromType(RefType.v(CausynthStaticFacts
                                .fieldOwner(target.cell)));
            } else {
                selected = originalCall(body, target.unitIndex,
                        target.siteId, "OBSERVED_SITE_NOT_UNIQUE",
                        "OBSERVED_SITE_INVOKE_NOT_FOUND");
                requireCallee(selected, target.declaredCallee,
                        "OBSERVED_SITE_DECLARED_CALLEE_MISMATCH",
                        target.siteId);
                InvokeExpr invocation = selected.getInvokeExpr();
                if (!(invocation instanceof InstanceInvokeExpr)) {
                    throw new IllegalStateException(
                            "OBSERVED_SITE_REQUIRES_INSTANCE_RECEIVER: "
                                    + target.siteId);
                }
                owner = ((InstanceInvokeExpr) invocation).getBase();
            }
            if (target.field) {
                List<Unit> before = new ArrayList<>();
                Value receiver = objectArg(body, owner, before);
                refs.bracket(before, Hook.OBSERVE_TRACKED_SITE,
                        StringConstant.v(target.siteId),
                        StringConstant.v(target.cell), receiver);
                insertBeforeSequence(body, selected, before);
            }
            if (!target.container) continue;
            List<Unit> observation = new ArrayList<>();
            if (!target.read) {
                Value receiver = objectArg(body, owner, observation);
                refs.bracket(observation, Hook.OBSERVE_TRACKED_CONTAINER,
                        StringConstant.v(target.siteId),
                        StringConstant.v(target.cell), receiver,
                        IntConstant.v(0));
                insertBeforeSequence(body, selected, observation);
                List<Unit> after = new ArrayList<>();
                refs.bracket(after, Hook.OBSERVE_TRACKED_CONTAINER,
                        StringConstant.v(target.siteId),
                        StringConstant.v(target.cell), receiver,
                        IntConstant.v(1));
                insertAfterSequence(body, selected, after);
            } else if (selected instanceof AssignStmt) {
                refs.bracket(observation, Hook.OBSERVE_TRACKED_CONTAINER,
                        StringConstant.v(target.siteId),
                        StringConstant.v(target.cell),
                        objectArg(body, ((AssignStmt) selected).getLeftOp(),
                                observation),
                        IntConstant.v(0));
                insertAfterSequence(body, selected, observation);
            } else {
                unobserved++;
            }
        }
        if (unobserved > 0) {
            LOG.info("Left {} tracked access(es) unobserved: before their "
                    + "object's constructor call, a read site that is no "
                    + "getfield of its cell, or a container read whose value "
                    + "nothing holds", unobserved);
        }
    }

    /**
     * The original store into, or read of, the target's cell -- an instance
     * field's or, for a static cell, its class's; null when an instance
     * access runs before the constructor call that makes its object, or when
     * a read site is no field read of its cell.
     */
    private static Stmt originalAccess(Body body, ObservedSite target) {
        tagOriginalUnits(snapshotUnits(body));
        Stmt selected = null;
        Unit constructed = null;
        for (Unit unit : snapshotUnits(body)) {
            if (constructed == null && constructorCall(body, unit)) {
                constructed = unit;
            }
            if (originalUnitIndex(unit) != target.unitIndex) continue;
            if (selected != null || !(unit instanceof AssignStmt)) {
                if (target.read) return null;
                throw new IllegalStateException(
                        "OBSERVED_SITE_NOT_UNIQUE: " + target.siteId);
            }
            selected = (Stmt) unit;
            FieldRef field = accessedField((AssignStmt) unit, target.read);
            if (field == null
                    || (field instanceof StaticFieldRef) != target.staticField
                    || !target.cell.equals(CausynthStaticFacts
                            .declaredFieldSignature(field.getFieldRef()))) {
                if (target.read) return null;
                throw new IllegalStateException(
                        "OBSERVED_SITE_STORE_NOT_FOUND: "
                                + target.siteId + " stores no " + target.cell);
            }
            if (!target.staticField && body.getMethod().isConstructor()
                    && constructed == null) {
                return null;
            }
        }
        if (selected == null && !target.read) {
            throw new IllegalStateException(
                    "OBSERVED_SITE_STORE_NOT_FOUND: " + target.siteId);
        }
        return selected;
    }

    /** The field an assignment reads or stores, or null. */
    private static FieldRef accessedField(AssignStmt access, boolean read) {
        Value field = read ? access.getRightOp() : access.getLeftOp();
        return field instanceof FieldRef ? (FieldRef) field : null;
    }

    /** Whether {@code unit} is a constructor's own this/super constructor
     *  call. */
    private static boolean constructorCall(Body body, Unit unit) {
        if (!body.getMethod().isConstructor() || !(unit instanceof Stmt)
                || !((Stmt) unit).containsInvokeExpr()) {
            return false;
        }
        InvokeExpr call = ((Stmt) unit).getInvokeExpr();
        return call instanceof SpecialInvokeExpr
                && "<init>".equals(call.getMethodRef().getName())
                && ((SpecialInvokeExpr) call).getBase()
                .equals(body.getThisLocal());
    }

    /** Materializes the campaign envelope's selected sites, and only those. */
    private void instrumentConcolicMaterializations(
            CampaignEnvelope envelope, HookCatalog refs) {
        ConcolicMaterializationSelection selection = envelope.materializations;
        if (selection.isEmpty()) {
            return;
        }
        instrumentMethods(envelope.methods, "", (body, method, originalUnits,
                entry, lowerBound, receiver) -> {
            for (int index = instrumentableFrom(originalUnits, lowerBound);
                    index >= 0 && index < originalUnits.size(); index++) {
                Unit unit = originalUnits.get(index);
                if (unit instanceof Stmt) {
                    materializeFieldReads(body, method, (Stmt) unit,
                            selection, refs);
                    materializeLocalDefinition(body, method, (Stmt) unit,
                            selection, refs);
                }
            }
        });
    }

    /** Materializes each selected field this statement reads, before it. */
    private static void materializeFieldReads(
            Body body, SootMethod method, Stmt stmt,
            ConcolicMaterializationSelection selection, HookCatalog refs) {
        int unitIndex = originalUnitIndex(stmt);
        Set<FieldRef> fields = Collections.newSetFromMap(
                new IdentityHashMap<FieldRef, Boolean>());
        if (stmt instanceof AssignStmt
                && ((AssignStmt) stmt).getRightOp() instanceof FieldRef) {
            fields.add((FieldRef) ((AssignStmt) stmt).getRightOp());
        }
        for (ValueBox box : stmt.getUseBoxes()) {
            if (box.getValue() instanceof FieldRef) {
                fields.add((FieldRef) box.getValue());
            }
        }
        for (FieldRef field : fields) {
            SootFieldRef fieldRef = field.getFieldRef();
            String declaredSignature =
                    CausynthStaticFacts.declaredFieldSignature(fieldRef);
            if (!selection.matches(fieldRef)) {
                continue;
            }
            if (field instanceof StaticFieldRef) {
                instrumentConsumedStaticPrimitiveFieldRead(body, method, stmt,
                        unitIndex, (StaticFieldRef) field, refs);
                continue;
            }
            if (!(field instanceof InstanceFieldRef)) {
                throw new IllegalStateException(
                        "UNKNOWN_FIELD_MATERIALIZATION_UNSUPPORTED: "
                                + declaredSignature + " at "
                                + SiteId.of(method.getSignature(), unitIndex));
            }
            List<Unit> before = new ArrayList<>();
            Value owner = objectArg(body,
                    ((InstanceFieldRef) field).getBase(), before);
            refs.bracket(before, Hook.MATERIALIZE_FIELD,
                    StringConstant.v(method.getSignature()),
                    IntConstant.v(unitIndex), owner,
                    StringConstant.v(declaredSignature),
                    StringConstant.v(CausynthStaticFacts.declaredFieldName(
                            fieldRef)));
            insertBeforeSequence(body, stmt, before);
        }
    }

    /** Materializes the selected local this statement defines, after it. */
    private static void materializeLocalDefinition(
            Body body, SootMethod method, Stmt stmt,
            ConcolicMaterializationSelection selection, HookCatalog refs) {
        if (!(stmt instanceof AssignStmt)) {
            return;
        }
        int unitIndex = originalUnitIndex(stmt);
        Value left = ((AssignStmt) stmt).getLeftOp();
        if (!(left instanceof Local) || !selection.matches(
                method.getSignature(), ((Local) left).getName(), unitIndex)) {
            return;
        }
        Local local = (Local) left;
        List<Unit> after = new ArrayList<>();
        if (local.getType() instanceof RefType
                || local.getType() instanceof ArrayType) {
            Local modeled = newTraceLocal(body, RefType.v("java.lang.Object"),
                    "$causynthReferenceModel");
            refs.bracket(after, modeled, Hook.MATERIALIZE_REFERENCE,
                    StringConstant.v(method.getSignature()),
                    IntConstant.v(unitIndex),
                    StringConstant.v(local.getName()), local);
            after.add(Jimple.v().newAssignStmt(local,
                    Jimple.v().newCastExpr(modeled, local.getType())));
        } else {
            addPrimitiveRoundTrip(body, local, after, "$causynth", refs,
                    Hook.MATERIALIZE_PRIMITIVE, boxed -> new Value[]{
                            StringConstant.v(method.getSignature()),
                            IntConstant.v(unitIndex),
                            StringConstant.v(local.getName()), boxed});
        }
        if (!after.isEmpty()) {
            insertAfterSequence(body, stmt, after);
        }
    }

    private void instrumentConcolicMethodArguments(
            ConcolicMaterializationSelection selection,
            HookCatalog refs) {
        // Every selected owner must be rewritten; a skipped one is refused.
        Collection<String> owners = selection.methodArgumentMethods();
        Set<String> rewritten = instrumentMethods(owners, "",
                (body, method, units, entry, lowerBound, receiver) -> {
                    String signature = method.getSignature();
                    List<Unit> prefix = new ArrayList<>();
                    for (Integer index
                            : selection.methodArguments(signature)) {
                        if (index == null || index < 0
                                || index >= method.getParameterCount()) {
                            throw new IllegalStateException(
                                    "CONCOLIC_METHOD_ARGUMENT_OUT_OF_RANGE: "
                                            + signature + "#param" + index);
                        }
                        materializeParameter(body,
                                body.getParameterLocal(index), index, prefix,
                                StringConstant.v(signature),
                                "$causynthMethodArgument",
                                Hook.MATERIALIZE_METHOD_ARGUMENT,
                                Hook.SYMBOLIZE_METHOD_ARGUMENT, refs);
                    }
                    insertBeforeOrAppendNoRedirect(body, entry, prefix);
                });
        for (String signature : owners) {
            if (!rewritten.contains(signature)) {
                throw new IllegalStateException(
                        "CONCOLIC_METHOD_ARGUMENT_OWNER_UNAVAILABLE: "
                                + signature);
            }
        }
    }

    /** Materializes a primitive {@code getstatic} on its consuming local. */
    private static void instrumentConsumedStaticPrimitiveFieldRead(
            Body body, SootMethod method, Stmt stmt, int unitIndex,
            StaticFieldRef field, HookCatalog refs) {
        if (!(stmt instanceof AssignStmt)
                || ((AssignStmt) stmt).getRightOp() != field
                || !(((AssignStmt) stmt).getLeftOp() instanceof Local)) {
            return;
        }
        Local consumed = (Local) ((AssignStmt) stmt).getLeftOp();
        List<Unit> after = new ArrayList<>();
        if (addPrimitiveRoundTrip(body, consumed, after,
                "$causynthStaticField", refs,
                Hook.MATERIALIZE_STATIC_PRIMITIVE_FIELD, boxed -> new Value[]{
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex),
                        StringConstant.v(CausynthStaticFacts
                                .declaredFieldSignature(field.getFieldRef())),
                        StringConstant.v(CausynthStaticFacts
                                .declaredFieldName(field.getFieldRef())),
                        boxed})) {
            insertAfterSequence(body, stmt, after);
        }
    }

    /**
     * Round-trips a primitive through {@code hook(arguments(boxed))}, paused:
     * box, materialize, unbox back into {@code primitive}.
     * @return false, adding nothing, for a non-primitive
     */
    private static boolean addPrimitiveRoundTrip(
            Body body, Value primitive, List<Unit> units, String localPrefix,
            HookCatalog refs, Hook hook,
            Function<Local, Value[]> arguments) {
        PrimitiveWrapper wrapper = PrimitiveWrapper.forType(primitive.getType());
        if (wrapper == null) {
            return false;
        }
        SootClass wrapperClass = Scene.v().getSootClass(wrapper.className);
        RefType wrapperType = RefType.v(wrapper.className);
        SootMethodRef valueOf = Scene.v().makeMethodRef(wrapperClass,
                "valueOf", Collections.singletonList(primitive.getType()),
                wrapperType, true);
        Local boxed = newTraceLocal(body, wrapperType, localPrefix + "Box");
        emit(units, boxed, valueOf, primitive);
        Local materialized = newTraceLocal(body,
                RefType.v("java.lang.Object"), localPrefix + "Materialized");
        refs.bracket(units, materialized, hook, arguments.apply(boxed));
        Local cast = newTraceLocal(body, wrapperType, localPrefix + "Unbox");
        units.add(Jimple.v().newAssignStmt(cast,
                Jimple.v().newCastExpr(materialized, wrapperType)));
        SootMethodRef unbox = Scene.v().makeMethodRef(wrapperClass,
                wrapper.unboxMethod, Collections.<Type>emptyList(),
                primitive.getType(), false);
        units.add(Jimple.v().newAssignStmt(primitive,
                Jimple.v().newVirtualInvokeExpr(cast, unbox)));
        return true;
    }

    /**
     * Pre-weave index of this unit, or -1 if woven: the ONE numbering of
     * every published site id (shared with {@link SiteControlDependence}).
     */
    static int originalUnitIndex(Unit unit) {
        for (Tag tag : unit.getTags()) {
            if (tag instanceof OriginalUnitIndexTag) {
                return ((OriginalUnitIndexTag) tag).index;
            }
        }
        return -1;
    }

    /**
     * Bounds loops at body entries, not latches, so an iterator exhausted
     * exactly at the bound still exits normally.  Loops come from the one
     * {@link CfgLoopControl.LoopCfg}; trap-only cycles get no bound.
     */
    private static void instrumentConcolicLoopBounds(
            Set<String> methods, LoopBoundPolicy policy,
            Set<String> fixedCountLoopSites, HookCatalog refs) {
        SootMethodRef replayBody = refs.ref(Hook.CHECK_REPLAY_LOOP_BODY);
        SootMethodRef checkBackedge = refs.ref(Hook.CHECK_LOOP_BACKEDGE);
        for (String methodSignature : methods) {
            SootMethod method = CausynthStaticFacts.method(methodSignature);
            if (method == null || !method.isConcrete()) {
                continue;
            }
            Body body = method.retrieveActiveBody();
            List<Unit> original = snapshotUnits(body);
            tagOriginalUnits(original);
            // One loop CFG per body, shared by every loop consumer.
            CfgLoopControl.LoopCfg loopCfg = CfgLoopControl.loopCfg(body);
            Unit safeEntry = safeInstrumentationEntry(body, method);
            for (CfgLoopControl.NaturalLoop loop
                    : CfgLoopControl.naturalLoops(loopCfg,
                            CausynthPipeline::originalUnitIndex)) {
                List<CfgLoopControl.Edge> continuations = continuationEdges(
                        body, loopCfg, original, loop);
                String loopId = loop.identity(method);
                boolean fixedCount = naturalLoopHasSite(
                        method, loop, continuations,
                                fixedCountLoopSites);
                // A fixed-count loop is a resource loop: charged per body.
                int loopBodyBound = fixedCount
                        ? policy.maxBackedgeTraversals()
                        : naturalLoopBodyBound(
                                method, loop, continuations, policy);
                for (CfgLoopControl.Backedge backedge : loop.backedges) {
                    if (method.isConstructor()
                            && (safeEntry == null || !unitAtOrAfter(
                            body, safeEntry, backedge.source))) {
                        throw new IllegalStateException(
                                "CFG_BACKEDGE_BEFORE_CONSTRUCTOR_"
                                        + "INITIALIZATION: "
                                        + backedge.identity(method));
                    }
                    boolean entersBody = removeEdge(continuations,
                            backedge.source, backedge.target);
                    // A resource loop is charged once per body entered; any
                    // other latch executes after one complete body.
                    if (fixedCount && !entersBody) continue;
                    splitLoopEdge(body, method, backedge.source,
                            backedge.target, loopId, "edge", invoke(
                                    fixedCount ? replayBody : checkBackedge,
                                    StringConstant.v(loopId),
                                    IntConstant.v(loopBodyBound)));
                }
                if (fixedCount) {
                    for (CfgLoopControl.Edge continuation : continuations) {
                        splitLoopEdge(body, method, continuation.source,
                                continuation.target, loopId, "edge",
                                invoke(replayBody, StringConstant.v(loopId),
                                        IntConstant.v(loopBodyBound)));
                    }
                }
            }
        }
    }

    private static boolean naturalLoopHasSite(
            SootMethod method, CfgLoopControl.NaturalLoop loop,
            List<CfgLoopControl.Edge> continuations, Set<String> selectedSites) {
        return !selectedSites.isEmpty() && !Collections.disjoint(
                selectedSites,
                naturalLoopControlSites(method, loop, continuations));
    }

    /** Resolves one natural loop's declared K_L from its actual CFG guards. */
    private static int naturalLoopBodyBound(
            SootMethod method, CfgLoopControl.NaturalLoop loop,
            List<CfgLoopControl.Edge> continuations, LoopBoundPolicy policy) {
        Set<String> controlSites = naturalLoopControlSites(
                method, loop, continuations);
        Integer declared = null;
        String declaredSite = "";
        // A multi-guard loop is declared under its composite loopSiteId
        // L(site+site+...); resolve it first, or a declared K_L is silently
        // replaced by the default here while later stages read the plan's.
        String retainedSite = retainedLoopSiteId(method, loop);
        Integer retainedBound = policy.declaredBounds().get(retainedSite);
        if (retainedBound != null) {
            declared = retainedBound;
            declaredSite = retainedSite;
        }
        for (String site : controlSites) {
            Integer candidate = policy.declaredBounds().get(site);
            if (candidate == null) continue;
            if (declared != null && !declared.equals(candidate)) {
                throw new IllegalStateException(
                        "BOUNDED_LOOP_BODY_BOUND_DISAGREES: loop "
                                + loop.identity(method) + " declares K_L="
                                + declared + " at " + declaredSite
                                + " and K_L=" + candidate + " at " + site);
            }
            declared = candidate;
            declaredSite = site;
        }
        return declared == null ? policy.defaultBackedgeTraversals()
                : declared.intValue();
    }

    /** The catalog's canonical id for this natural loop's retained guards. */
    private static String retainedLoopSiteId(
            SootMethod method, CfgLoopControl.NaturalLoop natural) {
        for (CfgLoopControl.RetainedLoop retained
                : CfgLoopControl.retainedLoops(
                CfgLoopControl.loopCfg(method.retrieveActiveBody()))) {
            if (retained.header != natural.header) continue;
            Set<String> sites = new LinkedHashSet<>();
            for (Unit guard : retained.guards) {
                addLoopControlSite(sites, method, guard);
            }
            return LoopBoundPolicy.loopSiteId(sites);
        }
        return "";
    }

    private static Set<String> naturalLoopControlSites(
            SootMethod method, CfgLoopControl.NaturalLoop loop,
            List<CfgLoopControl.Edge> continuations) {
        Set<String> controlSites = new LinkedHashSet<>();
        addLoopControlSite(controlSites, method, loop.header);
        for (CfgLoopControl.Backedge backedge : loop.backedges) {
            addLoopControlSite(controlSites, method, backedge.source);
        }
        for (CfgLoopControl.Edge continuation : continuations) {
            addLoopControlSite(controlSites, method, continuation.source);
        }
        return controlSites;
    }

    private static void addLoopControlSite(
            Set<String> sites, SootMethod method, Unit unit) {
        int index = originalUnitIndex(unit);
        if (index >= 0) {
            sites.add(SiteId.of(method.getSignature(), index));
        }
    }

    private static List<CfgLoopControl.Edge> continuationEdges(
            Body body, CfgLoopControl.LoopCfg loopCfg, List<Unit> original,
            CfgLoopControl.NaturalLoop loop) {
        List<CfgLoopControl.Edge> result = new ArrayList<>();
        for (CfgLoopControl.Backedge backedge : loop.backedges) {
            Set<Unit> members = loop.members(backedge);
            List<CfgLoopControl.Edge> latchEdges = continuationEdgesFrom(
                    body, loop.header, members);
            if (latchEdges.isEmpty()) {
                // The dominance header often precedes the IfStmt.
                for (Unit candidate : original) {
                    if (!members.contains(candidate)
                            || !loopCfg.isDominatedBy(
                            backedge.source, candidate)) {
                        continue;
                    }
                    latchEdges = continuationEdgesFrom(
                            body, candidate, members);
                    if (!latchEdges.isEmpty()) break;
                }
            }
            if (latchEdges.isEmpty()) {
                return Collections.emptyList();
            }
            result.addAll(latchEdges);
        }
        return deduplicateEdges(result);
    }

    private static List<CfgLoopControl.Edge> continuationEdgesFrom(
            Body body, Unit candidate, Set<Unit> loopMembers) {
        CausynthBranchShape shape = CausynthBranchShape.from(body, candidate);
        if (shape == null || shape.successorCount() < 2) {
            return Collections.emptyList();
        }
        boolean outside = false;
        List<CfgLoopControl.Edge> inside = new ArrayList<>();
        for (Unit successor : shape.successors) {
            if (loopMembers.contains(successor)) {
                inside.add(new CfgLoopControl.Edge(candidate, successor));
            } else {
                outside = true;
            }
        }
        return outside && !inside.isEmpty()
                ? deduplicateEdges(inside) : Collections.emptyList();
    }

    private static List<CfgLoopControl.Edge> deduplicateEdges(
            List<CfgLoopControl.Edge> edges) {
        List<CfgLoopControl.Edge> result = new ArrayList<>();
        for (CfgLoopControl.Edge edge : edges) {
            boolean duplicate = false;
            for (CfgLoopControl.Edge retained : result) {
                if (retained.source == edge.source
                        && retained.target == edge.target) {
                    duplicate = true;
                    break;
                }
            }
            if (!duplicate) result.add(edge);
        }
        return result;
    }

    private static boolean removeEdge(
            List<CfgLoopControl.Edge> edges, Unit source, Unit target) {
        boolean removed = false;
        for (int index = edges.size() - 1; index >= 0; index--) {
            CfgLoopControl.Edge edge = edges.get(index);
            if (edge.source == source && edge.target == target) {
                edges.remove(index);
                removed = true;
            }
        }
        return removed;
    }

    /** Splits one loop {@code edge} (or exit) with one hook call. */
    private static void splitLoopEdge(
            Body body, SootMethod method, Unit source, Unit target,
            String loopId, String edge, Unit hook) {
        redirectEdge(body, method, source, target,
                Collections.singletonList(hook),
                "Could not split CFG loop " + edge + " ", loopId);
    }

    /** Routes one edge through {@code bridge}, or names the failure. */
    private static void redirectEdge(
            Body body, SootMethod method, Unit source, Unit target,
            List<Unit> bridge, String failure, String loopId) {
        List<UnitBox> matchingTargets = new ArrayList<>();
        for (UnitBox targetBox : source.getUnitBoxes()) {
            if (targetBox.getUnit() == target) {
                matchingTargets.add(targetBox);
            }
        }
        boolean fallThrough = source.fallsThrough()
                && body.getUnits().getSuccOf(source) == target;
        if (matchingTargets.isEmpty() && !fallThrough) {
            throw new IllegalStateException(failure + loopId
                    + " in " + method.getSignature());
        }
        Unit first = bridge.get(0);
        // Appended: outside every application trap.
        for (Unit hook : bridge) {
            body.getUnits().add(hook);
        }
        Unit continuation = Jimple.v().newGotoStmt(target);
        body.getUnits().add(continuation);
        for (UnitBox targetBox : matchingTargets) {
            targetBox.setUnit(first);
        }
        if (fallThrough) {
            Unit transfer = Jimple.v().newGotoStmt(first);
            body.getUnits().insertAfter(transfer, source);
        }
    }

    /**
     * Weaves the decision marker at EVERY original conditional branch of
     * every instrumented method (the plan picks methods, not
     * branches) -- but a constructor's branch before its this/super call,
     * which runs before the region it is in is entered.
     */
    private void instrumentConcolicBranches(
            Collection<String> methods, HookCatalog refs) {
        int[] woven = new int[1];
        int[] beforeEntry = new int[1];
        instrumentMethods(methods, "",
                (body, method, units, entry, lowerBound, receiver) -> {
                    for (Unit unit : snapshotUnits(body)) {
                        boolean conditional = unit instanceof IfStmt
                                || unit instanceof SwitchStmt;
                        if (!conditional) continue;
                        int unitIndex = originalUnitIndex(unit);
                        if (unitIndex < 0) continue;
                        if (lowerBound != null
                                && !unitAtOrAfter(body, lowerBound, unit)) {
                            beforeEntry[0]++;
                            continue;
                        }
                        if (unit instanceof IfStmt) {
                            instrumentConcolicBranch(body, method,
                                    (IfStmt) unit, unitIndex, refs);
                        } else {
                            instrumentConcolicSwitch(body, method,
                                    (SwitchStmt) unit, unitIndex, refs);
                        }
                        woven[0]++;
                    }
                });
        LOG.info("Wove the decision marker at {} conditional branch site(s) "
                + "across {} instrumented method(s); {} before a constructor's"
                + " this/super call left unwoven", woven[0], methods.size(),
                beforeEntry[0]);
    }

    private void instrumentConcolicBranch(Body body, SootMethod method,
                                          IfStmt branch, int unitIndex,
                                          HookCatalog refs) {
        String expression = branch.getCondition().toString();
        Unit previousTarget = branch.getTarget();
        Unit falseSuccessor = body.getUnits().getSuccOf(branch);
        if (falseSuccessor == null) {
            return;
        }

        Local prepared = newTraceLocal(body, LongType.v(),
                "$causynthPreparedBranch");
        Local vmEvent = newTraceLocal(body, LongType.v(),
                "$causynthVmBranchEvent");
        Local vmOccurrence = newTraceLocal(body, IntType.v(),
                "$causynthVmBranchOccurrence");

        insertExactBranchMarkerPrefix(body, method, branch, unitIndex,
                expression, prepared, vmEvent, vmOccurrence, refs);

        // Each arm states the decision it observed (0 fell through, 1
        // jumped) and goes on where the branch sent it: the observation
        // never steers the run.
        List<List<Unit>> arms = new ArrayList<>();
        for (int observed = 0; observed <= 1; observed++) {
            List<Unit> arm = new ArrayList<>();
            refs.bracket(arm, Hook.RESOLVE_BRANCH, prepared,
                    vmEvent, StringConstant.v(method.getSignature()),
                    IntConstant.v(unitIndex), StringConstant.v(expression),
                    IntConstant.v(observed));
            arms.add(arm);
        }
        arms.get(1).add(Jimple.v().newGotoStmt(previousTarget));
        splitIfArms(body, branch, arms.get(0), arms.get(1));
    }

    /**
     * Runs {@code fallThrough} where the branch falls through and {@code
     * taken}, appended, where it jumps; each arm ends in its own transfer.
     */
    private static void splitIfArms(Body body, IfStmt branch,
                                    List<Unit> fallThrough,
                                    List<Unit> taken) {
        insertAfterSequence(body, branch, fallThrough);
        Unit takenEntry = Jimple.v().newNopStmt();
        body.getUnits().add(takenEntry);
        for (Unit unit : taken) {
            body.getUnits().add(unit);
        }
        branch.setTarget(takenEntry);
    }

    private void instrumentConcolicSwitch(
            Body body, SootMethod method, SwitchStmt branch, int unitIndex,
            HookCatalog refs) {
        CausynthBranchShape shape = CausynthBranchShape.from(body, branch);
        if (shape == null || !shape.isSwitch()) return;
        String expression = branch.getKey().toString();
        String encodedKeys = shape.encodedCaseKeys();

        Local prepared = newTraceLocal(body, LongType.v(),
                "$causynthPreparedSwitch");
        Local vmEvent = newTraceLocal(body, LongType.v(),
                "$causynthVmSwitchEvent");
        Local vmOccurrence = newTraceLocal(body, IntType.v(),
                "$causynthVmSwitchOccurrence");

        insertExactBranchMarkerPrefix(body, method, branch, unitIndex,
                expression, prepared, vmEvent, vmOccurrence, refs);

        // One entry per case label: it states the successor it observed and
        // goes on to it, so the weave grows with the labels, not their
        // square (ZooKeeper's FinalRequestProcessor switches on 120).
        List<Unit> entries = new ArrayList<>();
        for (int observed = 0; observed < shape.successorCount(); observed++) {
            Unit entry = Jimple.v().newNopStmt();
            entries.add(entry);
            body.getUnits().add(entry);
            refs.bracket(body.getUnits(),
                    Hook.RESOLVE_SWITCH_BRANCH, prepared, vmEvent,
                    StringConstant.v(method.getSignature()),
                    IntConstant.v(unitIndex), StringConstant.v(expression),
                    StringConstant.v(shape.kind),
                    StringConstant.v(encodedKeys), IntConstant.v(observed));
            body.getUnits().add(Jimple.v().newGotoStmt(
                    shape.successors.get(observed)));
        }
        for (int index = 0; index < shape.successorCount(); index++) {
            retargetSwitch(branch, shape, index, entries.get(index));
        }
    }

    /** Points the switch's {@code index}-th successor (shape order) there. */
    private static void retargetSwitch(SwitchStmt branch,
                                       CausynthBranchShape shape, int index,
                                       Unit entry) {
        if (index == shape.defaultSuccessorIndex) {
            branch.setDefaultTarget(entry);
        } else {
            branch.setTarget(index, entry);
        }
    }

    private void insertExactBranchMarkerPrefix(
            Body body, SootMethod method, Unit branch, int unitIndex,
            String expression, Local prepared, Local vmEvent,
            Local vmOccurrence, HookCatalog refs) {
        // The native marker must be the last invocation before the branch.
        Unit noMarkerPath = Jimple.v().newNopStmt();
        List<Unit> beforeBranch = new ArrayList<>();
        emit(beforeBranch, refs.ref(Hook.PAUSE_VM_PATH_CONDITION));
        emit(beforeBranch, prepared, refs.ref(Hook.PREPARE_BRANCH),
                StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex), StringConstant.v(expression));
        beforeBranch.add(Jimple.v().newAssignStmt(vmEvent,
                LongConstant.v(0L)));
        beforeBranch.add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(prepared, LongConstant.v(0L)),
                noMarkerPath));
        emit(beforeBranch, refs.ref(Hook.RESUME_VM_PATH_CONDITION));
        beforeBranch.add(Jimple.v().newAssignStmt(vmOccurrence,
                Jimple.v().newCastExpr(prepared, IntType.v())));
        emit(beforeBranch, vmEvent, refs.ref(Hook.MARK_CONCOLIC_BRANCH),
                StringConstant.v(SiteId.of(method.getSignature(), unitIndex)),
                vmOccurrence);
        Unit exactTransfer = Jimple.v().newGotoStmt(branch);
        beforeBranch.add(exactTransfer);
        beforeBranch.add(noMarkerPath);
        emit(beforeBranch, refs.ref(Hook.RESUME_VM_PATH_CONDITION));
        insertBeforeSequence(body, branch, beforeBranch);
        // Insertion redirects old targets to the prefix.
        ((soot.jimple.GotoStmt) exactTransfer).setTarget(branch);
    }

    private static Unit originalUnit(Body body, int requestedIndex) {
        List<Unit> current = snapshotUnits(body);
        boolean tagged = false;
        for (Unit unit : current) {
            int index = originalUnitIndex(unit);
            if (index == requestedIndex && index >= 0) return unit;
            tagged |= index >= 0;
        }
        // Once tags exist, an untagged unit is woven.
        if (tagged) {
            return null;
        }
        return requestedIndex >= 0 && requestedIndex < current.size()
                ? current.get(requestedIndex) : null;
    }

    static List<Unit> snapshotUnits(Body body) {
        List<Unit> units = new ArrayList<>();
        for (Unit unit : body.getUnits()) {
            units.add(unit);
        }
        return units;
    }

    /** Freezes one body's numbering ({@link #originalUnitIndex}). */
    static void tagOriginalUnits(List<Unit> units) {
        // Trace and concolic instrumentation may run in the same transform.
        for (Unit unit : units) {
            if (originalUnitIndex(unit) >= 0) return;
        }
        for (int index = 0; index < units.size(); index++) {
            units.get(index).addTag(new OriginalUnitIndexTag(index));
        }
    }

    /**
     * The active body of the method a selection names, or the refusal
     * {@code code_UNAVAILABLE} / {@code code_NOT_CONCRETE} naming
     * {@code subject}.
     */
    private static Body selectedBody(String signature, String code,
                                     String subject) {
        SootMethod method = CausynthStaticFacts.method(signature);
        if (method == null) {
            throw new IllegalStateException(code + "_UNAVAILABLE: "
                    + subject);
        }
        if (!method.isConcrete()) {
            throw new IllegalStateException(code + "_NOT_CONCRETE: "
                    + subject);
        }
        try {
            return method.retrieveActiveBody();
        } catch (RuntimeException failure) {
            throw new IllegalStateException(code + "_UNAVAILABLE: "
                    + subject, failure);
        }
    }

    /**
     * The one original unit at {@code unitIndex}, a call: refused as
     * {@code notUnique} when it is not one statement, {@code notFound} when
     * it is absent or calls nothing.
     */
    private static Stmt originalCall(Body body, int unitIndex, String site,
                                     String notUnique, String notFound) {
        tagOriginalUnits(snapshotUnits(body));
        Stmt selected = null;
        for (Unit unit : snapshotUnits(body)) {
            if (originalUnitIndex(unit) != unitIndex) continue;
            if (selected != null || !(unit instanceof Stmt)) {
                throw new IllegalStateException(notUnique + ": " + site);
            }
            selected = (Stmt) unit;
        }
        if (selected == null || !selected.containsInvokeExpr()) {
            throw new IllegalStateException(notFound + ": " + site);
        }
        return selected;
    }

    /** Refuses a call whose callee is not the declared one. */
    private static void requireCallee(Stmt call, String declared,
                                      String mismatch, String site) {
        String found = call.getInvokeExpr().getMethodRef().getSignature();
        if (!declared.equals(found)) {
            throw new IllegalStateException(mismatch + ": " + site
                    + " expected " + declared + " but found " + found);
        }
    }

    /** The parameter local bound at {@code index}, or {@code null}. */
    private static Local parameterLocal(Body body, int index) {
        try {
            return body.getParameterLocal(index);
        } catch (RuntimeException unavailable) {
            return null;
        }
    }

    /** The method's own {@code this}, or {@link NullConstant} without one. */
    private static Value receiverOrNull(Body body, SootMethod method) {
        if (method.isStatic()) {
            return NullConstant.v();
        }
        try {
            Local thisLocal = body.getThisLocal();
            return thisLocal == null ? NullConstant.v() : thisLocal;
        } catch (RuntimeException ignored) {
            return NullConstant.v();
        }
    }

    /** The scene's class for a name, added as a phantom when it is absent. */
    static SootClass phantomClass(String name) {
        SootClass existing = Scene.v().getSootClassUnsafe(name);
        if (existing != null) {
            return existing;
        }
        SootClass created = new SootClass(name, Modifier.PUBLIC);
        created.setPhantomClass();
        Scene.v().addClass(created);
        return created;
    }

    private void instrumentRichMethod(
            Body body, SootMethod method, List<Unit> originalUnits,
            Unit insertionPoint, Unit lowerBound, Value receiver,
            HookCatalog refs, String openedRegionId, TracedRows traced) {
        Local callId = newTraceLocal(body, LongType.v(), "$causynthCallId");
        List<Unit> entryUnits = new ArrayList<>();
        entryUnits.add(Jimple.v().newAssignStmt(callId, LongConstant.v(0L)));
        emit(entryUnits, callId, refs.ref(Hook.ENTER_METHOD),
                StringConstant.v(method.getSignature()), receiver,
                StringConstant.v(openedRegionId));
        for (int index = 0; index < method.getParameterCount(); index++) {
            Value parameter = parameterLocal(body, index);
            if (parameter == null) continue;
            boolean read = traced.methodArgument(method.getSignature(), index);
            emit(entryUnits, refs.ref(Hook.RECORD_METHOD_ARGUMENT), callId,
                    IntConstant.v(index),
                    StringConstant.v(method.getParameterType(index).toString()),
                    read ? objectArg(body, parameter, entryUnits)
                            : NullConstant.v(),
                    read ? primitiveValueString(body, parameter, entryUnits)
                            : StringConstant.v(""),
                    IntConstant.v(read ? 1 : 0));
        }
        insertBeforeOrAppendNoRedirect(body, insertionPoint, entryUnits);

        for (int unitIndex = instrumentableFrom(originalUnits, lowerBound);
                unitIndex >= 0 && unitIndex < originalUnits.size();
                unitIndex++) {
            Unit unit = originalUnits.get(unitIndex);
            if (!(unit instanceof Stmt)) {
                continue;
            }
            Stmt stmt = (Stmt) unit;
            if (stmt.containsInvokeExpr()
                    && !isRecorderInvoke(stmt.getInvokeExpr())) {
                instrumentCallSite(body, method, stmt, unitIndex, callId,
                        refs, traced);
            }
            if (stmt instanceof IfStmt) {
                instrumentBranch(body, method, (IfStmt) stmt, unitIndex,
                        callId, refs);
            } else if (stmt instanceof SwitchStmt) {
                instrumentSwitchBranch(body, method,
                        (SwitchStmt) stmt, unitIndex, callId, refs);
            }
            if (stmt instanceof ReturnStmt
                    || stmt instanceof ReturnVoidStmt) {
                insertMethodExit(body, stmt, stmt instanceof ReturnStmt
                                ? ((ReturnStmt) stmt).getOp()
                                : NullConstant.v(),
                        refs.ref(Hook.EXIT_ACTIVE_METHOD),
                        traced.methodExit(method.getSignature()));
            }
        }
        addThrowHandler(body, insertionPoint, refs, Hook.THROW_ACTIVE_METHOD,
                "$causynthThrown");
    }

    /**
     * One call site's hooks.  Every hook is called, so every row keeps its
     * number; a row the aggregation does not read ({@link TracedRows}) is
     * not written, and its values are not even taken.
     */
    private void instrumentCallSite(Body body, SootMethod method, Stmt stmt,
                                    int unitIndex, Local ownerCallId,
                                    HookCatalog refs, TracedRows traced) {
        InvokeExpr invoke = stmt.getInvokeExpr();
        String siteId = SiteId.render(method.getSignature(), unitIndex);
        String callee = invoke.getMethodRef().getSignature();
        boolean read = traced.callSite(siteId, callee);
        List<Unit> before = new ArrayList<>();
        Value receiverBase = runtimeCallSiteReceiver(invoke);
        Value receiver = receiverBase == null || !read
                ? NullConstant.v() : objectArg(body, receiverBase, before);
        Local invocationId = newTraceLocal(body, LongType.v(), "$causynthInvocation");
        emit(before, invocationId, refs.ref(Hook.BEGIN_CALL), ownerCallId,
                StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex), StringConstant.v(callee), receiver,
                IntConstant.v(read ? 1 : 0));
        for (int index = 0; index < invoke.getArgCount(); index++) {
            Value argument = invoke.getArg(index);
            boolean argumentRead = traced.callArgument(siteId, callee, index);
            Type declaredType = index < invoke.getMethodRef().parameterTypes().size()
                    ? invoke.getMethodRef().parameterType(index) : argument.getType();
            emit(before, refs.ref(Hook.RECORD_CALL_ARGUMENT), invocationId,
                    IntConstant.v(index),
                    StringConstant.v(declaredType.toString()),
                    argumentRead ? objectArg(body, argument, before)
                            : NullConstant.v(),
                    argumentRead ? primitiveValueString(body, argument, before)
                            : StringConstant.v(""),
                    IntConstant.v(argumentRead ? 1 : 0));
        }
        insertBeforeSequence(body, stmt, before);

        Value returnValue = runtimeCallSiteReturnValue(stmt, invoke);
        List<Unit> after = new ArrayList<>();
        Value returnObject = read ? objectArg(body, returnValue, after)
                : NullConstant.v();
        Value primitiveReturn = read
                ? primitiveValueString(body, returnValue, after)
                : StringConstant.v("");
        emit(after, refs.ref(Hook.END_CALL), invocationId, returnObject,
                primitiveReturn);
        insertAfterSequence(body, stmt, after);
    }

    /** Returns the object on which an ordinary instance call is dispatched. */
    static Value runtimeCallSiteReceiver(InvokeExpr invoke) {
        if (!(invoke instanceof InstanceInvokeExpr)
                || "<init>".equals(invoke.getMethodRef().name())) {
            return null;
        }
        return ((InstanceInvokeExpr) invoke).getBase();
    }

    /** The call's result; for a constructor, its initialized receiver. */
    static Value runtimeCallSiteReturnValue(Stmt stmt, InvokeExpr invoke) {
        if (invoke instanceof InstanceInvokeExpr
                && "<init>".equals(invoke.getMethodRef().name())) {
            return ((InstanceInvokeExpr) invoke).getBase();
        }
        return stmt instanceof AssignStmt
                ? ((AssignStmt) stmt).getLeftOp() : NullConstant.v();
    }


    private void instrumentBranch(Body body, SootMethod method, IfStmt branch,
                                  int unitIndex, Local callId,
                                  HookCatalog refs) {
        String expression = branch.getCondition().toString();
        List<List<Unit>> arms = new ArrayList<>();
        for (int outcome = 0; outcome <= 1; outcome++) {
            List<Unit> arm = new ArrayList<>();
            emit(arm, refs.ref(Hook.RECORD_BRANCH), callId,
                    StringConstant.v(method.getSignature()),
                    IntConstant.v(unitIndex), StringConstant.v(expression),
                    IntConstant.v(outcome));
            arms.add(arm);
        }
        arms.get(1).add(Jimple.v().newGotoStmt(branch.getTarget()));
        splitIfArms(body, branch, arms.get(0), arms.get(1));
    }

    private void instrumentSwitchBranch(
            Body body, SootMethod method, SwitchStmt branch, int unitIndex,
            Local callId, HookCatalog refs) {
        CausynthBranchShape shape = CausynthBranchShape.from(body, branch);
        if (shape == null || !shape.isSwitch()) return;
        String expression = branch.getKey().toString();
        String keys = shape.encodedCaseKeys();
        for (int successorIndex = 0;
             successorIndex < shape.successorCount(); successorIndex++) {
            Unit originalTarget = shape.successors.get(successorIndex);
            Unit entry = Jimple.v().newNopStmt();
            List<Unit> path = new ArrayList<>();
            path.add(entry);
            emit(path, refs.ref(Hook.RECORD_SWITCH_BRANCH), callId,
                    StringConstant.v(method.getSignature()),
                    IntConstant.v(unitIndex), StringConstant.v(expression),
                    IntConstant.v(successorIndex),
                    StringConstant.v(shape.kind), StringConstant.v(keys));
            path.add(Jimple.v().newGotoStmt(originalTarget));
            for (Unit unit : path) body.getUnits().add(unit);
            retargetSwitch(branch, shape, successorIndex, entry);
        }
    }

    private void insertMethodExit(Body body, Stmt returnUnit, Value returnValue,
                                  SootMethodRef exitRef, boolean read) {
        List<Unit> units = new ArrayList<>();
        Value objectValue = read ? objectArg(body, returnValue, units)
                : NullConstant.v();
        Value primitiveValue = read
                ? primitiveValueString(body, returnValue, units)
                : StringConstant.v("");
        emit(units, exitRef, objectValue, primitiveValue,
                IntConstant.v(read ? 1 : 0));
        insertBeforeSequence(body, returnUnit, units);
    }

    /**
     * THE WOVEN-TRAP RULE: a woven catch-all opens after the construct's
     * prologue, never inside it.  The JVM merges every range unit's frame
     * into the handler's, so a range covering the store of a local the
     * handler reads fails verification.  The prologue is entered by
     * fall-through only, so its stores dominate the range.
     *
     * @return the unit after {@code prologue}, or null (no trap) at body end
     */
    static Unit afterWovenPrologue(Body body, List<Unit> prologue) {
        if (prologue == null || prologue.isEmpty()) return null;
        return body.getUnits().getSuccOf(prologue.get(prologue.size() - 1));
    }

    /**
     * Appends a catch-all that reports the exceptional exit, bracketed, and
     * rethrows; {@code identity} precedes the throwable in the hook's
     * arguments.  {@code start} must obey {@link #afterWovenPrologue}.
     */
    private static void addThrowHandler(Body body, Unit start,
                                        HookCatalog refs, Hook throwHook,
                                        String localName, Value... identity) {
        appendCatchAll(body, start, localName, (units, caught) -> {
            Value[] args = Arrays.copyOf(identity, identity.length + 1);
            args[identity.length] = caught;
            refs.bracket(units, throwHook, args);
        });
    }

    /**
     * Appends a catch-all handler from {@code start} to the body end: bind
     * the throwable, run {@code report}, rethrow.  No trap at a null start.
     */
    static void appendCatchAll(Body body, Unit start,
                                       String localName,
                                       BiConsumer<List<Unit>, Local> report) {
        if (start == null) {
            return;
        }
        Local caught = newTraceLocal(body, RefType.v("java.lang.Throwable"),
                localName);
        List<Unit> units = new ArrayList<>();
        units.add(Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef()));
        report.accept(units, caught);
        units.add(Jimple.v().newThrowStmt(caught));
        Unit handler = units.get(0);
        for (Unit unit : units) {
            body.getUnits().add(unit);
        }
        body.getTraps().add(Jimple.v().newTrap(
                Scene.v().getSootClass("java.lang.Throwable"), start, handler,
                handler));
    }

    private static boolean isRecorderInvoke(InvokeExpr invoke) {
        return invoke != null
                && TRACE_RECORDER_CLASS.equals(invoke.getMethodRef()
                .declaringClass().getName());
    }

    static void insertBeforeSequence(Body body, Unit anchor,
                                             List<Unit> units) {
        for (Unit unit : units) {
            body.getUnits().insertBefore(unit, anchor);
        }
    }

    static void insertBeforeOrAppendNoRedirect(Body body, Unit anchor,
                                                        List<Unit> units) {
        if (anchor == null) {
            for (Unit unit : units) {
                body.getUnits().add(unit);
            }
            return;
        }
        for (Unit unit : units) {
            body.getUnits().insertBeforeNoRedirect(unit, anchor);
        }
    }

    static void insertAfterSequence(Body body, Unit anchor,
                                            List<Unit> units) {
        Unit current = anchor;
        for (Unit unit : units) {
            body.getUnits().insertAfter(unit, current);
            current = unit;
        }
    }

    private void instrumentFieldTrace(Body body, SootMethod method,
                                      SootMethodRef recordFieldRef,
                                      List<Unit> units,
                                      Unit lowerBound) {
        Value methodReceiver = receiverOrNull(body, method);
        for (int unitIndex = instrumentableFrom(units, lowerBound);
                unitIndex >= 0 && unitIndex < units.size(); unitIndex++) {
            Unit unit = units.get(unitIndex);
            if (!(unit instanceof Stmt)) {
                continue;
            }
            Stmt stmt = (Stmt) unit;
            if (stmt instanceof AssignStmt) {
                AssignStmt assign = (AssignStmt) stmt;
                Value left = assign.getLeftOp();
                Value right = assign.getRightOp();
                if (left instanceof FieldRef) {
                    insertFieldTrace(body, unit, recordFieldRef, "FIELD_WRITE",
                            method.getSignature(), unitIndex, (FieldRef) left,
                            methodReceiver, right, true);
                }
                if (right instanceof FieldRef) {
                    insertFieldTrace(body, unit, recordFieldRef, "FIELD_READ",
                            method.getSignature(), unitIndex, (FieldRef) right,
                            methodReceiver, left, true);
                }
            } else {
                for (ValueBox box : stmt.getUseBoxes()) {
                    Value value = box.getValue();
                    if (value instanceof FieldRef) {
                        insertFieldTrace(body, unit, recordFieldRef, "FIELD_READ",
                                method.getSignature(), unitIndex, (FieldRef) value,
                                methodReceiver, value, false);
                    }
                }
            }
        }
    }

    private void insertFieldTrace(
            Body body, Unit unit, SootMethodRef recordFieldRef,
            String kind, String method, int unitIndex,
            FieldRef fieldRef, Value methodReceiverValue, Value value,
            boolean fieldValueIsReadValue) {
        String field = CausynthStaticFacts.declaredFieldSignature(
                fieldRef.getFieldRef());
        List<Unit> prefixUnits = new ArrayList<>();
        Value methodReceiver = objectArg(body, methodReceiverValue, prefixUnits);
        // A static field has no Java receiver object.
        Value receiverValue = fieldRef instanceof InstanceFieldRef
                ? ((InstanceFieldRef) fieldRef).getBase()
                : StringConstant.v(field);
        Value receiver = objectArg(body, receiverValue, prefixUnits);
        Value valueObject = objectArg(body, value, prefixUnits);
        Value primitiveValue = primitiveValueString(body, value, prefixUnits);
        Stmt traceCall = invoke(recordFieldRef, StringConstant.v(kind),
                StringConstant.v(method), IntConstant.v(unitIndex),
                StringConstant.v(field), methodReceiver, receiver, valueObject,
                primitiveValue);
        prefixUnits.add(traceCall);
        if (fieldValueIsReadValue) {
            insertAfterSequence(body, unit, prefixUnits);
        } else {
            insertBeforeSequence(body, unit, prefixUnits);
        }
    }

    private static Value objectArg(Body body, Value value, List<Unit> prefixUnits) {
        if (value == null || value instanceof NullConstant) {
            return NullConstant.v();
        }
        if (value.getType() instanceof RefType || value.getType() instanceof ArrayType) {
            return immediateValue(body, value, prefixUnits);
        }
        return NullConstant.v();
    }

    private static Value primitiveValueString(Body body, Value value, List<Unit> prefixUnits) {
        if (value == null || value instanceof NullConstant) {
            return StringConstant.v("");
        }
        SootClass stringClass = Scene.v().getSootClass("java.lang.String");
        Type type = value.getType();
        boolean intLike = type instanceof IntType || type instanceof ByteType
                || type instanceof ShortType || type instanceof CharType;
        Type declared = intLike ? IntType.v()
                : type instanceof BooleanType ? BooleanType.v()
                : type instanceof LongType ? LongType.v() : null;
        if (declared == null) return StringConstant.v("");
        SootMethodRef ref = Scene.v().makeMethodRef(stringClass, "valueOf",
                Collections.singletonList(declared),
                RefType.v("java.lang.String"), true);
        return primitiveStringLocal(body, intLike && !(type instanceof IntType)
                        ? Jimple.v().newCastExpr(value, IntType.v()) : value,
                ref, prefixUnits);
    }

    private static Value primitiveStringLocal(Body body, Value value, SootMethodRef ref,
                                             List<Unit> prefixUnits) {
        Value source = immediateValue(body, value, prefixUnits);
        Local tmp = newTraceLocal(body, RefType.v("java.lang.String"), "$causynthPrim");
        emit(prefixUnits, tmp, ref, source);
        return tmp;
    }

    /** One static hook invocation as a unit. */
    private static Stmt invoke(SootMethodRef hook, Value... args) {
        return Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(hook, Arrays.asList(args)));
    }

    /** One assignment of a static hook's result as a unit. */
    private static Stmt invokeTo(Value target, SootMethodRef hook,
                                 Value... args) {
        return Jimple.v().newAssignStmt(target,
                Jimple.v().newStaticInvokeExpr(hook, Arrays.asList(args)));
    }

    /** Appends {@code hook(args)} to {@code units}. */
    private static void emit(Collection<Unit> units, SootMethodRef hook,
                             Value... args) {
        units.add(invoke(hook, args));
    }

    /** Appends {@code target = hook(args)} to {@code units}. */
    private static void emit(Collection<Unit> units, Value target,
                             SootMethodRef hook, Value... args) {
        units.add(invokeTo(target, hook, args));
    }

    private static Value immediateValue(Body body, Value value, List<Unit> prefixUnits) {
        if (value instanceof Local || value instanceof Constant) {
            return value;
        }
        Local tmp = newTraceLocal(body, value.getType(), "$causynthValue");
        prefixUnits.add(Jimple.v().newAssignStmt(tmp, value));
        return tmp;
    }

    static Local newTraceLocal(Body body, Type type, String prefix) {
        int index = body.getLocals().size();
        while (true) {
            String name = prefix + index;
            boolean exists = false;
            for (Local local : body.getLocals()) {
                if (name.equals(local.getName())) {
                    exists = true;
                    break;
                }
            }
            if (!exists) {
                Local local = Jimple.v().newLocal(name, type);
                body.getLocals().add(local);
                return local;
            }
            index++;
        }
    }

    private static Unit firstNonIdentity(Body body) {
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof IdentityStmt)) {
                return unit;
            }
        }
        return null;
    }

    /** Returns the first verifier-safe instrumentation point. */
    static Unit safeInstrumentationEntry(Body body, SootMethod method) {
        Unit first = firstNonIdentity(body);
        if (method == null || !method.isConstructor()) {
            return first;
        }
        Local thisLocal;
        try {
            thisLocal = body.getThisLocal();
        } catch (RuntimeException unavailable) {
            return null;
        }
        Set<Local> thisAliases = Collections.newSetFromMap(
                new IdentityHashMap<Local, Boolean>());
        thisAliases.add(thisLocal);
        for (Unit unit : body.getUnits()) {
            if (unit instanceof Stmt
                    && ((Stmt) unit).containsInvokeExpr()) {
                InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
                if (invoke instanceof SpecialInvokeExpr
                        && "<init>".equals(invoke.getMethodRef().name())
                        && localAlias(((SpecialInvokeExpr) invoke).getBase(),
                        thisAliases)) {
                    return body.getUnits().getSuccOf(unit);
                }
            }
            if (unit instanceof AssignStmt
                    && ((AssignStmt) unit).getLeftOp() instanceof Local) {
                AssignStmt assignment = (AssignStmt) unit;
                Local left = (Local) assignment.getLeftOp();
                Value right = assignment.getRightOp();
                if (right instanceof CastExpr) {
                    right = ((CastExpr) right).getOp();
                }
                if (localAlias(right, thisAliases)) {
                    thisAliases.add(left);
                } else {
                    thisAliases.remove(left);
                }
            }
        }
        return null;
    }

    /** Whether {@code value} is one of Soot's locals for uninitialized this. */
    private static boolean localAlias(Value value, Set<Local> aliases) {
        if (!(value instanceof Local)) return false;
        for (Local alias : aliases) {
            if (value == alias || value.equivTo(alias)) return true;
        }
        return false;
    }

    private static boolean unitAtOrAfter(
            Body body, Unit lowerBound, Unit candidate) {
        if (body == null || lowerBound == null || candidate == null) {
            return false;
        }
        boolean safe = false;
        for (Unit unit : body.getUnits()) {
            if (unit == lowerBound) safe = true;
            if (unit == candidate) return safe;
        }
        return false;
    }

    enum Hook {
        ENTER_METHOD,
        RECORD_METHOD_ARGUMENT,
        BEGIN_CALL,
        RECORD_CALL_ARGUMENT,
        END_CALL,
        RECORD_BRANCH,
        RECORD_SWITCH_BRANCH,
        EXIT_ACTIVE_METHOD,
        THROW_ACTIVE_METHOD,
        RECORD_FIELD,
        ENTER_LOOP_ROOT_INVOCATION_FRAME,
        EXIT_LOOP_ROOT_INVOCATION_FRAME,
        THROW_LOOP_ROOT_INVOCATION_FRAME,
        ENTER_REGION_FRAME,
        ENTER_REGION_ENTRY,
        EXIT_REGION_ENTRY,
        THROW_REGION_ENTRY,
        START_WORK,
        CLAIM_START,
        END_CLAIM,
        CLAIM_ITEM,
        ENTER_METHOD_FRAME,
        EXIT_METHOD_FRAME,
        THROW_METHOD_FRAME,
        ENTER_CONFIGURED_SOURCE_PHASE_SITE,
        EXIT_CONFIGURED_SOURCE_PHASE_SITE,
        THROW_CONFIGURED_SOURCE_PHASE_SITE,
        READ_CONFIGURATION,
        ENTER_ACCESSOR_CALL_CONTEXT,
        EXIT_ACCESSOR_CALL_CONTEXT,
        OBSERVE_TRACKED_SITE,
        OBSERVE_TRACKED_CONTAINER,
        MATERIALIZE_ARGUMENT,
        SYMBOLIZE_ARGUMENT,
        MATERIALIZE_METHOD_ARGUMENT,
        SYMBOLIZE_METHOD_ARGUMENT,
        MATERIALIZE_REFERENCE,
        MATERIALIZE_PRIMITIVE,
        MATERIALIZE_STATIC_PRIMITIVE_FIELD,
        MATERIALIZE_FIELD,
        EXPORT_COMMUNICATION_LEAF,
        ATTACH_COMMUNICATION_LEAF,
        PUSH_OUTBOUND_MESSAGE_FRAME,
        POP_OUTBOUND_MESSAGE_FRAME,
        PUSH_INBOUND_MESSAGE_FRAME,
        POP_INBOUND_MESSAGE_FRAME,
        PAUSE_OBSERVATION,
        RESUME_OBSERVATION,
        PAUSE_VM_PATH_CONDITION,
        RESUME_VM_PATH_CONDITION,
        PREPARE_BRANCH,
        MARK_CONCOLIC_BRANCH,
        RESOLVE_BRANCH,
        RESOLVE_SWITCH_BRANCH,
        CHECK_LOOP_BACKEDGE,
        CHECK_REPLAY_LOOP_BODY,
        EXIT_REGION_FRAME,
        THROW_REGION_FRAME
    }

    /** Typed registry for static instrumentation hooks. */
    static final class HookCatalog {
        private final EnumMap<Hook, SootMethodRef> refs =
                new EnumMap<>(Hook.class);

        private HookCatalog add(Hook hook, SootClass owner, String method,
                                Type result, Type... parameters) {
            refs.put(hook, Scene.v().makeMethodRef(owner, method,
                    Arrays.asList(parameters), result, true));
            return this;
        }

        private SootMethodRef ref(Hook hook) {
            return refs.get(hook);
        }

        /** THE hooks both passes weave, declared once for one index. */
        private HookCatalog shared(SootClass owner) {
            Type string = RefType.v("java.lang.String");
            Type object = RefType.v("java.lang.Object");
            return add(Hook.START_WORK, owner, "startWork", VoidType.v(),
                    string, object)
                    .add(Hook.CLAIM_START, owner, "claimStart", LongType.v(),
                            object)
                    .add(Hook.END_CLAIM, owner, "endClaim", VoidType.v(),
                            LongType.v())
                    .add(Hook.CLAIM_ITEM, owner, "claimItem", VoidType.v(),
                            object)
                    .add(Hook.ENTER_METHOD_FRAME, owner, "enterMethodFrame",
                            LongType.v(), string, object)
                    .add(Hook.EXIT_METHOD_FRAME, owner, "exitMethodFrame",
                            VoidType.v(), LongType.v())
                    .add(Hook.THROW_METHOD_FRAME, owner, "throwMethodFrame",
                            VoidType.v(), LongType.v(),
                            RefType.v("java.lang.Throwable"));
        }

        /**
         * Appends {@code hook(args)}, paused if this pass has a pause hook
         * (the recording has none).
         * @return the hook call
         */
        Unit bracket(Collection<Unit> units, Hook hook, Value... args) {
            return bracketed(units, invoke(ref(hook), args));
        }

        /** Appends {@code target = hook(args)}, the same way. */
        Unit bracket(Collection<Unit> units, Value target, Hook hook,
                     Value... args) {
            return bracketed(units, invokeTo(target, ref(hook), args));
        }

        private Unit bracketed(Collection<Unit> units, Unit call) {
            boolean observed = ref(Hook.PAUSE_OBSERVATION) != null;
            if (observed) emit(units, ref(Hook.PAUSE_OBSERVATION));
            units.add(call);
            if (observed) emit(units, ref(Hook.RESUME_OBSERVATION));
            return call;
        }

        private static HookCatalog trace() {
            SootClass recorder = phantomClass(TRACE_RECORDER_CLASS);
            Type string = RefType.v("java.lang.String");
            Type object = RefType.v("java.lang.Object");
            return new HookCatalog()
                    .add(Hook.ENTER_METHOD, recorder, "enterMethod",
                            LongType.v(), string, object, string)
                    .shared(recorder)
                    .add(Hook.RECORD_METHOD_ARGUMENT, recorder,
                            "recordMethodArgument", VoidType.v(), LongType.v(),
                            IntType.v(), string, object, string,
                            BooleanType.v())
                    .add(Hook.BEGIN_CALL, recorder, "beginCall", LongType.v(),
                            LongType.v(), string, IntType.v(), string, object,
                            BooleanType.v())
                    .add(Hook.RECORD_CALL_ARGUMENT, recorder,
                            "recordCallArgument", VoidType.v(), LongType.v(),
                            IntType.v(), string, object, string,
                            BooleanType.v())
                    .add(Hook.END_CALL, recorder, "endCall", VoidType.v(),
                            LongType.v(), object, string)
                    .add(Hook.RECORD_BRANCH, recorder, "recordBranch",
                            VoidType.v(), LongType.v(), string, IntType.v(),
                            string, BooleanType.v())
                    .add(Hook.RECORD_SWITCH_BRANCH, recorder,
                            "recordSwitchBranch", VoidType.v(), LongType.v(),
                            string, IntType.v(), string, IntType.v(), string,
                            string)
                    .add(Hook.EXIT_ACTIVE_METHOD, recorder, "exitActiveMethod",
                            VoidType.v(), object, string, BooleanType.v())
                    .add(Hook.THROW_ACTIVE_METHOD, recorder,
                            "throwActiveMethod", VoidType.v(),
                            RefType.v("java.lang.Throwable"))
                    .add(Hook.RECORD_FIELD, recorder, "recordField",
                            VoidType.v(), string, string, IntType.v(), string,
                            object, object, object, string);
        }

        private static HookCatalog concolic() {
            SootClass runtime = phantomClass(CONCOLIC_REGION_RUNTIME_CLASS);
            Type string = RefType.v("java.lang.String");
            Type object = RefType.v("java.lang.Object");
            SootClass system = phantomClass("java.lang.System");
            return new HookCatalog()
                    .add(Hook.ENTER_LOOP_ROOT_INVOCATION_FRAME, runtime,
                            "enterLoopRootInvocationFrame", LongType.v(),
                            string, string, object, ArrayType.v(object, 1))
                    .add(Hook.EXIT_LOOP_ROOT_INVOCATION_FRAME, runtime,
                            "exitLoopRootInvocationFrame", VoidType.v(),
                            LongType.v())
                    .add(Hook.THROW_LOOP_ROOT_INVOCATION_FRAME, runtime,
                            "throwLoopRootInvocationFrame", VoidType.v(),
                            LongType.v(),
                            RefType.v("java.lang.Throwable"))
                    .add(Hook.ENTER_REGION_FRAME, runtime, "enterRegionFrame",
                            LongType.v(), string, string, object,
                            ArrayType.v(object, 1))
                    .add(Hook.ENTER_REGION_ENTRY, runtime,
                            "enterRegionEntry", LongType.v(), string,
                            string, object)
                    .add(Hook.EXIT_REGION_ENTRY, runtime,
                            "exitRegionEntry", VoidType.v(), LongType.v())
                    .add(Hook.THROW_REGION_ENTRY, runtime,
                            "throwRegionEntry", VoidType.v(), LongType.v(),
                            RefType.v("java.lang.Throwable"))
                    .shared(runtime)
                    .add(Hook.ENTER_CONFIGURED_SOURCE_PHASE_SITE, runtime,
                            "enterConfiguredSourcePhaseCallSite",
                            LongType.v(), string, IntType.v(), string)
                    .add(Hook.EXIT_CONFIGURED_SOURCE_PHASE_SITE, runtime,
                            "exitConfiguredSourcePhaseCallSite", VoidType.v(),
                            LongType.v(), object, string)
                    .add(Hook.THROW_CONFIGURED_SOURCE_PHASE_SITE, runtime,
                            "throwConfiguredSourcePhaseCallSite", VoidType.v(),
                            LongType.v())
                    .add(Hook.READ_CONFIGURATION, runtime,
                            "readConfiguration", VoidType.v(), string,
                            object, string)
                    .add(Hook.ENTER_ACCESSOR_CALL_CONTEXT, runtime,
                            "enterAccessorCallContext", LongType.v(), string,
                            IntType.v(), string, string, object)
                    .add(Hook.EXIT_ACCESSOR_CALL_CONTEXT, runtime,
                            "exitAccessorCallContext", VoidType.v(), LongType.v())
                    .add(Hook.OBSERVE_TRACKED_SITE, runtime,
                            "observeTrackedSite", VoidType.v(), string,
                            string, object)
                    .add(Hook.OBSERVE_TRACKED_CONTAINER, runtime,
                            "observeTrackedContainer", VoidType.v(), string,
                            string, object, BooleanType.v())
                    .add(Hook.MATERIALIZE_ARGUMENT, runtime,
                            "materializeArgument", object, LongType.v(),
                            IntType.v(), object, string)
                    .add(Hook.SYMBOLIZE_ARGUMENT, runtime, "symbolizeArgument",
                            VoidType.v(), LongType.v(), IntType.v(), object,
                            string)
                    .add(Hook.MATERIALIZE_METHOD_ARGUMENT, runtime,
                            "materializeMethodArgument", object, string,
                            IntType.v(), object, string)
                    .add(Hook.SYMBOLIZE_METHOD_ARGUMENT, runtime,
                            "symbolizeMethodArgument", VoidType.v(), string,
                            IntType.v(), object, string)
                    .add(Hook.MATERIALIZE_REFERENCE, runtime,
                            "materializeReference", object, string,
                            IntType.v(), string, object)
                    .add(Hook.MATERIALIZE_PRIMITIVE, runtime,
                            "materializePrimitive", object, string,
                            IntType.v(), string, object)
                    .add(Hook.MATERIALIZE_STATIC_PRIMITIVE_FIELD, runtime,
                            "materializeStaticPrimitiveField", object, string,
                            IntType.v(), string, string, object)
                    .add(Hook.MATERIALIZE_FIELD, runtime, "materializeField",
                            VoidType.v(), string, IntType.v(), object, string,
                            string)
                    .add(Hook.EXPORT_COMMUNICATION_LEAF, runtime,
                            "exportCommunicationLeaf", VoidType.v(), string,
                            object, string, string)
                    .add(Hook.ATTACH_COMMUNICATION_LEAF, runtime,
                            "attachCommunicationLeaf", VoidType.v(), string,
                            object, string, string)
                    .add(Hook.PUSH_OUTBOUND_MESSAGE_FRAME, runtime,
                            "pushOutboundMessageFrame", VoidType.v())
                    .add(Hook.POP_OUTBOUND_MESSAGE_FRAME, runtime,
                            "popOutboundMessageFrame", VoidType.v())
                    .add(Hook.PUSH_INBOUND_MESSAGE_FRAME, runtime,
                            "pushInboundMessageFrame", VoidType.v())
                    .add(Hook.POP_INBOUND_MESSAGE_FRAME, runtime,
                            "popInboundMessageFrame", VoidType.v())
                    .add(Hook.PAUSE_OBSERVATION, runtime, "pauseObservation",
                            VoidType.v())
                    .add(Hook.RESUME_OBSERVATION, runtime, "resumeObservation",
                            VoidType.v())
                    .add(Hook.PAUSE_VM_PATH_CONDITION, system,
                            "pauseConcolicPathCondition", VoidType.v())
                    .add(Hook.RESUME_VM_PATH_CONDITION, system,
                            "resumeConcolicPathCondition", VoidType.v())
                    .add(Hook.PREPARE_BRANCH, runtime, "prepareBranch",
                            LongType.v(), string, IntType.v(), string)
                    .add(Hook.MARK_CONCOLIC_BRANCH, system,
                            "markConcolicBranch", LongType.v(), string,
                            IntType.v())
                    .add(Hook.RESOLVE_BRANCH, runtime, "resolveBranch",
                            VoidType.v(), LongType.v(), LongType.v(), string,
                            IntType.v(), string, BooleanType.v())
                    .add(Hook.RESOLVE_SWITCH_BRANCH, runtime,
                            "resolveSwitchBranch", VoidType.v(), LongType.v(),
                            LongType.v(), string, IntType.v(), string, string,
                            string, IntType.v())
                    .add(Hook.CHECK_LOOP_BACKEDGE, runtime,
                            "checkLoopBackedge", VoidType.v(), string,
                            IntType.v())
                    .add(Hook.CHECK_REPLAY_LOOP_BODY, runtime,
                            "checkReplayLoopBody", VoidType.v(), string,
                            IntType.v())
                    .add(Hook.EXIT_REGION_FRAME, runtime, "exitRegionFrame",
                            VoidType.v(), string, string)
                    .add(Hook.THROW_REGION_FRAME, runtime, "throwRegionFrame",
                            VoidType.v(), string, string,
                            RefType.v("java.lang.Throwable"));
        }
    }

    /**
     * The one primitive table: the wrapper a Jimple local round-trips through
     * and the {@code HandoffLeafCarrier} leaf it crosses a cut on.
     */
    private static final class PrimitiveWrapper {
        private final String className;
        private final String unboxMethod;
        private final String leafField;
        private final String descriptor;

        private PrimitiveWrapper(String className, String unboxMethod,
                                 String leafField, String descriptor) {
            this.className = className;
            this.unboxMethod = unboxMethod;
            this.leafField = leafField;
            this.descriptor = descriptor;
        }

        private static PrimitiveWrapper forType(Type type) {
            return type instanceof BooleanType
                    ? new PrimitiveWrapper("java.lang.Boolean",
                            "booleanValue", "z", "Z")
                    : type instanceof ByteType
                    ? new PrimitiveWrapper("java.lang.Byte",
                            "byteValue", "b", "B")
                    : type instanceof ShortType
                    ? new PrimitiveWrapper("java.lang.Short",
                            "shortValue", "s", "S")
                    : type instanceof CharType
                    ? new PrimitiveWrapper("java.lang.Character",
                            "charValue", "c", "C")
                    : type instanceof IntType
                    ? new PrimitiveWrapper("java.lang.Integer",
                            "intValue", "i", "I")
                    : type instanceof LongType
                    ? new PrimitiveWrapper("java.lang.Long",
                            "longValue", "j", "J")
                    : type instanceof FloatType
                    ? new PrimitiveWrapper("java.lang.Float",
                            "floatValue", "f", "F")
                    : type instanceof DoubleType
                    ? new PrimitiveWrapper("java.lang.Double",
                            "doubleValue", "d", "D")
                    : null;
        }
    }

    private static final class OriginalUnitIndexTag implements Tag {
        private static final String NAME = "CausynthOriginalUnitIndex";
        private final int index;

        private OriginalUnitIndexTag(int index) {
            this.index = index;
        }

        @Override
        public String getName() {
            return NAME;
        }

        @Override
        public byte[] getValue() {
            return new byte[]{
                    (byte) (index >>> 24),
                    (byte) (index >>> 16),
                    (byte) (index >>> 8),
                    (byte) index};
        }
    }

}
