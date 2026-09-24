package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ObservedWriteTarget;
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
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.option.GraphCheckerOptions;
import edu.uva.liftlab.graphchecker.runtime.RuntimeTraceMode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
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
import soot.SootField;
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


/** Annotation-directed static backward data-flow analysis. */
public final class CausynthPipeline {
    private static final Logger LOG = LoggerFactory.getLogger(CausynthPipeline.class);
    private static final String TRACE_RECORDER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder";
    private static final String CONCOLIC_REGION_RUNTIME_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime";
    /** Every local a weave adds is named for the weave that added it. */
    private static final String TRACE_LOCAL_PREFIX = "$causynth";
    /**
     * Soot's own body rules, run on every woven body by {@link
     * #validateWovenBodies}.  {@code CheckInitValidator} is the one that
     * answers the woven-trap rule of {@link #afterWovenPrologue}: it runs
     * Soot's {@code InitAnalysis} over an {@code ExceptionalUnitGraph} built
     * with the pedantic throw analysis, so every unit of a trap range has an
     * edge into the handler and a woven local the handler reads is reported
     * unless it is stored on every one of them -- which is the JVM's own
     * stackmap merge, one pass earlier and by name.  The other three are the
     * structural claims a weave can break: a local it used but did not
     * declare, a trap or a branch whose units it left out of the body.
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
            analyze();
            // Before Soot writes one class file: no woven body leaves this
            // JVM unless it satisfies the rules the JVM's verifier will
            // apply to it.
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
            LOG.info("REGION_STATE reused runtime-selected skeletons; "
                    + "static seed analysis was not rerun");
            return;
        }

        CausynthTargetContext target = CausynthTargetResolver.resolve();
        ExceptionTargetSite exceptionTarget =
                ExceptionTargetAnnotationScanner.select(
                        options.getInputList(), target.exceptionTargetId);
        target = target.withExceptionTarget(exceptionTarget);

        LOG.info("Seed backward analysis starts at annotated exception {}",
                exceptionTarget.stableIdentity());
        long seedAnalysisStart = System.nanoTime();
        StaticProgram result =
                new SeedBackwardStaticAnalyzer(target).analyze();
        long seedAnalysisMillis = elapsedMillis(seedAnalysisStart);
        long skeletonPlanningStart = System.nanoTime();
        // The graph is already resident here.
        SymbolicRegionPlanner.planSelectedSkeleton(result,
                result.traceMethods);
        // A shared helper may declare the same logical source fields for
        // several RPC handlers.
        StaticSymbolicSourceDiscovery.discover(result);
        long skeletonPlanningMillis = elapsedMillis(skeletonPlanningStart);
        // CLOSURE-V2 SS4, before ANY weaving: the sites of the static scope
        // map are named in original unit indices (the graph's own numbering),
        // and its guard sets are read off the same bodies the graph was built
        // from.  Computing them after instrumentRegionSkeletonTrace read the
        // guards off a body with hooks in it, which shifted every index past
        // the first hook -- 17960's target guard came out #u63 for a branch
        // INSTRUMENT wove as #u61 -- so no published guard id was a site any
        // replay could decide at.  SiteControlDependence also reads the
        // original-unit tags, so the two answers cannot drift apart again.
        List<StaticScopeMap.Site> scopeSites = StaticScopeMap.sites(
                result.edges, result.regions);
        List<JsonObject> scopeMap = StaticScopeMap.rows(scopeSites,
                SiteControlDependence.over(
                        StaticScopeMap.siteIds(scopeSites)));
        long instrumentationStart = System.nanoTime();
        instrumentRegionSkeletonTrace(result);
        long instrumentationMillis = elapsedMillis(instrumentationStart);
        long artifactWriteStart = System.nanoTime();
        CausynthArtifactWriter.writeDiscoveryArtifacts(
                target.outputDir, result, scopeMap);
        long artifactWriteMillis = elapsedMillis(artifactWriteStart);
        LOG.info("Discovery phase timing: seedAnalysis={} ms, "
                        + "skeletonPlanning={} ms, instrumentation={} ms, "
                        + "artifactWrite={} ms",
                seedAnalysisMillis, skeletonPlanningMillis,
                instrumentationMillis, artifactWriteMillis);
        LOG.info("Seed backward analysis wrote the frozen graph to {}; "
                + "symbolic regions will be finalized from the runtime trace",
                target.outputDir);
    }

    private static long elapsedMillis(long startNanos) {
        return (System.nanoTime() - startNanos) / 1_000_000L;
    }

    /**
     * The weave's own verifier gate: every body this run wove obeys Soot's
     * body rules, definite assignment included, or the run is refused by
     * name before a class file is written.
     *
     * <p>This is what makes {@link #afterWovenPrologue} a rule of the class
     * rather than a comment on one construct: a woven local read in a
     * handler or at a return that its store does not dominate is reported
     * here, whichever construct wove it.  The JVM used to report it
     * instead -- as a {@code VerifyError} inside a replay, hours into a
     * campaign, at a method the campaign never mentions.  Soot runs these
     * validators only under {@code -validate} or {@code -debug}, which is
     * why this states them itself.</p>
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
     * The one method walk every instrumentation mode takes: resolve, gate,
     * load the body, freeze its original unit indices, find the one entry a
     * rewrite may start at, and hand the emitter a frame it does not rebuild.
     * <p>A named refusal the emitter raises -- an {@link IllegalStateException}
     * whose message opens with an upper-case refusal code -- is the emitter
     * stating that a selected site cannot be rewritten, so it is rethrown.
     * Anything else a Soot rewrite throws leaves that one method alone.</p>
     * @param scopeFailure refusal prefix for a signature outside production
     *                     application scope; empty means skip it instead
     * @return the signatures the emitter rewrote, in walk order
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
                // A constructor may not be rewritten before its own
                // initialization, and one without a safe entry has no site
                // at all.
                if (method.isConstructor() && entry == null) continue;
                emitter.emit(body, method, originalUnits, entry,
                        method.isConstructor() ? entry : null,
                        receiverOrNull(body, method));
                rewritten.add(signature);
            } catch (RuntimeException exception) {
                if (namedRefusal(exception)) throw exception;
                // Not a named refusal: a Soot rewrite failed on this body.
                // Said at WARN with the exception, so a body the weave left
                // alone is visible in the stage's log rather than silent.
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

    /**
     * Index of the first original unit a rewrite may touch: the whole body
     * outside a constructor, everything at or after the initialization
     * boundary inside one, and {@code -1} when that boundary is not a unit of
     * this body, which is the body no site may be rewritten in.
     */
    private static int instrumentableFrom(List<Unit> originalUnits,
                                          Unit lowerBound) {
        if (lowerBound == null) return 0;
        for (int index = 0; index < originalUnits.size(); index++) {
            if (originalUnits.get(index) == lowerBound) return index;
        }
        return -1;
    }

    /** Second pass: rich evidence for only runtime-selected region methods. */
    private void instrumentRuntimeState(StaticProgram result) {
        HookCatalog refs = HookCatalog.trace();
        SootMethodRef recordFieldRef = refs.ref(Hook.RECORD_FIELD);
        // Which of the traced methods opens a region, read from the same
        // skeleton file the concolic pass reads its roots from: the
        // recording's execution index then has a frame exactly where the
        // replay's does (IDENTITY-IMPL B).
        Map<String, String> regionRoots =
                RegionSkeletonInstrumentationSelection
                        .regionRootsFromEnvironment();
        Set<String> rewritten = instrumentMethods(result.traceMethods,
                "REGION_STATE method is outside production application "
                        + "scope: ",
                (body, method, units, entry, lowerBound, receiver) -> {
                    instrumentRichMethod(body, method, units, entry,
                            lowerBound, receiver, refs,
                            regionRoots.getOrDefault(method.getSignature(),
                                    ""));
                    instrumentFieldTrace(body, method, recordFieldRef,
                            units, lowerBound);
                });
        // The same hooks, over the same scope, as the replay weaves: the
        // calling-context frame of every application method, the frame of
        // every work start and the claim of every work entry.  Last, so the
        // level of an activation is standing before anything woven inside
        // it reads an address, and one walk, so a scope one pass frames and
        // the other does not cannot exist.
        instrumentApplicationScope(refs);
        LOG.info("Instrumented {} of {} runtime-selected methods for "
                + "REGION_STATE trace; {} of them open a region",
                rewritten.size(), result.traceMethods.size(),
                regionRoots.size());
    }

    /** The methods the skeleton pass exists to watch. */
    static Set<String> skeletonCandidateMethods(StaticProgram result) {
        Set<String> candidates = new LinkedHashSet<>();
        for (Map<String, Object> region : result.regions) {
            Object methods = region.get("methods");
            if (!(methods instanceof Collection)) {
                continue;
            }
            for (Object method : (Collection<?>) methods) {
                candidates.add(String.valueOf(method));
            }
        }
        candidates.retainAll(new LinkedHashSet<>(result.traceMethods));
        Object target = result.targetResolved.get("method");
        if (target != null && !String.valueOf(target).trim().isEmpty()) {
            candidates.add(String.valueOf(target));
        }
        return candidates;
    }

    /**
     * Region discovery records only the balanced activation tree, plus the
     * annotated target method's exceptional exit.
     *
     * <p>An envelope is balanced by popping the thread-local activation, and
     * for every method but one that is all the skeleton pass needs: the
     * planner rebuilds nesting from {@code callId}/{@code parentCallId} on the
     * entry rows, so a silent pop costs it nothing. The annotated target is
     * the exception. Whether the run reached the target's throw is the one
     * question this pass exists to answer for the launcher, and a silent pop
     * cannot answer it - it leaves a run in which the exception escaped the
     * target twelve times indistinguishable from one in which the method
     * returned normally every time. So the target, and only the target, gets
     * the row-writing exceptional-exit hook.</p>
     *
     * <p>That difference is deliberate: the absence of a
     * {@code METHOD_EXIT_THROW} row for the target is an observation; the
     * absence of one for any other instrumented method is not, because none
     * is ever written.  Normal exits stay silent everywhere, the target
     * included, so the entry-row counts this pass has always produced do not
     * move.</p>
     */
    private void instrumentRegionSkeletonTrace(StaticProgram result) {
        Set<String> selectedMethods = skeletonCandidateMethods(result);
        if (selectedMethods.isEmpty()) {
            LOG.warn("No candidate region selected a method to instrument; "
                    + "the REGION_SKELETON pass will bind no activation");
        }
        HookCatalog refs = HookCatalog.trace();
        String annotatedTarget = annotatedTargetMethod(result);
        Set<String> rewritten = instrumentMethods(selectedMethods, "",
                (body, method, units, entry, lowerBound, receiver) ->
                        instrumentLiteMethod(body, method, units, entry,
                                lowerBound, receiver, refs,
                                !annotatedTarget.isEmpty()
                                        && annotatedTarget.equals(
                                                method.getSignature())));
        LOG.info("Instrumented {} of {} candidate methods for REGION_SKELETON "
                        + "trace out of a {}-method static slice "
                        + "and {} candidate regions",
                rewritten.size(), selectedMethods.size(),
                result.traceMethods.size(), result.regions.size());
        if (!annotatedTarget.isEmpty()
                && rewritten.contains(annotatedTarget)) {
            LOG.info("Exceptional exit is recorded for the annotated target "
                    + "{} only; every other instrumented method still pops "
                    + "its activation without a row", annotatedTarget);
        } else {
            LOG.warn("No exceptional-exit row will be written for the "
                    + "annotated target {}; a run in which the target throws "
                    + "will be indistinguishable from one in which it does "
                    + "not", annotatedTarget.isEmpty()
                    ? "<unresolved>" : annotatedTarget);
        }
    }

    /** The annotated target's Soot signature, or {@code ""} when absent. */
    private static String annotatedTargetMethod(StaticProgram result) {
        Object method = result.targetResolved.get("method");
        if (method == null || String.valueOf(method).trim().isEmpty()) {
            return "";
        }
        return String.valueOf(method);
    }

    /** The campaign's one deduplicated instrumentation envelope. */
    private final class CampaignEnvelope {
        private final List<InstrumentationPlan> campaign;
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<String> loopBoundMethods = new LinkedHashSet<>();
        private final Set<String> fixedCountLoopSites =
                new LinkedHashSet<>();
        /**
         * The closure a field write may be recorded in. It stays the union of
         * the tasks' own execution scopes rather than the whole envelope: a
         * write hook mints a writer, and a writer the relation did not ask
         * for is not a cheaper envelope, it is a different model.
         */
        /** Exact configured-source call sites, deduplicated across tasks. */
        private final Map<String, ConfiguredSourcePhaseContract.Occurrence>
                configuredSourcePhaseSites = new LinkedHashMap<>();
        private final ConcolicMaterializationSelection materializations =
                new ConcolicMaterializationSelection();
        // Keyed by the plan itself, not by its root method: a campaign may
        // hold several tasks rooted at one method - a path flip is exactly
        // that - and each keeps its own replay entry and engine arm.
        private final Map<InstrumentationPlan, SootMethod> replayEntries =
                new IdentityHashMap<>();
        /** Loop proofs frozen before any symbolic-region bridge is inserted. */
        private final Map<String, CfgLoopControl.NaturalLoop> rootLoops =
                new LinkedHashMap<>();
        private LoopBoundPolicy loopBound;

        private CampaignEnvelope(List<InstrumentationPlan> campaign) {
            this.campaign = campaign;
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
                            || prior.phase() != phase.phase()
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
                if (loopBound != null && !loopBound.identity()
                        .equals(plan.loopBound().identity())) {
                    // One union tree installs one policy on every shared
                    // method.
                    throw new IllegalStateException(
                            "CAMPAIGN_LOOP_BOUND_CONFLICT: "
                                    + loopBound.identity()
                                    + " and "
                                    + plan.loopBound().identity());
                }
                loopBound = plan.loopBound();
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
         * Freezes original unit indices for every body the campaign may
         * rewrite, before the first rewrite moves one.
         */
        /**
         * Numbers the original units of every body this campaign weaves.
         *
         * <p>The numbering IS the site vocabulary: `static_scope_map`'s
         * guard ids, the plan's `unitIndex` and the replay's decision sites
         * are all original-unit indices of these bodies, so a body whose
         * tagging fails is a body whose sites no replay can decide at --
         * the `#u63`/`#u61` defect class, where 17960's target guard was
         * published for one numbering and woven at another.  It used to be
         * swallowed with "unresolvable bodies are dropped by every later
         * pass too", which is true of a body with no active body and false
         * of one whose tagging threw: that one is still woven.</p>
         */
        private void tagSelectedBodies() {
            Set<String> tagged = new LinkedHashSet<>(methods);
            tagged.addAll(loopBoundMethods);
            for (String signature : tagged) {
                Body body;
                try {
                    body = CausynthStaticFacts.activeBody(
                            CausynthStaticFacts.method(signature));
                } catch (RuntimeException unresolvable) {
                    // No body to number: every later pass skips it too, and
                    // it is named rather than counted silently.
                    LOG.warn("ORIGINAL_UNIT_TAGGING_SKIPPED: {} has no "
                            + "active body to number", signature);
                    continue;
                }
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

        /** Bounds the campaign's loops once. */
        private void boundSelectedLoops() {
            if (loopBound == null) {
                return;
            }
            instrumentConcolicLoopBounds(loopBoundMethods, loopBound,
                    fixedCountLoopSites);
        }

        private SootMethod replayEntry(InstrumentationPlan plan) {
            return replayEntries.get(plan);
        }

        /**
         * Freezes each logical LOOP_BODY_ROOT once. Several path tasks may
         * instrument that same loop, and their synthetic traps and bridges
         * must not redefine the loop for the next task.
         */
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

    /**
     * Rewrites one campaign's one deduplicated instrumentation envelope.
     * README section 1: the envelope is the union of the per-task envelopes,
     * deduplicated, and each selected site is rewritten once.
     */
    void instrumentConcolicCampaign(List<InstrumentationPlan> campaign) {
        HookCatalog refs = HookCatalog.concolic();
        CampaignEnvelope envelope = new CampaignEnvelope(campaign);
        envelope.tagSelectedBodies();
        envelope.boundSelectedLoops();
        instrumentConcolicCommunicationHandoffs(campaign, refs);
        envelope.freezeRootLoops();
        for (InstrumentationPlan plan : campaign) {
            instrumentConcolicRegion(plan, refs, envelope);
        }
        // Every skeleton root, campaign roots included: ONE entry hook per
        // root method, which owns that activation's index frame and the
        // region it opens.  The plan rows' own hooks push nothing, so a
        // second row at one entry cannot add a frame and a recursive entry
        // cannot be mistaken for a second row.
        instrumentSkeletonRegions(refs);
        instrumentConcolicConfiguredSourceCallContexts(
                envelope.configuredSourcePhaseSites.values(), refs);
        instrumentConcolicAccessorCallContexts(envelope.materializations,
                refs);
        instrumentConcolicObservedWriteSites(envelope.materializations,
                refs);
        instrumentConcolicMethodArguments(envelope.materializations, refs);
        instrumentConcolicMaterializations(envelope, refs);
        instrumentConcolicBranches(envelope.methods, refs);
        // The same scope the recording weaves (instrumentRuntimeState), and
        // LAST: every application method's calling-context level, every
        // work start and every work entry claim, whatever this campaign
        // selected.  A level, a start frame or a claim one pass has and the
        // other does not names two different occurrences for one execution
        // point; woven last, the level opens ahead of every hook woven
        // inside it and closes after them.
        instrumentApplicationScope(refs);
    }

    /**
     * Opens the execution-index region of every skeleton root the campaign
     * did NOT select.
     *
     * <p>The recording opens one at every skeleton root, so a replay that
     * opened them only at its own task roots stood on a different frame
     * stack: {@code Identity.currentOccurrence} then named a different
     * occurrence for the same event, and every endpoint and every causal
     * anchor computed from it drifted.  Same file, same rule, same
     * one-region-per-activation: the campaign's own roots keep their rich
     * hooks and are excluded here, so a root that is both opens once.</p>
     */
    private void instrumentSkeletonRegions(HookCatalog refs) {
        Map<String, String> roots = RegionSkeletonInstrumentationSelection
                .regionRootsFromEnvironment();
        Set<SootMethod> entered = new LinkedHashSet<>();
        Set<String> rewritten = instrumentMethods(
                new ArrayList<>(roots.keySet()), "",
                (body, method, units, entry, lowerBound, receiver) -> {
                    // Fail closed: one entry hook per root method.  Two of
                    // them push two frames at one entry, and an index with
                    // a frame the recording does not have addresses a
                    // different occurrence -- silently, which is how 33 of
                    // 81 planned tasks came to be refused.
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
     * The index frame and the occurrence of ONE region activation, owned by
     * the token the workload frame holds.
     *
     * <p>The token is a local of this method, so every ENTRY has its own --
     * recursion included -- and the exit hooks close the entry that token
     * owns rather than whatever the runtime finds innermost.</p>
     */
    private void instrumentRegionEntry(Body body, SootMethod method,
                                       List<Unit> originalUnits,
                                       Unit insertionPoint, Unit lowerBound,
                                       Value receiver, HookCatalog refs,
                                       String regionId) {
        Local entryToken = newTraceLocal(body, LongType.v(),
                "$causynthRegionEntry");
        // The entry hook IS the token's store, and the trap opens after it,
        // so there is nothing for a `= 0L` ahead of it to make safe: it was
        // the false comfort that let the trap open at it.
        List<Unit> entry = new ArrayList<>();
        refs.bracket(entry, entryToken, Hook.ENTER_REGION_ENTRY,
                StringConstant.v(regionId),
                StringConstant.v(method.getSignature()), receiver);
        insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);
        for (int index = instrumentableFrom(originalUnits, lowerBound);
                index >= 0 && index < originalUnits.size(); index++) {
            Unit unit = originalUnits.get(index);
            if (!(unit instanceof ReturnStmt)
                    && !(unit instanceof ReturnVoidStmt)) {
                continue;
            }
            List<Unit> exit = new ArrayList<>();
            refs.bracket(exit, Hook.EXIT_REGION_ENTRY, entryToken);
            insertBeforeSequence(body, unit, exit);
        }
        // The handler reads the token, so the trap opens after the store:
        // afterWovenPrologue, not the prologue's own first unit.
        addThrowHandler(body, afterWovenPrologue(body, entry), refs,
                Hook.THROW_REGION_ENTRY, "$causynthRegionEntryThrown",
                entryToken);
    }

    /**
     * Inserts region hooks at the roots selected by one campaign task's
     * runtime activation plan.
     */
    private void instrumentConcolicRegion(InstrumentationPlan plan,
                                          HookCatalog refs,
                                          CampaignEnvelope envelope) {
        String signature = plan.rootMethod();
        SootMethod replayEntry = envelope.replayEntry(plan);
        String replayEntrySignature = replayEntry.getSignature();
        try {
            // The once-only-root rule: a region rooted on a service loop is
            // entered once per iteration, so its frame is the loop body of
            // the loop's own method, not the entry above it.
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
            CfgLoopControl.Edge loopBodyEntryEdge = rootLoop == null
                    ? null : loopBodyEntry(body, rootLoop,
                    plan.rootLoopControlSites(),
                    plan.rootLoopDemandedUnitIndex());
            Unit insertionPoint = rootLoop == null
                    ? safeInstrumentationEntry(body, method)
                    : loopBodyEntryEdge.target;
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
            Unit tokenInitialization = Jimple.v().newAssignStmt(token,
                    LongConstant.v(0L));
            entry.add(tokenInitialization);
            List<Unit> activation = entry;
            ArrayType objectArrayType = ArrayType.v(
                    RefType.v("java.lang.Object"), 1);
            Local rootArguments = newTraceLocal(body, objectArrayType,
                    "$causynthRootArguments");
            // A loop body binds no parameters: they were bound once at the
            // method entry above it, so the per-iteration activation carries
            // an empty argument array rather than a stale one.
            int rootArgumentCount = rootLoop == null
                    ? method.getParameterCount() : 0;
            activation.add(Jimple.v().newAssignStmt(rootArguments,
                    Jimple.v().newNewArrayExpr(
                            RefType.v("java.lang.Object"),
                            IntConstant.v(rootArgumentCount))));
            for (int index = 0; index < rootArgumentCount; index++) {
                Type parameterType = method.getParameterType(index);
                if (!(parameterType instanceof RefType)
                        && !(parameterType instanceof ArrayType)) {
                    continue;
                }
                Value parameter = parameterLocal(body, index);
                if (parameter == null) continue;
                activation.add(Jimple.v().newAssignStmt(
                        Jimple.v().newArrayRef(rootArguments,
                                IntConstant.v(index)),
                        objectArg(body, parameter, activation)));
            }
            // The entry hook decides admission, and that decision is this
            // bridge's own control flow over the workload's own objects: it
            // compares the root receiver against null and against a declared
            // class.
            emit(activation, refs.ref(Hook.PAUSE_OBSERVATION));
            Unit enterRegion = invokeTo(token,
                    refs.ref(Hook.ENTER_REGION_FRAME),
                    StringConstant.v(plan.instrumentationSelector()),
                    StringConstant.v(signature), receiver, rootArguments);
            activation.add(enterRegion);
            emit(activation, refs.ref(Hook.RESUME_OBSERVATION));
            Unit regionStart = enterRegion;
            for (int index = 0; index < rootArgumentCount; index++) {
                Value parameter = parameterLocal(body, index);
                if (parameter == null) continue;
                materializeParameter(body, parameter, index, activation,
                        token, "$causynthArgument",
                        Hook.MATERIALIZE_ARGUMENT, Hook.SYMBOLIZE_ARGUMENT,
                        refs);
            }
            if (rootLoop == null) {
                insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);
            } else {
                insertLoopBodyEntry(body, method,
                        rootLoop, loopBodyEntryEdge, entry,
                        rootLoop.identity(method));
            }

            if (rootLoop != null) {
                // One iteration is one activation: the frame closes on every
                // edge that leaves the body, the backedge into the next
                // iteration included.
                insertLoopBodyRegionExits(body, method, rootLoop, plan,
                        signature, refs);
            } else {
                for (Unit unit : originalUnits) {
                    if (!(unit instanceof Stmt)) {
                        continue;
                    }
                    Stmt stmt = (Stmt) unit;
                    if (stmt instanceof ReturnStmt
                            || stmt instanceof ReturnVoidStmt) {
                        insertRegionExit(body, stmt,
                                plan.instrumentationSelector(), signature,
                                refs);
                    }
                }
            }
            addThrowHandler(body, regionStart, refs,
                    Hook.THROW_REGION_FRAME, "$causynthRegionThrown",
                    StringConstant.v(plan.instrumentationSelector()),
                    StringConstant.v(signature));
            if (rootLoop != null) {
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
     * Instruments the real enclosing method invocation of a LOOP_BODY_ROOT.
     * Its request-local ordinal is stable when replay changes the number of
     * loop iterations; the body hook later opens one symbolic activation per
     * iteration only while this exact outer call is current.
     */
    private void instrumentLoopRootInvocationContext(
            InstrumentationPlan plan, SootMethod method, HookCatalog refs) {
        if (method == null || !method.isConcrete()) {
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
        ArrayType objectArrayType = ArrayType.v(
                RefType.v("java.lang.Object"), 1);
        Local rootArguments = newTraceLocal(body, objectArrayType,
                "$causynthLoopRootArguments");
        List<Unit> entry = new ArrayList<>();
        entry.add(Jimple.v().newAssignStmt(contextToken,
                LongConstant.v(0L)));
        entry.add(Jimple.v().newAssignStmt(rootArguments,
                Jimple.v().newNewArrayExpr(RefType.v("java.lang.Object"),
                        IntConstant.v(method.getParameterCount()))));
        for (int index = 0; index < method.getParameterCount(); index++) {
            Type parameterType = method.getParameterType(index);
            if (!(parameterType instanceof RefType)
                    && !(parameterType instanceof ArrayType)) {
                continue;
            }
            Value parameter = parameterLocal(body, index);
            if (parameter == null) continue;
            entry.add(Jimple.v().newAssignStmt(
                    Jimple.v().newArrayRef(rootArguments,
                            IntConstant.v(index)),
                    objectArg(body, parameter, entry)));
        }
        Value receiver = receiverOrNull(body, method);
        emit(entry, refs.ref(Hook.PAUSE_OBSERVATION));
        Unit enter = invokeTo(contextToken,
                refs.ref(Hook.ENTER_LOOP_ROOT_INVOCATION_FRAME),
                StringConstant.v(plan.instrumentationSelector()),
                StringConstant.v(plan.rootMethod()), receiver, rootArguments);
        entry.add(enter);
        emit(entry, refs.ref(Hook.RESUME_OBSERVATION));
        insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);

        for (Unit unit : originalUnits) {
            if (!(unit instanceof ReturnStmt)
                    && !(unit instanceof ReturnVoidStmt)) {
                continue;
            }
            List<Unit> exit = new ArrayList<>();
            refs.bracket(exit, Hook.EXIT_LOOP_ROOT_INVOCATION_FRAME,
                    contextToken);
            insertBeforeSequence(body, unit, exit);
        }
        addThrowHandler(body, enter, refs,
                Hook.THROW_LOOP_ROOT_INVOCATION_FRAME,
                "$causynthLoopRootThrown", contextToken);
    }

    /**
     * The natural loop this region is rooted at: the one whose dominance-proved
     * header is the plan's {@code headerUnitIndex}. A plan that names a header
     * this body no longer has is a refusal, not a silent fall back to the
     * method entry -- rooting the region one frame too high is exactly the
     * once-only-root bug the rule exists to fix.
     */
    private static CfgLoopControl.NaturalLoop rootedLoop(
            Body body, SootMethod method, InstrumentationPlan plan) {
        int headerIndex = plan.rootLoopHeaderUnitIndex();
        // An earlier pass may have inserted a unit before the header (a loop
        // counter), and PatchingChain re-targets the backedges to it: the
        // dominance-proved header is then that inserted unit, which carries
        // no original index.  The loop is therefore found as the innermost
        // natural loop whose members hold the original header unit.
        Unit original = originalUnit(body, headerIndex);
        CfgLoopControl.NaturalLoop found = null;
        int foundPosition = -1;
        if (original != null) {
            List<Unit> order = snapshotUnits(body);
            // Loops are proved on the CURRENT body: a backedge the bound pass
            // routed through an inserted bridge has no original index, and
            // dropping it would dissolve the loop.  Position order is enough
            // for the proof; identities are matched on units, not indices.
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
                int position = order.indexOf(loop.header);
                if (position <= order.indexOf(original)
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
     * Where a loop-body region's frame opens: the outermost declared
     * iteration-control edge whose body successor dominates the unit the
     * region needs.
     *
     * <p>An enhanced-for loop commonly has a dominance header that computes
     * {@code Iterator.hasNext()}, followed by the {@link IfStmt} that chooses
     * between its body and exit.  The header's lexical successor is therefore
     * the guard itself, not the body.  Treating that successor as the entry
     * opens an activation even for the terminal false check.  Resolve the
     * declared control sites instead. A natural loop may have several exits;
     * only the body edge on every path to the demanded unit can open its
     * activation. Nested guards can also dominate that unit, so the earliest
     * such edge is the unique candidate not dominated by another candidate.
     * Refuse a shape for which the CFG cannot prove that edge.</p>
     */
    static CfgLoopControl.Edge loopBodyEntry(
            Body body, CfgLoopControl.NaturalLoop loop,
            Set<String> controlSites, int demandedUnitIndex) {
        String loopId = loop == null || body == null
                ? "<unknown-loop>" : loop.identity(body.getMethod());
        if (body == null || loop == null || controlSites == null
                || controlSites.isEmpty() || demandedUnitIndex < 0) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: " + loopId
                            + " has no declared control sites and demanded "
                            + "unit");
        }

        Set<Unit> members = loop.members();
        ResolvedLoopControls controls = resolveLoopControls(body, loop,
                controlSites, "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: ");

        Unit demanded = stableLoopUnit(body, demandedUnitIndex,
                controls.plannedIndices, controls.units);
        if (demanded == null || !members.contains(demanded)
                || !loop.isDominatedBy(demanded, loop.header)) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: " + loopId
                            + " does not contain a header-dominated demanded "
                            + "unit u" + demandedUnitIndex);
        }
        List<CfgLoopControl.Edge> demandedEntries = new ArrayList<>();
        for (Unit unit : controls.units) {
            List<CfgLoopControl.Edge> continuations = new ArrayList<>();
            for (Unit successor : loop.stableSuccessors(unit)) {
                if (!members.contains(successor)) continue;
                continuations.add(currentLoopBoundaryEdge(body,
                        new CfgLoopControl.Edge(unit, successor), loopId,
                        false));
            }
            continuations = deduplicateEdges(continuations);
            if (continuations.size() != 1) {
                throw new IllegalStateException(
                        "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: " + loopId
                                + " control site u"
                                + originalUnitIndex(unit)
                                + " does not resolve through synthetic gates "
                                + "to exactly one original in-loop body "
                                + "successor");
            }
            CfgLoopControl.Edge entry = continuations.get(0);
            if (loop.isDominatedBy(demanded, entry.target)) {
                demandedEntries.add(entry);
            }
        }

        List<CfgLoopControl.Edge> outermost = new ArrayList<>();
        for (CfgLoopControl.Edge candidate : demandedEntries) {
            boolean nested = false;
            for (CfgLoopControl.Edge other : demandedEntries) {
                if (candidate == other || candidate.target == other.target) {
                    continue;
                }
                if (loop.isDominatedBy(candidate.target, other.target)) {
                    nested = true;
                    break;
                }
            }
            if (!nested) outermost.add(candidate);
        }
        if (outermost.size() != 1) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: " + loopId
                            + " cannot prove one outermost declared body "
                            + "edge reaching demanded unit u"
                            + demandedUnitIndex + "; candidates="
                            + demandedEntries.size() + ", outermost="
                            + outermost.size());
        }
        return outermost.get(0);
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

        // Unit indices describe one lowering of the bytecode. Soot can split
        // an expression into an extra Jimple assignment when the same frozen
        // class is loaded under a different application-class union. Branch
        // order and CFG role remain stable, so they are the durable anchors.
        Set<Unit> exits = Collections.newSetFromMap(
                new IdentityHashMap<Unit, Boolean>());
        for (CfgLoopControl.Edge edge : loop.exitEdges()) {
            if (edge.source instanceof IfStmt
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
        if (body == null || edge == null || edge.source == null
                || edge.target == null) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_EDGE_UNAVAILABLE: " + loopId
                            + " has no exact control edge");
        }
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
     * Inserts a straight-line bridge on the selected body edge; a
     * latch-controlled header also admits its proved initial-entry paths.
     */
    static Unit insertLoopBodyEntry(
            Body body, SootMethod method, CfgLoopControl.NaturalLoop loop,
            CfgLoopControl.Edge edge, List<Unit> entry, String loopId) {
        if (body == null || method == null || loop == null || edge == null
                || edge.source == null || edge.target == null
                || entry == null || entry.isEmpty()) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: " + loopId);
        }
        List<UnitBox> matchingTargets = new ArrayList<>();
        for (UnitBox targetBox : edge.source.getUnitBoxes()) {
            if (targetBox.getUnit() == edge.target) {
                matchingTargets.add(targetBox);
            }
        }
        boolean fallThrough = edge.source.fallsThrough()
                && body.getUnits().getSuccOf(edge.source) == edge.target;
        if (matchingTargets.isEmpty() && !fallThrough) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: " + loopId
                            + " no longer has its selected body edge in "
                            + method.getSignature());
        }

        Unit first = entry.get(0);
        boolean headerEntry = edge.target == loop.header;
        if (headerEntry) {
            // A latch-controlled loop reaches the same header from its method
            // preheader on the first iteration and from one or more latches on
            // later iterations. All normal header entries open an activation;
            // UnitBoxes owned by traps are deliberately not rewritten.
            matchingTargets.clear();
            for (Unit source : body.getUnits()) {
                for (UnitBox targetBox : source.getUnitBoxes()) {
                    if (targetBox.getUnit() == edge.target) {
                        matchingTargets.add(targetBox);
                    }
                }
            }
        } else if (!fallThrough) {
            Unit lexicalPredecessor = body.getUnits().getPredOf(edge.target);
            if (lexicalPredecessor != null
                    && lexicalPredecessor.fallsThrough()
                    && body.getUnits().getSuccOf(lexicalPredecessor)
                    == edge.target) {
                // The selected edge is an explicit target. Keep an unrelated
                // lexical fallthrough into the same block on its old path;
                // only the selected UnitBox may enter this activation.
                body.getUnits().insertBeforeNoRedirect(
                        Jimple.v().newGotoStmt(edge.target), edge.target);
            }
        }
        insertBeforeOrAppendNoRedirect(body, edge.target, entry);
        for (UnitBox targetBox : matchingTargets) {
            targetBox.setUnit(first);
        }
        if (fallThrough
                && body.getUnits().getSuccOf(edge.source) != first) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: " + loopId
                            + " could not preserve its body fallthrough in "
                            + method.getSignature());
        }
        return first;
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
     * Every edge that ends one iteration of a loop-body root: the loop's
     * backedges and its normal exits.
     *
     * <p>A backedge is the iteration boundary itself, so it always closes the
     * frame. The plan's iteration control sites select among the loop's normal
     * exits only, so the frame closes exactly where the loop's own guard
     * decided it: the bound pass has already routed each backedge through an
     * inserted bridge, so its source carries no original unit index and no
     * control site can name it. Filtering a backedge out would leave the frame
     * open for the whole loop, and {@code enterRegionFrame} would then answer
     * every later iteration from the frame the first one pushed - one
     * activation per thread instead of README {@code OCC-1}'s one activation
     * per iteration.</p>
     */
    static List<CfgLoopControl.Edge> loopBodyClosingEdges(
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

        ResolvedLoopControls controls = resolveLoopControls(body, loop,
                controlSites, "LOOP_BODY_ROOT_EXIT_UNAVAILABLE: ");
        for (Unit unit : controls.units) {
            List<CfgLoopControl.Edge> exits = new ArrayList<>();
            for (CfgLoopControl.Edge exit : loop.exitEdges()) {
                if (exit.source != unit) continue;
                exits.add(currentLoopBoundaryEdge(body, exit,
                        loop.identity(method), true));
            }
            exits = deduplicateEdges(exits);
            if (exits.size() != 1) {
                throw new IllegalStateException(
                        "LOOP_BODY_ROOT_EXIT_UNAVAILABLE: "
                                + loop.identity(method) + " control site "
                                + "u" + originalUnitIndex(unit)
                                + " does not resolve through "
                                + "synthetic gates to exactly one original "
                                + "loop exit");
            }
            closing.add(exits.get(0));
        }
        return deduplicateEdges(closing);
    }

    /**
     * Closes a loop-body region on every edge that ends one iteration.
     */
    private void insertLoopBodyRegionExits(
            Body body, SootMethod method, CfgLoopControl.NaturalLoop loop,
            InstrumentationPlan plan, String rootMethod, HookCatalog refs) {
        String loopId = loop.identity(method);
        int installed = 0;
        for (CfgLoopControl.Edge edge : loopBodyClosingEdges(method, loop,
                plan.rootLoopControlSites())) {
            List<Unit> bridge = new ArrayList<>();
            refs.bracket(bridge, Hook.EXIT_REGION_FRAME,
                    StringConstant.v(plan.instrumentationSelector()),
                    StringConstant.v(rootMethod));
            insertLoopBodyExit(body, method, edge, bridge, loopId);
            installed++;
        }
        if (installed == 0) {
            throw new IllegalStateException("LOOP_BODY_ROOT_EXIT_UNAVAILABLE: "
                    + loopId);
        }
    }

    /**
     * Inserts a close on the current first edge of one frozen boundary.
     * Resolving that first edge for every task prepends later closes and keeps
     * the activation stack in strict LIFO order.
     */
    static void insertLoopBodyExit(
            Body body, SootMethod method, CfgLoopControl.Edge edge,
            List<Unit> bridge, String loopId) {
        if (body == null || method == null || edge == null
                || edge.source == null || edge.target == null
                || bridge == null || bridge.isEmpty()) {
            throw new IllegalStateException(
                    "LOOP_BODY_ROOT_EXIT_UNAVAILABLE: " + loopId);
        }
        redirectEdge(body, method, edge.source, edge.target,
                bridge, "Could not close loop-body region on ", loopId);
    }

    /** Materializes and symbolizes one parameter local where it is bound. */
    private static void materializeParameter(
            Body body, Value parameter, int index, List<Unit> units,
            Value owner, String localPrefix, Hook materialize, Hook symbolize,
            HookCatalog refs) {
        Value primitiveValue = primitiveValueString(body, parameter, units);
        if (PrimitiveWrapper.forType(parameter.getType()) != null) {
            addPrimitiveRoundTrip(body, parameter, units, localPrefix,
                    refs.ref(Hook.PAUSE_OBSERVATION),
                    refs.ref(Hook.RESUME_OBSERVATION),
                    boxed -> Jimple.v().newStaticInvokeExpr(
                            refs.ref(materialize), owner,
                            IntConstant.v(index), boxed, primitiveValue));
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

    private void instrumentConcolicCommunicationHandoffs(
            List<InstrumentationPlan> campaign, HookCatalog refs) {
        Map<String, CommunicationHandoffSpec> sites = new LinkedHashMap<>();
        for (InstrumentationPlan plan : campaign) {
            for (CommunicationHandoffSpec site
                    : plan.communicationHandoffs()) {
                sites.putIfAbsent(site.side() + "\n" + site.portId()
                        + "\n" + site.siteId() + "\n"
                        + site.captureKind() + "\n" + site.argumentIndex(),
                        site);
            }
        }
        for (CommunicationHandoffSpec site : sites.values()) {
            instrumentCommunicationHandoff(site, refs);
        }
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
     * Brackets the one call that builds one message instance.
     *
     * <p>A declared port is one pair of bytecode sites, and a protocol sends
     * many unrelated values of that shape through it: without a frame the
     * receiver can only address a leaf by its position in the whole message,
     * and two groups of the same shape run together.  The frame method is the
     * one whose single call builds one instance of the value the port belongs
     * to, and its mirror on the other side decodes that same instance, so the
     * k-th frame means the same thing on both sides.  A port that declares no
     * frame keeps being addressed within its RPC message.</p>
     */
    private void instrumentCommunicationFrame(String frameMethod,
                                              boolean outgoing,
                                              HookCatalog refs) {
        SootMethod method = concreteSelected(frameMethod,
                "COMMUNICATION_FRAME_METHOD_UNAVAILABLE: " + frameMethod,
                "COMMUNICATION_FRAME_METHOD_NOT_CONCRETE: " + frameMethod);
        Body body = method.retrieveActiveBody();
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
        List<Unit> entry = new ArrayList<>();
        emit(entry, refs.ref(open));
        Unit opened = entry.get(entry.size() - 1);
        insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);
        for (Unit unit : originalUnits) {
            if (!(unit instanceof ReturnStmt)
                    && !(unit instanceof ReturnVoidStmt)) {
                continue;
            }
            List<Unit> exit = new ArrayList<>();
            emit(exit, refs.ref(close));
            insertBeforeSequence(body, unit, exit);
        }
        // A frame left open by a throw would swallow every later message of
        // this thread into it, so the close is on both ways out.  The close
        // hook takes no argument, so the trap is written here rather than
        // through addThrowHandler, which hands the caught throwable on.
        Local caught = newTraceLocal(body, RefType.v("java.lang.Throwable"),
                "$causynthMessageFrameThrown");
        List<Unit> trap = new ArrayList<>();
        trap.add(Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef()));
        emit(trap, refs.ref(close));
        trap.add(Jimple.v().newThrowStmt(caught));
        Unit handler = trap.get(0);
        for (Unit unit : trap) body.getUnits().add(unit);
        body.getTraps().add(Jimple.v().newTrap(
                Scene.v().getSootClass("java.lang.Throwable"), opened,
                handler, handler));
    }

    private void instrumentCommunicationHandoff(
            CommunicationHandoffSpec site, HookCatalog refs) {
        SootMethod method = concreteSelected(site.method(),
                "COMMUNICATION_HANDOFF_METHOD_UNAVAILABLE: " + site.portId(),
                "COMMUNICATION_HANDOFF_METHOD_NOT_CONCRETE: " + site.portId());
        Body body = method.retrieveActiveBody();
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
     * Restores the rich trace's exact call-site identity around manual source
     * hooks that execute during concolic replay.
     */
    private void instrumentConcolicConfiguredSourceCallContexts(
            Collection<ConfiguredSourcePhaseContract.Occurrence> phases,
            HookCatalog refs) {
        for (ConfiguredSourcePhaseContract.Occurrence phase : phases) {
            SootMethod method = concreteSelected(phase.declarationMethod(),
                    "CONFIGURED_SOURCE_PHASE_METHOD_UNAVAILABLE: "
                            + phase.siteId(),
                    "CONFIGURED_SOURCE_PHASE_METHOD_NOT_CONCRETE: "
                            + phase.siteId());
            Body body = method.retrieveActiveBody();
            Stmt selected = uniqueOriginalStmt(body,
                    phase.declarationUnitIndex(),
                    "CONFIGURED_SOURCE_PHASE_SITE_NOT_UNIQUE: "
                            + phase.siteId());
            if (selected == null || !selected.containsInvokeExpr()) {
                throw new IllegalStateException(
                        "CONFIGURED_SOURCE_PHASE_CALL_NOT_FOUND: "
                                + phase.siteId());
            }
            InvokeExpr invocation = selected.getInvokeExpr();
            if (!phase.runtimeDeclaredCallee().equals(
                    invocation.getMethodRef().getSignature())) {
                throw new IllegalStateException(
                        "CONFIGURED_SOURCE_PHASE_CALLEE_MISMATCH: "
                                + phase.siteId() + " expected "
                                + phase.runtimeDeclaredCallee() + " but found "
                                + invocation.getMethodRef().getSignature());
            }

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
                    selected, invocation);
            Value returnObject = objectArg(body, returnValue, after);
            Value primitiveReturn = primitiveValueString(
                    body, returnValue, after);
            Unit normalExit = invoke(refs.ref(Hook.EXIT_CONFIGURED_SOURCE_PHASE_SITE),
                    invocationId, returnObject, primitiveReturn);
            after.add(normalExit);
            Unit normalResume = invoke(refs.ref(Hook.RESUME_OBSERVATION));
            after.add(normalResume);
            Unit continuation = Jimple.v().newNopStmt();
            after.add(Jimple.v().newGotoStmt(continuation));
            Local caught = newTraceLocal(body,
                    RefType.v("java.lang.Throwable"),
                    "$causynthSourcePhaseThrown");
            Unit handler = Jimple.v().newIdentityStmt(caught,
                    Jimple.v().newCaughtExceptionRef());
            after.add(handler);
            emit(after, refs.ref(Hook.THROW_CONFIGURED_SOURCE_PHASE_SITE),
                    invocationId);
            emit(after, refs.ref(Hook.RESUME_OBSERVATION));
            after.add(Jimple.v().newThrowStmt(caught));
            after.add(continuation);
            insertAfterSequence(body, selected, after);
            // The source declaration itself is instrumentation bookkeeping:
            // its explicit native symbolize call must execute, but its Java
            // helper branches, maps and reflection must not enter the workload
            // path condition.
            SootClass throwable = Scene.v().getSootClass(
                    "java.lang.Throwable");
            body.getTraps().addFirst(Jimple.v().newTrap(throwable, selected,
                    normalExit, handler));
        }
    }

    /**
     * Files the start-site frame of every work start the analysis can see.
     *
     * <p>A thread inherits its creator's execution index when it is
     * CONSTRUCTED, which is before the start that made it run; and a pool
     * thread inherits it from whatever created the pool, which has nothing
     * to do with the work.  So the start itself is the frame: the site the
     * work was started at and the iteration of that start inside the
     * starter's activation, filed here for the work to take when it runs
     * (IDENTITY-V3 SS1 "scope transfer: Thread.start / executor ...").
     * Without it two siblings started from one site in one loop -- the two
     * {@code FSImageSaver} threads of hdfs-17960 -- stand on the same frames
     * and mint one address for two occurrences.</p>
     *
     * <p>One hook per started carrier, and no frame on the starter: a start
     * is an event of the starter, not a call it returns from.  Woven by BOTH
     * passes over the WHOLE application scope -- every class the analysis
     * loads, region selection included or not -- because an index computed
     * with the start frame on one side and without it on the other names two
     * different occurrences for one execution point, and a thread started
     * from a method no region selected is exactly the thread whose frames
     * begin nowhere (G9: hdfs-11741's two balancer pool threads, started by
     * {@code Dispatcher.dispatchBlockMoves}, shared one anchor).  The shapes
     * are {@link WorkStartSites}', which the recording's own call hooks read
     * too.</p>
     *
     * <p>And the other half of the same rule: the work CLAIMS that frame at
     * its own first instruction.  A start is filed under the object that
     * carries the work, and the thread that runs it never sees that object
     * through a hook of its own -- a pool worker is handed a task by {@code
     * ThreadPoolExecutor}, which is JDK code no weave touches -- so a claim
     * that waits for a region entry never happens at all on a pool thread
     * whose task enters no selected region.  On hdfs-11741 the two mover
     * threads {@code pool-57-thread-1/2} send the balancer's HDFS_SASL
     * request before any region entry: both stood on an empty index under
     * one degraded {@code ROLE.HDFS_SASL} occurrence, each counted its site
     * events from 0 in its own thread-local state, and the two messages
     * carried ONE producer endpoint id -- {@code Anchor:a496e8cab387ae3c},
     * which is the anchor dn1's {@code retrieveDataEncryptionKey} target
     * runs under.  Claimed at the entry of the functional method the start
     * named ({@link WorkStartSites#entersWork}), the frame is standing
     * before the first send, so two mover tasks are two occurrences with
     * their own counters and their own k (G8: the k of an occurrence's own
     * events, never a cross-thread counter).</p>
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
            // A class the lineage scope alone brought in carries its work
            // starts, claims and timed waits and nothing else (LineageScope).
            boolean lineageOnly = LineageScope.lineageOnly(type.getName());
            if (lineageOnly) lineage++;
            for (SootMethod method : new ArrayList<>(type.getMethods())) {
                Body body = CausynthStaticFacts.activeBody(method);
                if (body == null) continue;
                walked++;
                List<Unit> originalUnits = snapshotUnits(body);
                tagOriginalUnits(originalUnits);
                // A constructor may not be rewritten before its own
                // initialization, and one whose boundary this body does not
                // name has no site a weave may touch.
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
                    // The consumer half of a queue handoff: what the call
                    // returns is the work a producer put, and the consumer
                    // claims it where it takes it -- the element may be a
                    // lambda no weave reaches, so its own entry cannot.
                    boolean claims = claimsFromQueue(stmt.getInvokeExpr());
                    Unit last = replaceTimedWait(body, stmt, site);
                    if (last != null) waited++;
                    else last = stmt;
                    if (claims && last instanceof AssignStmt
                            && ((AssignStmt) last).getLeftOp()
                                    instanceof Local
                            && ((AssignStmt) last).getLeftOp().getType()
                                    instanceof RefType) {
                        List<Unit> claim = new ArrayList<>();
                        refs.bracket(claim, Hook.CLAIM_START,
                                ((AssignStmt) last).getLeftOp());
                        insertAfterSequence(body, last, claim);
                        claimed++;
                    }
                }
                // The claim first and the level second, at one entry, in this
                // order: the claim inserts the start frame at the boundary
                // between the starter's levels and the work's own, so a
                // level of the work opened ahead of it would put the start
                // frame above what the work has already entered.
                Unit entry = safeInstrumentationEntry(body, method);
                if (claimWorkEntry(body, method, entry, refs)) claimed++;
                if (!lineageOnly && openMethodLevel(body, method,
                        originalUnits, entry, refs)) {
                    framed++;
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
     * Replaces one timed wait with its {@code TimedWaits} stand-in, in place.
     *
     * <p>Where a service loop's next turn begins ({@link
     * WorkStartSites.TimedWait}).  The statement keeps its identity -- the invoke expression is swapped inside
     * it -- so every branch and trap that names it still does.  The receiver,
     * when there is one, becomes the first argument and the call site the
     * last.  A stand-in that returns {@code Object} where the call returned a
     * narrower type is followed by the cast the call's own bridge made.</p>
     *
     * @return the unit the call's result is final after -- the statement, or
     *         the cast that follows it -- or null when this is no timed wait
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
     * <p>THE frame rule (G11, IDENTITY-V3 §1): a calling context is the
     * application methods an event is inside, so every method of the
     * application scope opens a level at its entry and closes it at every
     * exit -- the normal returns and the exceptional edge -- in BOTH passes
     * from this one walk.  The region roots additionally open their region
     * where they always did, on top of the level this opens; nothing else
     * pushes a frame any more.</p>
     *
     * <p>What this replaces: frames at region roots, work starts and loop
     * roots only.  A thread outside every region then had an EMPTY calling
     * context -- hdfs-11741's balancer {@code main} addressed its whole
     * process as one degraded occurrence -- so the k of an event at a site
     * was a run-length ordinal over the process, which IDENTITY-V3 §1
     * forbids: the recording's declared {@code balance-block} request sent
     * at {@code HADOOP_IPC#REQUEST@18} and the replay's at {@code @22},
     * four polling requests later, and dn1's target was refused on the
     * causal anchor alone.</p>
     *
     * <p>Woven LAST, which is what puts the level's entry at the HEAD of a
     * method's woven prologue and its exits at the TAIL of every woven
     * epilogue: {@code safeInstrumentationEntry} answers the first
     * non-identity unit of the body as it now stands, so units another
     * weave already put at this entry come after this one, and the level is
     * standing before any region entry or materialization reads an address.
     * Its trap is registered last for the same reason and in the opposite
     * direction -- the exception table is searched in registration order,
     * so the level's handler runs after the handlers of everything woven
     * inside it, and the region closes before the frame it stood on
     * goes.</p>
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
        // The entry hook IS the token's store and the trap opens after it,
        // so there is nothing for a `= 0L` ahead of it to make safe: it was
        // the false comfort that let the trap open at it
        // (#instrumentRegionEntry, the woven-trap rule).
        // The receiver rides on the level: the attribution rule asks whether
        // the innermost frame's receiver is registered (runtime.Attribution,
        // rule 2).  None for a constructor -- an object being built is
        // nobody's registration yet.
        refs.bracket(opening, token, Hook.ENTER_METHOD_FRAME,
                StringConstant.v(method.getSignature()),
                method.isConstructor() ? NullConstant.v()
                        : receiverOrNull(body, method));
        insertBeforeOrAppendNoRedirect(body, entry, opening);
        for (int index = instrumentableFrom(originalUnits, null);
                index >= 0 && index < originalUnits.size(); index++) {
            Unit unit = originalUnits.get(index);
            if (!(unit instanceof ReturnStmt)
                    && !(unit instanceof ReturnVoidStmt)) {
                continue;
            }
            List<Unit> closing = new ArrayList<>();
            refs.bracket(closing, Hook.EXIT_METHOD_FRAME, token);
            insertBeforeSequence(body, unit, closing);
        }
        // The handler reads the token, so the trap opens after the store:
        // afterWovenPrologue, not the prologue's own first unit.
        addThrowHandler(body, afterWovenPrologue(body, opening), refs,
                Hook.THROW_METHOD_FRAME, "$causynthFrameThrown", token);
        return true;
    }

    /**
     * Claims the start frame of the work this method IS, at its entry.
     *
     * <p>The receiver is the carrier the start was filed under, so the
     * claim takes {@code this} and nothing else; a start nobody filed for
     * it is a no-op ({@code Identity.claimStart}).  At the entry, because
     * "the work's first identity event" is the rule and the entry precedes
     * every send, read, write and region entry the work makes.</p>
     *
     * @return whether this method received the claim
     */
    private boolean claimWorkEntry(Body body, SootMethod method, Unit entry,
                                   HookCatalog refs) {
        if (method.isStatic() || method.isConstructor()
                || !WorkStartSites.entersWork(method.getName(),
                        method.getParameterCount(),
                        hierarchyOf(method.getDeclaringClass()))) {
            return false;
        }
        Value receiver = receiverOrNull(body, method);
        if (receiver instanceof NullConstant) return false;
        if (entry == null) return false;
        List<Unit> claim = new ArrayList<>();
        refs.bracket(claim, Hook.CLAIM_START, receiver);
        insertBeforeOrAppendNoRedirect(body, entry, claim);
        return true;
    }

    /**
     * The objects that carry the work one invocation starts, in call order.
     *
     * <p>{@link WorkStartSites} owns which shapes those are; this is its
     * Soot projection: the declaring class answers the receiver's type and
     * the declared type of each argument answers whether it can be work.
     * One invocation can start several -- {@code invokeAll(t1, t2)} -- and
     * each start is its own event at this one site.</p>
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

    /**
     * Wraps only activation-selected accessor invocations with a tiny thread-
     * local runtime context.
     */
    private void instrumentConcolicAccessorCallContexts(
            ConcolicMaterializationSelection selection,
            HookCatalog refs) {
        for (AccessorCallTarget target : selection.accessorCalls()) {
            SootMethod method;
            Body body;
            try {
                method = Scene.v().getMethod(target.callerMethod);
                if (method == null || !method.isConcrete()) {
                    throw new IllegalStateException(
                            "ACCESSOR_CALLSITE_CALLER_NOT_CONCRETE: "
                                    + target.callSiteId);
                }
                body = method.retrieveActiveBody();
            } catch (RuntimeException failure) {
                throw new IllegalStateException(
                        "ACCESSOR_CALLSITE_CALLER_UNAVAILABLE: "
                                + target.callSiteId, failure);
            }
            tagOriginalUnits(snapshotUnits(body));
            Stmt selected = uniqueOriginalStmt(body, target.callUnitIndex,
                    "ACCESSOR_CALLSITE_NOT_UNIQUE: " + target.callSiteId);
            if (selected == null || !selected.containsInvokeExpr()) {
                throw new IllegalStateException(
                        "ACCESSOR_CALLSITE_INVOKE_NOT_FOUND: "
                                + target.callSiteId);
            }
            Unit safeEntry = safeInstrumentationEntry(body, method);
            if (method.isConstructor()
                    && (safeEntry == null
                    || !unitAtOrAfter(body, safeEntry, selected))) {
                throw new IllegalStateException(
                        "ACCESSOR_CALLSITE_BEFORE_CONSTRUCTOR_INITIALIZATION: "
                                + target.callSiteId);
            }
            InvokeExpr invocation = selected.getInvokeExpr();
            if (!target.declaredCallee.equals(
                    invocation.getMethodRef().getSignature())) {
                throw new IllegalStateException(
                        "ACCESSOR_CALLSITE_DECLARED_CALLEE_MISMATCH: "
                                + target.callSiteId + " expected "
                                + target.declaredCallee + " but found "
                                + invocation.getMethodRef().getSignature());
            }
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
            // One bracket over the whole context, not only over the
            // materialization inside it.
            emit(before, refs.ref(Hook.PAUSE_OBSERVATION));
            emit(before, contextToken,
                    refs.ref(Hook.ENTER_ACCESSOR_CALL_CONTEXT),
                    StringConstant.v(target.callerMethod),
                    IntConstant.v(target.callUnitIndex),
                    StringConstant.v(target.callSiteId),
                    StringConstant.v(target.declaredCallee), receiver);
            // The accessor implementation may live in a platform/JDK class
            // which is deliberately outside Soot's application-class set.
            // Materialize its exact backing field on the selected receiver
            // while the exact-call context is active, before the unmodified
            // getter consumes the field.
            emit(before, refs.ref(Hook.MATERIALIZE_FIELD),
                    StringConstant.v(target.implementationMethod),
                    IntConstant.v(-1), receiver,
                    StringConstant.v(target.fieldSignature),
                    StringConstant.v(target.fieldName));
            emit(before, refs.ref(Hook.RESUME_OBSERVATION));
            insertBeforeSequence(body, selected, before);

            // Closing the context is the same bookkeeping as opening it and
            // carries the same bracket on both edges.
            Unit normalPause = invoke(refs.ref(Hook.PAUSE_OBSERVATION));
            Unit normalExit = invoke(refs.ref(Hook.EXIT_ACCESSOR_CALL_CONTEXT),
                    contextToken);
            Unit normalResume = invoke(refs.ref(Hook.RESUME_OBSERVATION));
            Unit continuation = Jimple.v().newNopStmt();
            Unit skipHandler = Jimple.v().newGotoStmt(continuation);
            Local caught = newTraceLocal(body,
                    RefType.v("java.lang.Throwable"),
                    "$causynthAccessorThrown");
            Unit handler = Jimple.v().newIdentityStmt(caught,
                    Jimple.v().newCaughtExceptionRef());
            Unit exceptionalPause = invoke(refs.ref(Hook.PAUSE_OBSERVATION));
            Unit exceptionalExit = invoke(refs.ref(Hook.EXIT_ACCESSOR_CALL_CONTEXT),
                    contextToken);
            Unit exceptionalResume = invoke(refs.ref(Hook.RESUME_OBSERVATION));
            Unit rethrow = Jimple.v().newThrowStmt(caught);
            insertAfterSequence(body, selected, Arrays.asList(normalPause,
                    normalExit, normalResume, skipHandler, handler,
                    exceptionalPause, exceptionalExit, exceptionalResume,
                    rethrow, continuation));
            SootClass throwable = Scene.v().getSootClass(
                    "java.lang.Throwable");
            body.getTraps().addFirst(Jimple.v().newTrap(throwable, selected,
                    normalPause, handler));
        }
    }

    /**
     * Observes the stores of a declared input's cell that the plan selected.
     *
     * <p>Two hooks around one call: BEFORE it the cell is observed, which is
     * what starts the location's version log (the VM retains a location by
     * value, so an unobserved cell's stores publish nothing); AFTER a normal
     * return the version the store produced is asked for and stamped with
     * the execution index the store stood on -- the write log names the
     * location and the value, never the bytecode, and the row is published
     * when the activation ends, by which point those frames are gone.</p>
     *
     * <p>An atomic RMW runs inside the JDK and has no application
     * {@code putfield} for the ordinary carrier hook to stand at, which is
     * why the receiver has to be selected at the invocation.  An
     * exceptional return stamps nothing: a store that threw published no
     * version to name.</p>
     */
    private void instrumentConcolicObservedWriteSites(
            ConcolicMaterializationSelection selection, HookCatalog refs) {
        for (ObservedWriteTarget target : selection.observedWrites()) {
            SootMethod method;
            Body body;
            try {
                method = Scene.v().getMethod(target.method);
                if (method == null || !method.isConcrete()) {
                    throw new IllegalStateException(
                            "OBSERVED_WRITE_SITE_METHOD_NOT_CONCRETE: "
                                    + target.siteId);
                }
                body = method.retrieveActiveBody();
            } catch (RuntimeException failure) {
                throw new IllegalStateException(
                        "OBSERVED_WRITE_SITE_METHOD_UNAVAILABLE: "
                                + target.siteId, failure);
            }
            tagOriginalUnits(snapshotUnits(body));
            Stmt selected = uniqueOriginalStmt(body, target.unitIndex,
                    "OBSERVED_WRITE_SITE_NOT_UNIQUE: " + target.siteId);
            if (selected == null || !selected.containsInvokeExpr()) {
                throw new IllegalStateException(
                        "OBSERVED_WRITE_SITE_INVOKE_NOT_FOUND: "
                                + target.siteId);
            }
            InvokeExpr invocation = selected.getInvokeExpr();
            if (!target.declaredCallee.equals(
                    invocation.getMethodRef().getSignature())) {
                throw new IllegalStateException(
                        "OBSERVED_WRITE_SITE_DECLARED_CALLEE_MISMATCH: "
                                + target.siteId + " expected "
                                + target.declaredCallee + " but found "
                                + invocation.getMethodRef().getSignature());
            }
            if (!(invocation instanceof InstanceInvokeExpr)) {
                throw new IllegalStateException(
                        "OBSERVED_WRITE_SITE_REQUIRES_INSTANCE_RECEIVER: "
                                + target.siteId);
            }
            List<Unit> before = new ArrayList<>();
            Value receiver = objectArg(body,
                    ((InstanceInvokeExpr) invocation).getBase(), before);
            refs.bracket(before, Hook.OBSERVE_DECLARED_WRITE_SITE,
                    StringConstant.v(target.siteId),
                    StringConstant.v(target.cell), receiver);
            insertBeforeSequence(body, selected, before);
        }
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
            String signature = method.getSignature();
            for (int index = instrumentableFrom(originalUnits, lowerBound);
                    index >= 0 && index < originalUnits.size(); index++) {
                Unit unit = originalUnits.get(index);
                if (!(unit instanceof Stmt)) {
                    continue;
                }
                Stmt stmt = (Stmt) unit;
                int unitIndex = originalUnitIndex(unit);
                Set<FieldRef> fields = Collections.newSetFromMap(
                        new IdentityHashMap<FieldRef, Boolean>());
                if (stmt instanceof AssignStmt
                        && ((AssignStmt) stmt).getRightOp()
                        instanceof FieldRef) {
                    fields.add((FieldRef) ((AssignStmt) stmt)
                            .getRightOp());
                }
                for (ValueBox box : stmt.getUseBoxes()) {
                    if (box.getValue() instanceof FieldRef) {
                        fields.add((FieldRef) box.getValue());
                    }
                }
                for (FieldRef field : fields) {
                    SootFieldRef fieldRef = field.getFieldRef();
                    SootField declared =
                            CausynthStaticFacts.declaredField(fieldRef);
                    String declaredSignature =
                            CausynthStaticFacts.declaredFieldSignature(
                                    fieldRef);
                    String declaredName = declared == null
                            ? fieldRef.name() : declared.getName();
                    String staticRefusal =
                            selection.staticMaterializationRefusal(
                                    method.getSignature(), unitIndex,
                                    fieldRef);
                    // A shape the instrumenter has no hook for leaves the
                    // read concrete under its own named verdict
                    // (ConcolicMaterializationSelection): refusing is plan
                    // content, and throwing here killed a whole campaign
                    // over one static final byte[] constant.
                    if (!staticRefusal.isEmpty()) continue;
                    if (!selection.matches(method.getSignature(),
                            unitIndex, fieldRef)) {
                        continue;
                    }
                    if (field instanceof StaticFieldRef) {
                        instrumentConsumedStaticPrimitiveFieldRead(
                                body, method, stmt, unitIndex,
                                (StaticFieldRef) field, refs);
                        continue;
                    }
                    if (!(field instanceof InstanceFieldRef)) {
                        throw new IllegalStateException(
                                "UNKNOWN_FIELD_MATERIALIZATION_UNSUPPORTED: "
                                        + declaredSignature + " at "
                                        + SiteId.of(method.getSignature(),
                                        unitIndex));
                    }
                    InstanceFieldRef instanceField =
                            (InstanceFieldRef) field;
                    List<Unit> before = new ArrayList<>();
                    emit(before, refs.ref(Hook.PAUSE_OBSERVATION));
                    Value owner = objectArg(body, instanceField.getBase(),
                            before);
                    emit(before, refs.ref(Hook.MATERIALIZE_FIELD),
                            StringConstant.v(method.getSignature()),
                            IntConstant.v(unitIndex), owner,
                            StringConstant.v(declaredSignature),
                            StringConstant.v(declaredName));
                    emit(before, refs.ref(Hook.RESUME_OBSERVATION));
                    insertBeforeSequence(body, stmt, before);
                }

                if (!(stmt instanceof AssignStmt)) {
                    continue;
                }
                Value left = ((AssignStmt) stmt).getLeftOp();
                if (!(left instanceof Local)
                        || !selection.matches(method.getSignature(),
                        ((Local) left).getName(), unitIndex)) {
                    continue;
                }
                Local local = (Local) left;
                List<Unit> after = new ArrayList<>();
                if (local.getType() instanceof RefType
                        || local.getType() instanceof ArrayType) {
                    Local modeled = newTraceLocal(body,
                            RefType.v("java.lang.Object"),
                            "$causynthReferenceModel");
                    refs.bracket(after, modeled, Hook.MATERIALIZE_REFERENCE,
                            StringConstant.v(method.getSignature()),
                            IntConstant.v(unitIndex),
                            StringConstant.v(local.getName()), local);
                    after.add(Jimple.v().newAssignStmt(local,
                            Jimple.v().newCastExpr(modeled,
                                    local.getType())));
                } else {
                    addPrimitiveRoundTrip(body, local, after, "$causynth",
                            refs.ref(Hook.PAUSE_OBSERVATION),
                            refs.ref(Hook.RESUME_OBSERVATION),
                            boxed -> Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.MATERIALIZE_PRIMITIVE),
                                    StringConstant.v(method.getSignature()),
                                    IntConstant.v(unitIndex),
                                    StringConstant.v(local.getName()), boxed));
                }
                if (!after.isEmpty()) {
                    insertAfterSequence(body, stmt, after);
                }
            }
        });
    }

    private void instrumentConcolicMethodArguments(
            ConcolicMaterializationSelection selection,
            HookCatalog refs) {
        // Every selected owner must be rewritten: the walk skips what it
        // cannot rewrite, so anything it did not return is a refusal here.
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

    /**
     * Materializes a primitive {@code getstatic} on the exact local that
     * consumed it.
     */
    private static void instrumentConsumedStaticPrimitiveFieldRead(
            Body body, SootMethod method, Stmt stmt, int unitIndex,
            StaticFieldRef field, HookCatalog refs) {
        String declaredSignature =
                CausynthStaticFacts.declaredFieldSignature(
                        field.getFieldRef());
        SootField declared =
                CausynthStaticFacts.declaredField(field.getFieldRef());
        String declaredName = declared == null
                ? field.getFieldRef().name() : declared.getName();
        if (!(stmt instanceof AssignStmt)
                || ((AssignStmt) stmt).getRightOp() != field
                || !(((AssignStmt) stmt).getLeftOp() instanceof Local)) {
            return;
        }
        Local consumed = (Local) ((AssignStmt) stmt).getLeftOp();
        List<Unit> after = new ArrayList<>();
        boolean supported = addPrimitiveRoundTrip(body, consumed, after,
                "$causynthStaticField",
                refs.ref(Hook.PAUSE_OBSERVATION),
                refs.ref(Hook.RESUME_OBSERVATION),
                boxed -> Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.MATERIALIZE_STATIC_PRIMITIVE_FIELD),
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex),
                        StringConstant.v(declaredSignature),
                        StringConstant.v(declaredName), boxed));
        if (!supported) {
            return;
        }
        insertAfterSequence(body, stmt, after);
    }

    private static boolean addPrimitiveRoundTrip(
            Body body, Value primitive, List<Unit> units, String localPrefix,
            SootMethodRef pauseObservation, SootMethodRef resumeObservation,
            PrimitiveMaterializer materializer) {
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
        emit(units, pauseObservation);
        units.add(Jimple.v().newAssignStmt(materialized,
                materializer.invoke(boxed)));
        emit(units, resumeObservation);
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

    @FunctionalInterface
    private interface PrimitiveMaterializer {
        Value invoke(Local boxed);
    }

    /**
     * The index this unit had before any weaving, or -1 for a woven one.
     *
     * <p>Package-private because it is the ONE numbering every published
     * site id is in: {@link SiteControlDependence} names a guard by it for
     * the same reason {@link #instrumentConcolicBranches} finds a branch by
     * it.</p>
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
     * Bounds the loops of one selected method set.
     *
     * <p>Bounds natural-loop body entries rather than eagerly cutting at a
     * latch: a guarded loop may return to its header after body {@code K} and
     * is cut only if the header chooses the edge into body {@code K+1}, so a
     * concrete K-element iterator exhausted exactly at the bound still exits
     * normally.</p>
     *
     * <p>Every loop of a method comes from that method's one
     * {@link CfgLoopControl.LoopCfg}, which is also what the static analyzer
     * and the region planner prove iteration guards on.  Cycles a body has
     * only over trap edges are not loops of that model and carry no bound:
     * no bound can be installed on an abrupt transfer out of a protected
     * range.</p>
     */
    void instrumentConcolicLoopBounds(
            Set<String> methods, LoopBoundPolicy policy,
            Set<String> fixedCountLoopSites) {
        if (policy == null) {
            throw new IllegalArgumentException("loop bound policy is required");
        }
        HookCatalog hooks = HookCatalog.concolic();
        SootMethodRef replayBody = hooks.ref(Hook.CHECK_REPLAY_LOOP_BODY);
        SootMethodRef openInvocation = hooks.ref(Hook.OPEN_LOOP_INVOCATION);
        SootMethodRef closeInvocation = hooks.ref(Hook.CLOSE_LOOP_INVOCATION);
        SootMethodRef checkBackedge = hooks.ref(Hook.CHECK_LOOP_BACKEDGE);
        for (String methodSignature : methods) {
            SootMethod method = CausynthStaticFacts.method(methodSignature);
            if (method == null || !method.isConcrete()) {
                continue;
            }
            Body body = method.retrieveActiveBody();
            List<Unit> original = snapshotUnits(body);
            tagOriginalUnits(original);
            // One loop-CFG decision per body, shared with every other loop
            // consumer of this phase: backedge discovery, natural-loop
            // grouping, the continuation-guard search, and the loop-control
            // guards the static analyzer proves.
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
                List<CfgLoopControl.Edge> loopExits = fixedCount
                        ? deduplicateEdges(loop.exitEdges())
                        : Collections.<CfgLoopControl.Edge>emptyList();
                List<Unit> loopTerminals = fixedCount
                        ? loop.terminals()
                        : Collections.<Unit>emptyList();
                if (fixedCount) {
                    // One dynamic invocation of an indexed loop opens where
                    // its array length is computed, which is once per
                    // invocation and before the first body hook.  The length
                    // itself is no longer recorded: only the invocation the
                    // replay body budget is scoped to.
                    List<Unit> guards = new ArrayList<>();
                    for (CfgLoopControl.Edge edge : loopExits) {
                        guards.add(edge.source);
                    }
                    AssignStmt authority = CfgLoopControl
                            .arrayLengthAuthority(body, guards);
                    if (authority == null) {
                        throw new IllegalStateException(
                                "FIXED_COUNT_LOOP_INVOCATION_UNADDRESSABLE: "
                                        + loopId);
                    }
                    body.getUnits().insertAfter(invoke(openInvocation,
                            StringConstant.v(loopId)), authority);
                }
                boolean resourceLoop = fixedCount;
                int loopBodyBound = resourceLoop
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
                    if (resourceLoop && !entersBody) continue;
                    splitCfgEdge(body, method, backedge.source,
                            backedge.target, loopId, loopBodyBound,
                            resourceLoop ? replayBody : checkBackedge);
                }
                for (CfgLoopControl.Edge continuation : continuations) {
                    if (!resourceLoop) continue;
                    splitCfgEdge(body, method, continuation.source,
                            continuation.target, loopId, loopBodyBound,
                            replayBody);
                }
                if (fixedCount) {
                    for (CfgLoopControl.Edge exit : loopExits) {
                        splitStringHookEdge(body, method, exit.source,
                                exit.target, loopId, closeInvocation);
                    }
                    for (Unit terminal : loopTerminals) {
                        body.getUnits().insertBefore(invoke(closeInvocation,
                                StringConstant.v(loopId)), terminal);
                    }
                }
            }
        }
    }

    private static boolean naturalLoopHasSite(
            SootMethod method, CfgLoopControl.NaturalLoop loop,
            List<CfgLoopControl.Edge> continuations, Set<String> selectedSites) {
        if (selectedSites == null || selectedSites.isEmpty()) return false;
        Set<String> controlSites = naturalLoopControlSites(
                method, loop, continuations);
        for (String site : controlSites) {
            if (selectedSites.contains(site)) return true;
        }
        return false;
    }

    /** Resolves one natural loop's declared K_L from its actual CFG guards. */
    private static int naturalLoopBodyBound(
            SootMethod method, CfgLoopControl.NaturalLoop loop,
            List<CfgLoopControl.Edge> continuations, LoopBoundPolicy policy) {
        Set<String> controlSites = new LinkedHashSet<>();
        controlSites.addAll(naturalLoopControlSites(
                method, loop, continuations));
        Integer declared = null;
        String declaredSite = "";
        // The catalog and runtime plan name one multi-guard loop by the
        // composite loopSiteId built from its retained iteration guards.  The
        // policy therefore carries L(site+site+...), not one entry per member.
        // Resolve that canonical key before the edge-level fallback below;
        // otherwise a non-default declaration silently instruments at the
        // inherited bound even though every later stage reads the declared
        // K_L from the plan.
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
        if (method == null || natural == null || !method.isConcrete()) {
            return "";
        }
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
            // CfgLoopControl proves iteration guards per dominance-proved
            // latch. Keep the instrumentation on that exact same natural loop.
            Set<Unit> members = loop.members(backedge);
            List<CfgLoopControl.Edge> latchEdges = continuationEdgesFrom(
                    body, loop.header, members);
            if (latchEdges.isEmpty()) {
                // The dominance header is often the expression immediately
                // before the IfStmt.
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

    /** Splits one loop edge with the bounded-traversal hook it is charged on. */
    private static void splitCfgEdge(
            Body body, SootMethod method, Unit source, Unit target,
            String loopId, int maxTraversals, SootMethodRef hookRef) {
        redirectEdge(body, method, source, target,
                Collections.<Unit>singletonList(invoke(hookRef,
                        StringConstant.v(loopId),
                        IntConstant.v(maxTraversals))),
                "Could not split CFG loop edge ", loopId);
    }

    /** Splits one normal edge with a single-string, non-throwing hook. */
    private static void splitStringHookEdge(
            Body body, SootMethod method, Unit source, Unit target,
            String loopId, SootMethodRef hookRef) {
        redirectEdge(body, method, source, target,
                Collections.<Unit>singletonList(invoke(hookRef, StringConstant.v(loopId))),
                "Could not split CFG loop exit ", loopId);
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
        // Appending keeps the throwing hook outside every pre-existing
        // application trap.
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
     * Weaves the decision marker at EVERY conditional branch of every
     * instrumented method.
     *
     * <p>LEAN section 1: any decision whose term has a symbolic operand is
     * recorded, so there is nothing to select per branch and no plan member
     * to honour.  This used to weave only the sites the task's
     * {@code branches[]} array named, which made the recorded decision set a
     * function of an offline branch classification -- and a decision at a
     * site the plan had not named was dropped at the hook
     * ({@code ConcolicTaskPlan.declaresBranch}).  The plan still says which
     * METHODS are instrumented; which branches inside them exist is the
     * body's answer.</p>
     *
     * <p>A woven unit has no original index and is skipped: a hook's own
     * conditional is not a program decision, and no published site id could
     * name it.</p>
     *
     * @return the number of branch sites woven
     */
    private int instrumentConcolicBranches(
            Collection<String> methods, HookCatalog refs) {
        int[] woven = new int[1];
        instrumentMethods(methods, "",
                (body, method, units, entry, lowerBound, receiver) -> {
                    String signature = method.getSignature();
                    for (Unit unit : snapshotUnits(body)) {
                        boolean conditional = unit instanceof IfStmt
                                || unit instanceof SwitchStmt;
                        if (!conditional) continue;
                        int unitIndex = originalUnitIndex(unit);
                        if (unitIndex < 0) continue;
                        if (lowerBound != null
                                && !unitAtOrAfter(body, lowerBound, unit)) {
                            throw new IllegalStateException(
                                    "CONCOLIC_BRANCH_BEFORE_CONSTRUCTOR_"
                                            + "INITIALIZATION: "
                                            + SiteId.of(signature, unitIndex));
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
                + "across {} instrumented method(s)", woven[0],
                methods.size());
        return woven[0];
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

        Local decision = newTraceLocal(body, BooleanType.v(),
                "$causynthBranchDecision");
        Local prepared = newTraceLocal(body, LongType.v(),
                "$causynthPreparedBranch");
        Local vmEvent = newTraceLocal(body, LongType.v(),
                "$causynthVmBranchEvent");
        Local vmOccurrence = newTraceLocal(body, IntType.v(),
                "$causynthVmBranchOccurrence");

        insertExactBranchMarkerPrefix(body, method, branch, unitIndex,
                expression, prepared, vmEvent, vmOccurrence, refs);

        // Both arms resolve the same site; only the observed outcome and the
        // fallback transfer differ.
        List<Unit> falsePath = new ArrayList<>();
        refs.bracket(falsePath, decision, Hook.RESOLVE_BRANCH, prepared,
                vmEvent, StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex), StringConstant.v(expression),
                IntConstant.v(0));
        falsePath.add(Jimple.v().newIfStmt(
                Jimple.v().newNeExpr(decision, IntConstant.v(0)),
                previousTarget));
        insertAfterSequence(body, branch, falsePath);

        Unit trueEntry = Jimple.v().newNopStmt();
        List<Unit> truePath = new ArrayList<>();
        truePath.add(trueEntry);
        refs.bracket(truePath, decision, Hook.RESOLVE_BRANCH, prepared,
                vmEvent, StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex), StringConstant.v(expression),
                IntConstant.v(1));
        truePath.add(Jimple.v().newIfStmt(
                Jimple.v().newNeExpr(decision, IntConstant.v(0)),
                previousTarget));
        truePath.add(Jimple.v().newGotoStmt(falseSuccessor));
        for (Unit unit : truePath) {
            body.getUnits().add(unit);
        }
        branch.setTarget(trueEntry);
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
        Local effectiveSuccessor = newTraceLocal(body, IntType.v(),
                "$causynthSwitchSuccessor");

        insertExactBranchMarkerPrefix(body, method, branch, unitIndex,
                expression, prepared, vmEvent, vmOccurrence, refs);

        List<Unit> entries = new ArrayList<>();
        for (int observed = 0; observed < shape.successorCount(); observed++) {
            Unit entry = Jimple.v().newNopStmt();
            entries.add(entry);
            body.getUnits().add(entry);
            refs.bracket(body.getUnits(), effectiveSuccessor,
                    Hook.RESOLVE_SWITCH_BRANCH, prepared, vmEvent,
                    StringConstant.v(method.getSignature()),
                    IntConstant.v(unitIndex), StringConstant.v(expression),
                    StringConstant.v(shape.kind),
                    StringConstant.v(encodedKeys), IntConstant.v(observed));
            for (int targetIndex = 0;
                 targetIndex < shape.successorCount(); targetIndex++) {
                body.getUnits().add(Jimple.v().newIfStmt(
                        Jimple.v().newEqExpr(effectiveSuccessor,
                                IntConstant.v(targetIndex)),
                        shape.successors.get(targetIndex)));
            }
            // A malformed runtime result must retain the concrete Java
            // execution rather than jumping to an unrelated arm.
            body.getUnits().add(Jimple.v().newGotoStmt(
                    shape.successors.get(observed)));
        }
        for (int index = 0; index < shape.successorCount(); index++) {
            if (index == shape.defaultSuccessorIndex) {
                branch.setDefaultTarget(entries.get(index));
            } else {
                branch.setTarget(index, entries.get(index));
            }
        }
    }

    private void insertExactBranchMarkerPrefix(
            Body body, SootMethod method, Unit branch, int unitIndex,
            String expression, Local prepared, Local vmEvent,
            Local vmOccurrence, HookCatalog refs) {
        // Keep the native marker as the final invocation before the original
        // branch.
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
        boolean hasAuthoritativeOriginalTags = false;
        for (Unit unit : current) {
            for (Tag tag : unit.getTags()) {
                if (tag instanceof OriginalUnitIndexTag) {
                    hasAuthoritativeOriginalTags = true;
                    if (((OriginalUnitIndexTag) tag).index
                            == requestedIndex) {
                        return unit;
                    }
                }
            }
        }
        // Once any pass has established the original-index namespace, an
        // untagged unit belongs to instrumentation inserted by that or a later
        // pass.
        if (hasAuthoritativeOriginalTags) {
            return null;
        }
        return requestedIndex >= 0 && requestedIndex < current.size()
                ? current.get(requestedIndex) : null;
    }

    private void insertRegionExit(Body body, Stmt returnUnit,
                                  String taskId, String rootMethod,
                                  HookCatalog refs) {
        List<Unit> units = new ArrayList<>();
        emit(units, refs.ref(Hook.PAUSE_OBSERVATION));
        emit(units, refs.ref(Hook.EXIT_REGION_FRAME),
                StringConstant.v(taskId), StringConstant.v(rootMethod));
        emit(units, refs.ref(Hook.RESUME_OBSERVATION));
        insertBeforeSequence(body, returnUnit, units);
    }

    private static List<Unit> snapshotUnits(Body body) {
        List<Unit> units = new ArrayList<>();
        for (Unit unit : body.getUnits()) {
            units.add(unit);
        }
        return units;
    }

    /** Freezes one body's original numbering; see {@link
     *  #originalUnitIndex}. */
    static void tagOriginalUnits(List<Unit> units) {
        // Trace and concolic instrumentation may run in the same transform.
        for (Unit unit : units) {
            for (Tag tag : unit.getTags()) {
                if (tag instanceof OriginalUnitIndexTag) {
                    return;
                }
            }
        }
        for (int index = 0; index < units.size(); index++) {
            Unit unit = units.get(index);
            unit.addTag(new OriginalUnitIndexTag(index));
        }
    }

    /** The scene's concrete method for a selection, or the failure it is. */
    private static SootMethod concreteSelected(String signature,
                                               String unavailable,
                                               String notConcrete) {
        SootMethod method = CausynthStaticFacts.method(signature);
        if (method == null) {
            throw new IllegalStateException(unavailable);
        }
        if (!method.isConcrete()) {
            throw new IllegalStateException(notConcrete);
        }
        return method;
    }

    /** The one original unit at {@code unitIndex}, or {@code null}. */
    private static Stmt uniqueOriginalStmt(Body body, int unitIndex,
                                           String notUnique) {
        Stmt selected = null;
        for (Unit unit : snapshotUnits(body)) {
            if (originalUnitIndex(unit) != unitIndex) continue;
            if (selected != null || !(unit instanceof Stmt)) {
                throw new IllegalStateException(notUnique);
            }
            selected = (Stmt) unit;
        }
        return selected;
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
    private static SootClass phantomClass(String name) {
        SootClass existing = Scene.v().getSootClassUnsafe(name);
        if (existing != null) {
            return existing;
        }
        SootClass created = new SootClass(name, Modifier.PUBLIC);
        created.setPhantomClass();
        Scene.v().addClass(created);
        return created;
    }

    /** Wraps one method in a balanced skeleton envelope. */
    private void instrumentLiteMethod(
            Body body, SootMethod method, List<Unit> originalUnits,
            Unit insertionPoint, Unit lowerBound, Value receiver,
            HookCatalog refs, boolean recordExceptionalExit) {
        Local callId = newTraceLocal(body, LongType.v(),
                "$causynthLiteCallId");
        List<Unit> entry = new ArrayList<>();
        entry.add(Jimple.v().newAssignStmt(callId, LongConstant.v(0L)));
        emit(entry, callId, refs.ref(Hook.ENTER_METHOD_LITE),
                StringConstant.v(method.getSignature()), receiver);
        insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);

        for (int index = instrumentableFrom(originalUnits, lowerBound);
                index >= 0 && index < originalUnits.size(); index++) {
            Unit unit = originalUnits.get(index);
            if (unit instanceof ReturnStmt
                    || unit instanceof ReturnVoidStmt) {
                Stmt exit = invoke(refs.ref(Hook.EXIT_ACTIVE_METHOD_LITE));
                body.getUnits().insertBefore(exit, unit);
            }
        }
        addThrowHandler(body, insertionPoint, refs,
                recordExceptionalExit ? Hook.THROW_ACTIVE_METHOD
                        : Hook.THROW_ACTIVE_METHOD_LITE, "$causynthThrown");
    }

    private void instrumentRichMethod(
            Body body, SootMethod method, List<Unit> originalUnits,
            Unit insertionPoint, Unit lowerBound, Value receiver,
            HookCatalog refs, String openedRegionId) {
        Local callId = newTraceLocal(body, LongType.v(), "$causynthCallId");
        List<Unit> entryUnits = new ArrayList<>();
        // Keep the initialization as a defensive verifier-visible value.
        entryUnits.add(Jimple.v().newAssignStmt(callId, LongConstant.v(0L)));
        emit(entryUnits, callId, refs.ref(Hook.ENTER_METHOD),
                StringConstant.v(method.getSignature()), receiver,
                StringConstant.v(openedRegionId));
        for (int index = 0; index < method.getParameterCount(); index++) {
            Value parameter = parameterLocal(body, index);
            if (parameter == null) continue;
            Value objectValue = objectArg(body, parameter, entryUnits);
            Value primitiveValue = primitiveValueString(body, parameter, entryUnits);
            emit(entryUnits, refs.ref(Hook.RECORD_METHOD_ARGUMENT), callId,
                    IntConstant.v(index),
                    StringConstant.v(method.getParameterType(index).toString()),
                    objectValue, primitiveValue);
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
                        refs);
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
                        refs.ref(Hook.EXIT_ACTIVE_METHOD));
            }
        }
        addThrowHandler(body, insertionPoint, refs, Hook.THROW_ACTIVE_METHOD,
                "$causynthThrown");
    }

    private void instrumentCallSite(Body body, SootMethod method, Stmt stmt,
                                    int unitIndex, Local ownerCallId,
                                    HookCatalog refs) {
        InvokeExpr invoke = stmt.getInvokeExpr();
        List<Unit> before = new ArrayList<>();
        Value receiverBase = runtimeCallSiteReceiver(invoke);
        Value receiver = receiverBase == null
                ? NullConstant.v() : objectArg(body, receiverBase, before);
        Local invocationId = newTraceLocal(body, LongType.v(), "$causynthInvocation");
        emit(before, invocationId, refs.ref(Hook.BEGIN_CALL), ownerCallId,
                StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex),
                StringConstant.v(invoke.getMethodRef().getSignature()),
                receiver);
        for (int index = 0; index < invoke.getArgCount(); index++) {
            Value argument = invoke.getArg(index);
            Value objectValue = objectArg(body, argument, before);
            Value primitiveValue = primitiveValueString(body, argument, before);
            Type declaredType = index < invoke.getMethodRef().parameterTypes().size()
                    ? invoke.getMethodRef().parameterType(index) : argument.getType();
            emit(before, refs.ref(Hook.RECORD_CALL_ARGUMENT), invocationId,
                    IntConstant.v(index),
                    StringConstant.v(declaredType.toString()), objectValue,
                    primitiveValue);
        }
        insertBeforeSequence(body, stmt, before);

        Value returnValue = runtimeCallSiteReturnValue(stmt, invoke);
        List<Unit> after = new ArrayList<>();
        Value returnObject = objectArg(body, returnValue, after);
        Value primitiveReturn = primitiveValueString(body, returnValue, after);
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

    /**
     * The receiver of a successful constructor call is initialized when the
     * after-call hook runs, so it is both verifier-safe and the exact object
     * produced by that invocation.
     */
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
        Unit originalTarget = branch.getTarget();
        List<Unit> falsePath = new ArrayList<>();
        Unit falseRecord = invoke(refs.ref(Hook.RECORD_BRANCH), callId,
                StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex), StringConstant.v(expression),
                IntConstant.v(0));
        falsePath.add(falseRecord);
        insertAfterSequence(body, branch, falsePath);

        Unit trueEntry = Jimple.v().newNopStmt();
        List<Unit> truePath = new ArrayList<>();
        truePath.add(trueEntry);
        Unit trueRecord = invoke(refs.ref(Hook.RECORD_BRANCH), callId,
                StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex), StringConstant.v(expression),
                IntConstant.v(1));
        truePath.add(trueRecord);
        Unit resume = Jimple.v().newGotoStmt(originalTarget);
        truePath.add(resume);
        for (Unit unit : truePath) {
            body.getUnits().add(unit);
        }
        branch.setTarget(trueEntry);
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
            if (successorIndex == shape.defaultSuccessorIndex) {
                branch.setDefaultTarget(entry);
            } else {
                branch.setTarget(successorIndex, entry);
            }
        }
    }

    private void insertMethodExit(Body body, Stmt returnUnit, Value returnValue,
                                  SootMethodRef exitRef) {
        List<Unit> units = new ArrayList<>();
        Value objectValue = objectArg(body, returnValue, units);
        Value primitiveValue = primitiveValueString(body, returnValue, units);
        emit(units, exitRef, objectValue, primitiveValue);
        insertBeforeSequence(body, returnUnit, units);
    }

    /**
     * Appends a catch-all whose incoming verifier frame reads only the caught
     * throwable, reports the exceptional exit and rethrows.  {@code identity}
     * is the argument list the hook takes ahead of the throwable: empty is the
     * method-activation form, and a region identity additionally brackets the
     * report with paused observation.
     *
     * <p>{@code start} obeys the woven-trap rule of {@link
     * #afterWovenPrologue}: it is a unit the construct's prologue -- every
     * store of every woven local this handler reads through {@code identity}
     * -- has already fallen through to.  {@link #validateWovenBodies} is
     * what enforces that on the finished body.</p>
     */
    /**
     * THE WOVEN-TRAP RULE: a woven catch-all opens at the first unit the
     * construct's own prologue falls through to -- never at a unit of the
     * prologue itself.
     *
     * <p>Every woven local a handler reads (a region token, an invocation
     * id) is stored by that prologue, and the JVM merges the frame of EVERY
     * unit in the trap range into the handler's incoming frame.  A range
     * that opened at the store therefore merges the frame from before it, in
     * which the local is not assigned, and the handler's read of it cannot
     * be verified.  hdfs-17960's woven {@code FSNamesystem.allowSnapshot}
     * was refused exactly so -- {@code @142: lload_2, Local index 2 is
     * invalid}, "get long/double overflows locals", with the stackmap at the
     * handler carrying {@code {Object, Object}} and no {@code Long} because
     * the trap opened at bci 0 while the token's {@code lstore_2} is bci 1.
     * A long or double local owns two slots, so a partially assigned one
     * does not merely lose its type: the read overflows the frame.</p>
     *
     * <p>Nothing is owed on the excluded prefix: an exception raised before
     * the frame was opened has no frame to close.  And the prologue is
     * entered by fall-through only ({@code insertBeforeNoRedirect} keeps
     * every branch on its old target, and a loop-body entry moves the whole
     * prologue together), so the store dominates every unit from here on --
     * which is what makes the local assigned on every path into the range,
     * at every return the exit hooks read it at, and on every exception edge
     * into the handler.  Soot's {@code LocalPacker} cannot pack the local
     * into a slot shared with another type either: a local the handler reads
     * is live across the whole range.</p>
     *
     * @return the unit after {@code prologue}, or null when the prologue
     *         ends the body -- a construct with no unit to guard opens no
     *         trap rather than guarding its own store
     */
    private static Unit afterWovenPrologue(Body body, List<Unit> prologue) {
        if (prologue == null || prologue.isEmpty()) return null;
        return body.getUnits().getSuccOf(prologue.get(prologue.size() - 1));
    }

    private void addThrowHandler(Body body, Unit start, HookCatalog refs,
                                 Hook throwHook, String localName,
                                 Value... identity) {
        if (start == null) {
            return;
        }
        Local caught = newTraceLocal(body, RefType.v("java.lang.Throwable"),
                localName);
        Value[] args = Arrays.copyOf(identity, identity.length + 1);
        args[identity.length] = caught;
        List<Unit> units = new ArrayList<>();
        units.add(Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef()));
        if (identity.length == 0) {
            emit(units, refs.ref(throwHook), args);
        } else {
            refs.bracket(units, throwHook, args);
        }
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

    private static void insertBeforeSequence(Body body, Unit anchor,
                                             List<Unit> units) {
        for (Unit unit : units) {
            body.getUnits().insertBefore(unit, anchor);
        }
    }

    private static void insertBeforeOrAppendNoRedirect(Body body, Unit anchor,
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

    private static void insertAfterSequence(Body body, Unit anchor,
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
        boolean instrumentationSafe = lowerBound == null;
        for (int unitIndex = 0; unitIndex < units.size(); unitIndex++) {
            Unit unit = units.get(unitIndex);
            instrumentationSafe |= unit == lowerBound;
            if (!instrumentationSafe) continue;
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
        if (field == null) {
            return;
        }
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

    private static Local newTraceLocal(Body body, Type type, String prefix) {
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

    private enum Hook {
        ENTER_METHOD_LITE,
        EXIT_ACTIVE_METHOD_LITE,
        THROW_ACTIVE_METHOD_LITE,
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
        ENTER_METHOD_FRAME,
        EXIT_METHOD_FRAME,
        THROW_METHOD_FRAME,
        ENTER_CONFIGURED_SOURCE_PHASE_SITE,
        EXIT_CONFIGURED_SOURCE_PHASE_SITE,
        THROW_CONFIGURED_SOURCE_PHASE_SITE,
        ENTER_ACCESSOR_CALL_CONTEXT,
        EXIT_ACCESSOR_CALL_CONTEXT,
        OBSERVE_DECLARED_WRITE_SITE,
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
        OPEN_LOOP_INVOCATION,
        CLOSE_LOOP_INVOCATION,
        EXIT_REGION_FRAME,
        THROW_REGION_FRAME
    }

    /** Typed registry for static instrumentation hooks. */
    private static final class HookCatalog {
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

        /**
         * THE hooks both passes weave, declared once: the work start and its
         * claim, and the calling-context frame (which carries its receiver
         * for the attribution rule).  Each pass binds them to its own runtime
         * class; the shapes, and so the index both passes compute from
         * them, are one declaration.  Scope capture rides on the
         * start hook itself -- it used to ride on the recording's BEGIN_CALL
         * alone, which the replay never weaves.
         */
        private HookCatalog shared(SootClass owner) {
            Type string = RefType.v("java.lang.String");
            Type object = RefType.v("java.lang.Object");
            return add(Hook.START_WORK, owner, "startWork", VoidType.v(),
                    string, object)
                    .add(Hook.CLAIM_START, owner, "claimStart", VoidType.v(),
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
         * Appends {@code hook(args)} with observation paused across it.
         *
         * <p>Paused where there is symbolic observation to pause: the
         * recording pass registers no such hook, and this is the one place
         * that decides it rather than every caller asking
         * {@code ref(PAUSE_OBSERVATION) != null} for itself -- which is what
         * the work-start walk did and what the frame trio's throw handler
         * did not, so the recording's weave of it raised a
         * NullPointerException inside Soot's invoke builder.</p>
         */
        private void bracket(Collection<Unit> units, Hook hook,
                             Value... args) {
            boolean observed = ref(Hook.PAUSE_OBSERVATION) != null;
            if (observed) emit(units, ref(Hook.PAUSE_OBSERVATION));
            emit(units, ref(hook), args);
            if (observed) emit(units, ref(Hook.RESUME_OBSERVATION));
        }

        /** Appends {@code target = hook(args)}, observation paused. */
        private void bracket(Collection<Unit> units, Value target, Hook hook,
                             Value... args) {
            boolean observed = ref(Hook.PAUSE_OBSERVATION) != null;
            if (observed) emit(units, ref(Hook.PAUSE_OBSERVATION));
            emit(units, target, ref(hook), args);
            if (observed) emit(units, ref(Hook.RESUME_OBSERVATION));
        }

        private static HookCatalog trace() {
            SootClass recorder = phantomClass(TRACE_RECORDER_CLASS);
            Type string = RefType.v("java.lang.String");
            Type object = RefType.v("java.lang.Object");
            return new HookCatalog()
                    .add(Hook.ENTER_METHOD_LITE, recorder,
                            "enterMethodLite", LongType.v(), string, object)
                    .add(Hook.EXIT_ACTIVE_METHOD_LITE, recorder,
                            "exitActiveMethodLite", VoidType.v())
                    .add(Hook.THROW_ACTIVE_METHOD_LITE, recorder,
                            "throwActiveMethodLite", VoidType.v(),
                            RefType.v("java.lang.Throwable"))
                    .add(Hook.ENTER_METHOD, recorder, "enterMethod",
                            LongType.v(), string, object, string)
                    .shared(recorder)
                    .add(Hook.RECORD_METHOD_ARGUMENT, recorder,
                            "recordMethodArgument", VoidType.v(), LongType.v(),
                            IntType.v(), string, object, string)
                    .add(Hook.BEGIN_CALL, recorder, "beginCall", LongType.v(),
                            LongType.v(), string, IntType.v(), string, object)
                    .add(Hook.RECORD_CALL_ARGUMENT, recorder,
                            "recordCallArgument", VoidType.v(), LongType.v(),
                            IntType.v(), string, object, string)
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
                            VoidType.v(), object, string)
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
                    .add(Hook.ENTER_ACCESSOR_CALL_CONTEXT, runtime,
                            "enterAccessorCallContext", LongType.v(), string,
                            IntType.v(), string, string, object)
                    .add(Hook.EXIT_ACCESSOR_CALL_CONTEXT, runtime,
                            "exitAccessorCallContext", VoidType.v(), LongType.v())
                    .add(Hook.OBSERVE_DECLARED_WRITE_SITE, runtime,
                            "observeDeclaredWriteSite", VoidType.v(), string,
                            string, object)
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
                            BooleanType.v(), LongType.v(), LongType.v(), string,
                            IntType.v(), string, BooleanType.v())
                    .add(Hook.RESOLVE_SWITCH_BRANCH, runtime,
                            "resolveSwitchBranch", IntType.v(), LongType.v(),
                            LongType.v(), string, IntType.v(), string, string,
                            string, IntType.v())
                    .add(Hook.CHECK_LOOP_BACKEDGE, runtime,
                            "checkLoopBackedge", VoidType.v(), string,
                            IntType.v())
                    .add(Hook.CHECK_REPLAY_LOOP_BODY, runtime,
                            "checkReplayLoopBody", VoidType.v(), string,
                            IntType.v())
                    .add(Hook.OPEN_LOOP_INVOCATION, runtime,
                            "openLoopInvocation", VoidType.v(), string)
                    .add(Hook.CLOSE_LOOP_INVOCATION, runtime,
                            "closeLoopInvocation", VoidType.v(), string)
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
