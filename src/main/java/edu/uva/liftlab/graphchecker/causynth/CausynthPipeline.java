package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.AccessorCallTarget;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ConcolicBranchSelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ConcolicMaterializationSelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.InstrumentationPlan;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.CallArgumentOutputCapture;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ExactHeapOutputCapture;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.CommunicationEffectCapture;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.RootedOutputCapture;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
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
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.UnitBox;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.PrimType;
import soot.jimple.AssignStmt;
import soot.jimple.ArrayRef;
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
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.SwitchStmt;
import soot.jimple.ThisRef;
import soot.jimple.ThrowStmt;
import soot.tagkit.Tag;
import soot.toolkits.graph.BriefUnitGraph;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.EnumMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.firstNonBlank;

/**
 * Annotation-directed static backward data-flow analysis.
 *
 * <p>The analysis starts from one annotated exception construction and
 * discovers the control flow required to reach its throw. Local Java/Jimple
 * calls, interface dispatches, and explicitly configured protocol bridges all
 * emit edges into the same static data-flow graph.</p>
 */
public final class CausynthPipeline {
    private static final Logger LOG = LoggerFactory.getLogger(CausynthPipeline.class);
    private static final String TRACE_RECORDER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder";
    private static final String CONCOLIC_REGION_RUNTIME_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime";
    private final GraphCheckerOptions options;
    private final Map<SootField, SootMethod> exitFieldReaders =
            new IdentityHashMap<>();

    public CausynthPipeline(GraphCheckerOptions options) {
        this.options = options;
    }

    public void run() throws IOException {
        if (concolicInstrumentationEnabled()) {
            instrumentConcolicRegions();
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

        CausynthTargetContext target = CausynthTargetResolver.resolve(options);
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
        // The graph is already resident here. Persist broad candidate
        // skeletons now so the first runtime pass only has to bind concrete
        // activations. REGION.IN/OUT and field paths are deliberately absent.
        SymbolicRegionPlanner.planSelectedSkeleton(result,
                result.traceMethods);
        long skeletonPlanningMillis = elapsedMillis(skeletonPlanningStart);
        long instrumentationStart = System.nanoTime();
        instrumentRegionSkeletonTrace(result);
        long instrumentationMillis = elapsedMillis(instrumentationStart);
        long artifactWriteStart = System.nanoTime();
        CausynthArtifactWriter.writeDiscoveryArtifacts(
                target.outputDir, result);
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

    /** First pass: balanced method activation envelopes only. */
    private void instrumentRegionSkeletonTrace(StaticProgram result) {
        instrumentLiteRuntimeTrace(result);
    }

    /**
     * Second pass: rich evidence for only runtime-selected region methods.
     * Every direct call, branch and declared field access is recorded. Static
     * discovery edges no longer decide which state sites are visible here.
     */
    private void instrumentRuntimeState(StaticProgram result) {
        SootMethodRef recordFieldRef = traceRecorderFieldMethodRef();
        SootMethodRef recordArrayRef = traceRecorderArrayMethodRef();
        HookCatalog richRefs = HookCatalog.trace();
        TraceSelection traceSelection = TraceSelection.allRuntimeState();
        Set<String> skippedClasses = traceSkipClasses();
        int skippedMethods = 0;
        for (String signature : result.traceMethods) {
            SootMethod method;
            try {
                method = Scene.v().getMethod(signature);
            } catch (RuntimeException exception) {
                throw new IllegalStateException("REGION_STATE method is "
                        + "outside production application scope: "
                        + signature, exception);
            }
            if (method == null || !method.isConcrete()
                    || !method.getDeclaringClass().isApplicationClass()) {
                throw new IllegalStateException("REGION_STATE method is "
                        + "outside production application scope: "
                        + signature);
            }
            try {
                if (isTraceSkippedClass(method.getDeclaringClass().getName(),
                        skippedClasses)) {
                    skippedMethods++;
                    continue;
                }
                Body body = method.retrieveActiveBody();
                List<Unit> originalUnits = snapshotUnits(body);
                tagOriginalUnits(originalUnits);
                Unit insertionPoint = safeInstrumentationEntry(body, method);
                if (method.isConstructor() && insertionPoint == null) {
                    continue;
                }
                Unit lowerBound = method.isConstructor()
                        ? insertionPoint : null;
                Value receiver = NullConstant.v();
                if (!method.isStatic()) {
                    try {
                        Local thisLocal = body.getThisLocal();
                        if (thisLocal != null) {
                            receiver = thisLocal;
                        }
                    } catch (RuntimeException ignored) {
                    }
                }
                instrumentRichMethod(body, method,
                        originalUnits, insertionPoint, lowerBound, receiver,
                        traceSelection, richRefs);
                instrumentFieldTrace(body, method, recordFieldRef,
                        traceSelection, originalUnits, lowerBound);
                instrumentReferenceArrayTrace(body, method, recordArrayRef,
                        originalUnits, lowerBound);
            } catch (RuntimeException exception) {
                LOG.debug("Skipping trace instrumentation for {}", signature, exception);
            }
        }
        if (skippedMethods > 0) {
            LOG.info("Skipped runtime-trace instrumentation for {} "
                    + "configured methods", skippedMethods);
        }
        LOG.info("Instrumented {} runtime-selected methods for REGION_STATE "
                + "trace", result.traceMethods.size());
    }

    /**
     * The methods the skeleton pass exists to watch.
     *
     * <p>Pass 1 answers one question: which of the candidate regions the
     * static analysis just planned actually activate. That makes the
     * instrumentation set the candidate set. Every row the region planner
     * keeps is a row whose method belongs to the region it is binding - it
     * discards the rest before looking at anchors - so a method in the slice
     * but in no candidate region can only produce rows nobody reads, at the
     * price of running the recorder inside it. Envelope nesting survives the
     * narrowing because the recorder derives a parent from the enclosing
     * <em>instrumented</em> frame: dropping intermediate methods shortens the
     * chain and preserves every ancestor-descendant pair that remains.</p>
     *
     * <p>The annotated target method is added last and unconditionally. It is
     * the one method the run exists to observe, and whether some candidate
     * region happens to enclose it is a property of how far the planner's
     * forward closure reached, not of whether the pass should report that the
     * target executed. On this checkout no candidate region contains it, and
     * without this the pass would run the workload all the way through the
     * target and record nothing about it.</p>
     */
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
     * <p>That difference is deliberate and is recorded as such in
     * {@code target_resolved.json}: with {@code skeletonTargetThrowRecorded}
     * true, the absence of a {@code METHOD_EXIT_THROW} row for the target is
     * an observation; the absence of one for any other instrumented method is
     * not, because none is ever written. Normal exits stay silent everywhere,
     * the target included, so the entry-row counts this pass has always
     * produced do not move.</p>
     */
    private void instrumentLiteRuntimeTrace(StaticProgram result) {
        Set<String> selectedMethods = skeletonCandidateMethods(result);
        if (selectedMethods.isEmpty()) {
            LOG.warn("No candidate region selected a method to instrument; "
                    + "the REGION_SKELETON pass will bind no activation");
        }
        HookCatalog refs = HookCatalog.trace();
        Set<String> skippedClasses = traceSkipClasses();
        String annotatedTarget = annotatedTargetMethod(result);
        boolean targetThrowRecorded = false;
        int instrumentedMethods = 0;
        int skippedMethods = 0;
        for (String signature : selectedMethods) {
            try {
                SootMethod method = Scene.v().getMethod(signature);
                if (method == null || !method.isConcrete()) {
                    continue;
                }
                if (isTraceSkippedClass(method.getDeclaringClass().getName(),
                        skippedClasses)) {
                    skippedMethods++;
                    continue;
                }
                Body body = method.retrieveActiveBody();
                List<Unit> originalUnits = snapshotUnits(body);
                tagOriginalUnits(originalUnits);
                Unit insertionPoint = safeInstrumentationEntry(body, method);
                if (method.isConstructor() && insertionPoint == null) {
                    continue;
                }
                Unit lowerBound = method.isConstructor()
                        ? insertionPoint : null;
                Value receiver = NullConstant.v();
                if (!method.isStatic()) {
                    try {
                        receiver = body.getThisLocal();
                    } catch (RuntimeException ignored) {
                    }
                }
                boolean recordThrow = !annotatedTarget.isEmpty()
                        && annotatedTarget.equals(signature);
                instrumentLiteMethod(
                        body, method, originalUnits,
                        insertionPoint, lowerBound, receiver, refs,
                        recordThrow);
                targetThrowRecorded |= recordThrow;
                instrumentedMethods++;
            } catch (RuntimeException exception) {
                LOG.debug("Skipping skeleton trace instrumentation for {}",
                        signature, exception);
            }
        }
        // The flag travels with the discovery artifacts so a later reader of
        // targetThrowRecords knows whether a zero is an observation.
        result.targetResolved.put("skeletonTargetThrowRecorded",
                targetThrowRecorded);
        LOG.info("Instrumented {} of {} candidate methods for REGION_SKELETON "
                        + "trace ({} skipped) out of a {}-method static slice "
                        + "and {} candidate regions",
                instrumentedMethods, selectedMethods.size(), skippedMethods,
                result.traceMethods.size(), result.regions.size());
        if (targetThrowRecorded) {
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

    /**
     * The annotated target's Soot signature, or {@code ""} when absent.
     *
     * <p>Read exactly as {@link #skeletonCandidateMethods} reads it, so the
     * signature compared here is the one that entered the instrumented set.</p>
     */
    private static String annotatedTargetMethod(StaticProgram result) {
        Object method = result.targetResolved.get("method");
        if (method == null || String.valueOf(method).trim().isEmpty()) {
            return "";
        }
        return String.valueOf(method);
    }

    /**
     * The campaign's one deduplicated instrumentation envelope.
     *
     * <p>README section 1 states it per task as
     *
     * <pre>
     * mandatory target / region / RPC / SASL anchors
     *   UNION
     * (static target slice INTERSECT seed-executed sites
     *                      INTERSECT current output closure)
     *   UNION
     * exact alternative branch/writer/loop sites named by this task
     * </pre>
     *
     * <p>The first and third terms are the plan's anchors and its named
     * branch/materialization sites. The middle term is not recomputed here:
     * the scheduler already intersected the static slice with the seed trace
     * and the output closure when it wrote the task's execution
     * scope, and re-deriving it from the Scene would be a second analysis
     * framework. This class unions those per-task envelopes, deduplicates
     * them, and hands each hook family one method set to rewrite.</p>
     *
     * <p>It also owns original-unit tagging before any body is rewritten.</p>
     */
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
        private final Set<String> writerMethods = new LinkedHashSet<>();
        private final ConcolicMaterializationSelection materializations =
                new ConcolicMaterializationSelection();
        private final ConcolicBranchSelection branches =
                new ConcolicBranchSelection();
        // Keyed by the plan itself, not by its root method: a campaign may
        // hold several tasks rooted at one method - a path flip is exactly
        // that - and each keeps its own replay entry and engine arm.
        private final Map<InstrumentationPlan, SootMethod> replayEntries =
                new IdentityHashMap<>();
        private LoopBoundPolicy loopBound;
        private int boundedBackedges;
        private int associativeReadSites;
        private int unselectedAssociativeReads;
        private int fieldMaterializationSites;
        private int scannedBodies;
        private final Map<String, Integer> emittedHooks =
                new LinkedHashMap<>();
        private final Set<String> rewrittenMethods = new LinkedHashSet<>();

        private CampaignEnvelope(List<InstrumentationPlan> campaign) {
            this.campaign = campaign;
            for (InstrumentationPlan plan : campaign) {
                materializations.mergeFrom(plan.materializations());
                branches.mergeFrom(plan.branches());
                methods.addAll(plan.envelopeMethods());
                writerMethods.addAll(plan.instrumentationMethods());
                Set<String> bounded = new LinkedHashSet<>(
                        plan.instrumentationMethods());
                SootMethod replayEntry = declaredReplayEntry(plan);
                replayEntries.put(plan, replayEntry);
                // The logical region remains rooted at the plan's root.  The
                // replay entry is only the finite activation at which the VM
                // starts recording, so its loops are still part of the
                // bounded execution semantics.
                bounded.add(replayEntry.getSignature());
                methods.add(replayEntry.getSignature());
                writerMethods.add(replayEntry.getSignature());
                loopBoundMethods.addAll(bounded);
                fixedCountLoopSites.addAll(plan.fixedCountLoopSites());
                if (loopBound != null && !loopBound.identity()
                        .equals(plan.loopBound().identity())) {
                    // One union tree installs one policy on every shared
                    // method.  Equal campaign maxima are insufficient: two
                    // tasks may still declare different K_L for one loop.
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
        private void tagSelectedBodies() {
            Set<String> tagged = new LinkedHashSet<>(methods);
            tagged.addAll(loopBoundMethods);
            for (String signature : tagged) {
                try {
                    SootMethod method = Scene.v().getMethod(signature);
                    if (method != null && method.isConcrete()) {
                        tagOriginalUnits(snapshotUnits(
                                method.retrieveActiveBody()));
                    }
                } catch (RuntimeException ignored) {
                    // Unresolvable bodies are dropped by every later pass too.
                }
            }
        }

        /**
         * Bounds the campaign's loops once.
         *
         * <p>Every task in a schedule carries the same {@code K_L}, which the
         * constructor has already checked, so the union may be bounded in one
         * pass. Per task it installed one set of backedge hooks per plan row
         * on every method two tasks shared, and the runtime refuses a hook
         * whose declared bound is not the admitted activation's.</p>
         */
        private void boundSelectedLoops() {
            if (loopBound == null) {
                return;
            }
            boundedBackedges = instrumentConcolicLoopBounds(
                    loopBoundMethods, loopBound, fixedCountLoopSites);
            LOG.info("Bounded {} slice backedge(s) across {} selected "
                            + "method(s)",
                    boundedBackedges, loopBoundMethods.size());
        }

        private SootMethod replayEntry(InstrumentationPlan plan) {
            return replayEntries.get(plan);
        }

        private boolean needsAssociativeReadSite() {
            for (InstrumentationPlan plan : campaign) {
                if (plan.dynamicAssociativeTarget()) return true;
            }
            return false;
        }

        /**
         * Counts the hooks that are actually in the program now.
         *
         * <p>Deliberately measured from the rewritten bodies rather than from
         * the plan: the plan states what should have been instrumented, and
         * the question this answers is what was. Only bodies Soot already
         * holds are read, so this walks what the pass touched and does not
         * reintroduce the full-application body retrieval it removed.</p>
         */
        private void countEmittedHooks() {
            Set<String> reachable = new LinkedHashSet<>(methods);
            reachable.addAll(loopBoundMethods);
            for (String signature : reachable) {
                final SootMethod method;
                try {
                    method = Scene.v().getMethod(signature);
                } catch (RuntimeException missing) {
                    continue;
                }
                if (method == null || !method.hasActiveBody()) continue;
                boolean rewritten = false;
                for (Unit unit : method.getActiveBody().getUnits()) {
                    if (!(unit instanceof Stmt)
                            || !((Stmt) unit).containsInvokeExpr()) {
                        continue;
                    }
                    SootMethodRef ref = ((Stmt) unit).getInvokeExpr()
                            .getMethodRef();
                    if (!CONCOLIC_REGION_RUNTIME_CLASS.equals(
                            ref.declaringClass().getName())) {
                        continue;
                    }
                    String hook = ref.name();
                    Integer seen = emittedHooks.get(hook);
                    emittedHooks.put(hook, seen == null ? 1 : seen + 1);
                    if (!"pauseObservation".equals(hook)
                            && !"resumeObservation".equals(hook)) {
                        rewritten = true;
                    }
                }
                if (rewritten) {
                    rewrittenMethods.add(signature);
                }
            }
        }

        /**
         * States what was rewritten, and states it as a static count.
         *
         * <p>A trace sequence number is an event count: it says how many
         * times instrumented code ran, not how much code was instrumented.
         * The two were read as one number while diagnosing a replay that
         * never left {@code waitActive()}, so they are reported apart here -
         * unique rewritten methods and unique hook sites, both static.</p>
         */
        private void report() {
            countEmittedHooks();
            LOG.info("Concolic campaign rewrote {} unique method(s) at {} "
                            + "hook site(s): {}", rewrittenMethods.size(),
                    emittedSiteCount(), emittedHooks);
            LOG.info("Concolic campaign envelope: {} task(s); {} selected "
                            + "method(s), of which {} were scanned; "
                            + "static site counts: {} branch, "
                            + "{} local materialization, "
                            + "{} declared field over {} read site(s), "
                            + "{} method argument, "
                            + "{} accessor call, {} associative read; "
                            + "{} bounded backedge(s). These are unique rewritten "
                            + "methods/sites, not dynamic trace events.",
                    campaign.size(), methods.size(), scannedBodies,
                    branches.siteCount(),
                    materializations.localSiteCount(),
                    materializations.fieldCount(), fieldMaterializationSites,
                    materializations.methodArgumentCount(),
                    materializations.accessorCalls().size(),
                    associativeReadSites, boundedBackedges);
            if (materializations.fieldCount() > 0
                    && fieldMaterializationSites == 0
                    && materializations.accessorCalls().isEmpty()) {
                LOG.warn("{}: {} declared field(s) have no read site inside "
                                + "the campaign envelope",
                        GAP_FIELD_MATERIALIZATION_SITE_ABSENT,
                        materializations.fieldCount());
            }
            if (unselectedAssociativeReads > 0) {
                LOG.info("{}: {} associative read(s) inside the envelope are "
                                + "not selected sites and were left alone",
                        GAP_ASSOCIATIVE_READ_SITE_UNSELECTED,
                        unselectedAssociativeReads);
            }
            if (associativeReadSites == 0 && needsAssociativeReadSite()) {
                LOG.warn("{}: a task selects a value by associative access "
                                + "ordinal, but no exact selected method and "
                                + "unit names a Map read to apply it at",
                        GAP_ASSOCIATIVE_READ_SITE_UNDECLARED);
            }
            String report = firstNonBlank(System.getProperty(
                    "causynth.concolic.envelope.report"));
            if (report == null) {
                return;
            }
            try {
                Path path = Paths.get(report).toAbsolutePath().normalize();
                if (path.getParent() != null) {
                    Files.createDirectories(path.getParent());
                }
                Files.write(path, Collections.singletonList(
                        envelopeReportJson()), StandardCharsets.UTF_8);
            } catch (IOException failure) {
                LOG.warn("Could not write the envelope report to {}", report,
                        failure);
            }
        }

        /**
         * Hook sites, not counting the observation bracket: a pause/resume
         * pair belongs to the site it brackets and is not one of its own.
         */
        private int emittedSiteCount() {
            int sites = 0;
            for (Map.Entry<String, Integer> hook : emittedHooks.entrySet()) {
                if (!"pauseObservation".equals(hook.getKey())
                        && !"resumeObservation".equals(hook.getKey())) {
                    sites += hook.getValue();
                }
            }
            return sites;
        }

        private String envelopeReportJson() {
            JsonObject json = new JsonObject();
            json.addProperty("kind", "CONCOLIC_INSTRUMENTATION_ENVELOPE");
            json.addProperty("tasks", campaign.size());
            json.addProperty("selectedMethods", methods.size());
            json.addProperty("scannedMethods", scannedBodies);
            // Unique rewritten methods and hook sites, counted from the
            // rewritten bodies.  A trace sequence number is an event count
            // and answers a different question; these two are static.
            json.addProperty("uniqueRewrittenMethods",
                    rewrittenMethods.size());
            JsonObject hooks = new JsonObject();
            for (Map.Entry<String, Integer> hook : emittedHooks.entrySet()) {
                hooks.addProperty(hook.getKey(), hook.getValue());
            }
            json.addProperty("uniqueRewrittenSites", emittedSiteCount());
            json.add("emittedHooks", hooks);
            json.addProperty("branchSites", branches.siteCount());
            json.addProperty("localMaterializationSites",
                    materializations.localSiteCount());
            json.addProperty("declaredFields",
                    materializations.fieldCount());
            json.addProperty("methodArgumentSlots",
                    materializations.methodArgumentCount());
            json.addProperty("accessorCallSites",
                    materializations.accessorCalls().size());
            json.addProperty("fieldMaterializationSites",
                    fieldMaterializationSites);
            json.addProperty("associativeReadSites", associativeReadSites);
            json.addProperty("unselectedAssociativeReads",
                    unselectedAssociativeReads);
            json.addProperty("boundedBackedges", boundedBackedges);
            return json.toString();
        }
    }

    /**
     * An associative read inside the envelope that no task named as an exact
     * site. It is left alone; naming it is what a later task widens.
     */
    static final String GAP_ASSOCIATIVE_READ_SITE_UNSELECTED =
            "ASSOCIATIVE_READ_SITE_UNSELECTED";

    /**
     * A task whose solver model selects by associative access ordinal but
     * whose plan names no exact read site to apply it at.
     */
    static final String GAP_ASSOCIATIVE_READ_SITE_UNDECLARED =
            "ASSOCIATIVE_READ_SITE_UNDECLARED";

    /**
     * A declared field whose reads all lie outside the campaign envelope.
     * Narrowing the scan to the envelope is what makes this visible; the
     * widening that answers it belongs to a later task's plan.
     */
    static final String GAP_FIELD_MATERIALIZATION_SITE_ABSENT =
            "FIELD_MATERIALIZATION_SITE_ABSENT";

    /**
     * Rewrites the campaign's one deduplicated instrumentation envelope.
     *
     * <p>README section 1: the envelope is the union of the per-task
     * envelopes, deduplicated, and each selected site is rewritten once. The
     * pass this replaced walked every application method once per plan row
     * and inserted the same hook again for each of them, which is how a
     * three-thread fixture stayed fast while an HDFS startup - the same
     * rewrite applied to a `HashMap`-intensive program - did not.</p>
     *
     * <p>Only the region root and its output captures are per task, because
     * those hooks name a task's own root and bindings.
     * Every other evidence hook carries a site and no task id: the runtime
     * decides it by which activation is admitted, so one rewrite serves the
     * whole campaign.</p>
     */
    private void instrumentConcolicRegions() {
        instrumentConcolicCampaign(ConcolicInstrumentationSelections
                .instrumentationCampaignFromEnvironment());
    }

    /** Rewrites one campaign's envelope; see {@link #instrumentConcolicRegions}. */
    void instrumentConcolicCampaign(List<InstrumentationPlan> campaign) {
        HookCatalog refs = HookCatalog.concolic();
        CampaignEnvelope envelope = new CampaignEnvelope(campaign);
        envelope.tagSelectedBodies();
        envelope.boundSelectedLoops();
        for (InstrumentationPlan plan : campaign) {
            instrumentConcolicRegion(plan, refs, envelope);
        }
        instrumentConcolicCommunicationHandoffs(campaign, refs);
        instrumentConcolicAccessorCallContexts(envelope.materializations,
                refs);
        instrumentConcolicMethodArguments(envelope.materializations, refs);
        instrumentConcolicFieldWrites(envelope.writerMethods,
                envelope.materializations, refs);
        instrumentConcolicMaterializations(envelope, refs);
        instrumentConcolicBranches(envelope.branches, refs);
        envelope.report();
    }

    /**
     * Inserts region hooks at the roots selected by one campaign task's
     * runtime activation plan. Concolic instrumentation without that plan is
     * not executable.
     */
    private void instrumentConcolicRegion(InstrumentationPlan plan,
                                          HookCatalog refs,
                                          CampaignEnvelope envelope) {
        List<RootedOutputCapture> outputCaptureSelection =
                plan.outputCaptures();
        List<CallArgumentOutputCapture> callArgumentOutputs =
                plan.callArgumentOutputs();
        List<CommunicationEffectCapture> communicationEffects =
                plan.communicationEffects();
        List<ExactHeapOutputCapture> exactHeapOutputs =
                plan.exactHeapOutputs();
        String outputCaptureReceiverClass = plan.receiverClass();
        String signature = plan.rootMethod();
        SootMethod replayEntry = envelope.replayEntry(plan);
        String replayEntrySignature = replayEntry.getSignature();
        // Exact mutation captures must be installed before root-exit hooks.
        // When the definition method is the root itself, this guarantees the
        // completed mutation state is emitted while its region is still active.
        instrumentConcolicExactHeapOutputs(exactHeapOutputs, refs);
        instrumentConcolicCommunicationEffects(communicationEffects, refs);
        try {
            SootMethod method = replayEntry;
            if (method == null || !method.isConcrete()) {
                throw new IllegalStateException(
                        "Selected concolic root is not a concrete method: "
                                + replayEntrySignature);
            }
            Body body = method.retrieveActiveBody();
            List<Unit> originalUnits = snapshotUnits(body);
            tagOriginalUnits(originalUnits);
            Unit insertionPoint = safeInstrumentationEntry(body, method);
            if (method.isConstructor() && insertionPoint == null) {
                throw new IllegalStateException(
                        "Selected constructor root has no initialized-this "
                                + "instrumentation point: "
                                + replayEntrySignature);
            }
            Value receiver = NullConstant.v();
            if (!method.isStatic()) {
                try {
                    receiver = body.getThisLocal();
                } catch (RuntimeException ignored) {
                }
            }
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
            activation.add(Jimple.v().newAssignStmt(rootArguments,
                    Jimple.v().newNewArrayExpr(
                            RefType.v("java.lang.Object"),
                            IntConstant.v(method.getParameterCount()))));
            for (int index = 0; index < method.getParameterCount(); index++) {
                Type parameterType = method.getParameterType(index);
                if (!(parameterType instanceof RefType)
                        && !(parameterType instanceof ArrayType)) {
                    continue;
                }
                Value parameter;
                try {
                    parameter = body.getParameterLocal(index);
                } catch (RuntimeException ignored) {
                    continue;
                }
                activation.add(Jimple.v().newAssignStmt(
                        Jimple.v().newArrayRef(rootArguments,
                                IntConstant.v(index)),
                        objectArg(body, parameter, activation)));
            }
            // The entry hook decides admission, and that decision is this
            // bridge's own control flow over the workload's own objects: it
            // compares the root receiver against null and against a declared
            // class.  A campaign instruments one entry hook per plan row
            // naming this root, so on a thread that already carries symbolic
            // state every later hook re-evaluates those comparisons and, left
            // unbracketed, appends each one to the workload's path condition -
            // conditions the program never evaluated, inside whichever
            // occurrence is open.  Every other evidence hook is bracketed for
            // exactly this reason; the boundary belongs here, beside them, and
            // not in the runtime the boundary protects.
            //
            // The bracket cannot reach past the hook.  A frame entered while
            // paused is not tracking and cannot be made tracking afterwards,
            // so the resume has to stand between the hook and the first
            // workload bytecode that follows it - which is where it is.  The
            // region start keeps its own inner pause discipline either way.
            activation.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.PAUSE_OBSERVATION))));
            Unit enterRegion = Jimple.v().newAssignStmt(token,
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.ENTER_REGION_FRAME),
                            StringConstant.v(plan.instrumentationSelector()),
                            StringConstant.v(signature), receiver,
                            rootArguments));
            activation.add(enterRegion);
            activation.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RESUME_OBSERVATION))));
            Unit regionStart = enterRegion;
            for (int index = 0; index < method.getParameterCount(); index++) {
                Value parameter;
                try {
                    parameter = body.getParameterLocal(index);
                } catch (RuntimeException ignored) {
                    continue;
                }
                Value primitiveValue = primitiveValueString(body,
                        parameter, activation);
                if (PrimitiveWrapper.forType(parameter.getType()) != null) {
                    addPrimitiveArgumentMaterialization(body, parameter,
                            token, index, primitiveValue, activation,
                            refs.ref(Hook.MATERIALIZE_ARGUMENT),
                            refs.ref(Hook.PAUSE_OBSERVATION),
                            refs.ref(Hook.RESUME_OBSERVATION));
                } else {
                    Value objectValue = objectArg(body, parameter,
                            activation);
                    Local modeled = newTraceLocal(body,
                            RefType.v("java.lang.Object"),
                            "$causynthArgumentModel");
                    activation.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.PAUSE_OBSERVATION))));
                    activation.add(Jimple.v().newAssignStmt(modeled,
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.MATERIALIZE_ARGUMENT), token,
                                    IntConstant.v(index), objectValue,
                                    primitiveValue)));
                    activation.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.RESUME_OBSERVATION))));
                    Value converted = parameter.getType() instanceof RefType
                            && "java.lang.Object".equals(((RefType)
                            parameter.getType()).getClassName())
                            ? modeled : Jimple.v().newCastExpr(modeled,
                            parameter.getType());
                    activation.add(Jimple.v().newAssignStmt(parameter,
                            converted));
                    activation.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.PAUSE_OBSERVATION))));
                    activation.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.SYMBOLIZE_ARGUMENT), token,
                                    IntConstant.v(index), parameter,
                                    primitiveValue)));
                    activation.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.RESUME_OBSERVATION))));
                }
            }
            insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);

            for (Unit unit : originalUnits) {
                if (!(unit instanceof Stmt)) {
                    continue;
                }
                Stmt stmt = (Stmt) unit;
                if (stmt instanceof ReturnStmt) {
                    instrumentRegionExitFieldCaptures(body, stmt,
                            token, receiver, outputCaptureReceiverClass,
                            outputCaptureSelection, refs);
                    insertRegionExit(body, stmt, ((ReturnStmt) stmt).getOp(),
                            plan.instrumentationSelector(), signature,
                            refs.ref(Hook.EXIT_REGION_FRAME),
                            refs.ref(Hook.PAUSE_OBSERVATION),
                            refs.ref(Hook.RESUME_OBSERVATION));
                } else if (stmt instanceof ReturnVoidStmt) {
                    instrumentRegionExitFieldCaptures(body, stmt,
                            token, receiver, outputCaptureReceiverClass,
                            outputCaptureSelection, refs);
                    insertRegionExit(body, stmt, NullConstant.v(),
                            plan.instrumentationSelector(), signature,
                            refs.ref(Hook.EXIT_REGION_FRAME),
                            refs.ref(Hook.PAUSE_OBSERVATION),
                            refs.ref(Hook.RESUME_OBSERVATION));
                }
            }
            addRegionThrowHandler(body, regionStart,
                    plan.instrumentationSelector(), signature,
                    refs.ref(Hook.THROW_REGION_FRAME),
                    refs.ref(Hook.PAUSE_OBSERVATION),
                    refs.ref(Hook.RESUME_OBSERVATION));
        } catch (RuntimeException exception) {
            throw new IllegalStateException(
                    "Could not instrument selected concolic region root "
                            + signature + " at replay entry "
                            + replayEntrySignature, exception);
        }
        instrumentConcolicCallArgumentOutputs(callArgumentOutputs, refs);
        LOG.info("Instrumented symbolic-region root {} at replay entry {} "
                        + "for concolic replay; loop bodies bounded at {} "
                        + "iterations",
                signature, replayEntrySignature,
                plan.loopBound().maxBackedgeTraversals());
    }

    /** Captures the exact value presented at a configured protocol call. */
    private void instrumentConcolicCallArgumentOutputs(
            Collection<CallArgumentOutputCapture> captures,
            HookCatalog refs) {
        for (CallArgumentOutputCapture capture : captures) {
            final SootMethod method;
            try {
                method = Scene.v().getMethod(capture.method());
            } catch (RuntimeException missing) {
                throw new IllegalStateException(
                        "OUTPUT_CAPTURE_CALLER_UNAVAILABLE: "
                                + capture.captureBindingId(), missing);
            }
            if (method == null || !method.isConcrete()) {
                throw new IllegalStateException(
                        "OUTPUT_CAPTURE_CALLER_NOT_CONCRETE: "
                                + capture.captureBindingId());
            }
            Body body = method.retrieveActiveBody();
            Stmt selected = null;
            for (Unit unit : snapshotUnits(body)) {
                if (originalUnitIndex(unit) != capture.unitIndex()) continue;
                if (selected != null || !(unit instanceof Stmt)) {
                    throw new IllegalStateException(
                            "OUTPUT_CAPTURE_CALLSITE_NOT_UNIQUE: "
                                    + capture.captureBindingId());
                }
                selected = (Stmt) unit;
            }
            if (selected == null || !selected.containsInvokeExpr()) {
                throw new IllegalStateException(
                        "OUTPUT_CAPTURE_CALLSITE_UNAVAILABLE: "
                                + capture.captureBindingId());
            }
            InvokeExpr invoke = selected.getInvokeExpr();
            if (!capture.declaredCallee().equals(
                    invoke.getMethodRef().getSignature())
                    || capture.argumentIndex() < 0
                    || capture.argumentIndex() >= invoke.getArgCount()) {
                throw new IllegalStateException(
                        "OUTPUT_CAPTURE_CALL_ARGUMENT_MISMATCH: "
                                + capture.captureBindingId());
            }
            List<Unit> before = new ArrayList<>();
            // A primitive argument is a value the boundary publishes just as
            // much as a reference is.  Dropping it to null here is silent:
            // the capture row still exists, carries no expression, and can
            // never observe its relation, so the output boundary it belongs
            // to can never complete and the activation runs until something
            // else cuts it.  The declared parameter type is the boxing
            // authority, for the same reason it is on a field write.
            Value value = boxedCaptureValue(body,
                    invoke.getArg(capture.argumentIndex()),
                    invoke.getMethodRef().parameterType(
                            capture.argumentIndex()), before);
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.PAUSE_OBSERVATION))));
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RECORD_CALL_ARGUMENT_OUTPUT),
                            StringConstant.v(capture.captureBindingId()),
                            value)));
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RESUME_OBSERVATION))));
            insertBeforeSequence(body, selected, before);
        }
    }

    /** Records a semantic response event at its real normal return. */
    private void instrumentConcolicCommunicationEffects(
            Collection<CommunicationEffectCapture> captures,
            HookCatalog refs) {
        for (CommunicationEffectCapture capture : captures) {
            final SootMethod method;
            try {
                method = Scene.v().getMethod(capture.method());
            } catch (RuntimeException missing) {
                throw new IllegalStateException(
                        "OUTPUT_CAPTURE_RETURN_METHOD_UNAVAILABLE: "
                                + capture.captureBindingId(), missing);
            }
            if (method == null || !method.isConcrete()
                    || method.getReturnType() instanceof VoidType) {
                throw new IllegalStateException(
                        "OUTPUT_CAPTURE_RETURN_METHOD_NOT_CONCRETE: "
                                + capture.captureBindingId());
            }
            Body body = method.retrieveActiveBody();
            int returns = 0;
            for (Unit unit : snapshotUnits(body)) {
                if (!(unit instanceof ReturnStmt)) continue;
                returns++;
                List<Unit> before = new ArrayList<>();
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.PAUSE_OBSERVATION))));
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.RECORD_COMMUNICATION_EFFECT),
                                StringConstant.v(
                                        capture.captureBindingId()))));
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.RESUME_OBSERVATION))));
                insertBeforeSequence(body, unit, before);
            }
            if (returns == 0) {
                throw new IllegalStateException(
                        "OUTPUT_CAPTURE_RETURN_SITE_UNAVAILABLE: "
                                + capture.captureBindingId());
            }
        }
    }





    /**
     * Puts the VM's own handoff at every declared communication site of this
     * campaign.
     *
     * <p>README's "Symbolic propagation is the authority": at a real
     * boundary the sender exports the live expression and the receiver
     * attaches it, after which the receiver's own arithmetic builds on the
     * sender's term and the session ledger holds one {@code VALUE_HANDOFF}
     * edge.  Nothing in this rewrite pairs the two halves; it only puts each
     * half where the port's own declaration says its value crosses.</p>
     *
     * <p>The four sites are the four the static catalog already declares: a
     * request leaves at the cut argument and arrives at the server entry's
     * parameter, and a response leaves at that entry's return and arrives as
     * the cut call's own result.  One site is rewritten once for the whole
     * campaign, however many tasks declare it.</p>
     *
     * <p><b>This pass runs before every other concolic rewrite, and that is
     * load bearing.</b>  A declared receive port is also an input the entry
     * materialization mints a fresh root for, and after a successful attach
     * the receiving local must denote the <em>sender's</em> expression, so
     * the attach has to be the last writer of that local.  The two receive
     * sites reach that from opposite directions: the entry-parameter attach
     * is inserted before the body's first non-identity unit, which is by then
     * this pass's own first unit, so every later entry rewrite lands ahead of
     * it; the cut-return attach is inserted after the cut invoke, so every
     * later rewrite of that unit lands ahead of it too.  Running this pass
     * later would flip exactly one of the two.  The fresh root itself is not
     * removed here: {@code attachCommunicationLeaf} retracts it on success,
     * because a receive the delivery never reached still needs one.</p>
     */
    private void instrumentConcolicCommunicationHandoffs(
            List<InstrumentationPlan> campaign, HookCatalog refs) {
        Map<String, CommunicationHandoffSpec> sites = new LinkedHashMap<>();
        for (InstrumentationPlan plan : campaign) {
            for (CommunicationHandoffSpec site
                    : plan.communicationHandoffs()) {
                sites.putIfAbsent(site.exports() + "\n" + site.portId()
                        + "\n" + site.siteId() + "\n"
                        + site.argumentIndex(), site);
            }
        }
        for (CommunicationHandoffSpec site : sites.values()) {
            // Adapter-carried components already invoke the public VM ABI on
            // their exact storage.  Rewriting the structured parent cut here
            // would export a different value under the component's port id.
            if (site.manualCarrier()) continue;
            SootMethod method;
            try {
                method = Scene.v().getMethod(site.method());
            } catch (RuntimeException missing) {
                throw new IllegalStateException(
                        "COMMUNICATION_HANDOFF_METHOD_UNAVAILABLE: "
                                + site.portId(), missing);
            }
            if (method == null || !method.isConcrete()) {
                throw new IllegalStateException(
                        "COMMUNICATION_HANDOFF_METHOD_NOT_CONCRETE: "
                                + site.portId());
            }
            Body body = method.retrieveActiveBody();
            if (site.exportsCutArgument()) {
                instrumentCutArgumentExport(body, site, refs);
            } else if (site.exportsEntryReturn()) {
                instrumentEntryReturnExport(body, method, site, refs);
            } else if (site.attachesEntryParameter()) {
                instrumentEntryParameterAttach(body, method, site, refs);
            } else if (site.attachesCutReturn()) {
                instrumentCutReturnAttach(body, site, refs);
            }
        }
    }

    /** The unique invoke unit one declared cut site names, or {@code null}. */
    private static Stmt cutInvoke(Body body, CommunicationHandoffSpec site) {
        Stmt selected = null;
        for (Unit unit : snapshotUnits(body)) {
            if (originalUnitIndex(unit) != site.unitIndex()
                    || !(unit instanceof Stmt)) {
                continue;
            }
            Stmt statement = (Stmt) unit;
            if (!statement.containsInvokeExpr()
                    || !site.declaredCallee().equals(statement
                    .getInvokeExpr().getMethodRef().getSignature())) {
                continue;
            }
            if (selected != null) {
                throw new IllegalStateException(
                        "COMMUNICATION_HANDOFF_CUT_NOT_UNIQUE: "
                                + site.portId());
            }
            selected = statement;
        }
        return selected;
    }

    /** {@code Req_out}: exported one instruction ahead of the cut call. */
    private void instrumentCutArgumentExport(
            Body body, CommunicationHandoffSpec site, HookCatalog refs) {
        Stmt cut = cutInvoke(body, site);
        if (cut == null) return;
        InvokeExpr invoke = cut.getInvokeExpr();
        if (site.argumentIndex() >= invoke.getArgCount()) return;
        List<Unit> before = new ArrayList<>();
        addCommunicationLeafExport(body, invoke.getArg(
                site.argumentIndex()), site, before);
        insertBeforeSequence(body, cut, before);
    }

    /** {@code Resp_out}: exported at the server entry's normal return. */
    private void instrumentEntryReturnExport(
            Body body, SootMethod method, CommunicationHandoffSpec site,
            HookCatalog refs) {
        if (method.getReturnType() instanceof VoidType) return;
        for (Unit unit : snapshotUnits(body)) {
            if (!(unit instanceof ReturnStmt)) continue;
            List<Unit> before = new ArrayList<>();
            if (site.responsePathCarrier()) {
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                communicationFieldPathRef(
                                        "exportCommunicationFieldPath"),
                                StringConstant.v(site.portId()),
                                ((ReturnStmt) unit).getOp())));
            } else {
                addCommunicationLeafExport(body,
                        ((ReturnStmt) unit).getOp(), site, before);
            }
            insertBeforeSequence(body, unit, before);
        }
    }

    /**
     * Presents one value to the broker on a fresh carrier leaf.
     *
     * <p>The store is emitted here, in the application's own frame, and that
     * placement is the whole point: a value's expression propagates into a
     * field only while the executing frame is symbolically tracked, so a
     * carrier filled inside GraphChecker's runtime reaches the broker with no
     * shadow and every export answers
     * {@code RPC_HANDOFF_NOT_SYMBOLIC}.</p>
     */
    private void addCommunicationLeafExport(
            Body body, Value value, CommunicationHandoffSpec site,
            List<Unit> units) {
        String[] leaf = carrierLeaf(value.getType());
        Local carrier = newCarrierLeaf(body, leaf, value, units);
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        communicationLeafRef("exportCommunicationLeaf"),
                        StringConstant.v(site.portId()), carrier,
                        StringConstant.v(leaf[0]),
                        StringConstant.v(leaf[1]))));
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
                                carrierLeafType(leaf[1]), false)),
                immediateValue(body, value, units)));
        return carrier;
    }

    /** Reads one carrier leaf back into the receiving frame's own value. */
    private static Unit readCarrierLeaf(Local carrier, String[] leaf,
                                        Value target) {
        return Jimple.v().newAssignStmt(target,
                Jimple.v().newInstanceFieldRef(carrier,
                        Scene.v().makeFieldRef(carrierClass(), leaf[0],
                                carrierLeafType(leaf[1]), false)));
    }

    /** The carrier field and descriptor one Jimple type crosses on. */
    private static String[] carrierLeaf(Type type) {
        if (type instanceof BooleanType) return new String[]{"z", "Z"};
        if (type instanceof ByteType) return new String[]{"b", "B"};
        if (type instanceof ShortType) return new String[]{"s", "S"};
        if (type instanceof CharType) return new String[]{"c", "C"};
        if (type instanceof IntType) return new String[]{"i", "I"};
        if (type instanceof LongType) return new String[]{"j", "J"};
        if (type instanceof FloatType) return new String[]{"f", "F"};
        if (type instanceof DoubleType) return new String[]{"d", "D"};
        return new String[]{"o", "Ljava/lang/Object;"};
    }

    private static Type carrierLeafType(String descriptor) {
        if ("Z".equals(descriptor)) return BooleanType.v();
        if ("B".equals(descriptor)) return ByteType.v();
        if ("S".equals(descriptor)) return ShortType.v();
        if ("C".equals(descriptor)) return CharType.v();
        if ("I".equals(descriptor)) return IntType.v();
        if ("J".equals(descriptor)) return LongType.v();
        if ("F".equals(descriptor)) return FloatType.v();
        if ("D".equals(descriptor)) return DoubleType.v();
        return RefType.v("java.lang.Object");
    }

    private static final String HANDOFF_LEAF_CARRIER_CLASS =
            CONCOLIC_REGION_RUNTIME_CLASS + "$HandoffLeafCarrier";

    private static SootClass carrierClass() {
        SootClass carrier = Scene.v().getSootClassUnsafe(
                HANDOFF_LEAF_CARRIER_CLASS);
        if (carrier == null) {
            carrier = new SootClass(HANDOFF_LEAF_CARRIER_CLASS,
                    Modifier.PUBLIC);
            carrier.setPhantomClass();
            Scene.v().addClass(carrier);
        }
        return carrier;
    }

    private static SootMethodRef communicationLeafRef(String name) {
        Type string = RefType.v("java.lang.String");
        return Scene.v().makeMethodRef(Scene.v().getSootClass(
                        CONCOLIC_REGION_RUNTIME_CLASS), name,
                Arrays.asList(string, RefType.v("java.lang.Object"), string,
                        string), VoidType.v(), true);
    }

    private static SootMethodRef communicationFieldPathRef(String name) {
        return Scene.v().makeMethodRef(Scene.v().getSootClass(
                        CONCOLIC_REGION_RUNTIME_CLASS), name,
                Arrays.<Type>asList(RefType.v("java.lang.String"),
                        RefType.v("java.lang.Object")),
                VoidType.v(), true);
    }

    /** {@code Req_in}: attached onto the server entry's own parameter. */
    private void instrumentEntryParameterAttach(
            Body body, SootMethod method, CommunicationHandoffSpec site,
            HookCatalog refs) {
        if (site.argumentIndex() >= method.getParameterCount()) return;
        Unit insertionPoint = safeInstrumentationEntry(body, method);
        Value parameter = body.getParameterLocal(site.argumentIndex());
        List<Unit> entry = new ArrayList<>();
        addCommunicationLeafAttach(body, parameter, parameter.getType(),
                site, entry, refs);
        insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);
    }

    /** {@code Resp_in}: attached onto the value the cut call returned. */
    private void instrumentCutReturnAttach(
            Body body, CommunicationHandoffSpec site, HookCatalog refs) {
        Stmt cut = cutInvoke(body, site);
        if (cut == null || !(cut instanceof DefinitionStmt)) return;
        Value returned = ((DefinitionStmt) cut).getLeftOp();
        if (!(returned instanceof Local)) return;
        List<Unit> before = new ArrayList<>();
        before.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        prepareResponseHandoffRef(),
                        StringConstant.v(site.portId()))));
        insertBeforeSequence(body, cut, before);
        List<Unit> after = new ArrayList<>();
        if (site.responsePathCarrier()) {
            after.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            communicationFieldPathRef(
                                    "attachCommunicationFieldPath"),
                            StringConstant.v(site.portId()), returned)));
        } else {
            addCommunicationLeafAttach(body, returned,
                    cut.getInvokeExpr().getMethodRef().returnType(), site,
                    after, refs);
        }
        insertAfterSequence(body, cut, after);
    }

    /** Scheduling-only identity for the request issued by one response cut. */
    private static SootMethodRef prepareResponseHandoffRef() {
        return Scene.v().makeMethodRef(Scene.v().getSootClass(
                        CONCOLIC_REGION_RUNTIME_CLASS),
                "prepareResponseHandoff",
                Collections.<Type>singletonList(
                        RefType.v("java.lang.String")),
                VoidType.v(), true);
    }

    /**
     * Replaces {@code target} with the value the VM attached to it.
     *
     * <p>The read-back is the point: after a successful attach the carrier
     * leaf denotes the sender's expression, so assigning it into the
     * receiving frame's own local is what makes the receiver's later
     * arithmetic build on that term.  A refused attach hands the same
     * concrete value straight back, so the program is unchanged either
     * way.</p>
     *
     * <p>Deliberately not wrapped in the observation pause the evidence hooks
     * use: the boxing, the store and the read-back are exactly the value
     * moves the VM has to see, and {@code can_do_concolic()} is false inside
     * a paused subtree.  The runtime mutes its own bookkeeping around
     * them.</p>
     */
    private void addCommunicationLeafAttach(
            Body body, Value target, Type declaredType,
            CommunicationHandoffSpec site, List<Unit> units,
            HookCatalog refs) {
        Type valueType = target.getType();
        String[] leaf = carrierLeaf(valueType);
        Local carrier = newCarrierLeaf(body, leaf, target, units);
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        communicationLeafRef("attachCommunicationLeaf"),
                        StringConstant.v(site.portId()), carrier,
                        StringConstant.v(leaf[0]),
                        StringConstant.v(leaf[1]))));
        if (valueType instanceof PrimType
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

    /** Captures one exact heap definition at its activation-local site. */
    private void instrumentConcolicExactHeapOutputs(
            Collection<ExactHeapOutputCapture> captures,
            HookCatalog refs) {
        for (ExactHeapOutputCapture capture : captures) {
            final SootMethod method;
            try {
                method = Scene.v().getMethod(capture.method());
            } catch (RuntimeException missing) {
                throw exactHeapCaptureFailure(capture,
                        "DEFINITION_METHOD_UNAVAILABLE", missing);
            }
            if (method == null || !method.isConcrete()) {
                throw exactHeapCaptureFailure(capture,
                        "DEFINITION_METHOD_NOT_CONCRETE", null);
            }
            Body body = method.retrieveActiveBody();
            Stmt selected = null;
            for (Unit unit : snapshotUnits(body)) {
                if (originalUnitIndex(unit) != capture.unitIndex()) continue;
                if (selected != null || !(unit instanceof Stmt)) {
                    throw exactHeapCaptureFailure(capture,
                            "DEFINITION_SITE_NOT_UNIQUE", null);
                }
                selected = (Stmt) unit;
            }
            if (selected == null) {
                throw exactHeapCaptureFailure(capture,
                        "DEFINITION_SITE_UNAVAILABLE", null);
            }
            if (capture.mutationState()) {
                if (capture.definitionInvocationScoped()) {
                    instrumentConcolicMutationMethodEntry(body, capture,
                            refs);
                }
                instrumentConcolicMutationStateOutput(body, selected,
                        capture, refs);
                instrumentConcolicMutationMethodCompletion(body, capture,
                        refs);
            } else if (capture.fieldWriteState()) {
                instrumentConcolicFieldWriteStateOutput(body, selected,
                        capture, refs);
            } else {
                throw exactHeapCaptureFailure(capture,
                        "CAPTURE_KIND_UNSUPPORTED", null);
            }
        }
    }

    /** Starts the bounded mutator ordinal at each definition invocation. */
    private void instrumentConcolicMutationMethodEntry(
            Body body, ExactHeapOutputCapture capture, HookCatalog refs) {
        Unit entry = safeInstrumentationEntry(body, body.getMethod());
        if (entry == null) {
            throw exactHeapCaptureFailure(capture,
                    "DEFINITION_METHOD_ENTRY_UNAVAILABLE", null);
        }
        List<Unit> before = new ArrayList<>();
        before.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.PAUSE_OBSERVATION))));
        before.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(
                                Hook.BEGIN_MUTATION_METHOD_STATE_OUTPUT),
                        StringConstant.v(capture.captureBindingId()))));
        before.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.RESUME_OBSERVATION))));
        insertBeforeSequence(body, entry, before);
    }

    private void instrumentConcolicMutationStateOutput(
            Body body, Stmt selected, ExactHeapOutputCapture capture,
            HookCatalog refs) {
        if (!selected.containsInvokeExpr()
                || !(selected.getInvokeExpr()
                instanceof InstanceInvokeExpr)
                || !capture.declaredCallee().equals(selected
                .getInvokeExpr().getMethodRef().getSignature())) {
            throw exactHeapCaptureFailure(capture,
                    "MUTATOR_CALLSITE_MISMATCH", null);
        }
        Value receiver = ((InstanceInvokeExpr) selected.getInvokeExpr())
                .getBase();
        if (capture.atomicArithmeticMutationState()) {
            List<Unit> before = new ArrayList<>();
            Value atomicReceiver = objectArg(body, receiver, before);
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.PAUSE_OBSERVATION))));
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(
                                    Hook.PREPARE_ATOMIC_MUTATION_STATE_OUTPUT),
                            StringConstant.v(capture.captureBindingId()),
                            atomicReceiver)));
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RESUME_OBSERVATION))));
            insertBeforeSequence(body, selected, before);
        }
        List<Unit> after = new ArrayList<>();
        after.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.PAUSE_OBSERVATION))));
        Value container = objectArg(body, receiver, after);
        after.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.RECORD_MUTATION_STATE_OUTPUT),
                        StringConstant.v(capture.captureBindingId()),
                        container)));
        after.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.RESUME_OBSERVATION))));
        // insertAfter means the hook is reached only after a normal mutator
        // return; exceptional calls never manufacture an output definition.
        insertAfterSequence(body, selected, after);
    }

    /**
     * Flushes a selected mutation receiver only after the definition method
     * has completed all of its writes.  Exceptional exits deliberately have
     * no completion hook and therefore fail output validation closed.
     */
    private void instrumentConcolicMutationMethodCompletion(
            Body body, ExactHeapOutputCapture capture, HookCatalog refs) {
        boolean normalExit = false;
        for (Unit unit : snapshotUnits(body)) {
            if (!(unit instanceof ReturnStmt)
                    && !(unit instanceof ReturnVoidStmt)) {
                continue;
            }
            normalExit = true;
            List<Unit> before = new ArrayList<>();
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.PAUSE_OBSERVATION))));
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(
                                    Hook.RECORD_MUTATION_METHOD_EXIT_STATE_OUTPUT),
                            StringConstant.v(capture.captureBindingId()))));
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RESUME_OBSERVATION))));
            insertBeforeSequence(body, unit, before);
        }
        if (!normalExit) {
            throw exactHeapCaptureFailure(capture,
                    "DEFINITION_METHOD_HAS_NO_NORMAL_EXIT", null);
        }
    }

    private void instrumentConcolicFieldWriteStateOutput(
            Body body, Stmt selected, ExactHeapOutputCapture capture,
            HookCatalog refs) {
        if (!(selected instanceof AssignStmt)
                || !(((AssignStmt) selected).getLeftOp()
                instanceof InstanceFieldRef)) {
            // Name the unit that is actually there.  A mismatch here means
            // the plan's unit index and this body disagree, and which unit
            // the index landed on is the whole evidence for why.
            throw exactHeapCaptureFailure(capture,
                    "FIELD_ASSIGNMENT_MISMATCH at " + capture.method()
                            + "#u" + capture.unitIndex() + " which is \""
                            + selected + "\"", null);
        }
        InstanceFieldRef field = (InstanceFieldRef) ((AssignStmt) selected)
                .getLeftOp();
        String signature = CausynthStaticFacts.declaredFieldSignature(
                field.getFieldRef());
        if (!capture.definitionFieldSignature().equals(signature)) {
            throw exactHeapCaptureFailure(capture,
                    "FIELD_SIGNATURE_MISMATCH", null);
        }
        List<Unit> after = new ArrayList<>();
        Value capturedOwner = field.getBase();
        Value capturedValue = field;
        Unit inactive = null;
        if (capture.nestedFieldWriteState()) {
            if (capture.fieldPath().size() < 2
                    || !(field.getType() instanceof RefType)) {
                throw exactHeapCaptureFailure(capture,
                        "FIELD_PATH_NOT_EXACT", null);
            }
            inactive = Jimple.v().newNopStmt();
            Local current = newTraceLocal(body, field.getType(),
                    "$causynthWrittenCarrier");
            after.add(Jimple.v().newAssignStmt(current,
                    Jimple.v().newStaticInvokeExpr(
                            exitFieldReader(field.getField()).makeRef(),
                            field.getBase())));
            for (int index = 1; index < capture.fieldPath().size(); index++) {
                boolean leaf = index + 1 == capture.fieldPath().size();
                after.add(Jimple.v().newIfStmt(
                        Jimple.v().newEqExpr(current, NullConstant.v()),
                        inactive));
                SootField nested = leaf
                        ? exactInstanceField(current.getType(),
                        capture.fieldPath().get(index),
                        capture.leafFieldSignature())
                        : uniqueInstanceField(current.getType(),
                        capture.fieldPath().get(index));
                if (nested == null || nested.isStatic()
                        || !leaf && !(nested.getType() instanceof RefType)) {
                    throw exactHeapCaptureFailure(capture,
                            "FIELD_PATH_NOT_EXACT", null);
                }
                Type readType = leaf
                        && PrimitiveWrapper.forType(nested.getType()) != null
                        ? RefType.v("java.lang.Object") : nested.getType();
                Local nestedValue = newTraceLocal(body, readType,
                        "$causynthWrittenLeaf");
                after.add(Jimple.v().newAssignStmt(nestedValue,
                        Jimple.v().newStaticInvokeExpr(
                                exitFieldReader(nested).makeRef(), current)));
                capturedOwner = current;
                capturedValue = nestedValue;
                if (!leaf) current = nestedValue;
            }
        }
        after.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.PAUSE_OBSERVATION))));
        Value owner = objectArg(body, capturedOwner, after);
        Value value = boxedCaptureValue(body, capturedValue, after);
        after.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.RECORD_FIELD_WRITE_STATE_OUTPUT),
                        StringConstant.v(capture.captureBindingId()),
                        owner, value)));
        after.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.RESUME_OBSERVATION))));
        if (inactive != null) after.add(inactive);
        insertAfterSequence(body, selected, after);
    }

    private static IllegalStateException exactHeapCaptureFailure(
            ExactHeapOutputCapture capture, String reason,
            RuntimeException cause) {
        String message = "OUTPUT_CAPTURE_" + reason + ": "
                + capture.captureBindingId();
        return cause == null ? new IllegalStateException(message)
                : new IllegalStateException(message, cause);
    }

    /** Records exact heap definitions without enabling the runtime trace. */
    private void instrumentConcolicFieldWrites(
            Set<String> methods,
            ConcolicMaterializationSelection materializations,
            HookCatalog refs) {
        for (String signature : methods) {
            final SootMethod method;
            try {
                method = Scene.v().getMethod(signature);
            } catch (RuntimeException missing) {
                continue;
            }
            if (method == null || !method.isConcrete()) {
                continue;
            }
            Body body = method.retrieveActiveBody();
            List<Unit> originalUnits = snapshotUnits(body);
            Unit safeEntry = safeInstrumentationEntry(body, method);
            boolean instrumentationSafe = !method.isConstructor();
            for (Unit unit : originalUnits) {
                if (!instrumentationSafe) {
                    if (unit != safeEntry) {
                        continue;
                    }
                    instrumentationSafe = true;
                }
                if (!(unit instanceof AssignStmt)) {
                    continue;
                }
                Value left = ((AssignStmt) unit).getLeftOp();
                if (!(left instanceof InstanceFieldRef)) {
                    continue;
                }
                InstanceFieldRef field = (InstanceFieldRef) left;
                if (!materializations.matchesWriteCarrier(
                        field.getFieldRef())) {
                    continue;
                }
                String declaredField =
                        CausynthStaticFacts.declaredFieldSignature(
                                field.getFieldRef());
                // Before the store, not after it.  A shared location is
                // versioned only from the moment it is selected, so a carrier
                // this activation binds after its own write publishes an
                // initial version holding the value the write already left
                // and never the write itself.  The selection is the exact
                // access binding - this store's own base object - so it adds
                // no search, only the one bytecode of ordering that lets the
                // putfield below publish the writer's expression.
                List<Unit> before = new ArrayList<>();
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.PAUSE_OBSERVATION))));
                Value selectionOwner = objectArg(body, field.getBase(),
                        before);
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.SELECT_FIELD_WRITE_CARRIER),
                                selectionOwner,
                                StringConstant.v(declaredField))));
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.RESUME_OBSERVATION))));
                insertBeforeSequence(body, unit, before);

                List<Unit> after = new ArrayList<>();
                after.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.PAUSE_OBSERVATION))));
                Value owner = objectArg(body, field.getBase(), after);
                after.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.RECORD_FIELD_WRITE), owner,
                                StringConstant.v(declaredField))));
                after.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.RESUME_OBSERVATION))));
                insertAfterSequence(body, unit, after);
            }
        }
    }

    /**
     * Wraps only activation-selected accessor invocations with a tiny
     * thread-local runtime context. The exact-call trap covers the invocation
     * instruction alone; its rethrow remains inside any original enclosing
     * try range, preserving the application's handler semantics.
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
            List<Unit> units = snapshotUnits(body);
            tagOriginalUnits(units);
            Stmt selected = null;
            for (Unit unit : units) {
                if (originalUnitIndex(unit) != target.callUnitIndex) {
                    continue;
                }
                if (selected != null || !(unit instanceof Stmt)) {
                    throw new IllegalStateException(
                            "ACCESSOR_CALLSITE_NOT_UNIQUE: "
                                    + target.callSiteId);
                }
                selected = (Stmt) unit;
            }
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
            // materialization inside it.  Opening the context is bookkeeping
            // like every other evidence call: it compares this bridge's own
            // strings and walks its own stack, and an accessor call site sits
            // inside the workload's own fragment, so an unbracketed open
            // states those comparisons as conditions of the fragment that
            // merely called a getter.
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.PAUSE_OBSERVATION))));
            before.add(Jimple.v().newAssignStmt(contextToken,
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.ENTER_ACCESSOR_CALL_CONTEXT),
                            StringConstant.v(target.callerMethod),
                            IntConstant.v(target.callUnitIndex),
                            StringConstant.v(target.callSiteId),
                            StringConstant.v(target.declaredCallee),
                            receiver)));
            // The accessor implementation may live in a platform/JDK class
            // which is deliberately outside Soot's application-class set.
            // Materialize its exact backing field on the selected receiver
            // while the exact-call context is active, before the unmodified
            // getter consumes the field.
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.MATERIALIZE_FIELD),
                            StringConstant.v(target.implementationMethod),
                            IntConstant.v(-1), receiver,
                            StringConstant.v(target.fieldSignature),
                            StringConstant.v(target.fieldName))));
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RESUME_OBSERVATION))));
            insertBeforeSequence(body, selected, before);

            // Closing the context is the same bookkeeping as opening it and
            // carries the same bracket on both edges.  The normal pause is
            // also the trap's exclusive end, so the accessor call itself stays
            // protected while the bracket around its close does not re-enter
            // the handler that would then leave the pause depth raised.
            Unit normalPause = Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.PAUSE_OBSERVATION)));
            Unit normalExit = Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.EXIT_ACCESSOR_CALL_CONTEXT), contextToken));
            Unit normalResume = Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RESUME_OBSERVATION)));
            Unit continuation = Jimple.v().newNopStmt();
            Unit skipHandler = Jimple.v().newGotoStmt(continuation);
            Local caught = newTraceLocal(body,
                    RefType.v("java.lang.Throwable"),
                    "$causynthAccessorThrown");
            Unit handler = Jimple.v().newIdentityStmt(caught,
                    Jimple.v().newCaughtExceptionRef());
            Unit exceptionalPause = Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.PAUSE_OBSERVATION)));
            Unit exceptionalExit = Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.EXIT_ACCESSOR_CALL_CONTEXT), contextToken));
            Unit exceptionalResume = Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RESUME_OBSERVATION)));
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
     * Materializes the campaign envelope's selected sites, and only those.
     *
     * <p>This pass used to walk every application class once per plan row.
     * Its associative-read branch wrapped every {@code Map.get} it passed,
     * selected or not, so an HDFS startup ran the hook on every hash lookup
     * {@code MiniDFSCluster.waitActive()} makes, and the hook's own late
     * "no region is active" return could not repay that.  The envelope is
     * what fixed it: the hook is emitted only where the task named an exact
     * method and unit.</p>
     *
     * <p>What is emitted at such a site is the hook call and the argument
     * copies it needs, and nothing else.  The observation mute belongs to
     * the hook - it takes it after its own region check, so an inactive
     * thread pays no VM call at all - and a bracket here would only put that
     * mute back in front of the check.</p>
     */
    private void instrumentConcolicMaterializations(
            CampaignEnvelope envelope, HookCatalog refs) {
        ConcolicMaterializationSelection selection = envelope.materializations;
        if (selection.isEmpty()) {
            return;
        }
        for (String signature : envelope.methods) {
            final SootMethod method;
            try {
                method = Scene.v().getMethod(signature);
            } catch (RuntimeException missing) {
                continue;
            }
            if (method == null || !method.isConcrete()) {
                continue;
            }
            Body body;
            try {
                body = method.retrieveActiveBody();
            } catch (RuntimeException ignored) {
                continue;
            }
            envelope.scannedBodies++;
            List<Unit> originalUnits = snapshotUnits(body);
            tagOriginalUnits(originalUnits);
            Unit safeEntry = safeInstrumentationEntry(body, method);
            Unit lowerBound = method.isConstructor() ? safeEntry : null;
            if (method.isConstructor() && lowerBound == null) {
                continue;
            }
            boolean instrumentationSafe = lowerBound == null;
            for (Unit unit : originalUnits) {
                if (!instrumentationSafe) {
                    if (unit != lowerBound) {
                        continue;
                    }
                    instrumentationSafe = true;
                }
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
                    if (!selection.matches(method.getSignature(),
                            unitIndex, fieldRef)) {
                        continue;
                    }
                    envelope.fieldMaterializationSites++;
                    if (field instanceof StaticFieldRef) {
                        instrumentConsumedStaticPrimitiveFieldRead(body,
                                method, stmt, unitIndex,
                                (StaticFieldRef) field, refs);
                        continue;
                    }
                    if (!(field instanceof InstanceFieldRef)) {
                        throw new IllegalStateException(
                                "UNKNOWN_FIELD_MATERIALIZATION_UNSUPPORTED: "
                                        + declaredSignature
                                        + " at " + method.getSignature()
                                        + "#u" + unitIndex);
                    }
                    InstanceFieldRef instanceField =
                            (InstanceFieldRef) field;
                    List<Unit> before = new ArrayList<>();
                    before.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.PAUSE_OBSERVATION))));
                    Value owner = objectArg(body, instanceField.getBase(),
                            before);
                    before.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.MATERIALIZE_FIELD),
                                    StringConstant.v(method.getSignature()),
                                    IntConstant.v(unitIndex), owner,
                                    StringConstant.v(declaredSignature),
                                    StringConstant.v(declaredName))));
                    before.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.RESUME_OBSERVATION))));
                    insertBeforeSequence(body, stmt, before);
                }

                InvokeExpr invoke = stmt.containsInvokeExpr()
                        ? stmt.getInvokeExpr() : null;
                // The first gate. This hook takes only the container and
                // the key, so unlike every other materialization it
                // carries no site of its own and cannot be admitted by
                // one at runtime: whatever the plan did not name here is
                // simply not addressable later. It is therefore emitted
                // only where the task named an exact method and unit.
                // A read the plan did not name is a coverage gap with a
                // name, not permission to wrap every Map.get.
                if (associativeReadInvoke(invoke)) {
                    if (!selection.selectedSite(signature, unitIndex)) {
                        envelope.unselectedAssociativeReads++;
                        LOG.debug("{}: {}#u{}",
                                GAP_ASSOCIATIVE_READ_SITE_UNSELECTED,
                                signature, unitIndex);
                    } else {
                        envelope.associativeReadSites++;
                        InstanceInvokeExpr read =
                                (InstanceInvokeExpr) invoke;
                        // No pause/resume bracket: the hook owns its own
                        // mute now, and it takes it only after the
                        // thread-local region check has admitted the call.
                        // Bracketing here would put that mute back in front
                        // of the check, which is what made an inactive hook
                        // pay two reflective calls into the VM gate on every
                        // hash lookup.  Nothing between the argument copies
                        // and the hook needs muting: objectArg never boxes -
                        // it answers NullConstant for a primitive and a
                        // plain Jimple copy for a reference - so the only
                        // observable work here is the hook's own, which it
                        // mutes itself.
                        List<Unit> before = new ArrayList<>();
                        Value container = objectArg(body, read.getBase(),
                                before);
                        Value key = objectArg(body, read.getArg(0),
                                before);
                        before.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(refs.ref(
                                        Hook.MATERIALIZE_ASSOCIATIVE_READ),
                                        container, key)));
                        insertBeforeSequence(body, stmt, before);
                    }
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
                    after.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.PAUSE_OBSERVATION))));
                    after.add(Jimple.v().newAssignStmt(modeled,
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.MATERIALIZE_REFERENCE),
                                    StringConstant.v(method.getSignature()),
                                    IntConstant.v(unitIndex),
                                    StringConstant.v(local.getName()),
                                    local)));
                    after.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.RESUME_OBSERVATION))));
                    after.add(Jimple.v().newAssignStmt(local,
                            Jimple.v().newCastExpr(modeled,
                                    local.getType())));
                } else {
                    addPrimitiveMaterialization(body, method, unitIndex,
                            local, after,
                            refs.ref(Hook.MATERIALIZE_PRIMITIVE),
                            refs.ref(Hook.PAUSE_OBSERVATION),
                            refs.ref(Hook.RESUME_OBSERVATION));
                }
                if (!after.isEmpty()) {
                    insertAfterSequence(body, stmt, after);
                }
            }
        }
    }

    private void instrumentConcolicMethodArguments(
            ConcolicMaterializationSelection selection,
            HookCatalog refs) {
        for (String signature : selection.methodArgumentMethods()) {
            SootMethod method = Scene.v().getMethod(signature);
            if (method == null || !method.isConcrete()) {
                throw new IllegalStateException(
                        "Selected method-argument owner is not concrete: "
                                + signature);
            }
            Body body = method.retrieveActiveBody();
            Unit insertionPoint = safeInstrumentationEntry(body, method);
            if (method.isConstructor() && insertionPoint == null) {
                throw new IllegalStateException(
                        "Selected constructor argument has no safe entry: "
                                + signature);
            }
            List<Unit> entry = new ArrayList<>();
            for (Integer index : selection.methodArguments(signature)) {
                if (index == null || index < 0
                        || index >= method.getParameterCount()) {
                    throw new IllegalStateException(
                            "Selected method argument is out of range: "
                                    + signature + "#param" + index);
                }
                Value parameter = body.getParameterLocal(index);
                Value primitiveValue = primitiveValueString(body,
                        parameter, entry);
                if (PrimitiveWrapper.forType(parameter.getType()) != null) {
                    addPrimitiveMethodArgumentMaterialization(body, parameter,
                            signature, index, primitiveValue, entry,
                            refs.ref(Hook.MATERIALIZE_METHOD_ARGUMENT),
                            refs.ref(Hook.PAUSE_OBSERVATION),
                            refs.ref(Hook.RESUME_OBSERVATION));
                    continue;
                }
                Value objectValue = objectArg(body, parameter, entry);
                Local modeled = newTraceLocal(body,
                        RefType.v("java.lang.Object"),
                        "$causynthMethodArgumentModel");
                entry.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.PAUSE_OBSERVATION))));
                entry.add(Jimple.v().newAssignStmt(modeled,
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.MATERIALIZE_METHOD_ARGUMENT),
                                StringConstant.v(signature),
                                IntConstant.v(index), objectValue,
                                primitiveValue)));
                entry.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.RESUME_OBSERVATION))));
                Value converted = parameter.getType() instanceof RefType
                        && "java.lang.Object".equals(((RefType)
                        parameter.getType()).getClassName())
                        ? modeled : Jimple.v().newCastExpr(modeled,
                        parameter.getType());
                entry.add(Jimple.v().newAssignStmt(parameter, converted));
                entry.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.PAUSE_OBSERVATION))));
                entry.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.SYMBOLIZE_METHOD_ARGUMENT),
                                StringConstant.v(signature),
                                IntConstant.v(index), parameter,
                                primitiveValue)));
                entry.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.RESUME_OBSERVATION))));
            }
            insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);
        }
    }

    private static boolean associativeReadInvoke(InvokeExpr invoke) {
        if (!(invoke instanceof InstanceInvokeExpr)
                || !"get".equals(invoke.getMethodRef().name())
                || invoke.getArgCount() != 1
                || !"java.lang.Object".equals(invoke.getMethodRef()
                .parameterType(0).toString())
                || !"java.lang.Object".equals(invoke.getMethodRef()
                .returnType().toString())) {
            return false;
        }
        Type receiverType = ((InstanceInvokeExpr) invoke).getBase().getType();
        try {
            return Scene.v().getOrMakeFastHierarchy().canStoreType(
                    receiverType, RefType.v("java.util.Map"));
        } catch (RuntimeException incompleteHierarchy) {
            return "java.util.Map".equals(receiverType.toString());
        }
    }

    /**
     * Materializes a primitive {@code getstatic} on the exact local that
     * consumed it.  The static field itself is never overwritten: replay and
     * symbolic state are activation-local, while ordinary execution still
     * performs exactly one real getstatic before the hook runs.
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
            throw new IllegalStateException(
                    "STATIC_FIELD_READ_SHAPE_UNSUPPORTED: "
                            + declaredSignature + " at "
                            + method.getSignature() + "#u" + unitIndex);
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
            throw new IllegalStateException(
                    "STATIC_FIELD_MATERIALIZATION_UNSUPPORTED: "
                            + declaredSignature + " at "
                            + method.getSignature() + "#u" + unitIndex);
        }
        insertAfterSequence(body, stmt, after);
    }

    private void instrumentRegionExitFieldCaptures(
            Body body, Unit exit, Local token, Value rootReceiver,
            String receiverClass,
            Collection<RootedOutputCapture> selection, HookCatalog refs) {
        for (RootedOutputCapture target : selection) {
            if (!(rootReceiver instanceof Local)
                    || target.fieldPath().isEmpty()) {
                throw outputCaptureInstrumentationFailure(target,
                        "EXIT_FIELD_ACCESS_ROOT_UNAVAILABLE");
            }
            List<Unit> before = new ArrayList<>();
            Unit inactive = Jimple.v().newNopStmt();
            before.add(Jimple.v().newIfStmt(
                    Jimple.v().newEqExpr(token, LongConstant.v(0L)),
                    inactive));
            Local current = (Local) rootReceiver;
            if (receiverClass != null && !receiverClass.isEmpty()
                    && current.getType() instanceof RefType
                    && !receiverClass.equals(
                    ((RefType) current.getType()).getClassName())) {
                RefType selectedType = RefType.v(receiverClass);
                Local selectedReceiver = newTraceLocal(body, selectedType,
                        "$causynthExitReceiver");
                before.add(Jimple.v().newAssignStmt(selectedReceiver,
                        Jimple.v().newCastExpr(current, selectedType)));
                current = selectedReceiver;
            }
            Local fieldValue = null;
            Local fieldOwner = null;
            for (int index = 0; index < target.fieldPath().size(); index++) {
                boolean leaf = index + 1 == target.fieldPath().size();
                SootField field = leaf
                        ? exactInstanceField(current.getType(),
                        target.fieldPath().get(index),
                        target.fieldSignature())
                        : uniqueInstanceField(current.getType(),
                        target.fieldPath().get(index));
                if (field == null || field.isStatic()
                        || !leaf && !(field.getType() instanceof RefType)) {
                    throw outputCaptureInstrumentationFailure(target,
                            "EXIT_FIELD_PATH_NOT_EXACT");
                }
                // Output observation must not turn a normal return into an
                // instrumentation NPE when an intermediate carrier is null.
                before.add(Jimple.v().newIfStmt(
                        Jimple.v().newEqExpr(current, NullConstant.v()),
                        inactive));
                Type readType = leaf
                        && PrimitiveWrapper.forType(field.getType()) != null
                        ? RefType.v("java.lang.Object") : field.getType();
                fieldValue = newTraceLocal(body, readType,
                        "$causynthExitField");
                before.add(Jimple.v().newAssignStmt(fieldValue,
                        Jimple.v().newStaticInvokeExpr(
                                exitFieldReader(field).makeRef(), current)));
                if (leaf) {
                    fieldOwner = current;
                } else {
                    current = fieldValue;
                }
            }
            Value value = boxedCaptureValue(body, fieldValue, before);
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.PAUSE_OBSERVATION))));
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RECORD_REGION_EXIT_FIELD_OUTPUT),
                            StringConstant.v(target.captureBindingId()),
                            objectArg(body, fieldOwner, before),
                            value)));
            before.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RESUME_OBSERVATION))));
            before.add(inactive);
            insertBeforeSequence(body, exit, before);
        }
    }

    private SootField exactInstanceField(Type ownerType, String name,
                                         String exactSignature) {
        if (!(ownerType instanceof RefType) || name.isEmpty()
                || exactSignature.isEmpty()) {
            return null;
        }
        SootClass owner = ((RefType) ownerType).getSootClass();
        while (owner != null) {
            for (SootField field : owner.getFields()) {
                if (name.equals(field.getName())
                        && exactSignature.equals(field.getSignature())) {
                    return field;
                }
            }
            owner = owner.hasSuperclass() ? owner.getSuperclass() : null;
        }
        return null;
    }

    private SootField uniqueInstanceField(Type ownerType, String name) {
        if (!(ownerType instanceof RefType) || name.isEmpty()) return null;
        SootClass owner = ((RefType) ownerType).getSootClass();
        SootField match = null;
        while (owner != null) {
            for (SootField field : owner.getFields()) {
                if (!field.isStatic() && name.equals(field.getName())) {
                    if (match != null) return null;
                    match = field;
                }
            }
            owner = owner.hasSuperclass() ? owner.getSuperclass() : null;
        }
        return match;
    }

    /**
     * Reads an exit field from code owned by the declaring class.  A raw
     * getfield injected into the region root is illegal when the requested
     * output is private to another class; the tiny bridge preserves the real
     * JVM field read (and therefore its symbolic shadow) without changing the
     * program field's visibility.
     */
    private SootMethod exitFieldReader(SootField field) {
        SootMethod existing = exitFieldReaders.get(field);
        if (existing != null) return existing;

        SootClass owner = field.getDeclaringClass();
        String name = "$causynth$exitRead$" + field.getName() + "$"
                + Integer.toHexString(field.getSignature().hashCode());
        boolean primitive = PrimitiveWrapper.forType(field.getType()) != null;
        Type returnType = primitive ? RefType.v("java.lang.Object")
                : field.getType();
        SootMethod reader = new SootMethod(name,
                Collections.<Type>singletonList(owner.getType()),
                returnType, Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(reader);

        Body bridge = Jimple.v().newBody(reader);
        reader.setActiveBody(bridge);
        Local receiver = Jimple.v().newLocal("$owner", owner.getType());
        Local value = Jimple.v().newLocal("$value", field.getType());
        bridge.getLocals().add(receiver);
        bridge.getLocals().add(value);
        bridge.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newParameterRef(owner.getType(), 0)));
        bridge.getUnits().add(Jimple.v().newAssignStmt(value,
                Jimple.v().newInstanceFieldRef(receiver, field.makeRef())));
        List<Unit> boxing = new ArrayList<>();
        Value result = primitive
                ? boxedCaptureValue(bridge, value, field.getType(), boxing)
                : value;
        bridge.getUnits().addAll(boxing);
        bridge.getUnits().add(Jimple.v().newReturnStmt(result));

        exitFieldReaders.put(field, reader);
        return reader;
    }

    private static IllegalStateException outputCaptureInstrumentationFailure(
            RootedOutputCapture target, String reason) {
        return new IllegalStateException("OUTPUT_CAPTURE_" + reason + ": "
                + target.captureBindingId());
    }

    private static void addPrimitiveMaterialization(
            Body body, SootMethod method, int unitIndex, Local local,
            List<Unit> units,
            SootMethodRef materializePrimitive,
            SootMethodRef pauseObservation,
            SootMethodRef resumeObservation) {
        addPrimitiveRoundTrip(body, local, units, "$causynth",
                pauseObservation, resumeObservation,
                boxed -> Jimple.v().newStaticInvokeExpr(materializePrimitive,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex),
                        StringConstant.v(local.getName()), boxed));
    }

    private static void addPrimitiveArgumentMaterialization(
            Body body, Value parameter, Local token, int argumentIndex,
            Value primitiveValue, List<Unit> units,
            SootMethodRef materializeArgument,
            SootMethodRef pauseObservation,
            SootMethodRef resumeObservation) {
        addPrimitiveRoundTrip(body, parameter, units, "$causynthArgument",
                pauseObservation, resumeObservation,
                boxed -> Jimple.v().newStaticInvokeExpr(materializeArgument,
                        token, IntConstant.v(argumentIndex), boxed,
                        primitiveValue));
    }

    private static void addPrimitiveMethodArgumentMaterialization(
            Body body, Value parameter, String method, int argumentIndex,
            Value primitiveValue, List<Unit> units,
            SootMethodRef materializeArgument,
            SootMethodRef pauseObservation,
            SootMethodRef resumeObservation) {
        addPrimitiveRoundTrip(body, parameter, units,
                "$causynthMethodArgument",
                pauseObservation, resumeObservation,
                boxed -> Jimple.v().newStaticInvokeExpr(materializeArgument,
                        StringConstant.v(method),
                        IntConstant.v(argumentIndex), boxed,
                        primitiveValue));
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
        units.add(Jimple.v().newAssignStmt(boxed,
                Jimple.v().newStaticInvokeExpr(valueOf, primitive)));
        Local materialized = newTraceLocal(body,
                RefType.v("java.lang.Object"), localPrefix + "Materialized");
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(pauseObservation)));
        units.add(Jimple.v().newAssignStmt(materialized,
                materializer.invoke(boxed)));
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(resumeObservation)));
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

    private static int originalUnitIndex(Unit unit) {
        for (Tag tag : unit.getTags()) {
            if (tag instanceof OriginalUnitIndexTag) {
                return ((OriginalUnitIndexTag) tag).index;
            }
        }
        return -1;
    }

    /**
     * Bounds natural-loop body entries rather than eagerly cutting at a
     * latch. A guarded loop may return to its header after body {@code K}; it
     * is cut only if the header chooses the edge into body {@code K+1}. This
     * preserves a normal method exit when a concrete K-element iterator is
     * exhausted exactly at the configured bound.
     */
    int instrumentConcolicLoopBounds(
            Set<String> methods, LoopBoundPolicy policy) {
        return instrumentConcolicLoopBounds(methods, policy,
                Collections.<String>emptySet());
    }

    /**
     * Bounds the loops of one selected method set.
     *
     * <p>Every loop of a method comes from that method's one
     * {@link CfgLoopControl.LoopCfg}, which is also what the static analyzer
     * and the region planner prove iteration guards on.  Cycles a body has
     * only over trap edges are not loops of that model and carry no bound;
     * they are counted and reported under
     * {@link CfgLoopControl#GAP_EXCEPTION_CYCLE_UNBOUNDED}.</p>
     */
    int instrumentConcolicLoopBounds(
            Set<String> methods, LoopBoundPolicy policy,
            Set<String> fixedCountLoopSites) {
        if (policy == null) {
            throw new IllegalArgumentException("loop bound policy is required");
        }
        HookCatalog hooks = HookCatalog.concolic();
        SootMethodRef replayBody = hooks.ref(Hook.CHECK_REPLAY_LOOP_BODY);
        SootMethodRef recordCardinality =
                hooks.ref(Hook.RECORD_LOOP_CARDINALITY);
        SootMethodRef completeCardinality =
                hooks.ref(Hook.COMPLETE_LOOP_CARDINALITY);
        SootMethodRef checkBackedge = hooks.ref(Hook.CHECK_LOOP_BACKEDGE);
        int instrumented = 0;
        int exceptionCycles = 0;
        for (String methodSignature : methods) {
            final SootMethod method;
            try {
                method = Scene.v().getMethod(methodSignature);
            } catch (RuntimeException missing) {
                continue;
            }
            if (method == null || !method.isConcrete()) {
                continue;
            }
            Body body = method.retrieveActiveBody();
            List<Unit> original = snapshotUnits(body);
            tagOriginalUnits(original);
            // One loop-CFG decision per method, taken here and handed to
            // every consumer below: backedge discovery, natural-loop
            // grouping, the continuation-guard search, and the loop-control
            // guards the static analyzer proves.  A trapped method's loops
            // are proved with its trap edges, so a loop containing a caught
            // operation is discovered on exactly the graph it is
            // instrumented from.
            CfgLoopControl.LoopCfg loopCfg =
                    CfgLoopControl.loopCfg(body, new BriefUnitGraph(body));
            exceptionCycles += loopCfg.exceptionCycles();
            List<CfgBackedge> backedges = new ArrayList<>();
            for (Unit source : original) {
                int sourceIndex = originalUnitIndex(source);
                if (sourceIndex < 0) continue;
                for (Unit target : loopCfg.succsOf(source)) {
                    int targetIndex = originalUnitIndex(target);
                    if (targetIndex >= 0
                            && loopCfg.isDominatedBy(source, target)) {
                        backedges.add(new CfgBackedge(source, sourceIndex,
                                target, targetIndex));
                    }
                }
            }

            List<CfgNaturalLoop> loops = groupNaturalLoops(backedges);
            Unit safeEntry = safeInstrumentationEntry(body, method);
            for (CfgNaturalLoop loop : loops) {
                List<CfgEdge> continuations = continuationEdges(
                        body, loopCfg, original, loop);
                String loopId = loop.identity(method);
                boolean fixedCount = naturalLoopHasSite(
                        method, loop, continuations,
                                fixedCountLoopSites);
                Set<Unit> loopMembers = naturalLoopMembers(loopCfg, loop);
                List<CfgEdge> loopExits = fixedCount
                        ? loopExitEdges(loopCfg, loopMembers)
                        : Collections.<CfgEdge>emptyList();
                List<Unit> loopTerminals = fixedCount
                        ? loopTerminalUnits(loopCfg, loopMembers)
                        : Collections.<Unit>emptyList();
                if (fixedCount) {
                    List<Unit> guards = new ArrayList<>();
                    for (CfgEdge edge : loopExits) guards.add(edge.source);
                    AssignStmt authority = CfgLoopControl
                            .arrayLengthAuthority(body, guards);
                    if (authority == null
                            || !(authority.getLeftOp() instanceof Local)) {
                        throw new IllegalStateException(
                                "FIXED_COUNT_LOOP_CARDINALITY_UNADDRESSABLE: "
                                        + loopId);
                    }
                    Unit observation = Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(recordCardinality,
                                    StringConstant.v(loopId),
                                    (Local) authority.getLeftOp()));
                    body.getUnits().insertAfter(observation, authority);
                }
                boolean resourceLoop = fixedCount;
                int loopBodyBound = resourceLoop
                        ? policy.maxBackedgeTraversals()
                        : naturalLoopBodyBound(
                                method, loop, continuations, policy);
                for (CfgBackedge backedge : loop.backedges) {
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
                    List<LoopEdgeHook> edgeHooks = new ArrayList<>();
                    if (resourceLoop) {
                        // One charge per body entered.  The latch hooks exist
                        // to separate a guarded return to the header from the
                        // transfer into the next body; the resource cap counts
                        // bodies, so only the body-entering edge is charged.
                        // It counts them per loop, and so is given the loop.
                        if (!entersBody) continue;
                        edgeHooks.add(new LoopEdgeHook(replayBody, loopId));
                    } else {
                        // This latch executes after one complete body. Cutting
                        // its Kth transfer therefore retains exactly K body
                        // effects even when the selected region is inactive
                        // at the enclosing loop's next header.
                        edgeHooks.add(new LoopEdgeHook(
                                checkBackedge, loopId));
                    }
                    splitCfgEdge(body, method, backedge.source,
                            backedge.target, loopId,
                            loopBodyBound, edgeHooks);
                    instrumented++;
                }
                for (CfgEdge continuation : continuations) {
                    if (!resourceLoop) continue;
                    splitCfgEdge(body, method, continuation.source,
                            continuation.target, loopId,
                            loopBodyBound,
                            Collections.singletonList(new LoopEdgeHook(
                                    replayBody, loopId)));
                    // In bounded mode the return value counts the backedges
                    // this pass split, which a continuation edge is not.  The
                    // resource pass charges bodies, so for it a continuation
                    // is exactly what was instrumented.
                    instrumented++;
                }
                if (fixedCount) {
                    for (CfgEdge exit : loopExits) {
                        splitStringHookEdge(body, method, exit.source,
                                exit.target, loopId, completeCardinality);
                    }
                    for (Unit terminal : loopTerminals) {
                        body.getUnits().insertBefore(
                                Jimple.v().newInvokeStmt(
                                        Jimple.v().newStaticInvokeExpr(
                                                completeCardinality,
                                                StringConstant.v(loopId))),
                                terminal);
                    }
                }
            }
        }
        if (exceptionCycles > 0) {
            // Named, not silent: a cycle that exists only over trap edges
            // carries no iteration bound, because no bound can be installed
            // on an abrupt transfer out of a protected range.
            LOG.warn("{}: {} trap-edge cycle(s) across {} method(s) carry no "
                            + "iteration bound",
                    CfgLoopControl.GAP_EXCEPTION_CYCLE_UNBOUNDED,
                    exceptionCycles, methods.size());
        }
        return instrumented;
    }

    private static boolean naturalLoopHasSite(
            SootMethod method, CfgNaturalLoop loop,
            List<CfgEdge> continuations, Set<String> selectedSites) {
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
            SootMethod method, CfgNaturalLoop loop,
            List<CfgEdge> continuations, LoopBoundPolicy policy) {
        Set<String> controlSites = new LinkedHashSet<>();
        controlSites.addAll(naturalLoopControlSites(
                method, loop, continuations));
        Integer declared = null;
        String declaredSite = "";
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

    private static Set<String> naturalLoopControlSites(
            SootMethod method, CfgNaturalLoop loop,
            List<CfgEdge> continuations) {
        Set<String> controlSites = new LinkedHashSet<>();
        addLoopControlSite(controlSites, method, loop.header);
        for (CfgBackedge backedge : loop.backedges) {
            addLoopControlSite(controlSites, method, backedge.source);
        }
        for (CfgEdge continuation : continuations) {
            addLoopControlSite(controlSites, method, continuation.source);
        }
        return controlSites;
    }

    private static void addLoopControlSite(
            Set<String> sites, SootMethod method, Unit unit) {
        int index = originalUnitIndex(unit);
        if (index >= 0) {
            sites.add(method.getSignature() + "#u" + index);
        }
    }

    private static List<CfgNaturalLoop> groupNaturalLoops(
            List<CfgBackedge> backedges) {
        List<CfgNaturalLoop> loops = new ArrayList<>();
        for (CfgBackedge backedge : backedges) {
            CfgNaturalLoop match = null;
            for (CfgNaturalLoop loop : loops) {
                if (loop.header == backedge.target) {
                    match = loop;
                    break;
                }
            }
            if (match == null) {
                match = new CfgNaturalLoop(backedge.target,
                        backedge.targetIndex);
                loops.add(match);
            }
            match.backedges.add(backedge);
        }
        return loops;
    }

    private static Set<Unit> naturalLoopMembers(
            CfgLoopControl.LoopCfg loopCfg, CfgNaturalLoop loop) {
        Set<Unit> members = Collections.newSetFromMap(
                new IdentityHashMap<Unit, Boolean>());
        for (CfgBackedge backedge : loop.backedges) {
            members.addAll(loopCfg.naturalLoop(loop.header,
                    Collections.singletonList(backedge.source)));
        }
        return members;
    }

    /** Normal transfers ending one dynamic natural-loop invocation. */
    private static List<CfgEdge> loopExitEdges(
            CfgLoopControl.LoopCfg loopCfg, Set<Unit> members) {
        List<CfgEdge> exits = new ArrayList<>();
        for (Unit source : members) {
            for (Unit target : loopCfg.succsOf(source)) {
                if (!members.contains(target)) {
                    exits.add(new CfgEdge(source, target));
                }
            }
        }
        return deduplicateEdges(exits);
    }

    /** Abrupt method terminals inside a loop have no normal exit edge. */
    private static List<Unit> loopTerminalUnits(
            CfgLoopControl.LoopCfg loopCfg, Set<Unit> members) {
        List<Unit> terminals = new ArrayList<>();
        for (Unit unit : members) {
            if (loopCfg.succsOf(unit).isEmpty()
                    && (unit instanceof ReturnStmt
                    || unit instanceof ReturnVoidStmt
                    || unit instanceof ThrowStmt)) {
                terminals.add(unit);
            }
        }
        return terminals;
    }

    private static List<CfgEdge> continuationEdges(
            Body body, CfgLoopControl.LoopCfg loopCfg, List<Unit> original,
            CfgNaturalLoop loop) {
        List<CfgEdge> result = new ArrayList<>();
        for (CfgBackedge backedge : loop.backedges) {
            // CfgLoopControl proves iteration guards per dominance-proved
            // latch.  Keep the instrumentation on that exact same natural
            // loop.  Unioning the members of several latch paths first can
            // pull each path's exit into another path's loop and erase every
            // real guard; a later internal conditional then looks like the
            // only exit and is incorrectly charged as the body entry.
            Set<Unit> members = loopCfg.naturalLoop(loop.header,
                    Collections.singletonList(backedge.source));
            List<CfgEdge> latchEdges = continuationEdgesFrom(
                    body, loop.header, members);
            if (latchEdges.isEmpty()) {
                // The dominance header is often the expression immediately
                // before the IfStmt.  The first exiting branch that dominates
                // this latch is its continuation decision.  A do-while is
                // covered as well: its conditional latch dominates itself.
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

    private static List<CfgEdge> continuationEdgesFrom(
            Body body, Unit candidate, Set<Unit> loopMembers) {
        CausynthBranchShape shape = CausynthBranchShape.from(body, candidate);
        if (shape == null || shape.successorCount() < 2) {
            return Collections.emptyList();
        }
        boolean outside = false;
        List<CfgEdge> inside = new ArrayList<>();
        for (Unit successor : shape.successors) {
            if (loopMembers.contains(successor)) {
                inside.add(new CfgEdge(candidate, successor));
            } else {
                outside = true;
            }
        }
        return outside && !inside.isEmpty()
                ? deduplicateEdges(inside) : Collections.emptyList();
    }

    private static List<CfgEdge> deduplicateEdges(List<CfgEdge> edges) {
        List<CfgEdge> result = new ArrayList<>();
        for (CfgEdge edge : edges) {
            boolean duplicate = false;
            for (CfgEdge retained : result) {
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
            List<CfgEdge> edges, Unit source, Unit target) {
        boolean removed = false;
        for (int index = edges.size() - 1; index >= 0; index--) {
            CfgEdge edge = edges.get(index);
            if (edge.source == source && edge.target == target) {
                edges.remove(index);
                removed = true;
            }
        }
        return removed;
    }

    /** A loop hook and the edge identity that hook is handed. */
    private static final class LoopEdgeHook {
        private final SootMethodRef ref;
        private final String loopId;

        private LoopEdgeHook(SootMethodRef ref, String loopId) {
            this.ref = ref;
            this.loopId = loopId;
        }
    }

    private static void splitCfgEdge(
            Body body, SootMethod method, Unit source, Unit target,
            String loopId, int maxTraversals,
            List<LoopEdgeHook> hookRefs) {
        List<UnitBox> matchingTargets = new ArrayList<>();
        for (UnitBox targetBox : source.getUnitBoxes()) {
            if (targetBox.getUnit() == target) {
                matchingTargets.add(targetBox);
            }
        }
        boolean fallThrough = source.fallsThrough()
                && body.getUnits().getSuccOf(source) == target;
        if (matchingTargets.isEmpty() && !fallThrough) {
            throw new IllegalStateException(
                    "Could not split CFG loop edge " + loopId
                            + " in " + method.getSignature());
        }

        List<Unit> bridge = new ArrayList<>();
        for (LoopEdgeHook hook : hookRefs) {
            bridge.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(hook.ref,
                            StringConstant.v(hook.loopId),
                            IntConstant.v(maxTraversals))));
        }
        Unit first = bridge.get(0);
        Unit transfer = Jimple.v().newGotoStmt(target);
        // Appending keeps the throwing hook outside every pre-existing
        // application trap.  The root's synthetic catch-all is added later
        // and therefore still owns the cut signal.
        for (Unit hook : bridge) body.getUnits().add(hook);
        body.getUnits().add(transfer);
        for (UnitBox targetBox : matchingTargets) {
            targetBox.setUnit(first);
        }
        if (fallThrough) {
            body.getUnits().insertAfter(Jimple.v().newGotoStmt(first),
                    source);
        }
    }

    /** Splits one normal edge with a single-string, non-throwing hook. */
    private static void splitStringHookEdge(
            Body body, SootMethod method, Unit source, Unit target,
            String loopId, SootMethodRef hookRef) {
        List<UnitBox> matchingTargets = new ArrayList<>();
        for (UnitBox targetBox : source.getUnitBoxes()) {
            if (targetBox.getUnit() == target) matchingTargets.add(targetBox);
        }
        boolean fallThrough = source.fallsThrough()
                && body.getUnits().getSuccOf(source) == target;
        if (matchingTargets.isEmpty() && !fallThrough) {
            throw new IllegalStateException(
                    "Could not split CFG loop exit " + loopId
                            + " in " + method.getSignature());
        }
        Unit hook = Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(hookRef,
                        StringConstant.v(loopId)));
        Unit transfer = Jimple.v().newGotoStmt(target);
        body.getUnits().add(hook);
        body.getUnits().add(transfer);
        for (UnitBox targetBox : matchingTargets) targetBox.setUnit(hook);
        if (fallThrough) {
            body.getUnits().insertAfter(Jimple.v().newGotoStmt(hook), source);
        }
    }

    private static final class CfgEdge {
        private final Unit source;
        private final Unit target;

        private CfgEdge(Unit source, Unit target) {
            this.source = source;
            this.target = target;
        }
    }

    private static final class CfgNaturalLoop {
        private final Unit header;
        private final int headerIndex;
        private final List<CfgBackedge> backedges = new ArrayList<>();

        private CfgNaturalLoop(Unit header, int headerIndex) {
            this.header = header;
            this.headerIndex = headerIndex;
        }

        private String identity(SootMethod method) {
            return method.getSignature() + "#loop:u" + headerIndex;
        }
    }

    private static final class CfgBackedge {
        private final Unit source;
        private final int sourceIndex;
        private final Unit target;
        private final int targetIndex;

        private CfgBackedge(Unit source, int sourceIndex,
                            Unit target, int targetIndex) {
            this.source = source;
            this.sourceIndex = sourceIndex;
            this.target = target;
            this.targetIndex = targetIndex;
        }

        private String identity(SootMethod method) {
            return method.getSignature() + "#backedge:u" + sourceIndex
                    + "->u" + targetIndex;
        }
    }

    private void instrumentConcolicBranches(
            ConcolicBranchSelection selection, HookCatalog refs) {
        for (String methodSignature : selection.methods()) {
            try {
                SootMethod method = Scene.v().getMethod(methodSignature);
                if (method == null || !method.isConcrete()) {
                    continue;
                }
                Body body = method.retrieveActiveBody();
                Unit safeEntry = safeInstrumentationEntry(body, method);
                for (Integer unitIndex : selection.units(methodSignature)) {
                    Unit unit = originalUnit(body, unitIndex);
                    if (method.isConstructor()
                            && (safeEntry == null
                            || !unitAtOrAfter(body, safeEntry, unit))) {
                        throw new IllegalStateException(
                                "CONCOLIC_BRANCH_BEFORE_CONSTRUCTOR_"
                                        + "INITIALIZATION: "
                                        + methodSignature + "#u" + unitIndex);
                    }
                    if (unit instanceof IfStmt) {
                        instrumentConcolicBranch(body, method,
                                (IfStmt) unit, unitIndex, refs);
                    } else if (unit instanceof SwitchStmt) {
                        instrumentConcolicSwitch(body, method,
                                (SwitchStmt) unit, unitIndex, refs);
                    }
                }
            } catch (RuntimeException exception) {
                LOG.debug("Skipping concolic branch instrumentation for {}",
                        methodSignature, exception);
            }
        }
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

        List<Unit> falsePath = new ArrayList<>();
        falsePath.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.PAUSE_OBSERVATION))));
        falsePath.add(Jimple.v().newAssignStmt(decision,
                Jimple.v().newStaticInvokeExpr(refs.ref(Hook.RESOLVE_BRANCH),
                        prepared, vmEvent,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex), StringConstant.v(expression),
                        IntConstant.v(0))));
        falsePath.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.RESUME_OBSERVATION))));
        falsePath.add(Jimple.v().newIfStmt(
                Jimple.v().newNeExpr(decision, IntConstant.v(0)),
                previousTarget));
        insertAfterSequence(body, branch, falsePath);

        Unit trueEntry = Jimple.v().newNopStmt();
        Unit truePause = Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.PAUSE_OBSERVATION)));
        Unit trueResolve = Jimple.v().newAssignStmt(decision,
                Jimple.v().newStaticInvokeExpr(refs.ref(Hook.RESOLVE_BRANCH),
                        prepared, vmEvent,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex), StringConstant.v(expression),
                        IntConstant.v(1)));
        Unit trueResume = Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.RESUME_OBSERVATION)));
        Unit takeTrue = Jimple.v().newIfStmt(
                Jimple.v().newNeExpr(decision, IntConstant.v(0)),
                previousTarget);
        Unit takeFalse = Jimple.v().newGotoStmt(falseSuccessor);
        body.getUnits().add(trueEntry);
        body.getUnits().add(truePause);
        body.getUnits().add(trueResolve);
        body.getUnits().add(trueResume);
        body.getUnits().add(takeTrue);
        body.getUnits().add(takeFalse);
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
            body.getUnits().add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.PAUSE_OBSERVATION))));
            body.getUnits().add(Jimple.v().newAssignStmt(effectiveSuccessor,
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RESOLVE_SWITCH_BRANCH),
                            prepared, vmEvent,
                            StringConstant.v(method.getSignature()),
                            IntConstant.v(unitIndex),
                            StringConstant.v(expression),
                            StringConstant.v(shape.kind),
                            StringConstant.v(encodedKeys),
                            IntConstant.v(observed))));
            body.getUnits().add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RESUME_OBSERVATION))));
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
        for (int successorIndex = 0;
             successorIndex < shape.successorCount(); successorIndex++) {
            if (successorIndex == shape.defaultSuccessorIndex) {
                branch.setDefaultTarget(entries.get(successorIndex));
            } else {
                branch.setTarget(successorIndex,
                        entries.get(successorIndex));
            }
        }
    }

    private void insertExactBranchMarkerPrefix(
            Body body, SootMethod method, Unit branch, int unitIndex,
            String expression, Local prepared, Local vmEvent,
            Local vmOccurrence, HookCatalog refs) {
        // Keep the native marker as the final invocation before the original
        // branch. Runtime bookkeeping could otherwise consume its pending VM
        // event. A zero handle follows the concrete replay path.
        Unit noMarkerPath = Jimple.v().newNopStmt();
        List<Unit> beforeBranch = new ArrayList<>();
        beforeBranch.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.PAUSE_VM_PATH_CONDITION))));
        beforeBranch.add(Jimple.v().newAssignStmt(prepared,
                Jimple.v().newStaticInvokeExpr(refs.ref(Hook.PREPARE_BRANCH),
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex),
                        StringConstant.v(expression))));
        beforeBranch.add(Jimple.v().newAssignStmt(vmEvent,
                LongConstant.v(0L)));
        beforeBranch.add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(prepared, LongConstant.v(0L)),
                noMarkerPath));
        beforeBranch.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.RESUME_VM_PATH_CONDITION))));
        beforeBranch.add(Jimple.v().newAssignStmt(vmOccurrence,
                Jimple.v().newCastExpr(prepared, IntType.v())));
        beforeBranch.add(Jimple.v().newAssignStmt(vmEvent,
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.MARK_CONCOLIC_BRANCH),
                        StringConstant.v(method.getSignature() + "#u"
                                + unitIndex), vmOccurrence)));
        Unit exactTransfer = Jimple.v().newGotoStmt(branch);
        beforeBranch.add(exactTransfer);
        beforeBranch.add(noMarkerPath);
        beforeBranch.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.RESUME_VM_PATH_CONDITION))));
        insertBeforeSequence(body, branch, beforeBranch);
        // Insertion redirects old targets to the prefix. Restore this helper's
        // internal transfer so it reaches the original branch exactly once.
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
        // untagged unit belongs to instrumentation inserted by that or a
        // later pass.  Positional fallback would then be unsound: it could
        // attach a concolic hook to a trace-recorder call which merely shifted
        // into the requested slot.
        if (hasAuthoritativeOriginalTags) {
            return null;
        }
        return requestedIndex >= 0 && requestedIndex < current.size()
                ? current.get(requestedIndex) : null;
    }

    private void insertRegionExit(Body body, Stmt returnUnit, Value returnValue,
                                  String taskId, String rootMethod,
                                  SootMethodRef exitRef,
                                  SootMethodRef pauseObservation,
                                  SootMethodRef resumeObservation) {
        List<Unit> units = new ArrayList<>();
        // The fresh wrapper constructor must execute before observation is
        // paused so the interpreter's putfield shadow propagation can attach
        // the primitive expression without using a cached wrapper singleton.
        Value objectValue = boxedCaptureValue(body, returnValue, units);
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(pauseObservation)));
        Value primitiveValue = primitiveValueString(body, returnValue, units);
        units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                exitRef, StringConstant.v(taskId),
                StringConstant.v(rootMethod), objectValue,
                primitiveValue)));
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(resumeObservation)));
        insertBeforeSequence(body, returnUnit, units);
    }

    private static List<Unit> snapshotUnits(Body body) {
        List<Unit> units = new ArrayList<>();
        for (Unit unit : body.getUnits()) {
            units.add(unit);
        }
        return units;
    }

    private static void tagOriginalUnits(List<Unit> units) {
        // Trace and concolic instrumentation may run in the same transform.
        // The first pass tags the complete pre-instrumentation snapshot.  If
        // a later pass sees any such tag, every untagged unit is necessarily
        // synthetic and must stay outside the original-index namespace.
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

    private static Set<String> traceSkipClasses() {
        String configured = firstNonBlank(
                System.getProperty("causynth.trace.skip.classes"),
                System.getenv("CAUSYNTH_TRACE_SKIP_CLASSES"),
                System.getProperty("causynth.trace.summary.classes"),
                System.getenv("CAUSYNTH_TRACE_SUMMARY_CLASSES"), "");
        Set<String> result = new LinkedHashSet<>();
        if (configured == null) {
            return result;
        }
        for (String value : configured.split("[,\\s]+")) {
            if (!value.isEmpty()) {
                result.add(value);
            }
        }
        return result;
    }

    private static boolean isTraceSkippedClass(
            String className, Set<String> skippedClasses) {
        for (String skippedClass : skippedClasses) {
            if (className.equals(skippedClass)
                    || className.startsWith(skippedClass + "$")) {
                return true;
            }
        }
        return false;
    }

    /**
     * Wraps one method in a balanced skeleton envelope.
     *
     * <p>{@code recordExceptionalExit} selects which exceptional-exit hook the
     * catch-all handler calls. Both hooks pop the same thread-local
     * activation and close the same call sites; they differ only in whether
     * the pop is also written to the trace, so turning it on for a method does
     * not change how that method's envelope nests.</p>
     */
    private Local instrumentLiteMethod(
            Body body, SootMethod method, List<Unit> originalUnits,
            Unit insertionPoint, Unit lowerBound, Value receiver,
            HookCatalog refs, boolean recordExceptionalExit) {
        Local callId = newTraceLocal(body, LongType.v(),
                "$causynthLiteCallId");
        List<Unit> entry = new ArrayList<>();
        entry.add(Jimple.v().newAssignStmt(callId, LongConstant.v(0L)));
        entry.add(Jimple.v().newAssignStmt(callId,
                Jimple.v().newStaticInvokeExpr(
                        refs.ref(Hook.ENTER_METHOD_LITE),
                        StringConstant.v(method.getSignature()), receiver)));
        insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);

        boolean instrumentationSafe = lowerBound == null;
        for (Unit unit : originalUnits) {
            if (!instrumentationSafe) {
                if (unit != lowerBound) {
                    continue;
                }
                instrumentationSafe = true;
            }
            if (unit instanceof ReturnStmt
                    || unit instanceof ReturnVoidStmt) {
                Stmt exit = Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.EXIT_ACTIVE_METHOD_LITE)));
                body.getUnits().insertBefore(exit, unit);
            }
        }
        addActiveThrowHandler(body, insertionPoint,
                refs.ref(recordExceptionalExit
                        ? Hook.THROW_ACTIVE_METHOD
                        : Hook.THROW_ACTIVE_METHOD_LITE));
        return callId;
    }

    private void instrumentRichMethod(
            Body body, SootMethod method, List<Unit> originalUnits,
            Unit insertionPoint, Unit lowerBound, Value receiver,
            TraceSelection sites,
            HookCatalog refs) {
        Local callId = newTraceLocal(body, LongType.v(), "$causynthCallId");
        List<Unit> entryUnits = new ArrayList<>();
        // Keep the initialization as a defensive verifier-visible value.  The
        // whole entry probe is inserted without redirecting existing trap
        // boundaries: an original catch/finally must not observe a partially
        // executed probe or synthetic locals that did not exist in the input.
        entryUnits.add(Jimple.v().newAssignStmt(callId, LongConstant.v(0L)));
        entryUnits.add(Jimple.v().newAssignStmt(callId,
                Jimple.v().newStaticInvokeExpr(refs.ref(Hook.ENTER_METHOD),
                        StringConstant.v(method.getSignature()), receiver)));
        for (int index = 0; index < method.getParameterCount(); index++) {
            Value parameter;
            try {
                parameter = body.getParameterLocal(index);
            } catch (RuntimeException ignored) {
                continue;
            }
            Value objectValue = objectArg(body, parameter, entryUnits);
            Value primitiveValue = primitiveValueString(body, parameter, entryUnits);
            entryUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                    refs.ref(Hook.RECORD_METHOD_ARGUMENT),
                    callId,
                    IntConstant.v(index),
                    StringConstant.v(method.getParameterType(index).toString()),
                    objectValue,
                    primitiveValue)));
        }
        insertBeforeOrAppendNoRedirect(body, insertionPoint, entryUnits);

        Set<Integer> callUnits = sites.units(sites.callUnits,
                method.getSignature());
        Set<Integer> branchUnits = sites.units(sites.branchUnits,
                method.getSignature());
        boolean instrumentationSafe = lowerBound == null;
        for (int unitIndex = 0; unitIndex < originalUnits.size(); unitIndex++) {
            Unit unit = originalUnits.get(unitIndex);
            if (!instrumentationSafe) {
                if (unit != lowerBound) {
                    continue;
                }
                instrumentationSafe = true;
            }
            if (!(unit instanceof Stmt)) {
                continue;
            }
            Stmt stmt = (Stmt) unit;
            if ((sites.allSites || callUnits.contains(unitIndex))
                    && stmt.containsInvokeExpr()
                    && !isRecorderInvoke(stmt.getInvokeExpr())) {
                instrumentCallSite(body, method, stmt, unitIndex, callId,
                        refs);
            }
            if (sites.allSites || branchUnits.contains(unitIndex)) {
                if (stmt instanceof IfStmt) {
                    instrumentBranch(body, method, (IfStmt) stmt, unitIndex,
                            callId, refs);
                } else if (stmt instanceof SwitchStmt) {
                    instrumentSwitchBranch(body, method,
                            (SwitchStmt) stmt, unitIndex, callId, refs);
                }
            }
            if (stmt instanceof ReturnStmt) {
                insertMethodExit(body, stmt, ((ReturnStmt) stmt).getOp(),
                        refs.ref(Hook.EXIT_ACTIVE_METHOD));
            } else if (stmt instanceof ReturnVoidStmt) {
                insertMethodExit(body, stmt, NullConstant.v(),
                        refs.ref(Hook.EXIT_ACTIVE_METHOD));
            }
        }
        addActiveThrowHandler(body, insertionPoint,
                refs.ref(Hook.THROW_ACTIVE_METHOD));
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
        before.add(Jimple.v().newAssignStmt(invocationId,
                Jimple.v().newStaticInvokeExpr(refs.ref(Hook.BEGIN_CALL),
                        ownerCallId,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex),
                        StringConstant.v(invoke.getMethodRef().getSignature()),
                        receiver)));
        for (int index = 0; index < invoke.getArgCount(); index++) {
            Value argument = invoke.getArg(index);
            Value objectValue = objectArg(body, argument, before);
            Value primitiveValue = primitiveValueString(body, argument, before);
            Type declaredType = index < invoke.getMethodRef().parameterTypes().size()
                    ? invoke.getMethodRef().parameterType(index) : argument.getType();
            before.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                    refs.ref(Hook.RECORD_CALL_ARGUMENT),
                    invocationId,
                    IntConstant.v(index),
                    StringConstant.v(declaredType.toString()),
                    objectValue,
                    primitiveValue)));
        }
        insertBeforeSequence(body, stmt, before);

        Value returnValue = runtimeCallSiteReturnValue(stmt, invoke);
        List<Unit> after = new ArrayList<>();
        Value returnObject = objectArg(body, returnValue, after);
        Value primitiveReturn = primitiveValueString(body, returnValue, after);
        after.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.ref(Hook.END_CALL), invocationId, returnObject,
                primitiveReturn)));
        insertAfterSequence(body, stmt, after);
    }

    /**
     * Returns the object on which an ordinary instance call is dispatched.
     * This must come from the invoke expression itself, rather than from the
     * enclosing method's {@code this} local: an interface call may dispatch
     * on a receiver owned by a different caller object.
     *
     * <p>Constructor receivers remain excluded because passing an
     * uninitialized object to a recorder call before {@code <init>} would
     * violate JVM verification rules.</p>
     */
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

    /**
     * Static worklist admission is not receiver-type evidence.  Until an
     * exact runtime call-site observation is unique, retain every
     * class-hierarchy candidate and let activation binding distinguish the
     * concrete executions.
     */
    static List<String> conservativeDispatchTargets(List<String> targets) {
        return targets == null ? Collections.<String>emptyList()
                : new ArrayList<>(targets);
    }

    private void instrumentBranch(Body body, SootMethod method, IfStmt branch,
                                  int unitIndex, Local callId,
                                  HookCatalog refs) {
        String expression = branch.getCondition().toString();
        Unit originalTarget = branch.getTarget();
        List<Unit> falsePath = new ArrayList<>();
        Unit falseRecord = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.ref(Hook.RECORD_BRANCH),
                callId,
                StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex),
                StringConstant.v(expression),
                IntConstant.v(0)));
        falsePath.add(falseRecord);
        insertAfterSequence(body, branch, falsePath);

        Unit trueEntry = Jimple.v().newNopStmt();
        List<Unit> truePath = new ArrayList<>();
        truePath.add(trueEntry);
        Unit trueRecord = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.ref(Hook.RECORD_BRANCH),
                callId,
                StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex),
                StringConstant.v(expression),
                IntConstant.v(1)));
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
            path.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.RECORD_SWITCH_BRANCH),
                            callId,
                            StringConstant.v(method.getSignature()),
                            IntConstant.v(unitIndex),
                            StringConstant.v(expression),
                            IntConstant.v(successorIndex),
                            StringConstant.v(shape.kind),
                            StringConstant.v(keys))));
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
        units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                exitRef, objectValue, primitiveValue)));
        insertBeforeSequence(body, returnUnit, units);
    }

    /**
     * Appends a method-wide catch-all that reports the exceptional exit and
     * rethrows.
     *
     * <p>The trap is appended, never prepended, and the order is the whole
     * correctness argument for a throw inside {@code synchronized}. javac
     * compiles a synchronized statement into an inner {@code any} handler that
     * releases the monitor and rethrows; the JVM takes the first exception
     * table entry whose range covers the throw, so an appended catch-all lets
     * that inner handler run first and then catches its rethrow, which is
     * still inside the appended range. Prepending would preempt the monitor
     * release and leak the lock.</p>
     */
    private void addActiveThrowHandler(Body body, Unit start,
                                       SootMethodRef throwRef) {
        if (start == null) {
            return;
        }
        SootClass throwableClass = Scene.v().getSootClass("java.lang.Throwable");
        Local caught = newTraceLocal(body, RefType.v("java.lang.Throwable"),
                "$causynthThrown");
        Unit handler = Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef());
        Unit record = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                throwRef, caught));
        Unit rethrow = Jimple.v().newThrowStmt(caught);
        body.getUnits().add(handler);
        body.getUnits().add(record);
        body.getUnits().add(rethrow);
        Trap trap = Jimple.v().newTrap(throwableClass, start, handler, handler);
        body.getTraps().add(trap);
    }

    /**
     * Adds an invocation-exact catch-all whose incoming verifier frame reads
     * only the caught throwable.  Root ownership is resolved by the runtime's
     * frame stack from a verifier-independent string constant.
     */
    private void addRegionThrowHandler(Body body, Unit start,
                                       String taskId, String rootMethod,
                                       SootMethodRef throwRef,
                                       SootMethodRef pauseObservation,
                                       SootMethodRef resumeObservation) {
        if (start == null) {
            return;
        }
        SootClass throwableClass = Scene.v().getSootClass("java.lang.Throwable");
        Local caught = newTraceLocal(body, RefType.v("java.lang.Throwable"),
                "$causynthRegionThrown");
        Unit handler = Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef());
        Unit pause = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                pauseObservation));
        Unit record = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                throwRef, StringConstant.v(taskId),
                StringConstant.v(rootMethod), caught));
        Unit resume = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                resumeObservation));
        Unit rethrow = Jimple.v().newThrowStmt(caught);
        body.getUnits().add(handler);
        body.getUnits().add(pause);
        body.getUnits().add(record);
        body.getUnits().add(resume);
        body.getUnits().add(rethrow);
        body.getTraps().add(Jimple.v().newTrap(throwableClass, start, handler,
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
                                      TraceSelection traceFields,
                                      List<Unit> units,
                                      Unit lowerBound) {
        Value methodReceiver = NullConstant.v();
        if (!method.isStatic()) {
            try {
                Local thisLocal = body.getThisLocal();
                if (thisLocal != null) {
                    methodReceiver = thisLocal;
                }
            } catch (RuntimeException ignored) {
            }
        }
        boolean instrumentationSafe = lowerBound == null;
        for (int unitIndex = 0; unitIndex < units.size(); unitIndex++) {
            Unit unit = units.get(unitIndex);
            if (!instrumentationSafe) {
                if (unit != lowerBound) {
                    continue;
                }
                instrumentationSafe = true;
            }
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
                            methodReceiver, right, true, traceFields);
                }
                if (right instanceof FieldRef) {
                    insertFieldTrace(body, unit, recordFieldRef, "FIELD_READ",
                            method.getSignature(), unitIndex, (FieldRef) right,
                            methodReceiver, left, true, traceFields);
                }
            } else {
                for (ValueBox box : stmt.getUseBoxes()) {
                    Value value = box.getValue();
                    if (value instanceof FieldRef) {
                        insertFieldTrace(body, unit, recordFieldRef, "FIELD_READ",
                                method.getSignature(), unitIndex, (FieldRef) value,
                                methodReceiver, value, false, traceFields);
                    }
                }
            }
        }
    }

    /** Records only reference-array aaload/aastore identities. */
    private void instrumentReferenceArrayTrace(
            Body body, SootMethod method, SootMethodRef recordArrayRef,
            List<Unit> units, Unit lowerBound) {
        boolean instrumentationSafe = lowerBound == null;
        for (int unitIndex = 0; unitIndex < units.size(); unitIndex++) {
            Unit unit = units.get(unitIndex);
            if (!instrumentationSafe) {
                if (unit != lowerBound) continue;
                instrumentationSafe = true;
            }
            if (!(unit instanceof AssignStmt)) continue;
            AssignStmt assign = (AssignStmt) unit;
            Value left = assign.getLeftOp();
            Value right = assign.getRightOp();
            if (left instanceof ArrayRef
                    && referenceArrayElement((ArrayRef) left)) {
                insertArrayTrace(body, unit, recordArrayRef, "ARRAY_WRITE",
                        method.getSignature(), unitIndex, (ArrayRef) left,
                        right);
            }
            if (right instanceof ArrayRef
                    && referenceArrayElement((ArrayRef) right)) {
                insertArrayTrace(body, unit, recordArrayRef, "ARRAY_READ",
                        method.getSignature(), unitIndex, (ArrayRef) right,
                        left);
            }
        }
    }

    private static boolean referenceArrayElement(ArrayRef array) {
        Type element = array == null ? null : array.getType();
        return element instanceof RefType || element instanceof ArrayType;
    }

    private static void insertArrayTrace(
            Body body, Unit unit, SootMethodRef recordArrayRef, String kind,
            String method, int unitIndex, ArrayRef array, Value element) {
        List<Unit> suffix = new ArrayList<>();
        Value arrayObject = objectArg(body, array.getBase(), suffix);
        Value index = immediateValue(body, array.getIndex(), suffix);
        Value elementObject = objectArg(body, element, suffix);
        suffix.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                recordArrayRef,
                StringConstant.v(kind),
                StringConstant.v(method),
                IntConstant.v(unitIndex),
                arrayObject,
                index,
                elementObject)));
        insertAfterSequence(body, unit, suffix);
    }

    private void insertFieldTrace(
            Body body, Unit unit, SootMethodRef recordFieldRef,
            String kind, String method, int unitIndex,
            FieldRef fieldRef, Value methodReceiverValue, Value value,
            boolean fieldValueIsReadValue,
            TraceSelection traceFields) {
        String field = CausynthStaticFacts.declaredFieldSignature(
                fieldRef.getFieldRef());
        if (!shouldInstrumentField(field, traceFields)) {
            return;
        }
        List<Unit> prefixUnits = new ArrayList<>();
        Value methodReceiver = objectArg(body, methodReceiverValue, prefixUnits);
        // A static field has no Java receiver object.  Its interned canonical
        // signature is a process-local class-state identity token: all
        // getstatic/putstatic hooks for that exact declaration observe the
        // same non-null object while unrelated static fields cannot alias it.
        Value receiverValue = fieldRef instanceof InstanceFieldRef
                ? ((InstanceFieldRef) fieldRef).getBase()
                : StringConstant.v(field);
        Value receiver = objectArg(body, receiverValue, prefixUnits);
        Value valueObject = objectArg(body, value, prefixUnits);
        Value primitiveValue = primitiveValueString(body, value, prefixUnits);
        Stmt traceCall = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                recordFieldRef,
                StringConstant.v(kind),
                StringConstant.v(method),
                IntConstant.v(unitIndex),
                StringConstant.v(field),
                methodReceiver,
                receiver,
                valueObject,
                primitiveValue));
        prefixUnits.add(traceCall);
        if (fieldValueIsReadValue || "FIELD_WRITE".equals(kind)) {
            insertAfterSequence(body, unit, prefixUnits);
        } else {
            insertBeforeSequence(body, unit, prefixUnits);
        }
    }

    private static boolean shouldInstrumentField(String field,
                                                 TraceSelection traceFields) {
        return field != null && traceFields != null
                && traceFields.allFields;
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

    /** Returns the exact assigned value as an Object, boxing primitives. */
    private static Value boxedCaptureValue(Body body, Value value,
                                           List<Unit> prefixUnits) {
        return boxedCaptureValue(body, value,
                value == null ? null : value.getType(), prefixUnits);
    }

    /**
     * Returns the exact value as an Object using {@code declaredType} as the
     * primitive boxing authority.  JVM int-like locals share the same operand
     * representation, so a Soot-narrowed byte/short/char local can be passed
     * directly to an {@code Integer(int)} constructor without introducing a
     * second value computation or losing its VM shadow.
     */
    private static Value boxedCaptureValue(Body body, Value value,
                                           Type declaredType,
                                           List<Unit> prefixUnits) {
        if (value == null || value instanceof NullConstant) {
            return NullConstant.v();
        }
        if (value.getType() instanceof RefType
                || value.getType() instanceof ArrayType) {
            return immediateValue(body, value, prefixUnits);
        }
        Type boxingType = declaredType == null
                ? value.getType() : declaredType;
        PrimitiveWrapper wrapper = PrimitiveWrapper.forType(boxingType);
        if (wrapper == null) return NullConstant.v();
        SootClass wrapperClass = Scene.v().getSootClass(wrapper.className);
        RefType wrapperType = RefType.v(wrapper.className);
        Value source = immediateValue(body, value, prefixUnits);
        Local boxed = newTraceLocal(body, wrapperType,
                "$causynthCaptureBox");
        prefixUnits.add(Jimple.v().newAssignStmt(boxed,
                Jimple.v().newNewExpr(wrapperType)));
        SootMethodRef constructor = Scene.v().makeMethodRef(wrapperClass,
                "<init>", Collections.singletonList(boxingType),
                VoidType.v(), false);
        prefixUnits.add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(boxed, constructor,
                        source)));
        return boxed;
    }

    private static Value primitiveValueString(Body body, Value value, List<Unit> prefixUnits) {
        if (value == null || value instanceof NullConstant) {
            return StringConstant.v("");
        }
        SootClass stringClass = Scene.v().getSootClass("java.lang.String");
        if (value.getType() instanceof IntType
                || value.getType() instanceof ByteType
                || value.getType() instanceof ShortType
                || value.getType() instanceof CharType) {
            SootMethodRef ref = Scene.v().makeMethodRef(stringClass, "valueOf",
                    Collections.singletonList(IntType.v()), RefType.v("java.lang.String"), true);
            Value numeric = value.getType() instanceof IntType ? value
                    : Jimple.v().newCastExpr(value, IntType.v());
            return primitiveStringLocal(body, numeric, ref, prefixUnits);
        }
        if (value.getType() instanceof BooleanType) {
            SootMethodRef ref = Scene.v().makeMethodRef(stringClass, "valueOf",
                    Collections.singletonList(BooleanType.v()), RefType.v("java.lang.String"), true);
            return primitiveStringLocal(body, value, ref, prefixUnits);
        }
        if (value.getType() instanceof LongType) {
            SootMethodRef ref = Scene.v().makeMethodRef(stringClass, "valueOf",
                    Collections.singletonList(LongType.v()), RefType.v("java.lang.String"), true);
            return primitiveStringLocal(body, value, ref, prefixUnits);
        }
        return StringConstant.v("");
    }

    private static Value primitiveStringLocal(Body body, Value value, SootMethodRef ref,
                                             List<Unit> prefixUnits) {
        Value source = immediateValue(body, value, prefixUnits);
        Local tmp = newTraceLocal(body, RefType.v("java.lang.String"), "$causynthPrim");
        prefixUnits.add(Jimple.v().newAssignStmt(tmp,
                Jimple.v().newStaticInvokeExpr(ref, source)));
        return tmp;
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

    /**
     * Returns the first verifier-safe instrumentation point.  In a
     * constructor, {@code this} remains uninitialized until the mandatory
     * {@code this(...)} or {@code super(...)} special invocation returns and
     * therefore must not be passed to any trace or concolic hook earlier.
     */
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
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
            if (!(invoke instanceof SpecialInvokeExpr)
                    || !"<init>".equals(invoke.getMethodRef().name())) {
                continue;
            }
            Value base = ((SpecialInvokeExpr) invoke).getBase();
            if (base == thisLocal || base.equivTo(thisLocal)) {
                return body.getUnits().getSuccOf(unit);
            }
        }
        return null;
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

    private static SootMethodRef traceRecorderFieldMethodRef() {
        SootClass recorder = Scene.v().getSootClassUnsafe(TRACE_RECORDER_CLASS);
        if (recorder == null) {
            recorder = new SootClass(TRACE_RECORDER_CLASS, Modifier.PUBLIC);
            recorder.setPhantomClass();
            Scene.v().addClass(recorder);
        }
        return Scene.v().makeMethodRef(recorder, "recordField",
                Arrays.asList(
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.String"),
                        IntType.v(),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v(), true);
    }

    private static SootMethodRef traceRecorderArrayMethodRef() {
        SootClass recorder = traceRecorderClass();
        return Scene.v().makeMethodRef(recorder, "recordArrayElement",
                Arrays.asList(
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.String"),
                        IntType.v(),
                        RefType.v("java.lang.Object"),
                        IntType.v(),
                        RefType.v("java.lang.Object")),
                VoidType.v(), true);
    }

    private static SootClass traceRecorderClass() {
        SootClass recorder = Scene.v().getSootClassUnsafe(TRACE_RECORDER_CLASS);
        if (recorder == null) {
            recorder = new SootClass(TRACE_RECORDER_CLASS, Modifier.PUBLIC);
            recorder.setPhantomClass();
            Scene.v().addClass(recorder);
        }
        return recorder;
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
        ENTER_REGION_FRAME,
        ENTER_ACCESSOR_CALL_CONTEXT,
        EXIT_ACCESSOR_CALL_CONTEXT,
        MATERIALIZE_ARGUMENT,
        SYMBOLIZE_ARGUMENT,
        MATERIALIZE_METHOD_ARGUMENT,
        SYMBOLIZE_METHOD_ARGUMENT,
        MATERIALIZE_REFERENCE,
        MATERIALIZE_PRIMITIVE,
        MATERIALIZE_STATIC_PRIMITIVE_FIELD,
        MATERIALIZE_FIELD,
        MATERIALIZE_ASSOCIATIVE_READ,
        SELECT_FIELD_WRITE_CARRIER,
        RECORD_FIELD_WRITE,
        RECORD_REGION_EXIT_FIELD_OUTPUT,
        RECORD_CALL_ARGUMENT_OUTPUT,
        RECORD_COMMUNICATION_EFFECT,
        BEGIN_MUTATION_METHOD_STATE_OUTPUT,
        PREPARE_ATOMIC_MUTATION_STATE_OUTPUT,
        RECORD_MUTATION_STATE_OUTPUT,
        RECORD_MUTATION_METHOD_EXIT_STATE_OUTPUT,
        RECORD_FIELD_WRITE_STATE_OUTPUT,
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
        RECORD_LOOP_CARDINALITY,
        COMPLETE_LOOP_CARDINALITY,
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

        private static HookCatalog trace() {
            SootClass recorder = traceRecorderClass();
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
                            LongType.v(), string, object)
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
                            RefType.v("java.lang.Throwable"));
        }

        private static HookCatalog concolic() {
            SootClass runtime = Scene.v().getSootClassUnsafe(
                    CONCOLIC_REGION_RUNTIME_CLASS);
            if (runtime == null) {
                runtime = new SootClass(CONCOLIC_REGION_RUNTIME_CLASS,
                        Modifier.PUBLIC);
                runtime.setPhantomClass();
                Scene.v().addClass(runtime);
            }
            Type string = RefType.v("java.lang.String");
            Type object = RefType.v("java.lang.Object");
            SootClass system = Scene.v().getSootClassUnsafe(
                    "java.lang.System");
            if (system == null) {
                system = new SootClass("java.lang.System", Modifier.PUBLIC);
                system.setPhantomClass();
                Scene.v().addClass(system);
            }
            return new HookCatalog()
                    .add(Hook.ENTER_REGION_FRAME, runtime, "enterRegionFrame",
                            LongType.v(), string, string, object,
                            ArrayType.v(object, 1))
                    .add(Hook.ENTER_ACCESSOR_CALL_CONTEXT, runtime,
                            "enterAccessorCallContext", LongType.v(), string,
                            IntType.v(), string, string, object)
                    .add(Hook.EXIT_ACCESSOR_CALL_CONTEXT, runtime,
                            "exitAccessorCallContext", VoidType.v(), LongType.v())
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
                    .add(Hook.MATERIALIZE_ASSOCIATIVE_READ, runtime,
                            "materializeAssociativeRead", VoidType.v(),
                            object, object)
                    .add(Hook.SELECT_FIELD_WRITE_CARRIER, runtime,
                            "selectFieldWriteCarrier", VoidType.v(), object,
                            string)
                    .add(Hook.RECORD_FIELD_WRITE, runtime,
                            "recordFieldWrite", VoidType.v(), object, string)
                    .add(Hook.RECORD_REGION_EXIT_FIELD_OUTPUT, runtime,
                            "recordRegionExitFieldOutput", VoidType.v(),
                            string, object, object)
                    .add(Hook.RECORD_CALL_ARGUMENT_OUTPUT, runtime,
                            "recordCallArgumentOutput", VoidType.v(),
                            string, object)
                    .add(Hook.RECORD_COMMUNICATION_EFFECT, runtime,
                            "recordCommunicationEffect", VoidType.v(),
                            string)
                    .add(Hook.BEGIN_MUTATION_METHOD_STATE_OUTPUT, runtime,
                            "beginMutationMethodStateOutput", VoidType.v(),
                            string)
                    .add(Hook.PREPARE_ATOMIC_MUTATION_STATE_OUTPUT, runtime,
                            "prepareAtomicMutationStateOutput",
                            VoidType.v(), string, object)
                    .add(Hook.RECORD_MUTATION_STATE_OUTPUT, runtime,
                            "recordMutationStateOutput", VoidType.v(),
                            string, object)
                    .add(Hook.RECORD_MUTATION_METHOD_EXIT_STATE_OUTPUT,
                            runtime,
                            "recordMutationMethodExitStateOutput",
                            VoidType.v(), string)
                    .add(Hook.RECORD_FIELD_WRITE_STATE_OUTPUT, runtime,
                            "recordFieldWriteStateOutput", VoidType.v(),
                            string, object, object)
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
                    .add(Hook.RECORD_LOOP_CARDINALITY, runtime,
                            "recordLoopCardinality", VoidType.v(), string,
                            IntType.v())
                    .add(Hook.COMPLETE_LOOP_CARDINALITY, runtime,
                            "completeLoopCardinality", VoidType.v(), string)
                    .add(Hook.EXIT_REGION_FRAME, runtime, "exitRegionFrame",
                            VoidType.v(), string, string, object, string)
                    .add(Hook.THROW_REGION_FRAME, runtime, "throwRegionFrame",
                            VoidType.v(), string, string,
                            RefType.v("java.lang.Throwable"));
        }
    }

    /** Wrapper metadata needed to round-trip primitive Jimple locals. */
    private static final class PrimitiveWrapper {
        private final String className;
        private final String unboxMethod;

        private PrimitiveWrapper(String className, String unboxMethod) {
            this.className = className;
            this.unboxMethod = unboxMethod;
        }

        private static PrimitiveWrapper forType(Type type) {
            if (type instanceof BooleanType) {
                return new PrimitiveWrapper("java.lang.Boolean", "booleanValue");
            }
            if (type instanceof ByteType) {
                return new PrimitiveWrapper("java.lang.Byte", "byteValue");
            }
            if (type instanceof ShortType) {
                return new PrimitiveWrapper("java.lang.Short", "shortValue");
            }
            if (type instanceof CharType) {
                return new PrimitiveWrapper("java.lang.Character", "charValue");
            }
            if (type instanceof IntType) {
                return new PrimitiveWrapper("java.lang.Integer", "intValue");
            }
            if (type instanceof LongType) {
                return new PrimitiveWrapper("java.lang.Long", "longValue");
            }
            if (type instanceof FloatType) {
                return new PrimitiveWrapper("java.lang.Float", "floatValue");
            }
            if (type instanceof DoubleType) {
                return new PrimitiveWrapper("java.lang.Double", "doubleValue");
            }
            return null;
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

    private static final class TraceSelection {
        private final boolean allSites;
        private final boolean allFields;
        private final Map<String, Set<Integer>> callUnits = new LinkedHashMap<>();
        private final Map<String, Set<Integer>> branchUnits = new LinkedHashMap<>();

        private TraceSelection(boolean allSites, boolean allFields) {
            this.allSites = allSites;
            this.allFields = allFields;
        }

        private static TraceSelection allRuntimeState() {
            return new TraceSelection(true, true);
        }

        private Set<Integer> units(Map<String, Set<Integer>> sites,
                                   String method) {
            Set<Integer> values = sites.get(method);
            return values == null ? Collections.emptySet() : values;
        }
    }


    private static boolean concolicInstrumentationEnabled() {
        return ConcolicInstrumentationSelections
                .instrumentationRequested();
    }

}
