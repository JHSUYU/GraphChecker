package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.AccessorCallTarget;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ConcolicBranchSelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ConcolicMaterializationSelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.InstrumentationPlan;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.CallArgumentOutputCapture;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ExactHeapOutputCapture;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.RootedOutputCapture;
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
import soot.jimple.AssignStmt;
import soot.jimple.ArrayRef;
import soot.jimple.Constant;
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
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.MHGDominatorsFinder;

import java.io.IOException;
import java.util.ArrayDeque;
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
     * Region discovery records only the balanced activation tree.
     */
    private void instrumentLiteRuntimeTrace(StaticProgram result) {
        Set<String> selectedMethods = new LinkedHashSet<>(
                result.traceMethods);
        HookCatalog refs = HookCatalog.trace();
        Set<String> skippedClasses = traceSkipClasses();
        Set<String> instrumented = new LinkedHashSet<>();
        int instrumentedMethods = 0;
        int skippedMethods = 0;
        for (String signature : result.traceMethods) {
            if (!selectedMethods.contains(signature)) {
                continue;
            }
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
                instrumentLiteMethod(
                        body, method, originalUnits,
                        insertionPoint, lowerBound, receiver, refs);
                instrumentedMethods++;
                instrumented.add(signature);
            } catch (RuntimeException exception) {
                LOG.debug("Skipping skeleton trace instrumentation for {}",
                        signature, exception);
            }
        }
        LOG.info("Instrumented {} methods for REGION_SKELETON trace "
                        + "({} skipped)",
                instrumentedMethods, skippedMethods);
    }

    /**
     * Inserts region hooks at the roots selected by the runtime activation
     * plan. Concolic instrumentation without that plan is not executable.
     */
    private void instrumentConcolicRegions() {
        HookCatalog refs = HookCatalog.concolic();
        InstrumentationPlan plan = ConcolicInstrumentationSelections
                .instrumentationPlanFromEnvironment();
        ConcolicBranchSelection branchSelection = plan.branches();
        ConcolicMaterializationSelection materializationSelection =
                plan.materializations();
        List<RootedOutputCapture> outputCaptureSelection =
                plan.outputCaptures();
        List<CallArgumentOutputCapture> callArgumentOutputs =
                plan.callArgumentOutputs();
        List<ExactHeapOutputCapture> exactHeapOutputs =
                plan.exactHeapOutputs();
        String outputCaptureReceiverClass = plan.receiverClass();
        String signature = plan.rootMethod();
        Set<String> instrumentationMethods =
                new LinkedHashSet<>(plan.instrumentationMethods());
        final SootMethod logicalRoot;
        try {
            logicalRoot = Scene.v().getMethod(signature);
        } catch (RuntimeException missing) {
            throw new IllegalStateException(
                    "Selected concolic root is unavailable: " + signature,
                    missing);
        }
        SootMethod replayEntry = plan.replayAnchorAllowed()
                ? selectConcolicReplayEntry(logicalRoot,
                plan.replayAnchorMethods()) : logicalRoot;
        String replayEntrySignature = replayEntry.getSignature();
        // The logical region remains rooted at signature.  The replay entry
        // is only the finite activation at which the VM starts recording, so
        // its loops are still part of the bounded execution semantics.
        instrumentationMethods.add(replayEntrySignature);
        Set<String> taggedMethods = new LinkedHashSet<>(branchSelection.methods());
        taggedMethods.addAll(materializationSelection.localMethods());
        taggedMethods.addAll(materializationSelection.methodArgumentMethods());
        taggedMethods.addAll(materializationSelection.accessorCallerMethods());
        taggedMethods.addAll(instrumentationMethods);
        for (ExactHeapOutputCapture capture : exactHeapOutputs) {
            taggedMethods.add(capture.method());
        }
        Stmt preTargetReplayArm = selectPreTargetReplayArmCall(
                replayEntry, plan.targetMethod(), taggedMethods,
                plan.outputRelation(), plan.replayAnchorAllowed());
        Stmt delayedReplayArm = preTargetReplayArm == null
                ? selectDelayedReplayArmCall(
                replayEntry, plan.targetMethod(), taggedMethods,
                plan.outputRelation(), plan.replayAnchorAllowed()) : null;
        for (String methodSignature : taggedMethods) {
            try {
                SootMethod method = Scene.v().getMethod(methodSignature);
                if (method != null && method.isConcrete()) {
                    tagOriginalUnits(snapshotUnits(method.retrieveActiveBody()));
                }
            } catch (RuntimeException ignored) {
            }
        }
        int boundedBackedges = instrumentConcolicLoopBounds(
                instrumentationMethods, plan.loopBound());
        Set<String> replayPathMethods = replayPathLoopMethods(
                instrumentationMethods);
        for (String methodSignature : replayPathMethods) {
            try {
                SootMethod method = Scene.v().getMethod(methodSignature);
                if (method != null && method.isConcrete()) {
                    tagOriginalUnits(snapshotUnits(
                            method.retrieveActiveBody()));
                }
            } catch (RuntimeException ignored) {
                // Unresolvable bodies are dropped by the bounding pass too.
            }
        }
        int replayPathBodies = instrumentConcolicLoopBounds(
                replayPathMethods, plan.loopBound(), true);
        LOG.info("Bounded {} slice backedge(s) and {} replay-path loop "
                        + "body edge(s) across {} replay-path method(s)",
                boundedBackedges, replayPathBodies, replayPathMethods.size());
        // Exact mutation captures must be installed before root-exit hooks.
        // When the definition method is the root itself, this guarantees the
        // completed mutation state is emitted while its region is still active.
        instrumentConcolicExactHeapOutputs(exactHeapOutputs, refs);
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
            Unit delayedInactive = null;
            if (preTargetReplayArm != null || delayedReplayArm != null) {
                Local attempted = newTraceLocal(body, IntType.v(),
                        "$causynthRegionAttempted");
                entry.add(Jimple.v().newAssignStmt(attempted,
                        IntConstant.v(0)));
                activation = new ArrayList<>();
                delayedInactive = Jimple.v().newNopStmt();
                activation.add(Jimple.v().newIfStmt(
                        Jimple.v().newNeExpr(attempted,
                                IntConstant.v(0)), delayedInactive));
                // One engine acquisition attempt per replay activation.  A
                // throwing target never reaches this assignment or the arm.
                activation.add(Jimple.v().newAssignStmt(attempted,
                        IntConstant.v(1)));
            }
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
            Unit enterRegion = Jimple.v().newAssignStmt(token,
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.ENTER_REGION_FRAME),
                            StringConstant.v(signature), receiver,
                            rootArguments));
            activation.add(enterRegion);
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
            if (preTargetReplayArm == null && delayedReplayArm == null) {
                insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);
            } else {
                activation.add(delayedInactive);
                insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);
                if (preTargetReplayArm != null) {
                    // Demanded effects execute inside the exact target call,
                    // so arm immediately before its unique invocation.  This
                    // retains those effects without recording the unrelated
                    // connection/setup prefix of a long-lived service root.
                    insertBeforeSequence(body, preTargetReplayArm,
                            activation);
                } else {
                    // The arm is on the normal fall-through edge.  If the
                    // exact target throws, neither attempted nor
                    // enterRegionFrame runs.
                    insertAfterSequence(body, delayedReplayArm, activation);
                }
            }

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
                            signature, refs.ref(Hook.EXIT_REGION_FRAME),
                            refs.ref(Hook.PAUSE_OBSERVATION),
                            refs.ref(Hook.RESUME_OBSERVATION));
                } else if (stmt instanceof ReturnVoidStmt) {
                    instrumentRegionExitFieldCaptures(body, stmt,
                            token, receiver, outputCaptureReceiverClass,
                            outputCaptureSelection, refs);
                    insertRegionExit(body, stmt, NullConstant.v(),
                            signature, refs.ref(Hook.EXIT_REGION_FRAME),
                            refs.ref(Hook.PAUSE_OBSERVATION),
                            refs.ref(Hook.RESUME_OBSERVATION));
                }
            }
            addRegionThrowHandler(body, regionStart, signature,
                    refs.ref(Hook.THROW_REGION_FRAME),
                    refs.ref(Hook.PAUSE_OBSERVATION),
                    refs.ref(Hook.RESUME_OBSERVATION));
        } catch (RuntimeException exception) {
            throw new IllegalStateException(
                    "Could not instrument selected concolic region root "
                            + signature + " at replay entry "
                            + replayEntrySignature, exception);
        }
        instrumentConcolicAccessorCallContexts(materializationSelection, refs);
        instrumentConcolicCallArgumentOutputs(callArgumentOutputs, refs);
        instrumentConcolicMethodArguments(materializationSelection, refs);
        instrumentConcolicFieldWrites(instrumentationMethods,
                materializationSelection, refs);
        instrumentConcolicMaterializations(materializationSelection, refs);
        instrumentConcolicBranches(branchSelection, refs);
        LOG.info("Instrumented symbolic-region root {} at replay entry {} "
                        + "for concolic replay{}; "
                        + "bounded {} CFG backedges at {} loop-body "
                        + "iterations each",
                signature, replayEntrySignature,
                preTargetReplayArm != null ? " with pre-target engine arm"
                        : delayedReplayArm == null ? ""
                        : " with post-target engine arm",
                boundedBackedges,
                plan.loopBound().maxBackedgeTraversals());
    }

    /**
     * Selects a unique normal-return boundary at which the symbolic engine
     * may be armed without losing any demanded replay semantics.
     *
     * <p>This is deliberately fail-closed.  It applies only to an output
     * relation with a stable root selector, and only when the explicit task
     * target is not itself part of the methods that must be replayed.  The
     * declared target call must occur exactly once in the replay entry.</p>
     */
    static Stmt selectDelayedReplayArmCall(
            SootMethod replayEntry, String targetSignature,
            Collection<String> replayDemandSignatures,
            boolean outputRelation, boolean replayAnchorAllowed) {
        if (!outputRelation || !replayAnchorAllowed
                || replayEntry == null || !replayEntry.isConcrete()
                || targetSignature == null
                || targetSignature.trim().isEmpty()
                || replayDemandSignatures == null
                || replayDemandSignatures.contains(targetSignature)
                || targetReachesReplayDemand(targetSignature,
                replayDemandSignatures)) {
            return null;
        }
        Body body = activeBody(replayEntry);
        if (body == null) return null;
        Stmt selected = uniqueInvocation(body, targetSignature);
        return selected != null && body.getUnits().getSuccOf(selected) != null
                ? selected : null;
    }

    /**
     * Arms immediately before a unique target whose body contains demanded
     * replay effects.  This is the causal counterpart of the post-target arm:
     * it excludes a long concrete prefix without skipping output writes that
     * occur inside the target call itself.
     */
    static Stmt selectPreTargetReplayArmCall(
            SootMethod replayEntry, String targetSignature,
            Collection<String> replayDemandSignatures,
            boolean outputRelation, boolean replayAnchorAllowed) {
        if (!outputRelation || !replayAnchorAllowed
                || replayEntry == null || !replayEntry.isConcrete()
                || targetSignature == null
                || targetSignature.trim().isEmpty()
                || replayDemandSignatures == null
                || !(replayDemandSignatures.contains(targetSignature)
                || targetReachesReplayDemand(targetSignature,
                replayDemandSignatures))) {
            return null;
        }
        Body body = activeBody(replayEntry);
        return body == null ? null : uniqueInvocation(body, targetSignature);
    }

    private static Body activeBody(SootMethod method) {
        try {
            return method.retrieveActiveBody();
        } catch (RuntimeException unavailable) {
            return null;
        }
    }

    private static Stmt uniqueInvocation(Body body, String targetSignature) {
        Stmt selected = null;
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()
                    || !targetSignature.equals(((Stmt) unit)
                    .getInvokeExpr().getMethodRef().getSignature())) {
                continue;
            }
            if (selected != null) return null;
            selected = (Stmt) unit;
        }
        return selected;
    }

    /**
     * A target call is not a safe delayed arm when demanded effects execute
     * inside that call.  Arming after it would silently miss those effects.
     */
    private static boolean targetReachesReplayDemand(
            String targetSignature,
            Collection<String> replayDemandSignatures) {
        final SootMethod target;
        try {
            target = Scene.v().getMethod(targetSignature);
        } catch (RuntimeException missing) {
            return true;
        }
        Set<String> remaining = new LinkedHashSet<>(
                replayDemandSignatures);
        remaining.remove(targetSignature);
        if (remaining.isEmpty()) return false;
        Set<SootMethod> reached = new LinkedHashSet<>();
        ArrayDeque<SootMethod> pending = new ArrayDeque<>();
        reached.add(target);
        pending.add(target);
        while (!pending.isEmpty() && reached.size() <= 4096) {
            SootMethod caller = pending.removeFirst();
            for (SootMethod callee : directApplicationCallees(caller)) {
                if (!reached.add(callee)) continue;
                if (remaining.contains(callee.getSignature())) return true;
                pending.addLast(callee);
            }
        }
        return false;
    }

    /**
     * Chooses the nearest same-receiver activation that encloses both the
     * task target and every demanded output method.
     *
     * <p>A thread root such as {@code run()} can spend an unbounded concrete
     * prefix in connection setup before it reaches the code the task asks the
     * VM to summarize.  Starting the single symbolic engine at that root lets
     * an unrelated node monopolize it.  The deepest common caller is the same
     * logical region activation, but starts after that prefix and still
     * encloses all demanded effects.  We only move the entry when direct
     * application-call evidence proves the enclosure and the receiver and
     * argument shapes are unchanged; otherwise the logical root is retained.
     */
    static SootMethod selectConcolicReplayEntry(
            SootMethod logicalRoot, Collection<String> demandedSignatures) {
        if (logicalRoot == null || !logicalRoot.isConcrete()
                || demandedSignatures == null
                || demandedSignatures.isEmpty()) {
            return logicalRoot;
        }
        Set<SootMethod> demanded = new LinkedHashSet<>();
        for (String signature : demandedSignatures) {
            if (signature == null || signature.trim().isEmpty()) continue;
            try {
                SootMethod method = Scene.v().getMethod(signature);
                if (!method.equals(logicalRoot)) demanded.add(method);
            } catch (RuntimeException missing) {
                return logicalRoot;
            }
        }
        if (demanded.isEmpty()) return logicalRoot;

        Map<SootMethod, Integer> selfDepth = selfCallDepth(logicalRoot);
        List<Map.Entry<SootMethod, Integer>> candidates = new ArrayList<>(
                selfDepth.entrySet());
        candidates.sort((left, right) -> Integer.compare(
                right.getValue(), left.getValue()));
        for (Map.Entry<SootMethod, Integer> entry : candidates) {
            SootMethod candidate = entry.getKey();
            if (candidate.equals(logicalRoot)
                    || !compatibleReplayEntry(logicalRoot, candidate)
                    || inNontrivialSelfCallCycle(candidate)
                    || !reachesAllDemanded(candidate, demanded,
                    logicalRoot)) {
                continue;
            }
            return candidate;
        }
        return logicalRoot;
    }

    /** Receiver-preserving path used only to prove the activation nesting. */
    private static Map<SootMethod, Integer> selfCallDepth(
            SootMethod logicalRoot) {
        Map<SootMethod, Integer> depth = new LinkedHashMap<>();
        ArrayDeque<SootMethod> pending = new ArrayDeque<>();
        depth.put(logicalRoot, 0);
        pending.add(logicalRoot);
        while (!pending.isEmpty()) {
            SootMethod caller = pending.removeFirst();
            int nextDepth = depth.get(caller) + 1;
            for (SootMethod callee : directSelfCallees(caller)) {
                if (!compatibleReplayEntry(logicalRoot, callee)
                        || depth.containsKey(callee)) continue;
                depth.put(callee, nextDepth);
                pending.addLast(callee);
            }
        }
        return depth;
    }

    static boolean compatibleReplayEntry(
            SootMethod logicalRoot, SootMethod candidate) {
        return candidate != null && candidate.isConcrete()
                && !candidate.isConstructor()
                && !candidate.isStaticInitializer()
                && logicalRoot.isStatic() == candidate.isStatic()
                && logicalRoot.getDeclaringClass().equals(
                candidate.getDeclaringClass())
                && logicalRoot.getParameterTypes().equals(
                candidate.getParameterTypes())
                && logicalRoot.getReturnType().equals(
                candidate.getReturnType());
    }

    /** A cyclic helper cannot prove a strictly nested replay boundary. */
    private static boolean inNontrivialSelfCallCycle(SootMethod candidate) {
        Set<SootMethod> reached = new LinkedHashSet<>();
        ArrayDeque<SootMethod> pending = new ArrayDeque<>(
                directSelfCallees(candidate));
        while (!pending.isEmpty() && reached.size() <= 4096) {
            SootMethod method = pending.removeFirst();
            if (method.equals(candidate)) return true;
            if (!reached.add(method)) continue;
            pending.addAll(directSelfCallees(method));
        }
        return false;
    }

    static Set<SootMethod> directApplicationCallees(
            SootMethod caller) {
        Set<SootMethod> result = new LinkedHashSet<>();
        if (caller == null || !caller.isConcrete()) return result;
        Body body;
        try {
            body = caller.retrieveActiveBody();
        } catch (RuntimeException unavailable) {
            return result;
        }
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()) continue;
            try {
                SootMethodRef reference = ((Stmt) unit).getInvokeExpr()
                        .getMethodRef();
                SootMethod callee = reference.declaringClass()
                        .getMethodUnsafe(reference.getSubSignature());
                if (callee == null) callee = reference.tryResolve();
                if (callee != null && callee.isConcrete()
                        && callee.getDeclaringClass().isApplicationClass()) {
                    result.add(callee);
                }
            } catch (RuntimeException unresolved) {
                // An unresolved or polymorphic edge cannot prove that moving
                // the replay entry preserves the demanded enclosure.
            }
        }
        return result;
    }

    private static Set<SootMethod> directSelfCallees(SootMethod caller) {
        Set<SootMethod> result = new LinkedHashSet<>();
        if (caller == null || !caller.isConcrete()) return result;
        Body body;
        try {
            body = caller.retrieveActiveBody();
        } catch (RuntimeException unavailable) {
            return result;
        }
        Local thisLocal = null;
        if (!caller.isStatic()) {
            try {
                thisLocal = body.getThisLocal();
            } catch (RuntimeException unavailable) {
                return result;
            }
        }
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()) continue;
            InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
            boolean sameReceiver = caller.isStatic()
                    && !(invoke instanceof InstanceInvokeExpr);
            if (invoke instanceof InstanceInvokeExpr && thisLocal != null) {
                sameReceiver = ((InstanceInvokeExpr) invoke).getBase()
                        .equivTo(thisLocal);
            }
            if (!sameReceiver) continue;
            try {
                SootMethodRef reference = invoke.getMethodRef();
                SootMethod callee = reference.declaringClass()
                        .getMethodUnsafe(reference.getSubSignature());
                if (callee == null) callee = reference.tryResolve();
                if (callee != null && caller.getDeclaringClass().equals(
                        callee.getDeclaringClass())) {
                    result.add(callee);
                }
            } catch (RuntimeException unresolved) {
                // No exact receiver-preserving edge, so no anchor proof.
            }
        }
        return result;
    }

    private static boolean reachesAllDemanded(
            SootMethod start, Set<SootMethod> demanded,
            SootMethod logicalRoot) {
        Set<SootMethod> remaining = new LinkedHashSet<>(demanded);
        remaining.remove(start);
        if (remaining.isEmpty()) return true;
        Set<SootMethod> reached = new LinkedHashSet<>();
        ArrayDeque<SootMethod> pending = new ArrayDeque<>();
        reached.add(start);
        pending.add(start);
        while (!pending.isEmpty() && reached.size() <= 4096) {
            SootMethod method = pending.removeFirst();
            for (SootMethod callee : directApplicationCallees(method)) {
                if (callee.equals(logicalRoot) || !reached.add(callee)) {
                    continue;
                }
                if (remaining.remove(callee) && remaining.isEmpty()) {
                    return true;
                }
                pending.addLast(callee);
            }
        }
        return false;
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
            throw exactHeapCaptureFailure(capture,
                    "FIELD_ASSIGNMENT_MISMATCH", null);
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
                if (!materializations.matches(method.getSignature(),
                        originalUnitIndex(unit), field.getFieldRef())) {
                    continue;
                }
                List<Unit> after = new ArrayList<>();
                after.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.ref(Hook.PAUSE_OBSERVATION))));
                Value owner = objectArg(body, field.getBase(), after);
                String declaredField =
                        CausynthStaticFacts.declaredFieldSignature(
                                field.getFieldRef());
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
                            refs.ref(Hook.PAUSE_OBSERVATION))));
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

            Unit normalExit = Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.EXIT_ACCESSOR_CALL_CONTEXT), contextToken));
            Unit continuation = Jimple.v().newNopStmt();
            Unit skipHandler = Jimple.v().newGotoStmt(continuation);
            Local caught = newTraceLocal(body,
                    RefType.v("java.lang.Throwable"),
                    "$causynthAccessorThrown");
            Unit handler = Jimple.v().newIdentityStmt(caught,
                    Jimple.v().newCaughtExceptionRef());
            Unit exceptionalExit = Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.EXIT_ACCESSOR_CALL_CONTEXT), contextToken));
            Unit rethrow = Jimple.v().newThrowStmt(caught);
            insertAfterSequence(body, selected, Arrays.asList(normalExit,
                    skipHandler, handler, exceptionalExit, rethrow,
                    continuation));
            SootClass throwable = Scene.v().getSootClass(
                    "java.lang.Throwable");
            body.getTraps().addFirst(Jimple.v().newTrap(throwable, selected,
                    normalExit, handler));
        }
    }

    private void instrumentConcolicMaterializations(
            ConcolicMaterializationSelection selection,
            HookCatalog refs) {
        if (selection.isEmpty()) {
            return;
        }
        List<SootClass> classes = new ArrayList<>();
        for (SootClass sootClass : Scene.v().getApplicationClasses()) {
            classes.add(sootClass);
        }
        for (SootClass sootClass : classes) {
            for (SootMethod method : new ArrayList<>(sootClass.getMethods())) {
                if (!method.isConcrete()) {
                    continue;
                }
                Body body;
                try {
                    body = method.retrieveActiveBody();
                } catch (RuntimeException ignored) {
                    continue;
                }
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
                    if (associativeReadInvoke(invoke)) {
                        InstanceInvokeExpr read = (InstanceInvokeExpr) invoke;
                        List<Unit> before = new ArrayList<>();
                        before.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.ref(Hook.PAUSE_OBSERVATION))));
                        Value container = objectArg(body, read.getBase(),
                                before);
                        Value key = objectArg(body, read.getArg(0), before);
                        before.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.ref(Hook.MATERIALIZE_ASSOCIATIVE_READ),
                                        container, key)));
                        before.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.ref(Hook.RESUME_OBSERVATION))));
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
        return instrumentConcolicLoopBounds(methods, policy, false);
    }

    /**
     * The methods whose loops carry the replay between the region root and
     * the calls the task's slice is stated over.
     *
     * <p>A long-lived root does not reach its slice once and stop: it spins a
     * service loop that re-enters the same code every turn, and that loop
     * lives in a sibling method of the root - not in the slice, and so not in
     * any set the bounded semantics already instruments.  Taking the declaring
     * classes of the methods the task does name is a static over-approximation
     * of that path which needs no call graph, stays inside the code the
     * activation owns, and cannot depend on any application's naming.</p>
     */
    private static Set<String> replayPathLoopMethods(Set<String> bounded) {
        Set<SootClass> owners = new LinkedHashSet<>();
        for (String methodSignature : bounded) {
            try {
                SootMethod method = Scene.v().getMethod(methodSignature);
                if (method != null) owners.add(method.getDeclaringClass());
            } catch (RuntimeException ignored) {
                // A method the bounding pass cannot resolve owns no class
                // this pass could expand either.
            }
        }
        Set<String> expanded = new LinkedHashSet<>();
        for (SootClass owner : owners) {
            for (SootMethod candidate : new ArrayList<>(owner.getMethods())) {
                // A constructor's loop may precede the initialization that
                // makes a hook legal to insert, and the bounded pass already
                // rejects that case for the methods it owns.  Leaving them to
                // it keeps this expansion from failing a whole campaign over
                // a method the replay never runs a loop in.
                if (candidate.isConstructor()
                        || candidate.isStaticInitializer()
                        || !candidate.isConcrete()
                        || bounded.contains(candidate.getSignature())) {
                    continue;
                }
                expanded.add(candidate.getSignature());
            }
        }
        return expanded;
    }

    /**
     * Bounds the loops of one method set.
     *
     * <p>With {@code resourceOnly}, each loop body is charged to the replay
     * resource cap and nothing else.  This is what a replay-path method
     * outside the task's bounded slice gets: its loops are not part of the
     * path space the solver reasons about, so they must not spend the unroll
     * budget, but the work they do decides whether the replay can finish at
     * all and therefore has to be accounted for somewhere.</p>
     */
    int instrumentConcolicLoopBounds(
            Set<String> methods, LoopBoundPolicy policy,
            boolean resourceOnly) {
        if (policy == null) {
            throw new IllegalArgumentException("loop bound policy is required");
        }
        HookCatalog hooks = HookCatalog.concolic();
        SootMethodRef replayBody = hooks.ref(Hook.CHECK_REPLAY_LOOP_BODY);
        SootMethodRef checkBackedge = resourceOnly ? replayBody
                : hooks.ref(Hook.CHECK_LOOP_BACKEDGE);
        SootMethodRef recordBackedge = resourceOnly ? replayBody
                : hooks.ref(Hook.RECORD_LOOP_BACKEDGE);
        SootMethodRef checkBodyEntry = resourceOnly ? replayBody
                : hooks.ref(Hook.CHECK_LOOP_BODY_ENTRY);
        int instrumented = 0;
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
            BriefUnitGraph graph = new BriefUnitGraph(body);
            MHGDominatorsFinder<Unit> dominators =
                    new MHGDominatorsFinder<>(graph);
            List<CfgBackedge> backedges = new ArrayList<>();
            for (Unit source : original) {
                int sourceIndex = originalUnitIndex(source);
                if (sourceIndex < 0) continue;
                for (Unit target : graph.getSuccsOf(source)) {
                    int targetIndex = originalUnitIndex(target);
                    if (targetIndex >= 0
                            && dominators.isDominatedBy(source, target)) {
                        backedges.add(new CfgBackedge(source, sourceIndex,
                                target, targetIndex));
                    }
                }
            }

            List<CfgNaturalLoop> loops = groupNaturalLoops(backedges);
            Unit safeEntry = safeInstrumentationEntry(body, method);
            for (CfgNaturalLoop loop : loops) {
                List<CfgEdge> continuations = continuationEdges(
                        body, graph, dominators, original, loop);
                String loopId = loop.identity(method);
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
                    if (resourceOnly) {
                        // One charge per body entered.  The latch hooks exist
                        // to separate a guarded return to the header from the
                        // transfer into the next body; the resource cap counts
                        // bodies, so only the body-entering edge is charged.
                        // It counts them per loop, and so is given the loop.
                        if (!entersBody) continue;
                        edgeHooks.add(new LoopEdgeHook(checkBodyEntry, loopId));
                    } else {
                        edgeHooks.add(new LoopEdgeHook(
                                !loop.hasContinuationGuard
                                        ? checkBackedge : recordBackedge,
                                loopId));
                        if (entersBody) {
                            edgeHooks.add(new LoopEdgeHook(checkBodyEntry,
                                    bodyEntryLoopId(loopId,
                                            backedge.source)));
                        }
                    }
                    splitCfgEdge(body, method, backedge.source,
                            backedge.target, loopId,
                            policy.maxBackedgeTraversals(), edgeHooks);
                    instrumented++;
                }
                for (CfgEdge continuation : continuations) {
                    splitCfgEdge(body, method, continuation.source,
                            continuation.target, loopId,
                            policy.maxBackedgeTraversals(),
                            Collections.singletonList(new LoopEdgeHook(
                                    checkBodyEntry, resourceOnly ? loopId
                                            : bodyEntryLoopId(loopId,
                                            continuation.source))));
                    // In bounded mode the return value counts the backedges
                    // this pass split, which a continuation edge is not.  The
                    // resource pass charges bodies, so for it a continuation
                    // is exactly what was instrumented.
                    if (resourceOnly) instrumented++;
                }
            }
        }
        return instrumented;
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

    private static List<CfgEdge> continuationEdges(
            Body body, BriefUnitGraph graph,
            MHGDominatorsFinder<Unit> dominators, List<Unit> original,
            CfgNaturalLoop loop) {
        Set<Unit> members = naturalLoopMembers(graph, loop);
        List<CfgEdge> result = continuationEdgesFrom(
                body, loop.header, members);
        if (!result.isEmpty()) {
            loop.hasContinuationGuard = true;
            return result;
        }
        // A do-while guard is itself a conditional backedge.
        result = new ArrayList<>();
        for (CfgBackedge backedge : loop.backedges) {
            result.addAll(continuationEdgesFrom(
                    body, backedge.source, members));
        }
        if (!result.isEmpty()) {
            loop.hasContinuationGuard = true;
            return deduplicateEdges(result);
        }
        // Jimple often places hasNext() evaluation immediately before the
        // actual IfStmt, so the dominance header is not itself the guard.
        // Select the first loop-exit branch that dominates every latch.
        for (Unit candidate : original) {
            if (!members.contains(candidate)) continue;
            boolean dominatesEveryLatch = true;
            for (CfgBackedge backedge : loop.backedges) {
                if (!dominators.isDominatedBy(
                        backedge.source, candidate)) {
                    dominatesEveryLatch = false;
                    break;
                }
            }
            if (!dominatesEveryLatch) continue;
            result = continuationEdgesFrom(body, candidate, members);
            if (!result.isEmpty()) {
                loop.hasContinuationGuard = true;
                return deduplicateEdges(result);
            }
        }
        return Collections.emptyList();
    }

    private static Set<Unit> naturalLoopMembers(
            BriefUnitGraph graph, CfgNaturalLoop loop) {
        Set<Unit> members = Collections.newSetFromMap(
                new IdentityHashMap<Unit, Boolean>());
        members.add(loop.header);
        List<Unit> work = new ArrayList<>();
        for (CfgBackedge backedge : loop.backedges) {
            if (members.add(backedge.source)) work.add(backedge.source);
        }
        for (int index = 0; index < work.size(); index++) {
            Unit current = work.get(index);
            for (Unit predecessor : graph.getPredsOf(current)) {
                if (members.add(predecessor)
                        && predecessor != loop.header) {
                    work.add(predecessor);
                }
            }
        }
        return members;
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

    /**
     * Names the guard whose decision enters this body, so the replay charges
     * the unroll bound on evidence about this loop's own continuation instead
     * of whichever branch happened to be decided last.  An edge whose source
     * has no original identity names none, and the replay then charges it.
     */
    private static String bodyEntryLoopId(String loopId, Unit guard) {
        int guardIndex = originalUnitIndex(guard);
        return guardIndex < 0 ? loopId : loopId + "@guard:u" + guardIndex;
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
        private boolean hasContinuationGuard;

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
                                  String rootMethod,
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
                exitRef, StringConstant.v(rootMethod), objectValue,
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

    private Local instrumentLiteMethod(
            Body body, SootMethod method, List<Unit> originalUnits,
            Unit insertionPoint, Unit lowerBound, Value receiver,
            HookCatalog refs) {
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
                refs.ref(Hook.THROW_ACTIVE_METHOD_LITE));
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
                                       String rootMethod,
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
                throwRef, StringConstant.v(rootMethod), caught));
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
        RECORD_FIELD_WRITE,
        RECORD_REGION_EXIT_FIELD_OUTPUT,
        RECORD_CALL_ARGUMENT_OUTPUT,
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
        RECORD_LOOP_BACKEDGE,
        CHECK_LOOP_BODY_ENTRY,
        CHECK_REPLAY_LOOP_BODY,
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
                            LongType.v(), string, object, ArrayType.v(object, 1))
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
                    .add(Hook.RECORD_FIELD_WRITE, runtime,
                            "recordFieldWrite", VoidType.v(), object, string)
                    .add(Hook.RECORD_REGION_EXIT_FIELD_OUTPUT, runtime,
                            "recordRegionExitFieldOutput", VoidType.v(),
                            string, object, object)
                    .add(Hook.RECORD_CALL_ARGUMENT_OUTPUT, runtime,
                            "recordCallArgumentOutput", VoidType.v(),
                            string, object)
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
                    .add(Hook.RECORD_LOOP_BACKEDGE, runtime,
                            "recordLoopBackedge", VoidType.v(), string,
                            IntType.v())
                    .add(Hook.CHECK_LOOP_BODY_ENTRY, runtime,
                            "checkLoopBodyEntry", VoidType.v(), string,
                            IntType.v())
                    .add(Hook.CHECK_REPLAY_LOOP_BODY, runtime,
                            "checkReplayLoopBody", VoidType.v(), string,
                            IntType.v())
                    .add(Hook.EXIT_REGION_FRAME, runtime, "exitRegionFrame",
                            VoidType.v(), string, object, string)
                    .add(Hook.THROW_REGION_FRAME, runtime, "throwRegionFrame",
                            VoidType.v(), string,
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
        return Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.instrument.concolic"),
                System.getenv("CAUSYNTH_INSTRUMENT_CONCOLIC"),
                "false"));
    }

}
