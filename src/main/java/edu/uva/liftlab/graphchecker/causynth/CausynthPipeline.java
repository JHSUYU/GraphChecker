package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.AccessorCallTarget;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ConcolicBranchSelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ConcolicMaterializationSelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ConcolicOutputCaptureSelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ConcolicReplaySelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.OutputCaptureTarget;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ReplayTarget;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.option.GraphCheckerOptions;
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
import soot.SootFieldRef;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.jimple.AssignStmt;
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
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.SwitchStmt;
import soot.tagkit.Tag;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.readRuntimeSelectedRoots;

/**
 * Annotation-directed static backward data-flow analysis.
 *
 * <p>The analysis starts from one annotated exception construction and
 * discovers the throw value, exception payload, controlling guards, and their
 * data dependencies automatically. Local Java/Jimple calls, discovered RPC
 * dispatches, interface dispatches, and explicitly enabled protocol bridges
 * all emit edges into the same static data-flow graph.</p>
 */
public final class CausynthPipeline {
    private static final Logger LOG = LoggerFactory.getLogger(CausynthPipeline.class);
    private static final String TRACE_RECORDER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder";
    private static final String CONCOLIC_REGION_RUNTIME_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime";
    private final GraphCheckerOptions options;

    public CausynthPipeline(GraphCheckerOptions options) {
        this.options = options;
    }

    public void run() throws IOException {
        CausynthTargetContext target = CausynthTargetResolver.resolve(options);
        ExceptionTargetSite exceptionTarget =
                ExceptionTargetAnnotationScanner.select(
                        options.getInputList(), target.exceptionTargetId);
        target = target.withExceptionTarget(exceptionTarget);

        LOG.info("Seed backward analysis starts at annotated exception {}",
                exceptionTarget.stableIdentity());
        CausynthAnalysisResult result =
                new SeedBackwardStaticAnalyzer(target).analyze();
        SymbolicPlanningStage.build(result);
        SymbolicRegionAssemblyStage.assemble(result);
        buildAutomaticDerivationBoundary(result);
        instrumentRuntimeTrace(result);
        instrumentConcolicRegions(result);
        boolean boundedOutputClosureCoverageReady =
                recordSymbolicCoverageAuthority(result);
        new CausynthArtifactWriter(target.outputDir, result).writeAll();
        enforceSymbolicCoverage(result, boundedOutputClosureCoverageReady);
        LOG.info("Seed backward analysis wrote {} edges to {}",
                result.edges.size(), target.outputDir);
    }

    private boolean recordSymbolicCoverageAuthority(
            CausynthAnalysisResult result) {
        boolean ready = selectedBoundedOutputClosureCoverageReady(result);
        result.slices.put("boundedOutputClosureCoverageReady", ready);
        result.slices.put("symbolicCoverageGateAuthority", ready
                ? "RUNTIME_SELECTED_BOUNDED_OUTPUT_CLOSURE_V1"
                : "GLOBAL_SYMBOLIC_REGION_COVERAGE");
        return ready;
    }

    private void enforceSymbolicCoverage(CausynthAnalysisResult result,
                                         boolean boundedOutputClosureCoverageReady) {
        boolean strictCoverage = Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.coverage.strict"),
                System.getenv("CAUSYNTH_COVERAGE_STRICT"),
                "true"));
        if (strictCoverage
                && !Boolean.TRUE.equals(result.symbolicCoverage.get("complete"))
                && !boundedOutputClosureCoverageReady) {
            throw new IllegalStateException("Incomplete symbolic-region coverage: "
                    + result.symbolicCoverage);
        }
        if (strictCoverage
                && !Boolean.TRUE.equals(result.symbolicCoverage.get("complete"))) {
            LOG.info("Global symbolic-region coverage is incomplete, but the "
                            + "exact runtime-selected bounded output closure is "
                            + "ready; preserving strict coverage outside that "
                            + "selected activation");
        }
    }

    private void instrumentRuntimeTrace(CausynthAnalysisResult result) {
        if (!Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.instrument.trace"),
                System.getenv("CAUSYNTH_INSTRUMENT_TRACE"),
                "false"))) {
            return;
        }
        SootMethodRef recordRef = traceRecorderMethodRef();
        SootMethodRef recordFieldRef = traceRecorderFieldMethodRef();
        RichTraceRefs richRefs = RichTraceRefs.create();
        ConcolicRegionRefs observationIsolation = Boolean.parseBoolean(
                firstNonBlank(
                        System.getProperty("causynth.instrument.concolic"),
                        System.getenv("CAUSYNTH_INSTRUMENT_CONCOLIC"),
                        "false")) ? ConcolicRegionRefs.create() : null;
        TraceFieldSelection traceFields = traceFieldSelection(result);
        TraceSiteSelection traceSites = traceSiteSelection(result);
        int count = 0;
        int fieldCount = 0;
        int richMethodCount = 0;
        int callSiteCount = 0;
        int branchCount = 0;
        for (Map<String, Object> methodRow : result.traceMethods) {
            String signature = String.valueOf(methodRow.get("method"));
            try {
                SootMethod method = Scene.v().getMethod(signature);
                if (method == null || !method.isConcrete() || method.isConstructor()) {
                    continue;
                }
                Body body = method.retrieveActiveBody();
                List<Unit> originalUnits = snapshotUnits(body);
                tagOriginalUnits(originalUnits);
                Unit insertionPoint = firstNonIdentity(body);
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
                if (traceSites.relevantMethods.contains(signature)) {
                    RichInstrumentationStats stats = instrumentRichMethod(body, method,
                            originalUnits, insertionPoint, receiver, traceSites,
                            richRefs, observationIsolation);
                    richMethodCount++;
                    callSiteCount += stats.callSites;
                    branchCount += stats.branches;
                } else {
                    Stmt traceCall = Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(recordRef,
                                    StringConstant.v(signature), receiver));
                    List<Unit> traceUnits = new ArrayList<>();
                    beginTraceObservationIsolation(traceUnits,
                            observationIsolation);
                    traceUnits.add(traceCall);
                    endTraceObservationIsolation(traceUnits,
                            observationIsolation);
                    insertBeforeOrAppend(body, insertionPoint, traceUnits);
                }
                fieldCount += instrumentFieldTrace(body, method, recordFieldRef,
                        traceFields, originalUnits, observationIsolation);
                count++;
            } catch (RuntimeException exception) {
                LOG.debug("Skipping trace instrumentation for {}", signature, exception);
            }
        }
        result.slices.put("traceInstrumentedMethodCount", count);
        result.slices.put("traceInstrumentedFieldAccessCount", fieldCount);
        result.slices.put("richTraceInstrumentedMethodCount", richMethodCount);
        result.slices.put("traceInstrumentedCallSiteCount", callSiteCount);
        result.slices.put("traceInstrumentedBranchCount", branchCount);
        result.slices.put("traceObservationIsolatedFromConcolic",
                observationIsolation != null);
        LOG.info("Instrumented {} selected methods ({} rich), {} callsites, "
                        + "{} branches, and {} field accesses for runtime trace",
                count, richMethodCount, callSiteCount, branchCount, fieldCount);
    }

    /**
     * Inserts region hooks. Without an activation plan, static candidates are
     * retained for backward-compatible discovery runs. After concrete
     * discovery, the runtime activation plan is authoritative and a replay
     * transformation inserts hooks at the runtime-selected roots.
     */
    private void instrumentConcolicRegions(CausynthAnalysisResult result) {
        if (!Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.instrument.concolic"),
                System.getenv("CAUSYNTH_INSTRUMENT_CONCOLIC"),
                "false"))) {
            return;
        }
        ConcolicRegionRefs refs = ConcolicRegionRefs.create();
        ConcolicBranchSelection branchSelection =
                ConcolicBranchSelection.from(result.symbolicRegions);
        ConcolicMaterializationSelection materializationSelection =
                ConcolicInstrumentationSelections
                        .materializationSelectionFromEnvironment();
        ConcolicReplaySelection replaySelection =
                ConcolicInstrumentationSelections
                        .replaySelectionFromEnvironment();
        ConcolicOutputCaptureSelection outputCaptureSelection =
                ConcolicInstrumentationSelections
                        .outputCaptureSelectionFromEnvironment();
        Set<String> roots = concolicRootMethods(result);
        Set<String> backedViewMethods = concolicBackedViewMethods(result);
        backedViewMethods.addAll(roots);
        Set<String> taggedMethods = new LinkedHashSet<>(branchSelection.methods());
        taggedMethods.addAll(materializationSelection.localMethods());
        taggedMethods.addAll(materializationSelection.accessorCallerMethods());
        taggedMethods.addAll(replaySelection.methods());
        taggedMethods.addAll(outputCaptureSelection.methods());
        taggedMethods.addAll(backedViewMethods);
        for (String methodSignature : taggedMethods) {
            try {
                SootMethod method = Scene.v().getMethod(methodSignature);
                if (method != null && method.isConcrete()) {
                    tagOriginalUnits(snapshotUnits(method.retrieveActiveBody()));
                }
            } catch (RuntimeException ignored) {
            }
        }
        int instrumented = 0;
        int skipped = 0;
        for (String signature : roots) {
            try {
                SootMethod method = Scene.v().getMethod(signature);
                if (method == null || !method.isConcrete() || method.isConstructor()) {
                    skipped++;
                    continue;
                }
                Body body = method.retrieveActiveBody();
                List<Unit> originalUnits = snapshotUnits(body);
                tagOriginalUnits(originalUnits);
                Unit insertionPoint = firstNonIdentity(body);
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
                ArrayType objectArrayType = ArrayType.v(
                        RefType.v("java.lang.Object"), 1);
                Local rootArguments = newTraceLocal(body, objectArrayType,
                        "$causynthRootArguments");
                entry.add(Jimple.v().newAssignStmt(rootArguments,
                        Jimple.v().newNewArrayExpr(
                                RefType.v("java.lang.Object"),
                                IntConstant.v(method.getParameterCount()))));
                for (int index = 0; index < method.getParameterCount(); index++) {
                    Type parameterType = method.getParameterType(index);
                    if (!(parameterType instanceof RefType)
                            && !(parameterType instanceof ArrayType)) {
                        // Primitive slots remain null by construction.  They
                        // are intentionally not root-selection predicates.
                        continue;
                    }
                    Value parameter;
                    try {
                        parameter = body.getParameterLocal(index);
                    } catch (RuntimeException ignored) {
                        continue;
                    }
                    entry.add(Jimple.v().newAssignStmt(
                            Jimple.v().newArrayRef(rootArguments,
                                    IntConstant.v(index)),
                            objectArg(body, parameter, entry)));
                }
                Unit enterRegion = Jimple.v().newAssignStmt(token,
                        Jimple.v().newStaticInvokeExpr(refs.enterRegionFrame,
                                StringConstant.v(signature), receiver,
                                rootArguments));
                entry.add(enterRegion);
                // The wrapper pushes a zero placeholder before legacy entry.
                // Include the call itself so either this catch-all or an
                // existing handler closes that exact frame if entry fails.
                // The cleanup handler reads no incoming entry local, so this
                // is also verifier-safe at the call's exceptional edge.
                Unit regionStart = enterRegion;
                for (int index = 0; index < method.getParameterCount(); index++) {
                    Value parameter;
                    try {
                        parameter = body.getParameterLocal(index);
                    } catch (RuntimeException ignored) {
                        continue;
                    }
                    Value primitiveValue = primitiveValueString(body,
                            parameter, entry);
                    if (PrimitiveWrapper.forType(parameter.getType()) != null) {
                        addPrimitiveArgumentMaterialization(body, parameter,
                                token, index, primitiveValue, entry,
                                refs.materializeArgument,
                                refs.pauseObservation,
                                refs.resumeObservation);
                    } else {
                        Value objectValue = objectArg(body, parameter, entry);
                        Local modeled = newTraceLocal(body,
                                RefType.v("java.lang.Object"),
                                "$causynthArgumentModel");
                        entry.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.pauseObservation)));
                        entry.add(Jimple.v().newAssignStmt(modeled,
                                Jimple.v().newStaticInvokeExpr(
                                        refs.materializeArgument, token,
                                        IntConstant.v(index), objectValue,
                                        primitiveValue)));
                        entry.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.resumeObservation)));
                        Value converted = parameter.getType() instanceof RefType
                                && "java.lang.Object".equals(((RefType)
                                parameter.getType()).getClassName())
                                ? modeled : Jimple.v().newCastExpr(modeled,
                                parameter.getType());
                        entry.add(Jimple.v().newAssignStmt(parameter,
                                converted));
                        entry.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.pauseObservation)));
                        entry.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.symbolizeArgument, token,
                                        IntConstant.v(index), parameter,
                                        primitiveValue)));
                        entry.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.resumeObservation)));
                    }
                }
                // A region root is a method invocation boundary, not an
                // arbitrary control-flow visit to its first statement.  In
                // particular, service-loop backedges must keep targeting the
                // original loop head; redirecting them through this probe
                // creates one false activation/frame per iteration.
                insertBeforeOrAppendNoRedirect(body, insertionPoint, entry);

                for (Unit unit : originalUnits) {
                    if (!(unit instanceof Stmt)) {
                        continue;
                    }
                    Stmt stmt = (Stmt) unit;
                    if (stmt instanceof ReturnStmt) {
                        insertRegionExit(body, stmt, ((ReturnStmt) stmt).getOp(),
                                signature, refs.exitRegionFrame,
                                refs.pauseObservation,
                                refs.resumeObservation);
                    } else if (stmt instanceof ReturnVoidStmt) {
                        insertRegionExit(body, stmt, NullConstant.v(),
                                signature, refs.exitRegionFrame,
                                refs.pauseObservation,
                                refs.resumeObservation);
                    }
                }
                // Cleanup resolves the exact dynamic invocation frame from
                // the root signature constant.  The catch handler therefore
                // reads no entry local from its incoming StackMapFrame.
                addRegionThrowHandler(body, regionStart, signature,
                        refs.throwRegionFrame,
                        refs.pauseObservation, refs.resumeObservation);
                instrumented++;
            } catch (RuntimeException exception) {
                skipped++;
                LOG.debug("Skipping concolic region root instrumentation for {}",
                signature, exception);
            }
        }
        int accessorCallContextCount =
                instrumentConcolicAccessorCallContexts(
                        materializationSelection, refs);
        int materializationCount = instrumentConcolicMaterializations(
                materializationSelection, refs);
        int replayMaterializationCount =
                instrumentConcolicReplayMaterializations(replaySelection, refs);
        int outputCaptureHookCount = instrumentConcolicOutputCaptures(
                outputCaptureSelection, refs);
        int backedViewMutationHookCount =
                instrumentConcolicBackedViewMutations(backedViewMethods, refs);
        int branchCount = instrumentConcolicBranches(branchSelection, refs);
        result.slices.put("concolicRegionRootCount", roots.size());
        result.slices.put("concolicRegionInstrumentedRootCount", instrumented);
        result.slices.put("concolicRegionSkippedRootCount", skipped);
        result.slices.put("concolicMappedBranchCount", branchCount);
        result.slices.put("concolicMaterializationHookCount",
                materializationCount);
        result.slices.put("concolicAccessorCallContextHookCount",
                accessorCallContextCount);
        result.slices.put("concolicReplayMaterializationHookCount",
                replayMaterializationCount);
        result.slices.put("concolicOutputCaptureHookCount",
                outputCaptureHookCount);
        result.slices.put("concolicBackedViewMutationHookCount",
                backedViewMutationHookCount);
        LOG.info("Instrumented {} symbolic-region roots for concolic replay ({} skipped)",
                instrumented, skipped);
    }

    private Set<String> concolicRootMethods(CausynthAnalysisResult result) {
        String planValue = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.plan"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_PLAN")));
        if (!planValue.isEmpty()) {
            String selected = stringValue(firstNonBlank(
                    System.getProperty("causynth.concolic.activation.id"),
                    System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_ID")));
            try {
                Set<String> runtimeRoots = readRuntimeSelectedRoots(
                        Paths.get(planValue), selected);
                if (runtimeRoots.isEmpty()) {
                    throw new IllegalStateException(
                            "Activation plan contains no replayable runtime-selected roots: "
                                    + planValue);
                }
                result.slices.put("concolicRootAuthority",
                        "RUNTIME_ACTIVATION_PLAN");
                result.slices.put("concolicActivationPlan",
                        Paths.get(planValue).toAbsolutePath().toString());
                result.slices.put("concolicSelectedRootMethods",
                        new ArrayList<>(runtimeRoots));
                return runtimeRoots;
            } catch (IOException | RuntimeException exception) {
                throw new IllegalStateException(
                        "Could not load runtime-selected concolic roots from "
                                + planValue, exception);
            }
        }

        Set<String> staticCandidates = new LinkedHashSet<>();
        for (Map<String, Object> row : result.symbolicRegions) {
            String root = stringValue(firstNonBlank(
                    stringValue(row.get("staticRootCandidate")),
                    stringValue(row.get("rootMethod"))));
            if (!root.isEmpty()) {
                staticCandidates.add(root);
            }
        }
        result.slices.put("concolicRootAuthority", "STATIC_CANDIDATE_FALLBACK");
        return staticCandidates;
    }

    private boolean selectedBoundedOutputClosureCoverageReady(
            CausynthAnalysisResult result) {
        if (!Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.instrument.concolic"),
                System.getenv("CAUSYNTH_INSTRUMENT_CONCOLIC"),
                "false"))) {
            return false;
        }
        String planValue = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.plan"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_PLAN")));
        String selected = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.id"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_ID")));
        if (planValue.isEmpty() || selected.isEmpty()) {
            return false;
        }
        try {
            if (!ConcolicInstrumentationSelections
                    .selectedBoundedOutputClosureCoverageReady(
                    Paths.get(planValue), selected)) {
                return false;
            }
        } catch (IOException | RuntimeException unreadablePlan) {
            LOG.warn("Bounded output-closure coverage authority rejected "
                    + "activation plan {}", planValue, unreadablePlan);
            return false;
        }

        int rootCount = intValue(result.slices.get(
                "concolicRegionRootCount"), -1);
        int instrumentedCount = intValue(result.slices.get(
                "concolicRegionInstrumentedRootCount"), -1);
        int skippedCount = intValue(result.slices.get(
                "concolicRegionSkippedRootCount"), -1);
        String recordedPlan = stringValue(result.slices.get(
                "concolicActivationPlan"));
        boolean samePlan;
        try {
            samePlan = !recordedPlan.isEmpty()
                    && Paths.get(planValue).toAbsolutePath().normalize().equals(
                    Paths.get(recordedPlan).toAbsolutePath().normalize());
        } catch (RuntimeException invalidPath) {
            samePlan = false;
        }
        return "RUNTIME_ACTIVATION_PLAN".equals(stringValue(
                result.slices.get("concolicRootAuthority")))
                && samePlan
                && rootCount == 1
                && instrumentedCount == rootCount
                && skippedCount == 0;
    }

    private static String jsonString(JsonObject object, String field) {
        if (object == null) return "";
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static JsonObject jsonObject(JsonObject object, String field) {
        if (object == null) return new JsonObject();
        JsonElement value = object.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static boolean jsonBoolean(JsonObject object, String field,
                                       boolean fallback) {
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int jsonInt(JsonObject object, String field, int fallback) {
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    /**
     * Wraps only activation-selected accessor invocations with a tiny
     * thread-local runtime context. The exact-call trap covers the invocation
     * instruction alone; its rethrow remains inside any original enclosing
     * try range, preserving the application's handler semantics.
     */
    private int instrumentConcolicAccessorCallContexts(
            ConcolicMaterializationSelection selection,
            ConcolicRegionRefs refs) {
        int count = 0;
        for (AccessorCallTarget target : selection.accessorCalls()) {
            SootMethod method;
            Body body;
            try {
                method = Scene.v().getMethod(target.callerMethod);
                if (method == null || !method.isConcrete()
                        || method.isConstructor()) {
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
                            refs.enterAccessorCallContext,
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
                            refs.materializeField,
                            StringConstant.v(target.implementationMethod),
                            IntConstant.v(-1), receiver,
                            StringConstant.v(target.fieldSignature),
                            StringConstant.v(target.fieldName))));
            insertBeforeSequence(body, selected, before);

            Unit normalExit = Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.exitAccessorCallContext, contextToken));
            Unit continuation = Jimple.v().newNopStmt();
            Unit skipHandler = Jimple.v().newGotoStmt(continuation);
            Local caught = newTraceLocal(body,
                    RefType.v("java.lang.Throwable"),
                    "$causynthAccessorThrown");
            Unit handler = Jimple.v().newIdentityStmt(caught,
                    Jimple.v().newCaughtExceptionRef());
            Unit exceptionalExit = Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(
                            refs.exitAccessorCallContext, contextToken));
            Unit rethrow = Jimple.v().newThrowStmt(caught);
            insertAfterSequence(body, selected, Arrays.asList(normalExit,
                    skipHandler, handler, exceptionalExit, rethrow,
                    continuation));
            SootClass throwable = Scene.v().getSootClass(
                    "java.lang.Throwable");
            body.getTraps().addFirst(Jimple.v().newTrap(throwable, selected,
                    normalExit, handler));
            count++;
        }
        return count;
    }

    private int instrumentConcolicMaterializations(
            ConcolicMaterializationSelection selection,
            ConcolicRegionRefs refs) {
        if (selection.isEmpty()) {
            return 0;
        }
        int count = 0;
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
                for (Unit unit : originalUnits) {
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
                        if (!selection.matches(method.getSignature(),
                                unitIndex, fieldRef)) {
                            continue;
                        }
                        if (field instanceof StaticFieldRef) {
                            instrumentConsumedStaticPrimitiveFieldRead(body,
                                    method, stmt, unitIndex,
                                    (StaticFieldRef) field, refs);
                            count++;
                            continue;
                        }
                        if (!(field instanceof InstanceFieldRef)) {
                            throw new IllegalStateException(
                                    "UNKNOWN_FIELD_MATERIALIZATION_UNSUPPORTED: "
                                            + fieldRef.getSignature()
                                            + " at " + method.getSignature()
                                            + "#u" + unitIndex);
                        }
                        InstanceFieldRef instanceField =
                                (InstanceFieldRef) field;
                        if (fieldRef.type() instanceof ArrayType) {
                            instrumentConsumedArrayFieldRead(body, method,
                                    stmt, unitIndex, instanceField, refs);
                            count++;
                            continue;
                        }
                        List<Unit> before = new ArrayList<>();
                        before.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.pauseObservation)));
                        Value owner = objectArg(body, instanceField.getBase(),
                                before);
                        before.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.materializeField,
                                        StringConstant.v(method.getSignature()),
                                        IntConstant.v(unitIndex), owner,
                                        StringConstant.v(fieldRef.getSignature()),
                                        StringConstant.v(fieldRef.name()))));
                        before.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.resumeObservation)));
                        insertBeforeSequence(body, stmt, before);
                        count++;
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
                                        refs.pauseObservation)));
                        after.add(Jimple.v().newAssignStmt(modeled,
                                Jimple.v().newStaticInvokeExpr(
                                        refs.materializeReference,
                                        StringConstant.v(method.getSignature()),
                                        StringConstant.v(local.getName()),
                                        local)));
                        after.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.resumeObservation)));
                        after.add(Jimple.v().newAssignStmt(local,
                                Jimple.v().newCastExpr(modeled,
                                        local.getType())));
                    } else {
                        addPrimitiveMaterialization(body, method, local, after,
                                refs.materializePrimitive,
                                refs.pauseObservation,
                                refs.resumeObservation);
                    }
                    if (!after.isEmpty()) {
                        insertAfterSequence(body, stmt, after);
                        count++;
                    }
                }
            }
        }
        return count;
    }

    /**
     * Materializes a primitive {@code getstatic} on the exact local that
     * consumed it.  The static field itself is never overwritten: replay and
     * symbolic state are activation-local, while ordinary execution still
     * performs exactly one real getstatic before the hook runs.
     */
    private static void instrumentConsumedStaticPrimitiveFieldRead(
            Body body, SootMethod method, Stmt stmt, int unitIndex,
            StaticFieldRef field, ConcolicRegionRefs refs) {
        if (!(stmt instanceof AssignStmt)
                || ((AssignStmt) stmt).getRightOp() != field
                || !(((AssignStmt) stmt).getLeftOp() instanceof Local)) {
            throw new IllegalStateException(
                    "STATIC_FIELD_READ_SHAPE_UNSUPPORTED: "
                            + field.getFieldRef().getSignature() + " at "
                            + method.getSignature() + "#u" + unitIndex);
        }
        Local consumed = (Local) ((AssignStmt) stmt).getLeftOp();
        PrimitiveWrapper wrapper = PrimitiveWrapper.forType(
                consumed.getType());
        if (wrapper == null) {
            throw new IllegalStateException(
                    "STATIC_FIELD_MATERIALIZATION_UNSUPPORTED: "
                            + field.getFieldRef().getSignature() + " at "
                            + method.getSignature() + "#u" + unitIndex);
        }

        SootClass wrapperClass = Scene.v().getSootClass(wrapper.className);
        RefType wrapperType = RefType.v(wrapper.className);
        SootMethodRef valueOf = Scene.v().makeMethodRef(wrapperClass,
                "valueOf", Collections.singletonList(consumed.getType()),
                wrapperType, true);
        Local boxed = newTraceLocal(body, wrapperType,
                "$causynthStaticFieldBox");
        Local materialized = newTraceLocal(body,
                RefType.v("java.lang.Object"),
                "$causynthStaticFieldMaterialized");
        Local cast = newTraceLocal(body, wrapperType,
                "$causynthStaticFieldUnbox");
        SootMethodRef unbox = Scene.v().makeMethodRef(wrapperClass,
                wrapper.unboxMethod, Collections.<Type>emptyList(),
                consumed.getType(), false);

        List<Unit> after = new ArrayList<>();
        after.add(Jimple.v().newAssignStmt(boxed,
                Jimple.v().newStaticInvokeExpr(valueOf, consumed)));
        after.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.pauseObservation)));
        after.add(Jimple.v().newAssignStmt(materialized,
                Jimple.v().newStaticInvokeExpr(
                        refs.materializeStaticPrimitiveField,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex),
                        StringConstant.v(field.getFieldRef().getSignature()),
                        StringConstant.v(field.getFieldRef().name()), boxed)));
        after.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.resumeObservation)));
        after.add(Jimple.v().newAssignStmt(cast,
                Jimple.v().newCastExpr(materialized, wrapperType)));
        after.add(Jimple.v().newAssignStmt(consumed,
                Jimple.v().newVirtualInvokeExpr(cast, unbox)));
        insertAfterSequence(body, stmt, after);
    }

    /**
     * Splits an array-valued {@code getfield} around the runtime hooks without
     * ever evaluating the field twice.  The synthetic local is the JVM value
     * produced by the original field read; both the post hook and the original
     * statement consume that same local.  Consequently a concurrent putfield
     * after the read cannot change either the program value or the VM array
     * expression associated with it.
     */
    private static void instrumentConsumedArrayFieldRead(
            Body body, SootMethod method, Stmt stmt, int unitIndex,
            InstanceFieldRef field, ConcolicRegionRefs refs) {
        if (!(stmt instanceof AssignStmt)
                || ((AssignStmt) stmt).getRightOp() != field) {
            throw new IllegalStateException(
                    "ARRAY_FIELD_READ_SHAPE_UNSUPPORTED: "
                            + field.getFieldRef().getSignature() + " at "
                            + method.getSignature() + "#u" + unitIndex);
        }

        AssignStmt assignment = (AssignStmt) stmt;
        Local consumed = newTraceLocal(body, field.getType(),
                "$causynthConsumedArrayField");
        Unit exactGetField = Jimple.v().newAssignStmt(consumed, field);
        assignment.setRightOp(consumed);

        List<Unit> sequence = new ArrayList<>();
        sequence.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseObservation)));
        Value owner = objectArg(body, field.getBase(), sequence);
        sequence.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.prepareFieldMaterialization,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex), owner,
                        StringConstant.v(field.getFieldRef().getSignature()),
                        StringConstant.v(field.getFieldRef().name()))));
        sequence.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeObservation)));
        sequence.add(exactGetField);
        sequence.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseObservation)));
        sequence.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.materializeConsumedField,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex), owner,
                        StringConstant.v(field.getFieldRef().getSignature()),
                        StringConstant.v(field.getFieldRef().name()),
                        consumed)));
        sequence.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeObservation)));
        insertBeforeSequence(body, stmt, sequence);
    }

    /**
     * Exposes solver-derived reference results at exact Jimple sites.  The
     * transformer deliberately has no knowledge of the semantic theory that
     * produced the value (Map, protocol, collection, and so on); that
     * provenance remains in the activation plan.  The original assignment is
     * executed first so the VM can retain its expression, then the modeled
     * value is written back for ordinary Java control flow to consume.
     */
    private int instrumentConcolicReplayMaterializations(
            ConcolicReplaySelection selection, ConcolicRegionRefs refs) {
        int count = 0;
        for (ReplayTarget target : selection.targets()) {
            try {
                SootMethod method = Scene.v().getMethod(target.method);
                if (method == null || !method.isConcrete()) {
                    continue;
                }
                Body body = method.retrieveActiveBody();
                Unit unit = originalUnit(body, target.unitIndex);
                if (!(unit instanceof AssignStmt)) {
                    continue;
                }
                AssignStmt assignment = (AssignStmt) unit;
                Value result = assignment.getLeftOp();
                Type resultType = result.getType();
                if (!(resultType instanceof RefType)
                        && !(resultType instanceof ArrayType)) {
                    continue;
                }

                List<Unit> after = new ArrayList<>();
                after.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(refs.pauseObservation)));
                Value concreteResult = objectArg(body, result, after);
                Local modeledResult = newTraceLocal(body,
                        RefType.v("java.lang.Object"), "$causynthReplayResult");
                after.add(Jimple.v().newAssignStmt(modeledResult,
                        Jimple.v().newStaticInvokeExpr(
                                refs.materializeReplayReferenceResult,
                                StringConstant.v(method.getSignature()),
                                IntConstant.v(target.unitIndex),
                                concreteResult)));
                after.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(refs.resumeObservation)));
                Value converted = modeledResult;
                if (!(resultType instanceof RefType)
                        || !"java.lang.Object".equals(
                        ((RefType) resultType).getClassName())) {
                    converted = Jimple.v().newCastExpr(modeledResult,
                            resultType);
                }
                after.add(Jimple.v().newAssignStmt(result, converted));
                insertAfterSequence(body, assignment, after);
                count++;
            } catch (RuntimeException exception) {
                LOG.debug("Skipping concolic replay materialization for {}#u{}",
                        target.method, target.unitIndex, exception);
            }
        }
        return count;
    }

    /** Captures the VM expression at an exact activation-authorized endpoint. */
    private int instrumentConcolicOutputCaptures(
            ConcolicOutputCaptureSelection selection,
            ConcolicRegionRefs refs) {
        int count = 0;
        for (OutputCaptureTarget target : selection.targets()) {
            try {
                SootMethod method = Scene.v().getMethod(
                        target.instrumentedMethod());
                if (method == null || !method.isConcrete()) {
                    continue;
                }
                Body body = method.retrieveActiveBody();
                Unit unit = originalUnit(body, target.unitIndex);
                if (target.isFieldAssignmentRhs()) {
                    count += instrumentFieldAssignmentOutputCapture(body,
                            unit, target, refs);
                    continue;
                }
                if (!(unit instanceof Stmt)
                        || !((Stmt) unit).containsInvokeExpr()) {
                    continue;
                }
                Stmt stmt = (Stmt) unit;
                InvokeExpr invoke = stmt.getInvokeExpr();
                if (!target.calleeMethod.equals(
                        invoke.getMethodRef().getSignature())
                        || target.argumentIndex < 0
                        || target.argumentIndex >= invoke.getArgCount()) {
                    continue;
                }
                Value argument = invoke.getArg(target.argumentIndex);
                List<Unit> before = new ArrayList<>();
                // Box while symbolic propagation is still enabled.  Capture
                // boxes are always fresh: Wrapper.valueOf may return a JVM
                // cache singleton, which cannot safely own an activation-
                // local symbolic shadow.
                Value objectValue = boxedCaptureValue(body, argument, before);
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.pauseObservation)));
                Value primitiveValue = primitiveValueString(body, argument,
                        before);
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.recordOutputCapture,
                                StringConstant.v(target.callerMethod),
                                IntConstant.v(target.unitIndex),
                                StringConstant.v(target.siteId),
                                StringConstant.v(target.calleeMethod),
                                IntConstant.v(target.argumentIndex),
                                StringConstant.v(target.outputPort),
                                StringConstant.v(target.outputCell),
                                StringConstant.v(target.captureBindingId),
                                IntConstant.v(target.occurrence),
                                objectValue, primitiveValue)));
                before.add(Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(
                                refs.resumeObservation)));
                insertBeforeSequence(body, stmt, before);
                count++;
            } catch (RuntimeException exception) {
                LOG.debug("Skipping {} concolic output capture for {}#u{}",
                        target.captureKind, target.instrumentedMethod(),
                        target.unitIndex, exception);
            }
        }
        return count;
    }

    /**
     * Captures the value written by one exact original instance-field
     * assignment.  A non-immediate RHS is evaluated once into a local and the
     * original write is rewritten to consume that local; evaluating the RHS
     * again after the write could duplicate calls or allocation side effects.
     * The runtime hook itself is inserted after the write, so a failing
     * {@code putfield} cannot produce a capture.
     */
    private int instrumentFieldAssignmentOutputCapture(
            Body body, Unit unit, OutputCaptureTarget target,
            ConcolicRegionRefs refs) {
        if (!(unit instanceof AssignStmt)) return 0;
        AssignStmt assignment = (AssignStmt) unit;
        if (!(assignment.getLeftOp() instanceof InstanceFieldRef)) return 0;
        InstanceFieldRef field = (InstanceFieldRef) assignment.getLeftOp();
        if (!target.fieldSignature.equals(
                field.getFieldRef().getSignature())) {
            return 0;
        }

        Value rhs = assignment.getRightOp();
        if (!(rhs instanceof Local) && !(rhs instanceof Constant)) {
            Local evaluated = newTraceLocal(body, rhs.getType(),
                    "$causynthAssignedRhs");
            Unit evaluateOnce = Jimple.v().newAssignStmt(evaluated, rhs);
            assignment.setRightOp(evaluated);
            insertBeforeSequence(body, assignment,
                    Collections.singletonList(evaluateOnce));
            rhs = evaluated;
        }

        List<Unit> after = new ArrayList<>();
        Local activeToken = newTraceLocal(body, LongType.v(),
                "$causynthActiveToken");
        after.add(Jimple.v().newAssignStmt(activeToken,
                Jimple.v().newStaticInvokeExpr(refs.activeToken)));
        Value owner = objectArg(body, field.getBase(), after);
        Value assignedValue = boxedCaptureValue(body, rhs, after);
        after.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseObservation)));
        Value primitiveValue = primitiveValueString(body, rhs, after);
        after.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(
                        refs.recordFieldAssignmentOutput,
                        activeToken,
                        StringConstant.v(target.instrumentedMethod()),
                        IntConstant.v(target.unitIndex),
                        StringConstant.v(target.siteId),
                        StringConstant.v(target.fieldSignature),
                        StringConstant.v(target.captureBindingId),
                        StringConstant.v(target.outputPort),
                        StringConstant.v(target.outputCell),
                        IntConstant.v(target.occurrence),
                        owner, assignedValue, primitiveValue)));
        after.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeObservation)));
        insertAfterSequence(body, assignment, after);
        return 1;
    }

    /**
     * Instruments the Java collection-view protocol which implements
     * {@code Iterator.remove()} as a mutation of the backing map.  Static
     * analysis deliberately supplies a broad set of same-thread region
     * methods; the runtime's active activation and identity bindings decide
     * which concrete views actually belong to the selected heap state.
     */
    private int instrumentConcolicBackedViewMutations(
            Set<String> methods, ConcolicRegionRefs refs) {
        int count = 0;
        for (String signature : methods) {
            try {
                SootMethod method = Scene.v().getMethod(signature);
                if (method == null || !method.isConcrete()) {
                    continue;
                }
                Body body = method.retrieveActiveBody();
                List<Unit> units = snapshotUnits(body);
                tagOriginalUnits(units);
                for (Unit unit : units) {
                    if (!(unit instanceof Stmt)) {
                        continue;
                    }
                    Stmt stmt = (Stmt) unit;
                    if (!stmt.containsInvokeExpr()
                            || !(stmt.getInvokeExpr()
                            instanceof InstanceInvokeExpr)) {
                        continue;
                    }
                    InvokeExpr invoke = stmt.getInvokeExpr();
                    InstanceInvokeExpr instance = (InstanceInvokeExpr) invoke;
                    String name = invoke.getMethodRef().name();
                    int unitIndex = originalUnitIndex(unit);
                    if (unitIndex < 0 || invoke.getArgCount() != 0) {
                        continue;
                    }

                    List<Unit> after = new ArrayList<>();
                    after.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.pauseObservation)));
                    boolean recognized = false;
                    if (stmt instanceof AssignStmt
                            && isBackedMapViewFactory(name)) {
                        Value view = ((AssignStmt) stmt).getLeftOp();
                        after.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.registerMapView,
                                        StringConstant.v(method.getSignature()),
                                        IntConstant.v(unitIndex),
                                        objectArg(body, instance.getBase(), after),
                                        objectArg(body, view, after),
                                        StringConstant.v(mapViewKind(name)))));
                        recognized = true;
                    } else if (stmt instanceof AssignStmt
                            && isIteratorFactory(name)) {
                        Value iterator = ((AssignStmt) stmt).getLeftOp();
                        after.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.registerMapViewIterator,
                                        StringConstant.v(method.getSignature()),
                                        IntConstant.v(unitIndex),
                                        objectArg(body, instance.getBase(), after),
                                        objectArg(body, iterator, after))));
                        recognized = true;
                    } else if (stmt instanceof AssignStmt
                            && "next".equals(name)) {
                        Value element = ((AssignStmt) stmt).getLeftOp();
                        after.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.recordMapIteratorNext,
                                        StringConstant.v(method.getSignature()),
                                        IntConstant.v(unitIndex),
                                        objectArg(body, instance.getBase(), after),
                                        objectArg(body, element, after))));
                        recognized = true;
                    } else if ("remove".equals(name)
                            && invoke.getMethodRef().returnType()
                            instanceof VoidType) {
                        // A post-call hook is reached only when remove()
                        // returns normally. IllegalStateException and other
                        // exceptional removals therefore cannot become
                        // applied heap effects.
                        after.add(Jimple.v().newInvokeStmt(
                                Jimple.v().newStaticInvokeExpr(
                                        refs.recordMapIteratorRemove,
                                        StringConstant.v(method.getSignature()),
                                        IntConstant.v(unitIndex),
                                        objectArg(body, instance.getBase(), after))));
                        recognized = true;
                    }
                    if (!recognized) {
                        continue;
                    }
                    after.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.resumeObservation)));
                    insertAfterSequence(body, stmt, after);
                    count++;
                }
            } catch (RuntimeException exception) {
                LOG.debug("Skipping backed-view concolic instrumentation for {}",
                        signature, exception);
            }
        }
        return count;
    }

    private static Set<String> concolicBackedViewMethods(
            CausynthAnalysisResult result) {
        Set<String> methods = new LinkedHashSet<>();
        for (Map<String, Object> region : result.symbolicRegions) {
            Object values = region.get("methods");
            if (!(values instanceof Collection)) {
                continue;
            }
            for (Object value : (Collection<?>) values) {
                String method = stringValue(value);
                if (!method.isEmpty()) {
                    methods.add(method);
                }
            }
        }
        return methods;
    }

    private static boolean isBackedMapViewFactory(String name) {
        return "entrySet".equals(name) || "keySet".equals(name)
                || "values".equals(name);
    }

    private static boolean isIteratorFactory(String name) {
        return "iterator".equals(name) || "listIterator".equals(name)
                || "descendingIterator".equals(name);
    }

    private static String mapViewKind(String name) {
        if ("entrySet".equals(name)) return "ENTRY_SET";
        if ("keySet".equals(name)) return "KEY_SET";
        if ("values".equals(name)) return "VALUES";
        return "UNKNOWN";
    }

    private static void addPrimitiveMaterialization(
            Body body, SootMethod method, Local local, List<Unit> units,
            SootMethodRef materializePrimitive,
            SootMethodRef pauseObservation,
            SootMethodRef resumeObservation) {
        PrimitiveWrapper wrapper = PrimitiveWrapper.forType(local.getType());
        if (wrapper == null) {
            return;
        }
        SootClass wrapperClass = Scene.v().getSootClass(wrapper.className);
        RefType wrapperType = RefType.v(wrapper.className);
        SootMethodRef valueOf = Scene.v().makeMethodRef(wrapperClass,
                "valueOf", Collections.singletonList(local.getType()),
                wrapperType, true);
        Local boxed = newTraceLocal(body, wrapperType, "$causynthBox");
        units.add(Jimple.v().newAssignStmt(boxed,
                Jimple.v().newStaticInvokeExpr(valueOf, local)));
        Local materialized = newTraceLocal(body,
                RefType.v("java.lang.Object"), "$causynthMaterialized");
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(pauseObservation)));
        units.add(Jimple.v().newAssignStmt(materialized,
                Jimple.v().newStaticInvokeExpr(materializePrimitive,
                        StringConstant.v(method.getSignature()),
                        StringConstant.v(local.getName()), boxed)));
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(resumeObservation)));
        Local cast = newTraceLocal(body, wrapperType, "$causynthUnbox");
        units.add(Jimple.v().newAssignStmt(cast,
                Jimple.v().newCastExpr(materialized, wrapperType)));
        SootMethodRef unbox = Scene.v().makeMethodRef(wrapperClass,
                wrapper.unboxMethod, Collections.<Type>emptyList(),
                local.getType(), false);
        units.add(Jimple.v().newAssignStmt(local,
                Jimple.v().newVirtualInvokeExpr(cast, unbox)));
    }

    private static void addPrimitiveArgumentMaterialization(
            Body body, Value parameter, Local token, int argumentIndex,
            Value primitiveValue, List<Unit> units,
            SootMethodRef materializeArgument,
            SootMethodRef pauseObservation,
            SootMethodRef resumeObservation) {
        PrimitiveWrapper wrapper = PrimitiveWrapper.forType(
                parameter.getType());
        if (wrapper == null) return;
        SootClass wrapperClass = Scene.v().getSootClass(wrapper.className);
        RefType wrapperType = RefType.v(wrapper.className);
        SootMethodRef valueOf = Scene.v().makeMethodRef(wrapperClass,
                "valueOf", Collections.singletonList(parameter.getType()),
                wrapperType, true);
        Local boxed = newTraceLocal(body, wrapperType,
                "$causynthArgumentBox");
        units.add(Jimple.v().newAssignStmt(boxed,
                Jimple.v().newStaticInvokeExpr(valueOf, parameter)));
        Local materialized = newTraceLocal(body,
                RefType.v("java.lang.Object"),
                "$causynthArgumentMaterialized");
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(pauseObservation)));
        units.add(Jimple.v().newAssignStmt(materialized,
                Jimple.v().newStaticInvokeExpr(materializeArgument, token,
                        IntConstant.v(argumentIndex), boxed,
                        primitiveValue)));
        units.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(resumeObservation)));
        Local cast = newTraceLocal(body, wrapperType,
                "$causynthArgumentUnbox");
        units.add(Jimple.v().newAssignStmt(cast,
                Jimple.v().newCastExpr(materialized, wrapperType)));
        SootMethodRef unbox = Scene.v().makeMethodRef(wrapperClass,
                wrapper.unboxMethod, Collections.<Type>emptyList(),
                parameter.getType(), false);
        units.add(Jimple.v().newAssignStmt(parameter,
                Jimple.v().newVirtualInvokeExpr(cast, unbox)));
    }

    private static int originalUnitIndex(Unit unit) {
        for (Tag tag : unit.getTags()) {
            if (tag instanceof OriginalUnitIndexTag) {
                return ((OriginalUnitIndexTag) tag).index;
            }
        }
        return -1;
    }

    private int instrumentConcolicBranches(ConcolicBranchSelection selection,
                                           ConcolicRegionRefs refs) {
        int count = 0;
        for (String methodSignature : selection.methods()) {
            try {
                SootMethod method = Scene.v().getMethod(methodSignature);
                if (method == null || !method.isConcrete()) {
                    continue;
                }
                Body body = method.retrieveActiveBody();
                for (Integer unitIndex : selection.units(methodSignature)) {
                    Unit unit = originalUnit(body, unitIndex);
                    if (unit instanceof IfStmt) {
                        instrumentConcolicBranch(body, method,
                                (IfStmt) unit, unitIndex, refs);
                        count++;
                    } else if (unit instanceof SwitchStmt
                            && instrumentConcolicSwitch(body, method,
                            (SwitchStmt) unit, unitIndex, refs)) {
                        count++;
                    }
                }
            } catch (RuntimeException exception) {
                LOG.debug("Skipping concolic branch instrumentation for {}",
                        methodSignature, exception);
            }
        }
        return count;
    }

    private void instrumentConcolicBranch(Body body, SootMethod method,
                                          IfStmt branch, int unitIndex,
                                          ConcolicRegionRefs refs) {
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

        // Prepare Java-side occurrence state while observation is paused, but
        // invoke the native marker directly from the transformed method.  On
        // the exact path that native call is the final invocation before the
        // original IfStmt, so runtime bookkeeping bytecodes cannot consume
        // its pending VM event.  A zero handle means no symbolic activation
        // is active, or the required exact-event API was rejected; in either
        // case the runtime records concrete replay or fails closed.
        Unit noMarkerPath = Jimple.v().newNopStmt();
        List<Unit> beforeBranch = new ArrayList<>();
        // This must be a direct native call.  A long/double/float compare is
        // lowered by Soot before this prefix and leaves an exact VM witness
        // for the following IfStmt.  Entering a Java helper before pausing
        // would execute helper branches that could consume that witness.
        beforeBranch.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseVmPathCondition)));
        beforeBranch.add(Jimple.v().newAssignStmt(prepared,
                Jimple.v().newStaticInvokeExpr(refs.prepareBranch,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex),
                        StringConstant.v(expression))));
        beforeBranch.add(Jimple.v().newAssignStmt(vmEvent,
                LongConstant.v(0L)));
        beforeBranch.add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(prepared, LongConstant.v(0L)),
                noMarkerPath));
        beforeBranch.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeVmPathCondition)));
        beforeBranch.add(Jimple.v().newAssignStmt(vmOccurrence,
                Jimple.v().newCastExpr(prepared, IntType.v())));
        beforeBranch.add(Jimple.v().newAssignStmt(vmEvent,
                Jimple.v().newStaticInvokeExpr(refs.markConcolicBranch,
                                StringConstant.v(method.getSignature() + "#u"
                                + unitIndex),
                        vmOccurrence)));
        Unit exactTransfer = Jimple.v().newGotoStmt(branch);
        beforeBranch.add(exactTransfer);
        beforeBranch.add(noMarkerPath);
        beforeBranch.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeVmPathCondition)));
        insertBeforeSequence(body, branch, beforeBranch);
        // UnitPatchingChain redirects pre-existing targets whenever another
        // unit is inserted before their anchor.  Restore this internal edge
        // after the full prefix exists; otherwise the exact path jumps back
        // to prepareBranch and can never execute the original condition.
        ((soot.jimple.GotoStmt) exactTransfer).setTarget(branch);

        List<Unit> falsePath = new ArrayList<>();
        falsePath.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseObservation)));
        falsePath.add(Jimple.v().newAssignStmt(decision,
                Jimple.v().newStaticInvokeExpr(refs.resolveBranch,
                        prepared, vmEvent,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex), StringConstant.v(expression),
                        IntConstant.v(0))));
        falsePath.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeObservation)));
        falsePath.add(Jimple.v().newIfStmt(
                Jimple.v().newNeExpr(decision, IntConstant.v(0)),
                previousTarget));
        insertAfterSequence(body, branch, falsePath);

        Unit trueEntry = Jimple.v().newNopStmt();
        Unit truePause = Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseObservation));
        Unit trueResolve = Jimple.v().newAssignStmt(decision,
                Jimple.v().newStaticInvokeExpr(refs.resolveBranch,
                        prepared, vmEvent,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex), StringConstant.v(expression),
                        IntConstant.v(1)));
        Unit trueResume = Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeObservation));
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

    private boolean instrumentConcolicSwitch(
            Body body, SootMethod method, SwitchStmt branch, int unitIndex,
            ConcolicRegionRefs refs) {
        CausynthBranchShape shape = CausynthBranchShape.from(body, branch);
        if (shape == null || !shape.isSwitch()) return false;
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

        Unit noMarkerPath = Jimple.v().newNopStmt();
        List<Unit> beforeBranch = new ArrayList<>();
        beforeBranch.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.pauseVmPathCondition)));
        beforeBranch.add(Jimple.v().newAssignStmt(prepared,
                Jimple.v().newStaticInvokeExpr(refs.prepareBranch,
                        StringConstant.v(method.getSignature()),
                        IntConstant.v(unitIndex),
                        StringConstant.v(expression))));
        beforeBranch.add(Jimple.v().newAssignStmt(vmEvent,
                LongConstant.v(0L)));
        beforeBranch.add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(prepared, LongConstant.v(0L)),
                noMarkerPath));
        beforeBranch.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeVmPathCondition)));
        beforeBranch.add(Jimple.v().newAssignStmt(vmOccurrence,
                Jimple.v().newCastExpr(prepared, IntType.v())));
        beforeBranch.add(Jimple.v().newAssignStmt(vmEvent,
                Jimple.v().newStaticInvokeExpr(refs.markConcolicBranch,
                        StringConstant.v(method.getSignature() + "#u"
                                + unitIndex), vmOccurrence)));
        Unit exactTransfer = Jimple.v().newGotoStmt(branch);
        beforeBranch.add(exactTransfer);
        beforeBranch.add(noMarkerPath);
        beforeBranch.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(refs.resumeVmPathCondition)));
        insertBeforeSequence(body, branch, beforeBranch);
        ((soot.jimple.GotoStmt) exactTransfer).setTarget(branch);

        List<Unit> entries = new ArrayList<>();
        for (int observed = 0; observed < shape.successorCount(); observed++) {
            Unit entry = Jimple.v().newNopStmt();
            entries.add(entry);
            body.getUnits().add(entry);
            body.getUnits().add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(refs.pauseObservation)));
            body.getUnits().add(Jimple.v().newAssignStmt(effectiveSuccessor,
                    Jimple.v().newStaticInvokeExpr(refs.resolveSwitchBranch,
                            prepared, vmEvent,
                            StringConstant.v(method.getSignature()),
                            IntConstant.v(unitIndex),
                            StringConstant.v(expression),
                            StringConstant.v(shape.kind),
                            StringConstant.v(encodedKeys),
                            IntConstant.v(observed))));
            body.getUnits().add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(refs.resumeObservation)));
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
        return true;
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

    private static TraceSiteSelection traceSiteSelection(
            CausynthAnalysisResult result) {
        TraceSiteSelection selection = new TraceSiteSelection();
        for (Map<String, Object> row : result.symbolicPlan) {
            String method = stringValue(row.get("method"));
            if (!method.isEmpty()) {
                selection.relevantMethods.add(method);
            }
        }
        for (Map<String, Object> edge : result.edges) {
            String method = stringValue(edge.get("method"));
            int unitIndex = intValue(edge.get("unitIndex"), -1);
            if (method.isEmpty() || unitIndex < 0) {
                continue;
            }
            String invoke = stringValue(edge.get("invoke"));
            String transfer = stringValue(edge.get("transferKind"));
            if (!invoke.isEmpty()) {
                selection.add(selection.callUnits, method, unitIndex);
            }
            if ("GUARD".equals(transfer)) {
                selection.add(selection.branchUnits, method, unitIndex);
            }
        }
        return selection;
    }

    private RichInstrumentationStats instrumentRichMethod(
            Body body, SootMethod method, List<Unit> originalUnits,
            Unit insertionPoint, Value receiver, TraceSiteSelection sites,
            RichTraceRefs refs, ConcolicRegionRefs observationIsolation) {
        RichInstrumentationStats stats = new RichInstrumentationStats();
        Local callId = newTraceLocal(body, LongType.v(), "$causynthCallId");
        List<Unit> entryUnits = new ArrayList<>();
        beginTraceObservationIsolation(entryUnits, observationIsolation);
        // Keep the initialization as a defensive verifier-visible value.  The
        // whole entry probe is inserted without redirecting existing trap
        // boundaries: an original catch/finally must not observe a partially
        // executed probe or synthetic locals that did not exist in the input.
        entryUnits.add(Jimple.v().newAssignStmt(callId, LongConstant.v(0L)));
        entryUnits.add(Jimple.v().newAssignStmt(callId,
                Jimple.v().newStaticInvokeExpr(refs.enterMethod,
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
                    refs.recordMethodArgument,
                    callId,
                    IntConstant.v(index),
                    StringConstant.v(method.getParameterType(index).toString()),
                    objectValue,
                    primitiveValue)));
        }
        endTraceObservationIsolation(entryUnits, observationIsolation);
        insertBeforeOrAppendNoRedirect(body, insertionPoint, entryUnits);

        Set<Integer> callUnits = sites.units(sites.callUnits, method.getSignature());
        Set<Integer> branchUnits = sites.units(sites.branchUnits, method.getSignature());
        for (int unitIndex = 0; unitIndex < originalUnits.size(); unitIndex++) {
            Unit unit = originalUnits.get(unitIndex);
            if (!(unit instanceof Stmt)) {
                continue;
            }
            Stmt stmt = (Stmt) unit;
            if (callUnits.contains(unitIndex) && stmt.containsInvokeExpr()
                    && !isRecorderInvoke(stmt.getInvokeExpr())) {
                instrumentCallSite(body, method, stmt, unitIndex, callId,
                        refs, observationIsolation);
                stats.callSites++;
            }
            if (branchUnits.contains(unitIndex)) {
                if (stmt instanceof IfStmt) {
                    instrumentBranch(body, method, (IfStmt) stmt, unitIndex,
                            callId, refs, observationIsolation);
                    stats.branches++;
                } else if (stmt instanceof SwitchStmt
                        && instrumentSwitchBranch(body, method,
                        (SwitchStmt) stmt, unitIndex, callId, refs,
                        observationIsolation)) {
                    stats.branches++;
                }
            }
            if (stmt instanceof ReturnStmt) {
                insertMethodExit(body, stmt, ((ReturnStmt) stmt).getOp(),
                        refs.exitMethod, observationIsolation);
            } else if (stmt instanceof ReturnVoidStmt) {
                insertMethodExit(body, stmt, NullConstant.v(),
                        refs.exitMethod, observationIsolation);
            }
        }
        addActiveThrowHandler(body, insertionPoint, refs.throwMethod,
                observationIsolation == null ? null
                        : observationIsolation.pauseObservation,
                observationIsolation == null ? null
                        : observationIsolation.resumeObservation);
        return stats;
    }

    private void instrumentCallSite(Body body, SootMethod method, Stmt stmt,
                                    int unitIndex, Local ownerCallId,
                                    RichTraceRefs refs,
                                    ConcolicRegionRefs observationIsolation) {
        InvokeExpr invoke = stmt.getInvokeExpr();
        List<Unit> before = new ArrayList<>();
        beginTraceObservationIsolation(before, observationIsolation);
        Value receiverBase = runtimeCallSiteReceiver(invoke);
        Value receiver = receiverBase == null
                ? NullConstant.v() : objectArg(body, receiverBase, before);
        Local invocationId = newTraceLocal(body, LongType.v(), "$causynthInvocation");
        before.add(Jimple.v().newAssignStmt(invocationId,
                Jimple.v().newStaticInvokeExpr(refs.beginCall,
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
                    refs.recordCallArgument,
                    invocationId,
                    IntConstant.v(index),
                    StringConstant.v(declaredType.toString()),
                    objectValue,
                    primitiveValue)));
        }
        endTraceObservationIsolation(before, observationIsolation);
        insertBeforeSequence(body, stmt, before);

        Value returnValue = NullConstant.v();
        if (stmt instanceof AssignStmt) {
            returnValue = ((AssignStmt) stmt).getLeftOp();
        }
        List<Unit> after = new ArrayList<>();
        beginTraceObservationIsolation(after, observationIsolation);
        Value returnObject = objectArg(body, returnValue, after);
        Value primitiveReturn = primitiveValueString(body, returnValue, after);
        after.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.endCall, invocationId, returnObject, primitiveReturn)));
        endTraceObservationIsolation(after, observationIsolation);
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
                                  RichTraceRefs refs,
                                  ConcolicRegionRefs observationIsolation) {
        String expression = branch.getCondition().toString();
        Unit originalTarget = branch.getTarget();
        List<Unit> falsePath = new ArrayList<>();
        beginTraceObservationIsolation(falsePath, observationIsolation);
        Unit falseRecord = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.recordBranch,
                callId,
                StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex),
                StringConstant.v(expression),
                IntConstant.v(0)));
        falsePath.add(falseRecord);
        endTraceObservationIsolation(falsePath, observationIsolation);
        insertAfterSequence(body, branch, falsePath);

        Unit trueEntry = Jimple.v().newNopStmt();
        List<Unit> truePath = new ArrayList<>();
        truePath.add(trueEntry);
        beginTraceObservationIsolation(truePath, observationIsolation);
        Unit trueRecord = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.recordBranch,
                callId,
                StringConstant.v(method.getSignature()),
                IntConstant.v(unitIndex),
                StringConstant.v(expression),
                IntConstant.v(1)));
        truePath.add(trueRecord);
        endTraceObservationIsolation(truePath, observationIsolation);
        Unit resume = Jimple.v().newGotoStmt(originalTarget);
        truePath.add(resume);
        for (Unit unit : truePath) {
            body.getUnits().add(unit);
        }
        branch.setTarget(trueEntry);
    }

    private boolean instrumentSwitchBranch(
            Body body, SootMethod method, SwitchStmt branch, int unitIndex,
            Local callId, RichTraceRefs refs,
            ConcolicRegionRefs observationIsolation) {
        CausynthBranchShape shape = CausynthBranchShape.from(body, branch);
        if (shape == null || !shape.isSwitch()) return false;
        String expression = branch.getKey().toString();
        String keys = shape.encodedCaseKeys();
        for (int successorIndex = 0;
             successorIndex < shape.successorCount(); successorIndex++) {
            Unit originalTarget = shape.successors.get(successorIndex);
            Unit entry = Jimple.v().newNopStmt();
            List<Unit> path = new ArrayList<>();
            path.add(entry);
            beginTraceObservationIsolation(path, observationIsolation);
            path.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(refs.recordSwitchBranch,
                            callId,
                            StringConstant.v(method.getSignature()),
                            IntConstant.v(unitIndex),
                            StringConstant.v(expression),
                            IntConstant.v(successorIndex),
                            StringConstant.v(shape.kind),
                            StringConstant.v(keys))));
            endTraceObservationIsolation(path, observationIsolation);
            path.add(Jimple.v().newGotoStmt(originalTarget));
            for (Unit unit : path) body.getUnits().add(unit);
            if (successorIndex == shape.defaultSuccessorIndex) {
                branch.setDefaultTarget(entry);
            } else {
                branch.setTarget(successorIndex, entry);
            }
        }
        return true;
    }

    private void insertMethodExit(Body body, Stmt returnUnit, Value returnValue,
                                  SootMethodRef exitRef,
                                  ConcolicRegionRefs observationIsolation) {
        List<Unit> units = new ArrayList<>();
        beginTraceObservationIsolation(units, observationIsolation);
        Value objectValue = objectArg(body, returnValue, units);
        Value primitiveValue = primitiveValueString(body, returnValue, units);
        units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                exitRef, objectValue, primitiveValue)));
        endTraceObservationIsolation(units, observationIsolation);
        insertBeforeSequence(body, returnUnit, units);
    }

    private static void beginTraceObservationIsolation(
            List<Unit> units, ConcolicRegionRefs isolation) {
        if (isolation != null) {
            units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                    isolation.pauseObservation)));
        }
    }

    private static void endTraceObservationIsolation(
            List<Unit> units, ConcolicRegionRefs isolation) {
        if (isolation != null) {
            units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                    isolation.resumeObservation)));
        }
    }

    private void addActiveThrowHandler(Body body, Unit start,
                                       SootMethodRef throwRef) {
        addActiveThrowHandler(body, start, throwRef, null, null);
    }

    private void addActiveThrowHandler(Body body, Unit start,
                                       SootMethodRef throwRef,
                                       SootMethodRef pauseObservation,
                                       SootMethodRef resumeObservation) {
        if (start == null) {
            return;
        }
        SootClass throwableClass = Scene.v().getSootClass("java.lang.Throwable");
        Local caught = newTraceLocal(body, RefType.v("java.lang.Throwable"),
                "$causynthThrown");
        Unit handler = Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef());
        Unit pause = pauseObservation == null ? null
                : Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                pauseObservation));
        Unit record = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                throwRef, caught));
        Unit resume = resumeObservation == null ? null
                : Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                resumeObservation));
        Unit rethrow = Jimple.v().newThrowStmt(caught);
        body.getUnits().add(handler);
        if (pause != null) {
            body.getUnits().add(pause);
        }
        body.getUnits().add(record);
        if (resume != null) {
            body.getUnits().add(resume);
        }
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

    private static void insertBeforeOrAppend(Body body, Unit anchor,
                                             List<Unit> units) {
        if (anchor == null) {
            for (Unit unit : units) {
                body.getUnits().add(unit);
            }
            return;
        }
        insertBeforeSequence(body, anchor, units);
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

    private int instrumentFieldTrace(Body body, SootMethod method,
                                     SootMethodRef recordFieldRef,
                                     TraceFieldSelection traceFields,
                                     List<Unit> units,
                                     ConcolicRegionRefs observationIsolation) {
        int count = 0;
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
        for (int unitIndex = 0; unitIndex < units.size(); unitIndex++) {
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
                    count += insertFieldTrace(body, unit, recordFieldRef, "FIELD_WRITE",
                            method.getSignature(), unitIndex, (FieldRef) left,
                            methodReceiver, right, true, traceFields,
                            observationIsolation);
                }
                if (right instanceof FieldRef) {
                    count += insertFieldTrace(body, unit, recordFieldRef, "FIELD_READ",
                            method.getSignature(), unitIndex, (FieldRef) right,
                            methodReceiver, left, true, traceFields,
                            observationIsolation);
                }
            } else {
                for (ValueBox box : stmt.getUseBoxes()) {
                    Value value = box.getValue();
                    if (value instanceof FieldRef) {
                        count += insertFieldTrace(body, unit, recordFieldRef, "FIELD_READ",
                                method.getSignature(), unitIndex, (FieldRef) value,
                                methodReceiver, value, false, traceFields,
                                observationIsolation);
                    }
                }
            }
        }
        return count;
    }

    private int insertFieldTrace(Body body, Unit unit, SootMethodRef recordFieldRef,
                                 String kind, String method, int unitIndex,
                                 FieldRef fieldRef, Value methodReceiverValue,
                                 Value value,
                                 boolean fieldValueIsReadValue,
                                 TraceFieldSelection traceFields,
                                 ConcolicRegionRefs observationIsolation) {
        String field = fieldRef.getFieldRef().getSignature();
        if (!shouldInstrumentField(field, traceFields)) {
            return 0;
        }
        List<Unit> prefixUnits = new ArrayList<>();
        beginTraceObservationIsolation(prefixUnits, observationIsolation);
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
        endTraceObservationIsolation(prefixUnits, observationIsolation);
        if (fieldValueIsReadValue || "FIELD_WRITE".equals(kind)) {
            insertAfterSequence(body, unit, prefixUnits);
        } else {
            insertBeforeSequence(body, unit, prefixUnits);
        }
        return 1;
    }

    private static boolean shouldInstrumentField(String field,
                                                 TraceFieldSelection traceFields) {
        if (field == null || traceFields == null || traceFields.isEmpty()) {
            return false;
        }
        if (traceFields.signatures.contains(field)) {
            return true;
        }
        String fieldName = fieldNameFromSignature(field);
        return !fieldName.isEmpty() && traceFields.names.contains(fieldName);
    }

    private static TraceFieldSelection traceFieldSelection(
            CausynthAnalysisResult result) {
        TraceFieldSelection selection = new TraceFieldSelection();
        for (Map<String, Object> edge : result.edges) {
            collectTraceFields(selection, String.valueOf(edge.get("fromCell")));
            collectTraceFields(selection, String.valueOf(edge.get("toCell")));
            collectTraceFields(selection, String.valueOf(edge.get("objectFromCell")));
            collectTraceFields(selection, String.valueOf(edge.get("objectToCell")));
            collectFieldPathNames(selection, String.valueOf(edge.get("fieldPath")));
        }
        return selection;
    }

    private static void collectTraceFields(TraceFieldSelection selection, String cell) {
        if (cell == null || cell.isEmpty() || "null".equals(cell)) {
            return;
        }
        Matcher field = Pattern.compile("<[^:]+:\\s+[^()<>]+\\s+[^\\s()>]+>")
                .matcher(cell);
        while (field.find()) {
            String signature = field.group();
            if (parseMethodSig(signature) != null) {
                continue;
            }
            selection.signatures.add(signature);
            String fieldName = fieldNameFromSignature(signature);
            if (!fieldName.isEmpty()) {
                selection.names.add(fieldName);
            }
        }
        collectFieldPathNames(selection, cell);
    }

    private static void collectFieldPathNames(TraceFieldSelection selection, String text) {
        if (text == null || text.isEmpty() || "null".equals(text)) {
            return;
        }
        Matcher matcher = Pattern.compile("#field:([^#@]+)").matcher(text);
        while (matcher.find()) {
            String name = matcher.group(1).trim();
            if (!name.isEmpty()) {
                selection.names.add(name);
            }
        }
    }

    private static String fieldNameFromSignature(String fieldSignature) {
        if (fieldSignature == null) {
            return "";
        }
        Matcher matcher = Pattern.compile("<[^:]+:\\s+.+\\s+([^\\s>]+)>")
                .matcher(fieldSignature);
        return matcher.find() ? matcher.group(1) : "";
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

    private static SootMethodRef traceRecorderMethodRef() {
        SootClass recorder = Scene.v().getSootClassUnsafe(TRACE_RECORDER_CLASS);
        if (recorder == null) {
            recorder = new SootClass(TRACE_RECORDER_CLASS, Modifier.PUBLIC);
            recorder.setPhantomClass();
            Scene.v().addClass(recorder);
        }
        return Scene.v().makeMethodRef(recorder, "record",
                Arrays.asList(RefType.v("java.lang.String"), RefType.v("java.lang.Object")),
                VoidType.v(), true);
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

    private static SootClass traceRecorderClass() {
        SootClass recorder = Scene.v().getSootClassUnsafe(TRACE_RECORDER_CLASS);
        if (recorder == null) {
            recorder = new SootClass(TRACE_RECORDER_CLASS, Modifier.PUBLIC);
            recorder.setPhantomClass();
            Scene.v().addClass(recorder);
        }
        return recorder;
    }

    private static final class RichTraceRefs {
        private final SootMethodRef enterMethod;
        private final SootMethodRef recordMethodArgument;
        private final SootMethodRef beginCall;
        private final SootMethodRef recordCallArgument;
        private final SootMethodRef endCall;
        private final SootMethodRef recordBranch;
        private final SootMethodRef recordSwitchBranch;
        private final SootMethodRef exitMethod;
        private final SootMethodRef throwMethod;

        private RichTraceRefs(SootMethodRef enterMethod,
                              SootMethodRef recordMethodArgument,
                              SootMethodRef beginCall,
                              SootMethodRef recordCallArgument,
                              SootMethodRef endCall,
                              SootMethodRef recordBranch,
                              SootMethodRef recordSwitchBranch,
                              SootMethodRef exitMethod,
                              SootMethodRef throwMethod) {
            this.enterMethod = enterMethod;
            this.recordMethodArgument = recordMethodArgument;
            this.beginCall = beginCall;
            this.recordCallArgument = recordCallArgument;
            this.endCall = endCall;
            this.recordBranch = recordBranch;
            this.recordSwitchBranch = recordSwitchBranch;
            this.exitMethod = exitMethod;
            this.throwMethod = throwMethod;
        }

        private static RichTraceRefs create() {
            SootClass recorder = traceRecorderClass();
            Type string = RefType.v("java.lang.String");
            Type object = RefType.v("java.lang.Object");
            return new RichTraceRefs(
                    Scene.v().makeMethodRef(recorder, "enterMethod",
                            Arrays.asList(string, object), LongType.v(), true),
                    Scene.v().makeMethodRef(recorder, "recordMethodArgument",
                            Arrays.asList(LongType.v(), IntType.v(), string,
                                    object, string), VoidType.v(), true),
                    Scene.v().makeMethodRef(recorder, "beginCall",
                            Arrays.asList(LongType.v(), string, IntType.v(),
                                    string, object), LongType.v(), true),
                    Scene.v().makeMethodRef(recorder, "recordCallArgument",
                            Arrays.asList(LongType.v(), IntType.v(), string,
                                    object, string), VoidType.v(), true),
                    Scene.v().makeMethodRef(recorder, "endCall",
                            Arrays.asList(LongType.v(), object, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(recorder, "recordBranch",
                            Arrays.asList(LongType.v(), string, IntType.v(),
                                    string, BooleanType.v()), VoidType.v(), true),
                    Scene.v().makeMethodRef(recorder, "recordSwitchBranch",
                            Arrays.asList(LongType.v(), string, IntType.v(),
                                    string, IntType.v(), string, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(recorder, "exitActiveMethod",
                            Arrays.asList(object, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(recorder, "throwActiveMethod",
                            Collections.singletonList(
                                    RefType.v("java.lang.Throwable")),
                            VoidType.v(), true));
        }
    }

    private static final class ConcolicRegionRefs {
        private final SootMethodRef enterRegionFrame;
        private final SootMethodRef enterAccessorCallContext;
        private final SootMethodRef exitAccessorCallContext;
        private final SootMethodRef materializeArgument;
        private final SootMethodRef symbolizeArgument;
        private final SootMethodRef materializeReference;
        private final SootMethodRef materializePrimitive;
        private final SootMethodRef materializeStaticPrimitiveField;
        private final SootMethodRef materializeField;
        private final SootMethodRef prepareFieldMaterialization;
        private final SootMethodRef materializeConsumedField;
        private final SootMethodRef materializeReplayReferenceResult;
        private final SootMethodRef registerMapView;
        private final SootMethodRef registerMapViewIterator;
        private final SootMethodRef recordMapIteratorNext;
        private final SootMethodRef recordMapIteratorRemove;
        private final SootMethodRef recordOutputCapture;
        private final SootMethodRef activeToken;
        private final SootMethodRef recordFieldAssignmentOutput;
        private final SootMethodRef pauseObservation;
        private final SootMethodRef resumeObservation;
        private final SootMethodRef pauseVmPathCondition;
        private final SootMethodRef resumeVmPathCondition;
        private final SootMethodRef prepareBranch;
        private final SootMethodRef markConcolicBranch;
        private final SootMethodRef resolveBranch;
        private final SootMethodRef resolveSwitchBranch;
        private final SootMethodRef exitRegionFrame;
        private final SootMethodRef throwRegionFrame;

        private ConcolicRegionRefs(SootMethodRef enterRegionFrame,
                                   SootMethodRef enterAccessorCallContext,
                                   SootMethodRef exitAccessorCallContext,
                                   SootMethodRef materializeArgument,
                                   SootMethodRef symbolizeArgument,
                                   SootMethodRef materializeReference,
                                   SootMethodRef materializePrimitive,
                                   SootMethodRef materializeStaticPrimitiveField,
                                   SootMethodRef materializeField,
                                   SootMethodRef prepareFieldMaterialization,
                                   SootMethodRef materializeConsumedField,
                                   SootMethodRef materializeReplayReferenceResult,
                                   SootMethodRef registerMapView,
                                   SootMethodRef registerMapViewIterator,
                                   SootMethodRef recordMapIteratorNext,
                                   SootMethodRef recordMapIteratorRemove,
                                   SootMethodRef recordOutputCapture,
                                   SootMethodRef activeToken,
                                   SootMethodRef recordFieldAssignmentOutput,
                                   SootMethodRef pauseObservation,
                                   SootMethodRef resumeObservation,
                                   SootMethodRef pauseVmPathCondition,
                                   SootMethodRef resumeVmPathCondition,
                                   SootMethodRef prepareBranch,
                                   SootMethodRef markConcolicBranch,
                                   SootMethodRef resolveBranch,
                                   SootMethodRef resolveSwitchBranch,
                                   SootMethodRef exitRegionFrame,
                                   SootMethodRef throwRegionFrame) {
            this.enterRegionFrame = enterRegionFrame;
            this.enterAccessorCallContext = enterAccessorCallContext;
            this.exitAccessorCallContext = exitAccessorCallContext;
            this.materializeArgument = materializeArgument;
            this.symbolizeArgument = symbolizeArgument;
            this.materializeReference = materializeReference;
            this.materializePrimitive = materializePrimitive;
            this.materializeStaticPrimitiveField =
                    materializeStaticPrimitiveField;
            this.materializeField = materializeField;
            this.prepareFieldMaterialization = prepareFieldMaterialization;
            this.materializeConsumedField = materializeConsumedField;
            this.materializeReplayReferenceResult =
                    materializeReplayReferenceResult;
            this.registerMapView = registerMapView;
            this.registerMapViewIterator = registerMapViewIterator;
            this.recordMapIteratorNext = recordMapIteratorNext;
            this.recordMapIteratorRemove = recordMapIteratorRemove;
            this.recordOutputCapture = recordOutputCapture;
            this.activeToken = activeToken;
            this.recordFieldAssignmentOutput =
                    recordFieldAssignmentOutput;
            this.pauseObservation = pauseObservation;
            this.resumeObservation = resumeObservation;
            this.pauseVmPathCondition = pauseVmPathCondition;
            this.resumeVmPathCondition = resumeVmPathCondition;
            this.prepareBranch = prepareBranch;
            this.markConcolicBranch = markConcolicBranch;
            this.resolveBranch = resolveBranch;
            this.resolveSwitchBranch = resolveSwitchBranch;
            this.exitRegionFrame = exitRegionFrame;
            this.throwRegionFrame = throwRegionFrame;
        }

        private static ConcolicRegionRefs create() {
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
            return new ConcolicRegionRefs(
                    Scene.v().makeMethodRef(runtime, "enterRegionFrame",
                            Arrays.asList(string, object,
                                    ArrayType.v(object, 1)),
                            LongType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "enterAccessorCallContext",
                            Arrays.asList(string, IntType.v(), string,
                                    string, object), LongType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "exitAccessorCallContext",
                            Collections.<Type>singletonList(LongType.v()),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "materializeArgument",
                            Arrays.asList(LongType.v(), IntType.v(), object,
                                    string), object, true),
                    Scene.v().makeMethodRef(runtime, "symbolizeArgument",
                            Arrays.asList(LongType.v(), IntType.v(), object, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "materializeReference",
                            Arrays.asList(string, string, object),
                            object, true),
                    Scene.v().makeMethodRef(runtime, "materializePrimitive",
                            Arrays.asList(string, string, object),
                            object, true),
                    Scene.v().makeMethodRef(runtime,
                            "materializeStaticPrimitiveField",
                            Arrays.asList(string, IntType.v(), string, string,
                                    object), object, true),
                    Scene.v().makeMethodRef(runtime, "materializeField",
                            Arrays.asList(string, IntType.v(), object, string,
                                    string), VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "prepareFieldMaterialization",
                            Arrays.asList(string, IntType.v(), object, string,
                                    string), VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "materializeConsumedField",
                            Arrays.asList(string, IntType.v(), object, string,
                                    string, object), VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "materializeReplayReferenceResult",
                            Arrays.asList(string, IntType.v(), object),
                            object, true),
                    Scene.v().makeMethodRef(runtime, "registerMapView",
                            Arrays.asList(string, IntType.v(), object, object,
                                    string), VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "registerMapViewIterator",
                            Arrays.asList(string, IntType.v(), object, object),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "recordMapIteratorNext",
                            Arrays.asList(string, IntType.v(), object, object),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "recordMapIteratorRemove",
                            Arrays.asList(string, IntType.v(), object),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "recordOutputCapture",
                            Arrays.asList(string, IntType.v(), string, string,
                                    IntType.v(), string, string, string,
                                    IntType.v(), object, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "activeToken",
                            Collections.<Type>emptyList(), LongType.v(), true),
                    Scene.v().makeMethodRef(runtime,
                            "recordFieldAssignmentOutput",
                            Arrays.asList(LongType.v(), string, IntType.v(),
                                    string, string, string, string, string,
                                    IntType.v(), object, object, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "pauseObservation",
                            Collections.<Type>emptyList(), VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "resumeObservation",
                            Collections.<Type>emptyList(), VoidType.v(), true),
                    Scene.v().makeMethodRef(system,
                            "pauseConcolicPathCondition",
                            Collections.<Type>emptyList(), VoidType.v(), true),
                    Scene.v().makeMethodRef(system,
                            "resumeConcolicPathCondition",
                            Collections.<Type>emptyList(), VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "prepareBranch",
                            Arrays.asList(string, IntType.v(), string),
                            LongType.v(), true),
                    Scene.v().makeMethodRef(system, "markConcolicBranch",
                            Arrays.asList(string, IntType.v()),
                            LongType.v(), true),
                    Scene.v().makeMethodRef(runtime, "resolveBranch",
                            Arrays.asList(LongType.v(), LongType.v(), string,
                                    IntType.v(), string,
                                    BooleanType.v()), BooleanType.v(), true),
                    Scene.v().makeMethodRef(runtime, "resolveSwitchBranch",
                            Arrays.asList(LongType.v(), LongType.v(), string,
                                    IntType.v(), string, string, string,
                                    IntType.v()), IntType.v(), true),
                    Scene.v().makeMethodRef(runtime, "exitRegionFrame",
                            Arrays.asList(string, object, string),
                            VoidType.v(), true),
                    Scene.v().makeMethodRef(runtime, "throwRegionFrame",
                            Arrays.asList(string,
                                    RefType.v("java.lang.Throwable")),
                            VoidType.v(), true));
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

    private static final class TraceSiteSelection {
        private final Set<String> relevantMethods = new LinkedHashSet<>();
        private final Map<String, Set<Integer>> callUnits = new LinkedHashMap<>();
        private final Map<String, Set<Integer>> branchUnits = new LinkedHashMap<>();

        private void add(Map<String, Set<Integer>> sites, String method,
                         int unitIndex) {
            sites.computeIfAbsent(method, ignored -> new LinkedHashSet<>())
                    .add(unitIndex);
        }

        private Set<Integer> units(Map<String, Set<Integer>> sites,
                                   String method) {
            Set<Integer> values = sites.get(method);
            return values == null ? Collections.emptySet() : values;
        }
    }

    private static final class RichInstrumentationStats {
        private int callSites;
        private int branches;
    }

    private static final class TraceFieldSelection {
        private final Set<String> signatures = new LinkedHashSet<>();
        private final Set<String> names = new LinkedHashSet<>();

        private boolean isEmpty() {
            return signatures.isEmpty() && names.isEmpty();
        }
    }


    private static final class MethodSig {
        private final String raw;
        private final String owner;
        private final String returnType;
        private final String name;
        private final List<String> params;

        private MethodSig(String raw, String owner, String returnType,
                          String name, List<String> params) {
            this.raw = raw;
            this.owner = owner;
            this.returnType = returnType;
            this.name = name;
            this.params = params;
        }
    }

    private static MethodSig parseMethodSig(String raw) {
        if (raw == null || !raw.startsWith("<")) {
            return null;
        }
        Matcher matcher = Pattern.compile("<([^:]+):\\s+(.+)\\s+([^\\s(]+)\\((.*)\\)>")
                .matcher(raw);
        if (!matcher.find()) {
            return null;
        }
        String paramsText = matcher.group(4).trim();
        List<String> params = paramsText.isEmpty()
                ? Collections.emptyList()
                : Arrays.asList(paramsText.split("\\s*,\\s*"));
        return new MethodSig(raw, matcher.group(1), matcher.group(2),
                matcher.group(3), params);
    }

    private static String ownerOf(String methodSignature) {
        MethodSig sig = parseMethodSig(methodSignature);
        return sig == null ? "" : sig.owner;
    }

    private static void buildAutomaticDerivationBoundary(
            CausynthAnalysisResult result) {
        Map<String, Object> boundary = result.automaticDerivationBoundary;
        boundary.put("schemaVersion", 1);
        boundary.put("kind", "AUTOMATIC_DERIVATION_BOUNDARY");
        boundary.put("complete", true);
        boundary.put("domainSemanticAdapterUsed", false);
        boundary.put("automaticEqualityAuthority",
                "RUNTIME_COMPLETE_VALUE_FINGERPRINT_ONLY");
        boundary.put("automaticStateAuthority",
                "RUNTIME_CONFIRMED_WRITE_READ_PAIR_ONLY");
        boundary.put("scope", stringValue(result.targetResolved.get(
                "analysisScope")));
        result.slices.put("automaticDerivationBoundary", boundary);
    }

    private static String stableSiteId(String method, int unitIndex, String kind) {
        if (unitIndex >= 0) {
            return method + "#u" + unitIndex;
        }
        return method + "#synthetic:" + firstNonBlank(kind, "edge");
    }

    private static String stringValue(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static int intValue(Object value, int fallback) {
        if (value instanceof Number) {
            return ((Number) value).intValue();
        }
        try {
            return Integer.parseInt(String.valueOf(value));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String lower(String value) {
        return value == null ? "" : value.toLowerCase(Locale.ROOT);
    }

    private static List<String> sortedLimited(Set<String> values, int limit) {
        List<String> sorted = new ArrayList<>(values);
        Collections.sort(sorted);
        if (sorted.size() <= limit) {
            return sorted;
        }
        return new ArrayList<>(sorted.subList(0, limit));
    }

    private static Map<String, Object> summarizeEdgeKinds(List<Map<String, Object>> edges) {
        Map<String, Object> counts = object();
        for (Map<String, Object> edge : edges) {
            String kind = String.valueOf(edge.get("kind"));
            Object previous = counts.get(kind);
            counts.put(kind, previous instanceof Number
                    ? ((Number) previous).intValue() + 1 : 1);
        }
        return counts;
    }

    private static String cellKind(String cell) {
        if (cell.contains("#exception:")) {
            return "exception";
        }
        if (cell.contains(".param")) {
            return "parameter";
        }
        if (cell.endsWith(".return")) {
            return "return";
        }
        if (cell.contains("#u")) {
            return "unit";
        }
        if (cell.startsWith("<") && cell.contains(":")) {
            return cell.contains(" ") ? "field_or_method" : "signature";
        }
        if (cell.contains("::")) {
            return "local";
        }
        return "seed";
    }

    @SafeVarargs
    private static <T> List<T> concat(Collection<T>... lists) {
        List<T> result = new ArrayList<>();
        for (Collection<T> list : lists) {
            result.addAll(list);
        }
        return result;
    }

    private static boolean containsAny(String value, Collection<String> needles) {
        if (value == null) {
            return false;
        }
        for (String needle : needles) {
            if (needle != null && !needle.isEmpty() && value.contains(needle)) {
                return true;
            }
        }
        return false;
    }

    private static boolean containsAll(String value, Collection<String> needles) {
        if (value == null) {
            return false;
        }
        for (String needle : needles) {
            if (needle != null && !needle.isEmpty() && !value.contains(needle)) {
                return false;
            }
        }
        return true;
    }

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) {
                return value.trim();
            }
        }
        return null;
    }

    private static Map<String, Object> object(Object... keyValues) {
        Map<String, Object> map = new LinkedHashMap<>();
        for (int i = 0; i + 1 < keyValues.length; i += 2) {
            map.put(String.valueOf(keyValues[i]), keyValues[i + 1]);
        }
        return map;
    }
}
