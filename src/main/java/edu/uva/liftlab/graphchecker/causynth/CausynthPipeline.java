package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.AccessorCallTarget;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ConcolicBranchSelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.ConcolicMaterializationSelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.InstrumentationPlan;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.RootedOutputCapture;
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
import soot.SootField;
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
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.SwitchStmt;
import soot.tagkit.Tag;

import java.io.IOException;
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.firstNonBlank;
import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.intValue;
import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.stringValue;
import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;

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
    private static final Pattern TRACE_FIELD_SIGNATURE = Pattern.compile(
            "<[^:]+:\\s+[^()<>]+\\s+[^\\s()>]+>");
    private static final Pattern FIELD_PATH_NAME =
            Pattern.compile("#field:([^#@]+)");
    private static final Pattern FIELD_NAME = Pattern.compile(
            "<[^:]+:\\s+.+\\s+([^\\s>]+)>");
    private static final Pattern METHOD_SIGNATURE = Pattern.compile(
            "<[^:]+:\\s+.+\\s+[^\\s(]+\\((.*)\\)>");
    private final GraphCheckerOptions options;
    private final Map<SootField, SootMethod> exitFieldReaders =
            new IdentityHashMap<>();

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
        StaticProgram result =
                new SeedBackwardStaticAnalyzer(target).analyze();
        SymbolicRegionPlanner.plan(result);
        boolean concolicEnabled = concolicInstrumentationEnabled();
        instrumentRuntimeTrace(result, concolicEnabled);
        boolean boundedOutputClosureCoverageReady =
                concolicEnabled && instrumentConcolicRegions();
        if (!concolicEnabled) {
            CausynthArtifactWriter.write(target.outputDir, result);
        }
        enforceSymbolicCoverage(result, boundedOutputClosureCoverageReady);
        if (concolicEnabled) {
            LOG.info("Seed backward analysis completed for concolic "
                    + "instrumentation without duplicating static artifacts");
        } else {
            LOG.info("Seed backward analysis wrote {} edges to {}",
                    result.edges.size(), target.outputDir);
        }
    }

    private void enforceSymbolicCoverage(StaticProgram result,
                                         boolean boundedOutputClosureCoverageReady) {
        boolean strictCoverage = Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.coverage.strict"),
                System.getenv("CAUSYNTH_COVERAGE_STRICT"),
                "true"));
        if (strictCoverage
                && !result.coverageComplete
                && !boundedOutputClosureCoverageReady) {
            throw new IllegalStateException(
                    "Incomplete symbolic-region coverage");
        }
        if (strictCoverage
                && !result.coverageComplete) {
            LOG.info("Global symbolic-region coverage is incomplete, but the "
                            + "exact runtime-selected bounded output closure is "
                            + "ready; preserving strict coverage outside that "
                            + "selected activation");
        }
    }

    private void instrumentRuntimeTrace(StaticProgram result,
                                        boolean concolicEnabled) {
        if (!Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.instrument.trace"),
                System.getenv("CAUSYNTH_INSTRUMENT_TRACE"),
                "false"))) {
            return;
        }
        SootMethodRef recordRef = traceRecorderMethodRef();
        SootMethodRef recordFieldRef = traceRecorderFieldMethodRef();
        HookCatalog richRefs = HookCatalog.trace();
        HookCatalog observationIsolation =
                concolicEnabled ? HookCatalog.concolic() : null;
        TraceSelection traceSelection = traceSelection(result);
        for (String signature : result.traceMethods) {
            try {
                SootMethod method = Scene.v().getMethod(signature);
                if (method == null || !method.isConcrete()) {
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
                if (traceSelection.relevantMethods.contains(signature)) {
                    instrumentRichMethod(body, method,
                            originalUnits, insertionPoint, lowerBound, receiver,
                            traceSelection,
                            richRefs, observationIsolation);
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
                instrumentFieldTrace(body, method, recordFieldRef,
                        traceSelection, originalUnits, lowerBound,
                        observationIsolation);
            } catch (RuntimeException exception) {
                LOG.debug("Skipping trace instrumentation for {}", signature, exception);
            }
        }
        LOG.info("Instrumented selected methods for runtime trace");
    }

    /**
     * Inserts region hooks at the roots selected by the runtime activation
     * plan. Concolic instrumentation without that plan is not executable.
     */
    private boolean instrumentConcolicRegions() {
        HookCatalog refs = HookCatalog.concolic();
        InstrumentationPlan plan = ConcolicInstrumentationSelections
                .instrumentationPlanFromEnvironment();
        ConcolicBranchSelection branchSelection = plan.branches();
        ConcolicMaterializationSelection materializationSelection =
                plan.materializations();
        List<RootedOutputCapture> outputCaptureSelection =
                plan.outputCaptures();
        String outputCaptureReceiverClass = plan.receiverClass();
        String signature = plan.rootMethod();
        Set<String> instrumentationMethods =
                new LinkedHashSet<>(plan.instrumentationMethods());
        Set<String> taggedMethods = new LinkedHashSet<>(branchSelection.methods());
        taggedMethods.addAll(materializationSelection.localMethods());
        taggedMethods.addAll(materializationSelection.accessorCallerMethods());
        taggedMethods.addAll(instrumentationMethods);
        for (String methodSignature : taggedMethods) {
            try {
                SootMethod method = Scene.v().getMethod(methodSignature);
                if (method != null && method.isConcrete()) {
                    tagOriginalUnits(snapshotUnits(method.retrieveActiveBody()));
                }
            } catch (RuntimeException ignored) {
            }
        }
        try {
            SootMethod method = Scene.v().getMethod(signature);
            if (method == null || !method.isConcrete()) {
                throw new IllegalStateException(
                        "Selected concolic root is not a concrete method: "
                                + signature);
            }
            Body body = method.retrieveActiveBody();
            List<Unit> originalUnits = snapshotUnits(body);
            tagOriginalUnits(originalUnits);
            Unit insertionPoint = safeInstrumentationEntry(body, method);
            if (method.isConstructor() && insertionPoint == null) {
                throw new IllegalStateException(
                        "Selected constructor root has no initialized-this "
                                + "instrumentation point: " + signature);
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
                    Jimple.v().newStaticInvokeExpr(
                            refs.ref(Hook.ENTER_REGION_FRAME),
                            StringConstant.v(signature), receiver,
                            rootArguments));
            entry.add(enterRegion);
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
                            refs.ref(Hook.MATERIALIZE_ARGUMENT),
                            refs.ref(Hook.PAUSE_OBSERVATION),
                            refs.ref(Hook.RESUME_OBSERVATION));
                } else {
                    Value objectValue = objectArg(body, parameter, entry);
                    Local modeled = newTraceLocal(body,
                            RefType.v("java.lang.Object"),
                            "$causynthArgumentModel");
                    entry.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.PAUSE_OBSERVATION))));
                    entry.add(Jimple.v().newAssignStmt(modeled,
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.MATERIALIZE_ARGUMENT), token,
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
                    entry.add(Jimple.v().newAssignStmt(parameter,
                            converted));
                    entry.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.PAUSE_OBSERVATION))));
                    entry.add(Jimple.v().newInvokeStmt(
                            Jimple.v().newStaticInvokeExpr(
                                    refs.ref(Hook.SYMBOLIZE_ARGUMENT), token,
                                    IntConstant.v(index), parameter,
                                    primitiveValue)));
                    entry.add(Jimple.v().newInvokeStmt(
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
                            + signature, exception);
        }
        instrumentConcolicAccessorCallContexts(materializationSelection, refs);
        instrumentConcolicFieldWrites(instrumentationMethods,
                materializationSelection, refs);
        instrumentConcolicMaterializations(materializationSelection, refs);
        instrumentConcolicBranches(branchSelection, refs);
        LOG.info("Instrumented symbolic-region root {} for concolic replay",
                signature);
        return plan.boundedOutputClosureCoverageReady();
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
                            refs.ref(Hook.MATERIALIZE_FIELD),
                            StringConstant.v(target.implementationMethod),
                            IntConstant.v(-1), receiver,
                            StringConstant.v(target.fieldSignature),
                            StringConstant.v(target.fieldName))));
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

    private static TraceSelection traceSelection(
            StaticProgram result) {
        TraceSelection selection = new TraceSelection();
        for (Map<String, Object> edge : result.edges) {
            String method = stringValue(edge.get("method"));
            int unitIndex = intValue(edge.get("unitIndex"), -1);
            if (!method.isEmpty()) {
                selection.relevantMethods.add(method);
                if (unitIndex >= 0) {
                    String invoke = stringValue(edge.get("invoke"));
                    String transfer = stringValue(edge.get("transferKind"));
                    if (!invoke.isEmpty()) {
                        selection.callUnits.computeIfAbsent(method,
                                ignored -> new LinkedHashSet<>()).add(
                                unitIndex);
                    }
                    if ("GUARD".equals(transfer)) {
                        selection.branchUnits.computeIfAbsent(method,
                                ignored -> new LinkedHashSet<>()).add(
                                unitIndex);
                    }
                }
            }
            collectTraceFields(selection, String.valueOf(edge.get(
                    "fromCell")));
            collectTraceFields(selection, String.valueOf(edge.get(
                    "toCell")));
            collectTraceFields(selection, String.valueOf(edge.get(
                    "objectFromCell")));
            collectTraceFields(selection, String.valueOf(edge.get(
                    "objectToCell")));
            collectFieldPathNames(selection, String.valueOf(edge.get(
                    "fieldPath")));
        }
        return selection;
    }

    private void instrumentRichMethod(
            Body body, SootMethod method, List<Unit> originalUnits,
            Unit insertionPoint, Unit lowerBound, Value receiver,
            TraceSelection sites,
            HookCatalog refs, HookCatalog observationIsolation) {
        Local callId = newTraceLocal(body, LongType.v(), "$causynthCallId");
        List<Unit> entryUnits = new ArrayList<>();
        beginTraceObservationIsolation(entryUnits, observationIsolation);
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
        endTraceObservationIsolation(entryUnits, observationIsolation);
        insertBeforeOrAppendNoRedirect(body, insertionPoint, entryUnits);

        Set<Integer> callUnits = sites.units(sites.callUnits, method.getSignature());
        Set<Integer> branchUnits = sites.units(sites.branchUnits, method.getSignature());
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
            if (callUnits.contains(unitIndex) && stmt.containsInvokeExpr()
                    && !isRecorderInvoke(stmt.getInvokeExpr())) {
                instrumentCallSite(body, method, stmt, unitIndex, callId,
                        refs, observationIsolation);
            }
            if (branchUnits.contains(unitIndex)) {
                if (stmt instanceof IfStmt) {
                    instrumentBranch(body, method, (IfStmt) stmt, unitIndex,
                            callId, refs, observationIsolation);
                } else if (stmt instanceof SwitchStmt) {
                    instrumentSwitchBranch(body, method,
                            (SwitchStmt) stmt, unitIndex, callId, refs,
                            observationIsolation);
                }
            }
            if (stmt instanceof ReturnStmt) {
                insertMethodExit(body, stmt, ((ReturnStmt) stmt).getOp(),
                        refs.ref(Hook.EXIT_ACTIVE_METHOD), observationIsolation);
            } else if (stmt instanceof ReturnVoidStmt) {
                insertMethodExit(body, stmt, NullConstant.v(),
                        refs.ref(Hook.EXIT_ACTIVE_METHOD), observationIsolation);
            }
        }
        addActiveThrowHandler(body, insertionPoint,
                refs.ref(Hook.THROW_ACTIVE_METHOD),
                observationIsolation == null ? null
                        : observationIsolation.ref(Hook.PAUSE_OBSERVATION),
                observationIsolation == null ? null
                        : observationIsolation.ref(Hook.RESUME_OBSERVATION));
    }

    private void instrumentCallSite(Body body, SootMethod method, Stmt stmt,
                                    int unitIndex, Local ownerCallId,
                                    HookCatalog refs,
                                    HookCatalog observationIsolation) {
        InvokeExpr invoke = stmt.getInvokeExpr();
        List<Unit> before = new ArrayList<>();
        beginTraceObservationIsolation(before, observationIsolation);
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
        endTraceObservationIsolation(before, observationIsolation);
        insertBeforeSequence(body, stmt, before);

        Value returnValue = runtimeCallSiteReturnValue(stmt, invoke);
        List<Unit> after = new ArrayList<>();
        beginTraceObservationIsolation(after, observationIsolation);
        Value returnObject = objectArg(body, returnValue, after);
        Value primitiveReturn = primitiveValueString(body, returnValue, after);
        after.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.ref(Hook.END_CALL), invocationId, returnObject,
                primitiveReturn)));
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
                                  HookCatalog refs,
                                  HookCatalog observationIsolation) {
        String expression = branch.getCondition().toString();
        Unit originalTarget = branch.getTarget();
        List<Unit> falsePath = new ArrayList<>();
        beginTraceObservationIsolation(falsePath, observationIsolation);
        Unit falseRecord = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                refs.ref(Hook.RECORD_BRANCH),
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
                refs.ref(Hook.RECORD_BRANCH),
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

    private void instrumentSwitchBranch(
            Body body, SootMethod method, SwitchStmt branch, int unitIndex,
            Local callId, HookCatalog refs,
            HookCatalog observationIsolation) {
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
            beginTraceObservationIsolation(path, observationIsolation);
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
            endTraceObservationIsolation(path, observationIsolation);
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
                                  SootMethodRef exitRef,
                                  HookCatalog observationIsolation) {
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
            List<Unit> units, HookCatalog isolation) {
        if (isolation != null) {
            units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                    isolation.ref(Hook.PAUSE_OBSERVATION))));
        }
    }

    private static void endTraceObservationIsolation(
            List<Unit> units, HookCatalog isolation) {
        if (isolation != null) {
            units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                    isolation.ref(Hook.RESUME_OBSERVATION))));
        }
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

    private void instrumentFieldTrace(Body body, SootMethod method,
                                      SootMethodRef recordFieldRef,
                                      TraceSelection traceFields,
                                      List<Unit> units,
                                      Unit lowerBound,
                                      HookCatalog observationIsolation) {
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
                            methodReceiver, right, true, traceFields,
                            observationIsolation);
                }
                if (right instanceof FieldRef) {
                    insertFieldTrace(body, unit, recordFieldRef, "FIELD_READ",
                            method.getSignature(), unitIndex, (FieldRef) right,
                            methodReceiver, left, true, traceFields,
                            observationIsolation);
                }
            } else {
                for (ValueBox box : stmt.getUseBoxes()) {
                    Value value = box.getValue();
                    if (value instanceof FieldRef) {
                        insertFieldTrace(body, unit, recordFieldRef, "FIELD_READ",
                                method.getSignature(), unitIndex, (FieldRef) value,
                                methodReceiver, value, false, traceFields,
                                observationIsolation);
                    }
                }
            }
        }
    }

    private void insertFieldTrace(
            Body body, Unit unit, SootMethodRef recordFieldRef,
            String kind, String method, int unitIndex,
            FieldRef fieldRef, Value methodReceiverValue, Value value,
            boolean fieldValueIsReadValue,
            TraceSelection traceFields,
            HookCatalog observationIsolation) {
        String field = CausynthStaticFacts.declaredFieldSignature(
                fieldRef.getFieldRef());
        if (!shouldInstrumentField(field, traceFields)) {
            return;
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
    }

    private static boolean shouldInstrumentField(String field,
                                                 TraceSelection traceFields) {
        if (field == null || traceFields == null || traceFields.isEmpty()) {
            return false;
        }
        if (traceFields.signatures.contains(field)) {
            return true;
        }
        String fieldName = fieldNameFromSignature(field);
        return !fieldName.isEmpty() && traceFields.names.contains(fieldName);
    }

    private static void collectTraceFields(TraceSelection selection,
                                           String cell) {
        if (cell == null || cell.isEmpty() || "null".equals(cell)) {
            return;
        }
        Matcher field = TRACE_FIELD_SIGNATURE.matcher(cell);
        while (field.find()) {
            String signature = field.group();
            if (methodSignature(signature)) {
                continue;
            }
            selection.signatures.add(signature);
        }
        collectFieldPathNames(selection, cell);
    }

    private static void collectFieldPathNames(TraceSelection selection,
                                              String text) {
        if (text == null || text.isEmpty() || "null".equals(text)) {
            return;
        }
        Matcher matcher = FIELD_PATH_NAME.matcher(text);
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
        Matcher matcher = FIELD_NAME.matcher(fieldSignature);
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

    private enum Hook {
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
        MATERIALIZE_REFERENCE,
        MATERIALIZE_PRIMITIVE,
        MATERIALIZE_STATIC_PRIMITIVE_FIELD,
        MATERIALIZE_FIELD,
        RECORD_FIELD_WRITE,
        RECORD_REGION_EXIT_FIELD_OUTPUT,
        PAUSE_OBSERVATION,
        RESUME_OBSERVATION,
        PAUSE_VM_PATH_CONDITION,
        RESUME_VM_PATH_CONDITION,
        PREPARE_BRANCH,
        MARK_CONCOLIC_BRANCH,
        RESOLVE_BRANCH,
        RESOLVE_SWITCH_BRANCH,
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
                    .add(Hook.RECORD_FIELD_WRITE, runtime,
                            "recordFieldWrite", VoidType.v(), object, string)
                    .add(Hook.RECORD_REGION_EXIT_FIELD_OUTPUT, runtime,
                            "recordRegionExitFieldOutput", VoidType.v(),
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
        private final Set<String> relevantMethods = new LinkedHashSet<>();
        private final Map<String, Set<Integer>> callUnits = new LinkedHashMap<>();
        private final Map<String, Set<Integer>> branchUnits = new LinkedHashMap<>();
        private final Set<String> signatures = new LinkedHashSet<>();
        private final Set<String> names = new LinkedHashSet<>();

        private Set<Integer> units(Map<String, Set<Integer>> sites,
                                   String method) {
            Set<Integer> values = sites.get(method);
            return values == null ? Collections.emptySet() : values;
        }

        private boolean isEmpty() {
            return signatures.isEmpty() && names.isEmpty();
        }
    }


    private static boolean methodSignature(String value) {
        return value != null && value.startsWith("<")
                && METHOD_SIGNATURE.matcher(value).find();
    }

    private static boolean concolicInstrumentationEnabled() {
        return Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.instrument.concolic"),
                System.getenv("CAUSYNTH_INSTRUMENT_CONCOLIC"),
                "false"));
    }

}
