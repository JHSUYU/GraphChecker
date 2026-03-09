package edu.uva.liftlab.graphchecker.transformer;

import edu.uva.liftlab.graphchecker.analysis.PhaseInfo;
import edu.uva.liftlab.graphchecker.util.ClassFilterHelper;
import edu.uva.liftlab.graphchecker.util.SootUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.*;
import soot.jimple.*;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;

public class GraphCheckerTransformer extends SceneTransformer {

    public static final PhaseInfo PHASE_INFO = new PhaseInfo("wjtp", "transformer method",
            "Inject OTel context propagation at async boundaries",
            true, false);

    private static final Logger LOG = LoggerFactory.getLogger(GraphCheckerTransformer.class);

    private static final String OTEL_CONTEXT_CLASS = "io.opentelemetry.context.Context";
    private static final String BAGGAGE_CLASS = "io.opentelemetry.api.baggage.Baggage";
    private static final String BAGGAGE_BUILDER_CLASS = "io.opentelemetry.api.baggage.BaggageBuilder";
    private static final String SCOPE_CLASS = "io.opentelemetry.context.Scope";
    private static final String TRACE_RECORDER_CLASS = "org.apache.hadoop.hdfs.tracing.TraceRecorder";
    private static final String TRACE_ID_KEY = "traceId";

    /** OTel wrap strategies — only the three natively supported by Context.wrap(). */
    private static final int WRAP_RUNNABLE = 0;
    private static final int WRAP_CALLABLE = 1;
    private static final int WRAP_EXECUTOR = 2;

    /** Logger type names to skip during field access instrumentation. */
    private static final Set<String> LOGGER_TYPES = new HashSet<>(Arrays.asList(
            "org.slf4j.Logger",
            "org.apache.commons.logging.Log",
            "java.util.logging.Logger",
            "org.apache.log4j.Logger",
            "ch.qos.logback.classic.Logger"
    ));

    public String config_file_path;
    public ClassFilterHelper filter;

    /** Cached SootClass for OTel Context. */
    private SootClass otelContextClass;

    /** Counter for generating unique local variable names. */
    private int tempCounter = 0;

    /** Interface->method-name map parsed from the starting point file. */
    private Map<String, Set<String>> startingPointInterfaces = Collections.emptyMap();

    public GraphCheckerTransformer(String config_file_path) {
        this.config_file_path = config_file_path;
        this.filter = new ClassFilterHelper(this.config_file_path);
    }

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        if (!filter.contextPropagationEnabled) {
            LOG.info("Context propagation disabled — nothing to do");
            return;
        }

        otelContextClass = Scene.v().forceResolve(OTEL_CONTEXT_CLASS, SootClass.SIGNATURES);
        loadStartingPointDefinitions();
        LOG.info("OTel context propagation enabled; starting instrumentation phase: {}", phaseName);

        int classCount = 0;
        int asyncMethodCount = 0;
        int startingPointCount = 0;
        int fieldAccessMethodCount = 0;

        for (SootClass sc : new ArrayList<>(Scene.v().getApplicationClasses())) {
            if (shouldSkip(sc)) continue;

            classCount++;
            for (SootMethod sm : new ArrayList<>(sc.getMethods())) {
                if (!sm.isConcrete()) continue;
                try {
                    Body body = sm.retrieveActiveBody();

                    // Phase 1: Starting point trace initiation + TraceRecorder.onTraceStart
                    if (isStartingPointMethod(sc, sm)) {
                        LOG.info("Instrumenting starting point method: {}.{}", sc.getName(), sm.getName());
                        instrumentStartingPoint(body);
                        startingPointCount++;
                    }

                    // Phase 2: Async boundary context wrapping
                    if (instrumentBody(body)) asyncMethodCount++;

                    // Phase 3: Field access instrumentation (state tracing)
                    if (instrumentFieldAccess(body)) fieldAccessMethodCount++;
                } catch (Exception e) {
                    LOG.warn("Failed to instrument {}.{}: {}",
                            sc.getName(), sm.getName(), e.getMessage());
                }
            }
        }

        LOG.info("Instrumentation complete: {} classes, {} async boundaries, {} starting points, {} methods with field tracing",
                classCount, asyncMethodCount, startingPointCount, fieldAccessMethodCount);
    }

    // ========================================================================
    // Skip Logic
    // ========================================================================

    private boolean shouldSkip(SootClass sc) {
        String name = sc.getName();

        // Skip OTel internals
        if (name.startsWith("io.opentelemetry.")) return true;

        // Skip JDK / Soot internals
        if (name.startsWith("java.") || name.startsWith("javax.")
                || name.startsWith("sun.") || name.startsWith("jdk.")
                || name.startsWith("soot.")) {
            return true;
        }

        // Skip TraceRecorder itself (would cause infinite recursion)
        if (name.startsWith("org.apache.hadoop.hdfs.tracing.")) return true;

        // Apply user's filter
        if (filter.isBlackListPilotFuncClass(sc)
                && !filter.isWhiteListPilotFuncClass(sc)) {
            return true;
        }

        return false;
    }

    // ========================================================================
    // Body Instrumentation: Async Boundary Wrapping
    // ========================================================================

    private boolean instrumentBody(Body body) {
        LOG.info("Instrumenting method for async boundaries: {}.{}",
                body.getMethod().getDeclaringClass().getName(),
                body.getMethod().getName());
        PatchingChain<Unit> units = body.getUnits();
        List<Unit> snapshot = new ArrayList<>(units);
        boolean wrapped = false;

        for (Unit u : snapshot) {
            if (!(u instanceof Stmt)) continue;
            Stmt stmt = (Stmt) u;
            if (!stmt.containsInvokeExpr()) continue;

            try {
                if (tryInjectContextPropagation(body, stmt, units)) {
                    wrapped = true;
                }
            } catch (Exception e) {
                LOG.debug("Skip async-boundary injection in {}: {}",
                        body.getMethod().getSignature(), e.getMessage());
            }
        }

        return wrapped;
    }

    // ========================================================================
    // Context Propagation: Async Boundary Detection + Jimple Insertion
    // ========================================================================

    private boolean tryInjectContextPropagation(Body body, Stmt stmt,
                                                PatchingChain<Unit> units) {
        InvokeExpr invoke = stmt.getInvokeExpr();

        String declClass = invoke.getMethod().getDeclaringClass().getName();
        if (declClass.startsWith("io.opentelemetry.")) return false;

        int[] match = detectAsyncBoundary(invoke);
        if (match == null) return false;

        int argIdx   = match[0];
        int strategy = match[1];
        if (argIdx >= invoke.getArgCount()) return false;

        Value arg = invoke.getArg(argIdx);
        if (!(arg instanceof Local)) return false;

        Local wrapped = insertContextWrap(body, (Local) arg, strategy, stmt, units);
        invoke.setArg(argIdx, wrapped);
        LOG.debug("Context-wrapped arg {} of {} in {}",
                argIdx, invoke.getMethod().getSignature(),
                body.getMethod().getSignature());
        return true;
    }

    private int[] detectAsyncBoundary(InvokeExpr invoke) {
        SootMethod m = invoke.getMethod();
        String declClass  = m.getDeclaringClass().getName();
        String methodName = m.getName();
        List<Type> params = m.getParameterTypes();

        if (declClass.equals("java.lang.Thread") && methodName.equals("<init>")
                && !params.isEmpty() && isRunnableType(params.get(0))) {
            return new int[]{0, WRAP_RUNNABLE};
        }

        if (methodName.equals("execute") && params.size() >= 1
                && isRunnableType(params.get(0))) {
            return new int[]{0, WRAP_RUNNABLE};
        }

        if (methodName.equals("submit") && !params.isEmpty()) {
            if (isRunnableType(params.get(0)))  return new int[]{0, WRAP_RUNNABLE};
            if (isCallableType(params.get(0)))  return new int[]{0, WRAP_CALLABLE};
        }

        if ((methodName.equals("schedule")
                || methodName.equals("scheduleAtFixedRate")
                || methodName.equals("scheduleWithFixedDelay"))
                && !params.isEmpty()) {
            if (isRunnableType(params.get(0))) return new int[]{0, WRAP_RUNNABLE};
            if (isCallableType(params.get(0))) return new int[]{0, WRAP_CALLABLE};
        }

        if (declClass.equals("java.util.concurrent.CompletableFuture")
                && methodName.endsWith("Async") && !params.isEmpty()) {
            int last = params.size() - 1;
            if (isExecutorType(params.get(last))) return new int[]{last, WRAP_EXECUTOR};
        }

        if (declClass.contains(".Futures")
                && (methodName.equals("addCallback")
                    || methodName.equals("transformAsync")
                    || methodName.equals("transform"))
                && !params.isEmpty()) {
            int last = params.size() - 1;
            if (isExecutorType(params.get(last))) return new int[]{last, WRAP_EXECUTOR};
        }

        return null;
    }

    private boolean isRunnableType(Type t) {
        return "java.lang.Runnable".equals(t.toString());
    }

    private boolean isCallableType(Type t) {
        return "java.util.concurrent.Callable".equals(t.toString());
    }

    private boolean isExecutorType(Type t) {
        String name = t.toString();
        return "java.util.concurrent.Executor".equals(name)
                || "java.util.concurrent.ExecutorService".equals(name)
                || "java.util.concurrent.ScheduledExecutorService".equals(name);
    }

    private Local insertContextWrap(Body body, Local arg, int strategy,
                                    Unit insertBefore, PatchingChain<Unit> units) {
        RefType ctxType = RefType.v(OTEL_CONTEXT_CLASS);

        Local ctxLocal = newLocal(body, ctxType, "$otelCtx");
        SootMethodRef currentRef = Scene.v().makeMethodRef(
                otelContextClass, "current",
                Collections.<Type>emptyList(), ctxType, true);
        units.insertBefore(
                Jimple.v().newAssignStmt(ctxLocal,
                        Jimple.v().newStaticInvokeExpr(currentRef)),
                insertBefore);

        String wrapTypeName;
        switch (strategy) {
            case WRAP_CALLABLE: wrapTypeName = "java.util.concurrent.Callable"; break;
            case WRAP_EXECUTOR: wrapTypeName = "java.util.concurrent.Executor";  break;
            default:            wrapTypeName = "java.lang.Runnable";             break;
        }
        RefType wrapType = RefType.v(wrapTypeName);

        Local wrappedLocal = newLocal(body, wrapType, "$ctxWrapped");
        SootMethodRef wrapRef = Scene.v().makeMethodRef(
                otelContextClass, "wrap",
                Collections.<Type>singletonList(wrapType), wrapType, false);
        units.insertBefore(
                Jimple.v().newAssignStmt(wrappedLocal,
                        Jimple.v().newInterfaceInvokeExpr(ctxLocal, wrapRef,
                                Collections.<Value>singletonList(arg))),
                insertBefore);

        return wrappedLocal;
    }

    // ========================================================================
    // Starting Point Detection and Trace Initiation
    // ========================================================================

    private void loadStartingPointDefinitions() {
        String filePath = null;
        for (String s : filter.startingPointFile) {
            if (s != null && !s.trim().isEmpty()) {
                filePath = s.trim();
                break;
            }
        }
        if (filePath == null) {
            startingPointInterfaces = Collections.emptyMap();
            return;
        }

        try {
            startingPointInterfaces = parseStartingPointFile(filePath);
            int totalMethods = 0;
            for (Set<String> methods : startingPointInterfaces.values()) {
                totalMethods += methods.size();
            }
            LOG.info("Loaded {} starting point interfaces ({} methods) from {}",
                    startingPointInterfaces.size(), totalMethods, filePath);
        } catch (IOException e) {
            LOG.warn("Failed to load starting point file {}: {}", filePath, e.getMessage());
            startingPointInterfaces = Collections.emptyMap();
        }
    }

    private Map<String, Set<String>> parseStartingPointFile(String filePath) throws IOException {
        Map<String, Set<String>> result = new LinkedHashMap<>();
        String currentInterface = null;

        for (String line : Files.readAllLines(Paths.get(filePath))) {
            String trimmed = line.trim();

            if (trimmed.startsWith("Interface:")) {
                currentInterface = trimmed.substring("Interface:".length()).trim();
                result.putIfAbsent(currentInterface, new LinkedHashSet<>());
                continue;
            }

            if (currentInterface != null && trimmed.contains("(")
                    && !trimmed.startsWith("#") && !trimmed.startsWith("//")
                    && !trimmed.startsWith("File:") && !trimmed.startsWith("##")) {
                int parenIdx = trimmed.indexOf('(');
                String beforeParen = trimmed.substring(0, parenIdx).trim();
                int lastSpace = beforeParen.lastIndexOf(' ');
                if (lastSpace >= 0) {
                    String methodName = beforeParen.substring(lastSpace + 1);
                    result.get(currentInterface).add(methodName);
                }
            }
        }

        return result;
    }

    private boolean isStartingPointMethod(SootClass sc, SootMethod sm) {
        String methodName = sm.getName();

        if (methodName.equals("<init>") || methodName.equals("<clinit>")) return false;

        for (String sp : filter.startingPoints) {
            if (sp == null || sp.isEmpty()) continue;
            String[] parts = sp.split("#");
            if (parts.length == 2 && sc.getName().equals(parts[0].trim())
                    && methodName.equals(parts[1].trim())) {
                return true;
            }
        }

        if (methodName.equals("run") && sm.getParameterCount() == 0
                && sm.getReturnType().equals(VoidType.v())
                && implementsInterface(sc, "java.lang.Runnable")) {
            return true;
        }

        if (methodName.equals("call") && sm.getParameterCount() == 0
                && implementsInterface(sc, "java.util.concurrent.Callable")) {
            return true;
        }

        for (Map.Entry<String, Set<String>> entry : startingPointInterfaces.entrySet()) {
            if (entry.getValue().contains(methodName)) {
                return true;
            }
        }

        return false;
    }

    private boolean implementsInterface(SootClass sc, String interfaceName) {
        try {
            Deque<SootClass> worklist = new ArrayDeque<>();
            Set<String> visited = new HashSet<>();
            worklist.add(sc);

            while (!worklist.isEmpty()) {
                SootClass current = worklist.poll();
                if (!visited.add(current.getName())) continue;
                if (current.getName().equals(interfaceName)) return true;

                try {
                    for (SootClass iface : current.getInterfaces()) {
                        worklist.add(iface);
                    }
                } catch (Exception e) { /* phantom class */ }

                try {
                    if (current.hasSuperclass()) {
                        worklist.add(current.getSuperclass());
                    }
                } catch (Exception e) { /* phantom class */ }
            }
        } catch (Exception e) {
            LOG.debug("Failed to check interface hierarchy for {}: {}",
                    sc.getName(), e.getMessage());
        }
        return false;
    }

    /**
     * Instruments a starting point method body with trace initiation and
     * emits a {@code TraceRecorder.onTraceStart(methodSig)} call so the
     * trace is recorded regardless of state interactions.
     */
    private void instrumentStartingPoint(Body body) {
        PatchingChain<Unit> units = body.getUnits();

        Unit firstNonIdentity = SootUtils.getFirstNonIdentityStmt(body);
        if (firstNonIdentity == null) return;

        // --- Resolve types ---
        RefType baggageType = RefType.v(BAGGAGE_CLASS);
        RefType builderType = RefType.v(BAGGAGE_BUILDER_CLASS);
        RefType scopeType = RefType.v(SCOPE_CLASS);
        RefType uuidType = RefType.v("java.util.UUID");
        RefType stringType = RefType.v("java.lang.String");
        RefType throwableType = RefType.v("java.lang.Throwable");

        // --- Resolve classes ---
        SootClass baggageSc = Scene.v().forceResolve(BAGGAGE_CLASS, SootClass.SIGNATURES);
        SootClass builderSc = Scene.v().forceResolve(BAGGAGE_BUILDER_CLASS, SootClass.SIGNATURES);
        SootClass scopeSc = Scene.v().forceResolve(SCOPE_CLASS, SootClass.SIGNATURES);
        SootClass uuidSc = Scene.v().forceResolve("java.util.UUID", SootClass.SIGNATURES);
        SootClass traceRecorderSc = Scene.v().forceResolve(TRACE_RECORDER_CLASS, SootClass.SIGNATURES);

        // --- Create locals ---
        Local scopeLocal = newLocal(body, scopeType, "$gcScope");
        Local baggageLocal = newLocal(body, baggageType, "$gcBaggage");
        Local traceIdLocal = newLocal(body, stringType, "$gcTraceId");
        Local uuidLocal = newLocal(body, uuidType, "$gcUUID");
        Local newTraceIdLocal = newLocal(body, stringType, "$gcNewTraceId");
        Local builderLocal = newLocal(body, builderType, "$gcBuilder");
        Local builder2Local = newLocal(body, builderType, "$gcBuilder2");
        Local newBaggageLocal = newLocal(body, baggageType, "$gcNewBaggage");

        // --- Build method refs ---
        SootMethodRef baggageCurrentRef = Scene.v().makeMethodRef(
                baggageSc, "current",
                Collections.<Type>emptyList(), baggageType, true);
        SootMethodRef getEntryRef = Scene.v().makeMethodRef(
                baggageSc, "getEntryValue",
                Collections.<Type>singletonList(stringType), stringType, false);
        SootMethodRef baggageBuilderRef = Scene.v().makeMethodRef(
                baggageSc, "builder",
                Collections.<Type>emptyList(), builderType, true);
        SootMethodRef putRef = Scene.v().makeMethodRef(
                builderSc, "put",
                Arrays.<Type>asList(stringType, stringType), builderType, false);
        SootMethodRef buildRef = Scene.v().makeMethodRef(
                builderSc, "build",
                Collections.<Type>emptyList(), baggageType, false);
        SootMethodRef makeCurrentRef = Scene.v().makeMethodRef(
                baggageSc, "makeCurrent",
                Collections.<Type>emptyList(), scopeType, false);
        SootMethodRef uuidRandomRef = Scene.v().makeMethodRef(
                uuidSc, "randomUUID",
                Collections.<Type>emptyList(), uuidType, true);
        SootMethodRef toStringRef = Scene.v().makeMethodRef(
                uuidSc, "toString",
                Collections.<Type>emptyList(), stringType, false);
        SootMethodRef scopeCloseRef = Scene.v().makeMethodRef(
                scopeSc, "close",
                Collections.<Type>emptyList(), VoidType.v(), false);
        SootMethodRef onTraceStartRef = Scene.v().makeMethodRef(
                traceRecorderSc, "onTraceStart",
                Collections.<Type>singletonList(stringType), VoidType.v(), true);

        // --- Create branch target ---
        Unit bodyStartNop = Jimple.v().newNopStmt();

        // --- Save existing trap begin/end units before preamble insertion ---
        // PatchingChain auto-patches trap refs on insertBefore, which would
        // extend existing traps to cover our preamble where locals are not
        // yet initialized — causing VerifyError from bad stack map frames.
        Map<Trap, Unit> savedTrapBegins = new IdentityHashMap<>();
        Map<Trap, Unit> savedTrapEnds = new IdentityHashMap<>();
        for (Trap trap : body.getTraps()) {
            savedTrapBegins.put(trap, trap.getBeginUnit());
            savedTrapEnds.put(trap, trap.getEndUnit());
        }

        // --- Insert preamble before firstNonIdentity (in order) ---

        // $scope = null
        units.insertBefore(
                Jimple.v().newAssignStmt(scopeLocal, NullConstant.v()),
                firstNonIdentity);

        // $baggage = Baggage.current()
        units.insertBefore(
                Jimple.v().newAssignStmt(baggageLocal,
                        Jimple.v().newStaticInvokeExpr(baggageCurrentRef)),
                firstNonIdentity);

        // $traceId = baggage.getEntryValue("traceId")
        units.insertBefore(
                Jimple.v().newAssignStmt(traceIdLocal,
                        Jimple.v().newInterfaceInvokeExpr(baggageLocal, getEntryRef,
                                Collections.<Value>singletonList(StringConstant.v(TRACE_ID_KEY)))),
                firstNonIdentity);

        // if $traceId != null goto bodyStartNop
        units.insertBefore(
                Jimple.v().newIfStmt(
                        Jimple.v().newNeExpr(traceIdLocal, NullConstant.v()),
                        bodyStartNop),
                firstNonIdentity);

        // $uuid = UUID.randomUUID()
        units.insertBefore(
                Jimple.v().newAssignStmt(uuidLocal,
                        Jimple.v().newStaticInvokeExpr(uuidRandomRef)),
                firstNonIdentity);

        // $newTraceId = uuid.toString()
        units.insertBefore(
                Jimple.v().newAssignStmt(newTraceIdLocal,
                        Jimple.v().newVirtualInvokeExpr(uuidLocal, toStringRef)),
                firstNonIdentity);

        // $builder = Baggage.builder()
        units.insertBefore(
                Jimple.v().newAssignStmt(builderLocal,
                        Jimple.v().newStaticInvokeExpr(baggageBuilderRef)),
                firstNonIdentity);

        // $builder2 = builder.put("traceId", $newTraceId)
        units.insertBefore(
                Jimple.v().newAssignStmt(builder2Local,
                        Jimple.v().newInterfaceInvokeExpr(builderLocal, putRef,
                                Arrays.<Value>asList(
                                        StringConstant.v(TRACE_ID_KEY),
                                        newTraceIdLocal))),
                firstNonIdentity);

        // $newBaggage = builder2.build()
        units.insertBefore(
                Jimple.v().newAssignStmt(newBaggageLocal,
                        Jimple.v().newInterfaceInvokeExpr(builder2Local, buildRef)),
                firstNonIdentity);

        // $scope = newBaggage.makeCurrent()
        units.insertBefore(
                Jimple.v().newAssignStmt(scopeLocal,
                        Jimple.v().newInterfaceInvokeExpr(newBaggageLocal, makeCurrentRef)),
                firstNonIdentity);

        // bodyStartNop: nop  (branch target — merge point)
        units.insertBefore(bodyStartNop, firstNonIdentity);

        // --- TraceRecorder.onTraceStart("ClassName.methodName") ---
        // Inserted after bodyStartNop so it runs on BOTH branches
        // (new trace initiated OR existing trace inherited)
        String methodSig = body.getMethod().getDeclaringClass().getShortName()
                + "." + body.getMethod().getName();
        units.insertBefore(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(onTraceStartRef,
                                Collections.<Value>singletonList(StringConstant.v(methodSig)))),
                firstNonIdentity);

        // --- Restore existing trap begin/end units (undo PatchingChain redirects) ---
        for (Trap trap : body.getTraps()) {
            Unit savedBegin = savedTrapBegins.get(trap);
            Unit savedEnd = savedTrapEnds.get(trap);
            if (savedBegin != null) trap.setBeginUnit(savedBegin);
            if (savedEnd != null) trap.setEndUnit(savedEnd);
        }

        // --- Redirect all return statements to a single cleanup block ---
        // Instead of inserting scope.close() before each return (which puts
        // $gcScope reads inside existing catch blocks and causes VerifyError
        // from local-variable slot conflicts in stack map frames), we redirect
        // all returns through one cleanup block outside the original control flow.

        Type returnType = body.getMethod().getReturnType();
        boolean isVoid = returnType instanceof VoidType;
        Local retValLocal = null;
        if (!isVoid) {
            retValLocal = newLocal(body, returnType, "$gcRetVal");
        }

        Unit cleanupNop = Jimple.v().newNopStmt();
        Unit cleanupSkipClose = Jimple.v().newNopStmt();
        Unit cleanupReturn = isVoid
                ? Jimple.v().newReturnVoidStmt()
                : Jimple.v().newReturnStmt(retValLocal);

        // Replace every original return with goto cleanup (saving return value if needed)
        List<Unit> returnUnits = new ArrayList<>();
        for (Unit u : new ArrayList<>(units)) {
            if (u instanceof ReturnStmt || u instanceof ReturnVoidStmt) {
                returnUnits.add(u);
            }
        }

        for (Unit ret : returnUnits) {
            if (!isVoid && ret instanceof ReturnStmt) {
                Value retVal = ((ReturnStmt) ret).getOp();
                units.insertBefore(
                        Jimple.v().newAssignStmt(retValLocal, retVal), ret);
            }
            units.insertBefore(Jimple.v().newGotoStmt(cleanupNop), ret);
            units.remove(ret);
        }

        // Append cleanup block at the end of the original body:
        //   cleanupNop: nop
        //   if $gcScope == null goto cleanupSkipClose
        //   $gcScope.close()
        //   cleanupSkipClose: nop
        //   return / return $gcRetVal
        Unit lastUnit = units.getLast();
        Unit ifNullStmt = Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(scopeLocal, NullConstant.v()),
                cleanupSkipClose);
        Unit closeStmt = Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(scopeLocal, scopeCloseRef));

        units.insertAfter(cleanupNop, lastUnit);
        units.insertAfter(ifNullStmt, cleanupNop);
        units.insertAfter(closeStmt, ifNullStmt);
        units.insertAfter(cleanupSkipClose, closeStmt);
        units.insertAfter(cleanupReturn, cleanupSkipClose);

        // --- Add catch-all exception handler after the cleanup block ---
        Local exLocal = newLocal(body, throwableType, "$gcEx");
        Unit handlerIdentity = Jimple.v().newIdentityStmt(
                exLocal, Jimple.v().newCaughtExceptionRef());
        Unit rethrowNop = Jimple.v().newNopStmt();

        Unit handlerIfNull = Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(scopeLocal, NullConstant.v()), rethrowNop);
        Unit handlerClose = Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(scopeLocal, scopeCloseRef));
        Unit handlerThrow = Jimple.v().newThrowStmt(exLocal);

        units.insertAfter(handlerIdentity, cleanupReturn);
        units.insertAfter(handlerIfNull, handlerIdentity);
        units.insertAfter(handlerClose, handlerIfNull);
        units.insertAfter(rethrowNop, handlerClose);
        units.insertAfter(handlerThrow, rethrowNop);

        // Trap covers the original body + cleanup block; handler is outside
        body.getTraps().add(Jimple.v().newTrap(
                Scene.v().getSootClass("java.lang.Throwable"),
                bodyStartNop,
                handlerIdentity,
                handlerIdentity));

        LOG.debug("Instrumented starting point: {}", body.getMethod().getSignature());
    }

    // ========================================================================
    // Field Access Instrumentation (State Tracing)
    // ========================================================================

    /**
     * Instruments instance field reads and writes in {@code body} by inserting
     * calls to {@code TraceRecorder.onFieldWrite/onFieldRead} after each access.
     * This records every field operation for trace reconstruction and enables
     * cross-flow detection when two traces touch the same object.
     *
     * @return true if at least one field access was instrumented
     */
    private boolean instrumentFieldAccess(Body body) {
        LOG.info("Instrumenting method for field accesses: {}.{}",
                body.getMethod().getDeclaringClass().getName(),
                body.getMethod().getName());
        String methodName = body.getMethod().getName();
        // Skip constructors — too noisy (object being built)
        if (methodName.equals("<init>") || methodName.equals("<clinit>")) return false;

        PatchingChain<Unit> units = body.getUnits();
        List<Unit> snapshot = new ArrayList<>(units);
        boolean instrumented = false;

        SootClass traceRecorderSc = Scene.v().forceResolve(TRACE_RECORDER_CLASS, SootClass.SIGNATURES);
        RefType objectType = RefType.v("java.lang.Object");
        RefType stringType = RefType.v("java.lang.String");

        SootMethodRef onFieldWriteRef = Scene.v().makeMethodRef(
                traceRecorderSc, "onFieldWrite",
                Arrays.<Type>asList(objectType, stringType, stringType),
                VoidType.v(), true);
        SootMethodRef onFieldReadRef = Scene.v().makeMethodRef(
                traceRecorderSc, "onFieldRead",
                Arrays.<Type>asList(objectType, stringType, stringType),
                VoidType.v(), true);

        for (Unit u : snapshot) {
            if (!(u instanceof AssignStmt)) continue;
            AssignStmt assign = (AssignStmt) u;

            try {
                // Field WRITE: base.field = value
                if (assign.getLeftOp() instanceof InstanceFieldRef) {
                    InstanceFieldRef fieldRef = (InstanceFieldRef) assign.getLeftOp();
                    if (shouldSkipField(fieldRef)) continue;

                    Value base = fieldRef.getBase();
                    String className = fieldRef.getField().getDeclaringClass().getShortName();
                    String fieldName = fieldRef.getField().getName();

                    units.insertAfter(
                            Jimple.v().newInvokeStmt(
                                    Jimple.v().newStaticInvokeExpr(onFieldWriteRef,
                                            Arrays.<Value>asList(
                                                    (Value) base,
                                                    StringConstant.v(className),
                                                    StringConstant.v(fieldName)))),
                            u);
                    instrumented = true;
                }
                // Field READ: local = base.field
                else if (assign.getRightOp() instanceof InstanceFieldRef) {
                    InstanceFieldRef fieldRef = (InstanceFieldRef) assign.getRightOp();
                    if (shouldSkipField(fieldRef)) continue;

                    Value base = fieldRef.getBase();
                    String className = fieldRef.getField().getDeclaringClass().getShortName();
                    String fieldName = fieldRef.getField().getName();

                    units.insertAfter(
                            Jimple.v().newInvokeStmt(
                                    Jimple.v().newStaticInvokeExpr(onFieldReadRef,
                                            Arrays.<Value>asList(
                                                    (Value) base,
                                                    StringConstant.v(className),
                                                    StringConstant.v(fieldName)))),
                            u);
                    instrumented = true;
                }
            } catch (Exception e) {
                LOG.debug("Skip field-access instrumentation at {} in {}: {}",
                        u, body.getMethod().getSignature(), e.getMessage());
            }
        }

        return instrumented;
    }

    /**
     * Returns true if the field should NOT be instrumented for state tracing.
     */
    private boolean shouldSkipField(InstanceFieldRef fieldRef) {
        Type fieldType = fieldRef.getField().getType();

        // Skip primitive types — they are values, not trackable state objects
        if (fieldType instanceof PrimType) return true;

        // Skip array types of primitives
        if (fieldType instanceof ArrayType) {
            Type baseType = ((ArrayType) fieldType).baseType;
            if (baseType instanceof PrimType) return true;
        }

        // Skip logger fields
        String typeName = fieldType.toString();
        if (LOGGER_TYPES.contains(typeName)) return true;

        // Skip TraceRecorder's own fields (safety)
        if (typeName.startsWith("org.apache.hadoop.hdfs.tracing.")) return true;

        return false;
    }

    // ========================================================================
    // Helpers
    // ========================================================================

    private Local newLocal(Body body, Type type, String prefix) {
        String name = prefix + "_" + (tempCounter++);
        Local local = Jimple.v().newLocal(name, type);
        body.getLocals().add(local);
        return local;
    }
}
