package edu.uva.liftlab.graphchecker.transformer;

import edu.uva.liftlab.graphchecker.analysis.PhaseInfo;
import edu.uva.liftlab.graphchecker.util.ClassFilterHelper;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.*;

import java.util.*;

public class GraphCheckerTransformer extends SceneTransformer {

    public static final PhaseInfo PHASE_INFO = new PhaseInfo("wjtp", "transformer method",
            "Transform classes to insert PropTracer instrumentation for state propagation tracking",
            true, false);

    private static final Logger LOG = LoggerFactory.getLogger(GraphCheckerTransformer.class);

    private static final String PROP_TRACER_CLASS =
            "org.apache.hadoop.hdfs.server.federation.utils.PropTracer";

    private static final String OTEL_CONTEXT_CLASS = "io.opentelemetry.context.Context";

    /** OTel wrap strategies — only the three natively supported by Context.wrap(). */
    private static final int WRAP_RUNNABLE = 0;
    private static final int WRAP_CALLABLE = 1;
    private static final int WRAP_EXECUTOR = 2;

    public String config_file_path;
    public ClassFilterHelper filter;

    /** Cached SootClass for PropTracer. */
    private SootClass tracerClass;

    /** Cached SootClass for OTel Context (resolved lazily when propagation is enabled). */
    private SootClass otelContextClass;

    /** Counter for generating unique local variable names. */
    private int tempCounter = 0;

    public GraphCheckerTransformer(String config_file_path) {
        this.config_file_path = config_file_path;
        this.filter = new ClassFilterHelper(this.config_file_path);
    }

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        LOG.info("Starting PropTracer instrumentation phase: {}", phaseName);

        tracerClass = Scene.v().forceResolve(PROP_TRACER_CLASS, SootClass.SIGNATURES);
        tracerClass.setApplicationClass();

        if (filter.contextPropagationEnabled) {
            otelContextClass = Scene.v().forceResolve(OTEL_CONTEXT_CLASS, SootClass.SIGNATURES);
            LOG.info("Context propagation enabled; OTel Context class resolved");
        }

        int classCount = 0;
        int methodCount = 0;

        for (SootClass sc : new ArrayList<>(Scene.v().getApplicationClasses())) {
            if (shouldSkip(sc)) continue;

            classCount++;
            for (SootMethod sm : new ArrayList<>(sc.getMethods())) {
                if (!sm.isConcrete()) continue;
                try {
                    Body body = sm.retrieveActiveBody();
                    instrumentBody(body);
                    methodCount++;
                } catch (Exception e) {
                    LOG.warn("Failed to instrument {}.{}: {}",
                            sc.getName(), sm.getName(), e.getMessage());
                }
            }
        }

        LOG.info("Instrumentation complete: {} classes, {} methods", classCount, methodCount);
    }

    // ========================================================================
    // Skip Logic
    // ========================================================================

    private boolean shouldSkip(SootClass sc) {
        String name = sc.getName();

        // Never instrument PropTracer itself
        if (name.equals(PROP_TRACER_CLASS)) return true;

        // Skip JDK / Soot internals
        if (name.startsWith("java.") || name.startsWith("javax.")
                || name.startsWith("sun.") || name.startsWith("jdk.")
                || name.startsWith("soot.")) {
            return true;
        }

        // Apply user's filter
        if (filter.isBlackListPilotFuncClass(sc)
                && !filter.isWhiteListPilotFuncClass(sc)) {
            return true;
        }

        return false;
    }

    // ========================================================================
    // Body Instrumentation
    // ========================================================================

    private void instrumentBody(Body body) {
        SootMethod method = body.getMethod();
        PatchingChain<Unit> units = body.getUnits();
        String methodSig = method.getSignature();
        String className = method.getDeclaringClass().getName();

        // Snapshot to avoid ConcurrentModification
        List<Unit> originalUnits = new ArrayList<>(units);

        for (Unit u : originalUnits) {
            if (!(u instanceof Stmt)) continue;
            Stmt stmt = (Stmt) u;

            try {
                // Phase 1: propagate OTel context across async boundaries (before the call)
                if (filter.contextPropagationEnabled) {
                    tryInjectContextPropagation(body, stmt, units);
                }

                // Phase 2: PropTracer instrumentation (after the call)
                if (stmt instanceof AssignStmt) {
                    instrumentAssign(body, (AssignStmt) stmt, units,
                            methodSig, className);
                } else if (stmt instanceof InvokeStmt) {
                    instrumentInvokeStmt(body, (InvokeStmt) stmt, units,
                            methodSig, className);
                }
            } catch (Exception e) {
                LOG.debug("Skip instrumenting stmt in {}: {}",
                        methodSig, e.getMessage());
            }
        }
    }

    // ========================================================================
    // Context Propagation: Async Boundary Detection + Jimple Insertion
    // ========================================================================

    /**
     * If {@code stmt} contains an invoke at an async boundary, insert
     * {@code Context.current().wrap(arg)} before the call and replace the arg.
     * Only Runnable, Callable, and Executor are wrapped — the three types
     * natively supported by {@code io.opentelemetry.context.Context}.
     */
    private void tryInjectContextPropagation(Body body, Stmt stmt,
                                             PatchingChain<Unit> units) {
        if (!stmt.containsInvokeExpr()) return;
        InvokeExpr invoke = stmt.getInvokeExpr();

        String declClass = invoke.getMethod().getDeclaringClass().getName();
        // Never wrap calls into OTel or PropTracer itself
        if (declClass.startsWith("io.opentelemetry.") || declClass.equals(PROP_TRACER_CLASS)) return;

        int[] match = detectAsyncBoundary(invoke);
        if (match == null) return;

        int argIdx  = match[0];
        int strategy = match[1];
        if (argIdx >= invoke.getArgCount()) return;

        Value arg = invoke.getArg(argIdx);
        if (!(arg instanceof Local)) return;  // can only wrap locals

        try {
            Local wrapped = insertContextWrap(body, (Local) arg, strategy, stmt, units);
            invoke.setArg(argIdx, wrapped);
            LOG.debug("Context-wrapped arg {} of {} in {}",
                    argIdx, invoke.getMethod().getSignature(),
                    body.getMethod().getSignature());
        } catch (Exception e) {
            LOG.debug("Failed to context-wrap async boundary in {}: {}",
                    body.getMethod().getSignature(), e.getMessage());
        }
    }

    /**
     * Returns {argIndex, strategy} if {@code invoke} is an async boundary
     * call site where we should inject context propagation, otherwise null.
     *
     * <p>Covered patterns:
     * <ul>
     *   <li>Thread.&lt;init&gt;(Runnable)</li>
     *   <li>Any {@code execute(Runnable)} method (Executor, ForkJoinPool, …)</li>
     *   <li>Any {@code submit(Runnable|Callable)} method (ExecutorService, ForkJoinPool, …)</li>
     *   <li>ScheduledExecutorService {@code schedule*} with Runnable/Callable first arg</li>
     *   <li>CompletableFuture.*Async — wrap the trailing Executor arg if present</li>
     *   <li>Guava {@code Futures.addCallback / transformAsync} — wrap trailing Executor</li>
     * </ul>
     */
    private int[] detectAsyncBoundary(InvokeExpr invoke) {
        SootMethod m = invoke.getMethod();
        String declClass  = m.getDeclaringClass().getName();
        String methodName = m.getName();
        List<Type> params = m.getParameterTypes();

        // Thread.<init>(Runnable, ...)
        if (declClass.equals("java.lang.Thread") && methodName.equals("<init>")
                && !params.isEmpty() && isRunnableType(params.get(0))) {
            return new int[]{0, WRAP_RUNNABLE};
        }

        // execute(Runnable)  — Executor, ThreadPoolExecutor, ForkJoinPool, etc.
        if (methodName.equals("execute") && params.size() >= 1
                && isRunnableType(params.get(0))) {
            return new int[]{0, WRAP_RUNNABLE};
        }

        // submit(Runnable) or submit(Callable)
        if (methodName.equals("submit") && !params.isEmpty()) {
            if (isRunnableType(params.get(0)))  return new int[]{0, WRAP_RUNNABLE};
            if (isCallableType(params.get(0)))  return new int[]{0, WRAP_CALLABLE};
        }

        // schedule / scheduleAtFixedRate / scheduleWithFixedDelay
        if ((methodName.equals("schedule")
                || methodName.equals("scheduleAtFixedRate")
                || methodName.equals("scheduleWithFixedDelay"))
                && !params.isEmpty()) {
            if (isRunnableType(params.get(0))) return new int[]{0, WRAP_RUNNABLE};
            if (isCallableType(params.get(0))) return new int[]{0, WRAP_CALLABLE};
        }

        // CompletableFuture.*Async — if last param is Executor, wrap it so the
        // common-pool alternative also inherits context through the executor wrapper.
        if (declClass.equals("java.util.concurrent.CompletableFuture")
                && methodName.endsWith("Async") && !params.isEmpty()) {
            int last = params.size() - 1;
            if (isExecutorType(params.get(last))) return new int[]{last, WRAP_EXECUTOR};
        }

        // Guava ListenableFuture helpers: addCallback / transformAsync / transform
        // Last arg is usually an Executor.
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

    /**
     * Inserts before {@code insertBefore}:
     * <pre>
     *   $ctx     = staticinvoke Context.current();
     *   $wrapped = interfaceinvoke $ctx.wrap($arg);   // return type matches strategy
     * </pre>
     * and returns {@code $wrapped}.
     */
    private Local insertContextWrap(Body body, Local arg, int strategy,
                                    Unit insertBefore, PatchingChain<Unit> units) {
        RefType ctxType = RefType.v(OTEL_CONTEXT_CLASS);

        // $ctx = Context.current()
        Local ctxLocal = newLocal(body, ctxType, "$otelCtx");
        SootMethodRef currentRef = Scene.v().makeMethodRef(
                otelContextClass, "current",
                Collections.<Type>emptyList(), ctxType, true);
        units.insertBefore(
                Jimple.v().newAssignStmt(ctxLocal,
                        Jimple.v().newStaticInvokeExpr(currentRef)),
                insertBefore);

        // determine wrap(…) signature
        String wrapTypeName;
        switch (strategy) {
            case WRAP_CALLABLE: wrapTypeName = "java.util.concurrent.Callable"; break;
            case WRAP_EXECUTOR: wrapTypeName = "java.util.concurrent.Executor";  break;
            default:            wrapTypeName = "java.lang.Runnable";             break;
        }
        RefType wrapType = RefType.v(wrapTypeName);

        // $wrapped = interfaceinvoke $ctx.<Context: T wrap(T)>($arg)
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

    //Pilot Tracing -> Is it enough to capture distributed dependency?

    //

    // ========================================================================
    // AssignStmt Instrumentation
    // ========================================================================

    private void instrumentAssign(Body body, AssignStmt stmt,
                                  PatchingChain<Unit> units,
                                  String methodSig, String className) {
        Value lhs = stmt.getLeftOp();
        Value rhs = stmt.getRightOp();
        String callSite = callSiteOf(className, methodSig, stmt);

        // Case 1: $r = new X
        if (rhs instanceof NewExpr) {
            if (lhs instanceof Local) {
                insertAfter(units, stmt,
                        buildOnNew(body, (Local) lhs, callSite));
            }
        }
        // Case 2: x.f = y (instance field write, object type)
        else if (lhs instanceof InstanceFieldRef) {
            InstanceFieldRef fieldRef = (InstanceFieldRef) lhs;
            Local base = (Local) fieldRef.getBase();
            String fieldName = fieldRef.getField().getName();
            Type fieldType = fieldRef.getField().getType();

            if (fieldType instanceof PrimType) {
                // Primitive field write
                String localName = (rhs instanceof Local)
                        ? ((Local) rhs).getName() : "const";
                insertAfter(units, stmt,
                        buildOnPrimitiveFieldWrite(body, base, fieldName,
                                methodSig, localName, callSite));
            } else {
                // Object field write
                Local valueLocal = ensureLocal(body, rhs, stmt, units);
                insertAfter(units, stmt,
                        buildOnFieldWrite(body, base, fieldName,
                                valueLocal, callSite));
            }
        }
        // Case 3: y = x.f (instance field read, object type)
        else if (rhs instanceof InstanceFieldRef && lhs instanceof Local) {
            InstanceFieldRef fieldRef = (InstanceFieldRef) rhs;
            Local base = (Local) fieldRef.getBase();
            String fieldName = fieldRef.getField().getName();
            Type fieldType = fieldRef.getField().getType();

            if (fieldType instanceof PrimType) {
                // Primitive field read
                insertAfter(units, stmt,
                        buildOnPrimitiveFieldRead(body, base, fieldName,
                                methodSig, ((Local) lhs).getName(), callSite));
            } else {
                // Object field read
                insertAfter(units, stmt,
                        buildOnFieldRead(body, base, fieldName,
                                (Local) lhs, callSite));
            }
        }
        // Case 4: x.f = y (static field write)
        else if (lhs instanceof StaticFieldRef) {
            StaticFieldRef fieldRef = (StaticFieldRef) lhs;
            String fieldName = fieldRef.getField().getDeclaringClass().getName()
                    + "." + fieldRef.getField().getName();
            Type fieldType = fieldRef.getField().getType();

            if (!(fieldType instanceof PrimType)) {
                Local valueLocal = ensureLocal(body, rhs, stmt, units);
                // Use null as base for static fields; log with class name in fieldName
                insertAfter(units, stmt,
                        buildOnFieldWriteStatic(body, fieldName,
                                valueLocal, callSite));
            }
        }
        // Case 5: y = X.f (static field read)
        else if (rhs instanceof StaticFieldRef && lhs instanceof Local) {
            StaticFieldRef fieldRef = (StaticFieldRef) rhs;
            String fieldName = fieldRef.getField().getDeclaringClass().getName()
                    + "." + fieldRef.getField().getName();
            Type fieldType = fieldRef.getField().getType();

            if (!(fieldType instanceof PrimType)) {
                insertAfter(units, stmt,
                        buildOnFieldReadStatic(body, fieldName,
                                (Local) lhs, callSite));
            }
        }
        // Case 6: a[i] = v (array write)
        else if (lhs instanceof ArrayRef) {
            ArrayRef arrayRef = (ArrayRef) lhs;
            Local base = (Local) arrayRef.getBase();
            Value index = arrayRef.getIndex();
            Type elemType = ((ArrayType) base.getType()).getElementType();

            if (!(elemType instanceof PrimType)) {
                Local valueLocal = ensureLocal(body, rhs, stmt, units);
                int idx = (index instanceof IntConstant)
                        ? ((IntConstant) index).value : -1;
                insertAfter(units, stmt,
                        buildOnArrayWrite(body, base, idx,
                                valueLocal, callSite));
            }
        }
        // Case 7: v = a[i] (array read)
        else if (rhs instanceof ArrayRef && lhs instanceof Local) {
            ArrayRef arrayRef = (ArrayRef) rhs;
            Local base = (Local) arrayRef.getBase();
            Value index = arrayRef.getIndex();
            Type baseType = base.getType();

            if (baseType instanceof ArrayType) {
                Type elemType = ((ArrayType) baseType).getElementType();
                if (!(elemType instanceof PrimType)) {
                    int idx = (index instanceof IntConstant)
                            ? ((IntConstant) index).value : -1;
                    insertAfter(units, stmt,
                            buildOnArrayRead(body, base, idx,
                                    (Local) lhs, callSite));
                }
            }
        }
        // Case 8: $r = invoke xxx (method call with return value)
        else if (rhs instanceof InvokeExpr && lhs instanceof Local) {
            InvokeExpr invoke = (InvokeExpr) rhs;
            // Skip PropTracer's own methods
            if (invoke.getMethod().getDeclaringClass().getName()
                    .equals(PROP_TRACER_CLASS)) {
                return;
            }

            Type returnType = invoke.getMethod().getReturnType();
            if (returnType instanceof RefLikeType) {
                String invokedMethod = invoke.getMethod().getName();
                Local receiver = getReceiver(invoke);
                List<Value> invokeArgs = invoke.getArgs();

                // Check for collection operations
                if (isCollectionAdd(invoke)) {
                    if (!invokeArgs.isEmpty()) {
                        Local argLocal = ensureLocal(body, invokeArgs.get(0),
                                stmt, units);
                        Local collLocal = receiver != null ? receiver
                                : ensureLocal(body, invokeArgs.get(0),
                                stmt, units);
                        insertAfter(units, stmt,
                                buildOnCollectionAdd(body, receiver,
                                        argLocal, callSite));
                    }
                } else if (isCollectionGet(invoke)) {
                    if (receiver != null) {
                        insertAfter(units, stmt,
                                buildOnCollectionGet(body, receiver,
                                        (Local) lhs, callSite));
                    }
                } else {
                    // General invoke result
                    insertAfter(units, stmt,
                            buildOnInvokeResult(body, (Local) lhs, receiver,
                                    invokedMethod, invokeArgs, callSite));
                }
            }
        }
        // Case 9: $r1 = $r2 (local to local, object type)
        else if (lhs instanceof Local && rhs instanceof Local) {
            Type type = ((Local) rhs).getType();
            if (type instanceof RefLikeType) {
                // Object assignment: just register the same propId
                insertAfter(units, stmt,
                        buildOnLocalObjectAssign(body, (Local) lhs,
                                (Local) rhs, callSite));
            } else if (type instanceof PrimType) {
                insertAfter(units, stmt,
                        buildOnLocalAssign(body, methodSig,
                                ((Local) lhs).getName(),
                                ((Local) rhs).getName(),
                                (Local) rhs, callSite));
            }
        }
    }

    // ========================================================================
    // InvokeStmt Instrumentation (void calls)
    // ========================================================================

    private void instrumentInvokeStmt(Body body, InvokeStmt stmt,
                                      PatchingChain<Unit> units,
                                      String methodSig, String className) {
        InvokeExpr invoke = stmt.getInvokeExpr();

        if (invoke.getMethod().getDeclaringClass().getName()
                .equals(PROP_TRACER_CLASS)) {
            return;
        }

        String callSite = callSiteOf(className, methodSig, stmt);

        // Track collection.add() calls
        if (isCollectionAdd(invoke)) {
            Local receiver = getReceiver(invoke);
            List<Value> args = invoke.getArgs();
            if (receiver != null && !args.isEmpty()) {
                Local argLocal = ensureLocal(body, args.get(0), stmt, units);
                insertAfter(units, stmt,
                        buildOnCollectionAdd(body, receiver, argLocal, callSite));
            }
        }
        // Track void method invocations for API boundary detection
        else {
            Local receiver = getReceiver(invoke);
            String invokedMethod = invoke.getMethod().getName();
            insertAfter(units, stmt,
                    buildOnInvokeVoid(body, receiver, invokedMethod,
                            invoke.getArgs(), callSite));
        }
    }

    // ========================================================================
    // Build PropTracer Call: onNew
    // ========================================================================

    private List<Unit> buildOnNew(Body body, Local obj, String callSite) {
        // PropTracer.onNew(obj, callSite)
        SootMethodRef ref = makeTracerRef("onNew",
                Arrays.asList(RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        return Collections.singletonList(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(ref,
                                obj, StringConstant.v(callSite))));
    }

    // ========================================================================
    // Build PropTracer Call: onFieldWrite (object)
    // ========================================================================

    private List<Unit> buildOnFieldWrite(Body body, Local base,
                                         String fieldName, Local value,
                                         String callSite) {
        // PropTracer.onFieldWrite(base, fieldName, value, callSite)
        SootMethodRef ref = makeTracerRef("onFieldWrite",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        return Collections.singletonList(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(ref,
                                base,
                                StringConstant.v(fieldName),
                                value,
                                StringConstant.v(callSite))));
    }

    // ========================================================================
    // Build PropTracer Call: onFieldWrite (static field)
    // ========================================================================

    private List<Unit> buildOnFieldWriteStatic(Body body, String fieldName,
                                               Local value, String callSite) {
        // PropTracer.onFieldWrite(null, fieldName, value, callSite)
        // We pass NullConstant for base since it's a static field
        SootMethodRef ref = makeTracerRef("onFieldWrite",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        return Collections.singletonList(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(ref,
                                NullConstant.v(),
                                StringConstant.v(fieldName),
                                value,
                                StringConstant.v(callSite))));
    }

    // ========================================================================
    // Build PropTracer Call: onFieldRead (object)
    // ========================================================================

    private List<Unit> buildOnFieldRead(Body body, Local base,
                                        String fieldName, Local result,
                                        String callSite) {
        // PropTracer.onFieldRead(base, fieldName, result, callSite)
        SootMethodRef ref = makeTracerRef("onFieldRead",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        return Collections.singletonList(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(ref,
                                base,
                                StringConstant.v(fieldName),
                                result,
                                StringConstant.v(callSite))));
    }

    // ========================================================================
    // Build PropTracer Call: onFieldRead (static field)
    // ========================================================================

    private List<Unit> buildOnFieldReadStatic(Body body, String fieldName,
                                              Local result, String callSite) {
        SootMethodRef ref = makeTracerRef("onFieldRead",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        return Collections.singletonList(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(ref,
                                NullConstant.v(),
                                StringConstant.v(fieldName),
                                result,
                                StringConstant.v(callSite))));
    }

    // ========================================================================
    // Build PropTracer Call: onPrimitiveFieldWrite
    // ========================================================================

    private List<Unit> buildOnPrimitiveFieldWrite(Body body, Local base,
                                                  String fieldName,
                                                  String method,
                                                  String localName,
                                                  String callSite) {
        // PropTracer.onPrimitiveFieldWrite(base, fieldName, method, localName, callSite)
        SootMethodRef ref = makeTracerRef("onPrimitiveFieldWrite",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        return Collections.singletonList(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(ref,
                                base,
                                StringConstant.v(fieldName),
                                StringConstant.v(method),
                                StringConstant.v(localName),
                                StringConstant.v(callSite))));
    }

    // ========================================================================
    // Build PropTracer Call: onPrimitiveFieldRead
    // ========================================================================

    private List<Unit> buildOnPrimitiveFieldRead(Body body, Local base,
                                                 String fieldName,
                                                 String method,
                                                 String localName,
                                                 String callSite) {
        // PropTracer.onPrimitiveFieldRead(base, fieldName, method, localName, callSite)
        SootMethodRef ref = makeTracerRef("onPrimitiveFieldRead",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        return Collections.singletonList(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(ref,
                                base,
                                StringConstant.v(fieldName),
                                StringConstant.v(method),
                                StringConstant.v(localName),
                                StringConstant.v(callSite))));
    }

    // ========================================================================
    // Build PropTracer Call: onLocalAssign
    // ========================================================================

    private List<Unit> buildOnLocalAssign(Body body, String method,
                                          String lhsName, String rhsName,
                                          Local rhsLocal, String callSite) {
        // PropTracer.onLocalAssign(method, lhsName, rhsName, rhsValue, callSite)
        // rhsLocal is primitive, need to box it
        List<Unit> stmts = new ArrayList<>();
        Local boxed = boxPrimitive(body, rhsLocal, stmts);

        SootMethodRef ref = makeTracerRef("onLocalAssign",
                Arrays.asList(
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        stmts.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(ref,
                        StringConstant.v(method),
                        StringConstant.v(lhsName),
                        StringConstant.v(rhsName),
                        boxed,
                        StringConstant.v(callSite))));
        return stmts;
    }

    // ========================================================================
    // Build PropTracer Call: onLocalAssign for object types
    // ========================================================================

    private List<Unit> buildOnLocalObjectAssign(Body body, Local lhs,
                                                Local rhs, String callSite) {
        // For object-to-object local assign, just register lhs with rhs's propId
        // PropTracer.onFieldRead is not quite right here;
        // We use onInvokeResult-style: get rhs's propId, register lhs
        // Simplest: call registerObject(lhs, getPropId(rhs))
        // But that's two calls. Instead use onFieldWrite(null, lhsName, rhs, callSite)
        // Actually, the cleanest way: just log it

        SootMethodRef ref = makeTracerRef("onFieldWrite",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        return Collections.singletonList(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(ref,
                                NullConstant.v(),
                                StringConstant.v(lhs.getName() + "=" + rhs.getName()),
                                rhs,
                                StringConstant.v(callSite))));
    }

    // ========================================================================
    // Build PropTracer Call: onInvokeResult
    // ========================================================================

    private List<Unit> buildOnInvokeResult(Body body, Local result,
                                           Local receiver,
                                           String methodName,
                                           List<Value> invokeArgs,
                                           String callSite) {
        List<Unit> stmts = new ArrayList<>();

        // Build Object[] args array
        Local argsArray = buildArgsArray(body, invokeArgs, stmts);

        // PropTracer.onInvokeResult(result, receiver, methodName, args, callSite)
        SootMethodRef ref = makeTracerRef("onInvokeResult",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String"),
                        ArrayType.v(RefType.v("java.lang.Object"), 1),
                        RefType.v("java.lang.String")),
                VoidType.v());

        Value receiverVal = (receiver != null) ? receiver : NullConstant.v();

        stmts.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(ref,
                        result,
                        receiverVal,
                        StringConstant.v(methodName),
                        argsArray,
                        StringConstant.v(callSite))));
        return stmts;
    }

    // ========================================================================
    // Build PropTracer Call: onInvokeVoid
    // ========================================================================

    private List<Unit> buildOnInvokeVoid(Body body, Local receiver,
                                         String methodName,
                                         List<Value> invokeArgs,
                                         String callSite) {
        List<Unit> stmts = new ArrayList<>();

        Local argsArray = buildArgsArray(body, invokeArgs, stmts);

        SootMethodRef ref = makeTracerRef("onInvokeResult",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String"),
                        ArrayType.v(RefType.v("java.lang.Object"), 1),
                        RefType.v("java.lang.String")),
                VoidType.v());

        Value receiverVal = (receiver != null) ? receiver : NullConstant.v();

        stmts.add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(ref,
                        NullConstant.v(),  // result is null for void
                        receiverVal,
                        StringConstant.v(methodName),
                        argsArray,
                        StringConstant.v(callSite))));
        return stmts;
    }

    // ========================================================================
    // Build PropTracer Call: onCollectionAdd
    // ========================================================================

    private List<Unit> buildOnCollectionAdd(Body body, Local collection,
                                            Local element, String callSite) {
        SootMethodRef ref = makeTracerRef("onCollectionAdd",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        return Collections.singletonList(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(ref,
                                collection, element,
                                StringConstant.v(callSite))));
    }

    // ========================================================================
    // Build PropTracer Call: onCollectionGet
    // ========================================================================

    private List<Unit> buildOnCollectionGet(Body body, Local collection,
                                            Local element, String callSite) {
        SootMethodRef ref = makeTracerRef("onCollectionGet",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        return Collections.singletonList(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(ref,
                                collection, element,
                                StringConstant.v(callSite))));
    }

    // ========================================================================
    // Build PropTracer Call: onArrayWrite / onArrayRead
    // ========================================================================

    private List<Unit> buildOnArrayWrite(Body body, Local array, int index,
                                         Local value, String callSite) {
        SootMethodRef ref = makeTracerRef("onArrayWrite",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        IntType.v(),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        return Collections.singletonList(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(ref,
                                array, IntConstant.v(index),
                                value, StringConstant.v(callSite))));
    }

    private List<Unit> buildOnArrayRead(Body body, Local array, int index,
                                        Local result, String callSite) {
        SootMethodRef ref = makeTracerRef("onArrayRead",
                Arrays.asList(
                        RefType.v("java.lang.Object"),
                        IntType.v(),
                        RefType.v("java.lang.Object"),
                        RefType.v("java.lang.String")),
                VoidType.v());

        return Collections.singletonList(
                Jimple.v().newInvokeStmt(
                        Jimple.v().newStaticInvokeExpr(ref,
                                array, IntConstant.v(index),
                                result, StringConstant.v(callSite))));
    }

    // ========================================================================
    // Helpers: Collection detection
    // ========================================================================

    private boolean isCollectionAdd(InvokeExpr invoke) {
        String name = invoke.getMethod().getName();
        String declClass = invoke.getMethod().getDeclaringClass().getName();
        if (name.equals("add") || name.equals("addAll")) {
            return isCollectionType(declClass);
        }
        return false;
    }

    private boolean isCollectionGet(InvokeExpr invoke) {
        String name = invoke.getMethod().getName();
        String declClass = invoke.getMethod().getDeclaringClass().getName();
        if (name.equals("get") || name.equals("next")
                || name.equals("iterator")) {
            return isCollectionType(declClass)
                    || declClass.equals("java.util.Iterator");
        }
        return false;
    }

    private boolean isCollectionType(String className) {
        return className.startsWith("java.util.") && (
                className.contains("List") || className.contains("Set")
                        || className.contains("Collection")
                        || className.contains("Queue")
                        || className.contains("Map")
                        || className.equals("java.util.ArrayList")
                        || className.equals("java.util.LinkedList")
                        || className.equals("java.util.HashSet"));
    }

    // ========================================================================
    // Helpers: Receiver extraction
    // ========================================================================

    private Local getReceiver(InvokeExpr invoke) {
        if (invoke instanceof InstanceInvokeExpr) {
            Value base = ((InstanceInvokeExpr) invoke).getBase();
            if (base instanceof Local) {
                return (Local) base;
            }
        }
        return null;
    }

    // ========================================================================
    // Helpers: Build Object[] args array
    // ========================================================================

    private Local buildArgsArray(Body body, List<Value> args,
                                 List<Unit> stmts) {
        ArrayType objArrayType = ArrayType.v(RefType.v("java.lang.Object"), 1);
        Local arr = newLocal(body, objArrayType, "$propArgs");

        // arr = new Object[args.size()]
        stmts.add(Jimple.v().newAssignStmt(arr,
                Jimple.v().newNewArrayExpr(
                        RefType.v("java.lang.Object"),
                        IntConstant.v(args.size()))));

        for (int i = 0; i < args.size(); i++) {
            Value arg = args.get(i);
            Value boxedArg;

            if (arg.getType() instanceof PrimType) {
                // Box the primitive
                Local boxed = newLocal(body,
                        RefType.v("java.lang.Object"), "$boxArg");
                List<Unit> boxStmts = new ArrayList<>();
                boxed = boxPrimitiveValue(body, arg, boxStmts);
                stmts.addAll(boxStmts);
                boxedArg = boxed;
            } else if (arg instanceof Local) {
                boxedArg = arg;
            } else {
                // Constants or other — skip
                boxedArg = NullConstant.v();
            }

            // arr[i] = boxedArg
            stmts.add(Jimple.v().newAssignStmt(
                    Jimple.v().newArrayRef(arr, IntConstant.v(i)),
                    boxedArg));
        }

        return arr;
    }

    // ========================================================================
    // Helpers: Boxing primitives
    // ========================================================================

    private Local boxPrimitive(Body body, Local primitiveLocal,
                               List<Unit> stmts) {
        return boxPrimitiveValue(body, primitiveLocal, stmts);
    }

    private Local boxPrimitiveValue(Body body, Value primitiveValue,
                                    List<Unit> stmts) {
        Type primType = primitiveValue.getType();
        String wrapperClass;
        String valueOfSig;

        if (primType.equals(IntType.v())) {
            wrapperClass = "java.lang.Integer";
            valueOfSig = "java.lang.Integer valueOf(int)";
        } else if (primType.equals(LongType.v())) {
            wrapperClass = "java.lang.Long";
            valueOfSig = "java.lang.Long valueOf(long)";
        } else if (primType.equals(BooleanType.v())) {
            wrapperClass = "java.lang.Boolean";
            valueOfSig = "java.lang.Boolean valueOf(boolean)";
        } else if (primType.equals(DoubleType.v())) {
            wrapperClass = "java.lang.Double";
            valueOfSig = "java.lang.Double valueOf(double)";
        } else if (primType.equals(FloatType.v())) {
            wrapperClass = "java.lang.Float";
            valueOfSig = "java.lang.Float valueOf(float)";
        } else if (primType.equals(ShortType.v())) {
            wrapperClass = "java.lang.Short";
            valueOfSig = "java.lang.Short valueOf(short)";
        } else if (primType.equals(ByteType.v())) {
            wrapperClass = "java.lang.Byte";
            valueOfSig = "java.lang.Byte valueOf(byte)";
        } else if (primType.equals(CharType.v())) {
            wrapperClass = "java.lang.Character";
            valueOfSig = "java.lang.Character valueOf(char)";
        } else {
            // Unknown primitive, return null
            Local nullLocal = newLocal(body,
                    RefType.v("java.lang.Object"), "$boxNull");
            stmts.add(Jimple.v().newAssignStmt(nullLocal, NullConstant.v()));
            return nullLocal;
        }

        SootClass wrapperSootClass = Scene.v().getSootClass(wrapperClass);
        SootMethod valueOfMethod = wrapperSootClass.getMethod(valueOfSig);

        Local boxed = newLocal(body, RefType.v(wrapperClass), "$boxed");
        stmts.add(Jimple.v().newAssignStmt(boxed,
                Jimple.v().newStaticInvokeExpr(
                        valueOfMethod.makeRef(), primitiveValue)));
        return boxed;
    }

    // ========================================================================
    // Helpers: Local variable management
    // ========================================================================

    private Local newLocal(Body body, Type type, String prefix) {
        String name = prefix + "_" + (tempCounter++);
        Local local = Jimple.v().newLocal(name, type);
        body.getLocals().add(local);
        return local;
    }

    /**
     * Ensure a value is a Local. If it's already a Local, return it.
     * Otherwise, assign it to a new temp local.
     */
    private Local ensureLocal(Body body, Value v, Unit insertPoint,
                              PatchingChain<Unit> units) {
        if (v instanceof Local) return (Local) v;

        Type type = v.getType();
        if (type instanceof NullType) {
            type = RefType.v("java.lang.Object");
        }
        Local tmp = newLocal(body, type, "$propTmp");
        Unit assign = Jimple.v().newAssignStmt(tmp, v);
        units.insertBefore(assign, insertPoint);
        return tmp;
    }

    // ========================================================================
    // Helpers: Insert units after a statement
    // ========================================================================

    private void insertAfter(PatchingChain<Unit> units, Unit point,
                             List<Unit> toInsert) {
        if (toInsert == null || toInsert.isEmpty()) return;
        // Insert in reverse order so they end up in correct order
        Unit prev = point;
        for (Unit u : toInsert) {
            units.insertAfter(u, prev);
            prev = u;
        }
    }

    // ========================================================================
    // Helpers: SootMethodRef construction
    // ========================================================================

    private SootMethodRef makeTracerRef(String methodName,
                                        List<Type> paramTypes,
                                        Type returnType) {
        return Scene.v().makeMethodRef(
                tracerClass, methodName, paramTypes, returnType, true);
    }

    // ========================================================================
    // Helpers: Call site string
    // ========================================================================

    private String callSiteOf(String className, String methodSig, Stmt stmt) {
        int line = stmt.getJavaSourceStartLineNumber();
        String methodName = methodSig;
        // Shorten: use just class.method:line
        int parenIdx = methodSig.indexOf('(');
        if (parenIdx > 0) {
            methodName = methodSig.substring(0, parenIdx);
            int spaceIdx = methodName.lastIndexOf(' ');
            if (spaceIdx > 0) {
                methodName = methodName.substring(spaceIdx + 1);
            }
        }
        return className + "." + methodName + ":" + line;
    }
}