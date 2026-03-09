package edu.uva.liftlab.graphchecker.transformer;

import edu.uva.liftlab.graphchecker.analysis.PhaseInfo;
import edu.uva.liftlab.graphchecker.util.ClassFilterHelper;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.*;
import soot.jimple.*;

import java.util.*;

public class GraphCheckerTransformer extends SceneTransformer {

    public static final PhaseInfo PHASE_INFO = new PhaseInfo("wjtp", "transformer method",
            "Inject OTel context propagation at async boundaries",
            true, false);

    private static final Logger LOG = LoggerFactory.getLogger(GraphCheckerTransformer.class);

    private static final String OTEL_CONTEXT_CLASS = "io.opentelemetry.context.Context";

    /** OTel wrap strategies — only the three natively supported by Context.wrap(). */
    private static final int WRAP_RUNNABLE = 0;
    private static final int WRAP_CALLABLE = 1;
    private static final int WRAP_EXECUTOR = 2;

    public String config_file_path;
    public ClassFilterHelper filter;

    /** Cached SootClass for OTel Context. */
    private SootClass otelContextClass;

    /** Counter for generating unique local variable names. */
    private int tempCounter = 0;

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
        LOG.info("OTel context propagation enabled; starting instrumentation phase: {}", phaseName);

        int classCount = 0;
        int methodCount = 0;

        for (SootClass sc : new ArrayList<>(Scene.v().getApplicationClasses())) {
            if (shouldSkip(sc)) continue;

            classCount++;
            for (SootMethod sm : new ArrayList<>(sc.getMethods())) {
                if (!sm.isConcrete()) continue;
                try {
                    Body body = sm.retrieveActiveBody();
                    if (instrumentBody(body)) methodCount++;
                } catch (Exception e) {
                    LOG.warn("Failed to instrument {}.{}: {}",
                            sc.getName(), sm.getName(), e.getMessage());
                }
            }
        }

        LOG.info("Instrumentation complete: {} classes, {} methods with async boundaries wrapped",
                classCount, methodCount);
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

    /**
     * Scans all statements in {@code body} for async boundary call sites and
     * injects {@code Context.current().wrap(arg)} before each one found.
     *
     * @return true if at least one async boundary was wrapped
     */
    private boolean instrumentBody(Body body) {
        PatchingChain<Unit> units = body.getUnits();
        // Snapshot to avoid ConcurrentModification
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

    /**
     * If {@code stmt} contains an invoke at an async boundary, inserts
     * {@code Context.current().wrap(arg)} before the call and replaces the arg.
     * Only Runnable, Callable, and Executor are wrapped — the three types
     * natively supported by {@code io.opentelemetry.context.Context}.
     *
     * @return true if a wrap was injected
     */
    private boolean tryInjectContextPropagation(Body body, Stmt stmt,
                                                PatchingChain<Unit> units) {
        InvokeExpr invoke = stmt.getInvokeExpr();

        // Never wrap calls into OTel itself
        String declClass = invoke.getMethod().getDeclaringClass().getName();
        if (declClass.startsWith("io.opentelemetry.")) return false;

        int[] match = detectAsyncBoundary(invoke);
        if (match == null) return false;

        int argIdx   = match[0];
        int strategy = match[1];
        if (argIdx >= invoke.getArgCount()) return false;

        Value arg = invoke.getArg(argIdx);
        if (!(arg instanceof Local)) return false;  // can only wrap locals

        Local wrapped = insertContextWrap(body, (Local) arg, strategy, stmt, units);
        invoke.setArg(argIdx, wrapped);
        LOG.debug("Context-wrapped arg {} of {} in {}",
                argIdx, invoke.getMethod().getSignature(),
                body.getMethod().getSignature());
        return true;
    }

    /**
     * Returns {argIndex, strategy} if {@code invoke} is an async boundary
     * call site where context propagation should be injected, otherwise null.
     *
     * <p>Covered patterns:
     * <ul>
     *   <li>Thread.&lt;init&gt;(Runnable)</li>
     *   <li>Any {@code execute(Runnable)} method (Executor, ForkJoinPool, …)</li>
     *   <li>Any {@code submit(Runnable|Callable)} method (ExecutorService, ForkJoinPool, …)</li>
     *   <li>ScheduledExecutorService {@code schedule*} with Runnable/Callable first arg</li>
     *   <li>CompletableFuture.*Async — wrap the trailing Executor arg if present</li>
     *   <li>Guava {@code Futures.addCallback / transformAsync / transform} — wrap trailing Executor</li>
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

        // CompletableFuture.*Async — wrap trailing Executor arg if present
        if (declClass.equals("java.util.concurrent.CompletableFuture")
                && methodName.endsWith("Async") && !params.isEmpty()) {
            int last = params.size() - 1;
            if (isExecutorType(params.get(last))) return new int[]{last, WRAP_EXECUTOR};
        }

        // Guava ListenableFuture helpers: addCallback / transformAsync / transform
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

    // ========================================================================
    // Helpers: Local variable management
    // ========================================================================

    private Local newLocal(Body body, Type type, String prefix) {
        String name = prefix + "_" + (tempCounter++);
        Local local = Jimple.v().newLocal(name, type);
        body.getLocals().add(local);
        return local;
    }
}
