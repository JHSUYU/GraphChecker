package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import edu.uva.liftlab.graphchecker.concolic.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import edu.uva.liftlab.graphchecker.concolic.SmtModelValueCodec;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;

import java.io.BufferedReader;
import java.io.IOException;
import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Runtime bridge injected at symbolic-region roots for the second (concolic)
 * unit-test execution.
 *
 * <p>The class uses reflection for the custom {@code java.lang.System} APIs so
 * GraphChecker itself remains buildable and testable on an ordinary JDK.  On
 * the concolic OpenJDK, one activation row is selected, its live-in objects are
 * symbolized, and the region summary is persisted before the VM destroys its
 * symbolic thread context.</p>
 */
public final class ConcolicRegionRuntime {
    private static final Pattern DEFAULT_EXECUTOR_THREAD_NAME =
            Pattern.compile("^pool-[0-9]+-thread-([0-9]+)$");
    private static final Pattern DEFAULT_OBJECT_IDENTITY_THREAD_NAME =
            Pattern.compile("^([A-Za-z_$][A-Za-z0-9_$.]*?)@"
                    + "[0-9a-fA-F]+$");
    private static final String ROOT_ARGUMENT_PREDICATE_KIND =
            "EXACT_RUNTIME_TYPE";
    private static final Gson GSON = new GsonBuilder().disableHtmlEscaping().create();
    private static final Object CONFIG_LOCK = new Object();
    private static final Object WRITE_LOCK = new Object();
    private static final AtomicLong TOKEN_COUNTER = new AtomicLong();
    private static final AtomicLong ACCESSOR_CONTEXT_TOKEN_COUNTER =
            new AtomicLong();
    private static final AtomicBoolean ENGINE_BUSY = new AtomicBoolean();
    private static final Map<Long, ActiveRegion> ACTIVE = new ConcurrentHashMap<>();
    private static final ThreadLocal<Long> CURRENT_TOKEN = new ThreadLocal<>();
    /**
     * Dynamic root-invocation ownership used only by injected entry/exit
     * hooks.  Every injected root invocation owns a frame once its wrapper
     * begins, including failed or unselected entries whose token stays zero.
     * Keeping this separate from {@link #CURRENT_TOKEN} prevents any nested
     * invocation from closing its selected caller.
     */
    private static final ThreadLocal<Deque<RootInvocationFrame>>
            ROOT_INVOCATION_FRAMES = new ThreadLocal<Deque<RootInvocationFrame>>() {
        @Override
        protected Deque<RootInvocationFrame> initialValue() {
            return new ArrayDeque<>();
        }
    };
    private static final ThreadLocal<AccessorCallContext>
            CURRENT_ACCESSOR_CALL_CONTEXT = new ThreadLocal<>();
    private static final Map<String, Integer> ORDINALS = new LinkedHashMap<>();
    private static final Map<String, ReceiverSelectorState>
            RECEIVER_SELECTOR_STATES = new LinkedHashMap<>();
    private static final Pattern FIELD_SIGNATURE = Pattern.compile(
            "<[^:]+:\\s+[^()<>]+\\s+([^\\s()>]+)>");
    private static final Pattern BRANCH_OPERATOR = Pattern.compile(
            "(?:^|\\s)(==|!=|<=|>=|<|>)(?:\\s|$)");
    private static volatile Configuration configuration;
    private static volatile EngineApi engineApi;

    private ConcolicRegionRuntime() {
    }

    /**
     * Copies a Gson tree without linking against Gson's newer tree-copy
     * methods. Application classpaths can provide an older Gson at runtime;
     * a JSON round trip preserves the value and gives callers an independently
     * mutable result across the supported versions.
     */
    @SuppressWarnings("unchecked")
    static <T extends JsonElement> T copyJsonTree(T source) {
        if (source == null) return null;
        return (T) new JsonParser().parse(GSON.toJson(source));
    }

    /**
     * Starts an observation-only subtree before an instrumented method calls
     * back into this runtime. Soot emits this boundary in the analyzed method
     * so runtime/Gson frames are entered while symbolic propagation is muted.
     * The VM still keeps structural shadow frames balanced.
     */
    public static void pauseObservation() {
        try {
            engine().pausePathCondition();
        } catch (Throwable ignored) {
            // A missing/inactive engine is already handled by the region hook.
        }
    }

    /** Completes the observation-only subtree started by {@link #pauseObservation()}. */
    public static void resumeObservation() {
        try {
            engine().resumePathCondition();
        } catch (Throwable ignored) {
            // Resume is intentionally harmless when no region is active.
        }
    }

    /**
     * Opens the exact accessor invocation selected by one activation's
     * symbolize action. Unlike the general runtime recorder this hook keeps
     * no value fingerprints and emits no trace events: it only retains the
     * caller-site identity and invocation receiver on the current concolic
     * thread until the matching exit hook executes.
     *
     * <p>A zero return means that no selected region is active on this
     * thread. Soot initializes the token to zero and always invokes the exit
     * hook, so disabled and unselected executions remain harmless.</p>
     */
    public static long enterAccessorCallContext(
            String callerMethod, int callUnitIndex, String callSiteId,
            String declaredCallee, Object receiver) {
        try {
            ActiveRegion active = activeRegion();
            String caller = safe(callerMethod);
            String site = safe(callSiteId);
            String callee = safe(declaredCallee);
            if (active == null || caller.isEmpty() || callUnitIndex < 0
                    || callee.isEmpty()
                    || !site.equals(siteId(caller, callUnitIndex))) {
                return 0L;
            }
            AccessorCallContext previous =
                    CURRENT_ACCESSOR_CALL_CONTEXT.get();
            if (previous != null && previous.regionToken != active.token) {
                // A context may never cross a region activation. Clearing a
                // stale stack is fail-closed and prevents an old receiver
                // from authorizing a field read in the new activation.
                CURRENT_ACCESSOR_CALL_CONTEXT.remove();
                previous = null;
            }
            long contextToken = ACCESSOR_CONTEXT_TOKEN_COUNTER
                    .incrementAndGet();
            CURRENT_ACCESSOR_CALL_CONTEXT.set(new AccessorCallContext(
                    contextToken, active.token, Thread.currentThread(),
                    caller, callUnitIndex, site, callee, receiver, previous));
            return contextToken;
        } catch (Throwable ignored) {
            // Instrumentation hooks must not perturb the workload.
            return 0L;
        }
    }

    /** Closes a lightweight accessor scope on normal or exceptional return. */
    public static void exitAccessorCallContext(long contextToken) {
        if (contextToken == 0L) return;
        try {
            AccessorCallContext current =
                    CURRENT_ACCESSOR_CALL_CONTEXT.get();
            if (current == null) return;
            if (current.contextToken == contextToken) {
                if (current.previous == null) {
                    CURRENT_ACCESSOR_CALL_CONTEXT.remove();
                } else {
                    CURRENT_ACCESSOR_CALL_CONTEXT.set(current.previous);
                }
                return;
            }
            // Out-of-order close means malformed instrumentation or a missed
            // exceptional edge. If the token belongs to this stack, discard
            // the whole stack instead of exposing a stale outer context.
            for (AccessorCallContext cursor = current; cursor != null;
                 cursor = cursor.previous) {
                if (cursor.contextToken == contextToken) {
                    CURRENT_ACCESSOR_CALL_CONTEXT.remove();
                    return;
                }
            }
        } catch (Throwable ignored) {
            CURRENT_ACCESSOR_CALL_CONTEXT.remove();
        }
    }

    static void resetForTests() {
        synchronized (CONFIG_LOCK) {
            configuration = null;
            engineApi = null;
        }
        synchronized (ORDINALS) {
            ORDINALS.clear();
            RECEIVER_SELECTOR_STATES.clear();
        }
        ACTIVE.clear();
        CURRENT_TOKEN.remove();
        ROOT_INVOCATION_FRAMES.remove();
        CURRENT_ACCESSOR_CALL_CONTEXT.remove();
        ENGINE_BUSY.set(false);
    }

    static void installEngineApiForTests(Class<?> owner) throws Exception {
        engineApi = new EngineApi(
                testEngineMethod(owner, "startRegion",
                        String.class, String.class),
                testEngineMethod(owner, "symbolize",
                        Object.class, String.class),
                testEngineMethod(owner, "symbolizeField",
                        Object.class, String.class, String.class),
                testEngineMethod(owner, "expression", Object.class),
                testEngineMethod(owner, "finishRegion"),
                testEngineMethod(owner, "pathCondition"),
                testEngineMethod(owner, "pausePathCondition"),
                testEngineMethod(owner, "resumePathCondition"),
                optionalTestEngineMethod(owner, "markBranch",
                        String.class, int.class),
                optionalTestEngineMethod(owner, "branchEvents"),
                testEngineMethod(owner, "endRegion"));
    }

    private static Method optionalTestEngineMethod(
            Class<?> owner, String name, Class<?>... parameters) {
        try {
            return testEngineMethod(owner, name, parameters);
        } catch (NoSuchMethodException ignored) {
            return null;
        }
    }

    private static Method testEngineMethod(Class<?> owner, String name,
                                           Class<?>... parameters)
            throws NoSuchMethodException {
        Method method = owner.getDeclaredMethod(name, parameters);
        if (!method.isAccessible()) {
            method.setAccessible(true);
        }
        return method;
    }

    /**
     * Called at a statically selected same-thread region root with its actual
     * reference arguments.  Primitive parameter slots are null.
     */
    public static long enterRegion(String rootMethod, Object receiver,
                                   Object[] rootArguments) {
        Configuration config = configuration();
        if (config.task == null || rootMethod == null) {
            return 0L;
        }
        int ordinal = nextOrdinal(rootMethod);
        RuntimeTask activation = config.select(rootMethod, ordinal,
                receiver, rootArguments);
        if (activation == null) {
            return 0L;
        }
        return startSymbolicRegion(activation, receiver);
    }

    private static long startSymbolicRegion(RuntimeTask activation,
                                            Object receiver) {
        if (!reserveSymbolicEngine()) {
            writeSkipped(activation, "another concolic region is active");
            return 0L;
        }

        EngineApi api = engine();
        if (!api.available()) {
            releaseSymbolicEngine();
            writeSkipped(activation, "custom concolic System API is unavailable");
            return 0L;
        }
        boolean engineStarted = false;
        boolean pathConditionPaused = false;
        long token = 0L;
        try {
            api.start(activation.regionId, activation.taskId);
            engineStarted = true;
            // Region setup performs reflection, collection lookups and JSON-safe
            // bookkeeping.  Once the first receiver field becomes symbolic,
            // those operations must not become part of the program-under-test
            // path condition.  Explicit native symbolize calls temporarily
            // drain this pause depth around the initializer itself.
            api.pausePathCondition();
            pathConditionPaused = true;
            token = TOKEN_COUNTER.incrementAndGet();
            ActiveRegion active = new ActiveRegion(token, activation, receiver,
                    Thread.currentThread());
            ACTIVE.put(token, active);
            CURRENT_TOKEN.set(token);
            symbolizeReceiverFields(active, api);
            api.resumePathCondition();
            pathConditionPaused = false;
            return token;
        } catch (Throwable throwable) {
            if (token != 0L) {
                ACTIVE.remove(token);
                Long current = CURRENT_TOKEN.get();
                if (current != null && current == token) {
                    CURRENT_TOKEN.remove();
                }
            }
            if (engineStarted) {
                if (pathConditionPaused) {
                    // Best effort only: cleanupAfterFailure is also valid while recording
                    // is paused, but balancing the API keeps diagnostics clear.
                    try {
                        api.resumePathCondition();
                    } catch (Throwable ignored) {
                        // cleanupAfterFailure below owns the definitive cleanup.
                    }
                }
                api.cleanupAfterFailure();
            }
            releaseSymbolicEngine();
            writeSkipped(activation, "engine start failed: " + rootCause(throwable));
            return 0L;
        }
    }

    /**
     * Instrumentation-facing root entry.  A zero-token placeholder is pushed
     * before {@link #enterRegion(String, Object, Object[])} starts the engine,
     * then filled without another allocation.  If entry fails, that exact
     * placeholder remains for the injected exceptional or original-handler
     * cleanup path; this prevents a caught same-root entry failure from
     * exposing an enclosing frame.  Token zero is likewise retained after a
     * successful unselected entry as its exact ownership marker.
     */
    public static long enterRegionFrame(String rootMethod, Object receiver,
                                        Object[] rootArguments) {
        Deque<RootInvocationFrame> frames = ROOT_INVOCATION_FRAMES.get();
        RootInvocationFrame frame = new RootInvocationFrame(rootMethod, 0L);
        frames.push(frame);
        long token = enterRegion(rootMethod, receiver, rootArguments);
        frame.token = token;
        return token;
    }

    private static boolean reserveSymbolicEngine() {
        return ENGINE_BUSY.compareAndSet(false, true);
    }

    private static void releaseSymbolicEngine() {
        ENGINE_BUSY.set(false);
    }

    /** Called once per Java argument immediately after {@link #enterRegion}. */
    public static void symbolizeArgument(long token, int argumentIndex,
                                         Object value, String primitiveValue) {
        ActiveRegion active = ownerRegion(token);
        if (active == null) {
            return;
        }
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!("ARGUMENT".equals(action.location)
                    || "ARGUMENT_FIELD_PATH".equals(action.location))
                    || action.index != argumentIndex) {
                continue;
            }
            if (value == null) {
                if (active.hasAppliedExactNullReferenceAssignment(action)) {
                    // The exact model assignment has already replaced this
                    // declared reference argument with null.  A null Java
                    // reference has no object that the VM can symbolize. The
                    // applied assignment remains recorded, while any zero-PC
                    // concrete branch stays observation-only.
                    continue;
                } else if ("ARGUMENT".equals(action.location)
                        && action.declaresArrayInput(
                        Collections.<String>emptyList())) {
                    symbolize(active, action, null, engine());
                } else {
                    active.unresolved.add(action.symbol
                            + ": primitive argument requires a stack-value model (concrete="
                            + safe(primitiveValue) + ")");
                }
                continue;
            }
            if ("ARGUMENT_FIELD_PATH".equals(action.location)) {
                if (action.fieldPaths.isEmpty()) {
                    active.unresolved.add(action.symbol
                            + ": selective argument has no field paths");
                    continue;
                }
                for (List<String> path : action.fieldPaths) {
                    symbolizeFieldPath(active, action, value, path, engine());
                }
            } else {
                symbolize(active, action, value, engine());
            }
        }
    }

    /**
     * Applies a solver model to the real root argument before ordinary Java
     * control flow consumes it.  Soot writes the returned value back to the
     * parameter local (including an unbox for primitive parameters).  No
     * branch outcome is overridden here: the changed input must make the
     * unmodified branch evaluate to the requested outcome during replay.
     */
    public static Object materializeArgument(long token, int argumentIndex,
                                             Object boxedOrReference,
                                             String primitiveValue) {
        ActiveRegion active = ownerRegion(token);
        if (active == null) return boxedOrReference;
        for (SymbolizeAction action : active.activation.symbolize) {
            if (action.index != argumentIndex
                    || !("ARGUMENT".equals(action.location)
                    || "ARGUMENT_FIELD_PATH".equals(action.location))) {
                continue;
            }
            if (boxedOrReference != null
                    && isPrimitiveBox(boxedOrReference)) {
                return materializePrimitiveValue(active, action,
                        boxedOrReference, null);
            }
            if (boxedOrReference == null) {
                ModelAssignment assignment = active.assignment(action, null);
                if (assignment == null) return null;
                Object modeled = assignment.referenceValue(null);
                if (modeled == UnsupportedReplayValue.INSTANCE) {
                    active.unresolved.add(action.symbol
                            + ": unsupported root reference model "
                            + assignment.valueType + "=" + assignment.value);
                    return null;
                }
                active.recordModelAssignment(assignment);
                return modeled;
            }
            if ("ARGUMENT_FIELD_PATH".equals(action.location)) {
                for (List<String> path : action.fieldPaths) {
                    applyFieldPathModel(active, action, boxedOrReference,
                            path);
                }
            } else {
                ModelAssignment assignment = active.assignment(action, null);
                if (assignment != null) {
                    Object modeled = assignment.referenceValue(
                            boxedOrReference);
                    if (modeled != UnsupportedReplayValue.INSTANCE) {
                        active.recordModelAssignment(assignment);
                        return modeled;
                    }
                    active.unresolved.add(action.symbol
                            + ": unsupported root reference model "
                            + assignment.valueType + "=" + assignment.value);
                }
            }
        }
        return boxedOrReference;
    }

    /** Materializes a reference-valued live-in at its defining Jimple local. */
    public static Object materializeReference(String method, String local,
                                              Object value) {
        ActiveRegion active = activeRegion();
        if (active == null) {
            return value;
        }
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesLocal(method, local)) {
                continue;
            }
            if (!active.materialized.add(action.symbol)) {
                continue;
            }
            Object materialized = value;
            ModelAssignment assignment = active.assignment(action, null);
            if (assignment != null) {
                Object modeled = assignment.referenceValue(value);
                if (modeled == UnsupportedReplayValue.INSTANCE) {
                    active.unresolved.add(action.symbol
                            + ": unsupported local reference model "
                            + assignment.valueType + "=" + assignment.value);
                } else {
                    materialized = modeled;
                    active.recordModelAssignment(assignment);
                }
            }
            if (materialized != null
                    || action.declaresArrayInput(
                    Collections.<String>emptyList())) {
                symbolize(active, action, materialized, engine());
            }
            return materialized;
        }
        return value;
    }

    /**
     * Materializes a primitive live-in and returns a fresh boxed value.  Soot
     * immediately unboxes this result back into the original local, allowing
     * the VM's symbolic field expression to flow into the actual branch.
     */
    public static Object materializePrimitive(String method, String local,
                                              Object boxedValue) {
        ActiveRegion active = activeRegion();
        if (active == null || boxedValue == null) {
            return boxedValue;
        }
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesLocal(method, local)
                    || !action.repeatedPrimitiveAccessor()
                    && !active.materialized.add(action.symbol)) {
                continue;
            }
            return materializePrimitiveValue(active, action, boxedValue,
                    null);
        }
        return boxedValue;
    }

    /**
     * Materializes the primitive value consumed by one exact {@code getstatic}
     * site.  Static JVM state is process-global, so the hook deliberately
     * symbolizes the activation-local consumed value instead of mutating the
     * real static field and leaking a replay assignment into another region.
     */
    public static Object materializeStaticPrimitiveField(
            String method, int unitIndex, String fieldSignature,
            String fieldName, Object boxedValue) {
        ActiveRegion active = activeRegion();
        if (active == null || boxedValue == null) {
            return boxedValue;
        }
        SymbolizeAction selected = null;
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesStaticField(method, unitIndex,
                    fieldSignature, fieldName)) {
                continue;
            }
            if (selected != null && selected != action) {
                active.addUnresolvedOnce(siteId(method, unitIndex)
                        + ": AMBIGUOUS_STATIC_FIELD_MATERIALIZATION");
                return boxedValue;
            }
            selected = action;
        }
        if (selected == null
                || !active.materialized.add(selected.symbol)) {
            return boxedValue;
        }
        List<String> logicalPath = selected.exactStaticFieldPath(
                fieldSignature, fieldName);
        if (logicalPath == null) {
            active.addUnresolvedOnce(siteId(method, unitIndex)
                    + ": STATIC_FIELD_LOGICAL_PATH_OR_DECLARATION_MISMATCH");
            return boxedValue;
        }
        return materializePrimitiveValue(active, selected, boxedValue,
                logicalPath);
    }


    public static void materializeField(String method, int unitIndex,
                                        Object owner, String fieldSignature,
                                        String fieldName) {
        ActiveRegion active = activeRegion();
        if (active == null || owner == null) return;
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesField(method, unitIndex, owner, fieldSignature,
                    fieldName) || !active.materialized.add(action.symbol)) {
                continue;
            }
            Object leafOwner = action.leafOwner(owner);
            if (leafOwner == null || leafOwner == MissingValue.INSTANCE) {
                active.addUnresolvedOnce(action.symbol
                        + ": field owner is unavailable for "
                        + action.fieldPath);
                continue;
            }
            try {
                boolean assignmentFailed = false;
                for (ModelAssignment assignment
                        : active.fieldAssignments(action)) {
                    List<String> path = assignment.path.isEmpty()
                            ? action.fieldPath : assignment.path;
                    Object modeledOwner = path.equals(action.fieldPath)
                            ? leafOwner : resolveFieldPathLeafOwner(owner, path);
                    String modeledField = path.isEmpty() ? ""
                            : path.get(path.size() - 1);
                    if (modeledOwner == null
                            || modeledOwner == MissingValue.INSTANCE
                            || !writeModeledField(modeledOwner, modeledField,
                            assignment)) {
                        active.addUnresolvedOnce(action.symbol + "."
                                + joinFieldPath(path)
                                + ": solver model could not be materialized");
                        assignmentFailed = true;
                        continue;
                    }
                    active.recordModelAssignment(assignment);
                }
                if (assignmentFailed) continue;

                EngineApi api = engine();
                Object value = readField(leafOwner, action.leafField);
                if (value != null && value != MissingValue.INSTANCE
                        && value.getClass().isArray()) {
                    api.symbolize(value, action.symbol);
                    active.recordSymbolizedObject(action.symbol, value);
                } else {
                    api.symbolizeField(leafOwner, action.leafField,
                            action.symbol);
                }
                active.symbolized.add(action.symbol);
            } catch (Throwable throwable) {
                active.addUnresolvedOnce(action.symbol
                        + ": field materialization "
                        + safe(method) + "#u" + unitIndex + " failed: "
                        + rootCause(throwable));
            }
        }
    }


    private static JsonElement engineExpression(String serialized) {
        JsonElement parsed = parseJson(serialized);
        if (!parsed.isJsonObject()) {
            return null;
        }
        JsonElement expression = parsed.getAsJsonObject().get("expression");
        return expression == null || expression.isJsonNull()
                ? null : expression;
    }

    private static String siteId(String method, int unitIndex) {
        return safe(method) + "#u" + unitIndex;
    }

    private static String appendReason(String previous, String next) {
        String left = safe(previous);
        String right = safe(next);
        if (left.isEmpty()) return right;
        if (right.isEmpty()) return left;
        return left + "; " + right;
    }

    /** Returns the activation token owned by the current thread, or zero. */
    public static long activeToken() {
        try {
            RootInvocationFrame frame = ROOT_INVOCATION_FRAMES.get().peek();
            if (frame != null) {
                return frame.token != 0L && ownerRegion(frame.token) != null
                        ? frame.token : 0L;
            }
            Long token = CURRENT_TOKEN.get();
            return token != null && ownerRegion(token) != null ? token : 0L;
        } catch (Throwable ignored) {
            // Instrumentation token lookup must never perturb the workload.
            return 0L;
        }
    }

    /**
     * Captures one real Jimple field-path read immediately before a normal
     * region return. The injected code supplies the exact leaf owner and
     * value; reflection is used only to attest that endpoint, never to
     * manufacture the symbolic expression.
     */
    public static void recordRegionExitFieldOutput(
            String captureBindingId, String outputPort, String outputCell,
            String fieldSignature, Object fieldOwner, Object fieldValue) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request =
                active.activation.regionExitFieldCapture(
                        captureBindingId, outputPort, outputCell,
                        fieldSignature);
        if (request == null) return;

        JsonObject row = new JsonObject();
        row.addProperty("captureBindingId", request.captureBindingId());

        EngineApi api = engine();
        boolean paused = false;
        try {
            api.pausePathCondition();
            paused = true;
            if (fieldOwner == null) {
                throw new IllegalStateException(
                        "normal-exit field endpoint mismatch");
            }
            JsonElement expression = engineExpression(
                    api.expression(fieldValue));
            if (expression == null || expression.isJsonNull()) {
                throw new IllegalStateException(
                        "custom VM returned no normal-exit field expression");
            }
            row.add("expression", expression);
        } catch (Throwable throwable) {
            row.addProperty("expressionError", rootCause(throwable));
            active.addUnresolvedOnce(request.captureBindingId()
                    + ": normal-exit field capture failed: "
                    + rootCause(throwable));
        } finally {
            active.outputCaptures.add(row);
            if (paused) resumePathCondition(active, api);
        }
    }

    /** Normal region exit. */
    public static void exitRegion(long token, Object returnValue,
                                  String primitiveValue) {
        finish(token, "NORMAL", "", returnValue);
    }

    /**
     * Invocation-exact normal cleanup used by injected roots.  This method is
     * intentionally no-throw: instrumentation bookkeeping must never turn a
     * normal program return into an exception (or let the synthetic catch-all
     * pop an enclosing frame a second time).
     */
    public static void exitRegionFrame(String rootMethod, Object returnValue,
                                       String primitiveValue) {
        try {
            RootInvocationFrame frame = popRootInvocationFrame(rootMethod);
            if (frame != null && frame.token != 0L) {
                exitRegion(frame.token, returnValue, primitiveValue);
            }
        } catch (Throwable ignored) {
            // Runtime observation is fail-closed and cannot alter the return.
        }
    }

    /** Exceptional region exit. */
    public static void throwRegion(long token, Throwable throwable) {
        finish(token, "THROW",
                throwable == null ? "" : throwable.getClass().getName(),
                throwable);
    }

    /**
     * Invocation-exact exceptional cleanup used by the synthetic catch-all.
     * The original throwable is rethrown by injected bytecode; consequently
     * every runtime failure is swallowed here so it cannot replace it.
     */
    public static void throwRegionFrame(String rootMethod,
                                        Throwable throwable) {
        try {
            RootInvocationFrame frame = popRootInvocationFrame(rootMethod);
            if (frame != null && frame.token != 0L) {
                throwRegion(frame.token, throwable);
            }
        } catch (Throwable ignored) {
            // Preserve the program's original throwable identity.
        }
    }

    private static RootInvocationFrame popRootInvocationFrame(
            String rootMethod) {
        Deque<RootInvocationFrame> frames = ROOT_INVOCATION_FRAMES.get();
        RootInvocationFrame frame = frames.peek();
        if (frame == null) {
            ROOT_INVOCATION_FRAMES.remove();
            return null;
        }
        boolean matches = rootMethod == null
                ? frame.rootMethod == null
                : rootMethod.equals(frame.rootMethod);
        if (!matches) {
            // Never guess ownership.  In particular, do not expose or close
            // an outer selected frame when instrumentation is malformed.
            return null;
        }
        frames.pop();
        if (frames.isEmpty()) {
            ROOT_INVOCATION_FRAMES.remove();
        }
        return frame;
    }

    private static final class RootInvocationFrame {
        private final String rootMethod;
        private long token;

        private RootInvocationFrame(String rootMethod, long token) {
            this.rootMethod = rootMethod;
            this.token = token;
        }
    }

    /**
     * Reserves a VM-attested branch event immediately before the original
     * conditional executes.  The returned handle is activation-local and is
     * consumed by the matching post-branch resolve hook.
     */
    public static long prepareBranch(String method, int unitIndex,
                                     String expression) {
        ActiveRegion active = activeRegion();
        if (active == null) return 0L;
        try {
            PreparedBranch prepared = active.prepareBranch(method, unitIndex,
                    expression, engine());
            return prepared == null ? 0L : prepared.handle;
        } catch (Throwable throwable) {
            active.addUnresolvedOnce("branch event preparation failed: "
                    + rootCause(throwable));
            return 0L;
        }
    }

    /**
     * Exact-event overload carrying the id returned by the native marker that
     * the instrumented class executes immediately before its original if.
     */
    public static boolean resolveBranch(long preparedHandle, long vmEventId,
                                        String method, int unitIndex,
                                        String expression,
                                        boolean observedOutcome) {
        ActiveRegion active = activeRegion();
        if (active == null) return observedOutcome;
        PreparedBranch prepared = active.takePreparedBranch(preparedHandle);
        if (prepared == null || !prepared.matches(method, unitIndex,
                expression)) {
            active.addUnresolvedOnce("missing or mismatched prepared branch "
                    + preparedHandle + " for " + safe(method) + "#u"
                    + unitIndex);
            // No unverified VM event may be rebound heuristically on a JDK
            // that advertised the exact API.
            return observedOutcome;
        }
        EngineApi api = engine();
        boolean paused = false;
        try {
            api.pausePathCondition();
            paused = true;
            recordBranchPaused(active, api, method, unitIndex, expression,
                    prepared.occurrence, observedOutcome, vmEventId);
            return observedOutcome;
        } catch (Throwable throwable) {
            active.addUnresolvedOnce("branch/PC exact-event observation "
                    + "failed: " + rootCause(throwable));
            return observedOutcome;
        } finally {
            if (paused) resumePathCondition(active, api);
        }
    }

    /**
     * Exact multiway counterpart of {@link #resolveBranch}. Successor ids use
     * the static case-key order followed by default; they are not collapsed
     * into the VM event's case-vs-default Boolean envelope.
     */
    public static int resolveSwitchBranch(
            long preparedHandle, long vmEventId, String method, int unitIndex,
            String expression, String branchKind, String encodedCaseKeys,
            int observedSuccessorIndex) {
        SwitchExpectation expected;
        try {
            expected = SwitchExpectation.parse(branchKind, encodedCaseKeys,
                    observedSuccessorIndex);
        } catch (IllegalArgumentException malformed) {
            ActiveRegion active = activeRegion();
            if (active != null) {
                active.addUnresolvedOnce(safe(method) + "#u" + unitIndex
                        + ": invalid static switch contract: "
                        + rootCause(malformed));
            }
            return observedSuccessorIndex;
        }
        ActiveRegion active = activeRegion();
        if (active == null) return observedSuccessorIndex;
        PreparedBranch prepared = active.takePreparedBranch(preparedHandle);
        if (prepared == null || !prepared.matches(method, unitIndex,
                expression)) {
            active.addUnresolvedOnce("missing or mismatched prepared switch "
                    + preparedHandle + " for " + safe(method) + "#u"
                    + unitIndex);
            return observedSuccessorIndex;
        }
        EngineApi api = engine();
        boolean paused = false;
        try {
            api.pausePathCondition();
            paused = true;
            recordSwitchBranchPaused(active, api, method, unitIndex,
                    expression, prepared.occurrence, expected, vmEventId);
            return observedSuccessorIndex;
        } catch (Throwable throwable) {
            active.addUnresolvedOnce("switch/PC exact-event observation "
                    + "failed: " + rootCause(throwable));
            return observedSuccessorIndex;
        } finally {
            if (paused) resumePathCondition(active, api);
        }
    }

    private static void recordBranchPaused(
            ActiveRegion active, EngineApi api, String method, int unitIndex,
            String expression, int occurrence, boolean observedOutcome,
            long vmEventId) throws Exception {
        String siteId = safe(method) + "#u" + unitIndex;
        JsonElement parsed = parseJson(api.pathCondition());
        JsonArray conditions = parsed.isJsonArray()
                ? parsed.getAsJsonArray() : new JsonArray();
        int baseline = active.lastPathConditionSize;
        VmBranchEventAttestation vmAttestation = attestVmBranchEvent(api,
                active, siteId, expression, observedOutcome, vmEventId,
                occurrence, conditions, baseline);
        int conditionIndex = vmAttestation.valid
                && vmAttestation.conditionIndices.size() == 1
                ? vmAttestation.conditionIndices.get(0) : -1;
        JsonObject mapping = branchMapping(method, unitIndex, expression,
                occurrence);
        mapping.addProperty("observedOutcome", observedOutcome);
        mapping.addProperty("rawPathConditionSize", conditions.size());
        mapping.addProperty("rawPathConditionBaseline", baseline);
        mapping.addProperty("rawConditionIndex", conditionIndex);
        if (conditionIndex >= 0) {
            // Gson 2.2.x exposes its native tree-copy method only at package
            // scope.
            // The parsed path-condition tree is immutable after this point, so
            // retaining this node is safe and compatible with older Gson
            // versions supplied by concrete workloads.
            JsonElement condition = conditions.get(conditionIndex);
            JsonElement semanticCondition = semanticBranchCondition(
                    expression, observedOutcome, condition);
            mapping.add("rawCondition", condition);
            mapping.add("condition", semanticCondition);
            mapping.addProperty("conditionCodePosition",
                    conditionCodePosition(condition));
            String rawOperator = binaryOperator(condition);
            String semanticOperator = binaryOperator(semanticCondition);
            if (!rawOperator.equals(semanticOperator)) {
                mapping.addProperty("conditionNormalization",
                        "JVM_CMP_TRICHOTOMY_TO_JIMPLE_BRANCH_PREDICATE");
            }
            if (vmAttestation.valid) {
                BranchWitness witness = BranchWitness.vmPc(siteId,
                        safe(method), unitIndex, occurrence,
                        observedOutcome, semanticCondition, conditionIndex,
                        branchPredicateMetadata(rawOperator,
                                semanticOperator));
                mapping.add("witness", witness.toJson());
            }
        } else if (vmAttestation.valid
                && vmAttestation.conditionIndices.isEmpty()) {
            mapping.add("concreteObservation",
                    ExactConcreteBranchObservation.attested(siteId,
                            safe(method), unitIndex, occurrence,
                            observedOutcome).toJson());
        }
        boolean pathConditionShrank = conditions.size() < baseline;
        if (pathConditionShrank) {
            mapping.addProperty("mappingWarning",
                    "path condition shrank between branch hooks");
        } else if (!vmAttestation.valid) {
            mapping.addProperty("mappingWarning",
                    "VM exact branch event rejected: "
                            + vmAttestation.error);
        } else if (conditionIndex < 0) {
            mapping.addProperty("mappingWarning",
                    "no newly added target-method condition matches selected branch");
        }
        active.lastPathConditionSize = conditions.size();
        active.branchMappings.add(mapping);
    }

    private static JsonObject branchPredicateMetadata(
            String rawOperator, String semanticOperator) {
        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization",
                safe(rawOperator).equals(safe(semanticOperator))
                        ? BranchWitness.IDENTITY_NORMALIZATION
                        : BranchWitness.CMP_NORMALIZATION);
        return metadata;
    }

    private static void recordSwitchBranchPaused(
            ActiveRegion active, EngineApi api, String method, int unitIndex,
            String expression, int occurrence, SwitchExpectation expected,
            long vmEventId) throws Exception {
        String siteId = safe(method) + "#u" + unitIndex;
        JsonElement parsed = parseJson(api.pathCondition());
        JsonArray conditions = parsed.isJsonArray()
                ? parsed.getAsJsonArray() : new JsonArray();
        int baseline = active.lastPathConditionSize;
        VmBranchEventAttestation attestation = attestVmBranchEvent(api,
                active, siteId, expression, expected.caseArm(), vmEventId,
                occurrence, conditions, baseline, expected);
        List<Integer> conditionIndices = attestation.valid
                ? attestation.conditionIndices
                : Collections.<Integer>emptyList();
        JsonObject mapping = branchMapping(method, unitIndex, expression,
                occurrence);
        mapping.addProperty("branchKind", expected.branchKind);
        mapping.add("switchCaseKeys", GSON.toJsonTree(expected.caseKeys));
        mapping.addProperty("defaultSuccessorIndex",
                expected.defaultSuccessorIndex());
        mapping.addProperty("observedSuccessorIndex",
                expected.observedSuccessorIndex);
        mapping.addProperty("observedOutcome", expected.caseArm());
        mapping.addProperty("rawPathConditionSize", conditions.size());
        mapping.addProperty("rawPathConditionBaseline", baseline);
        mapping.addProperty("rawConditionIndex",
                conditionIndices.size() == 1
                        ? conditionIndices.get(0) : -1);
        mapping.add("conditionIndices", GSON.toJsonTree(conditionIndices));
        JsonArray ownedConditions = new JsonArray();
        for (Integer conditionIndex : conditionIndices) {
            ownedConditions.add(conditions.get(conditionIndex));
        }
        mapping.add("conditions", ownedConditions);
        if (!attestation.valid) {
            mapping.addProperty("mappingWarning",
                    "VM exact switch event rejected: "
                            + attestation.error);
            active.addUnresolvedOnce(siteId
                    + ": exact switch event attestation failed: "
                    + attestation.error);
        } else if (conditionIndices.isEmpty()) {
            mapping.addProperty("mappingWarning",
                    "switch selector was concrete; no symbolic arm guard "
                            + "is available for path closure");
            active.addUnresolvedOnce(siteId
                    + ": exact switch event has no symbolic selector "
                    + "conditions");
        }
        if ("EXPLORE".equals(active.activation.policy(siteId))) {
            active.addUnresolvedOnce(siteId
                    + ": multiway switch requires successor-aware path "
                    + "enumeration; Boolean outcome negation is prohibited");
        }
        active.lastPathConditionSize = conditions.size();
        active.branchMappings.add(mapping);
    }

    private static JsonObject branchMapping(
            String method, int unitIndex, String expression, int occurrence) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", siteId(method, unitIndex));
        mapping.addProperty("method", safe(method));
        mapping.addProperty("unitIndex", unitIndex);
        mapping.addProperty("expression", safe(expression));
        mapping.addProperty("occurrence", occurrence);
        return mapping;
    }

    private static VmBranchEventAttestation attestVmBranchEvent(
            EngineApi api, ActiveRegion active, String siteId,
            String expression, boolean observedOutcome, long eventId,
            int occurrence, JsonArray conditions, int baseline) {
        return attestVmBranchEvent(api, active, siteId, expression,
                observedOutcome, eventId, occurrence, conditions, baseline,
                null);
    }

    private static VmBranchEventAttestation attestVmBranchEvent(
            EngineApi api, ActiveRegion active, String siteId,
            String expression, boolean observedOutcome, long eventId,
            int occurrence, JsonArray conditions, int baseline,
            SwitchExpectation switchExpectation) {
        if (eventId <= 0L) {
            return VmBranchEventAttestation.invalid(
                    "marker returned a non-positive event id");
        }
        final JsonElement parsed;
        try {
            parsed = parseJson(api.branchEvents());
        } catch (Throwable throwable) {
            return VmBranchEventAttestation.invalid(
                    "event stream is not readable: " + rootCause(throwable));
        }
        if (!parsed.isJsonObject()) {
            return VmBranchEventAttestation.invalid(
                    "event stream is not a JSON object");
        }
        JsonObject envelope = parsed.getAsJsonObject();
        if (integer(envelope, "schemaVersion", -1) != 1
                || !"CONCOLIC_THREAD_BRANCH_EVENTS".equals(
                string(envelope, "kind"))
                || !bool(envelope, "active", false)) {
            return VmBranchEventAttestation.invalid(
                    "unexpected or inactive event stream");
        }
        long envelopeContext = longInteger(envelope, "contextId", 0L);
        long envelopeOwner = longInteger(envelope,
                "ownerJavaThreadId", 0L);
        long envelopeOsOwner = longInteger(envelope,
                "ownerOsThreadId", 0L);
        if (envelopeContext <= 0L) {
            return VmBranchEventAttestation.invalid(
                    "missing positive VM thread context id");
        }
        if (envelopeOwner != active.thread.getId()) {
            return VmBranchEventAttestation.invalid(
                    "event stream belongs to Java thread " + envelopeOwner
                            + " instead of " + active.thread.getId());
        }
        if (!safe(active.activation.regionId).equals(
                string(envelope, "regionId"))
                || !safe(active.activation.taskId).equals(
                string(envelope, "taskId"))) {
            return VmBranchEventAttestation.invalid(
                    "event stream region/task does not match owner");
        }

        JsonObject selected = null;
        int matches = 0;
        for (JsonElement candidate : array(envelope, "events")) {
            if (!candidate.isJsonObject()) continue;
            JsonObject event = candidate.getAsJsonObject();
            if (longInteger(event, "eventId", -1L) == eventId) {
                selected = event;
                matches++;
            }
        }
        if (matches != 1 || selected == null) {
            return VmBranchEventAttestation.invalid(
                    "event id " + eventId + " matched " + matches
                            + " records");
        }
        String authority = string(selected, "authority");
        if (!"VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1".equals(authority)) {
            return VmBranchEventAttestation.invalid(
                    "unsupported event authority " + authority);
        }
        if (longInteger(selected, "contextId", 0L) != envelopeContext
                || longInteger(selected, "ownerJavaThreadId", 0L)
                != envelopeOwner
                || longInteger(selected, "ownerOsThreadId", 0L)
                != envelopeOsOwner) {
            return VmBranchEventAttestation.invalid(
                    "event owner/context differs from its thread envelope");
        }
        if (!safe(active.activation.regionId).equals(
                string(selected, "regionId"))
                || !safe(active.activation.taskId).equals(
                string(selected, "taskId"))) {
            return VmBranchEventAttestation.invalid(
                    "event region/task differs from its owner");
        }
        if (!safe(siteId).equals(string(selected, "siteId"))
                || integer(selected, "occurrence", -1) != occurrence) {
            return VmBranchEventAttestation.invalid(
                    "event site/occurrence does not match prepared branch");
        }
        if (bool(selected, "outcome", !observedOutcome)
                != observedOutcome) {
            return VmBranchEventAttestation.invalid(
                    "event outcome differs from observed branch");
        }
        JsonArray indices = array(selected, "conditionIndices");
        if (integer(selected, "conditionCount", -1) != indices.size()) {
            return VmBranchEventAttestation.invalid(
                    "event condition count differs from its index vector");
        }
        if (switchExpectation != null) {
            return attestVmSwitchConditions(selected,
                    switchExpectation, indices, conditions, baseline);
        }
        if (indices.size() > 1) {
            return VmBranchEventAttestation.invalid(
                    "instrumented IfStmt emitted multiple condition indices");
        }
        int conditionIndex = -1;
        if (indices.size() == 1) {
            try {
                conditionIndex = indices.get(0).getAsInt();
            } catch (RuntimeException exception) {
                return VmBranchEventAttestation.invalid(
                        "condition index is not an integer");
            }
            if (conditionIndex < baseline
                    || conditionIndex >= conditions.size()) {
                return VmBranchEventAttestation.invalid(
                        "condition index " + conditionIndex
                                + " is outside new path-condition suffix ["
                                + baseline + "," + conditions.size() + ")");
            }
            if (!branchConditionMatches(expression, observedOutcome,
                    conditions.get(conditionIndex))) {
                return VmBranchEventAttestation.invalid(
                        "selected VM condition does not match the original "
                                + "branch predicate");
            }
        }
        return VmBranchEventAttestation.valid(
                conditionIndex < 0
                        ? Collections.<Integer>emptyList()
                        : Collections.singletonList(conditionIndex));
    }

    private static VmBranchEventAttestation attestVmSwitchConditions(
            JsonObject event, SwitchExpectation expected,
            JsonArray rawIndices, JsonArray conditions, int baseline) {
        int expectedOpcode = "TABLE_SWITCH".equals(expected.branchKind)
                ? 170 : 171;
        if (integer(event, "opcode", -1) != expectedOpcode) {
            return VmBranchEventAttestation.invalid(
                    "event opcode does not match static "
                            + expected.branchKind);
        }
        if (string(event, "codePosition").isEmpty()) {
            return VmBranchEventAttestation.invalid(
                    "switch event has no bytecode position");
        }

        int completeSymbolicCount = expected.caseArm()
                ? 1 : expected.caseKeys.size();
        // The VM still emits an exact event when the selector is concrete.
        // Such an observation can validate replay identity, but it supplies
        // no condition that a path worklist may negate or redirect.
        if (rawIndices.size() == 0) {
            if (conditions.size() != baseline) {
                return VmBranchEventAttestation.invalid(
                        "conditionless switch event does not own an empty "
                                + "path-condition suffix");
            }
            return VmBranchEventAttestation.valid(
                    Collections.<Integer>emptyList());
        }
        if (rawIndices.size() != completeSymbolicCount) {
            return VmBranchEventAttestation.invalid(
                    "switch arm owns " + rawIndices.size()
                            + " conditions; exact arm requires "
                            + completeSymbolicCount);
        }
        if (conditions.size() != baseline + completeSymbolicCount) {
            return VmBranchEventAttestation.invalid(
                    "switch conditions do not form the complete new "
                            + "path-condition suffix");
        }

        List<Integer> indices = new ArrayList<>();
        String selector = "";
        String expectedPosition = string(event, "codePosition");
        for (int offset = 0; offset < rawIndices.size(); offset++) {
            final int conditionIndex;
            try {
                conditionIndex = rawIndices.get(offset).getAsInt();
            } catch (RuntimeException malformed) {
                return VmBranchEventAttestation.invalid(
                        "switch condition index is not an integer");
            }
            if (conditionIndex != baseline + offset) {
                return VmBranchEventAttestation.invalid(
                        "switch condition indices are not the exact ordered "
                                + "new path-condition suffix");
            }
            JsonElement condition = conditions.get(conditionIndex);
            int key = expected.caseArm()
                    ? expected.caseKeys.get(
                    expected.observedSuccessorIndex)
                    : expected.caseKeys.get(offset);
            String operator = expected.caseArm() ? "==" : "!=";
            String matchedSelector = switchSelectorIfMatches(condition,
                    operator, key);
            if (matchedSelector.isEmpty()) {
                return VmBranchEventAttestation.invalid(
                        "switch condition " + offset
                                + " is not selector " + operator + " "
                                + key);
            }
            if (selector.isEmpty()) {
                selector = matchedSelector;
            } else if (!selector.equals(matchedSelector)) {
                return VmBranchEventAttestation.invalid(
                        "switch conditions do not share one selector");
            }
            String conditionPosition = conditionCodePosition(condition);
            if (!conditionPosition.isEmpty()
                    && !expectedPosition.equals(conditionPosition)) {
                return VmBranchEventAttestation.invalid(
                        "switch condition bytecode position differs from "
                                + "its exact event");
            }
            indices.add(conditionIndex);
        }
        return VmBranchEventAttestation.valid(indices);
    }

    private static String switchSelectorIfMatches(
            JsonElement condition, String expectedOperator, int expectedKey) {
        if (condition == null || !condition.isJsonObject()) return "";
        JsonObject object = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(string(object, "_type"))
                || !expectedOperator.equals(string(object, "_op"))) {
            return "";
        }
        JsonElement left = object.get("_left");
        JsonElement right = object.get("_right");
        if (left == null || !left.isJsonObject()
                || right == null || !right.isJsonObject()
                || "ConstExpr".equals(string(left.getAsJsonObject(),
                "_type"))) {
            return "";
        }
        JsonObject constant = right.getAsJsonObject();
        if (!"ConstExpr".equals(string(constant, "_type"))) return "";
        Matcher encoded = Pattern.compile("^Y_I_(-?(?:0|[1-9][0-9]*))$")
                .matcher(string(constant, "_exp"));
        if (!encoded.matches()) return "";
        final int key;
        try {
            key = Integer.parseInt(encoded.group(1));
        } catch (NumberFormatException malformed) {
            return "";
        }
        return key == expectedKey ? left.toString() : "";
    }

    private static void finish(long token, String exitKind,
                               String exceptionType, Object output) {
        ActiveRegion active = ownerRegion(token);
        if (active == null || !active.finished.compareAndSet(false, true)
                || !ACTIVE.remove(token, active)) {
            return;
        }
        // Exact call-site traps normally close every accessor scope first.
        // Region cleanup is the final fail-closed boundary for malformed or
        // externally interrupted control flow.
        clearAccessorCallContexts(token);
        JsonObject result = new JsonObject();
        EngineApi api = engine();
        boolean engineFinished = false;
        try {
            // Everything below is observational bookkeeping.  Pause PC
            // recording before any null checks, Gson work, or string building
            // can reuse a symbolic value and manufacture a false condition.
            api.pausePathCondition();
            populateCompletedResult(result, active, exitKind, exceptionType,
                    output);
            try {
                String expression = api.expression(output);
                result.add("rootOutputExpression", parseJson(expression));
            } catch (Throwable throwable) {
                result.addProperty("outputExpressionError", rootCause(throwable));
            }
            String summary = api.finish();
            engineFinished = true;
            result.add("engineSummary", parseJson(summary));
        } catch (Throwable throwable) {
            result.addProperty("engineSummaryError", rootCause(throwable));
        } finally {
            if (!engineFinished) {
                api.cleanupAfterFailure();
            }
            Long current = CURRENT_TOKEN.get();
            if (current != null && current == token) {
                CURRENT_TOKEN.remove();
            }
            releaseSymbolicEngine();
        }
        // If isolation failed before metadata construction, add the minimum
        // identity only after cleanup has removed the symbolic VM context.
        if (!result.has("event")) {
            addResultIdentity(result, active, exitKind, exceptionType);
        }
        appendResult(result);
    }

    private static void populateCompletedResult(
            JsonObject result, ActiveRegion active, String exitKind,
            String exceptionType, Object output) {
        addResultIdentity(result, active, exitKind, exceptionType);
        if (output instanceof Throwable) {
            result.add("exceptionChain", exceptionChain((Throwable) output));
        }
        active.validateRegionExitFieldCaptures(exitKind);
        result.add("unresolvedInputs", GSON.toJsonTree(active.unresolved));
        result.add("symbolizedInputs", GSON.toJsonTree(active.symbolized));
        result.add("branchMappings", GSON.toJsonTree(active.branchMappings));
        result.add("modelAssignmentsApplied",
                GSON.toJsonTree(active.modelAssignmentsApplied));
        result.add("outputCaptures", GSON.toJsonTree(active.outputCaptures));
    }

    private static void addResultIdentity(
            JsonObject result, ActiveRegion active, String exitKind,
            String exceptionType) {
        result.addProperty("event", "CONCOLIC_REGION_RESULT");
        result.addProperty("schemaVersion", 1);
        result.addProperty("taskId", active.activation.taskId);
        result.addProperty("exitKind", exitKind);
        result.addProperty("exceptionType", safe(exceptionType));
    }

    private static void symbolizeReceiverFields(ActiveRegion active, EngineApi api) {
        for (SymbolizeAction action : active.activation.symbolize) {
            // Nested/shared heap fields are materialized on their real owner at
            // the field-access hook. Looking them up on an unrelated region
            // root is incorrect and creates unresolved heap ports.
            if (!"RECEIVER_FIELD".equals(action.location)) {
                continue;
            }
            if (!action.fieldPath.isEmpty()) {
                symbolizeFieldPath(active, action, active.receiver,
                        action.fieldPath, api);
                continue;
            }
            String fieldName = runtimeFieldName(
                    action.accessFieldSignature, action.cell);
            Object value = readField(active.receiver, fieldName);
            if (value == MissingValue.INSTANCE) {
                active.unresolved.add(action.symbol + ": field not found: " + fieldName);
            } else {
                symbolizeField(active, action, active.receiver, fieldName, api);
            }
        }
    }

    private static void symbolizeField(ActiveRegion active,
                                       SymbolizeAction action,
                                       Object owner, String field,
                                       EngineApi api) {
        symbolizeField(active, action, owner, field, safe(field),
                Collections.singletonList(safe(field)), api);
    }

    private static void symbolizeField(ActiveRegion active,
                                       SymbolizeAction action,
                                       Object owner, String field,
                                       String symbolicPath,
                                       List<String> exactFieldPath,
                                       EngineApi api) {
        String symbol = action.symbol + "." + safe(symbolicPath);
        try {
            Object value = readField(owner, field);
            if (value != null && value != MissingValue.INSTANCE
                    && value.getClass().isArray()) {
                api.symbolize(value, action.symbol);
                active.recordSymbolizedObject(action.symbol, value);
                active.symbolized.add(action.symbol);
            } else {
                api.symbolizeField(owner, field, symbol);
                active.symbolized.add(symbol);
            }
        } catch (Throwable throwable) {
            active.unresolved.add(symbol + ": shallow field symbolize failed: "
                    + rootCause(throwable));
        }
    }

    private static void symbolizeFieldPath(ActiveRegion active,
                                           SymbolizeAction action,
                                           Object root,
                                           List<String> path,
                                           EngineApi api) {
        String label = joinFieldPath(path);
        if (path == null || path.isEmpty() || label.isEmpty()) {
            active.unresolved.add(action.symbol
                    + ": selective argument contains an empty field path");
            return;
        }
        Object leafOwner = resolveFieldPathLeafOwner(root, path);
        if (leafOwner == MissingValue.INSTANCE) {
            active.unresolved.add(action.symbol + "." + label
                    + ": projected field owner is missing");
            return;
        }
        if (leafOwner == null) {
            active.unresolved.add(action.symbol + "." + label
                    + ": projected field owner is null");
            return;
        }
        symbolizeField(active, action, leafOwner,
                path.get(path.size() - 1), label, path, api);
    }

    private static void applyFieldPathModel(ActiveRegion active,
                                            SymbolizeAction action,
                                            Object root,
                                            List<String> path) {
        ModelAssignment assignment = active.assignment(action, path);
        if (assignment == null || path == null || path.isEmpty()) return;
        Object owner = resolveFieldPathLeafOwner(root, path);
        if (owner == null || owner == MissingValue.INSTANCE) {
            active.unresolved.add(action.symbol + "." + joinFieldPath(path)
                    + ": solver-model field owner is unavailable");
            return;
        }
        applyFieldModel(active, action, owner,
                path.get(path.size() - 1), path);
    }

    private static void applyFieldModel(ActiveRegion active,
                                        SymbolizeAction action,
                                        Object owner, String field,
                                        List<String> path) {
        ModelAssignment assignment = active.assignment(action, path);
        if (assignment == null) return;
        if (!writeModeledField(owner, field, assignment)) {
            active.unresolved.add(action.symbol + "." + joinFieldPath(path)
                    + ": solver model could not be written to real field");
            return;
        }
        active.recordModelAssignment(assignment);
    }

    private static Object materializePrimitiveValue(
            ActiveRegion active, SymbolizeAction action, Object concrete,
            List<String> path) {
        ModelAssignment assignment = active.assignment(action, path);
        Object modeled = concrete;
        if (assignment != null) {
            modeled = coerceModelValue(assignment.valueType,
                    assignment.value, concrete == null
                            ? null : concrete.getClass());
            if (modeled == UnsupportedReplayValue.INSTANCE) {
                active.unresolved.add(action.symbol
                        + ": unsupported primitive model "
                        + assignment.valueType + "=" + assignment.value);
                modeled = concrete;
            } else {
                active.recordModelAssignment(assignment);
            }
        }
        Object fresh = freshPrimitiveBox(modeled);
        try {
            engine().symbolizeField(fresh, "value", action.symbol);
            active.symbolized.add(action.symbol);
            return fresh;
        } catch (Throwable throwable) {
            active.unresolved.add(action.symbol
                    + ": primitive materialization failed: "
                    + rootCause(throwable));
            return concrete;
        }
    }

    private static boolean writeModeledField(Object owner, String name,
                                             ModelAssignment assignment) {
        if (owner == null || name == null || name.isEmpty()) return false;
        Class<?> type = owner.getClass();
        while (type != null) {
            try {
                Field field = type.getDeclaredField(name);
                if (Modifier.isStatic(field.getModifiers())) return false;
                if (!field.isAccessible()) field.setAccessible(true);
                Object value = coerceModelValue(assignment.valueType,
                        assignment.value, field.getType());
                if (value == UnsupportedReplayValue.INSTANCE) return false;
                field.set(owner, value);
                return true;
            } catch (NoSuchFieldException ignored) {
                type = type.getSuperclass();
            } catch (Throwable ignored) {
                return false;
            }
        }
        return false;
    }

    /** Resolves no subclass-first fallback: owner, type and name are exact. */
    private static Field exactDeclaredInstanceField(
            Object owner, String fieldSignature) {
        DeclaredField declared = FieldPathSpec.declaredField(fieldSignature);
        if (owner == null || declared == null) return null;
        Class<?> declaringClass = owner.getClass();
        while (declaringClass != null
                && !declared.owner().equals(declaringClass.getName())) {
            declaringClass = declaringClass.getSuperclass();
        }
        if (declaringClass == null) return null;
        try {
            Field field = declaringClass.getDeclaredField(declared.name());
            if (Modifier.isStatic(field.getModifiers())
                    || !javaTypeDescriptor(declared.type()).equals(
                    javaTypeDescriptor(field.getType().getTypeName()))) {
                return null;
            }
            if (!field.isAccessible()) field.setAccessible(true);
            return field;
        } catch (Throwable ignored) {
            return null;
        }
    }

    static Object coerceModelValue(String valueType, String value,
                                   Class<?> requestedType) {
        String type = safe(valueType).toUpperCase();
        String raw = safe(value).trim();
        try {
            // Reference null must be decided before type-specific String
            // decoding.  Otherwise a NULL model for a String-typed field is
            // silently materialized as the four-character string "null".
            if ((requestedType == null || !requestedType.isPrimitive())
                    && ("NULL".equals(type)
                    || "null".equalsIgnoreCase(raw))) {
                return null;
            }
            if (requestedType == boolean.class
                    || requestedType == Boolean.class
                    || "BOOL".equals(type)) {
                return "true".equalsIgnoreCase(raw) || "1".equals(raw);
            }
            if (requestedType == byte.class || requestedType == Byte.class) {
                return Byte.valueOf(raw);
            }
            if (requestedType == short.class || requestedType == Short.class) {
                return Short.valueOf(raw);
            }
            if (requestedType == char.class
                    || requestedType == Character.class) {
                return raw.length() == 1 ? raw.charAt(0)
                        : (char) Integer.parseInt(raw);
            }
            if (requestedType == int.class || requestedType == Integer.class) {
                return Integer.valueOf(raw);
            }
            if (requestedType == long.class || requestedType == Long.class
                    || "INT".equals(type) && requestedType == null) {
                return Long.valueOf(raw);
            }
            if (requestedType == float.class || requestedType == Float.class) {
                String decimal = SmtModelValueCodec.realToJavaLiteral(raw);
                return decimal == null ? UnsupportedReplayValue.INSTANCE
                        : Float.valueOf(decimal);
            }
            if (requestedType == double.class || requestedType == Double.class
                    || "REAL".equals(type) && requestedType == null) {
                String decimal = SmtModelValueCodec.realToJavaLiteral(raw);
                return decimal == null ? UnsupportedReplayValue.INSTANCE
                        : Double.valueOf(decimal);
            }
            if (requestedType == String.class || "STRING".equals(type)) {
                return SmtModelValueCodec.decodeString(raw);
            }
        } catch (RuntimeException ignored) {
            return UnsupportedReplayValue.INSTANCE;
        }
        return UnsupportedReplayValue.INSTANCE;
    }

    private static String unquoteSmtString(String value) {
        return SmtModelValueCodec.decodeString(value);
    }

    private static boolean isPrimitiveBox(Object value) {
        return value instanceof Boolean || value instanceof Byte
                || value instanceof Short || value instanceof Character
                || value instanceof Integer || value instanceof Long
                || value instanceof Float || value instanceof Double;
    }

    static Object resolveFieldPathLeafOwner(Object root, List<String> path) {
        if (root == null || path == null || path.isEmpty()) {
            return MissingValue.INSTANCE;
        }
        Object current = root;
        for (int index = 0; index + 1 < path.size(); index++) {
            String field = safe(path.get(index)).trim();
            if (field.isEmpty()) {
                return MissingValue.INSTANCE;
            }
            current = readPathSegment(current, field);
            if (current == null || current == MissingValue.INSTANCE) {
                return current;
            }
        }
        String leaf = safe(path.get(path.size() - 1)).trim();
        return leaf.isEmpty() ? MissingValue.INSTANCE : current;
    }

    private static Object readPathSegment(Object receiver, String segment) {
        if (receiver == null || segment == null || segment.isEmpty()) {
            return MissingValue.INSTANCE;
        }
        Integer index = pathIndex(segment);
        if (index != null && receiver.getClass().isArray()) {
            return index >= 0 && index < Array.getLength(receiver)
                    ? Array.get(receiver, index) : MissingValue.INSTANCE;
        }
        if (index != null && receiver instanceof List) {
            List<?> values = (List<?>) receiver;
            return index >= 0 && index < values.size()
                    ? values.get(index) : MissingValue.INSTANCE;
        }
        return readField(receiver, segment);
    }

    private static Integer pathIndex(String segment) {
        String value = safe(segment).trim();
        if (value.startsWith("[") && value.endsWith("]")) {
            value = value.substring(1, value.length() - 1).trim();
        }
        if (!value.matches("[0-9]+")) return null;
        try {
            return Integer.valueOf(value);
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    private static String joinFieldPath(List<String> path) {
        if (path == null || path.isEmpty()) {
            return "";
        }
        StringBuilder result = new StringBuilder();
        for (String segment : path) {
            String value = safe(segment).trim();
            if (value.isEmpty()) {
                return "";
            }
            if (result.length() > 0) {
                result.append('.');
            }
            result.append(value);
        }
        return result.toString();
    }

    private static void symbolize(ActiveRegion active, SymbolizeAction action,
                                  Object value, EngineApi api) {
        try {
            boolean liveArray = value != null && value.getClass().isArray();
            boolean declaredArray = action.declaresArrayInput(
                    Collections.<String>emptyList());
            long symbolizationToken = liveArray
                    ? active.objectToken(value) : 0L;
            if (declaredArray && !liveArray) return;
            api.symbolize(value, action.symbol);
            active.symbolized.add(action.symbol);
            if (value != null && !liveArray) {
                active.recordSymbolizedObject(action.symbol, value);
            }
        } catch (Throwable throwable) {
            active.unresolved.add(action.symbol + ": symbolize failed: "
                    + rootCause(throwable));
        }
    }

    private static Object readField(Object receiver, String name) {
        if (receiver == null || name == null || name.isEmpty()) {
            return MissingValue.INSTANCE;
        }
        Class<?> type = receiver.getClass();
        while (type != null) {
            try {
                Field field = type.getDeclaredField(name);
                if (Modifier.isStatic(field.getModifiers())) {
                    return MissingValue.INSTANCE;
                }
                if (!field.isAccessible()) {
                    field.setAccessible(true);
                }
                return field.get(receiver);
            } catch (NoSuchFieldException ignored) {
                type = type.getSuperclass();
            } catch (Throwable throwable) {
                return MissingValue.INSTANCE;
            }
        }
        return MissingValue.INSTANCE;
    }

    private static String normalizeFieldType(String type) {
        return safe(type).trim().replace('/', '.');
    }

    private static ActiveRegion activeRegion() {
        Long token = CURRENT_TOKEN.get();
        return token == null ? null : ownerRegion(token);
    }

    /**
     * Returns null only when no lightweight accessor scope is active. A
     * present scope is authoritative, including a negative result; this is
     * what prevents the recorder fallback from accepting the right site on a
     * different invocation receiver.
     */
    private static Boolean lightweightAccessorContextMatches(
            String callerMethod, int callUnitIndex, String callSiteId,
            String declaredCallee, Object fieldOwner) {
        AccessorCallContext context = CURRENT_ACCESSOR_CALL_CONTEXT.get();
        if (context == null) return null;
        ActiveRegion active = activeRegion();
        if (active == null || context.regionToken != active.token
                || context.thread != Thread.currentThread()) {
            CURRENT_ACCESSOR_CALL_CONTEXT.remove();
            return Boolean.FALSE;
        }
        return context.matches(callerMethod, callUnitIndex, callSiteId,
                declaredCallee, fieldOwner);
    }

    private static void clearAccessorCallContexts(long regionToken) {
        AccessorCallContext context = CURRENT_ACCESSOR_CALL_CONTEXT.get();
        if (context != null && context.regionToken == regionToken) {
            CURRENT_ACCESSOR_CALL_CONTEXT.remove();
        }
    }

    private static ActiveRegion ownerRegion(long token) {
        ActiveRegion active = ACTIVE.get(token);
        return active != null && active.thread == Thread.currentThread()
                ? active : null;
    }

    @SuppressWarnings("deprecation")
    private static Object freshPrimitiveBox(Object value) {
        if (value instanceof Integer) {
            return new Integer(((Integer) value).intValue());
        }
        if (value instanceof Boolean) {
            return new Boolean(((Boolean) value).booleanValue());
        }
        if (value instanceof Long) {
            return new Long(((Long) value).longValue());
        }
        if (value instanceof Byte) {
            return new Byte(((Byte) value).byteValue());
        }
        if (value instanceof Short) {
            return new Short(((Short) value).shortValue());
        }
        if (value instanceof Character) {
            return new Character(((Character) value).charValue());
        }
        if (value instanceof Float) {
            return new Float(((Float) value).floatValue());
        }
        if (value instanceof Double) {
            return new Double(((Double) value).doubleValue());
        }
        return value;
    }

    private static boolean instanceOfName(Class<?> type, String expected) {
        if (type == null || expected == null || expected.isEmpty()) {
            return expected == null || expected.isEmpty();
        }
        if (expected.equals(type.getName())) {
            return true;
        }
        for (Class<?> iface : type.getInterfaces()) {
            if (instanceOfName(iface, expected)) {
                return true;
            }
        }
        return instanceOfName(type.getSuperclass(), expected);
    }

    private static String fieldName(String cell) {
        if (cell == null) {
            return "";
        }
        int projected = cell.indexOf("#field:");
        if (projected >= 0) {
            int end = cell.indexOf('#', projected + 7);
            return cell.substring(projected + 7,
                    end < 0 ? cell.length() : end).trim();
        }
        Matcher matcher = FIELD_SIGNATURE.matcher(cell);
        return matcher.find() ? matcher.group(1) : "";
    }

    static String runtimeFieldName(String field, String cell) {
        String candidate = firstNonBlank(field, cell);
        String parsed = fieldName(candidate);
        return parsed.isEmpty() ? safe(candidate) : parsed;
    }

    private static String conditionCodePosition(JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) {
            return "";
        }
        return string(condition.getAsJsonObject(), "_code_position");
    }

    static boolean branchConditionMatches(String expression, boolean outcome,
                                          JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) {
            return false;
        }
        JsonObject object = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(string(object, "_type"))) {
            Boolean requiredValue = booleanValueRequiredByZeroBranch(
                    expression, outcome);
            Boolean representedValue = representedBooleanValue(object);
            return requiredValue != null && representedValue != null
                    && requiredValue.equals(representedValue);
        }
        Matcher matcher = BRANCH_OPERATOR.matcher(safe(expression));
        if (!matcher.find()) {
            return false;
        }
        String declared = matcher.group(1);
        String expected = outcome ? declared
                : BranchPredicateAlgebra.complementOperator(declared);
        String observed = string(object, "_op");
        if (!observedOperatorImpliesBranch(expected, observed,
                safe(expression).matches(".*\\bnull\\b.*"))) {
            return false;
        }
        if (safe(expression).matches(".*\\bnull\\b.*")) {
            return symbolicNull(object.get("_left"))
                    || symbolicNull(object.get("_right"));
        }
        return true;
    }

    /**
     * Resolves the Java boolean value selected by a Jimple zero test.  JVM
     * boolean-returning operations are consumed by {@code ifeq}/{@code ifne},
     * while the engine can retain the original higher-level Boolean IR (for
     * example an {@code OpStrExpression}) instead of manufacturing a numeric
     * {@code BinaryExpression}.  Attestation must relate those two exact
     * representations without treating arbitrary integer comparisons as
     * Boolean predicates.
     */
    private static Boolean booleanValueRequiredByZeroBranch(
            String expression, boolean outcome) {
        String rendered = safe(expression).trim();
        Matcher matcher = BRANCH_OPERATOR.matcher(rendered);
        if (!matcher.find()) return null;
        String declared = matcher.group(1);
        if (!("==".equals(declared) || "!=".equals(declared))) {
            return null;
        }
        String left = rendered.substring(0, matcher.start()).trim();
        String right = rendered.substring(matcher.end()).trim();
        boolean leftZero = "0".equals(left);
        boolean rightZero = "0".equals(right);
        if (leftZero == rightZero) return null;
        String effective = outcome ? declared
                : BranchPredicateAlgebra.complementOperator(declared);
        return "!=".equals(effective);
    }

    /**
     * Returns the underlying Java boolean represented by an asserted engine
     * condition, or {@code null} when the IR node is value-producing or its
     * semantics are not part of the exact codec.  The operation set mirrors
     * the exact String predicate lowering in both SMT encoders.
     */
    private static Boolean representedBooleanValue(JsonObject condition) {
        if (!"OpStrExpression".equals(string(condition, "_type"))) {
            return null;
        }
        String operation = string(condition, "_name");
        int expectedArity;
        if ("isEmpty".equals(operation)) {
            expectedArity = 1;
        } else if ("contains".equals(operation)
                || "equals".equals(operation)
                || "startsWith".equals(operation)
                || "endsWith".equals(operation)) {
            expectedArity = 2;
        } else {
            return null;
        }
        if (array(condition, "_param_list").size() != expectedArity) {
            return null;
        }
        return !bool(condition, "_is_not", false);
    }

    /**
     * Soot may describe one selected Jimple edge as {@code >=}/{@code <=}
     * while the asserted VM relation for that concrete edge is the stronger
     * {@code >}, {@code <}, or {@code ==}.  Admit only that forward
     * implication, then canonicalize the retained condition to the actual
     * Jimple predicate below.  Numeric {@code *cmp*} bytecodes now propagate
     * their symbolic trichotomy result to the consuming branch; this is not a
     * fallback to the removed concrete compare-witness mechanism.
     */
    private static boolean observedOperatorImpliesBranch(
            String expected, String observed, boolean nullComparison) {
        if (expected.equals(observed)) {
            return true;
        }
        if (nullComparison) {
            return false;
        }
        return ">=".equals(expected)
                && (">".equals(observed) || "==".equals(observed))
                || "<=".equals(expected)
                && ("<".equals(observed) || "==".equals(observed));
    }

    /** Returns the branch-level predicate while retaining the VM operands. */
    private static JsonElement semanticBranchCondition(
            String expression, boolean outcome, JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) {
            return condition;
        }
        JsonObject original = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(string(original, "_type"))) {
            return condition;
        }
        Matcher matcher = BRANCH_OPERATOR.matcher(safe(expression));
        if (!matcher.find()) {
            return condition;
        }
        String expected = outcome ? matcher.group(1)
                : BranchPredicateAlgebra.complementOperator(
                matcher.group(1));
        String observed = string(original, "_op");
        if (!observedOperatorImpliesBranch(expected, observed,
                safe(expression).matches(".*\\bnull\\b.*"))
                || expected.equals(observed)) {
            return condition;
        }
        JsonObject normalized = copyJsonTree(original);
        normalized.addProperty("_op", expected);
        return normalized;
    }

    private static String binaryOperator(JsonElement condition) {
        return condition != null && condition.isJsonObject()
                ? string(condition.getAsJsonObject(), "_op") : "";
    }

    private static boolean symbolicNull(JsonElement element) {
        if (element == null || !element.isJsonObject()) {
            return false;
        }
        JsonObject object = element.getAsJsonObject();
        return "SymbolExpression".equals(string(object, "_type"))
                && "N".equals(string(object, "_exp"));
    }

    private static Configuration configuration() {
        Configuration current = configuration;
        if (current != null) {
            return current;
        }
        synchronized (CONFIG_LOCK) {
            if (configuration == null) {
                configuration = Configuration.load();
            }
            return configuration;
        }
    }

    private static EngineApi engine() {
        EngineApi current = engineApi;
        if (current != null) {
            return current;
        }
        synchronized (CONFIG_LOCK) {
            if (engineApi == null) {
                engineApi = EngineApi.load();
            }
            return engineApi;
        }
    }

    private static void resumePathCondition(ActiveRegion active,
                                            EngineApi api) {
        try {
            api.resumePathCondition();
        } catch (Throwable throwable) {
            active.unresolved.add("path-condition recording resume failed: "
                    + rootCause(throwable));
        }
    }

    private static int nextOrdinal(String key) {
        synchronized (ORDINALS) {
            Integer previous = ORDINALS.get(key);
            int value = previous == null ? 1 : previous + 1;
            ORDINALS.put(key, value);
            return value;
        }
    }

    private static SelectorOccurrence nextSelectorOccurrence(
            String rootMethod, RootArgumentSelector selector,
            RootContextSelector contextSelector, Object receiver) {
        String key = safe(rootMethod) + "\n" + contextSelector.identity()
                + "\n" + selector.identity();
        synchronized (ORDINALS) {
            ReceiverSelectorState state = RECEIVER_SELECTOR_STATES.get(key);
            if (state == null) {
                state = new ReceiverSelectorState();
                RECEIVER_SELECTOR_STATES.put(key, state);
            }
            return state.next(receiver);
        }
    }

    private static int nextRootContextOccurrence(
            String rootMethod, RootContextSelector selector) {
        return nextOrdinal("stable-root-context\n" + safe(rootMethod) + "\n"
                + selector.identity());
    }

    private static void writeSkipped(RuntimeTask activation,
                                     String reason) {
        JsonObject result = new JsonObject();
        result.addProperty("event", "CONCOLIC_REGION_SKIPPED");
        result.addProperty("schemaVersion", 1);
        result.addProperty("taskId", activation.taskId);
        result.addProperty("reason", reason);
        appendResult(result);
    }

    private static void appendResult(JsonObject result) {
        Path output = configuration().resultFile;
        synchronized (WRITE_LOCK) {
            try {
                Path parent = output.toAbsolutePath().getParent();
                if (parent != null) {
                    Files.createDirectories(parent);
                }
                Files.write(output,
                        (GSON.toJson(result) + System.lineSeparator())
                                .getBytes(StandardCharsets.UTF_8),
                        StandardOpenOption.CREATE, StandardOpenOption.APPEND);
            } catch (IOException exception) {
                System.err.println("Causynth could not write concolic result: "
                        + exception);
            }
        }
    }

    private static JsonElement parseJson(String value) {
        if (value == null || value.trim().isEmpty()) {
            return new JsonObject();
        }
        try {
            return new JsonParser().parse(value);
        } catch (RuntimeException ignored) {
            return GSON.toJsonTree(value);
        }
    }

    private static String rootCause(Throwable throwable) {
        Throwable current = throwable;
        while (current instanceof InvocationTargetException
                && ((InvocationTargetException) current).getTargetException() != null) {
            current = ((InvocationTargetException) current).getTargetException();
        }
        return current == null ? "unknown" : current.toString();
    }

    private static JsonArray exceptionChain(Throwable throwable) {
        JsonArray result = new JsonArray();
        Set<Throwable> seen = Collections.newSetFromMap(
                new java.util.IdentityHashMap<Throwable, Boolean>());
        Throwable current = throwable;
        while (current != null && result.size() < 16 && seen.add(current)) {
            JsonObject item = new JsonObject();
            item.addProperty("type", current.getClass().getName());
            item.addProperty("message", safe(current.getMessage()));
            result.add(item);
            current = current.getCause();
        }
        return result;
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }

    private enum MissingValue { INSTANCE }

    private enum UnsupportedReplayValue { INSTANCE }

    private static final class AccessorCallContext {
        private final long contextToken;
        private final long regionToken;
        private final Thread thread;
        private final String callerMethod;
        private final int callUnitIndex;
        private final String callSiteId;
        private final String declaredCallee;
        private final Object receiver;
        private final AccessorCallContext previous;

        private AccessorCallContext(
                long contextToken, long regionToken, Thread thread,
                String callerMethod, int callUnitIndex, String callSiteId,
                String declaredCallee, Object receiver,
                AccessorCallContext previous) {
            this.contextToken = contextToken;
            this.regionToken = regionToken;
            this.thread = thread;
            this.callerMethod = callerMethod;
            this.callUnitIndex = callUnitIndex;
            this.callSiteId = callSiteId;
            this.declaredCallee = declaredCallee;
            this.receiver = receiver;
            this.previous = previous;
        }

        private boolean matches(
                String actualCallerMethod, int actualCallUnitIndex,
                String actualCallSiteId, String actualDeclaredCallee,
                Object actualFieldOwner) {
            return callerMethod.equals(safe(actualCallerMethod))
                    && callUnitIndex == actualCallUnitIndex
                    && callSiteId.equals(safe(actualCallSiteId))
                    && declaredCallee.equals(safe(actualDeclaredCallee))
                    && receiver == actualFieldOwner;
        }
    }

    private static final class SwitchExpectation {
        private final String branchKind;
        private final List<Integer> caseKeys;
        private final int observedSuccessorIndex;

        private SwitchExpectation(String branchKind, List<Integer> caseKeys,
                                  int observedSuccessorIndex) {
            this.branchKind = branchKind;
            this.caseKeys = Collections.unmodifiableList(
                    new ArrayList<>(caseKeys));
            this.observedSuccessorIndex = observedSuccessorIndex;
        }

        private static SwitchExpectation parse(
                String branchKind, String encodedCaseKeys,
                int observedSuccessorIndex) {
            String kind = safe(branchKind);
            if (!("TABLE_SWITCH".equals(kind)
                    || "LOOKUP_SWITCH".equals(kind))) {
                throw new IllegalArgumentException(
                        "unsupported branch kind " + kind);
            }
            List<Integer> keys = new ArrayList<>();
            String encoded = safe(encodedCaseKeys);
            if (!encoded.isEmpty()) {
                for (String token : encoded.split(",", -1)) {
                    if (!token.matches("-?(?:0|[1-9][0-9]*)")) {
                        throw new IllegalArgumentException(
                                "malformed switch key " + token);
                    }
                    try {
                        keys.add(Integer.parseInt(token));
                    } catch (NumberFormatException malformed) {
                        throw new IllegalArgumentException(
                                "switch key outside int domain " + token,
                                malformed);
                    }
                }
            }
            if (keys.isEmpty() || observedSuccessorIndex < 0
                    || observedSuccessorIndex > keys.size()) {
                throw new IllegalArgumentException(
                        "successor " + observedSuccessorIndex
                                + " outside switch domain [0,"
                                + keys.size() + "]");
            }
            if ("TABLE_SWITCH".equals(kind)) {
                for (int index = 1; index < keys.size(); index++) {
                    if ((long) keys.get(index - 1) + 1L
                            != (long) keys.get(index)) {
                        throw new IllegalArgumentException(
                                "tableswitch keys are not dense/ordered");
                    }
                }
            } else {
                Set<Integer> distinct = new LinkedHashSet<>(keys);
                if (distinct.size() != keys.size()) {
                    throw new IllegalArgumentException(
                            "lookupswitch keys are not unique");
                }
            }
            return new SwitchExpectation(kind, keys,
                    observedSuccessorIndex);
        }

        private int defaultSuccessorIndex() {
            return caseKeys.size();
        }

        private boolean caseArm() {
            return observedSuccessorIndex < caseKeys.size();
        }
    }

    private static final class VmBranchEventAttestation {
        private final List<Integer> conditionIndices;
        private final boolean valid;
        private final String error;

        private VmBranchEventAttestation(List<Integer> conditionIndices,
                                         boolean valid,
                                         String error) {
            this.conditionIndices = Collections.unmodifiableList(
                    new ArrayList<>(conditionIndices));
            this.valid = valid;
            this.error = safe(error);
        }

        private static VmBranchEventAttestation valid(
                List<Integer> conditionIndices) {
            return new VmBranchEventAttestation(conditionIndices, true, "");
        }

        private static VmBranchEventAttestation invalid(String error) {
            return new VmBranchEventAttestation(
                    Collections.<Integer>emptyList(), false, error);
        }
    }

    private static final class PreparedBranch {
        private final long handle;
        private final String method;
        private final int unitIndex;
        private final String expression;
        private final int occurrence;

        private PreparedBranch(long handle, String method, int unitIndex,
                               String expression, int occurrence) {
            this.handle = handle;
            this.method = safe(method);
            this.unitIndex = unitIndex;
            this.expression = safe(expression);
            this.occurrence = occurrence;
        }

        private boolean matches(String actualMethod, int actualUnitIndex,
                                String actualExpression) {
            return method.equals(safe(actualMethod))
                    && unitIndex == actualUnitIndex
                    && expression.equals(safe(actualExpression));
        }
    }

    private static final class ActiveRegion {
        private final long token;
        private final RuntimeTask activation;
        private final Object receiver;
        private final Thread thread;
        private final AtomicBoolean finished = new AtomicBoolean();
        private final List<String> symbolized = new ArrayList<>();
        private final List<String> unresolved = new ArrayList<>();
        private final Set<String> unresolvedUnique = new LinkedHashSet<>();
        private final List<JsonObject> branchMappings = new ArrayList<>();
        private final List<JsonObject> modelAssignmentsApplied =
                new ArrayList<>();
        private final List<JsonObject> outputCaptures = new ArrayList<>();
        private final Set<String> materialized = new LinkedHashSet<>();
        private final Set<String> appliedModelAssignments =
                new LinkedHashSet<>();
        private final Map<String, Integer> branchOccurrences =
                new LinkedHashMap<>();
        private final Map<Long, PreparedBranch> preparedBranches =
                new LinkedHashMap<>();
        private final IdentityHashMap<Object, Long> objectTokens =
                new IdentityHashMap<>();
        private final Map<Long, String> symbolizedObjectPorts =
                new LinkedHashMap<>();
        private long nextObjectToken = 1L;
        private long preparedBranchSequence;
        private int lastPathConditionSize;

        private ActiveRegion(long token, RuntimeTask activation,
                             Object receiver, Thread thread) {
            this.token = token;
            this.activation = activation;
            this.receiver = receiver;
            this.thread = thread;
        }

        private int nextBranchOccurrence(String siteId) {
            Integer previous = branchOccurrences.get(siteId);
            int occurrence = previous == null ? 1 : previous + 1;
            branchOccurrences.put(siteId, occurrence);
            return occurrence;
        }

        private PreparedBranch prepareBranch(
                String method, int unitIndex, String expression,
                EngineApi api) throws Exception {
            String site = safe(method) + "#u" + unitIndex;
            if (!api.exactBranchEventsAvailable()) {
                addUnresolvedOnce(site
                        + ": custom JDK exact branch-event API is required");
                return null;
            }
            int occurrence = nextBranchOccurrence(site);
            long sequence = ++preparedBranchSequence;
            if (sequence > Integer.MAX_VALUE) {
                addUnresolvedOnce(site + "#" + occurrence
                        + ": prepared branch sequence overflow");
                return null;
            }
            long handle = (sequence << 32)
                    | (occurrence & 0xffffffffL);
            PreparedBranch prepared = new PreparedBranch(handle, method,
                    unitIndex, expression, occurrence);
            preparedBranches.put(handle, prepared);
            return prepared;
        }

        private PreparedBranch takePreparedBranch(long handle) {
            return handle <= 0L ? null : preparedBranches.remove(handle);
        }

        private void validateRegionExitFieldCaptures(String exitKind) {
            boolean normal = "NORMAL".equals(exitKind);
            for (OutputCaptureSpec request : activation.outputCaptures) {
                int matches = 0;
                for (JsonObject capture : outputCaptures) {
                    if (request.captureBindingId().equals(
                            string(capture, "captureBindingId"))) {
                        matches++;
                    }
                }
                if (normal && matches != 1) {
                    addUnresolvedOnce(request.captureBindingId()
                            + ": expected one normal-exit field capture, got "
                            + matches);
                } else if (!normal && matches != 0) {
                    addUnresolvedOnce(request.captureBindingId()
                            + ": field output captured on " + exitKind
                            + " exit");
                }
            }
            if (!normal) outputCaptures.clear();
        }

        private void addUnresolvedOnce(String detail) {
            String value = safe(detail);
            if (!value.isEmpty() && unresolvedUnique.add(value)) {
                unresolved.add(value);
            }
        }

        private long objectToken(Object value) {
            if (value == null) return 0L;
            Long existing = objectTokens.get(value);
            if (existing != null) return existing;
            long token = nextObjectToken++;
            objectTokens.put(value, token);
            return token;
        }

        private void recordSymbolizedObject(String symbol, Object value) {
            long objectToken = objectToken(value);
            String previous = symbolizedObjectPorts.get(objectToken);
            symbolizedObjectPorts.put(objectToken, previous == null
                    || previous.equals(symbol) ? symbol : "");
        }

        private ModelAssignment assignment(SymbolizeAction action,
                                           List<String> path) {
            ModelAssignment selected = null;
            for (ModelAssignment candidate : activation.modelAssignments) {
                if (!candidate.matches(action, path)
                        || !action.repeatedPrimitiveAccessor()
                        && appliedModelAssignments.contains(candidate.key)) {
                    continue;
                }
                if (selected != null) {
                    addUnresolvedOnce(action.symbol
                            + ": ambiguous model assignments");
                    return null;
                }
                selected = candidate;
            }
            return selected;
        }

        private boolean hasAppliedExactNullReferenceAssignment(
                SymbolizeAction action) {
            if (action == null || !action.declaresReferenceInput()) {
                return false;
            }
            int matches = 0;
            for (ModelAssignment assignment : activation.modelAssignments) {
                if (assignment.matches(action, null)
                        && assignment.exactNullReferenceModel(action)
                        && appliedModelAssignments.contains(assignment.key)) {
                    matches++;
                }
            }
            return matches == 1;
        }

        private List<ModelAssignment> fieldAssignments(
                SymbolizeAction action) {
            List<ModelAssignment> result = new ArrayList<>();
            for (ModelAssignment assignment : activation.modelAssignments) {
                if (assignment.targetsFieldAccess(action)
                        && !appliedModelAssignments.contains(assignment.key)) {
                    result.add(assignment);
                }
            }
            return result;
        }

        private void recordModelAssignment(ModelAssignment assignment) {
            if (appliedModelAssignments.add(assignment.key)) {
                modelAssignmentsApplied.add(assignment.appliedJson());
            }
        }
    }


    private static final class SymbolizeAction {
        private final String symbol;
        private final String cell;
        private final String location;
        private final int index;
        private final List<List<String>> fieldPaths;
        private final String bindingMode;
        private final String method;
        private final String local;
        private final String leafField;
        private final String leafOwnerClass;
        private final String accessField;
        private final String accessOwnerClass;
        private final String accessFieldSignature;
        private final String accessMethod;
        private final int accessUnitIndex;
        private final String accessorCallerMethod;
        private final int accessorCallUnitIndex;
        private final String accessorDeclaredCallee;
        private final String accessorImplementationMethod;
        private final List<String> fieldPath;
        private final String javaType;
        private final Map<String, String> leafFieldSignaturesByPath =
                new LinkedHashMap<>();

        private SymbolizeAction(JsonObject json) {
            this.symbol = string(json, "symbol");
            this.cell = string(json, "cell");
            this.location = string(json, "location");
            this.index = integer(json, "index", -1);
            this.bindingMode = string(json, "bindingMode");
            this.javaType = string(json, "javaType");
            this.method = string(json, "method");
            this.local = string(json, "local");
            this.fieldPath = new ArrayList<>(
                    FieldPathSpec.stringArray(json, "fieldPath"));
            this.accessField = this.fieldPath.isEmpty() ? ""
                    : this.fieldPath.get(0);
            this.accessFieldSignature = string(json,
                    "accessFieldSignature");
            DeclaredField accessDeclaration = FieldPathSpec.declaredField(
                    this.accessFieldSignature);
            this.accessOwnerClass = accessDeclaration == null ? ""
                    : accessDeclaration.owner();
            this.accessMethod = string(json, "accessMethod");
            this.accessUnitIndex = integer(json, "accessUnitIndex", -1);
            this.accessorCallerMethod = string(json,
                    "accessorCallerMethod");
            this.accessorCallUnitIndex = integer(json,
                    "accessorCallUnitIndex", -1);
            this.accessorDeclaredCallee = string(json,
                    "accessorDeclaredCallee");
            this.accessorImplementationMethod = string(json,
                    "accessorImplementationMethod");
            this.leafField = this.fieldPath.isEmpty() ? ""
                    : this.fieldPath.get(this.fieldPath.size() - 1);
            String explicitLeafSignature = string(json,
                    "leafFieldSignature");
            DeclaredField leafDeclaration = FieldPathSpec.declaredField(
                    explicitLeafSignature);
            this.leafOwnerClass = leafDeclaration == null ? ""
                    : leafDeclaration.owner();
            this.fieldPaths = new ArrayList<>(
                    FieldPathSpec.paths(json, "fieldPaths"));
            for (JsonElement declarationElement : array(json,
                    "fieldPathLeafDeclarations")) {
                if (!declarationElement.isJsonObject()) continue;
                JsonObject declaration = declarationElement
                        .getAsJsonObject();
                List<String> path = new ArrayList<>();
                for (JsonElement segment : array(declaration,
                        "fieldPath")) {
                    if (segment.isJsonPrimitive()) {
                        path.add(segment.getAsString());
                    }
                }
                String signature = string(declaration,
                        "fieldSignature");
                if (!path.isEmpty() && FieldPathSpec.declaredField(
                        signature) != null) {
                    leafFieldSignaturesByPath.put(joinFieldPath(path),
                            signature);
                }
            }
            if (!this.fieldPath.isEmpty()
                    && FieldPathSpec.declaredField(
                    explicitLeafSignature) != null) {
                leafFieldSignaturesByPath.put(joinFieldPath(
                        this.fieldPath), explicitLeafSignature);
            }
        }

        private boolean declaresArrayInput(List<String> actualPath) {
            String pathSignature = leafFieldSignaturesByPath.get(
                    joinFieldPath(actualPath));
            DeclaredField declared = FieldPathSpec.declaredField(
                    pathSignature);
            if (declared != null
                    && javaTypeDescriptor(declared.type()).startsWith("[")) {
                return true;
            }
            for (String signature : new String[]{accessFieldSignature,
                    cell}) {
                declared = FieldPathSpec.declaredField(signature);
                if (declared != null
                        && javaTypeDescriptor(declared.type()).startsWith("[")
                        && (actualPath == null || actualPath.isEmpty()
                        || declared.name().equals(actualPath.get(
                        actualPath.size() - 1)))) {
                    return true;
                }
            }
            return javaTypeDescriptor(javaType).startsWith("[");
        }

        private boolean declaresReferenceInput() {
            String descriptor = javaTypeDescriptor(javaType);
            return descriptor.startsWith("L") || descriptor.startsWith("[");
        }

        private boolean declaresJavaString() {
            return "Ljava/lang/String;".equals(
                    javaTypeDescriptor(javaType));
        }

        private boolean matchesLocal(String actualMethod, String actualLocal) {
            return "LOCAL_DEFINITION".equals(bindingMode)
                    && method.equals(safe(actualMethod))
                    && local.equals(safe(actualLocal));
        }

        private boolean repeatedPrimitiveAccessor() {
            return "LOCAL_DEFINITION".equals(bindingMode)
                    && "CALL_RETURN".equals(location)
                    && MaterializationSpec
                    .repeatedPrimitiveAccessorReturn(cell);
        }

        private boolean matchesStaticField(String actualMethod,
                                           int actualUnitIndex,
                                           String signature,
                                           String actualField) {
            if (!("FIELD_ACCESS".equals(bindingMode)
                    || "HEAP_OBJECT_FIELD".equals(location))) {
                return false;
            }
            String exactSignature = safe(signature);
            DeclaredField declaration = FieldPathSpec.declaredField(
                    exactSignature);
            if (declaration == null
                    || !declaration.name().equals(safe(actualField))
                    || !accessField.equals(safe(actualField))) {
                return false;
            }
            if (!accessOwnerClass.isEmpty()
                    && !accessOwnerClass.equals(declaration.owner())) {
                return false;
            }
            if (!accessFieldSignature.isEmpty()
                    && !accessFieldSignature.equals(exactSignature)) {
                return false;
            }
            boolean accessSiteConstrained = !accessMethod.isEmpty()
                    || accessUnitIndex >= 0;
            if (!accessSiteConstrained) {
                return false;
            }
            return accessMethod.equals(safe(actualMethod))
                    && accessUnitIndex == actualUnitIndex
                    && (cell.contains(exactSignature)
                    || accessFieldSignature.equals(exactSignature));
        }

        /**
         * Reconstructs the activation's logical path for an exact getstatic
         * materialization.  The runtime hook observes the consumed primitive
         * value rather than mutating process-global state, but model matching
         * must still use the same declared field path that the solver bound.
         */
        private List<String> exactStaticFieldPath(
                String signature, String actualField) {
            String exactSignature = safe(signature);
            DeclaredField declaration = FieldPathSpec.declaredField(
                    exactSignature);
            if (declaration == null
                    || !declaration.name().equals(safe(actualField))
                    || fieldPath.size() != 1
                    || !fieldPath.get(0).equals(actualField)
                    || !accessField.equals(actualField)
                    || !accessFieldSignature.isEmpty()
                    && !accessFieldSignature.equals(exactSignature)
                    || !accessOwnerClass.isEmpty()
                    && !accessOwnerClass.equals(declaration.owner())
                    || !javaType.isEmpty()
                    && !javaTypeDescriptor(javaType).equals(
                    javaTypeDescriptor(declaration.type()))) {
                return null;
            }
            return Collections.singletonList(actualField);
        }

        private boolean matchesField(String actualMethod,
                                     int actualUnitIndex, Object owner,
                                     String signature, String actualField) {
            return matchesField(actualMethod, actualUnitIndex, owner,
                    signature, actualField, null);
        }

        private boolean matchesField(String actualMethod,
                                     int actualUnitIndex, Object owner,
                                     String signature, String actualField,
                                     Boolean accessorContextOverride) {
            if (!("FIELD_ACCESS".equals(bindingMode)
                    || "HEAP_OBJECT_FIELD".equals(location))) {
                return false;
            }
            boolean accessSiteConstrained = !accessMethod.isEmpty()
                    || accessUnitIndex >= 0;
            if (accessSiteConstrained
                    && (!accessMethod.equals(safe(actualMethod))
                    || accessUnitIndex != actualUnitIndex)) {
                return false;
            }
            boolean accessorConstrained = !accessorCallerMethod.isEmpty()
                    || accessorCallUnitIndex >= 0
                    || !accessorDeclaredCallee.isEmpty()
                    || !accessorImplementationMethod.isEmpty();
            String accessorSiteId = accessorCallerMethod.isEmpty()
                    || accessorCallUnitIndex < 0 ? ""
                    : accessorCallerMethod + "#u" + accessorCallUnitIndex;
            Boolean lightweightContext = accessorContextOverride != null
                    ? null : lightweightAccessorContextMatches(
                    accessorCallerMethod, accessorCallUnitIndex,
                    accessorSiteId, accessorDeclaredCallee, owner);
            boolean accessorContextMatches = accessorContextOverride != null
                    ? accessorContextOverride
                    : lightweightContext != null
                    ? lightweightContext
                    : CausynthTraceRecorder.currentCallParentSiteMatches(
                    accessorCallerMethod, accessorCallUnitIndex,
                    accessorSiteId, accessorDeclaredCallee);
            if (accessorConstrained
                    && (!accessorImplementationMethod.equals(
                    safe(actualMethod))
                    || !accessorContextMatches)) {
                return false;
            }
            if (!accessField.equals(safe(actualField))) {
                return false;
            }
            if (!accessOwnerClass.isEmpty()
                    && !instanceOfName(owner.getClass(), accessOwnerClass)) {
                return false;
            }
            if (accessSiteConstrained
                    && (accessOwnerClass.isEmpty()
                    || accessFieldSignature.isEmpty()
                    || !accessFieldSignature.equals(safe(signature)))) {
                return false;
            }
            // A projection rooted at a method return/local may not carry a
            // statically known access owner.  Matching such an action by the
            // leaf name alone aliases unrelated same-named fields (for
            // example ExportedBlockKeys.allKeys and
            // BlockTokenSecretManager.allKeys).  Only an explicit owner or an
            // exact declared-field signature is authoritative enough to
            // symbolize a concrete field access.
            return !accessOwnerClass.isEmpty()
                    || !safe(signature).isEmpty()
                    && cell.contains(safe(signature));
        }

        private Object leafOwner(Object accessOwner) {
            Object current = accessOwner;
            // The hook runs before the first field read.  Follow every path
            // component except the leaf; the VM then symbolizes only that
            // leaf on its actual concrete owner (including inherited fields).
            for (int index = 0; index + 1 < fieldPath.size(); index++) {
                current = readField(current, fieldPath.get(index));
                if (current == null || current == MissingValue.INSTANCE) {
                    return current;
                }
            }
            return current;
        }

        /**
         * Returns the exact declaration of the scalar/array leaf that will
         * actually be symbolized.  For a projected path the root hook
         * signature is deliberately not a fallback: it describes a
         * different heap field and would turn an intermediate reference into
         * a primitive action.
         */
        private String exactLeafFieldSignature() {
            String explicit = leafFieldSignaturesByPath.get(
                    joinFieldPath(fieldPath));
            DeclaredField declaration = FieldPathSpec.declaredField(
                    explicit);
            if (declaration != null
                    && declaration.name().equals(leafField)) {
                return explicit;
            }
            if (fieldPath.size() != 1) {
                return "";
            }
            String selected = "";
            for (String candidate : new String[]{accessFieldSignature,
                    cell}) {
                declaration = FieldPathSpec.declaredField(candidate);
                if (declaration == null
                        || !declaration.name().equals(leafField)) {
                    continue;
                }
                if (!selected.isEmpty() && !selected.equals(candidate)) {
                    return "";
                }
                selected = candidate;
            }
            return selected;
        }
    }

    private static String exactFieldIdentity(DeclaredField declared) {
        return declared == null ? ""
                : declared.owner() + "\u0000"
                + normalizeFieldType(declared.type())
                + "\u0000" + declared.name();
    }

    /**
     * The frozen JDK API accepts only a field name.  It walks every
     * non-static field in the runtime hierarchy, so an exact Soot signature
     * is safe to pass only when that name occurs once in the whole hierarchy.
     */
    private static boolean uniqueNameResolvesExactDeclaredField(
            Object owner, String fieldSignature) {
        DeclaredField declared = FieldPathSpec.declaredField(fieldSignature);
        Field exact = exactDeclaredInstanceField(owner, fieldSignature);
        if (owner == null || declared == null || exact == null) return false;
        int occurrences = 0;
        Class<?> current = owner.getClass();
        while (current != null) {
            for (Field candidate : current.getDeclaredFields()) {
                if (!Modifier.isStatic(candidate.getModifiers())
                        && declared.name().equals(candidate.getName())) {
                    occurrences++;
                }
            }
            current = current.getSuperclass();
        }
        return occurrences == 1
                && exact.getDeclaringClass().getName().equals(
                declared.owner());
    }

    /** One scalar or reference assignment returned by a path-flip solve. */
    private static final class ModelAssignment {
        private final String key;
        private final String engineSymbol;
        private final String inputSymbol;
        private final String valueType;
        private final String value;
        private final boolean modelIsNull;
        private final JsonObject target;
        private final List<String> path = new ArrayList<>();

        private ModelAssignment(JsonObject json) {
            this.engineSymbol = string(json, "engineSymbol");
            this.inputSymbol = string(json, "inputSymbol");
            this.valueType = string(json, "valueType");
            this.value = string(json, "value");
            this.modelIsNull = bool(json, "modelIsNull", false);
            this.target = copyJsonTree(object(json, "target"));
            for (JsonElement element : array(json,
                    "materializationPath")) {
                if (element.isJsonPrimitive()) {
                    path.add(element.getAsString());
                }
            }
            this.key = firstNonBlank(string(json, "modelAssignmentKey"),
                    engineSymbol,
                    inputSymbol + ":" + joinFieldPath(path));
        }

        private boolean exactNullReferenceModel(SymbolizeAction action) {
            return action != null && action.declaresReferenceInput()
                    && inputSymbol.equals(action.symbol)
                    && modelIsNull
                    && ("NULL".equalsIgnoreCase(valueType)
                    || "null".equalsIgnoreCase(value));
        }

        private boolean matches(SymbolizeAction action,
                                List<String> actualPath) {
            if (!inputSymbol.equals(action.symbol)) return false;
            if (path.isEmpty()) {
                return actualPath == null || actualPath.isEmpty()
                        || action.fieldPath.equals(actualPath);
            }
            return actualPath != null && path.equals(actualPath);
        }

        private boolean targetsFieldAccess(SymbolizeAction action) {
            if (!inputSymbol.equals(action.symbol)) return false;
            if (path.isEmpty()) return true;
            if (action.fieldPath.isEmpty()
                    || path.size() < action.fieldPath.size()) return false;
            for (int index = 0; index < action.fieldPath.size(); index++) {
                if (!path.get(index).equals(action.fieldPath.get(index))) {
                    return false;
                }
            }
            return true;
        }

        private Object referenceValue(Object concrete) {
            if ("STRING".equalsIgnoreCase(valueType)) {
                return unquoteSmtString(value);
            }
            if ("NULL".equalsIgnoreCase(valueType)
                    || "null".equalsIgnoreCase(value)) return null;
            if ("UNCHANGED".equalsIgnoreCase(valueType)) return concrete;
            return UnsupportedReplayValue.INSTANCE;
        }

        private JsonObject appliedJson() {
            JsonObject result = new JsonObject();
            result.addProperty("modelAssignmentKey", key);
            return result;
        }
    }


    private static final class RootContextSelector {
        private final boolean present;
        private final String receiverRuntimeClass;
        private final String threadName;
        private final int invocationOrdinalWithinContext;

        private RootContextSelector(boolean present,
                                    String receiverRuntimeClass,
                                    String threadName,
                                    int invocationOrdinalWithinContext) {
            this.present = present;
            this.receiverRuntimeClass = safe(receiverRuntimeClass);
            this.threadName = stableReplayThreadContext(threadName);
            this.invocationOrdinalWithinContext =
                    invocationOrdinalWithinContext;
        }

        private static RootContextSelector from(JsonObject selector) {
            String kind = string(selector, "kind");
            if ("GLOBAL_INVOCATION".equals(kind)) {
                return new RootContextSelector(false, "", "", -1);
            }
            String receiverClass = string(selector, "receiverClass");
            String thread = selector.has("thread")
                    ? string(selector, "thread") : "";
            int ordinal = integer(selector, "ordinal", -1);
            if (receiverClass.isEmpty()
                    || !receiverClass.equals(receiverClass.trim())
                    || !"RECEIVER_CONTEXT".equals(kind)
                    || selector.has("thread") && (thread.isEmpty()
                    || !thread.equals(thread.trim()))
                    || ordinal < 1) {
                throw new IllegalArgumentException(
                        "rootSelector requires GLOBAL_INVOCATION or an exact "
                                + "RECEIVER_CONTEXT");
            }
            return new RootContextSelector(true, receiverClass, thread,
                    ordinal);
        }

        private boolean matches(Object receiver, String actualThreadName) {
            if (!present || receiver == null
                    || !receiverRuntimeClass.equals(
                    receiver.getClass().getName())) {
                return false;
            }
            return threadName.isEmpty()
                    || threadName.equals(stableReplayThreadContext(
                    actualThreadName));
        }

        private static String stableReplayThreadContext(String value) {
            String thread = safe(value);
            Matcher executor = DEFAULT_EXECUTOR_THREAD_NAME.matcher(thread);
            if (executor.matches()) {
                return "pool-*-thread-" + executor.group(1);
            }
            Matcher objectIdentity =
                    DEFAULT_OBJECT_IDENTITY_THREAD_NAME.matcher(thread);
            return objectIdentity.matches()
                    ? objectIdentity.group(1) + "@*" : thread;
        }

        private String identity() {
            if (!present) return "GLOBAL_INVOCATION";
            return "RECEIVER_CONTEXT|"
                    + receiverRuntimeClass.length() + ':'
                    + receiverRuntimeClass + '|'
                    + threadName.length() + ':' + threadName;
        }

        private boolean selects(Integer occurrence) {
            return occurrence != null
                    && invocationOrdinalWithinContext == occurrence;
        }

    }

    private static final class RootArgumentSelector {
        private final boolean present;
        private final int receiverOrdinal;
        private final int matchOrdinalWithinReceiver;
        private final List<RootArgumentTypePredicate> predicates;

        private RootArgumentSelector(boolean present, int receiverOrdinal,
                                     int matchOrdinalWithinReceiver,
                                     List<RootArgumentTypePredicate> predicates) {
            this.present = present;
            this.receiverOrdinal = receiverOrdinal;
            this.matchOrdinalWithinReceiver = matchOrdinalWithinReceiver;
            this.predicates = predicates;
        }

        private static RootArgumentSelector from(JsonObject rootSelector) {
            if (!rootSelector.has("arguments")) {
                return new RootArgumentSelector(false, -1, -1,
                        Collections.emptyList());
            }
            JsonElement raw = rootSelector.get("arguments");
            if (raw == null || !raw.isJsonObject()) {
                return invalid("rootSelector.arguments must be an object");
            }
            JsonObject json = raw.getAsJsonObject();
            JsonElement rawPredicates = json.get("predicates");
            if (rawPredicates == null || !rawPredicates.isJsonArray()
                    || rawPredicates.getAsJsonArray().size() == 0) {
                return invalid("predicates must be a non-empty array");
            }
            List<RootArgumentTypePredicate> predicates = new ArrayList<>();
            Set<Integer> indices = new LinkedHashSet<>();
            for (JsonElement rawPredicate
                    : rawPredicates.getAsJsonArray()) {
                if (rawPredicate == null || !rawPredicate.isJsonObject()) {
                    return invalid("each predicate must be an object");
                }
                JsonObject predicate = rawPredicate.getAsJsonObject();
                if (!ROOT_ARGUMENT_PREDICATE_KIND.equals(
                        string(predicate, "kind"))) {
                    return invalid("predicate kind must be exact runtime type");
                }
                int index = integer(predicate, "argumentIndex", -1);
                String runtimeType = string(predicate, "runtimeType");
                if (index < 0 || runtimeType.isEmpty()
                        || !runtimeType.equals(runtimeType.trim())
                        || !indices.add(index)) {
                    return invalid("predicate index/type is malformed or duplicate");
                }
                predicates.add(new RootArgumentTypePredicate(index,
                        runtimeType));
            }
            predicates.sort((left, right) -> Integer.compare(
                    left.argumentIndex, right.argumentIndex));
            int receiverOrdinal = integer(json,
                    "receiverOrdinal", -1);
            int withinReceiver = integer(json,
                    "matchOrdinalWithinReceiver", -1);
            if (receiverOrdinal < 1 || withinReceiver < 1) {
                return invalid("argument selector requires receiverOrdinal "
                        + "and matchOrdinalWithinReceiver");
            }
            return new RootArgumentSelector(true, receiverOrdinal,
                    withinReceiver,
                    Collections.unmodifiableList(predicates));
        }

        private static RootArgumentSelector invalid(String error) {
            throw new IllegalArgumentException(error);
        }

        private boolean matches(Object[] rootArguments) {
            if (!present || rootArguments == null) return false;
            for (RootArgumentTypePredicate predicate : predicates) {
                if (predicate.argumentIndex >= rootArguments.length) {
                    return false;
                }
                Object value = rootArguments[predicate.argumentIndex];
                if (value == null || !predicate.runtimeType.equals(
                        value.getClass().getName())) {
                    return false;
                }
            }
            return true;
        }

        private String identity() {
            if (!present) return "NO_ARGUMENT_SELECTOR";
            StringBuilder result = new StringBuilder("ROOT_ARGUMENTS");
            for (RootArgumentTypePredicate predicate : predicates) {
                result.append('|').append(predicate.argumentIndex)
                        .append('=').append(predicate.runtimeType.length())
                        .append(':').append(predicate.runtimeType);
            }
            return result.toString();
        }

        private boolean selects(SelectorOccurrence occurrence) {
            if (occurrence == null) return false;
            return receiverOrdinal == occurrence.receiverOrdinal
                    && matchOrdinalWithinReceiver
                    == occurrence.matchOrdinalWithinReceiver;
        }

    }

    private static final class SelectorOccurrence {
        private final int receiverOrdinal;
        private final int matchOrdinalWithinReceiver;

        private SelectorOccurrence(int receiverOrdinal,
                                   int matchOrdinalWithinReceiver) {
            this.receiverOrdinal = receiverOrdinal;
            this.matchOrdinalWithinReceiver = matchOrdinalWithinReceiver;
        }

        private static SelectorOccurrence receiver(int receiverOrdinal,
                                                   int withinReceiver) {
            return new SelectorOccurrence(receiverOrdinal, withinReceiver);
        }
    }

    private static final class ReceiverSelectorState {
        private final IdentityHashMap<Object, ReceiverInvocationState>
                receivers = new IdentityHashMap<>();
        private int receiverCount;

        private SelectorOccurrence next(Object receiver) {
            ReceiverInvocationState state = receivers.get(receiver);
            if (state == null) {
                state = new ReceiverInvocationState(++receiverCount);
                receivers.put(receiver, state);
            }
            return SelectorOccurrence.receiver(state.receiverOrdinal,
                    ++state.matchCount);
        }
    }

    private static final class ReceiverInvocationState {
        private final int receiverOrdinal;
        private int matchCount;

        private ReceiverInvocationState(int receiverOrdinal) {
            this.receiverOrdinal = receiverOrdinal;
        }
    }

    private static final class RootArgumentTypePredicate {
        private final int argumentIndex;
        private final String runtimeType;

        private RootArgumentTypePredicate(int argumentIndex,
                                          String runtimeType) {
            this.argumentIndex = argumentIndex;
            this.runtimeType = runtimeType;
        }
    }

    private static final class RuntimeTask {
        private final String taskId;
        private final String regionId;
        private final String rootMethod;
        private final int invocationOrdinal;
        private final RootContextSelector rootContextSelector;
        private final RootArgumentSelector rootArgumentSelector;
        /** Complete planner-authored action catalog used by exact selector
         * declarations, including observation-only deferred leaf actions. */
        private final List<SymbolizeAction> declaredSymbolize;
        /** Actions that execute directly at ordinary instrumentation hooks. */
        private final List<SymbolizeAction> symbolize;
        private final Map<String, String> branchPolicies;
        private final List<ModelAssignment> modelAssignments;
        private final List<OutputCaptureSpec> outputCaptures;
        private RuntimeTask(ExecutionTask task) {
            if (!task.executable()) {
                throw new IllegalArgumentException(
                        "runtime task must be executable");
            }
            JsonObject rootSelector = task.rootSelector();
            this.taskId = task.taskId();
            this.regionId = task.regionId();
            this.rootMethod = task.rootMethod();
            this.invocationOrdinal = task.rootOrdinal();
            this.rootContextSelector = RootContextSelector.from(rootSelector);
            this.rootArgumentSelector = RootArgumentSelector.from(
                    rootSelector);
            this.declaredSymbolize = new ArrayList<>();
            this.symbolize = new ArrayList<>();
            this.branchPolicies = new LinkedHashMap<>();
            this.modelAssignments = new ArrayList<>();
            this.outputCaptures = new ArrayList<>();
            for (JsonElement element : task.inputActions().all()) {
                JsonObject encoded = element.getAsJsonObject();
                SymbolizeAction action = new SymbolizeAction(encoded);
                this.declaredSymbolize.add(action);
                if (InputActionCatalog.Mode.SYMBOLIC.name().equals(
                        string(encoded, "mode"))) {
                    this.symbolize.add(action);
                }
            }
            for (JsonElement element : task.branches()) {
                JsonObject branch = element.getAsJsonObject();
                branchPolicies.put(string(branch, "siteId"),
                        string(branch, "policy"));
            }
            for (JsonElement element : task.modelAssignments()) {
                modelAssignments.add(new ModelAssignment(
                        element.getAsJsonObject()));
            }
            Set<String> assignmentKeys = new LinkedHashSet<>();
            for (ModelAssignment assignment : modelAssignments) {
                if (assignment.key.isEmpty()
                        || !assignmentKeys.add(assignment.key)) {
                    throw new IllegalArgumentException(
                            "model assignment keys must be nonempty and "
                                    + "unique in " + taskId);
                }
            }
            for (OutputCaptureSpec request : task.outputCaptures()) {
                outputCaptures.add(request);
            }
        }

        private int actionCount(String symbol) {
            int count = 0;
            for (SymbolizeAction action : symbolize) {
                if (action.symbol.equals(symbol)) count++;
            }
            return count;
        }

        private SymbolizeAction uniqueAction(String symbol) {
            SymbolizeAction match = null;
            for (SymbolizeAction action : symbolize) {
                if (!action.symbol.equals(symbol)) continue;
                if (match != null) return null;
                match = action;
            }
            return match;
        }

        private int declaredActionCount(String symbol) {
            int count = 0;
            for (SymbolizeAction action : declaredSymbolize) {
                if (action.symbol.equals(symbol)) count++;
            }
            return count;
        }

        private SymbolizeAction uniqueDeclaredAction(String symbol) {
            SymbolizeAction match = null;
            for (SymbolizeAction action : declaredSymbolize) {
                if (!action.symbol.equals(symbol)) continue;
                if (match != null) return null;
                match = action;
            }
            return match;
        }

        private String policy(String siteId) {
            String policy = branchPolicies.get(siteId);
            return validBranchPolicy(policy) ? policy : "EXPLORE";
        }

        private static boolean validBranchPolicy(String policy) {
            return "EXPLORE".equals(policy)
                    || "PATH_ASSUMPTION".equals(policy);
        }

        private OutputCaptureSpec regionExitFieldCapture(
                String captureBindingId, String outputPort,
                String outputCell, String fieldSignature) {
            OutputCaptureSpec match = null;
            for (OutputCaptureSpec request : outputCaptures) {
                if (!request.matchesRegionExitField(captureBindingId,
                        outputPort, outputCell, fieldSignature)) {
                    continue;
                }
                if (match != null) return null;
                match = request;
            }
            return match;
        }

    }

    private static final class Configuration {
        private final Path resultFile;
        private final RuntimeTask task;

        private Configuration(Path resultFile, RuntimeTask task) {
            this.resultFile = resultFile;
            this.task = task;
        }

        private RuntimeTask select(String rootMethod, int ordinal,
                                     Object receiver,
                                     Object[] rootArguments) {
            if (!rootMethod.equals(task.rootMethod)) {
                return null;
            }
            String actualThreadName = Thread.currentThread().getName();
            RootContextSelector context = task.rootContextSelector;
            if (context.present
                    && (!context.matches(receiver, actualThreadName)
                    || !context.selects(nextRootContextOccurrence(
                    rootMethod, context)))) {
                return null;
            }
            RootArgumentSelector arguments = task.rootArgumentSelector;
            if (arguments.present
                    && (!arguments.matches(rootArguments)
                    || !arguments.selects(nextSelectorOccurrence(rootMethod,
                    arguments, context, receiver)))) {
                return null;
            }
            return arguments.present || context.present
                    || task.invocationOrdinal == ordinal ? task : null;
        }

        private static Configuration load() {
            String planValue = safe(System.getProperty(
                    "causynth.concolic.task.plan")).trim();
            String selectedTask = safe(System.getProperty(
                    "causynth.concolic.task.id")).trim();
            if (planValue.isEmpty()) {
                return new Configuration(null, null);
            }
            String resultValue = safe(System.getProperty(
                    "causynth.concolic.results")).trim();
            if (selectedTask.isEmpty() || resultValue.isEmpty()) {
                throw new IllegalStateException("Concolic runtime requires "
                        + "task id and result path with a task plan");
            }
            Path result = Paths.get(resultValue);
            Path plan = Paths.get(planValue);
            if (!Files.isRegularFile(plan)) {
                throw new IllegalStateException(
                        "Concolic task plan not found: " + plan);
            }
            RuntimeTask selected = null;
            try (BufferedReader reader = Files.newBufferedReader(plan,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.trim().isEmpty()) continue;
                    JsonElement parsed = new JsonParser().parse(line);
                    if (!parsed.isJsonObject() || selected != null) {
                        throw new IllegalStateException(
                                "task plan must contain exactly one object");
                    }
                    selected = new RuntimeTask(ExecutionTask.decode(
                            parsed.getAsJsonObject()));
                    if (!selected.taskId.equals(selectedTask)) {
                        throw new IllegalStateException(
                                "task plan contains non-selected task "
                                        + selected.taskId);
                    }
                }
            } catch (IOException | RuntimeException exception) {
                throw new IllegalStateException("Causynth rejected "
                        + "task plan " + plan + ": "
                        + exception.getMessage(), exception);
            }
            if (selected == null) {
                throw new IllegalStateException("Selected execution task "
                        + selectedTask + " is absent in " + plan);
            }
            return new Configuration(result, selected);
        }
    }

    private static final class EngineApi {
        private final Method startRegion;
        private final Method symbolizeWithPrefix;
        private final Method symbolizeField;
        private final Method getExpression;
        private final Method finishRegion;
        private final Method getPathCondition;
        private final Method pausePathCondition;
        private final Method resumePathCondition;
        private final Method markBranch;
        private final Method getBranchEvents;
        private final Method cleanupEnd;

        private EngineApi(Method startRegion,
                          Method symbolizeWithPrefix, Method symbolizeField,
                          Method getExpression,
                          Method finishRegion, Method getPathCondition,
                          Method pausePathCondition,
                          Method resumePathCondition,
                          Method markBranch, Method getBranchEvents,
                          Method cleanupEnd) {
            this.startRegion = startRegion;
            this.symbolizeWithPrefix = symbolizeWithPrefix;
            this.symbolizeField = symbolizeField;
            this.getExpression = getExpression;
            this.finishRegion = finishRegion;
            this.getPathCondition = getPathCondition;
            this.pausePathCondition = pausePathCondition;
            this.resumePathCondition = resumePathCondition;
            this.markBranch = markBranch;
            this.getBranchEvents = getBranchEvents;
            this.cleanupEnd = cleanupEnd;
        }

        private boolean available() {
            return startRegion != null
                    && symbolizeWithPrefix != null
                    && getExpression != null
                    && finishRegion != null
                    && getPathCondition != null
                    && pausePathCondition != null
                    && resumePathCondition != null
                    && cleanupEnd != null;
        }

        private void start(String regionId, String taskId) throws Exception {
            Object status = startRegion.invoke(null, regionId, taskId);
            if (status instanceof Number
                    && ((Number) status).longValue() != 0L) {
                throw new IllegalStateException(
                        "custom concolic engine rejected region start: "
                                + ((Number) status).longValue());
            }
        }

        private void symbolize(Object value, String prefix) throws Exception {
            symbolizeWithPrefix.invoke(null, value, prefix);
        }

        private void symbolizeField(Object owner, String field, String prefix)
                throws Exception {
            if (symbolizeField == null) {
                throw new UnsupportedOperationException(
                        "custom concolic System.symbolizeField API is unavailable");
            }
            symbolizeField.invoke(null, owner, field, prefix);
        }

        private String expression(Object value) throws Exception {
            return String.valueOf(getExpression.invoke(null, value));
        }

        private String finish() throws Exception {
            return String.valueOf(finishRegion.invoke(null));
        }

        private String pathCondition() throws Exception {
            return String.valueOf(getPathCondition.invoke(null));
        }

        private void pausePathCondition() throws Exception {
            pausePathCondition.invoke(null);
        }

        private void resumePathCondition() throws Exception {
            resumePathCondition.invoke(null);
        }

        private boolean exactBranchEventsAvailable() {
            return markBranch != null && getBranchEvents != null;
        }

        private String branchEvents() throws Exception {
            return String.valueOf(getBranchEvents.invoke(null));
        }

        private void cleanupAfterFailure() {
            if (cleanupEnd != null) {
                try {
                    cleanupEnd.invoke(null);
                } catch (Throwable ignored) {
                }
            }
        }

        private static EngineApi load() {
            Class<System> system = System.class;
            return new EngineApi(
                    method(system, "startConcolicRegion", String.class, String.class),
                    method(system, "symbolize", Object.class, String.class),
                    method(system, "symbolizeField", Object.class,
                            String.class, String.class),
                    method(system, "getSymbolicExpression", Object.class),
                    method(system, "finishConcolicRegion"),
                    method(system, "getPathCondition"),
                    method(system, "pauseConcolicPathCondition"),
                    method(system, "resumeConcolicPathCondition"),
                    method(system, "markConcolicBranch",
                            String.class, int.class),
                    method(system, "getConcolicBranchEvents"),
                    method(system, "endConcolic"));
        }

        private static Method method(Class<?> owner, String name,
                                     Class<?>... parameters) {
            try {
                return owner.getMethod(name, parameters);
            } catch (NoSuchMethodException ignored) {
                return null;
            }
        }
    }

}
