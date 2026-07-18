package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import edu.uva.liftlab.graphchecker.concolic.ConcolicCodePosition;

import java.io.BufferedReader;
import java.io.IOException;
import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
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
    private static final int MAX_MAP_PROJECTION_ELEMENTS = 4096;
    private static final String FRESH_MAP_ENTRY_REBINDING_AUTHORITY =
            "EXACT_BASE_PORT_GETTER_SITE_OCCURRENCE_THEN_"
                    + "FRESH_ENTRY_REBIND_V1";
    private static final String MAP_PROJECTION_IMPLEMENTATION_AUTHORITY =
            "EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_LINKEDHASHMAP_"
                    + "JAVA_EQUALS_HASHCODE_EXTENSIONAL_V1";
    private static final String MAP_PROJECTION_FIELD_VALUE_AUTHORITY =
            "SAME_EXECUTION_BOUNDED_OBSERVED_SCHEDULE_EXACT_DECLARED_FIELD_"
                    + "ENTRY_VALUE_PLUS_NO_INTERVENING_RUNTIME_FIELD_WRITE_"
                    + "AND_EXACT_OUTPUT_RECHECK";
    private static final String FINITE_MAP_SNAPSHOT_AUTHORITY =
            "FIRST_BOUND_ENTRY_SET_ITERATOR_NEXT_EXACT_HASHMAP_OR_"
                    + "LINKEDHASHMAP_SAME_EXECUTION_PRE_REMOVE_STABLE_SIZE_"
                    + "AND_ENTRY_SET_DISTINCT_IMMUTABLE_KEYS_V1";
    private static final String FINITE_MAP_VALUE_EXPRESSION_AUTHORITY =
            "PER_ENTRY_EXACT_RUNTIME_NULL_OR_ACTIVATION_LOCAL_OBJECT_TOKEN_"
                    + "REF_WITNESS_V1";
    private static final String EXACT_RUNTIME_NULL_AUTHORITY =
            "EXACT_RUNTIME_NULL_AT_SAME_EXECUTION_ENTRY_SET_SNAPSHOT";
    private static final String ROOT_ARGUMENT_SELECTOR_SCHEMA_V1 =
            "EXACT_RUNTIME_ROOT_ARGUMENT_TYPES_V1";
    private static final String ROOT_ARGUMENT_SELECTOR_AUTHORITY_V1 =
            "RUNTIME_METHOD_ARGUMENT_EXACT_TYPES_"
                    + "PREDICATE_RELATIVE_ORDINAL_V1";
    private static final String ROOT_ARGUMENT_SELECTOR_SCHEMA_V2 =
            "EXACT_RUNTIME_ROOT_ARGUMENT_TYPES_AND_RECEIVER_V2";
    private static final String ROOT_ARGUMENT_SELECTOR_AUTHORITY_V2 =
            "RUNTIME_METHOD_ARGUMENT_EXACT_TYPES_DISTINCT_RECEIVER_"
                    + "AND_WITHIN_RECEIVER_ORDINAL_V2";
    private static final String ROOT_ARGUMENT_PREDICATE_KIND =
            "EXACT_RUNTIME_TYPE";
    private static final String ROOT_CONTEXT_SELECTION_AUTHORITY =
            "TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_THREAD_NAME_"
                    + "CONTEXT_ORDINAL_V1";
    private static final String VALUE_REF_WITNESS_AUTHORITY =
            "ACTIVATION_LOCAL_OBJECT_TOKEN_REF_WITNESS_V1";
    private static final String VALUE_REF_WITNESS_KIND =
            "ACTIVATION_LOCAL_REF_SYMBOL_WITNESS";
    private static final String VALUE_REF_WITNESS_TOKEN_AUTHORITY =
            "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN_TO_"
                    + "SCOPED_REF_SYMBOL_V1";
    private static final String VALUE_REF_WITNESS_SYMBOL_PREFIX =
            "CAUSYNTH_REF_WITNESS_V1_A";
    private static final Gson GSON = new GsonBuilder().disableHtmlEscaping().create();
    private static final Object CONFIG_LOCK = new Object();
    private static final Object WRITE_LOCK = new Object();
    private static final Object EXECUTION_MODE_LOCK = new Object();
    private static final AtomicLong TOKEN_COUNTER = new AtomicLong();
    private static final AtomicLong ACCESSOR_CONTEXT_TOKEN_COUNTER =
            new AtomicLong();
    private static final AtomicBoolean ENGINE_BUSY = new AtomicBoolean();
    private static int concreteReplayActiveCount;
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
    private static final Pattern FIELD_DETAIL = Pattern.compile(
            "<([^:]+):\\s+([^()<>]+)\\s+([^\\s()>]+)>");
    private static final Pattern FIELD_PROJECTION = Pattern.compile(
            "#field:([^#]+)");
    private static final Pattern LOCAL_CELL = Pattern.compile(
            "^(<.+>)::([^#]+)(?:#.*)?$");
    private static final Pattern BRANCH_OPERATOR = Pattern.compile(
            "(?:^|\\s)(==|!=|<=|>=|<|>)(?:\\s|$)");
    private static volatile Configuration configuration;
    private static volatile EngineApi engineApi;

    private ConcolicRegionRuntime() {
    }

    /**
     * Copies a Gson tree without linking against Gson's tree-copy methods.
     * Hadoop workloads can provide Gson 2.2.x at runtime, where those methods
     * are not public even though the newer Gson used to compile GraphChecker
     * exposes them publicly.  A JSON round trip both preserves the tree value
     * and gives callers an independently mutable result on every supported
     * Gson version.
     */
    @SuppressWarnings("unchecked")
    static <T extends JsonElement> T copyJsonTree(T source) {
        if (source == null) return null;
        return (T) new JsonParser().parse(GSON.toJson(source));
    }

    static JsonObject valueRefWitnessExpressionForTests(
            String activationId, long objectToken) {
        return activationLocalValueRefWitnessExpression(activationId,
                objectToken);
    }

    /**
     * Process-wide companion to the ordinary field trace hook.  A schema-v3
     * Map projection uses it as execution-local evidence that the exact
     * projected field was not assigned between its entry snapshot and the
     * producer output.  MiniDFS workers may perform that assignment on a
     * thread other than the region root, so every active region is notified.
     * Calls outside an active region are intentional no-ops.
     */
    static void observeRuntimeFieldEvent(String kind, Object fieldOwner,
                                         String fieldSignature) {
        if (!"FIELD_WRITE".equals(safe(kind)) || fieldOwner == null) return;
        for (ActiveRegion active : ACTIVE.values()) {
            active.observeFieldWrite(fieldOwner, fieldSignature);
        }
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
        synchronized (EXECUTION_MODE_LOCK) {
            ENGINE_BUSY.set(false);
            concreteReplayActiveCount = 0;
        }
    }

    static void installEngineApiForTests(Class<?> owner) throws Exception {
        engineApi = new EngineApi(
                testEngineMethod(owner, "startRegion",
                        String.class, String.class),
                null,
                testEngineMethod(owner, "symbolize",
                        Object.class, String.class),
                null,
                testEngineMethod(owner, "symbolizeField",
                        Object.class, String.class, String.class),
                testEngineMethod(owner, "expression", Object.class),
                null,
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

    /** Called at a statically selected same-thread region root. */
    public static long enterRegion(String rootMethod, Object receiver) {
        return enterRegion(rootMethod, receiver, null);
    }

    /**
     * Called at a statically selected same-thread region root with its actual
     * reference arguments.  Primitive parameter slots are null.  The
     * compatibility overload above preserves legacy instrumented classes and
     * legacy plans that select by the global invocation ordinal.
     */
    public static long enterRegion(String rootMethod, Object receiver,
                                   Object[] rootArguments) {
        Configuration config = configuration();
        if (!config.enabled || rootMethod == null) {
            return 0L;
        }
        String test = firstNonBlank(System.getProperty("causynth.trace.test"),
                System.getenv("CAUSYNTH_TRACE_TEST"), "unknown-test");
        int ordinal = nextOrdinal(test + "\n" + rootMethod);
        Activation activation = config.select(rootMethod, test, ordinal,
                receiver, rootArguments);
        if (activation == null) {
            return 0L;
        }
        if (activation.concreteReplayOnly) {
            return enterConcreteReplay(activation, receiver);
        }
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
            api.start(activation.regionId, activation.activationId);
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
                    Thread.currentThread(), System.nanoTime());
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
                    // Best effort only: forceEnd is also valid while recording
                    // is paused, but balancing the API keeps diagnostics clear.
                    try {
                        api.resumePathCondition();
                    } catch (Throwable ignored) {
                        // forceEnd below owns the definitive cleanup.
                    }
                }
                api.forceEnd();
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

    private static long enterConcreteReplay(Activation activation,
                                            Object receiver) {
        String invalid = activation.concreteReplayError();
        if (!invalid.isEmpty()) {
            writeSkipped(activation, invalid);
            return 0L;
        }
        if (CURRENT_TOKEN.get() != null) {
            writeSkipped(activation,
                    "nested concrete replay on the same thread is unsupported");
            return 0L;
        }
        if (!reserveConcreteReplay()) {
            writeSkipped(activation,
                    "a symbolic concolic region is active");
            return 0L;
        }
        long token = 0L;
        try {
            token = TOKEN_COUNTER.incrementAndGet();
            ActiveRegion active = new ActiveRegion(token, activation,
                    receiver, Thread.currentThread(), System.nanoTime());
            ACTIVE.put(token, active);
            CURRENT_TOKEN.set(token);
            return token;
        } catch (Throwable throwable) {
            if (token != 0L) ACTIVE.remove(token);
            CURRENT_TOKEN.remove();
            releaseConcreteReplay();
            writeSkipped(activation, "concrete replay start failed: "
                    + rootCause(throwable));
            return 0L;
        }
    }

    private static boolean reserveSymbolicEngine() {
        synchronized (EXECUTION_MODE_LOCK) {
            if (ENGINE_BUSY.get() || concreteReplayActiveCount != 0) {
                return false;
            }
            ENGINE_BUSY.set(true);
            return true;
        }
    }

    private static void releaseSymbolicEngine() {
        synchronized (EXECUTION_MODE_LOCK) {
            ENGINE_BUSY.set(false);
        }
    }

    private static boolean reserveConcreteReplay() {
        synchronized (EXECUTION_MODE_LOCK) {
            if (ENGINE_BUSY.get()) return false;
            concreteReplayActiveCount++;
            return true;
        }
    }

    private static void releaseConcreteReplay() {
        synchronized (EXECUTION_MODE_LOCK) {
            if (concreteReplayActiveCount > 0) concreteReplayActiveCount--;
        }
    }

    /** Called once per Java argument immediately after {@link #enterRegion}. */
    public static void symbolizeArgument(long token, int argumentIndex,
                                         Object value, String primitiveValue) {
        ActiveRegion active = ownerRegion(token);
        if (active == null || !active.engineBacked) {
            return;
        }
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!("ARGUMENT".equals(action.location)
                    || "ARGUMENT_FIELD".equals(action.location)
                    || "ARGUMENT_FIELD_PATH".equals(action.location))
                    || action.index != argumentIndex) {
                continue;
            }
            if (value == null) {
                if ("ARGUMENT".equals(action.location)
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
            if (("ARGUMENT_FIELD".equals(action.location)
                    || "ARGUMENT_FIELD_PATH".equals(action.location))
                    && action.declaresArrayInput(action.fieldPath)) {
                active.registerLogicalArrayRoot(action, value,
                        "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_"
                                + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY");
                continue;
            }
            if ("ARGUMENT_FIELD".equals(action.location)) {
                if (action.fields.isEmpty()) {
                    active.unresolved.add(action.symbol
                            + ": selective argument has no fields");
                    continue;
                }
                for (String field : action.fields) {
                    symbolizeField(active, action, value, field, engine());
                }
            } else if ("ARGUMENT_FIELD_PATH".equals(action.location)) {
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
            active.observeContainerActionValue(action, value,
                    "ROOT_ARGUMENT_SYMBOLIZATION");
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
                    || "ARGUMENT_FIELD".equals(action.location)
                    || "ARGUMENT_FIELD_PATH".equals(action.location))) {
                continue;
            }
            if (boxedOrReference != null
                    && ("ARGUMENT_FIELD".equals(action.location)
                    || "ARGUMENT_FIELD_PATH".equals(action.location))
                    && action.declaresArrayInput(action.fieldPath)) {
                active.registerLogicalArrayRoot(action, boxedOrReference,
                        "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_"
                                + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY");
                return boxedOrReference;
            }
            if (boxedOrReference != null
                    && isPrimitiveBox(boxedOrReference)) {
                return materializePrimitiveValue(active, action,
                        boxedOrReference, "ROOT_ARGUMENT", null);
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
                active.recordModelAssignment(assignment, "ROOT_ARGUMENT",
                        null, modeled);
                return modeled;
            }
            if ("ARGUMENT_FIELD_PATH".equals(action.location)) {
                for (List<String> path : action.fieldPaths) {
                    applyFieldPathModel(active, action, boxedOrReference,
                            path, "ROOT_ARGUMENT_FIELD_PATH");
                }
            } else if ("ARGUMENT_FIELD".equals(action.location)) {
                for (String field : action.fields) {
                    applyFieldModel(active, action, boxedOrReference, field,
                            Collections.singletonList(field),
                            "ROOT_ARGUMENT_FIELD");
                }
            } else {
                ModelAssignment assignment = active.assignment(action, null);
                if (assignment != null) {
                    Object modeled = assignment.referenceValue(
                            boxedOrReference);
                    if (modeled != UnsupportedReplayValue.INSTANCE) {
                        active.recordModelAssignment(assignment,
                                "ROOT_ARGUMENT", null, modeled);
                        active.observeContainerActionValue(action, modeled,
                                "ROOT_ARGUMENT");
                        return modeled;
                    }
                    active.unresolved.add(action.symbol
                            + ": unsupported root reference model "
                            + assignment.valueType + "=" + assignment.value);
                }
            }
            active.observeContainerActionValue(action, boxedOrReference,
                    "ROOT_ARGUMENT");
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
                active.observeContainerActionValue(action, value,
                        "LOCAL_DEFINITION_REPEAT");
                continue;
            }
            if (value != null
                    && "LOCAL_DEFINITION_IDENTITY_AT_EXACT_DEFINITION_"
                    .concat("SITE_AND_LOGICAL_PATH_PREFIX_REFERENCE_"
                            + "EQUALITY").equals(
                            action.consumedFieldRootAuthority)
                    && action.declaresArrayInput(action.fieldPath)) {
                // A nested array-valued local action is rooted at the exact
                // definition value.  The leaf itself is prepared and joined
                // at its real getfield; symbolizing this carrier object here
                // would broaden the input and would miss that consumed-value
                // join.
                active.registerLogicalArrayRoot(action, value,
                        action.consumedFieldRootAuthority);
                active.observeContainerActionValue(action, value,
                        "LOCAL_DEFINITION_LOGICAL_ARRAY_ROOT");
                return value;
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
                    active.recordModelAssignment(assignment,
                            "LOCAL_DEFINITION", null, modeled);
                }
            }
            if (active.engineBacked && (materialized != null
                    || action.declaresArrayInput(
                    Collections.<String>emptyList()))) {
                symbolize(active, action, materialized, engine());
            }
            active.observeContainerActionValue(action, materialized,
                    "LOCAL_DEFINITION");
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
                    || !active.materialized.add(action.symbol)) {
                continue;
            }
            return materializePrimitiveValue(active, action, boxedValue,
                    "LOCAL_DEFINITION", null);
        }
        return boxedValue;
    }

    /**
     * Prepares one array-valued leaf field before the instrumented program
     * executes its single real getfield.  This method never symbolizes or
     * captures the array.  It writes any selected model first, reads the leaf
     * exactly once, and retains that reference for the post-getfield join.
     */
    public static void prepareFieldMaterialization(
            String method, int unitIndex, Object leafOwner,
            String leafFieldSignature, String leafFieldName) {
        ActiveRegion active = activeRegion();
        if (active == null || leafOwner == null) {
            return;
        }
        String site = siteId(method, unitIndex);
        if (active.pendingArrayFieldMaterialization != null) {
            active.addUnresolvedOnce(site
                    + ": ARRAY_VALUE_PENDING_PREPARE_CONFLICT");
            return;
        }
        List<SymbolizeAction> matches = new ArrayList<>();
        for (SymbolizeAction action : active.activation.symbolize) {
            if (action.identifiesConsumedLeaf(leafOwner,
                    leafFieldSignature, leafFieldName)) {
                matches.add(action);
            }
        }
        if (matches.isEmpty()) {
            return;
        }
        if (matches.size() != 1) {
            active.addUnresolvedOnce(site
                    + ": ARRAY_VALUE_EXACT_LEAF_ACTION_AMBIGUOUS:"
                    + matches.size());
            return;
        }
        SymbolizeAction action = matches.get(0);
        if (!action.matchesConsumedFieldSite(method, unitIndex)) {
            active.addUnresolvedOnce(action.symbol
                    + ": ARRAY_VALUE_CONSUMED_FIELD_SITE_AUTHORITY_MISSING");
            return;
        }
        List<String> logicalPath = action.logicalPathForConsumedLeaf(
                leafFieldSignature, leafFieldName);
        if (logicalPath.isEmpty()
                || !active.logicalLeafOwnerVerified(action, leafOwner,
                logicalPath)) {
            active.addUnresolvedOnce(action.symbol
                    + ": ARRAY_VALUE_CONSUMED_OWNER_AUTHORITY_MISSING");
            return;
        }
        DeclaredArrayInputType declaredType = action
                .exactConsumedLeafArrayType(leafOwner,
                        leafFieldSignature, leafFieldName);
        if (!declaredType.complete()) {
            active.addUnresolvedOnce(action.symbol
                    + ": ARRAY_VALUE_EXACT_LEAF_TYPE_INCOMPLETE: "
                    + declaredType.problem);
            return;
        }
        if (active.preparedArrayInputPorts.contains(action.symbol)) {
            active.addUnresolvedOnce(action.symbol
                    + ": ARRAY_VALUE_PREPARE_REPEATED");
            return;
        }

        List<ModelAssignment> selectedAssignments =
                active.fieldAssignments(action);
        if (selectedAssignments.size() > 1) {
            active.addUnresolvedOnce(action.symbol
                    + ": ARRAY_VALUE_MODEL_ASSIGNMENT_AMBIGUOUS:"
                    + selectedAssignments.size());
            return;
        }
        List<ModelAssignment> applied = new ArrayList<>();
        for (ModelAssignment assignment : selectedAssignments) {
            List<String> path = assignment.path.isEmpty()
                    ? logicalPath : assignment.path;
            boolean exactLogicalPath = path.isEmpty()
                    || path.equals(logicalPath)
                    || action.fieldPaths.contains(path);
            if (!exactLogicalPath || !path.isEmpty()
                    && !leafFieldName.equals(path.get(path.size() - 1))) {
                active.addUnresolvedOnce(action.symbol
                        + ": ARRAY_VALUE_MODEL_TARGET_IS_NOT_EXACT_LEAF");
                return;
            }
            if (!writeModeledExactField(leafOwner, leafFieldSignature,
                    assignment)) {
                active.addUnresolvedOnce(action.symbol
                        + ": ARRAY_VALUE_MODEL_WRITE_FAILED_AT_EXACT_LEAF");
                return;
            }
            applied.add(assignment);
        }

        ExactFieldObservation prepared = observeExactField(leafOwner,
                leafFieldSignature);
        if (!prepared.ownerVerified || !prepared.typeVerified
                || !prepared.available) {
            active.addUnresolvedOnce(action.symbol
                    + ": ARRAY_VALUE_PREPARED_EXACT_LEAF_READ_UNAVAILABLE: "
                    + prepared.error);
            return;
        }
        Object expected = prepared.value;
        long expectedToken = active.objectToken(expected);
        for (ModelAssignment assignment : applied) {
            active.recordModelAssignment(assignment,
                    "ARRAY_VALUE_EXACT_LEAF_PREPARE",
                    logicalPath, expected);
        }
        active.pendingArrayFieldMaterialization =
                new PendingArrayFieldMaterialization(method, unitIndex,
                        action, leafOwner, leafFieldSignature,
                        leafFieldName, logicalPath, expected, expectedToken,
                        declaredType);
        active.preparedArrayInputPorts.add(action.symbol);
    }

    /**
     * Joins the exact value consumed by the program's real getfield to the
     * prepared leaf reference.  No reflective field read occurs here: a
     * concurrent replacement after getfield cannot redirect the binding.
     */
    public static void materializeConsumedField(
            String method, int unitIndex, Object leafOwner,
            String leafFieldSignature, String leafFieldName,
            Object consumedValue) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        String site = siteId(method, unitIndex);
        PendingArrayFieldMaterialization pending =
                active.pendingArrayFieldMaterialization;
        active.pendingArrayFieldMaterialization = null;
        if (pending == null) {
            active.addUnresolvedOnce(site
                    + ": ARRAY_VALUE_CONSUMED_WITHOUT_PREPARE");
            return;
        }
        if (!pending.matches(method, unitIndex, leafOwner,
                leafFieldSignature, leafFieldName)) {
            active.addUnresolvedOnce(site
                    + ": ARRAY_VALUE_PREPARED_CONSUMED_SITE_OWNER_MISMATCH");
            return;
        }
        if (pending.expectedReference != consumedValue) {
            active.addUnresolvedOnce(pending.action.symbol
                    + ": ARRAY_VALUE_PREPARED_CONSUMED_REFERENCE_MISMATCH");
            return;
        }
        long consumedToken = active.objectToken(consumedValue);
        if (consumedToken != pending.expectedObjectToken) {
            active.addUnresolvedOnce(pending.action.symbol
                    + ": ARRAY_VALUE_PREPARED_CONSUMED_TOKEN_MISMATCH");
            return;
        }

        SymbolizeAction action = pending.action;
        active.observeMapProjectionInput(action, consumedValue,
                "EXACT_CONSUMED_LEAF_GETFIELD");
        active.observeContainerInput(action, consumedValue,
                "EXACT_CONSUMED_LEAF_GETFIELD");
        active.observeContainerActionValue(action, consumedValue,
                "EXACT_CONSUMED_LEAF_GETFIELD");
        if (!active.engineBacked) {
            // Concrete replay still needs one exact observation for the
            // container leaf that was joined to the program's real getfield.
            // Use the already-verified leaf owner directly: the logical path
            // may start at an argument/receiver/local root and is therefore
            // not traversable from this object.  A later rejected dynamic
            // element selection must not manufacture a second legacy/base
            // observation for the element field.
            active.fieldObservations.add(exactLeafFieldObservation(active,
                    action.symbol, pending.leafOwner,
                    pending.leafFieldSignature, pending.leafFieldName,
                    "AT_EXACT_CONSUMED_LEAF_GETFIELD"));
            return;
        }
        EngineApi api = engine();
        boolean liveArray = consumedValue != null
                && consumedValue.getClass().isArray();
        if (liveArray) {
            try {
                api.symbolize(consumedValue, action.symbol);
                active.symbolized.add(action.symbol);
            } catch (Throwable throwable) {
                active.addUnresolvedOnce(action.symbol
                        + ": ARRAY_VALUE_CONSUMED_SYMBOLIZATION_FAILED: "
                        + rootCause(throwable));
                return;
            }
        }
        active.captureEngineArrayInputBinding(action, consumedValue,
                consumedValue, consumedToken, pending.declaredType,
                "EXACT_CONSUMED_LEAF_GETFIELD", api);
        EngineArrayInputBinding captured = active.engineArrayInputByPort.get(
                action.symbol);
        if (captured != null) {
            captured.markConsumedLeaf(active, leafOwner,
                    leafFieldSignature, pending.logicalFieldPath);
        }
        if (liveArray) {
            refreshEntryReadsForFieldOwner(active, leafOwner,
                    action.symbol, null);
        }
    }

    /** Materializes a heap field on the concrete owner seen at its read site. */
    public static void materializeField(String method, int unitIndex,
                                        Object owner, String fieldSignature,
                                        String fieldName) {
        ActiveRegion active = activeRegion();
        if (active == null || owner == null) {
            return;
        }
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesField(method, unitIndex, owner, fieldSignature,
                    fieldName)) {
                continue;
            }
            if (action.declaresArrayInput(action.fieldPath)) {
                active.addUnresolvedOnce(action.symbol
                        + ": ARRAY_VALUE_LEGACY_PRE_READ_"
                        + "MATERIALIZATION_UNSAFE");
                continue;
            }
            Object leafOwner = action.leafOwner(owner);
            if (leafOwner == MissingValue.INSTANCE) {
                active.unresolved.add(action.symbol
                        + ": projected field owner is missing for "
                        + action.fieldPath);
                continue;
            }
            if (leafOwner == null) {
                active.unresolved.add(action.symbol
                        + ": projected field owner is null for "
                        + action.fieldPath);
                continue;
            }
            // Container identity is an input binding, so observe it before
            // either dynamic dispatch or the legacy one-static-symbol gate.
            // A second concrete container for the same port must be detected
            // as ambiguity rather than hidden by materialized.add(symbol).
            Object exactFieldValue = readField(leafOwner,
                    action.leafField);
            active.observeMapProjectionInput(action, exactFieldValue,
                    "FIELD_ACCESS");
            active.observeContainerInput(action, exactFieldValue,
                    "FIELD_ACCESS");
            ContainerFieldResolution containerResolution =
                    active.dynamicContainerFieldBinding(action, owner,
                            leafOwner, firstNonBlank(fieldSignature,
                                    action.field, action.cell),
                            siteId(method, unitIndex));
            if (containerResolution.declared) {
                if (containerResolution.ignored) {
                    // FIELD_ACCESS hooks are owner-wide.  A read of the same
                    // declared field on an object outside the activation's
                    // exact container is not this input family.  Required
                    // exact selectors are checked once more at region exit,
                    // so ignoring the unrelated owner cannot hide a missing
                    // selected element.
                    continue;
                } else if (!containerResolution.resolved()) {
                    active.addUnresolvedOnce(action.symbol
                            + ": generic container-element field binding "
                            + "failed closed at " + siteId(method, unitIndex)
                            + ": " + containerResolution.problem);
                } else {
                    materializeDynamicContainerElementField(active, action,
                            owner, leafOwner, containerResolution.selection);
                }
                continue;
            }
            MapIteratorCursor entryCursor = currentMapEntryCursor(active,
                    leafOwner);
            if (entryCursor != null) {
                materializeDynamicMapEntryField(active, action, method,
                        unitIndex, owner, leafOwner, fieldSignature,
                        entryCursor);
                continue;
            }
            // Non-entry fields retain the legacy one-static-port behavior.
            // Dynamic instance materialization is deliberately opt-in so a
            // manager map field or an ordinary receiver field is never
            // reclassified merely because an unrelated iterator is active.
            if (!active.materialized.add(action.symbol)) {
                continue;
            }
            try {
                boolean assignmentFailed = false;
                for (ModelAssignment assignment
                        : active.fieldAssignments(action)) {
                    List<String> path = assignment.path.isEmpty()
                            ? action.fieldPath : assignment.path;
                    Object modeledOwner;
                    String modeledField;
                    if (path.equals(action.fieldPath)) {
                        modeledOwner = leafOwner;
                        modeledField = action.leafField;
                    } else {
                        modeledOwner = resolveFieldPathLeafOwner(owner, path);
                        modeledField = path.isEmpty() ? ""
                                : path.get(path.size() - 1);
                    }
                    if (modeledOwner == null
                            || modeledOwner == MissingValue.INSTANCE) {
                        active.unresolved.add(action.symbol + "."
                                + joinFieldPath(path)
                                + ": solver-model field owner is unavailable");
                        assignmentFailed = true;
                        continue;
                    }
                    if (!writeModeledField(modeledOwner, modeledField,
                            assignment)) {
                        active.unresolved.add(action.symbol + "."
                                + joinFieldPath(path)
                                + ": solver model could not be written to real field");
                        assignmentFailed = true;
                        continue;
                    }
                    active.recordModelAssignment(assignment,
                            "FIELD_ACCESS", path,
                            readField(modeledOwner, modeledField));
                }
                if (assignmentFailed) {
                    continue;
                }
                active.fieldTargets.put(action.symbol,
                        new FieldObservationTarget(action.symbol, owner,
                                action.fieldPath));
                if (active.engineBacked) {
                    EngineApi observationApi = engine();
                    observationApi.pausePathCondition();
                    try {
                        active.fieldObservations.add(fieldObservation(
                                active, action.symbol, owner, action.fieldPath,
                                "AT_MATERIALIZATION"));
                    } finally {
                        observationApi.resumePathCondition();
                    }
                    Object liveFieldValue = readField(leafOwner,
                            action.leafField);
                    DeclaredArrayInputType declaredType = action
                            .exactLeafArrayType(leafOwner,
                                    action.leafField,
                                    action.fieldPath);
                    boolean liveArray = liveFieldValue != null
                            && liveFieldValue != MissingValue.INSTANCE
                            && liveFieldValue.getClass().isArray();
                    boolean declaredArray = declaredType.complete()
                            || action.declaresArrayInput(action.fieldPath);
                    if (liveArray || declaredArray) {
                        long symbolizationToken = liveArray
                                ? active.objectToken(liveFieldValue) : 0L;
                        if (liveArray) {
                        engine().symbolize(liveFieldValue, action.symbol);
                            active.symbolized.add(action.symbol);
                        }
                        Object postSymbolizationValue = readField(leafOwner,
                                action.leafField);
                        active.captureEngineArrayInputBinding(action,
                                liveFieldValue, postSymbolizationValue,
                                symbolizationToken, declaredType,
                                "FIELD_ACCESS", engine());
                    } else {
                        engine().symbolizeField(leafOwner, action.leafField,
                                action.symbol);
                        active.symbolized.add(action.symbol);
                    }
                    // Iterator.next precedes the guarded field read.  Some
                    // custom-JDK object expressions become available only
                    // after that concrete entry value owns a symbolic field.
                    refreshEntryReadsForFieldOwner(active, leafOwner,
                            action.symbol, null);
                } else {
                    active.fieldObservations.add(fieldObservation(
                            active, action.symbol, owner, action.fieldPath,
                            "AT_MATERIALIZATION"));
                }
            } catch (Throwable throwable) {
                active.unresolved.add(action.symbol + ": field-site materialization "
                        + safe(method) + "#u" + unitIndex + " failed: "
                        + rootCause(throwable));
            }
        }
    }

    private static void materializeDynamicContainerElementField(
            ActiveRegion active, SymbolizeAction action, Object accessOwner,
            Object leafOwner, DynamicFieldSelection selection) {
        DynamicFieldBinding binding = selection.binding;
        if (!selection.created) {
            // A repeated read of the exact same heap cell is an alias, not a
            // new element occurrence.  Keep the first VM symbol and replay
            // target so later reads cannot fork the same field state.
            return;
        }
        try {
            List<ModelAssignment> assignments =
                    active.dynamicFieldAssignments(action, binding);
            if (assignments.size() > 1) {
                active.addUnresolvedOnce(binding.dynamicBindingId
                        + ": multiple exact model assignments target one "
                        + "container-element field binding");
                return;
            }
            if (!assignments.isEmpty()) {
                ModelAssignment assignment = assignments.get(0);
                if (!writeModeledField(leafOwner, action.leafField,
                        assignment)) {
                    active.addUnresolvedOnce(binding.dynamicBindingId
                            + ": solver model could not be written to exact "
                            + "container element field owner");
                    return;
                }
                active.recordModelAssignment(assignment,
                        "DYNAMIC_CONTAINER_ELEMENT_FIELD_ACCESS",
                        action.fieldPath,
                        readField(leafOwner, action.leafField));
            }

            active.fieldTargets.put(binding.dynamicBindingId,
                    new FieldObservationTarget(binding.dynamicFieldSymbol,
                            accessOwner, action.fieldPath, binding));
            JsonObject observation = fieldObservation(active,
                    binding.dynamicFieldSymbol, accessOwner,
                    action.fieldPath, "AT_MATERIALIZATION", binding);
            active.fieldObservations.add(observation);
            if (active.engineBacked) {
                symbolizeDynamicField(active, action, binding, leafOwner,
                        "DYNAMIC_CONTAINER_ELEMENT_FIELD_ACCESS", engine());
            }
        } catch (Throwable throwable) {
            active.addUnresolvedOnce(binding.dynamicBindingId
                    + ": dynamic container field materialization failed: "
                    + rootCause(throwable));
        }
    }

    private static MapIteratorCursor currentMapEntryCursor(
            ActiveRegion active, Object leafOwner) {
        MapIteratorCursor selected = null;
        for (MapIteratorCursor cursor : active.mapIterators.values()) {
            if (!cursor.hasCurrent || !cursor.valueKnown
                    || cursor.value != leafOwner
                    || cursor.entryObservation == null
                    || !"ENTRY_SET".equals(cursor.binding.viewKind)) {
                continue;
            }
            if (selected != null && selected != cursor) {
                // Two live iterators claim the same value.  There is no
                // unique entry/key selector, so leave this on the fail-closed
                // legacy path instead of inventing a dynamic association.
                return null;
            }
            selected = cursor;
        }
        return selected;
    }

    private static void materializeDynamicMapEntryField(
            ActiveRegion active, SymbolizeAction action, String method,
            int unitIndex, Object accessOwner, Object leafOwner,
            String fieldSignature, MapIteratorCursor cursor) {
        String materializationSite = siteId(method, unitIndex);
        int occurrence = active.nextFieldMaterializationOccurrence(
                action.symbol, materializationSite);
        DynamicFieldSelection selection = active.dynamicFieldBinding(
                action, accessOwner, leafOwner, firstNonBlank(fieldSignature,
                        action.field, action.cell), materializationSite,
                occurrence, cursor);
        DynamicFieldBinding binding = selection.binding;
        annotateDynamicFieldBinding(cursor.entryObservation, binding,
                cursor.entryObservationId);
        if (!selection.created) {
            // The heap cell was already symbolized.  Re-reading the same
            // concrete owner must reuse its first dynamic symbol so aliases
            // remain aliases in the VM expression graph.
            return;
        }

        try {
            List<ModelAssignment> assignments =
                    active.dynamicFieldAssignments(action, binding);
            if (assignments.size() > 1) {
                active.unresolved.add(binding.dynamicBindingId
                        + ": multiple exact model assignments target one "
                        + "dynamic field binding");
                return;
            }
            if (assignments.isEmpty()) {
                assignments = active.explicitUniqueLegacyFieldAssignments(
                        action, binding);
            }
            if (assignments.size() > 1) {
                active.unresolved.add(binding.dynamicBindingId
                        + ": multiple legacy-unique assignments target one "
                        + "dynamic field binding");
                return;
            }
            if (!assignments.isEmpty()) {
                ModelAssignment assignment = assignments.get(0);
                if (!writeModeledField(leafOwner, action.leafField,
                        assignment)) {
                    active.unresolved.add(binding.dynamicBindingId
                            + ": solver model could not be written to exact "
                            + "entry field owner");
                    return;
                }
                active.recordDynamicMapModelAssignment(assignment,
                        "DYNAMIC_MAP_ENTRY_FIELD_ACCESS", action.fieldPath,
                        binding, readField(leafOwner, action.leafField));
            }

            active.fieldTargets.put(binding.dynamicBindingId,
                    new FieldObservationTarget(binding.dynamicFieldSymbol,
                            accessOwner, action.fieldPath, binding));
            JsonObject observation = fieldObservation(active,
                    binding.dynamicFieldSymbol, accessOwner,
                    action.fieldPath, "AT_MATERIALIZATION", binding);
            active.fieldObservations.add(observation);
            if (active.engineBacked) {
                symbolizeDynamicField(active, action, binding, leafOwner,
                        "DYNAMIC_MAP_ENTRY_FIELD_ACCESS", engine());
                // Iterator.next precedes the guarded field read.  Refresh the
                // same runtime entry after its value has acquired a symbolic
                // field, and retain the dynamic rather than static symbol.
                refreshEntryReadsForFieldOwner(active, leafOwner,
                        binding.dynamicFieldSymbol, binding);
            }
            binding.refresh(active, cursor);
            annotateDynamicFieldBinding(cursor.entryObservation, binding,
                    cursor.entryObservationId);
            annotateDynamicFieldBinding(observation, binding,
                    binding.entryReadObservationId);
        } catch (Throwable throwable) {
            active.unresolved.add(binding.dynamicBindingId
                    + ": dynamic field-site materialization "
                    + materializationSite + " failed: "
                    + rootCause(throwable));
        }
    }

    private static void symbolizeDynamicField(
            ActiveRegion active, SymbolizeAction action,
            DynamicFieldBinding binding, Object leafOwner, String location,
            EngineApi api) throws Exception {
        Object preSymbolizationValue = readField(leafOwner,
                action.leafField);
        DeclaredArrayInputType declaredType = action.exactLeafArrayType(
                leafOwner, action.leafField, action.fieldPath);
        boolean liveArray = preSymbolizationValue != null
                && preSymbolizationValue != MissingValue.INSTANCE
                && preSymbolizationValue.getClass().isArray();
        boolean declaredArray = declaredType.complete()
                || action.declaresArrayInput(action.fieldPath);
        if (!liveArray && !declaredArray) {
            api.symbolizeField(leafOwner, action.leafField,
                    binding.dynamicFieldSymbol);
            active.symbolized.add(binding.dynamicFieldSymbol);
            return;
        }
        long token = liveArray ? active.objectToken(
                preSymbolizationValue) : 0L;
        if (liveArray) {
            api.symbolize(preSymbolizationValue,
                    binding.dynamicFieldSymbol);
            active.symbolized.add(binding.dynamicFieldSymbol);
        }
        Object postSymbolizationValue = readField(leafOwner,
                action.leafField);
        active.captureDynamicEngineArrayInputBinding(action, binding,
                preSymbolizationValue, postSymbolizationValue, token,
                declaredType, location, api);
    }

    /**
     * Applies a solver-derived reference result at one scheduled assignment
     * occurrence.  The original operation has already executed, so its VM
     * expression remains available in the captured path condition.  This
     * runtime interface is intentionally theory-neutral: operation semantics
     * are metadata, not Java class or project-specific behavior.
     */
    public static Object materializeReplayReferenceResult(
            String method, int unitIndex, Object concreteResult) {
        ActiveRegion active = activeRegion();
        if (active == null) {
            return concreteResult;
        }
        if (!active.engineBacked) {
            // concreteReplayOnly plans prohibit reference-result injection.
            // Instrumented sites may still be shared with another activation;
            // in this mode they must be observational no-ops.
            return concreteResult;
        }
        EngineApi api = engine();
        boolean paused = false;
        try {
            api.pausePathCondition();
            paused = true;
            String siteId = safe(method) + "#u" + unitIndex;
            int occurrence = active.nextReplayOccurrence(siteId);
            ReplayMaterialization action = active.activation.replay(
                    method, unitIndex, occurrence);
            if (action == null) {
                return concreteResult;
            }
            if (!"REFERENCE_RESULT".equals(action.kind)) {
                active.unresolved.add(siteId
                        + ": unsupported replay value kind " + action.kind);
                return concreteResult;
            }

            Object modeled = modeledReferenceResult(action.desiredResult,
                    concreteResult);
            if (modeled == UnsupportedReplayValue.INSTANCE) {
                active.unresolved.add(siteId
                        + ": unsupported desired reference result "
                        + action.desiredResult);
                return concreteResult;
            }
            JsonObject applied = action.toJson();
            applied.addProperty("observedOccurrence", occurrence);
            applied.addProperty("concreteResultWasNull", concreteResult == null);
            applied.addProperty("modeledResultWasNull", modeled == null);
            active.replayMaterializationsApplied.add(applied);
            return modeled;
        } catch (Throwable throwable) {
            active.unresolved.add("replay materialization bookkeeping failed: "
                    + rootCause(throwable));
            return concreteResult;
        } finally {
            if (paused) {
                resumePathCondition(active, api);
            }
        }
    }

    static Object modeledReferenceResult(String desiredResult,
                                         Object concreteResult) {
        if ("NULL".equals(desiredResult)) {
            return null;
        }
        if ("UNCHANGED".equals(desiredResult)) {
            return concreteResult;
        }
        return UnsupportedReplayValue.INSTANCE;
    }

    /**
     * Binds a concrete Java Map view to its backing map for the currently
     * selected activation.  Instrumentation calls this only after the view
     * factory returned normally and while path-condition recording is paused.
     */
    public static void registerMapView(String method, int unitIndex,
                                       Object map, Object view,
                                       String viewKind) {
        ActiveRegion active = activeRegion();
        if (active == null || !(map instanceof Map) || view == null) {
            return;
        }
        active.mapViews.put(view, new MapViewBinding(map, safe(viewKind),
                siteId(method, unitIndex)));
    }

    /** Binds an iterator returned by a previously bound Map view. */
    public static void registerMapViewIterator(String method, int unitIndex,
                                               Object view,
                                               Object iterator) {
        ActiveRegion active = activeRegion();
        if (active == null || view == null || iterator == null) {
            return;
        }
        MapViewBinding binding = active.mapViews.get(view);
        if (binding == null) {
            return;
        }
        active.mapIterators.put(iterator, new MapIteratorCursor(binding,
                siteId(method, unitIndex)));
    }

    /**
     * Captures the entry selected by {@code Iterator.next()} before a later
     * remove mutates the map.  Expressions are obtained from the custom JDK's
     * public expression API, never reconstructed from HDFS-specific fields.
     */
    public static void recordMapIteratorNext(String method, int unitIndex,
                                             Object iterator,
                                             Object element) {
        ActiveRegion active = activeRegion();
        if (active == null || iterator == null) {
            return;
        }
        MapIteratorCursor cursor = active.mapIterators.get(iterator);
        if (cursor == null) {
            return;
        }
        cursor.resetForNext(siteId(method, unitIndex), element);
        try {
            if ("ENTRY_SET".equals(cursor.binding.viewKind)) {
                if (!(element instanceof Map.Entry)) {
                    cursor.bindingError = "entrySet iterator returned "
                            + (element == null ? "null"
                            : element.getClass().getName());
                } else {
                    Map.Entry<?, ?> entry = (Map.Entry<?, ?>) element;
                    cursor.key = entry.getKey();
                    cursor.value = entry.getValue();
                    cursor.keyKnown = true;
                    cursor.valueKnown = true;
                }
            } else if ("KEY_SET".equals(cursor.binding.viewKind)) {
                cursor.key = element;
                cursor.keyKnown = true;
                cursor.value = ((Map<?, ?>) cursor.binding.map).get(element);
                cursor.valueKnown = true;
            } else if ("VALUES".equals(cursor.binding.viewKind)) {
                // Values views do not reveal a unique key when values are
                // duplicated.  The native remove expression may supply that
                // key after the successful call; until then this remains an
                // explicit fail-closed binding obligation.
                cursor.value = element;
                cursor.valueKnown = true;
            } else {
                cursor.bindingError = "unsupported map view kind "
                        + cursor.binding.viewKind;
            }
            captureIteratorExpressions(active, cursor);
        } catch (Throwable throwable) {
            cursor.bindingError = "iterator next provenance failed: "
                    + rootCause(throwable);
        }
        if ("ENTRY_SET".equals(cursor.binding.viewKind)) {
            recordMapEntryRead(active, method, unitIndex, cursor);
            recordFiniteMapEntrySnapshot(active, method, unitIndex, cursor);
        }
    }

    /**
     * Records cardinality only from one complete, same-execution map
     * snapshot.  Individual MAP_ENTRY_READ rows are deliberately insufficient
     * evidence: the first bound ENTRY_SET iterator must identify the same
     * first entry, and the exact map implementation, size, entry order, keys,
     * and value identities must remain unchanged across the snapshot.
     */
    private static void recordFiniteMapEntrySnapshot(
            ActiveRegion active, String method, int unitIndex,
            MapIteratorCursor cursor) {
        if (cursor.finiteMapSnapshotAttempted) return;
        cursor.finiteMapSnapshotAttempted = true;
        Object candidate = cursor.binding.map;
        if (!"ENTRY_SET".equals(cursor.binding.viewKind) || candidate == null
                || active.finiteMapSnapshotAttemptedMaps.put(
                candidate, Boolean.TRUE) != null
                || !supportedMapProjectionImplementation(candidate)
                || !(cursor.element instanceof Map.Entry<?, ?>)
                || !completeRuntimeExpression(cursor.mapExpression)) {
            return;
        }

        Map<?, ?> map = (Map<?, ?>) candidate;
        try {
            int sizeBefore = map.size();
            int entrySetSizeBefore = map.entrySet().size();
            if (sizeBefore < 1 || sizeBefore > MAX_MAP_PROJECTION_ELEMENTS
                    || entrySetSizeBefore != sizeBefore) {
                return;
            }
            Object[] before = map.entrySet().toArray();
            if (before.length != sizeBefore) return;

            JsonArray keys = new JsonArray();
            JsonArray keyTokens = new JsonArray();
            JsonArray valueTokens = new JsonArray();
            JsonArray values = new JsonArray();
            JsonArray entries = new JsonArray();
            String[] selectors = new String[sizeBefore];
            Object[] concreteValues = new Object[sizeBefore];
            Set<String> distinct = new LinkedHashSet<>();
            for (int index = 0; index < before.length; index++) {
                if (!(before[index] instanceof Map.Entry<?, ?>)) return;
                Map.Entry<?, ?> entry = (Map.Entry<?, ?>) before[index];
                Object key = entry.getKey();
                Object value = entry.getValue();
                JsonElement keyExpression = immutableEntryKeyExpression(key);
                String selector = stableMapProjectionKeySelector(
                        keyExpression);
                if (keyExpression == null || selector.isEmpty()
                        || !distinct.add(selector)) {
                    return;
                }
                selectors[index] = selector;
                concreteValues[index] = value;
                long keyToken = active.objectToken(key);
                long valueToken = active.objectToken(value);
                JsonElement valueExpression = value == null
                        ? nullReferenceExpression()
                        : activationLocalValueRefWitnessExpression(
                        active.activation.activationId, valueToken);

                keys.add(copyJsonTree(keyExpression));
                keyTokens.add(new JsonPrimitive(Long.valueOf(keyToken)));
                valueTokens.add(new JsonPrimitive(Long.valueOf(valueToken)));
                values.add(copyJsonTree(valueExpression));
                JsonObject row = new JsonObject();
                row.addProperty("index", index);
                row.add("keyExpression", copyJsonTree(keyExpression));
                row.addProperty("keyObjectToken", keyToken);
                row.add("valueExpression", copyJsonTree(valueExpression));
                row.addProperty("valueObjectToken", valueToken);
                row.addProperty("valueWasNull", value == null);
                row.addProperty("valueExpressionAuthority", value == null
                        ? EXACT_RUNTIME_NULL_AUTHORITY
                        : VALUE_REF_WITNESS_AUTHORITY);
                entries.add(row);
            }

            Map.Entry<?, ?> first = (Map.Entry<?, ?>) cursor.element;
            String firstSelector = stableMapProjectionKeySelector(
                    immutableEntryKeyExpression(first.getKey()));
            if (!selectors[0].equals(firstSelector)
                    || first.getValue() != concreteValues[0]) {
                return;
            }

            Object[] after = map.entrySet().toArray();
            int entrySetSizeAfter = map.entrySet().size();
            int sizeAfter = map.size();
            if (sizeAfter != sizeBefore
                    || entrySetSizeAfter != entrySetSizeBefore
                    || after.length != before.length) {
                return;
            }
            for (int index = 0; index < after.length; index++) {
                if (!(after[index] instanceof Map.Entry<?, ?>)) return;
                Map.Entry<?, ?> entry = (Map.Entry<?, ?>) after[index];
                String selector = stableMapProjectionKeySelector(
                        immutableEntryKeyExpression(entry.getKey()));
                if (!selectors[index].equals(selector)
                        || entry.getValue() != concreteValues[index]
                        || !map.containsKey(entry.getKey())
                        || map.get(entry.getKey()) != concreteValues[index]) {
                    return;
                }
            }

            long mapToken = active.objectToken(map);
            String dedupe = mapToken + "|" + distinct + "|" + valueTokens;
            if (!active.finiteMapSnapshotIdentities.add(dedupe)) return;
            String site = siteId(method, unitIndex);
            int occurrence = active.nextFiniteMapSnapshotOccurrence(site);
            JsonObject observation = new JsonObject();
            observation.addProperty("schemaVersion", 1);
            observation.addProperty("kind", "FINITE_MAP_ENTRY_SNAPSHOT");
            observation.addProperty("operation", "java.util.Map.entrySet");
            observation.addProperty("observationId",
                    "FINITE_MAP_ENTRY_SNAPSHOT:" + site + "#" + occurrence);
            observation.addProperty("eventSequence",
                    cursor.entryObservationSequence);
            observation.addProperty("eventSequenceAuthority",
                    "SAME_ITERATOR_NEXT_AS_MAP_ENTRY_READ");
            observation.addProperty("originMethod", safe(method));
            observation.addProperty("originUnitIndex", unitIndex);
            observation.addProperty("siteId", site);
            observation.addProperty("viewKind", cursor.binding.viewKind);
            observation.addProperty("viewOriginSiteId",
                    cursor.binding.originSiteId);
            observation.addProperty("iteratorOriginSiteId",
                    cursor.iteratorOriginSiteId);
            observation.addProperty("mapImplementationClass",
                    map.getClass().getName());
            observation.addProperty("mapImplementationAuthority",
                    MAP_PROJECTION_IMPLEMENTATION_AUTHORITY);
            observation.addProperty("mapObjectToken", mapToken);
            observation.addProperty("backingMapObjectToken", mapToken);
            observation.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            observation.addProperty("objectTokenScope",
                    active.activation.activationId);
            observation.add("mapExpression",
                    copyJsonTree(cursor.mapExpression));
            observation.addProperty("mapExpressionAuthority",
                    active.engineBacked
                            ? "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_FIRST_"
                            + "ENTRY_SET_NEXT"
                            : "CONCRETE_REPLAY_RUNTIME_VALUE_AT_FIRST_"
                            + "ENTRY_SET_NEXT");
            observation.addProperty("entryCount", sizeBefore);
            observation.addProperty("finiteEntryBound",
                    MAX_MAP_PROJECTION_ELEMENTS);
            observation.addProperty("sizeBefore", sizeBefore);
            observation.addProperty("entrySetSizeBefore",
                    entrySetSizeBefore);
            observation.addProperty("sizeAfter", sizeAfter);
            observation.addProperty("entrySetSizeAfter", entrySetSizeAfter);
            observation.add("keyExpressions", keys);
            observation.add("keyObjectTokens", keyTokens);
            observation.addProperty("keyExpressionAuthority",
                    "CONCRETE_IMMUTABLE_MAP_ENTRY_KEYS_AT_SAME_EXECUTION_"
                            + "ENTRY_SET_SNAPSHOT");
            observation.add("valueObjectTokens", valueTokens);
            observation.add("valueExpressions", values);
            observation.addProperty("valueExpressionAuthority",
                    FINITE_MAP_VALUE_EXPRESSION_AUTHORITY);
            observation.add("entries", entries);
            observation.addProperty("keysDistinct", true);
            observation.addProperty("firstIteratorEntryMatched", true);
            observation.addProperty("sizeStable", true);
            observation.addProperty("entrySetStable", true);
            observation.addProperty("preRemove", true);
            observation.addProperty("authority",
                    FINITE_MAP_SNAPSHOT_AUTHORITY);
            observation.addProperty("complete", true);
            active.finiteMapSnapshots.add(observation);
        } catch (Throwable ignored) {
            // Optional finite-domain evidence is emitted only when every
            // check succeeds.  A failed snapshot must not be weakened into a
            // cardinality claim or invalidate ordinary MAP_ENTRY_READ rows.
        }
    }

    private static JsonObject nullReferenceExpression() {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "L");
        expression.addProperty("_exp", "N");
        return expression;
    }

    /**
     * Persists the non-mutating entry read independently of a later
     * {@code Iterator.remove()}.  Keeping this separate from heap effects is
     * important: a path which retains the entry still needs an exact witness
     * that its guard value came from one key/value pair in the backing map.
     */
    private static void recordMapEntryRead(ActiveRegion active,
                                           String method, int unitIndex,
                                           MapIteratorCursor cursor) {
        // Ordinary heap objects whose fields have become symbolic do not
        // necessarily acquire a custom-JDK reference shadow.  Preserve the
        // exact entry/value identity with a distinctly-authorized Ref witness;
        // a later successful public-expression lookup still replaces it.
        ensureActivationLocalValueRefWitness(active, cursor);
        String originSite = siteId(method, unitIndex);
        int occurrence = active.nextHeapObservationOccurrence(originSite);
        long sequence = active.nextRuntimeEventSequence();
        String observationId = "MAP_ENTRY_READ:" + originSite + "#"
                + occurrence;

        JsonObject observation = new JsonObject();
        observation.addProperty("schemaVersion", 1);
        observation.addProperty("kind", "MAP_ENTRY_READ");
        observation.addProperty("operation", "java.util.Iterator.next");
        observation.addProperty("observationId", observationId);
        observation.addProperty("eventSequence", sequence);
        observation.addProperty("occurrence", occurrence);
        observation.addProperty("originMethod", safe(method));
        observation.addProperty("originUnitIndex", unitIndex);
        observation.addProperty("siteId", originSite);
        observation.addProperty("viewKind", cursor.binding.viewKind);
        observation.addProperty("viewOriginSiteId",
                cursor.binding.originSiteId);
        observation.addProperty("iteratorOriginSiteId",
                cursor.iteratorOriginSiteId);
        observation.addProperty("nextOriginSiteId", cursor.nextOriginSiteId);
        observation.addProperty("rawPathConditionBoundary",
                cursor.pathConditionSize);
        observation.addProperty("pcBoundary", cursor.pathConditionSize);
        observation.addProperty("provenanceAuthority",
                "ACTIVATION_LOCAL_BACKED_ENTRY_SET_IDENTITY_AT_NEXT");
        observation.addProperty("mapBindingAuthority",
                "BOUND_ENTRY_SET_VIEW_BACKING_MAP_IDENTITY");
        observation.addProperty("entryBindingAuthority",
                "JAVA_MAP_ENTRY_FROM_BOUND_ENTRY_SET_NEXT");
        observation.addProperty("keyBindingAuthority",
                "SAME_MAP_ENTRY_GET_KEY_AT_NEXT");
        observation.addProperty("valueBindingAuthority",
                "SAME_MAP_ENTRY_GET_VALUE_AT_NEXT");
        observation.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observation.addProperty("objectTokenScope",
                active.activation.activationId);
        observation.addProperty("expressionAuthority", active.engineBacked
                ? "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT"
                : "CONCRETE_REPLAY_RUNTIME_VALUE_AT_ITERATOR_NEXT");
        observation.addProperty("keyExpressionAuthority",
                cursor.keyExpressionAuthority);
        observation.addProperty("valueExpressionAuthority",
                cursor.valueExpressionAuthority);
        if (!cursor.entryExpressionWarning.isEmpty()) {
            observation.addProperty("entryExpressionWarning",
                    cursor.entryExpressionWarning);
        }
        if (!cursor.valueExpressionWarning.isEmpty()) {
            observation.addProperty("initialValueExpressionWarning",
                    cursor.valueExpressionWarning);
        }

        Object map = cursor.binding.map;
        long backingMapObjectToken = active.objectToken(map);
        long entryObjectToken = active.objectToken(cursor.element);
        long keyObjectToken = cursor.keyKnown
                ? active.objectToken(cursor.key) : 0L;
        long valueObjectToken = cursor.valueKnown
                ? active.objectToken(cursor.value) : 0L;
        observation.addProperty("backingMapIdentity",
                System.identityHashCode(map));
        observation.addProperty("backingMapIdentityKnown", true);
        observation.addProperty("backingMapObjectToken",
                backingMapObjectToken);
        observation.addProperty("backingMapObjectTokenKnown", true);

        boolean entryKnown = cursor.element instanceof Map.Entry;
        observation.addProperty("entryIdentity", cursor.element == null ? 0
                : System.identityHashCode(cursor.element));
        observation.addProperty("entryIdentityKnown", entryKnown);
        observation.addProperty("entryObjectToken",
                entryObjectToken);
        observation.addProperty("entryObjectTokenKnown", entryKnown);
        observation.addProperty("entryWasNull", cursor.element == null);

        observation.addProperty("keyIdentity", cursor.keyKnown
                && cursor.key != null ? System.identityHashCode(cursor.key) : 0);
        observation.addProperty("keyIdentityKnown", cursor.keyKnown);
        observation.addProperty("keyObjectToken",
                keyObjectToken);
        observation.addProperty("keyObjectTokenKnown", cursor.keyKnown);
        observation.addProperty("keyWasNull",
                cursor.keyKnown && cursor.key == null);

        observation.addProperty("valueIdentity", cursor.valueKnown
                && cursor.value != null
                ? System.identityHashCode(cursor.value) : 0);
        observation.addProperty("valueIdentityKnown", cursor.valueKnown);
        observation.addProperty("valueObjectToken",
                valueObjectToken);
        observation.addProperty("valueObjectTokenKnown", cursor.valueKnown);
        observation.addProperty("valueWasNull",
                cursor.valueKnown && cursor.value == null);

        if (cursor.mapExpression != null) {
            observation.add("mapExpression", cursor.mapExpression);
        }
        if (cursor.keyExpression != null) {
            observation.add("keyExpression", cursor.keyExpression);
        }
        if (cursor.valueExpression != null) {
            observation.add("valueExpression", cursor.valueExpression);
        }
        if (cursor.entryExpression != null) {
            observation.add("entryExpression", cursor.entryExpression);
        }

        active.runtimeHeapObservations.add(observation);
        cursor.entryObservationId = observationId;
        cursor.entryObservationSequence = sequence;
        cursor.entryObservation = observation;
        updateMapEntryReadObservation(active, cursor, "AT_ITERATOR_NEXT");
    }

    private static boolean completeRuntimeExpression(JsonElement expression) {
        return expression != null && !expression.isJsonNull()
                && expression.isJsonObject();
    }

    static boolean completeMapEntryReadPayload(
            JsonElement mapExpression, JsonElement keyExpression,
            JsonElement valueExpression, JsonElement optionalEntryExpression,
            long backingMapObjectToken, long keyObjectToken,
            long valueObjectToken, long entryObjectToken) {
        // The custom JDK does not promise a symbolic reference for the
        // concrete HashMap.Node/Map.Entry wrapper.  Exact entry provenance is
        // instead carried by its collision-free activation-local object token
        // and the SAME_MAP_ENTRY key/value authorities.
        boolean knownNullKey = nullEntryKeyExpression(keyExpression);
        return completeRuntimeExpression(mapExpression)
                && completeRuntimeExpression(keyExpression)
                && completeRuntimeExpression(valueExpression)
                && backingMapObjectToken > 0L
                && (keyObjectToken > 0L || knownNullKey)
                && valueObjectToken > 0L && entryObjectToken > 0L;
    }

    private static boolean nullEntryKeyExpression(JsonElement expression) {
        if (!completeRuntimeExpression(expression)) {
            return false;
        }
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        if (("SymbolExpression".equals(type)
                || "ConSymbolExp".equals(type))
                && "N".equals(string(object, "_exp"))) {
            return true;
        }
        return "CONCRETE_RUNTIME_VALUE".equals(string(object, "kind"))
                && "NULL".equals(string(object, "valueType"));
    }

    private static void updateMapEntryReadObservation(
            ActiveRegion active, MapIteratorCursor cursor,
            String refreshAuthority) {
        JsonObject observation = cursor.entryObservation;
        if (observation == null) {
            return;
        }
        if (completeRuntimeExpression(cursor.mapExpression)) {
            observation.add("mapExpression", cursor.mapExpression);
        }
        if (completeRuntimeExpression(cursor.keyExpression)) {
            observation.add("keyExpression", cursor.keyExpression);
        }
        if (completeRuntimeExpression(cursor.valueExpression)) {
            observation.add("valueExpression", cursor.valueExpression);
        }
        if (completeRuntimeExpression(cursor.entryExpression)) {
            observation.add("entryExpression", cursor.entryExpression);
        }
        observation.addProperty("keyExpressionAuthority",
                cursor.keyExpressionAuthority);
        observation.addProperty("valueExpressionAuthority",
                cursor.valueExpressionAuthority);
        annotateValueRefWitness(observation, active, cursor);
        observation.addProperty("lastRefreshAuthority", refreshAuthority);
        observation.addProperty("refreshCount", ++cursor.entryRefreshCount);

        long backingMapObjectToken = active.objectToken(cursor.binding.map);
        long keyObjectToken = cursor.keyKnown
                ? active.objectToken(cursor.key) : 0L;
        long valueObjectToken = cursor.valueKnown
                ? active.objectToken(cursor.value) : 0L;
        long entryObjectToken = active.objectToken(cursor.element);
        boolean entryKnown = cursor.element instanceof Map.Entry;
        String unresolved = safe(cursor.bindingError);
        if (!cursor.hasCurrent) {
            unresolved = appendReason(unresolved,
                    "Iterator.next did not establish a current entry");
        }
        if (!entryKnown) {
            unresolved = appendReason(unresolved,
                    "entrySet iterator result is not a java.util.Map.Entry");
        }
        if (!cursor.keyKnown || !cursor.valueKnown) {
            unresolved = appendReason(unresolved,
                    "entry key/value binding is incomplete");
        }
        List<String> missingExpressions = new ArrayList<>();
        if (!completeRuntimeExpression(cursor.mapExpression)) {
            missingExpressions.add("map");
        }
        if (!completeRuntimeExpression(cursor.keyExpression)) {
            missingExpressions.add("key");
        }
        if (!completeRuntimeExpression(cursor.valueExpression)) {
            missingExpressions.add("value");
        }
        if (!missingExpressions.isEmpty()) {
            unresolved = appendReason(unresolved,
                    "symbolic expressions unavailable for "
                            + missingExpressions);
        }
        boolean payloadComplete = completeMapEntryReadPayload(
                cursor.mapExpression, cursor.keyExpression,
                cursor.valueExpression, cursor.entryExpression,
                backingMapObjectToken, keyObjectToken, valueObjectToken,
                entryObjectToken);
        boolean keyAuthorityComplete =
                "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT".equals(
                        cursor.keyExpressionAuthority)
                        || "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT".equals(
                        cursor.keyExpressionAuthority)
                        || "CONCRETE_REPLAY_RUNTIME_VALUE_AT_ITERATOR_NEXT"
                        .equals(cursor.keyExpressionAuthority);
        boolean valueAuthorityComplete =
                "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT".equals(
                        cursor.valueExpressionAuthority)
                        || "AFTER_MATCHED_FIELD_SYMBOLIZATION".equals(
                        cursor.valueExpressionAuthority)
                        || "BEFORE_ITERATOR_REMOVE_JOIN".equals(
                        cursor.valueExpressionAuthority)
                        || "CONCRETE_REPLAY_RUNTIME_VALUE_AT_ITERATOR_NEXT"
                        .equals(cursor.valueExpressionAuthority)
                        || VALUE_REF_WITNESS_AUTHORITY.equals(
                        cursor.valueExpressionAuthority);
        boolean bindingAuthorityComplete = keyAuthorityComplete
                && valueAuthorityComplete;
        if (!payloadComplete && missingExpressions.isEmpty()) {
            unresolved = appendReason(unresolved,
                    "activation-local map/key/value/entry object tokens are incomplete");
        }
        if (!keyAuthorityComplete) {
            unresolved = appendReason(unresolved,
                    "entry key expression authority is incomplete");
        }
        if (!valueAuthorityComplete) {
            unresolved = appendReason(unresolved,
                    "entry value expression authority is incomplete");
        }
        boolean complete = unresolved.isEmpty()
                && cursor.hasCurrent && entryKnown
                && cursor.keyKnown && cursor.valueKnown
                && payloadComplete && bindingAuthorityComplete;
        observation.addProperty("entryBindingComplete",
                cursor.hasCurrent && entryKnown
                        && cursor.keyKnown && cursor.valueKnown);
        observation.addProperty("expressionBindingComplete",
                missingExpressions.isEmpty());
        observation.addProperty("entryExpressionAvailable",
                completeRuntimeExpression(cursor.entryExpression));
        observation.addProperty("objectTokenBindingComplete",
                backingMapObjectToken > 0L
                        && (keyObjectToken > 0L
                        || cursor.keyKnown && cursor.key == null
                        && nullEntryKeyExpression(cursor.keyExpression))
                        && valueObjectToken > 0L && entryObjectToken > 0L);
        observation.addProperty("bindingAuthorityComplete",
                bindingAuthorityComplete);
        observation.addProperty("runtimeProvenanceComplete", complete);
        observation.addProperty("complete", complete);

        if (!cursor.entryObservationUnresolved.isEmpty()) {
            active.unresolved.remove(cursor.entryObservationUnresolved);
            cursor.entryObservationUnresolved = "";
        }
        if (complete) {
            observation.remove("unresolvedReason");
        } else {
            observation.addProperty("unresolvedReason", unresolved);
            cursor.entryObservationUnresolved = string(observation, "siteId")
                    + ": backed entry-set read unresolved: " + unresolved;
            active.unresolved.add(cursor.entryObservationUnresolved);
        }
        cursor.entryObservationComplete = complete;
    }

    private static void refreshMapEntryValueExpression(
            ActiveRegion active, MapIteratorCursor cursor,
            String refreshAuthority) {
        if (cursor == null || cursor.entryObservation == null
                || !cursor.valueKnown || cursor.value == null) {
            return;
        }
        if (active.engineBacked) {
            try {
                JsonElement refreshed = canonicalEngineExpression(
                        engine().expression(cursor.value));
                if (completeRuntimeExpression(refreshed)) {
                    cursor.valueExpression = refreshed;
                    cursor.valueExpressionAuthority = refreshAuthority;
                    clearValueRefWitness(cursor.entryObservation);
                    cursor.entryObservation.addProperty(
                            "valueExpressionAuthority", refreshAuthority);
                    cursor.entryObservation.addProperty(
                            "valueExpressionResolvedAfterRefresh", true);
                }
            } catch (Throwable throwable) {
                cursor.entryObservation.addProperty("valueExpressionWarning",
                        rootCause(throwable));
            }
        }
        ensureActivationLocalValueRefWitness(active, cursor);
        updateMapEntryReadObservation(active, cursor, refreshAuthority);
    }

    private static boolean ensureActivationLocalValueRefWitness(
            ActiveRegion active, MapIteratorCursor cursor) {
        if (active == null || cursor == null || !active.engineBacked
                || !cursor.valueKnown || cursor.value == null
                || completeRuntimeExpression(cursor.valueExpression)) {
            return false;
        }
        long valueObjectToken = active.objectToken(cursor.value);
        if (valueObjectToken <= 0L
                || safe(active.activation.activationId).isEmpty()) {
            return false;
        }
        JsonObject witness = activationLocalValueRefWitnessExpression(
                active.activation.activationId, valueObjectToken);
        cursor.valueExpression = witness;
        cursor.valueExpressionAuthority = VALUE_REF_WITNESS_AUTHORITY;
        annotateValueRefWitness(cursor.entryObservation, active, cursor);
        return true;
    }

    private static JsonObject activationLocalValueRefWitnessExpression(
            String activationId, long objectToken) {
        JsonObject witness = new JsonObject();
        witness.addProperty("_type", "SymbolExpression");
        witness.addProperty("_java_type", "L");
        witness.addProperty("_exp", valueRefWitnessSymbol(activationId,
                objectToken));
        return witness;
    }

    private static void annotateValueRefWitness(
            JsonObject target, ActiveRegion active, MapIteratorCursor cursor) {
        if (target == null || active == null || cursor == null
                || !VALUE_REF_WITNESS_AUTHORITY.equals(
                cursor.valueExpressionAuthority)
                || !completeRuntimeExpression(cursor.valueExpression)
                || !cursor.valueKnown || cursor.value == null) {
            return;
        }
        long token = active.objectToken(cursor.value);
        if (token <= 0L) return;
        target.addProperty("valueExpressionWitnessSchemaVersion", 1);
        target.addProperty("valueExpressionWitnessKind",
                VALUE_REF_WITNESS_KIND);
        target.addProperty("valueExpressionWitnessObjectToken", token);
        target.addProperty("valueExpressionWitnessObjectTokenScope",
                active.activation.activationId);
        target.addProperty("valueExpressionWitnessAuthority",
                VALUE_REF_WITNESS_TOKEN_AUTHORITY);
    }

    private static void clearValueRefWitness(JsonObject target) {
        if (target == null) return;
        target.remove("valueExpressionWitnessSchemaVersion");
        target.remove("valueExpressionWitnessKind");
        target.remove("valueExpressionWitnessObjectToken");
        target.remove("valueExpressionWitnessObjectTokenScope");
        target.remove("valueExpressionWitnessAuthority");
    }

    private static String valueRefWitnessSymbol(String activationId,
                                                long objectToken) {
        byte[] bytes = safe(activationId).getBytes(StandardCharsets.UTF_8);
        StringBuilder hex = new StringBuilder(bytes.length * 2);
        for (byte value : bytes) {
            int unsigned = value & 0xff;
            hex.append(Character.forDigit(unsigned >>> 4, 16));
            hex.append(Character.forDigit(unsigned & 0x0f, 16));
        }
        return VALUE_REF_WITNESS_SYMBOL_PREFIX + hex.length() + "_" + hex
                + "_T" + objectToken;
    }

    private static void refreshEntryReadsForFieldOwner(
            ActiveRegion active, Object leafOwner, String symbol,
            DynamicFieldBinding binding) {
        if (leafOwner == null || leafOwner == MissingValue.INSTANCE) {
            return;
        }
        for (MapIteratorCursor cursor : active.mapIterators.values()) {
            if (cursor.hasCurrent && cursor.valueKnown
                    && cursor.value == leafOwner
                    && cursor.entryObservation != null) {
                JsonArray fields = array(cursor.entryObservation,
                        "fieldSymbols");
                boolean present = false;
                for (JsonElement field : fields) {
                    if (field.isJsonPrimitive()
                            && safe(symbol).equals(field.getAsString())) {
                        present = true;
                        break;
                    }
                }
                if (!present) {
                    // Hadoop 2.x supplies Gson 2.2.4 at runtime.  That
                    // version only exposes JsonArray.add(JsonElement), not
                    // the scalar convenience overloads added later.
                    fields.add(new JsonPrimitive(safe(symbol)));
                    cursor.entryObservation.add("fieldSymbols", fields);
                }
                if (binding != null) {
                    annotateDynamicFieldBinding(cursor.entryObservation,
                            binding, cursor.entryObservationId);
                }
                refreshMapEntryValueExpression(active, cursor,
                        "AFTER_MATCHED_FIELD_SYMBOLIZATION");
                if (binding != null) {
                    binding.refresh(active, cursor);
                    annotateDynamicFieldBinding(cursor.entryObservation,
                            binding, cursor.entryObservationId);
                }
            }
        }
    }

    private static void annotateDynamicFieldBinding(
            JsonObject target, DynamicFieldBinding binding,
            String entryReadObservationId) {
        if (target == null || binding == null) {
            return;
        }
        target.addProperty("dynamicBindingId", binding.dynamicBindingId);
        target.addProperty("baseInputSymbol", binding.baseInputSymbol);
        target.addProperty("dynamicFieldSymbol",
                binding.dynamicFieldSymbol);
        target.addProperty("materializationSiteId",
                binding.materializationSiteId);
        target.addProperty("materializationOccurrence",
                binding.materializationOccurrence);
        if (binding.containerSelector != null) {
            target.addProperty("actualHookSiteId",
                    binding.actualHookSiteId);
            target.addProperty("actualHookOccurrence",
                    binding.actualHookOccurrence);
            target.addProperty("effectiveMaterializationSiteId",
                    binding.materializationSiteId);
            target.addProperty("effectiveMaterializationOccurrence",
                    binding.materializationOccurrence);
            target.addProperty("materializationSiteBridgeAuthority",
                    binding.materializationSiteBridgeAuthority);
            target.addProperty("materializationSiteBridgeBindingId",
                    binding.materializationSiteBridgeBindingId);
            target.addProperty(
                    "materializationSiteBridgeElementObjectToken",
                    binding.materializationSiteBridgeElementObjectToken);
            target.addProperty(
                    "materializationSiteBridgeObjectTokenScope",
                    binding.materializationSiteBridgeObjectTokenScope);
        }
        target.addProperty("dynamicFieldBindingSchemaVersion",
                binding.schemaVersion);
        target.addProperty("dynamicFieldBindingKind", binding.kind);
        target.addProperty("fieldSignature", binding.fieldSignature);
        target.add("fieldPath", GSON.toJsonTree(binding.fieldPath));
        target.addProperty("leafOwnerObjectToken",
                binding.leafOwnerObjectToken);
        String entryRead = firstNonBlank(entryReadObservationId,
                binding.entryReadObservationId);
        if (!entryRead.isEmpty()) {
            target.addProperty("entryReadObservationId", entryRead);
        }
        if (binding.keyExpression != null) {
            target.add("keyExpression", copyJsonTree(binding.keyExpression));
        }
        if (!safe(binding.keyExpressionAuthority).isEmpty()) {
            target.addProperty("keyExpressionAuthority",
                    binding.keyExpressionAuthority);
        }
        if (binding.containerSelector != null) {
            target.add("containerSelector",
                    binding.containerSelector.toJson());
            binding.containerSelector.addFlatCompatibilityFields(target);
        }
        target.addProperty("dynamicFieldBindingAuthority",
                binding.authority);
        target.addProperty("dynamicFieldBindingComplete", binding.complete);
        boolean enclosingComplete = !"MAP_ENTRY_READ".equals(
                string(target, "kind")) || bool(target, "complete", true);
        target.addProperty("complete", binding.complete
                && enclosingComplete);
    }

    /**
     * Records one canonical map removal after {@code Iterator.remove()}
     * returned normally.  Because the hook is post-call, an exceptional
     * remove never sets {@code applied=true}.  The application site is joined
     * to the unique native MethodExpression in the newly recorded VM suffix.
     */
    public static void recordMapIteratorRemove(String method, int unitIndex,
                                               Object iterator) {
        ActiveRegion active = activeRegion();
        if (active == null || iterator == null) {
            return;
        }
        MapIteratorCursor cursor = active.mapIterators.get(iterator);
        if (cursor == null) {
            // Most Iterator.remove calls in a broad static region are not map
            // backed. Identity provenance, rather than the method name alone,
            // is the admission authority.
            return;
        }

        // A field hook between next() and remove() may have made the entry
        // value's custom-JDK expression available.  Refresh once more before
        // joining application provenance to the native map transformer.
        refreshMapEntryValueExpression(active, cursor,
                "BEFORE_ITERATOR_REMOVE_JOIN");

        String originSite = siteId(method, unitIndex);
        JsonObject effect = new JsonObject();
        effect.addProperty("schemaVersion", 1);
        effect.addProperty("kind", "MAP_REMOVE");
        effect.addProperty("operation", "java.util.Iterator.remove");
        effect.addProperty("originMethod", safe(method));
        effect.addProperty("originUnitIndex", unitIndex);
        effect.addProperty("siteId", originSite);
        effect.addProperty("occurrence",
                active.nextHeapEffectOccurrence(originSite));
        effect.addProperty("eventSequence",
                active.nextRuntimeEventSequence());
        effect.addProperty("applied", true);
        effect.addProperty("viewKind", cursor.binding.viewKind);
        effect.addProperty("viewOriginSiteId",
                cursor.binding.originSiteId);
        effect.addProperty("iteratorOriginSiteId",
                cursor.iteratorOriginSiteId);
        effect.addProperty("nextOriginSiteId", cursor.nextOriginSiteId);
        effect.addProperty("provenanceAuthority",
                "ACTIVATION_LOCAL_BACKED_VIEW_IDENTITY_AND_NORMAL_RETURN");
        effect.addProperty("portBindingAuthority",
                "DEFERRED_TO_IMPORTER_EXACT_ACTIVATION_PORT");
        effect.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        effect.addProperty("objectTokenScope",
                active.activation.activationId);
        effect.addProperty("entryReadObservationId",
                cursor.entryObservationId);
        effect.addProperty("entryReadObservationSequence",
                cursor.entryObservationSequence);
        effect.addProperty("entryReadObservationComplete",
                cursor.entryObservationComplete);
        effect.addProperty("backingMapIdentity",
                System.identityHashCode(cursor.binding.map));
        effect.addProperty("backingMapIdentityKnown", true);
        effect.addProperty("backingMapObjectToken",
                active.objectToken(cursor.binding.map));
        effect.addProperty("backingMapObjectTokenKnown", true);
        effect.addProperty("keyIdentity", cursor.keyKnown
                && cursor.key != null ? System.identityHashCode(cursor.key) : 0);
        effect.addProperty("keyIdentityKnown", cursor.keyKnown);
        effect.addProperty("keyObjectToken", cursor.keyKnown
                ? active.objectToken(cursor.key) : 0L);
        effect.addProperty("keyObjectTokenKnown", cursor.keyKnown);
        effect.addProperty("keyWasNull",
                cursor.keyKnown && cursor.key == null);
        int valueIdentity = cursor.valueKnown && cursor.value != null
                ? System.identityHashCode(cursor.value) : 0;
        effect.addProperty("valueIdentity", valueIdentity);
        effect.addProperty("valueIdentityKnown", cursor.valueKnown);
        effect.addProperty("valueObjectToken", cursor.valueKnown
                ? active.objectToken(cursor.value) : 0L);
        effect.addProperty("valueObjectTokenKnown", cursor.valueKnown);
        effect.addProperty("valueWasNull",
                cursor.valueKnown && cursor.value == null);
        effect.addProperty("entryIdentity", cursor.element == null ? 0
                : System.identityHashCode(cursor.element));
        effect.addProperty("entryIdentityKnown",
                cursor.element instanceof Map.Entry);
        effect.addProperty("entryObjectToken",
                active.objectToken(cursor.element));
        effect.addProperty("entryObjectTokenKnown",
                cursor.element instanceof Map.Entry);
        effect.addProperty("valueRequiredForTransformer", false);
        boolean entrySet = "ENTRY_SET".equals(cursor.binding.viewKind);
        effect.addProperty("valueRequiredForGuardProvenance", entrySet);
        if (entrySet && cursor.element instanceof Map.Entry) {
            effect.addProperty("entryIdentity",
                    System.identityHashCode(cursor.element));
            effect.addProperty("entryBindingAuthority",
                    "JAVA_MAP_ENTRY_FROM_BOUND_ENTRY_SET_NEXT");
            effect.addProperty("valueBindingAuthority",
                    "SAME_MAP_ENTRY_GET_VALUE_AT_NEXT");
            effect.addProperty("keyBindingAuthority",
                    "SAME_MAP_ENTRY_GET_KEY_AT_NEXT");
        } else if ("KEY_SET".equals(cursor.binding.viewKind)) {
            effect.addProperty("keyBindingAuthority",
                    "BOUND_KEY_SET_NEXT_ELEMENT");
            effect.addProperty("valueBindingAuthority",
                    "BACKING_MAP_LOOKUP_AT_NEXT");
        } else if ("VALUES".equals(cursor.binding.viewKind)) {
            effect.addProperty("valueBindingAuthority",
                    "BOUND_VALUES_NEXT_ELEMENT");
        }

        String unresolved = cursor.hasCurrent ? safe(cursor.bindingError)
                : "Iterator.remove returned normally without a bound next element";
        JsonArray conditions = new JsonArray();
        int start = Math.max(cursor.pathConditionSize,
                active.lastPathConditionSize);
        int end = start;
        if (active.engineBacked) {
            try {
                JsonElement parsed = parseJson(engine().pathCondition());
                conditions = parsed.isJsonArray()
                        ? parsed.getAsJsonArray() : new JsonArray();
                end = conditions.size();
            } catch (Throwable throwable) {
                unresolved = appendReason(unresolved,
                        "VM path condition unavailable: "
                                + rootCause(throwable));
            }
        }
        effect.addProperty("rawPathConditionStart", start);
        effect.addProperty("rawPathConditionEnd", end);

        if (cursor.mapExpression != null) {
            effect.add("mapExpression", cursor.mapExpression);
        }
        if (cursor.keyExpression != null) {
            effect.add("keyExpression", cursor.keyExpression);
        }
        if (!safe(cursor.keyExpressionAuthority).isEmpty()) {
            effect.addProperty("keyExpressionAuthority",
                    cursor.keyExpressionAuthority);
        }
        if (cursor.valueExpression != null) {
            effect.add("valueExpression", cursor.valueExpression);
        }
        effect.addProperty("valueExpressionAuthority",
                cursor.valueExpressionAuthority);
        annotateValueRefWitness(effect, active, cursor);

        if (active.engineBacked && cursor.mapExpression != null) {
            List<Integer> matches = nativeRemoveConditionIndices(conditions,
                    start, cursor.mapExpression, cursor.keyKnown
                            ? cursor.keyExpression : null);
            boolean runtimeEntryKeyFallback = false;
            if (matches.isEmpty() && entrySet && cursor.hasCurrent
                    && cursor.entryObservationComplete && cursor.keyKnown
                    && cursor.valueKnown && cursor.keyExpression != null
                    && cursor.valueExpression != null
                    && "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT".equals(
                    cursor.keyExpressionAuthority)) {
                List<Integer> receiverMatches = nativeRemoveConditionIndices(
                        conditions, start, cursor.mapExpression, null);
                if (receiverMatches.size() == 1
                        && nativeRemoveSupportsIntegerEntryKeyRebind(
                        conditions.get(receiverMatches.get(0)),
                        cursor.mapExpression, cursor.keyExpression,
                        cursor.valueExpression)) {
                    matches = receiverMatches;
                    runtimeEntryKeyFallback = true;
                } else if (receiverMatches.size() > 1) {
                    // Preserve ambiguity.  A key representation fallback is
                    // admissible only for one remove on the exact receiver in
                    // the post-call PC suffix.
                    matches = receiverMatches;
                }
            }
            if (matches.size() == 1) {
                int index = matches.get(0);
                JsonObject nativeEffect = conditions.get(index)
                        .getAsJsonObject();
                effect.addProperty("vmJoinStatus", "UNIQUE_MATCH");
                effect.addProperty("vmKeyJoinAuthority",
                        runtimeEntryKeyFallback
                                ? "UNIQUE_HASHMAP_REMOVENODE_RECEIVER_RESULT_"
                                + "HASH_PLUS_RUNTIME_ENTRY_KEY_V1"
                                : "EXACT_NATIVE_REMOVE_MAP_AND_KEY_"
                                + "EXPRESSION_V1");
                effect.addProperty("vmConditionIndex", index);
                effect.add("vmExpression", nativeEffect);
                if (runtimeEntryKeyFallback) {
                    effect.add("nativeKeyExpression",
                            copyJsonTree(nativeRemoveKey(nativeEffect)));
                }
                JsonElement resolvedKey = resolvedIteratorRemoveKey(
                        cursor.keyExpression, nativeEffect);
                if (cursor.keyExpression == null && resolvedKey != null) {
                    cursor.keyExpression = resolvedKey;
                    effect.add("keyExpression", resolvedKey);
                    effect.addProperty("keyBindingAuthority",
                            "UNIQUE_NATIVE_REMOVE_EXPRESSION_EXACT_JOIN");
                }
            } else {
                String status = matches.isEmpty() ? "NO_MATCH" : "AMBIGUOUS";
                effect.addProperty("vmJoinStatus", status);
                unresolved = appendReason(unresolved,
                        status + " native map-remove expression in selected PC suffix");
            }
        } else if (!active.engineBacked) {
            effect.addProperty("vmJoinStatus", "NOT_SYMBOLIC_EXECUTION");
        } else {
            effect.addProperty("vmJoinStatus", "MISSING_MAP_EXPRESSION");
            unresolved = appendReason(unresolved,
                    "map expression unavailable for native effect join");
        }

        int guardIndex = latestGuardMapping(active, method,
                cursor.pathConditionSize, end);
        if (guardIndex >= 0) {
            JsonObject guard = active.branchMappings.get(guardIndex);
            effect.addProperty("guardCandidateMappingIndex", guardIndex);
            effect.addProperty("guardCandidateSiteId",
                    string(guard, "siteId"));
            effect.addProperty("guardCandidateAuthority",
                    "ORDERED_CANDIDATE_REQUIRES_STATIC_DOMINANCE_VALIDATION");
            if (guard.has("condition")) {
                effect.add("guardCandidateCondition",
                        guard.get("condition"));
            }
        }

        if (cursor.mapExpression == null || cursor.keyExpression == null) {
            unresolved = appendReason(unresolved,
                    "map/key symbolic transformer binding is incomplete");
        }
        boolean transformerComplete = cursor.mapExpression != null
                && cursor.keyExpression != null
                && (!active.engineBacked
                || "UNIQUE_MATCH".equals(string(effect, "vmJoinStatus")));
        boolean guardValueBindingComplete = !entrySet
                || cursor.valueExpression != null
                && cursor.element instanceof Map.Entry
                && valueIdentity != 0;
        if (!guardValueBindingComplete) {
            unresolved = appendReason(unresolved,
                    "entry value expression is unavailable for guard provenance");
        }
        effect.addProperty("transformerComplete", transformerComplete);
        effect.addProperty("guardValueBindingComplete",
                guardValueBindingComplete);
        effect.addProperty("valueCaptureComplete",
                cursor.valueExpression != null);
        boolean complete = unresolved.isEmpty() && transformerComplete
                && guardValueBindingComplete;
        effect.addProperty("runtimeProvenanceComplete", complete);
        effect.addProperty("complete", complete);
        if (!complete) {
            effect.addProperty("unresolvedReason", unresolved);
            active.unresolved.add(originSite
                    + ": backed-view heap effect unresolved: " + unresolved);
        }
        active.runtimeHeapEffects.add(effect);
        active.lastPathConditionSize = Math.max(
                active.lastPathConditionSize, end);
        cursor.hasCurrent = false;
    }

    private static void captureIteratorExpressions(ActiveRegion active,
                                                   MapIteratorCursor cursor) {
        cursor.hasCurrent = true;
        if (!active.engineBacked) {
            cursor.mapExpression = concreteExpression(cursor.binding.map);
            cursor.entryExpression = concreteExpression(cursor.element);
            cursor.keyExpressionAuthority =
                    "CONCRETE_REPLAY_RUNTIME_VALUE_AT_ITERATOR_NEXT";
            if (cursor.keyKnown) {
                cursor.keyExpression = concreteExpression(cursor.key);
            }
            if (cursor.valueKnown) {
                cursor.valueExpression = concreteExpression(cursor.value);
                cursor.valueExpressionAuthority =
                        "CONCRETE_REPLAY_RUNTIME_VALUE_AT_ITERATOR_NEXT";
            }
            cursor.pathConditionSize = 0;
            return;
        }
        EngineApi api = engine();
        try {
            cursor.mapExpression = canonicalEngineExpression(
                    api.expression(cursor.binding.map));
        } catch (Throwable throwable) {
            cursor.bindingError = appendReason(cursor.bindingError,
                    "map expression failed: " + rootCause(throwable));
        }
        try {
            cursor.entryExpression = canonicalEngineExpression(
                    api.expression(cursor.element));
        } catch (Throwable throwable) {
            // HashMap.Node/Map.Entry is a concrete provenance wrapper.  The
            // custom JDK does not guarantee that it has a symbolic reference;
            // its activation-local object token remains authoritative.
            cursor.entryExpressionWarning = "entry expression unavailable: "
                    + rootCause(throwable);
        }
        if (cursor.keyKnown) {
            Throwable keyExpressionFailure = null;
            try {
                cursor.keyExpression = canonicalEngineExpression(
                        api.expression(cursor.key));
            } catch (Throwable throwable) {
                keyExpressionFailure = throwable;
            }
            if (completeRuntimeExpression(cursor.keyExpression)) {
                cursor.keyExpressionAuthority =
                        "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT";
            } else {
                JsonElement fallback = immutableEntryKeyExpression(cursor.key);
                if (fallback != null) {
                    cursor.keyExpression = fallback;
                    cursor.keyExpressionAuthority =
                            "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT";
                } else if (keyExpressionFailure != null) {
                    cursor.bindingError = appendReason(cursor.bindingError,
                            "key expression failed: "
                                    + rootCause(keyExpressionFailure));
                }
            }
        }
        if (cursor.valueKnown) {
            try {
                cursor.valueExpression = canonicalEngineExpression(
                        api.expression(cursor.value));
                if (completeRuntimeExpression(cursor.valueExpression)) {
                    cursor.valueExpressionAuthority =
                            "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT";
                }
            } catch (Throwable throwable) {
                // A subsequent field-symbolization hook gets one or more
                // chances to refresh this expression.
                cursor.valueExpressionWarning = "value expression unavailable: "
                        + rootCause(throwable);
            }
        }
        try {
            JsonElement parsed = parseJson(api.pathCondition());
            cursor.pathConditionSize = parsed.isJsonArray()
                    ? parsed.getAsJsonArray().size()
                    : active.lastPathConditionSize;
        } catch (Throwable throwable) {
            cursor.pathConditionSize = active.lastPathConditionSize;
            cursor.bindingError = appendReason(cursor.bindingError,
                    "next PC boundary failed: " + rootCause(throwable));
        }
    }

    private static JsonElement concreteExpression(Object value) {
        JsonObject expression = new JsonObject();
        expression.addProperty("kind", "CONCRETE_RUNTIME_VALUE");
        expression.addProperty("symbolic", false);
        if (value == null) {
            expression.addProperty("valueType", "NULL");
        } else if (value instanceof Number || value instanceof Boolean
                || value instanceof Character || value instanceof String) {
            expression.addProperty("valueType", value.getClass().getName());
            expression.add("value", GSON.toJsonTree(value));
        } else {
            expression.addProperty("valueType", value.getClass().getName());
            expression.addProperty("identity",
                    System.identityHashCode(value));
        }
        return expression;
    }

    /**
     * Produces the same ConstExpr shape consumed by the generic SMT emitter
     * when an immutable Java key is concrete and the custom JDK has no shadow
     * reference for its wrapper object.
     */
    static JsonElement immutableEntryKeyExpression(Object value) {
        if (value == null) {
            return null;
        }
        String javaType;
        String prefix;
        String payload;
        if (value instanceof Boolean) {
            javaType = "java/lang/Boolean";
            prefix = "Z";
            payload = ((Boolean) value) ? "1" : "0";
        } else if (value instanceof Byte) {
            javaType = "java/lang/Byte";
            prefix = "B";
            payload = value.toString();
        } else if (value instanceof Character) {
            javaType = "java/lang/Character";
            prefix = "C";
            payload = Integer.toString((Character) value);
        } else if (value instanceof Short) {
            javaType = "java/lang/Short";
            prefix = "S";
            payload = value.toString();
        } else if (value instanceof Integer) {
            javaType = "java/lang/Integer";
            prefix = "I";
            payload = value.toString();
        } else if (value instanceof Long) {
            javaType = "java/lang/Long";
            prefix = "J";
            payload = value.toString();
        } else if (value instanceof String) {
            javaType = "java/lang/String";
            prefix = "L";
            payload = (String) value;
        } else {
            return null;
        }
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "ConstExpr");
        expression.addProperty("_java_type", javaType);
        expression.addProperty("_exp", "Y_" + prefix + "_" + payload);
        return expression;
    }

    /**
     * Exact, cross-execution selector admitted for producer Map snapshots.
     * Floating point wrappers are deliberately excluded: Java Map equality
     * distinguishes signed zero while decimal normalization can collapse it.
     */
    private static String stableMapProjectionKeySelector(
            JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return "";
        JsonObject object = expression.getAsJsonObject();
        if (!"ConstExpr".equals(jsonString(object, "_type"))) return "";
        String encoded = jsonString(object, "_exp");
        if (!encoded.startsWith("Y_") || encoded.length() < 4
                || encoded.charAt(3) != '_') return "";
        char kind = encoded.charAt(2);
        String type = jsonString(object, "_java_type").replace('.', '/');
        char declared;
        if ("java/lang/Boolean".equals(type)) declared = 'Z';
        else if ("java/lang/Byte".equals(type)) declared = 'B';
        else if ("java/lang/Character".equals(type)) declared = 'C';
        else if ("java/lang/Short".equals(type)) declared = 'S';
        else if ("java/lang/Integer".equals(type)) declared = 'I';
        else if ("java/lang/Long".equals(type)) declared = 'J';
        else if ("java/lang/String".equals(type)) declared = 'L';
        else return "";
        if (kind != declared) return "";
        String payload = encoded.substring(4);
        try {
            if (kind == 'Z') {
                if (!("0".equals(payload) || "1".equals(payload))) {
                    return "";
                }
            } else if (kind != 'L') {
                java.math.BigInteger integer =
                        new java.math.BigInteger(payload);
                if (!integer.toString().equals(payload)) return "";
                if (kind == 'B' && (integer.compareTo(
                        java.math.BigInteger.valueOf(Byte.MIN_VALUE)) < 0
                        || integer.compareTo(java.math.BigInteger.valueOf(
                        Byte.MAX_VALUE)) > 0)) return "";
                if (kind == 'C' && (integer.signum() < 0
                        || integer.compareTo(java.math.BigInteger.valueOf(
                        Character.MAX_VALUE)) > 0)) return "";
                if (kind == 'S' && (integer.compareTo(
                        java.math.BigInteger.valueOf(Short.MIN_VALUE)) < 0
                        || integer.compareTo(java.math.BigInteger.valueOf(
                        Short.MAX_VALUE)) > 0)) return "";
                if (kind == 'I' && (integer.compareTo(
                        java.math.BigInteger.valueOf(Integer.MIN_VALUE)) < 0
                        || integer.compareTo(java.math.BigInteger.valueOf(
                        Integer.MAX_VALUE)) > 0)) return "";
                if (kind == 'J' && (integer.compareTo(
                        java.math.BigInteger.valueOf(Long.MIN_VALUE)) < 0
                        || integer.compareTo(java.math.BigInteger.valueOf(
                        Long.MAX_VALUE)) > 0)) return "";
            }
        } catch (RuntimeException malformed) {
            return "";
        }
        return kind + ":" + payload.length() + ":" + payload;
    }

    private static boolean supportedMapProjectionImplementation(Object map) {
        return map != null && (map.getClass() == HashMap.class
                || map.getClass() == LinkedHashMap.class);
    }

    /**
     * Converts only immutable, concrete entry-key expressions into one
     * representation-independent selector. Symbolic names, object identities
     * and partially parsed values remain incomparable across executions.
     */
    private static String stableImmutableKeySelector(JsonElement expression,
                                                     String authority) {
        if (expression == null || !expression.isJsonObject()
                || !stableKeyAuthority(authority)) {
            return "";
        }
        JsonObject object = expression.getAsJsonObject();
        if ("ConstExpr".equals(jsonString(object, "_type"))) {
            String encoded = jsonString(object, "_exp");
            if (encoded.length() < 4 || !encoded.startsWith("Y_")
                    || encoded.charAt(3) != '_') {
                return "";
            }
            char kind = encoded.charAt(2);
            char declared = immutableKeyKind(jsonString(object,
                    "_java_type"));
            if (declared == 0 || declared != kind) return "";
            return canonicalImmutableKey(kind, encoded.substring(4));
        }
        if (!"CONCRETE_RUNTIME_VALUE".equals(jsonString(object, "kind"))) {
            return "";
        }
        char kind = immutableKeyKind(jsonString(object, "valueType"));
        JsonElement value = object.get("value");
        if (kind == 0 || value == null || value.isJsonNull()
                || !value.isJsonPrimitive()) {
            return "";
        }
        String payload;
        try {
            if (kind == 'C' && value.getAsJsonPrimitive().isString()) {
                String character = value.getAsString();
                if (character.length() != 1) return "";
                payload = Integer.toString(character.charAt(0));
            } else if (kind == 'Z'
                    && value.getAsJsonPrimitive().isBoolean()) {
                payload = value.getAsBoolean() ? "1" : "0";
            } else {
                payload = value.getAsString();
            }
        } catch (RuntimeException malformed) {
            return "";
        }
        return canonicalImmutableKey(kind, payload);
    }

    private static boolean stableKeyAuthority(String authority) {
        return "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT".equals(
                authority)
                || "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT".equals(authority)
                || "CONCRETE_REPLAY_RUNTIME_VALUE_AT_ITERATOR_NEXT".equals(
                authority);
    }

    private static char immutableKeyKind(String type) {
        String value = safe(type).replace('.', '/');
        if ("Z".equals(value) || "java/lang/Boolean".equals(value)) return 'Z';
        if ("B".equals(value) || "java/lang/Byte".equals(value)) return 'B';
        if ("C".equals(value) || "java/lang/Character".equals(value)) return 'C';
        if ("S".equals(value) || "java/lang/Short".equals(value)) return 'S';
        if ("I".equals(value) || "java/lang/Integer".equals(value)) return 'I';
        if ("J".equals(value) || "java/lang/Long".equals(value)) return 'J';
        if ("F".equals(value) || "java/lang/Float".equals(value)) return 'F';
        if ("D".equals(value) || "java/lang/Double".equals(value)) return 'D';
        if ("L".equals(value) || "java/lang/String".equals(value)) return 'L';
        return 0;
    }

    private static String canonicalImmutableKey(char kind, String payload) {
        try {
            String normalized;
            if (kind == 'Z') {
                if ("1".equals(payload) || "true".equalsIgnoreCase(payload)) {
                    normalized = "1";
                } else if ("0".equals(payload)
                        || "false".equalsIgnoreCase(payload)) {
                    normalized = "0";
                } else {
                    return "";
                }
            } else if (kind == 'B' || kind == 'C' || kind == 'S'
                    || kind == 'I' || kind == 'J') {
                normalized = new java.math.BigInteger(payload).toString();
            } else if (kind == 'F' || kind == 'D') {
                normalized = new java.math.BigDecimal(payload)
                        .stripTrailingZeros().toPlainString();
            } else if (kind == 'L') {
                normalized = payload;
            } else {
                return "";
            }
            return kind + ":" + normalized.length() + ":" + normalized;
        } catch (RuntimeException malformed) {
            return "";
        }
    }

    /**
     * {@code System.getSymbolicExpression} returns an API envelope while VM
     * MethodExpression parameters contain the nested expression itself.
     * Canonical effects use that nested node so equality joins are structural
     * rather than string- or project-specific.
     */
    static JsonElement canonicalEngineExpression(String serialized) {
        return engineExpressionCapture(serialized).expression;
    }

    private static EngineExpressionCapture engineExpressionCapture(
            String serialized) {
        JsonElement parsed = parseJson(serialized);
        if (parsed.isJsonObject()) {
            JsonObject envelope = parsed.getAsJsonObject();
            // A VM envelope can legitimately omit expression (for example
            // CONCOLIC_DISABLED and NULL).  Recognize the envelope from its
            // schema fields so it can never be mistaken for a legacy bare
            // expression tree.
            if (envelope.has("expression")
                    || envelope.has("schemaVersion")
                    && envelope.has("kind")
                    && envelope.has("active")
                    && envelope.has("symbolic")) {
                JsonElement expression = envelope.has("expression")
                        ? envelope.get("expression") : null;
                return new EngineExpressionCapture(expression == null
                        || expression.isJsonNull() ? null : expression,
                        integer(envelope, "schemaVersion", -1),
                        bool(envelope, "active", false),
                        jsonString(envelope, "kind"),
                        bool(envelope, "symbolic", false),
                        jsonString(envelope, "expressionAuthority"),
                        jsonString(envelope, "javaTypeDescriptor"));
            }
        }
        return new EngineExpressionCapture(parsed, -1, false, "", false,
                "", "");
    }

    private static final class EngineExpressionCapture {
        private final JsonElement expression;
        private final int schemaVersion;
        private final boolean active;
        private final String kind;
        private final boolean symbolic;
        private final String authority;
        private final String javaTypeDescriptor;

        private EngineExpressionCapture(JsonElement expression,
                                        int schemaVersion, boolean active,
                                        String kind, boolean symbolic,
                                        String authority,
                                        String javaTypeDescriptor) {
            this.expression = expression;
            this.schemaVersion = schemaVersion;
            this.active = active;
            this.kind = safe(kind);
            this.symbolic = symbolic;
            this.authority = safe(authority);
            this.javaTypeDescriptor = safe(javaTypeDescriptor);
        }

        private void addEvidence(JsonObject row) {
            row.addProperty("expressionEnvelopeSchemaVersion",
                    schemaVersion);
            row.addProperty("expressionEnvelopeActive", active);
            row.addProperty("expressionEnvelopeKind", kind);
            row.addProperty("expressionEnvelopeSymbolic", symbolic);
            row.addProperty("expressionEnvelopeAuthority", authority);
            row.addProperty("expressionEnvelopeJavaTypeDescriptor",
                    javaTypeDescriptor);
        }
    }

    /** Returns every exact native remove match in the selected raw suffix. */
    static List<Integer> nativeRemoveConditionIndices(
            JsonArray conditions, int baseline, JsonElement mapExpression,
            JsonElement keyExpression) {
        List<Integer> matches = new ArrayList<>();
        if (conditions == null || mapExpression == null) {
            return matches;
        }
        int first = Math.max(0, Math.min(baseline, conditions.size()));
        for (int index = first; index < conditions.size(); index++) {
            JsonElement candidate = conditions.get(index);
            if (!candidate.isJsonObject()) {
                continue;
            }
            JsonObject object = candidate.getAsJsonObject();
            if (!"MethodExpression".equals(jsonString(object, "_type"))
                    || !jsonString(object, "_name").endsWith(" remove")) {
                continue;
            }
            JsonArray parameters = array(object, "_param_list");
            int keyIndex = parameters.size() == 2 ? 1
                    : parameters.size() == 5 ? 2 : -1;
            if (keyIndex < 0 || parameters.size() == 5
                    && (!"java/util/HashMap remove".equals(
                    jsonString(object, "_name"))
                    || !concreteFalseBoolean(parameters.get(3)))
                    || !mapExpression.equals(parameters.get(0))) {
                continue;
            }
            if (keyExpression != null
                    && !keyExpression.equals(parameters.get(keyIndex))) {
                continue;
            }
            matches.add(index);
        }
        return matches;
    }

    static int findNativeRemoveConditionIndex(
            JsonArray conditions, int baseline, JsonElement mapExpression,
            JsonElement keyExpression) {
        List<Integer> matches = nativeRemoveConditionIndices(conditions,
                baseline, mapExpression, keyExpression);
        return matches.size() == 1 ? matches.get(0) : -1;
    }

    private static JsonElement nativeRemoveKey(JsonObject expression) {
        JsonArray parameters = array(expression, "_param_list");
        int index = parameters.size() == 2 ? 1
                : parameters.size() == 5 ? 2 : -1;
        return index < 0 ? null : parameters.get(index);
    }

    private static boolean opaqueNativeIntegerRemoveKey(
            JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) {
            return false;
        }
        JsonElement key = nativeRemoveKey(expression.getAsJsonObject());
        if (key == null || !key.isJsonObject()) {
            return false;
        }
        JsonObject object = key.getAsJsonObject();
        return "SymbolExpression".equals(jsonString(object, "_type"))
                && "java/lang/Integer".equals(jsonString(object,
                "_java_type"))
                && "P_L'java/lang/Integer'_".equals(jsonString(object,
                "_exp"));
    }

    /**
     * Certifies the narrow Java-8 HashMap.removeNode shape emitted for a
     * normally-returning ENTRY_SET Iterator.remove when the VM exposes the
     * boxed key only as an opaque P_L reference.  The concrete immutable
     * runtime entry key is authoritative only when the native hash and removed
     * value independently identify that same entry.
     */
    static boolean nativeRemoveSupportsIntegerEntryKeyRebind(
            JsonElement expression, JsonElement mapExpression,
            JsonElement runtimeKeyExpression,
            JsonElement runtimeValueExpression) {
        if (expression == null || !expression.isJsonObject()
                || mapExpression == null || runtimeValueExpression == null
                || !opaqueNativeIntegerRemoveKey(expression)) {
            return false;
        }
        JsonObject object = expression.getAsJsonObject();
        JsonArray parameters = array(object, "_param_list");
        Integer key = boxedIntegerConstant(runtimeKeyExpression);
        if (!"MethodExpression".equals(jsonString(object, "_type"))
                || !"java/util/HashMap remove".equals(jsonString(object,
                "_name"))
                || parameters.size() != 5
                || !mapExpression.equals(parameters.get(0))
                || key == null
                || !exactIntConstant(parameters.get(1),
                key ^ key >>> 16)
                || !concreteFalseBoolean(parameters.get(3))
                || !concreteFalseBoolean(parameters.get(4))
                || !object.has("_res_exp")
                || !runtimeValueExpression.equals(object.get("_res_exp"))) {
            return false;
        }
        return true;
    }

    private static Integer boxedIntegerConstant(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject object = expression.getAsJsonObject();
        String encoded = jsonString(object, "_exp");
        if (!"ConstExpr".equals(jsonString(object, "_type"))
                || !"java/lang/Integer".equals(jsonString(object,
                "_java_type")) || !encoded.startsWith("Y_I_")) {
            return null;
        }
        try {
            int value = Integer.parseInt(encoded.substring(4));
            return ("Y_I_" + value).equals(encoded) ? value : null;
        } catch (NumberFormatException malformed) {
            return null;
        }
    }

    private static boolean exactIntConstant(JsonElement expression,
                                            int expected) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        return "ConstExpr".equals(jsonString(object, "_type"))
                && "I".equals(jsonString(object, "_java_type"))
                && ("Y_I_" + expected).equals(jsonString(object, "_exp"));
    }

    static List<Integer> nativeRemoveConditionIndicesWithRuntimeEntryKey(
            JsonArray conditions, int baseline, JsonElement mapExpression,
            JsonElement keyExpression, JsonElement valueExpression) {
        List<Integer> exact = nativeRemoveConditionIndices(conditions,
                baseline, mapExpression, keyExpression);
        if (!exact.isEmpty()) {
            return exact;
        }
        List<Integer> receiver = nativeRemoveConditionIndices(conditions,
                baseline, mapExpression, null);
        return receiver.size() == 1
                && nativeRemoveSupportsIntegerEntryKeyRebind(
                conditions.get(receiver.get(0)), mapExpression,
                keyExpression, valueExpression)
                ? receiver : Collections.<Integer>emptyList();
    }

    static JsonElement resolvedIteratorRemoveKey(
            JsonElement captured, JsonObject nativeExpression) {
        return captured != null ? captured
                : nativeRemoveKey(nativeExpression);
    }

    private static boolean concreteFalseBoolean(JsonElement expression) {
        if (expression == null || expression.isJsonNull()) {
            return false;
        }
        if (expression.isJsonPrimitive()
                && expression.getAsJsonPrimitive().isBoolean()) {
            return !expression.getAsBoolean();
        }
        if (!expression.isJsonObject()) {
            return false;
        }
        JsonObject object = expression.getAsJsonObject();
        return "ConstExpr".equals(jsonString(object, "_type"))
                && "Z".equals(jsonString(object, "_java_type"))
                && "Y_Z_0".equals(jsonString(object, "_exp"));
    }

    private static int latestGuardMapping(ActiveRegion active,
                                          String method,
                                          int baseline, int end) {
        for (int index = active.branchMappings.size() - 1;
             index >= 0; index--) {
            JsonObject mapping = active.branchMappings.get(index);
            if (!safe(method).equals(string(mapping, "method"))) {
                continue;
            }
            int condition = integer(mapping, "rawConditionIndex", -1);
            if (condition >= baseline && condition < end) {
                return index;
            }
        }
        return -1;
    }

    private static String siteId(String method, int unitIndex) {
        return safe(method) + "#u" + unitIndex;
    }

    private static String strongSiteHash(String siteId) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(safe(siteId).getBytes(
                    StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte value : bytes) {
                result.append(String.format("%02x", value & 0xff));
            }
            return result.substring(0, 12);
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException("SHA-256 is unavailable",
                    impossible);
        }
    }

    static String dynamicFieldSymbolForTests(String baseInputSymbol,
                                             String siteId,
                                             int occurrence) {
        return safe(baseInputSymbol) + ".field." + strongSiteHash(siteId)
                + ".occ." + occurrence;
    }

    static boolean dynamicEngineSymbolMatchesForTests(String engine,
                                                      String dynamic) {
        if (engine == null || dynamic == null || dynamic.isEmpty()) {
            return false;
        }
        if (engine.equals(dynamic)) return true;
        if (engine.length() <= 10 || engine.charAt(0) != 'M'
                || engine.charAt(1) != '_'
                || "ZCBSIFJDL".indexOf(engine.charAt(2)) < 0
                || !engine.startsWith("_field_", 3)) {
            return false;
        }
        String payload = engine.substring(10);
        if (payload.equals(dynamic)) return true;
        String boundary = dynamic + "_";
        return payload.startsWith(boundary)
                && legalVmOwnerSuffix(payload.substring(boundary.length()));
    }

    private static boolean legalVmOwnerSuffix(String suffix) {
        return suffix != null && suffix.matches(
                "[A-Za-z_$][A-Za-z0-9_$]*"
                        + "(?:/[A-Za-z_$][A-Za-z0-9_$]*)*");
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
     * Observes the custom-VM expression at one activation-authorized original
     * call argument.  The bytecode hook and this runtime check both match the
     * complete endpoint tuple; a textual method or port match alone is not
     * accepted.
     */
    public static void recordOutputCapture(
            String callerMethod, int unitIndex, String siteId,
            String calleeMethod, int argumentIndex, String outputPort,
            String outputCell, String captureBindingId,
            int requestedOccurrence, Object value, String primitiveValue) {
        ActiveRegion active = activeRegion();
        if (active == null || !active.engineBacked) return;
        OutputCaptureRequest request = active.activation.callArgumentCapture(
                callerMethod, unitIndex, siteId, calleeMethod, argumentIndex,
                outputPort, outputCell, captureBindingId,
                requestedOccurrence);
        if (request == null) return;
        int occurrence = active.nextOutputCaptureOccurrence(
                request.captureBindingId);
        if (request.occurrence != occurrence) return;

        JsonObject row = request.toJson();
        row.addProperty("occurrence", occurrence);
        row.addProperty("captureAuthority",
                "ACTIVE_TOKEN_EXACT_ORIGINAL_CALL_ARGUMENT");
        row.addProperty("concreteValueClass", value == null
                ? "null" : value.getClass().getName());
        row.addProperty("concretePrimitiveValue", safe(primitiveValue));
        EngineApi api = engine();
        boolean paused = false;
        try {
            api.pausePathCondition();
            paused = true;
            EngineExpressionCapture captured = engineExpressionCapture(
                    api.expression(value));
            JsonElement expression = captured.expression;
            if (expression == null || expression.isJsonNull()) {
                throw new IllegalStateException("custom VM returned no "
                        + "expression for captured output value "
                        + row.get("concreteValueClass").getAsString());
            }
            row.add("expression", expression);
            captured.addEvidence(row);
            row.addProperty("expressionCaptured", true);
            JsonArray projectionVerifications =
                    active.verifyMapProjectionOutput(outputPort, outputCell,
                            value,
                            "ACTIVE_TOKEN_EXACT_ORIGINAL_CALL_ARGUMENT");
            if (projectionVerifications.size() > 0) {
                row.add("mapValueElementProjectionVerifications",
                        projectionVerifications);
            }
        } catch (Throwable throwable) {
            row.addProperty("expressionCaptured", false);
            row.addProperty("expressionError", rootCause(throwable));
            active.unresolved.add(request.captureBindingId
                    + ": output expression capture failed: "
                    + rootCause(throwable));
        } finally {
            active.outputCaptures.add(row);
            if (paused) resumePathCondition(active, api);
        }
    }

    /**
     * Observes one activation-authorized scalar method return while its
     * custom-VM expression is still live.  Both the current region token and
     * the complete static capture tuple must match.  A zero-token nested root
     * frame therefore cannot attach its helper return to an enclosing active
     * region.  This hook is deliberately no-throw because it executes on the
     * original method's return path.
     */
    public static void recordMethodReturnOutput(
            long token, String method, int unitIndex, String siteId,
            String captureBindingId, String outputPort, String outputCell,
            int requestedOccurrence, Object value, String primitiveValue) {
        try {
            Long current = CURRENT_TOKEN.get();
            if (token == 0L || current == null
                    || current.longValue() != token) {
                return;
            }
            RootInvocationFrame frame =
                    ROOT_INVOCATION_FRAMES.get().peek();
            if (frame != null && frame.token != token) return;

            ActiveRegion active = ownerRegion(token);
            if (active == null || !active.engineBacked) return;
            OutputCaptureRequest request =
                    active.activation.methodReturnCapture(
                            method, unitIndex, siteId, outputPort, outputCell,
                            captureBindingId, requestedOccurrence);
            if (request == null) return;
            int occurrence = active.nextOutputCaptureOccurrence(
                    request.captureBindingId);
            if (request.occurrence != occurrence) return;

            JsonObject row = request.toJson();
            row.addProperty("occurrence", occurrence);
            row.addProperty("captureAuthority",
                    "ACTIVE_TOKEN_EXACT_METHOD_RETURN_VALUE");
            EngineApi api = engine();
            boolean paused = false;
            try {
                api.pausePathCondition();
                paused = true;
                row.addProperty("concreteValueClass", value == null
                        ? "null" : value.getClass().getName());
                row.addProperty("concretePrimitiveValue",
                        safe(primitiveValue));
                EngineExpressionCapture captured = engineExpressionCapture(
                        api.expression(value));
                JsonElement expression = captured.expression;
                if (expression == null || expression.isJsonNull()) {
                    throw new IllegalStateException("custom VM returned no "
                            + "expression for captured method return value "
                            + row.get("concreteValueClass").getAsString());
                }
                row.add("expression", expression);
                captured.addEvidence(row);
                row.addProperty("expressionCaptured", true);
            } catch (Throwable throwable) {
                try {
                    row.addProperty("expressionCaptured", false);
                    row.addProperty("expressionError",
                            rootCause(throwable));
                    active.unresolved.add(request.captureBindingId
                            + ": method-return expression capture failed: "
                            + rootCause(throwable));
                } catch (Throwable ignored) {
                    // Preserve the original method return even if diagnostic
                    // construction itself fails.
                }
            } finally {
                if (paused) resumePathCondition(active, api);
                try {
                    active.outputCaptures.add(row);
                } catch (Throwable ignored) {
                    // Runtime observation is fail-closed and best-effort.
                }
            }
        } catch (Throwable ignored) {
            // Instrumentation bookkeeping must not replace a normal return.
        }
    }

    /**
     * Observes one activation-authorized instance-field write after the
     * assignment completed.  The explicit token prevents a hook in another
     * MiniDFSCluster thread from attaching to the region owner.  A hook whose
     * complete endpoint tuple is not requested is intentionally a no-op.
     */
    public static void recordFieldAssignmentOutput(
            long token, String method, int unitIndex, String siteId,
            String fieldSignature, String captureBindingId,
            String outputPort, String outputCell, int requestedOccurrence,
            Object fieldOwner, Object assignedValue, String primitiveValue) {
        Long current = CURRENT_TOKEN.get();
        if (token == 0L || current == null || current.longValue() != token) {
            return;
        }
        ActiveRegion active = ownerRegion(token);
        if (active == null || !active.engineBacked) return;
        OutputCaptureRequest request =
                active.activation.fieldAssignmentCapture(
                        method, unitIndex, siteId, fieldSignature,
                        outputPort, outputCell, captureBindingId,
                        requestedOccurrence);
        if (request == null) return;
        int occurrence = active.nextOutputCaptureOccurrence(
                request.captureBindingId);
        if (request.occurrence != occurrence) return;

        JsonObject row = request.toJson();
        row.addProperty("occurrence", occurrence);
        row.addProperty("captureAuthority",
                "ACTIVE_TOKEN_EXACT_POST_INSTANCE_FIELD_ASSIGNMENT");

        EngineApi api = engine();
        boolean paused = false;
        try {
            api.pausePathCondition();
            paused = true;
            // From this point on the hook may branch on symbolic references;
            // keep all identity/reflection/Gson bookkeeping outside the
            // program path condition.
            row.addProperty("fieldOwnerClass", fieldOwner == null
                    ? "null" : fieldOwner.getClass().getName());
            row.addProperty("assignedValueClass", assignedValue == null
                    ? "null" : assignedValue.getClass().getName());
            row.addProperty("concretePrimitiveValue", safe(primitiveValue));
            row.addProperty("fieldOwnerObjectToken",
                    active.objectToken(fieldOwner));
            row.addProperty("fieldOwnerObjectTokenKnown",
                    fieldOwner != null);
            row.addProperty("assignedValueObjectToken",
                    active.objectToken(assignedValue));
            row.addProperty("assignedValueObjectTokenKnown",
                    assignedValue != null);
            row.addProperty("assignedValueWasNull", assignedValue == null);
            row.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            row.addProperty("objectTokenScope",
                    active.activation.activationId);
            JsonArray projectionVerifications =
                    active.verifyMapProjectionOutput(outputPort, outputCell,
                            assignedValue,
                            "ACTIVE_TOKEN_EXACT_POST_INSTANCE_FIELD_ASSIGNMENT");
            if (projectionVerifications.size() > 0) {
                row.add("mapValueElementProjectionVerifications",
                        projectionVerifications);
            }
            ExactFieldObservation observation = observeExactField(
                    fieldOwner, request.fieldSignature);
            row.addProperty("declaredFieldOwnerVerified",
                    observation.ownerVerified);
            row.addProperty("declaredFieldTypeVerified",
                    observation.typeVerified);
            row.addProperty("observedFieldValueAvailable",
                    observation.available);
            row.addProperty("observedFieldValueClass",
                    observation.available && observation.value != null
                            ? observation.value.getClass().getName() : "null");
            row.addProperty("observedFieldValueObjectToken",
                    observation.available
                            ? active.objectToken(observation.value) : 0L);
            row.addProperty("observedFieldValueWasNull",
                    observation.available && observation.value == null);
            boolean primitiveField = observation.fieldType != null
                    && observation.fieldType.isPrimitive();
            boolean identityVerified = observation.available
                    && (primitiveField
                    ? valuesEqual(observation.value, assignedValue)
                    : observation.value == assignedValue);
            row.addProperty("assignmentIdentityMode", primitiveField
                    ? "BOXED_PRIMITIVE_VALUE_EQUALITY"
                    : "REFERENCE_IDENTITY");
            row.addProperty("assignmentIdentityVerified",
                    identityVerified);
            row.addProperty("assignmentIdentityAuthority", primitiveField
                    ? "EXACT_DECLARED_FIELD_REFLECTION_AND_BOXED_VALUE_EQUALITY"
                    : "EXACT_DECLARED_FIELD_REFLECTION_AND_REFERENCE_IDENTITY");
            if (!observation.error.isEmpty()) {
                row.addProperty("assignmentIdentityError",
                        observation.error);
            }
            if (!identityVerified) {
                active.unresolved.add(request.captureBindingId
                        + ": post-assignment field identity verification "
                        + "failed" + (observation.error.isEmpty() ? ""
                        : ": " + observation.error));
            }
            EngineExpressionCapture captured = engineExpressionCapture(
                    api.expression(assignedValue));
            JsonElement expression = captured.expression;
            if (expression == null || expression.isJsonNull()) {
                throw new IllegalStateException("custom VM returned no "
                        + "expression for captured field assignment value "
                        + row.get("assignedValueClass").getAsString());
            }
            row.add("expression", expression);
            captured.addEvidence(row);
            row.addProperty("expressionCaptured", true);
        } catch (Throwable throwable) {
            row.addProperty("expressionCaptured", false);
            row.addProperty("expressionError", rootCause(throwable));
            active.unresolved.add(request.captureBindingId
                    + ": field-assignment expression capture failed: "
                    + rootCause(throwable));
        } finally {
            active.outputCaptures.add(row);
            if (paused) resumePathCondition(active, api);
        }
    }

    /** Normal region exit. */
    public static void exitRegion(long token, Object returnValue,
                                  String primitiveValue) {
        finish(token, "NORMAL", "", returnValue, primitiveValue);
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

    /** Normal exit resolved from the current concolic thread. */
    public static void exitActiveRegion(Object returnValue,
                                        String primitiveValue) {
        Long token = CURRENT_TOKEN.get();
        if (token != null) {
            exitRegion(token, returnValue, primitiveValue);
        }
    }

    /** Exceptional region exit. */
    public static void throwRegion(long token, Throwable throwable) {
        finish(token, "THROW",
                throwable == null ? "" : throwable.getClass().getName(),
                throwable, "");
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

    /** Exceptional exit resolved from the current concolic thread. */
    public static void throwActiveRegion(Throwable throwable) {
        Long token = CURRENT_TOKEN.get();
        if (token != null) {
            throwRegion(token, throwable);
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

    static int regionFrameDepthForTests() {
        return ROOT_INVOCATION_FRAMES.get().size();
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
        if (!active.engineBacked) return 0L;
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
        if (!active.engineBacked) {
            recordConcreteBranch(active, method, unitIndex, expression,
                    observedOutcome);
            return observedOutcome;
        }
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
            ForcedBranch force = active.activation.force(prepared.siteId,
                    prepared.occurrence);
            boolean effectiveOutcome = force == null
                    ? observedOutcome : force.desiredOutcome;
            recordBranchPaused(active, api, method, unitIndex, expression,
                    prepared.occurrence, observedOutcome, effectiveOutcome,
                    force != null, vmEventId);
            return effectiveOutcome;
        } catch (Throwable throwable) {
            active.addUnresolvedOnce("branch/PC exact-event observation "
                    + "failed: " + rootCause(throwable));
            return observedOutcome;
        } finally {
            if (paused) resumePathCondition(active, api);
        }
    }

    private static void recordConcreteBranch(
            ActiveRegion active, String method, int unitIndex,
            String expression, boolean observedOutcome) {
        String siteId = safe(method) + "#u" + unitIndex;
        int occurrence = active.nextBranchOccurrence(siteId);
        recordConcreteBranch(active, method, unitIndex, expression,
                observedOutcome, occurrence);
    }

    private static void recordConcreteBranch(
            ActiveRegion active, String method, int unitIndex,
            String expression, boolean observedOutcome, int occurrence) {
        String siteId = safe(method) + "#u" + unitIndex;
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", siteId);
        mapping.addProperty("method", safe(method));
        mapping.addProperty("unitIndex", unitIndex);
        mapping.addProperty("expression", safe(expression));
        mapping.addProperty("occurrence", occurrence);
        mapping.addProperty("outcome", observedOutcome);
        mapping.addProperty("observedOutcome", observedOutcome);
        mapping.addProperty("effectiveOutcome", observedOutcome);
        mapping.addProperty("overrideApplied", false);
        mapping.addProperty("overrideMode", "NONE");
        mapping.addProperty("pathConditionSize", 0);
        mapping.addProperty("rawPathConditionSize", 0);
        mapping.addProperty("pathConditionBaseline", 0);
        mapping.addProperty("rawPathConditionBaseline", 0);
        mapping.addProperty("pathConditionsAdded", 0);
        mapping.addProperty("rawPathConditionsAdded", 0);
        mapping.addProperty("targetMethodConditionsAdded", 0);
        mapping.addProperty("branchConditionCandidateCount", 0);
        mapping.addProperty("conditionIndex", -1);
        mapping.addProperty("rawConditionIndex", -1);
        mapping.addProperty("mappingPolicy",
                "CONCRETE_OBSERVATION_WITHOUT_SYMBOLIC_PC");
        mapping.addProperty("policy", active.activation.policy(siteId));
        ScheduledTarget scheduledTarget = active.activation.target(
                siteId, occurrence);
        mapping.addProperty("scheduledTarget", scheduledTarget != null);
        if (scheduledTarget != null) {
            boolean matched = scheduledTarget.desiredOutcome
                    == observedOutcome;
            mapping.addProperty("scheduledDesiredOutcome",
                    scheduledTarget.desiredOutcome);
            mapping.addProperty("scheduledOutcomeMatched", matched);
            mapping.addProperty("conditionAuthority",
                    "UPSTREAM_ONLY_CONCRETE_PROPAGATION");
            mapping.addProperty("replayValidation", matched
                    && active.activation.observationOnlyReplay
                    ? "PASS" : "FAIL");
            mapping.addProperty("mappingNote",
                    "branch was observed without symbolic execution, "
                            + "materialization, or override at the target");
        }
        active.branchMappings.add(mapping);
    }

    private static void recordBranchPaused(
            ActiveRegion active, EngineApi api, String method, int unitIndex,
            String expression, int occurrence, boolean observedOutcome,
            boolean effectiveOutcome, boolean overrideApplied,
            long vmEventId) throws Exception {
        String siteId = safe(method) + "#u" + unitIndex;
        JsonElement parsed = parseJson(api.pathCondition());
        JsonArray conditions = parsed.isJsonArray()
                ? parsed.getAsJsonArray() : new JsonArray();
        int baseline = active.lastPathConditionSize;
        int added = Math.max(0, conditions.size() - baseline);
        VmBranchEventAttestation vmAttestation = attestVmBranchEvent(api,
                active, siteId, expression, observedOutcome, vmEventId,
                occurrence, conditions, baseline);
        int conditionCandidates = vmAttestation.valid
                && vmAttestation.conditionIndex >= 0 ? 1 : 0;
        int conditionIndex = vmAttestation.valid
                ? vmAttestation.conditionIndex : -1;
        int targetMethodConditions = conditionCandidates;
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", siteId);
        mapping.addProperty("method", safe(method));
        mapping.addProperty("unitIndex", unitIndex);
        mapping.addProperty("expression", safe(expression));
        mapping.addProperty("occurrence", occurrence);
        mapping.addProperty("outcome", observedOutcome);
        mapping.addProperty("observedOutcome", observedOutcome);
        mapping.addProperty("effectiveOutcome", effectiveOutcome);
        mapping.addProperty("overrideApplied", overrideApplied);
        mapping.addProperty("overrideMode", overrideApplied
                ? "SOOT_BRANCH_OVERRIDE_VALIDATION" : "NONE");
        mapping.addProperty("pathConditionSize", conditions.size());
        mapping.addProperty("rawPathConditionSize", conditions.size());
        mapping.addProperty("pathConditionBaseline", baseline);
        mapping.addProperty("rawPathConditionBaseline", baseline);
        mapping.addProperty("pathConditionsAdded", added);
        mapping.addProperty("rawPathConditionsAdded", added);
        mapping.addProperty("targetMethodConditionsAdded",
                targetMethodConditions);
        mapping.addProperty("branchConditionCandidateCount",
                conditionCandidates);
        mapping.addProperty("conditionIndex", conditionIndex);
        mapping.addProperty("rawConditionIndex", conditionIndex);
        mapping.addProperty("mappingPolicy",
                "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_PC_INDEX");
        mapping.addProperty("vmBranchEventExpected", true);
        mapping.addProperty("vmBranchEventId", vmEventId);
        mapping.addProperty("vmOccurrence", occurrence);
        mapping.addProperty("vmBranchEventValidated", vmAttestation.valid);
        mapping.addProperty("vmBranchEventAuthority",
                vmAttestation.authority);
        if (vmAttestation.event != null) {
            mapping.addProperty("vmThreadContextId",
                    longInteger(vmAttestation.event, "contextId", 0L));
            mapping.addProperty("vmOwnerJavaThreadId",
                    longInteger(vmAttestation.event,
                            "ownerJavaThreadId", 0L));
            mapping.addProperty("vmOwnerOsThreadId",
                    longInteger(vmAttestation.event,
                            "ownerOsThreadId", 0L));
            mapping.addProperty("vmOpcode",
                    integer(vmAttestation.event, "opcode", -1));
            mapping.addProperty("vmCodePosition",
                    string(vmAttestation.event, "codePosition"));
            mapping.add("vmConditionIndices",
                    array(vmAttestation.event, "conditionIndices"));
        }
        mapping.addProperty("policy", active.activation.policy(siteId));
        ScheduledTarget scheduledTarget = active.activation.target(
                siteId, occurrence);
        boolean replayValidated = scheduledTarget != null
                && scheduledTarget.desiredOutcome == observedOutcome
                && active.hasAppliedSolverReplay();
        mapping.addProperty("scheduledTarget", scheduledTarget != null);
        if (scheduledTarget != null) {
            mapping.addProperty("scheduledDesiredOutcome",
                    scheduledTarget.desiredOutcome);
            mapping.addProperty("scheduledOutcomeMatched",
                    scheduledTarget.desiredOutcome == observedOutcome);
        }
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
            mapping.addProperty("rawConditionOperator", rawOperator);
            mapping.addProperty("semanticConditionOperator",
                    semanticOperator);
            if (!rawOperator.equals(semanticOperator)) {
                mapping.addProperty("conditionNormalization",
                        "JVM_CMP_TRICHOTOMY_TO_JIMPLE_BRANCH_PREDICATE");
            }
            if (vmAttestation.valid) {
                mapping.addProperty("conditionAuthority",
                        "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_PC_INDEX");
            }
        } else if (vmAttestation.valid) {
            mapping.addProperty("conditionAuthority",
                    "VM_THREAD_CONTEXT_EXACT_CONCRETE_BRANCH_EVENT");
        }
        boolean pathConditionShrank = conditions.size() < baseline;
        if (pathConditionShrank) {
            mapping.addProperty("mappingWarning",
                    "path condition shrank between branch hooks");
        } else if (!vmAttestation.valid) {
            mapping.addProperty("mappingWarning",
                    "VM exact branch event rejected: "
                            + vmAttestation.error);
            mapping.addProperty("conditionAuthority",
                    "UNRESOLVED_VM_EXACT_BRANCH_EVENT");
        } else if (conditionIndex < 0 && conditionCandidates == 0
                && replayValidated) {
            mapping.addProperty("conditionAuthority",
                    "SCHEDULED_NEGATED_CONDITION_CONCRETE_REPLAY");
            mapping.addProperty("replayValidation", "PASS");
            mapping.addProperty("mappingNote",
                    "modeled reference became concrete null; no new VM PC element");
        } else if (conditionIndex < 0) {
            mapping.addProperty("mappingWarning",
                    "no newly added target-method condition matches selected branch");
        }
        active.lastPathConditionSize = conditions.size();
        active.branchMappings.add(mapping);
    }

    private static VmBranchEventAttestation attestVmBranchEvent(
            EngineApi api, ActiveRegion active, String siteId,
            String expression, boolean observedOutcome, long eventId,
            int occurrence, JsonArray conditions, int baseline) {
        if (eventId <= 0L) {
            return VmBranchEventAttestation.invalid(null, "",
                    "marker returned a non-positive event id");
        }
        final JsonElement parsed;
        try {
            parsed = parseJson(api.branchEvents());
        } catch (Throwable throwable) {
            return VmBranchEventAttestation.invalid(null, "",
                    "event stream is not readable: " + rootCause(throwable));
        }
        if (!parsed.isJsonObject()) {
            return VmBranchEventAttestation.invalid(null, "",
                    "event stream is not a JSON object");
        }
        JsonObject envelope = parsed.getAsJsonObject();
        if (integer(envelope, "schemaVersion", -1) != 1
                || !"CONCOLIC_THREAD_BRANCH_EVENTS".equals(
                string(envelope, "kind"))
                || !bool(envelope, "active", false)) {
            return VmBranchEventAttestation.invalid(null, "",
                    "unexpected or inactive event stream");
        }
        long envelopeContext = longInteger(envelope, "contextId", 0L);
        long envelopeOwner = longInteger(envelope,
                "ownerJavaThreadId", 0L);
        long envelopeOsOwner = longInteger(envelope,
                "ownerOsThreadId", 0L);
        if (envelopeContext <= 0L) {
            return VmBranchEventAttestation.invalid(null, "",
                    "missing positive VM thread context id");
        }
        if (envelopeOwner != active.thread.getId()) {
            return VmBranchEventAttestation.invalid(null, "",
                    "event stream belongs to Java thread " + envelopeOwner
                            + " instead of " + active.thread.getId());
        }
        if (!safe(active.activation.regionId).equals(
                string(envelope, "regionId"))
                || !safe(active.activation.activationId).equals(
                string(envelope, "activationId"))) {
            return VmBranchEventAttestation.invalid(null, "",
                    "event stream region/activation does not match owner");
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
            return VmBranchEventAttestation.invalid(selected, "",
                    "event id " + eventId + " matched " + matches
                            + " records");
        }
        String authority = string(selected, "authority");
        if (!"VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1".equals(authority)) {
            return VmBranchEventAttestation.invalid(selected, authority,
                    "unsupported event authority " + authority);
        }
        if (longInteger(selected, "contextId", 0L) != envelopeContext
                || longInteger(selected, "ownerJavaThreadId", 0L)
                != envelopeOwner
                || longInteger(selected, "ownerOsThreadId", 0L)
                != envelopeOsOwner) {
            return VmBranchEventAttestation.invalid(selected, authority,
                    "event owner/context differs from its thread envelope");
        }
        if (!safe(active.activation.regionId).equals(
                string(selected, "regionId"))
                || !safe(active.activation.activationId).equals(
                string(selected, "activationId"))) {
            return VmBranchEventAttestation.invalid(selected, authority,
                    "event region/activation differs from its owner");
        }
        if (!safe(siteId).equals(string(selected, "siteId"))
                || integer(selected, "occurrence", -1) != occurrence) {
            return VmBranchEventAttestation.invalid(selected, authority,
                    "event site/occurrence does not match prepared branch");
        }
        if (bool(selected, "outcome", !observedOutcome)
                != observedOutcome) {
            return VmBranchEventAttestation.invalid(selected, authority,
                    "event outcome differs from observed branch");
        }
        JsonArray indices = array(selected, "conditionIndices");
        if (integer(selected, "conditionCount", -1) != indices.size()) {
            return VmBranchEventAttestation.invalid(selected, authority,
                    "event condition count differs from its index vector");
        }
        if (indices.size() > 1) {
            return VmBranchEventAttestation.invalid(selected, authority,
                    "instrumented IfStmt emitted multiple condition indices");
        }
        int conditionIndex = -1;
        if (indices.size() == 1) {
            try {
                conditionIndex = indices.get(0).getAsInt();
            } catch (RuntimeException exception) {
                return VmBranchEventAttestation.invalid(selected, authority,
                        "condition index is not an integer");
            }
            if (conditionIndex < baseline
                    || conditionIndex >= conditions.size()) {
                return VmBranchEventAttestation.invalid(selected, authority,
                        "condition index " + conditionIndex
                                + " is outside new path-condition suffix ["
                                + baseline + "," + conditions.size() + ")");
            }
            if (!branchConditionMatches(expression, observedOutcome,
                    conditions.get(conditionIndex))) {
                return VmBranchEventAttestation.invalid(selected, authority,
                        "selected VM condition does not match the original "
                                + "branch predicate");
            }
        }
        return VmBranchEventAttestation.valid(selected, authority,
                conditionIndex);
    }

    private static void finish(long token, String exitKind, String exceptionType,
                               Object output, String primitiveValue) {
        ActiveRegion active = ownerRegion(token);
        if (active == null || !active.finished.compareAndSet(false, true)
                || !ACTIVE.remove(token, active)) {
            return;
        }
        // Exact call-site traps normally close every accessor scope first.
        // Region cleanup is the final fail-closed boundary for malformed or
        // externally interrupted control flow.
        clearAccessorCallContexts(token);
        if (!active.engineBacked) {
            finishConcreteReplay(active, token, exitKind, exceptionType,
                    output, primitiveValue);
            return;
        }
        JsonObject result = new JsonObject();
        EngineApi api = engine();
        boolean engineFinished = false;
        try {
            // Everything below is observational bookkeeping.  Pause PC
            // recording before any null checks, Gson work, or string building
            // can reuse a symbolic value and manufacture a false condition.
            api.pausePathCondition();
            active.verifyRootMapProjectionOutputs(output, exitKind);
            result.addProperty("event", "CONCOLIC_REGION_RESULT");
            result.addProperty("schemaVersion", 1);
            result.addProperty("executionMode", "SYMBOLIC_CONCOLIC");
            result.addProperty("pathConditionIsolationPolicy",
                    "GRAPH_CHECKER_RUNTIME_HOOKS_PAUSED_V1");
            result.addProperty("activationId", active.activation.activationId);
            result.addProperty("regionId", active.activation.regionId);
            result.addProperty("rootMethod", active.activation.rootMethod);
            result.addProperty("test", active.activation.test);
            result.addProperty("invocationOrdinal",
                    active.activation.invocationOrdinal);
            result.addProperty("runtimeThread", active.thread.getName());
            result.addProperty("runtimeThreadId", active.thread.getId());
            result.addProperty("exitKind", exitKind);
            result.addProperty("exceptionType", safe(exceptionType));
            if (output instanceof Throwable) {
                result.add("exceptionChain", exceptionChain((Throwable) output));
            }
            result.addProperty("concretePrimitiveOutput", safe(primitiveValue));
            result.addProperty("durationNanos",
                    System.nanoTime() - active.startNanos);
            if (active.pendingArrayFieldMaterialization != null) {
                active.addUnresolvedOnce(
                        active.pendingArrayFieldMaterialization.siteId
                                + ": ARRAY_VALUE_PREPARED_NOT_CONSUMED");
                active.pendingArrayFieldMaterialization = null;
            }
            active.validateContainerElementFieldCoverage();
            result.add("unresolvedInputs", GSON.toJsonTree(active.unresolved));
            result.add("symbolizedInputs", GSON.toJsonTree(active.symbolized));
            result.add("branchMappings", GSON.toJsonTree(active.branchMappings));
            result.add("runtimeHeapEffects",
                    GSON.toJsonTree(active.runtimeHeapEffects));
            result.add("runtimeHeapObservations",
                    active.runtimeHeapObservationsJson());
            result.add("replayMaterializationsApplied",
                    GSON.toJsonTree(active.replayMaterializationsApplied));
            result.add("modelAssignmentsApplied",
                    GSON.toJsonTree(active.modelAssignmentsApplied));
            result.add("fieldObservations",
                    GSON.toJsonTree(active.fieldObservations));
            result.add("dynamicFieldBindings",
                    active.dynamicFieldBindingsJson());
            result.add("mapValueElementProjectionObservations",
                    GSON.toJsonTree(active.mapProjectionObservations));
            result.add("engineArrayInputBindings",
                    active.engineArrayInputBindingsJson());
            result.add("outputCaptures",
                    GSON.toJsonTree(active.outputCaptures));
            JsonArray finalFields = new JsonArray();
            for (FieldObservationTarget target
                    : active.fieldTargets.values()) {
                finalFields.add(fieldObservation(active, target.symbol,
                        target.owner, target.path, "AT_REGION_EXIT",
                        target.binding));
            }
            result.add("finalFieldObservations", finalFields);
            result.addProperty("modelAssignmentCount",
                    active.activation.modelAssignments.size());
            result.addProperty("modelAssignmentAppliedCount",
                    active.modelAssignmentsApplied.size());
            result.addProperty("allModelAssignmentsApplied",
                    active.activation.modelAssignments.size()
                            == active.modelAssignmentsApplied.size());
            result.addProperty("branchOverrideUsed",
                    branchOverrideUsed(active.branchMappings));
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
                api.forceEnd();
            }
            Long current = CURRENT_TOKEN.get();
            if (current != null && current == token) {
                CURRENT_TOKEN.remove();
            }
            releaseSymbolicEngine();
        }
        // If isolation failed before metadata construction, add the minimum
        // identity only after forceEnd has removed the symbolic VM context.
        if (!result.has("event")) {
            result.addProperty("event", "CONCOLIC_REGION_RESULT");
            result.addProperty("schemaVersion", 1);
            result.addProperty("activationId", active.activation.activationId);
            result.addProperty("regionId", active.activation.regionId);
            result.addProperty("rootMethod", active.activation.rootMethod);
            result.addProperty("exitKind", exitKind);
            result.addProperty("exceptionType", safe(exceptionType));
        }
        if (!result.has("runtimeHeapObservations")) {
            result.add("runtimeHeapObservations",
                    active.runtimeHeapObservationsJson());
        }
        appendResult(result);
    }

    private static void finishConcreteReplay(
            ActiveRegion active, long token, String exitKind,
            String exceptionType, Object output, String primitiveValue) {
        JsonObject result = new JsonObject();
        try {
            active.verifyRootMapProjectionOutputs(output, exitKind);
            result.addProperty("event", "CONCOLIC_REGION_RESULT");
            result.addProperty("schemaVersion", 1);
            result.addProperty("executionMode", "CONCRETE_REPLAY_ONLY");
            result.addProperty("pathConditionIsolationPolicy",
                    "CONCRETE_REPLAY_NO_SYMBOLIC_ENGINE_V1");
            result.addProperty("activationId",
                    active.activation.activationId);
            result.addProperty("regionId", active.activation.regionId);
            result.addProperty("rootMethod", active.activation.rootMethod);
            result.addProperty("test", active.activation.test);
            result.addProperty("invocationOrdinal",
                    active.activation.invocationOrdinal);
            result.addProperty("runtimeThread", active.thread.getName());
            result.addProperty("runtimeThreadId", active.thread.getId());
            result.addProperty("exitKind", exitKind);
            result.addProperty("exceptionType", safe(exceptionType));
            if (output instanceof Throwable) {
                result.add("exceptionChain",
                        exceptionChain((Throwable) output));
            }
            result.addProperty("concretePrimitiveOutput",
                    safe(primitiveValue));
            result.addProperty("durationNanos",
                    System.nanoTime() - active.startNanos);
            if (active.pendingArrayFieldMaterialization != null) {
                active.addUnresolvedOnce(
                        active.pendingArrayFieldMaterialization.siteId
                                + ": ARRAY_VALUE_PREPARED_NOT_CONSUMED");
                active.pendingArrayFieldMaterialization = null;
            }
            active.validateContainerElementFieldCoverage();
            result.add("unresolvedInputs",
                    GSON.toJsonTree(active.unresolved));
            result.add("symbolizedInputs", new JsonArray());
            result.add("branchMappings",
                    GSON.toJsonTree(active.branchMappings));
            result.add("runtimeHeapEffects",
                    GSON.toJsonTree(active.runtimeHeapEffects));
            result.add("runtimeHeapObservations",
                    active.runtimeHeapObservationsJson());
            result.add("replayMaterializationsApplied",
                    GSON.toJsonTree(active.replayMaterializationsApplied));
            result.add("modelAssignmentsApplied",
                    GSON.toJsonTree(active.modelAssignmentsApplied));
            result.add("fieldObservations",
                    GSON.toJsonTree(active.fieldObservations));
            result.add("dynamicFieldBindings",
                    active.dynamicFieldBindingsJson());
            result.add("mapValueElementProjectionObservations",
                    GSON.toJsonTree(active.mapProjectionObservations));
            result.add("engineArrayInputBindings",
                    active.engineArrayInputBindingsJson());
            result.add("outputCaptures",
                    GSON.toJsonTree(active.outputCaptures));
            JsonArray finalFields = new JsonArray();
            for (FieldObservationTarget target
                    : active.fieldTargets.values()) {
                finalFields.add(fieldObservation(active, target.symbol,
                        target.owner, target.path, "AT_REGION_EXIT",
                        target.binding));
            }
            result.add("finalFieldObservations", finalFields);
            result.addProperty("modelAssignmentCount",
                    active.activation.modelAssignments.size());
            result.addProperty("modelAssignmentAppliedCount",
                    active.modelAssignmentsApplied.size());
            result.addProperty("allModelAssignmentsApplied",
                    active.activation.modelAssignments.size()
                            == active.modelAssignmentsApplied.size());
            result.addProperty("branchOverrideUsed", false);
            JsonObject summary = new JsonObject();
            summary.addProperty("schemaVersion", 1);
            summary.addProperty("engine", "CONCRETE_REPLAY_ONLY");
            summary.addProperty("active", false);
            summary.addProperty("regionId", active.activation.regionId);
            summary.addProperty("activationId",
                    active.activation.activationId);
            summary.addProperty("pathConditionRecordingPaused", false);
            summary.addProperty("pathConditionPauseDepth", 0);
            summary.add("pathCondition", new JsonArray());
            result.add("engineSummary", summary);
        } catch (Throwable throwable) {
            result.addProperty("engineSummaryError", rootCause(throwable));
        } finally {
            Long current = CURRENT_TOKEN.get();
            if (current != null && current == token) {
                CURRENT_TOKEN.remove();
            }
            releaseConcreteReplay();
        }
        if (!result.has("event")) {
            result.addProperty("event", "CONCOLIC_REGION_RESULT");
            result.addProperty("schemaVersion", 1);
            result.addProperty("executionMode", "CONCRETE_REPLAY_ONLY");
            result.addProperty("activationId",
                    active.activation.activationId);
            result.addProperty("regionId", active.activation.regionId);
            result.addProperty("rootMethod", active.activation.rootMethod);
            result.addProperty("exitKind", exitKind);
            result.addProperty("exceptionType", safe(exceptionType));
        }
        if (!result.has("runtimeHeapObservations")) {
            result.add("runtimeHeapObservations",
                    active.runtimeHeapObservationsJson());
        }
        appendResult(result);
    }

    private static boolean branchOverrideUsed(List<JsonObject> mappings) {
        for (JsonObject mapping : mappings) {
            if (bool(mapping, "overrideApplied", false)) return true;
        }
        return false;
    }

    private static void symbolizeReceiverFields(ActiveRegion active, EngineApi api) {
        for (SymbolizeAction action : active.activation.symbolize) {
            // Nested/shared heap fields are materialized on their real owner at
            // the field-access hook. Looking them up on an unrelated region
            // root is incorrect and creates unresolved heap ports.
            if (!"RECEIVER_FIELD".equals(action.location)) {
                continue;
            }
            String fieldName = runtimeFieldName(action.field, action.cell);
            Object value = readField(active.receiver, fieldName);
            if (value == MissingValue.INSTANCE) {
                active.unresolved.add(action.symbol + ": field not found: " + fieldName);
            } else if (value == null) {
                active.unresolved.add(action.symbol + ": field is null: " + fieldName);
            } else {
                active.observeMapProjectionInput(action, value,
                        "RECEIVER_FIELD");
                active.observeContainerInput(action, value,
                        "RECEIVER_FIELD");
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
            Object preSymbolizationValue = readField(owner, field);
            DeclaredArrayInputType declaredType = action
                    .exactLeafArrayType(owner, field, exactFieldPath);
            boolean liveArray = preSymbolizationValue != null
                    && preSymbolizationValue != MissingValue.INSTANCE
                    && preSymbolizationValue.getClass().isArray();
            boolean declaredArray = declaredType.complete()
                    || action.declaresArrayInput(exactFieldPath);
            if (liveArray || declaredArray) {
                long symbolizationToken = liveArray ? active.objectToken(
                        preSymbolizationValue) : 0L;
                if (liveArray) {
                    api.symbolize(preSymbolizationValue, action.symbol);
                    active.symbolized.add(action.symbol);
                }
                Object postSymbolizationValue = readField(owner, field);
                active.captureEngineArrayInputBinding(action,
                        preSymbolizationValue, postSymbolizationValue,
                        symbolizationToken, declaredType,
                        safe(action.location) + ":" + safe(symbolicPath),
                        api);
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
                                            List<String> path,
                                            String location) {
        ModelAssignment assignment = active.assignment(action, path);
        if (assignment == null || path == null || path.isEmpty()) return;
        Object owner = resolveFieldPathLeafOwner(root, path);
        if (owner == null || owner == MissingValue.INSTANCE) {
            active.unresolved.add(action.symbol + "." + joinFieldPath(path)
                    + ": solver-model field owner is unavailable");
            return;
        }
        applyFieldModel(active, action, owner,
                path.get(path.size() - 1), path, location);
    }

    private static void applyFieldModel(ActiveRegion active,
                                        SymbolizeAction action,
                                        Object owner, String field,
                                        List<String> path,
                                        String location) {
        ModelAssignment assignment = active.assignment(action, path);
        if (assignment == null) return;
        if (!writeModeledField(owner, field, assignment)) {
            active.unresolved.add(action.symbol + "." + joinFieldPath(path)
                    + ": solver model could not be written to real field");
            return;
        }
        active.recordModelAssignment(assignment, location, path,
                readField(owner, field));
    }

    private static Object materializePrimitiveValue(
            ActiveRegion active, SymbolizeAction action, Object concrete,
            String location, List<String> path) {
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
                active.recordModelAssignment(assignment, location, path,
                        modeled);
            }
        }
        Object fresh = freshPrimitiveBox(modeled);
        if (!active.engineBacked) {
            return fresh;
        }
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
                if (assignment.isClearOperation()) {
                    Object current = field.get(owner);
                    if (current instanceof Map) {
                        ((Map<?, ?>) current).clear();
                        return true;
                    }
                    if (current instanceof Collection) {
                        ((Collection<?>) current).clear();
                        return true;
                    }
                    return false;
                }
                if (assignment.isDetachArrayElementsOperation()) {
                    Object current = field.get(owner);
                    return detachArrayElements(current);
                }
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

    /** Writes only the field named by the complete declaring-owner signature. */
    private static boolean writeModeledExactField(
            Object owner, String fieldSignature,
            ModelAssignment assignment) {
        Field field = exactDeclaredInstanceField(owner, fieldSignature);
        if (field == null) return false;
        try {
            if (assignment.isClearOperation()) {
                Object current = field.get(owner);
                if (current instanceof Map) {
                    ((Map<?, ?>) current).clear();
                    return true;
                }
                if (current instanceof Collection) {
                    ((Collection<?>) current).clear();
                    return true;
                }
                return false;
            }
            if (assignment.isDetachArrayElementsOperation()) {
                return detachArrayElements(field.get(owner));
            }
            Object value = coerceModelValue(assignment.valueType,
                    assignment.value, field.getType());
            if (value == UnsupportedReplayValue.INSTANCE) return false;
            field.set(owner, value);
            return true;
        } catch (Throwable ignored) {
            return false;
        }
    }

    /** Resolves no subclass-first fallback: owner, type and name are exact. */
    private static Field exactDeclaredInstanceField(
            Object owner, String fieldSignature) {
        String[] declared = declaredField(fieldSignature);
        if (owner == null || declared == null) return null;
        Class<?> declaringClass = owner.getClass();
        while (declaringClass != null
                && !declared[0].equals(declaringClass.getName())) {
            declaringClass = declaringClass.getSuperclass();
        }
        if (declaringClass == null) return null;
        try {
            Field field = declaringClass.getDeclaredField(declared[2]);
            if (Modifier.isStatic(field.getModifiers())
                    || !javaTypeDescriptor(declared[1]).equals(
                    reflectionDescriptor(field.getType()))) {
                return null;
            }
            if (!field.isAccessible()) field.setAccessible(true);
            return field;
        } catch (Throwable ignored) {
            return null;
        }
    }

    private static boolean detachArrayElements(Object array) {
        if (array == null || !array.getClass().isArray()
                || array.getClass().getComponentType().isPrimitive()) {
            return false;
        }
        int length = Array.getLength(array);
        Object[] copies = new Object[length];
        for (int index = 0; index < length; index++) {
            Object value = Array.get(array, index);
            if (value == null) {
                copies[index] = null;
                continue;
            }
            Object copy = shallowCopy(value);
            if (copy == MissingValue.INSTANCE) return false;
            copies[index] = copy;
        }
        try {
            for (int index = 0; index < length; index++) {
                Array.set(array, index, copies[index]);
            }
            return true;
        } catch (RuntimeException ignored) {
            return false;
        }
    }

    private static Object shallowCopy(Object source) {
        try {
            Constructor<?> constructor = source.getClass()
                    .getDeclaredConstructor();
            if (!constructor.isAccessible()) constructor.setAccessible(true);
            Object copy = constructor.newInstance();
            Class<?> type = source.getClass();
            while (type != null) {
                for (Field field : type.getDeclaredFields()) {
                    if (Modifier.isStatic(field.getModifiers())) continue;
                    if (!field.isAccessible()) field.setAccessible(true);
                    field.set(copy, field.get(source));
                }
                type = type.getSuperclass();
            }
            return copy;
        } catch (Throwable ignored) {
            return MissingValue.INSTANCE;
        }
    }

    static Object coerceModelValue(String valueType, String value,
                                   Class<?> requestedType) {
        String type = safe(valueType).toUpperCase();
        String raw = safe(value).trim();
        try {
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
                return Float.valueOf(rationalDecimal(raw));
            }
            if (requestedType == double.class || requestedType == Double.class
                    || "REAL".equals(type) && requestedType == null) {
                return Double.valueOf(rationalDecimal(raw));
            }
            if (requestedType == String.class || "STRING".equals(type)) {
                return unquoteSmtString(raw);
            }
            if ((requestedType == null || !requestedType.isPrimitive())
                    && ("NULL".equals(type) || "null".equalsIgnoreCase(raw))) {
                return null;
            }
        } catch (RuntimeException ignored) {
            return UnsupportedReplayValue.INSTANCE;
        }
        return UnsupportedReplayValue.INSTANCE;
    }

    private static String rationalDecimal(String value) {
        String raw = safe(value).trim();
        if (raw.startsWith("(/ ") && raw.endsWith(")")) {
            String[] pieces = raw.substring(3, raw.length() - 1).trim()
                    .split("\\s+");
            if (pieces.length == 2) {
                return String.valueOf(Double.parseDouble(pieces[0])
                        / Double.parseDouble(pieces[1]));
            }
        }
        return raw;
    }

    private static String unquoteSmtString(String value) {
        String raw = safe(value);
        if (raw.length() >= 2 && raw.startsWith("\"")
                && raw.endsWith("\"")) {
            raw = raw.substring(1, raw.length() - 1);
        }
        return raw.replace("\"\"", "\"");
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
            if (declaredArray && !liveArray) {
                active.captureEngineArrayInputBinding(action, value, value,
                        symbolizationToken, action.directArrayType(value),
                        safe(action.location), api);
                return;
            }
            api.symbolize(value, action.symbol);
            active.symbolized.add(action.symbol);
            if (liveArray) {
                active.captureEngineArrayInputBinding(action, value, value,
                        symbolizationToken, action.directArrayType(value),
                        safe(action.location), api);
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

    /** Reads only the field declared by the exact Soot field signature. */
    private static ExactFieldObservation observeExactField(
            Object owner, String fieldSignature) {
        ExactFieldObservation result = new ExactFieldObservation();
        String[] declared = declaredField(fieldSignature);
        if (declared == null) {
            result.error = "invalid field signature";
            return result;
        }
        if (owner == null) {
            result.error = "field owner is null";
            return result;
        }
        Class<?> declaringClass = owner.getClass();
        while (declaringClass != null
                && !declared[0].equals(declaringClass.getName())) {
            declaringClass = declaringClass.getSuperclass();
        }
        if (declaringClass == null) {
            result.error = "owner is not an instance of declared field owner "
                    + declared[0];
            return result;
        }
        result.ownerVerified = true;
        try {
            // Reuse the same exact resolver as ARRAY_VALUE model writes so
            // type discovery, prepared reads and replay writes cannot drift
            // to a hidden same-named subclass field.
            Field field = exactDeclaredInstanceField(owner, fieldSignature);
            if (field == null) {
                result.error = "declared instance field is absent, static, "
                        + "or has a signature type mismatch: " + declared[2];
                return result;
            }
            result.fieldType = field.getType();
            result.typeVerified = true;
            result.value = field.get(owner);
            result.available = true;
        } catch (Throwable throwable) {
            result.error = "declared field read failed: "
                    + rootCause(throwable);
        }
        return result;
    }

    private static boolean sameExactFieldValue(Object entry, Object output,
                                               Class<?> fieldType) {
        if (fieldType == null) return false;
        if (!fieldType.isPrimitive()) return entry == output;
        return entry == null ? output == null : entry.equals(output);
    }

    private static String normalizeFieldType(String type) {
        return safe(type).trim().replace('/', '.');
    }

    private static String javaTypeDescriptor(String javaType) {
        String value = safe(javaType).trim();
        if (value.isEmpty()) return "";
        if (value.startsWith("[")) {
            return value.replace('.', '/');
        }
        int dimensions = 0;
        while (value.endsWith("[]")) {
            dimensions++;
            value = value.substring(0, value.length() - 2).trim();
        }
        String base;
        if (value.length() == 1 && "ZBCSIJFDV".contains(value)) {
            base = value;
        } else if ("boolean".equals(value)) base = "Z";
        else if ("byte".equals(value)) base = "B";
        else if ("char".equals(value)) base = "C";
        else if ("short".equals(value)) base = "S";
        else if ("int".equals(value)) base = "I";
        else if ("long".equals(value)) base = "J";
        else if ("float".equals(value)) base = "F";
        else if ("double".equals(value)) base = "D";
        else if ("void".equals(value)) base = "V";
        else if (value.startsWith("L") && value.endsWith(";")) {
            base = "L" + value.substring(1, value.length() - 1)
                    .replace('.', '/') + ";";
        } else {
            base = "L" + value.replace('.', '/') + ";";
        }
        StringBuilder descriptor = new StringBuilder();
        for (int index = 0; index < dimensions; index++) {
            descriptor.append('[');
        }
        return descriptor.append(base).toString();
    }

    private static String reflectionDescriptor(Class<?> type) {
        if (type == null) return "";
        if (type.isArray()) return type.getName().replace('.', '/');
        return javaTypeDescriptor(reflectionTypeName(type));
    }

    private static String inputJavaTypeFromCell(String cell) {
        String[] field = declaredField(cell);
        if (field != null) return field[1];
        Matcher parameter = Pattern.compile(
                "\\.param\\d+:([^#]+)").matcher(safe(cell));
        return parameter.find() ? parameter.group(1).trim() : "";
    }

    private static String reflectionTypeName(Class<?> type) {
        if (type == null) return "";
        if (type.isArray()) {
            return reflectionTypeName(type.getComponentType()) + "[]";
        }
        return type.getName();
    }

    private static boolean valuesEqual(Object left, Object right) {
        return left == right || left != null && left.equals(right);
    }

    private static JsonObject fieldObservation(ActiveRegion active,
                                               String symbol, Object root,
                                               List<String> path,
                                               String phase) {
        return fieldObservation(active, symbol, root, path, phase, null);
    }

    private static JsonObject fieldObservation(ActiveRegion active,
                                               String symbol, Object root,
                                               List<String> path,
                                               String phase,
                                               DynamicFieldBinding binding) {
        JsonObject result = new JsonObject();
        result.addProperty("symbol", safe(symbol));
        result.addProperty("phase", safe(phase));
        result.add("path", GSON.toJsonTree(path));
        result.addProperty("accessOwnerClass", root == null ? "null"
                : root.getClass().getName());
        result.addProperty("accessOwnerIdentity", root == null ? 0
                : System.identityHashCode(root));
        result.addProperty("accessOwnerObjectToken",
                active.objectToken(root));
        result.addProperty("accessOwnerObjectTokenKnown", root != null);
        result.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        result.addProperty("objectTokenScope",
                active.activation.activationId);
        Object owner = resolveFieldPathLeafOwner(root, path);
        if (owner == null || owner == MissingValue.INSTANCE
                || path == null || path.isEmpty()) {
            result.addProperty("available", false);
            return result;
        }
        String leaf = path.get(path.size() - 1);
        Object value = readField(owner, leaf);
        if (value == MissingValue.INSTANCE) {
            result.addProperty("available", false);
            return result;
        }
        result.addProperty("available", true);
        result.addProperty("leafOwnerClass", owner.getClass().getName());
        result.addProperty("leafOwnerIdentity", System.identityHashCode(owner));
        result.addProperty("leafOwnerObjectToken",
                active.objectToken(owner));
        result.addProperty("leafOwnerObjectTokenKnown", true);
        JsonArray entryReads = new JsonArray();
        for (MapIteratorCursor cursor : active.mapIterators.values()) {
            if (cursor.hasCurrent && cursor.valueKnown
                    && cursor.value == owner
                    && !cursor.entryObservationId.isEmpty()) {
                entryReads.add(new JsonPrimitive(
                        cursor.entryObservationId));
            }
        }
        if (entryReads.size() > 0) {
            result.add("entryReadObservationIds", entryReads);
            result.addProperty("entryReadObservationCount",
                    entryReads.size());
            result.addProperty("entryReadBindingAuthority",
                    "RUNTIME_REFERENCE_EQUALITY_TO_CURRENT_ENTRY_VALUE");
        }
        result.addProperty("valueClass", value == null ? "null"
                : value.getClass().getName());
        result.addProperty("valueIdentity", value == null ? 0
                : System.identityHashCode(value));
        result.addProperty("valueObjectToken", active.objectToken(value));
        result.addProperty("valueObjectTokenKnown", value != null);
        appendValueObservation(result, value);
        if (binding != null) {
            annotateDynamicFieldBinding(result, binding,
                    binding.entryReadObservationId);
        }
        return result;
    }

    /** Exact-signature counterpart used only by consumed ARRAY_VALUE leaves. */
    private static JsonObject exactLeafFieldObservation(
            ActiveRegion active, String symbol, Object leafOwner,
            String fieldSignature, String fieldName, String phase) {
        JsonObject result = new JsonObject();
        result.addProperty("symbol", safe(symbol));
        result.addProperty("phase", safe(phase));
        result.add("path", GSON.toJsonTree(
                Collections.singletonList(fieldName)));
        result.addProperty("accessOwnerClass", leafOwner == null ? "null"
                : leafOwner.getClass().getName());
        result.addProperty("accessOwnerIdentity", leafOwner == null ? 0
                : System.identityHashCode(leafOwner));
        result.addProperty("accessOwnerObjectToken",
                active.objectToken(leafOwner));
        result.addProperty("accessOwnerObjectTokenKnown",
                leafOwner != null);
        result.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        result.addProperty("objectTokenScope",
                active.activation.activationId);
        result.addProperty("exactFieldSignature", safe(fieldSignature));
        result.addProperty("exactFieldSignatureAuthority",
                "BYTECODE_GETFIELD_DECLARING_OWNER_NAME_AND_TYPE");
        ExactFieldObservation exact = observeExactField(leafOwner,
                fieldSignature);
        if (!exact.ownerVerified || !exact.typeVerified
                || !exact.available) {
            result.addProperty("available", false);
            result.addProperty("problem", exact.error);
            return result;
        }
        Object value = exact.value;
        result.addProperty("available", true);
        result.addProperty("leafOwnerClass", leafOwner.getClass().getName());
        result.addProperty("leafOwnerIdentity",
                System.identityHashCode(leafOwner));
        result.addProperty("leafOwnerObjectToken",
                active.objectToken(leafOwner));
        result.addProperty("leafOwnerObjectTokenKnown", true);
        result.addProperty("valueClass", value == null ? "null"
                : value.getClass().getName());
        result.addProperty("valueIdentity", value == null ? 0
                : System.identityHashCode(value));
        result.addProperty("valueObjectToken", active.objectToken(value));
        result.addProperty("valueObjectTokenKnown", value != null);
        appendValueObservation(result, value);
        return result;
    }

    private static void appendValueObservation(JsonObject result,
                                               Object value) {
        if (value instanceof Map) {
            Map<?, ?> map = (Map<?, ?>) value;
            result.addProperty("collectionSize", map.size());
            JsonArray keys = new JsonArray();
            int count = 0;
            for (Object key : map.keySet()) {
                if (count++ >= 32) break;
                keys.add(primitiveObservation(key));
            }
            result.add("mapKeys", keys);
        } else if (value != null && value.getClass().isArray()) {
            int length = Array.getLength(value);
            result.addProperty("arrayLength", length);
            JsonArray elements = new JsonArray();
            for (int index = 0; index < length && index < 32; index++) {
                Object element = Array.get(value, index);
                JsonObject item = new JsonObject();
                item.addProperty("index", index);
                item.addProperty("class", element == null ? "null"
                        : element.getClass().getName());
                item.addProperty("identity", element == null ? 0
                        : System.identityHashCode(element));
                Object keyId = readField(element, "keyId");
                if (keyId != MissingValue.INSTANCE) {
                    item.add("keyId", primitiveObservation(keyId));
                }
                elements.add(item);
            }
            result.add("arrayElements", elements);
        } else {
            result.add("value", primitiveObservation(value));
        }
    }

    private static JsonElement primitiveObservation(Object value) {
        if (value == null) return GSON.toJsonTree(null);
        if (value instanceof Number || value instanceof Boolean
                || value instanceof Character || value instanceof String) {
            return GSON.toJsonTree(value);
        }
        JsonObject result = new JsonObject();
        result.addProperty("class", value.getClass().getName());
        result.addProperty("identity", System.identityHashCode(value));
        return result;
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

    static Boolean lightweightAccessorContextMatchesForTests(
            String callerMethod, int callUnitIndex, String callSiteId,
            String declaredCallee, Object fieldOwner) {
        return lightweightAccessorContextMatches(callerMethod,
                callUnitIndex, callSiteId, declaredCallee, fieldOwner);
    }

    private static ActiveRegion ownerRegion(long token) {
        ActiveRegion active = ACTIVE.get(token);
        return active != null && active.thread == Thread.currentThread()
                ? active : null;
    }

    static boolean activeTokenForTests(long token) {
        return ACTIVE.containsKey(token);
    }

    static int concreteReplayActiveCountForTests() {
        synchronized (EXECUTION_MODE_LOCK) {
            return concreteReplayActiveCount;
        }
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
        return jsonString(condition.getAsJsonObject(), "_code_position");
    }

    static boolean branchConditionMatches(String expression, boolean outcome,
                                          JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) {
            return false;
        }
        JsonObject object = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(jsonString(object, "_type"))) {
            return false;
        }
        Matcher matcher = BRANCH_OPERATOR.matcher(safe(expression));
        if (!matcher.find()) {
            return false;
        }
        String declared = matcher.group(1);
        String expected = outcome ? declared : opposite(declared);
        String observed = jsonString(object, "_op");
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
     * The Zero interpreter records a concrete {@code lcmp}/{@code dcmp}
     * trichotomy ({@code <}, {@code ==}, or {@code >}) before Jimple consumes
     * the compare result.  A true Jimple {@code >=} branch is therefore
     * witnessed by either raw {@code >} or raw {@code ==}.  Both imply the
     * branch predicate, but negating either raw witness would not flip the
     * branch.  Admit the implication here and canonicalize the retained
     * condition to the actual Jimple predicate below.
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
        if (!"BinaryExpression".equals(jsonString(original, "_type"))) {
            return condition;
        }
        Matcher matcher = BRANCH_OPERATOR.matcher(safe(expression));
        if (!matcher.find()) {
            return condition;
        }
        String expected = outcome ? matcher.group(1)
                : opposite(matcher.group(1));
        String observed = jsonString(original, "_op");
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
                ? jsonString(condition.getAsJsonObject(), "_op") : "";
    }

    private static boolean symbolicNull(JsonElement element) {
        if (element == null || !element.isJsonObject()) {
            return false;
        }
        JsonObject object = element.getAsJsonObject();
        return "SymbolExpression".equals(jsonString(object, "_type"))
                && "N".equals(jsonString(object, "_exp"));
    }

    private static String opposite(String operator) {
        if ("==".equals(operator)) return "!=";
        if ("!=".equals(operator)) return "==";
        if ("<".equals(operator)) return ">=";
        if (">".equals(operator)) return "<=";
        if ("<=".equals(operator)) return ">";
        if (">=".equals(operator)) return "<";
        return operator;
    }

    private static String jsonString(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value == null || value.isJsonNull()
                ? "" : value.getAsString();
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
            String test, String rootMethod, RootArgumentSelector selector,
            RootContextSelector contextSelector, Object receiver) {
        String key = safe(test) + "\n" + safe(rootMethod) + "\n"
                + (contextSelector == null
                ? "LEGACY_NO_STABLE_ROOT_CONTEXT"
                : contextSelector.identity()) + "\n" + selector.identity();
        synchronized (ORDINALS) {
            if (!selector.receiverScoped) {
                Integer previous = ORDINALS.get(key);
                int value = previous == null ? 1 : previous + 1;
                ORDINALS.put(key, value);
                return SelectorOccurrence.global(value);
            }
            ReceiverSelectorState state = RECEIVER_SELECTOR_STATES.get(key);
            if (state == null) {
                state = new ReceiverSelectorState();
                RECEIVER_SELECTOR_STATES.put(key, state);
            }
            return state.next(receiver);
        }
    }

    private static int nextRootContextOccurrence(
            String test, String rootMethod, RootContextSelector selector) {
        return nextOrdinal("stable-root-context\n" + safe(test) + "\n"
                + safe(rootMethod) + "\n" + selector.identity());
    }

    private static void writeSkipped(Activation activation, String reason) {
        JsonObject result = new JsonObject();
        result.addProperty("event", "CONCOLIC_REGION_SKIPPED");
        result.addProperty("schemaVersion", 1);
        result.addProperty("activationId", activation.activationId);
        result.addProperty("regionId", activation.regionId);
        result.addProperty("rootMethod", activation.rootMethod);
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

    private static String firstNonBlank(String... values) {
        if (values != null) {
            for (String value : values) {
                if (value != null && !value.trim().isEmpty()) {
                    return value.trim();
                }
            }
        }
        return "";
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }

    private static final class ExactFieldObservation {
        private boolean ownerVerified;
        private boolean typeVerified;
        private boolean available;
        private Class<?> fieldType;
        private Object value;
        private String error = "";
    }

    private enum MissingValue { INSTANCE }

    private enum UnsupportedReplayValue { INSTANCE }

    private static final class MapViewBinding {
        private final Object map;
        private final String viewKind;
        private final String originSiteId;

        private MapViewBinding(Object map, String viewKind,
                               String originSiteId) {
            this.map = map;
            this.viewKind = viewKind;
            this.originSiteId = originSiteId;
        }
    }

    private static final class MapIteratorCursor {
        private final MapViewBinding binding;
        private final String iteratorOriginSiteId;
        private String nextOriginSiteId = "";
        private Object element;
        private Object key;
        private Object value;
        private boolean hasCurrent;
        private boolean keyKnown;
        private boolean valueKnown;
        private String bindingError = "";
        private JsonElement mapExpression;
        private JsonElement keyExpression;
        private JsonElement valueExpression;
        private JsonElement entryExpression;
        private String keyExpressionAuthority = "";
        private String valueExpressionAuthority = "";
        private String entryExpressionWarning = "";
        private String valueExpressionWarning = "";
        private String entryObservationId = "";
        private long entryObservationSequence;
        private boolean entryObservationComplete;
        private JsonObject entryObservation;
        private String entryObservationUnresolved = "";
        private int entryRefreshCount;
        private int pathConditionSize;
        private boolean finiteMapSnapshotAttempted;

        private MapIteratorCursor(MapViewBinding binding,
                                  String iteratorOriginSiteId) {
            this.binding = binding;
            this.iteratorOriginSiteId = iteratorOriginSiteId;
        }

        private void resetForNext(String originSiteId, Object current) {
            nextOriginSiteId = originSiteId;
            element = current;
            key = null;
            value = null;
            hasCurrent = false;
            keyKnown = false;
            valueKnown = false;
            bindingError = "";
            mapExpression = null;
            keyExpression = null;
            valueExpression = null;
            entryExpression = null;
            keyExpressionAuthority = "";
            valueExpressionAuthority = "";
            entryExpressionWarning = "";
            valueExpressionWarning = "";
            entryObservationId = "";
            entryObservationSequence = 0L;
            entryObservationComplete = false;
            entryObservation = null;
            entryObservationUnresolved = "";
            entryRefreshCount = 0;
            pathConditionSize = 0;
        }
    }

    private static final class ContainerInputObservation {
        private final Object container;
        private final long objectToken;
        private final String location;
        private boolean ambiguous;

        private ContainerInputObservation(Object container, long objectToken,
                                          String location,
                                          boolean ambiguous) {
            this.container = container;
            this.objectToken = objectToken;
            this.location = safe(location);
            this.ambiguous = ambiguous;
        }

        private static ContainerInputObservation ambiguous(
                Object container, long objectToken, String location) {
            return new ContainerInputObservation(container, objectToken,
                    location, true);
        }
    }

    private static final class ContainerFieldResolution {
        private final boolean declared;
        private final boolean ignored;
        private final DynamicFieldSelection selection;
        private final String problem;

        private ContainerFieldResolution(boolean declared,
                                         boolean ignored,
                                         DynamicFieldSelection selection,
                                         String problem) {
            this.declared = declared;
            this.ignored = ignored;
            this.selection = selection;
            this.problem = safe(problem);
        }

        private static ContainerFieldResolution notDeclared() {
            return new ContainerFieldResolution(false, false, null, "");
        }

        private static ContainerFieldResolution ignored() {
            return new ContainerFieldResolution(true, true, null, "");
        }

        private static ContainerFieldResolution resolved(
                DynamicFieldSelection selection) {
            return new ContainerFieldResolution(true, false, selection, "");
        }

        private static ContainerFieldResolution unresolved(String problem) {
            return new ContainerFieldResolution(true, false, null, problem);
        }

        private boolean resolved() {
            return selection != null && selection.binding != null
                    && problem.isEmpty();
        }
    }

    private static final class ContainerElementMatch {
        private final ContainerElementFieldBindingSpec spec;
        private final int resolvedElementIndex;

        private ContainerElementMatch(
                ContainerElementFieldBindingSpec spec,
                int resolvedElementIndex) {
            this.spec = spec;
            this.resolvedElementIndex = resolvedElementIndex;
        }
    }

    private static final class DeclaredArrayInputType {
        private final String javaType;
        private final String authority;
        private final String problem;

        private DeclaredArrayInputType(String javaType, String authority,
                                       String problem) {
            this.javaType = safe(javaType);
            this.authority = safe(authority);
            this.problem = safe(problem);
        }

        private static DeclaredArrayInputType exact(
                String javaType, String authority) {
            return new DeclaredArrayInputType(javaType, authority, "");
        }

        private static DeclaredArrayInputType incomplete(String problem) {
            return new DeclaredArrayInputType("", "", problem);
        }

        private static DeclaredArrayInputType incomplete(
                String javaType, String problem) {
            return new DeclaredArrayInputType(javaType, "", problem);
        }

        private boolean complete() {
            return problem.isEmpty() && javaTypeDescriptor(javaType)
                    .startsWith("[") && !authority.isEmpty();
        }
    }

    /**
     * Exact runtime bridge from one declared array input port to the custom
     * VM's active symbolic-array identity.  The engine id is captured only
     * after the same live array has been symbolized by its unique input
     * action; activation-local object tokens are evidence, never an ordinal
     * selector across executions.
     */
    private static final class EngineArrayInputBinding {
        private static final String KIND = "ENGINE_ARRAY_TO_INPUT_PORT";
        private static final String ENGINE_ID_AUTHORITY =
                "VM_ACTIVE_SYM_ARRAY_ID_V1";
        private static final String TOKEN_AUTHORITY =
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN";
        private static final String CAPTURE_AUTHORITY =
                "SAME_LIVE_ARRAY_AFTER_EXACT_INPUT_ACTION_SYMBOLIZATION";

        private final int schemaVersion = 1;
        private final String kind = KIND;
        private final String sourceActivationId;
        private final String inputPort;
        private final String inputCell;
        private final String baseInputPort;
        private final String dynamicBindingId;
        private final boolean dynamicInput;
        private final String inputJavaType;
        private final String inputJavaTypeDescriptor;
        private final String inputJavaTypeAuthority;
        private final long arrayObjectToken;
        private final long symbolizationArrayObjectToken;
        private final String symbolizationPrefix;
        private final String symbolizationMode =
                "DIRECT_ARRAY_VALUE_WITH_CANONICAL_INPUT_PREFIX";
        private final String symbolizationIdentityAuthority =
                "SAME_JAVA_REFERENCE_PASSED_TO_SYMBOLIZE_AND_"
                        + "EXPRESSION_CAPTURE";
        private final String objectTokenAuthority = TOKEN_AUTHORITY;
        private final String objectTokenScope;
        private final String captureAuthority = CAPTURE_AUTHORITY;
        private final String captureLocation;
        private String engineArrayId = "";
        private String engineArrayIdAuthority = "";
        private String vmArrayValueAuthority = "";
        private String vmArrayJavaTypeDescriptor = "";
        private String vmComponentJavaTypeDescriptor = "";
        private JsonObject arrayValueExpression = new JsonObject();
        private int reflectedArrayLength = -1;
        private int vmConcreteLength = -1;
        private boolean sameArrayObjectTokenVerified;
        private boolean fieldPrePostReferenceVerified;
        private long postReadArrayObjectToken;
        private boolean vmActive;
        private boolean vmSymbolic;
        private boolean complete;
        private String problem = "";
        private long consumedLeafOwnerObjectToken;
        private String consumedLeafFieldSignature = "";
        private final List<String> consumedLogicalFieldPath =
                new ArrayList<>();
        private boolean logicalRootIdentityVerified;

        private EngineArrayInputBinding(ActiveRegion active,
                                        SymbolizeAction action,
                                        Object array,
                                        long expectedToken,
                                        DeclaredArrayInputType declaredType,
                                        String location,
                                        String canonicalInputPort,
                                        String canonicalInputCell,
                                        DynamicFieldBinding dynamicBinding) {
            this.sourceActivationId = active.activation.activationId;
            this.inputPort = safe(canonicalInputPort);
            this.inputCell = safe(canonicalInputCell);
            this.baseInputPort = action.symbol;
            this.dynamicBindingId = dynamicBinding == null ? ""
                    : dynamicBinding.dynamicBindingId;
            this.dynamicInput = dynamicBinding != null;
            this.inputJavaType = safe(declaredType.javaType);
            this.inputJavaTypeAuthority = safe(declaredType.authority);
            this.inputJavaTypeDescriptor = reflectionDescriptor(
                    array == null ? null : array.getClass());
            this.arrayObjectToken = active.objectToken(array);
            this.symbolizationArrayObjectToken = expectedToken;
            this.symbolizationPrefix = this.inputPort;
            this.objectTokenScope = active.activation.activationId;
            this.captureLocation = safe(location);
        }

        private static EngineArrayInputBinding capture(
                ActiveRegion active, SymbolizeAction action, Object array,
                Object postReadArray, long expectedToken,
                DeclaredArrayInputType declaredType, String location,
                EngineApi api) {
            return capture(active, action, array, postReadArray,
                    expectedToken, declaredType, location, action.symbol,
                    action.cell, null, api);
        }

        private static EngineArrayInputBinding capture(
                ActiveRegion active, SymbolizeAction action, Object array,
                Object postReadArray, long expectedToken,
                DeclaredArrayInputType declaredType, String location,
                String canonicalInputPort, String canonicalInputCell,
                DynamicFieldBinding dynamicBinding, EngineApi api) {
            EngineArrayInputBinding binding = new EngineArrayInputBinding(
                    active, action, array, expectedToken,
                    declaredType, location, canonicalInputPort,
                    canonicalInputCell, dynamicBinding);
            boolean exactStaticAction = active.activation.actionCount(
                    action.symbol) == 1 && !action.symbol.isEmpty()
                    && !action.cell.isEmpty();
            boolean exactDynamicInput = dynamicBinding == null
                    || !binding.inputPort.isEmpty()
                    && binding.inputPort.equals(
                    dynamicBinding.dynamicFieldSymbol)
                    && !binding.dynamicBindingId.isEmpty();
            if (!exactStaticAction || !exactDynamicInput
                    || binding.inputPort.isEmpty()
                    || binding.inputCell.isEmpty()) {
                binding.fail("input port does not identify one unique exact "
                        + "symbolize action");
                return binding;
            }
            if (array == null || !array.getClass().isArray()) {
                binding.fail("symbolized live input is not a non-null array");
                return binding;
            }
            binding.postReadArrayObjectToken = active.objectToken(
                    postReadArray);
            binding.fieldPrePostReferenceVerified = postReadArray == array;
            if (!binding.fieldPrePostReferenceVerified) {
                binding.fail("field value reference changed between direct "
                        + "array symbolization and post-symbolization read");
            }
            binding.sameArrayObjectTokenVerified = expectedToken > 0L
                    && expectedToken == binding.arrayObjectToken;
            if (!binding.sameArrayObjectTokenVerified) {
                binding.fail("symbolization array token does not identify "
                        + "the exact Java reference captured from the VM");
            }
            if (!declaredType.complete()) {
                binding.fail(firstNonBlank(declaredType.problem,
                        "exact declared leaf array type is unavailable"));
            }
            String declaredDescriptor = javaTypeDescriptor(
                    declaredType.javaType);
            if (declaredType.javaType.isEmpty()
                    || !declaredDescriptor.startsWith("[")) {
                binding.fail("input action has no exact declared array "
                        + "javaType");
            } else if (!declaredDescriptor.equals(
                    binding.inputJavaTypeDescriptor)) {
                binding.fail("declared input javaType descriptor "
                        + declaredDescriptor + " differs from live array "
                        + binding.inputJavaTypeDescriptor);
            }

            binding.reflectedArrayLength = Array.getLength(array);
            boolean paused = false;
            try {
                api.pausePathCondition();
                paused = true;
                JsonElement parsed = parseJson(api.expression(array));
                if (!parsed.isJsonObject()) {
                    binding.fail("VM array expression envelope is not an "
                            + "object");
                    return binding;
                }
                JsonObject envelope = parsed.getAsJsonObject();
                binding.vmActive = bool(envelope, "active", false);
                binding.vmSymbolic = bool(envelope, "symbolic", false);
                if (integer(envelope, "schemaVersion", -1) != 1
                        || !binding.vmActive
                        || !binding.vmSymbolic
                        || !"ARRAY_VALUE".equals(string(envelope,
                        "kind"))) {
                    binding.fail("VM envelope is not one active symbolic "
                            + "ARRAY_VALUE");
                }
                JsonElement expressionElement = envelope.get("expression");
                if (expressionElement == null
                        || !expressionElement.isJsonObject()) {
                    binding.fail("VM ARRAY_VALUE expression is missing");
                    return binding;
                }
                JsonObject expression = expressionElement.getAsJsonObject();
                binding.arrayValueExpression = copyJsonTree(expression);
                if (!"ArrayValueExpression".equals(string(expression,
                        "_type")) || integer(expression,
                        "_schema_version", -1) != 1) {
                    binding.fail("VM finite-array expression schema is "
                            + "unsupported");
                }
                binding.vmArrayValueAuthority = string(expression,
                        "_authority");
                if (!"VM_EXACT_FINITE_ARRAY_VALUE_V1".equals(
                        binding.vmArrayValueAuthority)) {
                    binding.fail("VM finite-array value authority is invalid");
                }
                binding.vmArrayJavaTypeDescriptor = string(expression,
                        "_java_type").replace('.', '/');
                binding.vmComponentJavaTypeDescriptor = string(expression,
                        "_component_java_type").replace('.', '/');
                if (!binding.inputJavaTypeDescriptor.equals(
                        binding.vmArrayJavaTypeDescriptor)) {
                    binding.fail("VM array descriptor differs from the same "
                            + "live input array");
                }
                String expectedComponent = binding.inputJavaTypeDescriptor
                        .startsWith("[")
                        ? binding.inputJavaTypeDescriptor.substring(1) : "";
                if (!expectedComponent.equals(
                        binding.vmComponentJavaTypeDescriptor)) {
                    binding.fail("VM component descriptor differs from the "
                            + "live input array component");
                }
                binding.vmConcreteLength = integer(expression,
                        "_concrete_length", -1);
                if (binding.vmConcreteLength
                        != binding.reflectedArrayLength) {
                    binding.fail("VM array length differs from reflection: "
                            + binding.vmConcreteLength + " != "
                            + binding.reflectedArrayLength);
                }
                binding.validateFiniteElements(expression,
                        expectedComponent, array);
                binding.engineArrayId = string(expression,
                        "_engine_array_id");
                binding.engineArrayIdAuthority = string(expression,
                        "_engine_array_id_authority");
                char expectedIdType = expectedComponent.isEmpty()
                        ? '\0' : expectedComponent.charAt(0);
                if (binding.engineArrayId.isEmpty()
                        || !binding.engineArrayId.matches("A._[0-9]+")
                        || binding.engineArrayId.length() < 4
                        || binding.engineArrayId.charAt(1)
                        != expectedIdType
                        || !ENGINE_ID_AUTHORITY.equals(
                        binding.engineArrayIdAuthority)) {
                    binding.fail("VM active symbolic-array id/authority is "
                            + "missing, malformed, or disagrees with the "
                            + "component descriptor");
                }
            } catch (Throwable throwable) {
                binding.fail("VM array-id capture failed: "
                        + rootCause(throwable));
            } finally {
                if (paused) {
                    try {
                        api.resumePathCondition();
                    } catch (Throwable throwable) {
                        binding.fail("array-id capture PC resume failed: "
                                + rootCause(throwable));
                    }
                }
            }
            long tokenAfter = active.objectToken(array);
            if (tokenAfter != expectedToken
                    || tokenAfter != binding.arrayObjectToken) {
                binding.sameArrayObjectTokenVerified = false;
                binding.fail("array object token changed during VM capture");
            }
            binding.complete = binding.problem.isEmpty();
            return binding;
        }

        private void validateFiniteElements(JsonObject expression,
                                            String componentDescriptor,
                                            Object concreteArray) {
            JsonElement lengthValue = expression.get("_length_exp");
            if (lengthValue == null || !lengthValue.isJsonObject()) {
                fail("VM finite-array length expression is missing");
            } else {
                JsonObject length = lengthValue.getAsJsonObject();
                if (!"ConstExpr".equals(string(length, "_type"))
                        || !"I".equals(string(length, "_java_type"))
                        || !("Y_I_" + reflectedArrayLength).equals(
                        string(length, "_exp"))) {
                    fail("VM finite-array length expression is not the "
                            + "exact reflected length constant");
                }
            }
            if (!bool(expression, "_elements_complete", false)) {
                fail("VM finite-array element snapshot is incomplete");
            }
            JsonElement elementsValue = expression.get("_elements");
            if (elementsValue == null || !elementsValue.isJsonArray()) {
                fail("VM finite-array elements are missing");
                return;
            }
            JsonArray elements = elementsValue.getAsJsonArray();
            if (elements.size() != reflectedArrayLength) {
                fail("VM finite-array element count differs from reflected "
                        + "length");
            }
            Set<Integer> indices = new LinkedHashSet<>();
            for (int ordinal = 0; ordinal < elements.size(); ordinal++) {
                JsonElement elementValue = elements.get(ordinal);
                if (!elementValue.isJsonObject()) {
                    fail("VM finite-array element " + ordinal
                            + " is malformed");
                    continue;
                }
                JsonObject element = elementValue.getAsJsonObject();
                int index = integer(element, "index", -1);
                if (index != ordinal || index < 0
                        || index >= reflectedArrayLength
                        || !indices.add(index)) {
                    fail("VM finite-array element index is not one exact "
                            + "contiguous ordinal at " + ordinal);
                }
                JsonElement value = element.get("expression");
                if (value == null || !value.isJsonObject()) {
                    fail("VM finite-array element expression is missing at "
                            + ordinal);
                    continue;
                }
                String provenance = string(element, "provenance");
                if (!validElementProvenance(provenance, value,
                        componentDescriptor)) {
                    fail("VM finite-array element provenance is invalid at "
                            + ordinal);
                }
                if (!elementTypeCompatible(value,
                        componentDescriptor)) {
                    fail("VM finite-array element type differs from its "
                            + "component descriptor at " + ordinal);
                }
                if ("CONCRETE_PRIMITIVE".equals(provenance)
                        && !exactPrimitiveLiteral(value.getAsJsonObject(),
                        componentDescriptor, concreteArray, ordinal)) {
                    fail("VM concrete primitive literal differs from the "
                            + "reflected array element at " + ordinal);
                }
            }
        }

        private static boolean exactPrimitiveLiteral(
                JsonObject expression, String componentDescriptor,
                Object concreteArray, int index) {
            if (concreteArray == null || !concreteArray.getClass().isArray()
                    || componentDescriptor.length() != 1) {
                return false;
            }
            char type = componentDescriptor.charAt(0);
            String prefix = "Y_" + type + "_";
            String encoded = string(expression, "_exp");
            if (!encoded.startsWith(prefix)) return false;
            String literal = encoded.substring(prefix.length());
            try {
                Object concrete = Array.get(concreteArray, index);
                switch (type) {
                    case 'Z':
                        return (Boolean.TRUE.equals(concrete) ? "1" : "0")
                                .equals(literal);
                    case 'B':
                        return Byte.parseByte(literal)
                                == ((Number) concrete).byteValue();
                    case 'C':
                        return concrete instanceof Character
                                && literal.equals(String.valueOf(
                                ((Character) concrete).charValue()));
                    case 'S':
                        return Short.parseShort(literal)
                                == ((Number) concrete).shortValue();
                    case 'I':
                        return Integer.parseInt(literal)
                                == ((Number) concrete).intValue();
                    case 'J':
                        return Long.parseLong(literal)
                                == ((Number) concrete).longValue();
                    case 'F':
                        return Float.floatToIntBits(Float.parseFloat(literal))
                                == Float.floatToIntBits(
                                ((Number) concrete).floatValue());
                    case 'D':
                        return Double.doubleToLongBits(
                                Double.parseDouble(literal))
                                == Double.doubleToLongBits(
                                ((Number) concrete).doubleValue());
                    default:
                        return false;
                }
            } catch (Throwable ignored) {
                return false;
            }
        }

        private static boolean validElementProvenance(
                String provenance, JsonElement expression,
                String componentDescriptor) {
            JsonObject value = expression.getAsJsonObject();
            if ("CONCRETE_NULL".equals(provenance)) {
                return (componentDescriptor.startsWith("L")
                        || componentDescriptor.startsWith("["))
                        && "SymbolExpression".equals(string(value,
                        "_type")) && "N".equals(string(value, "_exp"));
            }
            if ("CONCRETE_PRIMITIVE".equals(provenance)) {
                return componentDescriptor.length() == 1
                        && "ZBCSIJFD".contains(componentDescriptor)
                        && "ConstExpr".equals(string(value, "_type"));
            }
            return "ARRAY_SHADOW".equals(provenance)
                    || "SYMBOLIC_ELEMENT".equals(provenance);
        }

        private static boolean elementTypeCompatible(
                JsonElement expression, String componentDescriptor) {
            JsonObject value = expression.getAsJsonObject();
            if ("N".equals(string(value, "_exp"))) {
                return componentDescriptor.startsWith("L")
                        || componentDescriptor.startsWith("[");
            }
            return componentDescriptor.equals(javaTypeDescriptor(
                    string(value, "_java_type")));
        }

        private void fail(String detail) {
            complete = false;
            problem = appendReason(problem, detail);
        }

        private void markConsumedLeaf(ActiveRegion active, Object leafOwner,
                                      String leafFieldSignature,
                                      List<String> logicalFieldPath) {
            this.consumedLeafOwnerObjectToken = active.objectToken(leafOwner);
            this.consumedLeafFieldSignature = safe(leafFieldSignature);
            this.consumedLogicalFieldPath.clear();
            this.consumedLogicalFieldPath.addAll(logicalFieldPath);
            this.logicalRootIdentityVerified = true;
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", schemaVersion);
            result.addProperty("kind", kind);
            result.addProperty("sourceActivationId", sourceActivationId);
            result.addProperty("inputPort", inputPort);
            result.addProperty("inputCell", inputCell);
            result.addProperty("baseInputPort", baseInputPort);
            result.addProperty("dynamicInput", dynamicInput);
            if (!dynamicBindingId.isEmpty()) {
                result.addProperty("dynamicBindingId", dynamicBindingId);
            }
            result.addProperty("inputJavaType", inputJavaType);
            result.addProperty("inputJavaTypeDescriptor",
                    inputJavaTypeDescriptor);
            result.addProperty("inputJavaTypeAuthority",
                    inputJavaTypeAuthority);
            result.addProperty("symbolizationPrefix",
                    symbolizationPrefix);
            result.addProperty("symbolizationMode", symbolizationMode);
            result.addProperty("symbolizationArrayObjectToken",
                    symbolizationArrayObjectToken);
            result.addProperty("symbolizationIdentityAuthority",
                    symbolizationIdentityAuthority);
            result.addProperty("engineArrayId", engineArrayId);
            result.addProperty("engineArrayIdAuthority",
                    engineArrayIdAuthority);
            result.addProperty("arrayObjectToken", arrayObjectToken);
            result.addProperty("objectTokenAuthority",
                    objectTokenAuthority);
            result.addProperty("objectTokenScope", objectTokenScope);
            result.addProperty("crossExecutionOrdinalAuthority", "NONE");
            result.addProperty("captureAuthority", captureAuthority);
            result.addProperty("captureLocation", captureLocation);
            result.add("arrayValueExpression",
                    copyJsonTree(arrayValueExpression));
            result.addProperty("vmArrayValueAuthority",
                    vmArrayValueAuthority);
            result.addProperty("vmArrayJavaTypeDescriptor",
                    vmArrayJavaTypeDescriptor);
            result.addProperty("vmComponentJavaTypeDescriptor",
                    vmComponentJavaTypeDescriptor);
            result.addProperty("reflectedArrayLength",
                    reflectedArrayLength);
            result.addProperty("vmConcreteLength", vmConcreteLength);
            result.addProperty("vmActive", vmActive);
            result.addProperty("vmSymbolic", vmSymbolic);
            result.addProperty("sameArrayObjectTokenVerified",
                    sameArrayObjectTokenVerified);
            result.addProperty("fieldPrePostReferenceVerified",
                    fieldPrePostReferenceVerified);
            result.addProperty("postReadArrayObjectToken",
                    postReadArrayObjectToken);
            result.addProperty("consumedLeafOwnerObjectToken",
                    consumedLeafOwnerObjectToken);
            if (!consumedLeafFieldSignature.isEmpty()) {
                result.addProperty("consumedLeafFieldSignature",
                        consumedLeafFieldSignature);
                result.add("consumedLogicalFieldPath",
                        GSON.toJsonTree(consumedLogicalFieldPath));
            }
            result.addProperty("logicalRootIdentityVerified",
                    logicalRootIdentityVerified);
            result.addProperty("complete", complete);
            if (!problem.isEmpty()) result.addProperty("problem", problem);
            return result;
        }
    }

    private static final class MapProjectionSnapshot {
        private final String groupId;
        private final List<MapValueElementProjectionSpec> specs;
        private final Object map;
        private final long mapObjectToken;
        private final Object[] elements;
        private final long[] elementObjectTokens;
        private final JsonElement[] entryKeyExpressions;
        private final String[] entryKeySelectors;
        private final String location;
        private final String objectTokenScope;
        private final String mapImplementationClass;
        private final String mapImplementationAuthority;
        private final List<MapProjectionFieldBinding> bindings =
                new ArrayList<>();
        private final Map<String, Integer> authorizedReplayIndices =
                new LinkedHashMap<>();
        private int expectedMapKeyAssignmentCount;
        private int expectedMapKeyValidatedCount;
        private boolean entrySetViewOrderVerified;
        private boolean complete;
        private boolean outputIdentityVerified;
        private long outputArrayObjectToken;
        private String outputVerificationAuthority = "";
        private String problem = "";

        private MapProjectionSnapshot(
                String groupId, List<MapValueElementProjectionSpec> specs,
                Object map, long mapObjectToken, Object[] elements,
                long[] elementObjectTokens,
                JsonElement[] entryKeyExpressions,
                String[] entryKeySelectors, String location,
                String objectTokenScope, boolean complete, String problem) {
            this.groupId = groupId;
            this.specs = specs;
            this.map = map;
            this.mapObjectToken = mapObjectToken;
            this.elements = elements;
            this.elementObjectTokens = elementObjectTokens;
            this.entryKeyExpressions = entryKeyExpressions;
            this.entryKeySelectors = entryKeySelectors;
            this.location = safe(location);
            this.objectTokenScope = safe(objectTokenScope);
            this.mapImplementationClass = map == null ? ""
                    : map.getClass().getName();
            this.mapImplementationAuthority =
                    supportedMapProjectionImplementation(map)
                            ? MAP_PROJECTION_IMPLEMENTATION_AUTHORITY : "";
            this.complete = complete;
            this.entrySetViewOrderVerified = complete;
            this.problem = safe(problem);
        }

        private static MapProjectionSnapshot create(
                ActiveRegion active, SymbolizeAction action,
                List<MapValueElementProjectionSpec> specs, Object candidate,
                String location, EngineApi api) {
            String groupId = specs.isEmpty() ? action.symbol
                    : specs.get(0).groupId();
            if (!(candidate instanceof Map<?, ?>)) {
                return failed(groupId, specs, candidate, active, location,
                        "declared backing-map input is not a java.util.Map");
            }
            if (!supportedMapProjectionImplementation(candidate)) {
                return failed(groupId, specs, candidate, active, location,
                        "backing Map exact runtime class is not java.util."
                                + "HashMap or java.util.LinkedHashMap");
            }
            if (specs.isEmpty()) {
                return failed(groupId, specs, candidate, active, location,
                        "projection has no demanded fields");
            }
            Set<String> bindingIds = new LinkedHashSet<>();
            Set<String> fields = new LinkedHashSet<>();
            for (MapValueElementProjectionSpec spec : specs) {
                if (!groupId.equals(spec.groupId())
                        || !bindingIds.add(spec.bindingId)
                        || !fields.add(spec.declaredFieldSignature)) {
                    return failed(groupId, specs, candidate, active,
                            location, "projection field declarations are "
                                    + "duplicate or span multiple groups");
                }
            }

            Map<?, ?> map = (Map<?, ?>) candidate;
            Object[] elements;
            JsonElement[] keyExpressions;
            String[] keySelectors;
            try {
                int initialSize = map.size();
                Object[] entries = map.entrySet().toArray();
                Collection<?> view = map.values();
                int viewSize = view.size();
                if (viewSize > MAX_MAP_PROJECTION_ELEMENTS) {
                    return failed(groupId, specs, map, active, location,
                            "finite projection bound exceeded: "
                                    + viewSize + " > "
                                    + MAX_MAP_PROJECTION_ELEMENTS);
                }
                elements = view.toArray();
                if (entries.length != initialSize
                        || elements.length != viewSize
                        || entries.length != elements.length
                        || map.size() != initialSize
                        || map.entrySet().size() != initialSize
                        || view.size() != viewSize) {
                    return failed(groupId, specs, map, active, location,
                            "entrySet and map view changed while the same-"
                                    + "execution positional snapshot was read");
                }
                if (elements.length == 0) {
                    return failed(groupId, specs, map, active, location,
                            "finite projection contains no element field "
                                    + "owner");
                }
                keyExpressions = new JsonElement[elements.length];
                keySelectors = new String[elements.length];
                Set<String> uniqueKeys = new LinkedHashSet<>();
                IdentityHashMap<Object, Boolean> keyIdentities =
                        new IdentityHashMap<>();
                for (int index = 0; index < entries.length; index++) {
                    if (!(entries[index] instanceof Map.Entry<?, ?>)) {
                        return failed(groupId, specs, map, active, location,
                                "entrySet snapshot did not contain Map.Entry "
                                        + "at index " + index);
                    }
                    Map.Entry<?, ?> entry = (Map.Entry<?, ?>) entries[index];
                    Object key = entry.getKey();
                    Object expected = entry.getValue();
                    keyIdentities.put(key, Boolean.TRUE);
                    if (elements[index] != expected) {
                        return failed(groupId, specs, map, active, location,
                                "entrySet and map view positional reference "
                                        + "identity mismatch at index "
                                        + index);
                    }
                    JsonElement keyExpression =
                            immutableEntryKeyExpression(key);
                    String keySelector = stableMapProjectionKeySelector(
                            keyExpression);
                    if (keyExpression == null || keySelector.isEmpty()) {
                        return failed(groupId, specs, map, active, location,
                                "map entry key at index " + index
                                        + " is not an exact immutable boxed "
                                        + "Z/B/C/S/I/J or String key");
                    }
                    if (!uniqueKeys.add(keySelector)) {
                        return failed(groupId, specs, map, active, location,
                                "immutable map entry key is not unique at "
                                        + "snapshot index " + index);
                    }
                    keyExpressions[index] = copyJsonTree(keyExpression);
                    keySelectors[index] = keySelector;
                }
                for (int index = 0; index < elements.length; index++) {
                    if (keyIdentities.containsKey(elements[index])) {
                        return failed(groupId, specs, map, active, location,
                                "projected value aliases a backing-map key "
                                        + "identity at index " + index);
                    }
                }
            } catch (Throwable throwable) {
                return failed(groupId, specs, map, active, location,
                        "map view snapshot failed: " + rootCause(throwable));
            }

            IdentityHashMap<Object, Boolean> identities =
                    new IdentityHashMap<>();
            long[] elementTokens = new long[elements.length];
            for (int index = 0; index < elements.length; index++) {
                Object element = elements[index];
                if (element == null) {
                    return failed(groupId, specs, map, active, location,
                            "null map element at snapshot index " + index);
                }
                if (identities.put(element, Boolean.TRUE) != null) {
                    return failed(groupId, specs, map, active, location,
                            "one object identity occurs at multiple map-view "
                                    + "indices");
                }
                if (element == map) {
                    return failed(groupId, specs, map, active, location,
                            "map object is also a projected element at index "
                                    + index);
                }
                elementTokens[index] = active.objectToken(element);
            }

            MapProjectionSnapshot snapshot = new MapProjectionSnapshot(
                    groupId, new ArrayList<>(specs), map,
                    active.objectToken(map), elements, elementTokens,
                    keyExpressions, keySelectors, location,
                    active.activation.activationId, true, "");
            snapshot.validateReplayAssignments(active);
            for (MapValueElementProjectionSpec spec : specs) {
                for (int index = 0; index < elements.length; index++) {
                    Object element = elements[index];
                    if (!instanceOfName(element.getClass(),
                            spec.declaredFieldOwnerClass)) {
                        snapshot.fail("map element at index " + index
                                + " is not an instance of demanded field owner "
                                + spec.declaredFieldOwnerClass);
                        return snapshot;
                    }
                    ExactFieldObservation exact = observeExactField(element,
                            spec.declaredFieldSignature);
                    if (!exact.ownerVerified || !exact.typeVerified
                            || !exact.available) {
                        snapshot.fail("exact demanded field reflection failed "
                                + "at index " + index + ": " + exact.error);
                        return snapshot;
                    }
                    if (!uniqueNameResolvesExactDeclaredField(element,
                            spec.declaredFieldSignature)) {
                        snapshot.fail("JDK name-only symbolizeField cannot "
                                + "uniquely resolve exact declared field "
                                + spec.declaredFieldSignature
                                + " at index " + index);
                        return snapshot;
                    }
                    MapProjectionFieldBinding binding =
                            new MapProjectionFieldBinding(active, spec,
                                    snapshot, element, index);
                    List<ModelAssignment> assignments =
                            active.mapProjectionAssignments(binding);
                    if (assignments.size() > 1) {
                        snapshot.fail("multiple exact model assignments target "
                                + binding.dynamicBindingId);
                        return snapshot;
                    }
                    if (!assignments.isEmpty()) {
                        ModelAssignment assignment = assignments.get(0);
                        if (!writeModeledExactField(element,
                                spec.declaredFieldSignature, assignment)) {
                            snapshot.fail("solver model could not be written "
                                    + "to exact map element field at index "
                                    + index);
                            return snapshot;
                        }
                        active.recordModelAssignment(assignment,
                                "MAP_PROJECTION_ENTRY_ELEMENT_FIELD",
                                spec.fieldPath, observeExactField(element,
                                spec.declaredFieldSignature).value);
                    }
                    ExactFieldObservation entryField = observeExactField(
                            element, spec.declaredFieldSignature);
                    if (!entryField.ownerVerified || !entryField.typeVerified
                            || !entryField.available) {
                        snapshot.fail("exact demanded field baseline read "
                                + "failed at index " + index + ": "
                                + entryField.error);
                        return snapshot;
                    }
                    binding.captureEntryValue(active, entryField.value);
                    if (active.engineBacked) {
                        try {
                            api.symbolizeField(element,
                                    spec.declaredFieldName,
                                    binding.dynamicFieldSymbol);
                        } catch (Throwable throwable) {
                            snapshot.fail("map element field symbolize failed "
                                    + "at index " + index + ": "
                                    + rootCause(throwable));
                            return snapshot;
                        }
                        active.symbolized.add(binding.dynamicFieldSymbol);
                    }
                    active.mapProjectionFieldBindings.put(
                            binding.dynamicBindingId, binding);
                    snapshot.bindings.add(binding);
                    JsonObject observation = exactLeafFieldObservation(active,
                            binding.dynamicFieldSymbol, element,
                            spec.declaredFieldSignature,
                            spec.declaredFieldName,
                            "AT_MAP_PROJECTION_ENTRY");
                    observation.addProperty("dynamicBindingId",
                            binding.dynamicBindingId);
                    observation.addProperty("dynamicFieldBindingKind",
                            binding.kind);
                    observation.add("mapProjectionSelector",
                            binding.selectorJson());
                    active.fieldObservations.add(observation);
                }
            }
            return snapshot;
        }

        private static MapProjectionSnapshot failed(
                String groupId, List<MapValueElementProjectionSpec> specs,
                Object map, ActiveRegion active, String location,
                String problem) {
            return new MapProjectionSnapshot(groupId,
                    new ArrayList<>(specs), map, active.objectToken(map),
                    new Object[0], new long[0], new JsonElement[0],
                    new String[0], location,
                    active.activation.activationId, false, problem);
        }

        /**
         * Resolves replay assignments by immutable key first.  The recorded
         * source index is only admitted after the key has a unique current
         * entry and that entry remains at the same map-view position.
         */
        private void validateReplayAssignments(ActiveRegion active) {
            for (ModelAssignment assignment
                    : active.activation.modelAssignments) {
                MapValueElementProjectionSpec selected = null;
                for (MapValueElementProjectionSpec spec : specs) {
                    if (!assignment.targetsMapProjection(spec)) continue;
                    if (selected != null) {
                        fail("one replay assignment targets multiple map "
                                + "projection declarations");
                        selected = null;
                        break;
                    }
                    selected = spec;
                }
                if (selected == null) continue;
                expectedMapKeyAssignmentCount++;
                int currentIndex = uniqueIndexForExpectedKey(assignment);
                if (currentIndex < 0) {
                    fail("replay expected immutable map key is absent, "
                            + "ambiguous, or malformed for "
                            + assignment.engineSymbol);
                    continue;
                }
                if (currentIndex != assignment.mapProjectionOutputIndex) {
                    fail("replay immutable map key resolved to current index "
                            + currentIndex + " but source output index was "
                            + assignment.mapProjectionOutputIndex);
                    continue;
                }
                if (!assignment.validMapProjectionReplaySelector(selected,
                        this, currentIndex)) {
                    fail("replay keyed map/output selector is incomplete or "
                            + "does not authorize the current activation for "
                            + assignment.engineSymbol);
                    continue;
                }
                if (authorizedReplayIndices.put(assignment.key,
                        currentIndex) != null) {
                    fail("duplicate replay assignment identity for keyed map "
                            + "projection " + assignment.engineSymbol);
                    continue;
                }
                expectedMapKeyValidatedCount++;
            }
        }

        private int uniqueIndexForExpectedKey(ModelAssignment assignment) {
            String expected = stableMapProjectionKeySelector(
                    assignment.mapProjectionExpectedMapKey);
            if (expected.isEmpty()) return -1;
            int selected = -1;
            for (int index = 0; index < entryKeySelectors.length; index++) {
                if (!expected.equals(entryKeySelectors[index])) continue;
                if (selected >= 0) return -1;
                selected = index;
            }
            return selected;
        }

        private boolean replayAuthorized(ModelAssignment assignment,
                                         int outputIndex) {
            Integer selected = authorizedReplayIndices.get(assignment.key);
            return selected != null && selected == outputIndex;
        }

        private void fail(String detail) {
            complete = false;
            outputIdentityVerified = false;
            problem = appendReason(problem, detail);
            for (MapProjectionFieldBinding binding : bindings) {
                binding.outputIdentityVerified = false;
                binding.complete = false;
            }
        }

        private JsonObject entryObservation() {
            JsonObject row = baseObservation("ENTRY_SNAPSHOT");
            row.addProperty("snapshotElementCount", elements.length);
            JsonArray tokens = new JsonArray();
            for (long token : elementObjectTokens) {
                tokens.add(new JsonPrimitive(Long.valueOf(token)));
            }
            row.add("snapshotElementObjectTokens", tokens);
            JsonArray keys = new JsonArray();
            for (JsonElement key : entryKeyExpressions) {
                keys.add(copyJsonTree(key));
            }
            row.add("snapshotEntryKeyExpressions", keys);
            row.addProperty("entryKeyExpressionAuthority",
                    "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
            row.addProperty("expectedMapKeyAssignmentCount",
                    expectedMapKeyAssignmentCount);
            row.addProperty("expectedMapKeyValidatedCount",
                    expectedMapKeyValidatedCount);
            row.addProperty("expectedMapKeyAndSourceIndexValidated",
                    expectedMapKeyAssignmentCount
                            == expectedMapKeyValidatedCount);
            row.addProperty("entrySnapshotComplete", complete);
            return row;
        }

        private JsonObject verifyOutput(ActiveRegion active, Object candidate,
                                        String authority,
                                        boolean candidateIsProjectedValue) {
            JsonObject row = baseObservation("OUTPUT_IDENTITY_VALIDATION");
            Object array;
            String[] outputField = specs.isEmpty() ? null
                    : declaredField(specs.get(0).outputCell);
            if (!candidateIsProjectedValue && outputField != null) {
                ExactFieldObservation exact = observeExactField(candidate,
                        specs.get(0).outputCell);
                row.addProperty("outputDeclaredFieldOwnerVerified",
                        exact.ownerVerified);
                row.addProperty("outputDeclaredFieldTypeVerified",
                        exact.typeVerified);
                if (!exact.ownerVerified || !exact.typeVerified
                        || !exact.available) {
                    fail("exact producer output field reflection failed: "
                            + exact.error);
                    array = MissingValue.INSTANCE;
                } else {
                    array = exact.value;
                }
            } else {
                array = projectedArray(candidate,
                        candidateIsProjectedValue);
            }
            if (array == MissingValue.INSTANCE || array == null
                    || !array.getClass().isArray()
                    || array.getClass().getComponentType().isPrimitive()) {
                fail("producer output is not the declared non-null object "
                        + "array projection");
            } else if (Array.getLength(array) != elements.length) {
                fail("producer output array length " + Array.getLength(array)
                        + " differs from entry snapshot " + elements.length);
            } else {
                for (int index = 0; index < elements.length; index++) {
                    if (Array.get(array, index) != elements[index]) {
                        fail("producer output element identity mismatch at "
                                + "index " + index);
                        break;
                    }
                }
            }
            int outputFieldValueVerifiedCount = 0;
            if (complete && array != null && array != MissingValue.INSTANCE) {
                for (MapProjectionFieldBinding binding : bindings) {
                    Object outputElement = Array.get(array,
                            binding.outputIndex);
                    if (!binding.verifyUnmodifiedOutputField(active,
                            outputElement)) {
                        fail("projected exact field was assigned or changed "
                                + "between entry snapshot and output at index "
                                + binding.outputIndex + ": "
                                + binding.spec.declaredFieldSignature);
                        break;
                    }
                    outputFieldValueVerifiedCount++;
                }
            }
            if (complete && array != null && array != MissingValue.INSTANCE) {
                long candidateToken = active.objectToken(array);
                if (candidateToken <= 0L || candidateToken == mapObjectToken) {
                    fail("producer output array token is missing or aliases "
                            + "the backing map token");
                }
                for (long elementToken : elementObjectTokens) {
                    if (candidateToken == elementToken) {
                        fail("producer output array token aliases a projected "
                                + "element token");
                        break;
                    }
                }
                outputArrayObjectToken = candidateToken;
            }
            if (complete && outputArrayObjectToken > 0L) {
                outputIdentityVerified = true;
                outputVerificationAuthority = safe(authority);
                for (MapProjectionFieldBinding binding : bindings) {
                    binding.outputArrayObjectToken = outputArrayObjectToken;
                    binding.outputIdentityVerified = true;
                    binding.outputVerificationAuthority =
                            outputVerificationAuthority;
                    binding.complete = true;
                }
            }
            row.addProperty("outputIdentityVerified",
                    outputIdentityVerified);
            row.addProperty("outputArrayObjectToken",
                    outputArrayObjectToken);
            row.addProperty("outputVerificationAuthority",
                    outputVerificationAuthority);
            row.addProperty("projectedFieldBindingCount", bindings.size());
            row.addProperty("outputFieldValueVerifiedCount",
                    outputFieldValueVerifiedCount);
            row.addProperty("outputFieldValueFlowVerified",
                    complete && outputFieldValueVerifiedCount
                    == bindings.size() && !bindings.isEmpty());
            row.addProperty("fieldValueFlowAuthority",
                    complete && outputFieldValueVerifiedCount
                    == bindings.size() && !bindings.isEmpty()
                            ? MAP_PROJECTION_FIELD_VALUE_AUTHORITY : "");
            row.addProperty("complete", complete
                    && outputIdentityVerified);
            if (!problem.isEmpty()) row.addProperty("problem", problem);
            return row;
        }

        private Object projectedArray(Object candidate,
                                      boolean candidateIsProjectedValue) {
            if (candidate == null || candidate == MissingValue.INSTANCE) {
                return candidate;
            }
            if (candidateIsProjectedValue) return candidate;
            List<String> path = specs.isEmpty()
                    ? Collections.<String>emptyList()
                    : specs.get(0).outputFieldPath;
            if (path.isEmpty()) return candidate;
            Object current = candidate;
            for (String field : path) {
                current = readField(current, field);
                if (current == null || current == MissingValue.INSTANCE) {
                    return current;
                }
            }
            return current;
        }

        private JsonObject baseObservation(String phase) {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind", "MAP_VALUE_OUTPUT_ARRAY_PROJECTION");
            row.addProperty("phase", phase);
            row.addProperty("groupId", groupId);
            row.addProperty("mapInputPort", specs.isEmpty() ? ""
                    : specs.get(0).mapInputPort);
            row.addProperty("outputPort", specs.isEmpty() ? ""
                    : specs.get(0).outputPort);
            row.addProperty("outputCell", specs.isEmpty() ? ""
                    : specs.get(0).outputCell);
            row.addProperty("mapProjectionOperation", specs.isEmpty() ? ""
                    : specs.get(0).mapProjectionOperation);
            row.addProperty("mapObjectToken", mapObjectToken);
            row.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            row.addProperty("objectTokenScope", objectTokenScope);
            row.addProperty("inputObservationLocation", location);
            row.addProperty("mapImplementationClass",
                    mapImplementationClass);
            row.addProperty("mapImplementationAuthority",
                    mapImplementationAuthority);
            row.addProperty("crossExecutionOrdinalAuthority", "NONE");
            row.addProperty("identityPolicy",
                    "ENTRYSET_KEY_AND_MAP_VIEW_ELEMENT_SAME_EXECUTION_"
                            + "POSITIONAL_REFERENCE_EQUALITY");
            row.addProperty("entrySetViewOrderVerified",
                    entrySetViewOrderVerified);
            row.addProperty("entrySetViewOrderAuthority",
                    "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                            + "POSITIONAL_REFERENCE_EQUALITY");
            row.addProperty("complete", complete);
            if (!problem.isEmpty()) row.addProperty("problem", problem);
            return row;
        }
    }

    private static final class MapProjectionFieldBinding {
        private static final String KIND =
                "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING";
        private static final String AUTHORITY =
                "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                        + "EXACT_OUTPUT_IDENTITY";

        private final int schemaVersion = 3;
        private final String kind = KIND;
        private final MapValueElementProjectionSpec spec;
        private final MapProjectionSnapshot snapshot;
        private final String dynamicBindingId;
        private final String baseInputSymbol;
        private final String dynamicFieldSymbol;
        private final String materializationSiteId;
        private final int materializationOccurrence;
        private final String fieldSignature;
        private final List<String> fieldPath;
        private final int outputIndex;
        private final long mapObjectToken;
        private final long elementObjectToken;
        private final Object elementOwner;
        private final String objectTokenScope;
        private final JsonElement expectedMapKey;
        private Object entryConcreteFieldValue;
        private long entryExactFieldWriteCount;
        private boolean entryConcreteFieldValueCaptured;
        private boolean noInterveningFieldWriteVerified;
        private boolean outputFieldValueVerified;
        private String fieldValueFlowAuthority = "";
        private boolean outputIdentityVerified;
        private long outputArrayObjectToken;
        private String outputVerificationAuthority = "";
        private boolean complete;

        private MapProjectionFieldBinding(
                ActiveRegion active, MapValueElementProjectionSpec spec,
                MapProjectionSnapshot snapshot, Object element,
                int outputIndex) {
            this.spec = spec;
            this.snapshot = snapshot;
            this.baseInputSymbol = spec.mapInputPort;
            this.materializationSiteId = spec.materializationSiteId();
            this.materializationOccurrence = outputIndex + 1;
            this.dynamicFieldSymbol = dynamicFieldSymbolForTests(
                    baseInputSymbol, materializationSiteId,
                    materializationOccurrence);
            this.dynamicBindingId = "DYNAMIC_FIELD:"
                    + dynamicFieldSymbol;
            this.fieldSignature = spec.declaredFieldSignature;
            this.fieldPath = new ArrayList<>(spec.fieldPath);
            this.outputIndex = outputIndex;
            this.mapObjectToken = snapshot.mapObjectToken;
            this.elementObjectToken = active.objectToken(element);
            this.elementOwner = element;
            this.objectTokenScope = active.activation.activationId;
            this.expectedMapKey = copyJsonTree(
                    snapshot.entryKeyExpressions[outputIndex]);
        }

        private void captureEntryValue(ActiveRegion active, Object value) {
            this.entryConcreteFieldValue = value;
            this.entryExactFieldWriteCount = active.observedFieldWriteCount(
                    elementOwner, spec.declaredFieldSignature);
            this.entryConcreteFieldValueCaptured = true;
        }

        private boolean verifyUnmodifiedOutputField(ActiveRegion active,
                                                    Object outputElement) {
            noInterveningFieldWriteVerified = outputElement == elementOwner
                    && active.observedFieldWriteCount(outputElement,
                    spec.declaredFieldSignature)
                    == entryExactFieldWriteCount;
            ExactFieldObservation output = observeExactField(outputElement,
                    spec.declaredFieldSignature);
            boolean sameValue = output.ownerVerified && output.typeVerified
                    && output.available && entryConcreteFieldValueCaptured
                    && active.objectToken(outputElement)
                    == elementObjectToken
                    && sameExactFieldValue(entryConcreteFieldValue,
                    output.value, output.fieldType);
            outputFieldValueVerified = noInterveningFieldWriteVerified
                    && sameValue;
            fieldValueFlowAuthority = outputFieldValueVerified
                    ? MAP_PROJECTION_FIELD_VALUE_AUTHORITY : "";
            return outputFieldValueVerified;
        }

        private JsonObject selectorJson() {
            JsonObject selector = new JsonObject();
            selector.addProperty("kind", "MAP_OUTPUT_ARRAY_INDEX");
            selector.addProperty("bindingId", spec.bindingId);
            selector.addProperty("mapInputPort", spec.mapInputPort);
            selector.addProperty("mapInputCell", spec.mapInputCell);
            selector.addProperty("outputPort", spec.outputPort);
            selector.addProperty("outputCell", spec.outputCell);
            selector.addProperty("mapProjectionOperation",
                    spec.mapProjectionOperation);
            selector.addProperty("outputIndex", outputIndex);
            selector.addProperty("elementOccurrence",
                    materializationOccurrence);
            selector.addProperty("declaredFieldOwnerClass",
                    spec.declaredFieldOwnerClass);
            selector.addProperty("declaredFieldType",
                    spec.declaredFieldType);
            selector.addProperty("declaredFieldSignature",
                    spec.declaredFieldSignature);
            selector.addProperty("mapObjectToken", mapObjectToken);
            selector.addProperty("elementObjectToken", elementObjectToken);
            selector.addProperty("outputArrayObjectToken",
                    outputArrayObjectToken);
            selector.addProperty("outputIdentityVerified",
                    outputIdentityVerified);
            selector.addProperty("outputVerificationAuthority",
                    outputVerificationAuthority);
            selector.addProperty("mapImplementationClass",
                    snapshot.mapImplementationClass);
            selector.addProperty("mapImplementationAuthority",
                    snapshot.mapImplementationAuthority);
            selector.addProperty("entryConcreteFieldValueCaptured",
                    entryConcreteFieldValueCaptured);
            selector.addProperty("noInterveningFieldWriteVerified",
                    noInterveningFieldWriteVerified);
            selector.addProperty("outputFieldValueVerified",
                    outputFieldValueVerified);
            selector.addProperty("fieldValueFlowAuthority",
                    fieldValueFlowAuthority);
            selector.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            selector.addProperty("objectTokenScope", objectTokenScope);
            selector.addProperty("crossExecutionOrdinalAuthority", "NONE");
            selector.add("expectedMapKey", copyJsonTree(expectedMapKey));
            selector.addProperty("expectedMapKeyAuthority",
                    "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
            selector.addProperty("sourceOutputIndexAuthority",
                    "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                            + "POSITIONAL_REFERENCE_EQUALITY");
            selector.addProperty("replaySelectionAuthority",
                    "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_AND_"
                            + "EXACT_OUTPUT_IDENTITY");
            selector.addProperty("authority", AUTHORITY);
            selector.addProperty("complete", complete);
            return selector;
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", schemaVersion);
            result.addProperty("kind", kind);
            result.addProperty("dynamicBindingId", dynamicBindingId);
            result.addProperty("baseInputSymbol", baseInputSymbol);
            result.addProperty("dynamicFieldSymbol", dynamicFieldSymbol);
            result.addProperty("materializationSiteId",
                    materializationSiteId);
            result.addProperty("materializationOccurrence",
                    materializationOccurrence);
            result.addProperty("fieldSignature", fieldSignature);
            result.add("fieldPath", GSON.toJsonTree(fieldPath));
            result.addProperty("leafOwnerObjectToken",
                    elementObjectToken);
            result.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            result.addProperty("objectTokenScope", objectTokenScope);
            result.add("mapProjectionSelector", selectorJson());
            result.addProperty("authority", AUTHORITY);
            result.addProperty("complete", complete);
            return result;
        }
    }

    /**
     * One-shot evidence spanning the model-preparation hook and the single
     * real JVM getfield that follows it.  The owner is already the exact leaf
     * owner; no logical root path is traversed from this object.
     */
    private static final class PendingArrayFieldMaterialization {
        private final String method;
        private final int unitIndex;
        private final String siteId;
        private final SymbolizeAction action;
        private final Object leafOwner;
        private final String leafFieldSignature;
        private final String leafFieldName;
        private final List<String> logicalFieldPath;
        private final Object expectedReference;
        private final long expectedObjectToken;
        private final DeclaredArrayInputType declaredType;

        private PendingArrayFieldMaterialization(
                String method, int unitIndex, SymbolizeAction action,
                Object leafOwner, String leafFieldSignature,
                String leafFieldName, List<String> logicalFieldPath,
                Object expectedReference,
                long expectedObjectToken,
                DeclaredArrayInputType declaredType) {
            this.method = safe(method);
            this.unitIndex = unitIndex;
            this.siteId = siteId(method, unitIndex);
            this.action = action;
            this.leafOwner = leafOwner;
            this.leafFieldSignature = safe(leafFieldSignature);
            this.leafFieldName = safe(leafFieldName);
            this.logicalFieldPath = new ArrayList<>(logicalFieldPath);
            this.expectedReference = expectedReference;
            this.expectedObjectToken = expectedObjectToken;
            this.declaredType = declaredType;
        }

        private boolean matches(String actualMethod, int actualUnitIndex,
                                Object actualOwner,
                                String actualFieldSignature,
                                String actualFieldName) {
            return method.equals(safe(actualMethod))
                    && unitIndex == actualUnitIndex
                    && leafOwner == actualOwner
                    && leafFieldSignature.equals(safe(
                    actualFieldSignature))
                    && leafFieldName.equals(safe(actualFieldName));
        }
    }

    /** One immutable frame in the activation-local accessor call stack. */
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

    private static final class VmBranchEventAttestation {
        private final JsonObject event;
        private final String authority;
        private final int conditionIndex;
        private final boolean valid;
        private final String error;

        private VmBranchEventAttestation(JsonObject event, String authority,
                                         int conditionIndex, boolean valid,
                                         String error) {
            this.event = event;
            this.authority = safe(authority);
            this.conditionIndex = conditionIndex;
            this.valid = valid;
            this.error = safe(error);
        }

        private static VmBranchEventAttestation valid(
                JsonObject event, String authority, int conditionIndex) {
            return new VmBranchEventAttestation(event, authority,
                    conditionIndex, true, "");
        }

        private static VmBranchEventAttestation invalid(
                JsonObject event, String authority, String error) {
            return new VmBranchEventAttestation(event, authority,
                    -1, false, error);
        }
    }

    private static final class PreparedBranch {
        private final long handle;
        private final String method;
        private final int unitIndex;
        private final String expression;
        private final String siteId;
        private final int occurrence;

        private PreparedBranch(long handle, String method, int unitIndex,
                               String expression, String siteId,
                               int occurrence) {
            this.handle = handle;
            this.method = safe(method);
            this.unitIndex = unitIndex;
            this.expression = safe(expression);
            this.siteId = safe(siteId);
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
        private final Activation activation;
        private final Object receiver;
        private final Thread thread;
        private final long startNanos;
        private final boolean engineBacked;
        private final AtomicBoolean finished = new AtomicBoolean();
        private final List<String> symbolized = new ArrayList<>();
        private final List<String> unresolved = new ArrayList<>();
        private final Set<String> unresolvedUnique = new LinkedHashSet<>();
        private final List<JsonObject> branchMappings = new ArrayList<>();
        private final List<JsonObject> runtimeHeapEffects = new ArrayList<>();
        private final List<JsonObject> runtimeHeapObservations =
                new ArrayList<>();
        private final List<JsonObject> finiteMapSnapshots =
                new ArrayList<>();
        private final Set<String> finiteMapSnapshotIdentities =
                new LinkedHashSet<>();
        private final IdentityHashMap<Object, Boolean>
                finiteMapSnapshotAttemptedMaps = new IdentityHashMap<>();
        private final List<JsonObject> replayMaterializationsApplied =
                new ArrayList<>();
        private final List<JsonObject> modelAssignmentsApplied =
                new ArrayList<>();
        private final List<JsonObject> fieldObservations = new ArrayList<>();
        private final List<JsonObject> outputCaptures = new ArrayList<>();
        private final Map<String, FieldObservationTarget> fieldTargets =
                new LinkedHashMap<>();
        private final Map<String, DynamicFieldBinding> dynamicFieldBindings =
                new LinkedHashMap<>();
        private final Map<String, MapProjectionFieldBinding>
                mapProjectionFieldBindings = new LinkedHashMap<>();
        private final Map<String, MapProjectionSnapshot>
                mapProjectionSnapshots = new LinkedHashMap<>();
        private final List<JsonObject> mapProjectionObservations =
                new ArrayList<>();
        private final IdentityHashMap<Object, Map<String, Long>>
                observedFieldWrites = new IdentityHashMap<>();
        private final List<EngineArrayInputBinding>
                engineArrayInputBindings = new ArrayList<>();
        private final Map<String, EngineArrayInputBinding>
                engineArrayInputByPort = new LinkedHashMap<>();
        private final Map<String, EngineArrayInputBinding>
                engineArrayInputByEngineId = new LinkedHashMap<>();
        private final IdentityHashMap<Object,
                Map<String, DynamicFieldBinding>> dynamicFieldsByOwner =
                new IdentityHashMap<>();
        private final Set<String> materialized = new LinkedHashSet<>();
        private final Set<String> appliedModelAssignments =
                new LinkedHashSet<>();
        private final Map<String, Integer> branchOccurrences =
                new LinkedHashMap<>();
        private final Map<Long, PreparedBranch> preparedBranches =
                new LinkedHashMap<>();
        private final Map<String, Integer> replayOccurrences =
                new LinkedHashMap<>();
        private final Map<String, Integer> heapEffectOccurrences =
                new LinkedHashMap<>();
        private final Map<String, Integer> heapObservationOccurrences =
                new LinkedHashMap<>();
        private final Map<String, Integer> finiteMapSnapshotOccurrences =
                new LinkedHashMap<>();
        private final Map<String, Integer> fieldMaterializationOccurrences =
                new LinkedHashMap<>();
        private final Map<String, Integer> actualFieldHookOccurrences =
                new LinkedHashMap<>();
        private final Map<String, Integer> outputCaptureOccurrences =
                new LinkedHashMap<>();
        private final IdentityHashMap<Object, MapViewBinding> mapViews =
                new IdentityHashMap<>();
        private final IdentityHashMap<Object, MapIteratorCursor> mapIterators =
                new IdentityHashMap<>();
        private final Map<String, ContainerInputObservation> containerInputs =
                new LinkedHashMap<>();
        private final Map<String, Object> logicalArrayRootsByPort =
                new LinkedHashMap<>();
        private final Map<String, String> logicalArrayRootAuthoritiesByPort =
                new LinkedHashMap<>();
        private final IdentityHashMap<Object, Long> objectTokens =
                new IdentityHashMap<>();
        private long nextObjectToken = 1L;
        private long runtimeEventSequence;
        private long preparedBranchSequence;
        private int lastPathConditionSize;
        private PendingArrayFieldMaterialization
                pendingArrayFieldMaterialization;
        private final Set<String> preparedArrayInputPorts =
                new LinkedHashSet<>();

        private ActiveRegion(long token, Activation activation, Object receiver,
                             Thread thread, long startNanos) {
            this.token = token;
            this.activation = activation;
            this.receiver = receiver;
            this.thread = thread;
            this.startNanos = startNanos;
            this.engineBacked = !activation.concreteReplayOnly;
            registerReceiverArrayRoots();
        }

        private void registerReceiverArrayRoots() {
            if (receiver == null) return;
            for (SymbolizeAction action : activation.symbolize) {
                if ("ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_LOGICAL_"
                        .concat("PATH_PREFIX_REFERENCE_EQUALITY").equals(
                                action.consumedFieldRootAuthority)) {
                    registerLogicalArrayRoot(action, receiver,
                            action.consumedFieldRootAuthority);
                }
            }
        }

        private void registerLogicalArrayRoot(SymbolizeAction action,
                                              Object root,
                                              String authority) {
            if (action == null || root == null || action.symbol.isEmpty()) {
                return;
            }
            Object previous = logicalArrayRootsByPort.get(action.symbol);
            if (previous != null && previous != root) {
                addUnresolvedOnce(action.symbol
                        + ": ARRAY_VALUE_LOGICAL_ROOT_AMBIGUOUS");
                logicalArrayRootsByPort.remove(action.symbol);
                logicalArrayRootAuthoritiesByPort.remove(action.symbol);
                return;
            }
            logicalArrayRootsByPort.put(action.symbol, root);
            logicalArrayRootAuthoritiesByPort.put(action.symbol,
                    safe(authority));
        }

        private boolean logicalLeafOwnerVerified(
                SymbolizeAction action, Object actualLeafOwner,
                List<String> logicalPath) {
            if ("DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_OWNER_V1"
                    .equals(action.consumedFieldRootAuthority)) {
                // This authority is emitted only after the planner has joined
                // one exact static leaf getfield to one runtime FIELD_READ in
                // this region instance.  The hook argument is the base used
                // by that real getfield, so no earlier logical root exists to
                // register.  Restrict it to a direct one-segment leaf; nested
                // paths still require argument/receiver/local root identity.
                return actualLeafOwner != null && logicalPath != null
                        && logicalPath.size() == 1;
            }
            Object root = logicalArrayRootsByPort.get(action.symbol);
            String authority = logicalArrayRootAuthoritiesByPort.get(
                    action.symbol);
            if (root == null || logicalPath == null
                    || logicalPath.isEmpty()
                    || !safe(action.consumedFieldRootAuthority).equals(
                    safe(authority))) {
                return false;
            }
            if (logicalPath.size() == 1) {
                return root == actualLeafOwner;
            }
            return resolveFieldPathLeafOwner(root, logicalPath)
                    == actualLeafOwner;
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
            String siteId = safe(method) + "#u" + unitIndex;
            if (!api.exactBranchEventsAvailable()) {
                addUnresolvedOnce(siteId
                        + ": custom JDK exact branch-event API is required");
                return null;
            }
            int occurrence = nextBranchOccurrence(siteId);
            long sequence = ++preparedBranchSequence;
            if (sequence > Integer.MAX_VALUE) {
                addUnresolvedOnce(siteId + "#" + occurrence
                        + ": prepared branch sequence overflow");
                return null;
            }
            // The complete value is an activation-local unique handle.  Its
            // low 32 bits deliberately carry the real per-site occurrence so
            // transformed bytecode can pass that value to the native marker
            // with a single long-to-int cast and no intervening Java call.
            long handle = (sequence << 32)
                    | (occurrence & 0xffffffffL);
            PreparedBranch prepared = new PreparedBranch(handle, method,
                    unitIndex, expression, siteId, occurrence);
            preparedBranches.put(handle, prepared);
            return prepared;
        }

        private PreparedBranch takePreparedBranch(long handle) {
            return handle <= 0L ? null : preparedBranches.remove(handle);
        }

        private int nextReplayOccurrence(String siteId) {
            Integer previous = replayOccurrences.get(siteId);
            int occurrence = previous == null ? 1 : previous + 1;
            replayOccurrences.put(siteId, occurrence);
            return occurrence;
        }

        private int nextHeapEffectOccurrence(String siteId) {
            Integer previous = heapEffectOccurrences.get(siteId);
            int occurrence = previous == null ? 1 : previous + 1;
            heapEffectOccurrences.put(siteId, occurrence);
            return occurrence;
        }

        private int nextHeapObservationOccurrence(String siteId) {
            Integer previous = heapObservationOccurrences.get(siteId);
            int occurrence = previous == null ? 1 : previous + 1;
            heapObservationOccurrences.put(siteId, occurrence);
            return occurrence;
        }

        private int nextFiniteMapSnapshotOccurrence(String siteId) {
            Integer previous = finiteMapSnapshotOccurrences.get(siteId);
            int occurrence = previous == null ? 1 : previous + 1;
            finiteMapSnapshotOccurrences.put(siteId, occurrence);
            return occurrence;
        }

        private JsonArray runtimeHeapObservationsJson() {
            JsonArray result = new JsonArray();
            for (JsonObject observation : runtimeHeapObservations) {
                result.add(copyJsonTree(observation));
            }
            // Keep legacy per-entry rows in their original order.  Finite
            // snapshots carry an eventSequence tied to their first next hook,
            // so consumers must use that field rather than array position.
            for (JsonObject snapshot : finiteMapSnapshots) {
                result.add(copyJsonTree(snapshot));
            }
            return result;
        }

        private int nextFieldMaterializationOccurrence(String baseSymbol,
                                                       String siteId) {
            String key = safe(baseSymbol) + "\n" + safe(siteId);
            Integer previous = fieldMaterializationOccurrences.get(key);
            int occurrence = previous == null ? 1 : previous + 1;
            fieldMaterializationOccurrences.put(key, occurrence);
            return occurrence;
        }

        private int nextActualFieldHookOccurrence(String baseSymbol,
                                                  String siteId) {
            String key = safe(baseSymbol) + "\n" + safe(siteId);
            Integer previous = actualFieldHookOccurrences.get(key);
            int occurrence = previous == null ? 1 : previous + 1;
            actualFieldHookOccurrences.put(key, occurrence);
            return occurrence;
        }

        private int nextOutputCaptureOccurrence(String captureBindingId) {
            String key = safe(captureBindingId);
            Integer previous = outputCaptureOccurrences.get(key);
            int occurrence = previous == null ? 1 : previous + 1;
            outputCaptureOccurrences.put(key, occurrence);
            return occurrence;
        }

        private void addUnresolvedOnce(String detail) {
            String value = safe(detail);
            if (!value.isEmpty() && unresolvedUnique.add(value)) {
                unresolved.add(value);
            }
        }

        private void captureEngineArrayInputBinding(
                SymbolizeAction action, Object symbolizedValue,
                Object postReadValue, long symbolizationToken,
                DeclaredArrayInputType declaredType, String location,
                EngineApi api) {
            if (!engineBacked) {
                return;
            }
            EngineArrayInputBinding candidate =
                    EngineArrayInputBinding.capture(this, action,
                            symbolizedValue, postReadValue,
                            symbolizationToken, declaredType, location, api);
            EngineArrayInputBinding samePort = engineArrayInputByPort.get(
                    candidate.inputPort);
            if (samePort != null) {
                if (samePort.arrayObjectToken
                        != candidate.arrayObjectToken
                        || !samePort.engineArrayId.equals(
                        candidate.engineArrayId)) {
                    samePort.fail("one input port was observed with more "
                            + "than one live array token or VM array id");
                    addUnresolvedOnce(candidate.inputPort
                            + ": engine-array input binding is ambiguous: "
                            + samePort.problem);
                }
                return;
            }

            if (!candidate.engineArrayId.isEmpty()) {
                EngineArrayInputBinding sameId =
                        engineArrayInputByEngineId.get(
                                candidate.engineArrayId);
                if (sameId != null && (!sameId.inputPort.equals(
                        candidate.inputPort) || sameId.arrayObjectToken
                        != candidate.arrayObjectToken)) {
                    sameId.fail("one VM engine array id resolved to a "
                            + "different input port or activation-local "
                            + "object token");
                    candidate.fail("one VM engine array id resolved to a "
                            + "different input port or activation-local "
                            + "object token");
                    addUnresolvedOnce(candidate.engineArrayId
                            + ": VM array id aliases distinct live arrays");
                } else if (sameId == null) {
                    engineArrayInputByEngineId.put(candidate.engineArrayId,
                            candidate);
                }
            }
            engineArrayInputByPort.put(candidate.inputPort, candidate);
            engineArrayInputBindings.add(candidate);
            if (!candidate.complete) {
                addUnresolvedOnce(candidate.inputPort
                        + ": engine-array input binding failed closed: "
                        + candidate.problem);
            }
        }

        private void captureDynamicEngineArrayInputBinding(
                SymbolizeAction action, DynamicFieldBinding dynamicBinding,
                Object symbolizedValue, Object postReadValue,
                long symbolizationToken,
                DeclaredArrayInputType declaredType, String location,
                EngineApi api) {
            if (!engineBacked || dynamicBinding == null) return;
            EngineArrayInputBinding candidate =
                    EngineArrayInputBinding.capture(this, action,
                            symbolizedValue, postReadValue,
                            symbolizationToken, declaredType, location,
                            dynamicBinding.dynamicFieldSymbol, action.cell,
                            dynamicBinding, api);
            EngineArrayInputBinding samePort = engineArrayInputByPort.get(
                    candidate.inputPort);
            if (samePort != null) {
                if (samePort.arrayObjectToken
                        != candidate.arrayObjectToken
                        || !samePort.engineArrayId.equals(
                        candidate.engineArrayId)) {
                    samePort.fail("one dynamic input port was observed with "
                            + "more than one live array token or VM array id");
                    addUnresolvedOnce(candidate.inputPort
                            + ": engine-array input binding is ambiguous: "
                            + samePort.problem);
                }
                return;
            }
            if (!candidate.engineArrayId.isEmpty()) {
                EngineArrayInputBinding sameId =
                        engineArrayInputByEngineId.get(
                                candidate.engineArrayId);
                if (sameId != null && (!sameId.inputPort.equals(
                        candidate.inputPort) || sameId.arrayObjectToken
                        != candidate.arrayObjectToken)) {
                    sameId.fail("one VM engine array id resolved to a "
                            + "different dynamic input or object token");
                    candidate.fail("one VM engine array id resolved to a "
                            + "different dynamic input or object token");
                    addUnresolvedOnce(candidate.engineArrayId
                            + ": VM array id aliases distinct live arrays");
                } else if (sameId == null) {
                    engineArrayInputByEngineId.put(candidate.engineArrayId,
                            candidate);
                }
            }
            engineArrayInputByPort.put(candidate.inputPort, candidate);
            engineArrayInputBindings.add(candidate);
            if (!candidate.complete) {
                addUnresolvedOnce(candidate.inputPort
                        + ": engine-array input binding failed closed: "
                        + candidate.problem);
            }
        }

        private JsonArray engineArrayInputBindingsJson() {
            JsonArray result = new JsonArray();
            for (EngineArrayInputBinding binding
                    : engineArrayInputBindings) {
                result.add(binding.toJson());
            }
            return result;
        }

        private void observeMapProjectionInput(SymbolizeAction action,
                                               Object value,
                                               String location) {
            List<MapValueElementProjectionSpec> declared = activation
                    .mapProjectionsForInput(action.symbol);
            if (declared.isEmpty()) {
                return;
            }
            EngineApi api = engineBacked ? engine() : null;
            boolean paused = false;
            try {
                // This snapshot is input materialization, not program logic.
                // It must happen before producer execution while all identity,
                // reflection and collection traversal is excluded from the PC.
                if (api != null) {
                    api.pausePathCondition();
                    paused = true;
                }
                Map<String, List<MapValueElementProjectionSpec>> groups =
                        new LinkedHashMap<>();
                for (MapValueElementProjectionSpec spec : declared) {
                    String error = spec.validationError(activation, action);
                    if (!error.isEmpty()) {
                        addUnresolvedOnce(spec.bindingId
                                + ": map/output element projection failed "
                                + "closed: " + error);
                        continue;
                    }
                    groups.computeIfAbsent(spec.groupId(), ignored ->
                            new ArrayList<>()).add(spec);
                }
                for (Map.Entry<String,
                        List<MapValueElementProjectionSpec>> group
                        : groups.entrySet()) {
                    MapProjectionSnapshot existing =
                            mapProjectionSnapshots.get(group.getKey());
                    if (existing != null) {
                        if (existing.map != value) {
                            existing.fail("more than one backing Map instance "
                                    + "was observed for one projection");
                            addUnresolvedOnce(existing.groupId
                                    + ": backing Map input is ambiguous");
                        }
                        continue;
                    }
                    MapProjectionSnapshot snapshot =
                            MapProjectionSnapshot.create(this, action,
                                    group.getValue(), value, location, api);
                    mapProjectionSnapshots.put(group.getKey(), snapshot);
                    mapProjectionObservations.add(snapshot.entryObservation());
                    if (!snapshot.complete) {
                        addUnresolvedOnce(snapshot.groupId + ": "
                                + snapshot.problem);
                    }
                }
            } catch (Throwable throwable) {
                addUnresolvedOnce(action.symbol
                        + ": map/output element entry snapshot failed: "
                        + rootCause(throwable));
            } finally {
                if (paused) {
                    try {
                        api.resumePathCondition();
                    } catch (Throwable throwable) {
                        addUnresolvedOnce(action.symbol
                                + ": map projection PC resume failed: "
                                + rootCause(throwable));
                    }
                }
            }
        }

        private JsonArray verifyMapProjectionOutput(
                String outputPort, String outputCell, Object candidate,
                String authority) {
            JsonArray rows = new JsonArray();
            for (MapProjectionSnapshot snapshot
                    : mapProjectionSnapshots.values()) {
                if (snapshot.specs.isEmpty()) continue;
                MapValueElementProjectionSpec spec = snapshot.specs.get(0);
                if (!spec.outputPort.equals(safe(outputPort))
                        || !spec.outputCell.equals(safe(outputCell))) {
                    continue;
                }
                JsonObject row = snapshot.verifyOutput(this, candidate,
                        authority, true);
                rows.add(row);
                mapProjectionObservations.add(row);
                if (!snapshot.complete
                        || !snapshot.outputIdentityVerified) {
                    addUnresolvedOnce(snapshot.groupId + ": "
                            + firstNonBlank(snapshot.problem,
                            "output identity validation incomplete"));
                }
            }
            return rows;
        }

        private void verifyRootMapProjectionOutputs(Object rootOutput,
                                                    String exitKind) {
            Set<String> declaredGroups = new LinkedHashSet<>();
            for (MapValueElementProjectionSpec spec
                    : activation.mapValueElementFieldProjections) {
                declaredGroups.add(spec.groupId());
            }
            for (String group : declaredGroups) {
                if (!mapProjectionSnapshots.containsKey(group)) {
                    addUnresolvedOnce(group + ": declared backing Map input "
                            + "was never observed before producer output");
                    JsonObject missing = new JsonObject();
                    missing.addProperty("schemaVersion", 1);
                    missing.addProperty("kind",
                            "MAP_VALUE_OUTPUT_ARRAY_PROJECTION");
                    missing.addProperty("phase", "MISSING_ENTRY_SNAPSHOT");
                    missing.addProperty("groupId", group);
                    missing.addProperty("objectTokenScope",
                            activation.activationId);
                    missing.addProperty("complete", false);
                    missing.addProperty("problem",
                            "declared backing Map input was never observed");
                    mapProjectionObservations.add(missing);
                }
            }
            for (MapProjectionSnapshot snapshot
                    : mapProjectionSnapshots.values()) {
                if (snapshot.outputIdentityVerified) continue;
                if (!"NORMAL".equals(exitKind)) {
                    snapshot.fail("producer did not return normally; output "
                            + "array identity cannot be validated");
                    addUnresolvedOnce(snapshot.groupId + ": "
                            + snapshot.problem);
                    continue;
                }
                if (snapshot.specs.isEmpty()) continue;
                MapValueElementProjectionSpec spec = snapshot.specs.get(0);
                if ("EXACT_REQUESTED_OUTPUT_CAPTURE".equals(
                        spec.outputValidationMode)) {
                    snapshot.fail("required exact output capture hook was not "
                            + "observed");
                    addUnresolvedOnce(snapshot.groupId + ": "
                            + snapshot.problem);
                    continue;
                }
                JsonObject row = snapshot.verifyOutput(this, rootOutput,
                        "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD",
                        false);
                mapProjectionObservations.add(row);
                if (!snapshot.complete
                        || !snapshot.outputIdentityVerified) {
                    addUnresolvedOnce(snapshot.groupId + ": "
                            + firstNonBlank(snapshot.problem,
                            "root output identity validation incomplete"));
                }
            }
        }

        private void observeContainerInput(SymbolizeAction action,
                                           Object value,
                                           String location) {
            List<ContainerElementFieldBindingSpec> declared = activation
                    .containerBindingsForInput(action.symbol);
            if (declared.isEmpty()) return;
            Set<String> cells = new LinkedHashSet<>();
            for (ContainerElementFieldBindingSpec spec : declared) {
                cells.add(spec.containerInputCell);
            }
            if (cells.size() != 1 || !cells.contains(action.cell)) {
                addUnresolvedOnce(action.symbol
                        + ": container input action/cell is ambiguous or "
                        + "does not match its explicit binding");
                ContainerInputObservation previous = containerInputs.get(
                        action.symbol);
                if (previous == null) {
                    containerInputs.put(action.symbol,
                            ContainerInputObservation.ambiguous(value,
                                    objectToken(value), location));
                } else {
                    previous.ambiguous = true;
                }
                return;
            }
            if (value == null || value == MissingValue.INSTANCE
                    || !value.getClass().isArray()
                    || value.getClass().getComponentType().isPrimitive()) {
                addUnresolvedOnce(action.symbol
                        + ": explicit ARRAY_INDEX container input is not a "
                        + "non-null object array");
                return;
            }
            ContainerInputObservation previous = containerInputs.get(
                    action.symbol);
            if (previous == null) {
                containerInputs.put(action.symbol,
                        new ContainerInputObservation(value,
                                objectToken(value), safe(location), false));
            } else if (previous.container != value) {
                previous.ambiguous = true;
                addUnresolvedOnce(action.symbol
                        + ": more than one concrete container instance was "
                        + "observed for one input port");
            }
        }

        private void observeContainerActionValue(SymbolizeAction action,
                                                 Object root,
                                                 String location) {
            observeMapProjectionInput(action, root, location);
            if (activation.containerBindingsForInput(action.symbol)
                    .isEmpty()) {
                return;
            }
            if ("ARGUMENT_FIELD_PATH".equals(action.location)) {
                for (List<String> path : action.fieldPaths) {
                    Object owner = resolveFieldPathLeafOwner(root, path);
                    Object value = owner == null
                            || owner == MissingValue.INSTANCE
                            || path.isEmpty() ? MissingValue.INSTANCE
                            : readField(owner, path.get(path.size() - 1));
                    observeContainerInput(action, value,
                            safe(location) + ":" + joinFieldPath(path));
                }
                return;
            }
            if ("ARGUMENT_FIELD".equals(action.location)) {
                for (String field : action.fields) {
                    observeContainerInput(action, readField(root, field),
                            safe(location) + ":" + safe(field));
                }
                return;
            }
            observeContainerInput(action, root, location);
        }

        private ContainerFieldResolution dynamicContainerFieldBinding(
                SymbolizeAction action, Object accessOwner, Object leafOwner,
                String fieldSignature, String materializationSite) {
            List<ContainerElementFieldBindingSpec> declared = activation
                    .containerBindingsForBase(action.symbol);
            if (declared.isEmpty()) {
                return ContainerFieldResolution.notDeclared();
            }

            Map<String, DynamicFieldBinding> byField =
                    dynamicFieldsByOwner.get(leafOwner);
            String fieldKey = action.symbol + "\n" + safe(fieldSignature)
                    + "\n" + joinFieldPath(action.fieldPath);
            if (byField != null) {
                DynamicFieldBinding existing = byField.get(fieldKey);
                if (existing != null && existing.containerSelector != null) {
                    return ContainerFieldResolution.resolved(
                            new DynamicFieldSelection(existing, false));
                }
            }

            String actualHookSite = safe(materializationSite);
            int actualHookOccurrence = nextActualFieldHookOccurrence(
                    action.symbol, actualHookSite);
            List<ContainerElementMatch> matches =
                    new ArrayList<>();
            List<String> fatalProblems = new ArrayList<>();
            for (ContainerElementFieldBindingSpec spec : declared) {
                String structural = spec.structuralValidationError(
                        activation, action, leafOwner, fieldSignature);
                if (!structural.isEmpty()) {
                    fatalProblems.add(spec.bindingId + "=" + structural);
                    continue;
                }
                ContainerInputObservation container = containerInputs.get(
                        spec.containerInputPort);
                if (container == null) {
                    fatalProblems.add(spec.bindingId
                            + "=container input has not been observed");
                    continue;
                }
                if (container.ambiguous) {
                    fatalProblems.add(spec.bindingId
                            + "=container input instance is ambiguous");
                    continue;
                }
                int resolvedIndex = spec.resolveElementIndex(
                        container.container, leafOwner);
                if (resolvedIndex < 0) {
                    String resolution = spec.elementResolutionError(
                            container.container, leafOwner);
                    if (!spec.unrelatedOwner(container.container,
                            leafOwner)) {
                        fatalProblems.add(spec.bindingId + "="
                                + resolution);
                    }
                    continue;
                }
                matches.add(new ContainerElementMatch(spec,
                        resolvedIndex));
            }
            if (!fatalProblems.isEmpty()) {
                return ContainerFieldResolution.unresolved(
                        "container selector validation failed ["
                                + String.join("; ", fatalProblems) + "]");
            }
            if (matches.isEmpty()) {
                // The field hook is intentionally owner-wide.  Exact
                // declaration coverage is checked at region exit, so an
                // unrelated same-field owner can be ignored here without
                // allowing the selected array element to disappear.
                return ContainerFieldResolution.ignored();
            }
            if (matches.size() != 1) {
                return ContainerFieldResolution.unresolved(
                        "multiple explicit selectors matched the same owner");
            }
            ContainerElementMatch match = matches.get(0);
            ContainerElementFieldBindingSpec spec = match.spec;
            String effectiveSite = spec.fieldMaterializationSiteId;
            int effectiveOccurrence = nextFieldMaterializationOccurrence(
                    action.symbol, effectiveSite);
            String selectorProblem = spec.effectiveSelectorError(
                    effectiveSite, effectiveOccurrence);
            if (!selectorProblem.isEmpty()) {
                return ContainerFieldResolution.unresolved(spec.bindingId
                        + "=" + selectorProblem);
            }
            ContainerInputObservation container = containerInputs.get(
                    spec.containerInputPort);
            if (byField == null) {
                byField = new LinkedHashMap<>();
                dynamicFieldsByOwner.put(leafOwner, byField);
            }
            DynamicFieldBinding binding = new DynamicFieldBinding(this,
                    action, accessOwner, leafOwner, fieldSignature,
                    effectiveSite, effectiveOccurrence, spec, container,
                    match.resolvedElementIndex, actualHookSite,
                    actualHookOccurrence);
            byField.put(fieldKey, binding);
            dynamicFieldBindings.put(binding.dynamicBindingId, binding);
            return ContainerFieldResolution.resolved(
                    new DynamicFieldSelection(binding, true));
        }

        private long nextRuntimeEventSequence() {
            return ++runtimeEventSequence;
        }

        private long objectToken(Object value) {
            if (value == null) {
                return 0L;
            }
            Long existing = objectTokens.get(value);
            if (existing != null) {
                return existing;
            }
            long token = nextObjectToken++;
            objectTokens.put(value, token);
            return token;
        }

        private synchronized void observeFieldWrite(Object owner,
                                                    String signature) {
            String[] declared = declaredField(signature);
            if (owner == null || declared == null) return;
            Map<String, Long> signatures = observedFieldWrites.get(owner);
            if (signatures == null) {
                signatures = new LinkedHashMap<>();
                observedFieldWrites.put(owner, signatures);
            }
            String identity = exactFieldIdentity(declared);
            Long count = signatures.get(identity);
            signatures.put(identity, count == null ? 1L : count + 1L);
        }

        private synchronized long observedFieldWriteCount(Object owner,
                                                          String signature) {
            String[] declared = declaredField(signature);
            Map<String, Long> signatures = owner == null || declared == null
                    ? null : observedFieldWrites.get(owner);
            Long count = signatures == null ? null
                    : signatures.get(exactFieldIdentity(declared));
            return count == null ? 0L : count;
        }

        private boolean hasAppliedSolverReplay() {
            for (JsonObject applied : replayMaterializationsApplied) {
                if (bool(applied, "solverDerived", false)) {
                    return true;
                }
            }
            return false;
        }

        private ModelAssignment assignment(SymbolizeAction action,
                                           List<String> path) {
            for (ModelAssignment assignment
                    : activation.modelAssignments) {
                if (assignment.matches(action, path)
                        && !appliedModelAssignments.contains(
                        assignment.key)) {
                    return assignment;
                }
            }
            return null;
        }

        private List<ModelAssignment> fieldAssignments(
                SymbolizeAction action) {
            List<ModelAssignment> result = new ArrayList<>();
            for (ModelAssignment assignment
                    : activation.modelAssignments) {
                if (!assignment.hasDynamicMetadata()
                        && assignment.targetsFieldAccess(action)
                        && !appliedModelAssignments.contains(
                        assignment.key)) {
                    result.add(assignment);
                }
            }
            return result;
        }

        private DynamicFieldSelection dynamicFieldBinding(
                SymbolizeAction action, Object accessOwner, Object leafOwner,
                String fieldSignature, String siteId, int occurrence,
                MapIteratorCursor cursor) {
            Map<String, DynamicFieldBinding> byField =
                    dynamicFieldsByOwner.get(leafOwner);
            if (byField == null) {
                byField = new LinkedHashMap<>();
                dynamicFieldsByOwner.put(leafOwner, byField);
            }
            String fieldKey = action.symbol + "\n" + safe(fieldSignature)
                    + "\n" + joinFieldPath(action.fieldPath);
            DynamicFieldBinding binding = byField.get(fieldKey);
            if (binding != null) {
                return new DynamicFieldSelection(binding, false);
            }
            binding = new DynamicFieldBinding(this, action, accessOwner,
                    leafOwner, fieldSignature, siteId, occurrence, cursor);
            byField.put(fieldKey, binding);
            dynamicFieldBindings.put(binding.dynamicBindingId, binding);
            return new DynamicFieldSelection(binding, true);
        }

        private List<ModelAssignment> dynamicFieldAssignments(
                SymbolizeAction action, DynamicFieldBinding binding) {
            List<ModelAssignment> result = new ArrayList<>();
            for (ModelAssignment assignment : activation.modelAssignments) {
                if (appliedModelAssignments.contains(assignment.key)
                        || !assignment.hasDynamicMetadata()) {
                    continue;
                }
                if (assignment.matchesDynamic(action, binding)) {
                    result.add(assignment);
                } else if (assignment.matchesDynamicExceptExpectedKey(
                        action, binding)) {
                    unresolved.add(binding.dynamicBindingId
                            + ": expected entry key selector mismatch for "
                            + assignment.engineSymbol);
                } else if (assignment.matchesDynamicIdentity(action,
                        binding) && binding.containerSelector != null) {
                    addUnresolvedOnce(binding.dynamicBindingId
                            + ": exact container selector mismatch for "
                            + assignment.engineSymbol);
                }
            }
            return result;
        }

        private List<ModelAssignment> mapProjectionAssignments(
                MapProjectionFieldBinding binding) {
            List<ModelAssignment> result = new ArrayList<>();
            for (ModelAssignment assignment : activation.modelAssignments) {
                if (appliedModelAssignments.contains(assignment.key)
                        || !assignment.hasDynamicMetadata()) {
                    continue;
                }
                if (assignment.matchesMapProjection(binding)) {
                    result.add(assignment);
                } else if (assignment.targetsMapProjection(binding.spec)) {
                    addUnresolvedOnce(binding.dynamicBindingId
                            + ": immutable-key-primary map/output replay "
                            + "selector mismatch for "
                            + assignment.engineSymbol);
                } else if (assignment.dynamicBindingId.equals(
                        binding.dynamicBindingId)
                        || assignment.dynamicFieldSymbol.equals(
                        binding.dynamicFieldSymbol)) {
                    addUnresolvedOnce(binding.dynamicBindingId
                            + ": exact map/output projection selector mismatch "
                            + "for " + assignment.engineSymbol);
                }
            }
            return result;
        }

        private List<ModelAssignment> explicitUniqueLegacyFieldAssignments(
                SymbolizeAction action, DynamicFieldBinding binding) {
            List<ModelAssignment> result = new ArrayList<>();
            // A base-only assignment cannot be broadcast across entry values.
            // Preserve it solely when the producer explicitly certified one
            // unique field target and this is that first stable occurrence.
            if (binding.materializationOccurrence != 1) {
                return result;
            }
            for (ModelAssignment assignment : activation.modelAssignments) {
                if (!assignment.hasDynamicMetadata()
                        && assignment.legacyUniqueFieldTarget
                        && assignment.targetsFieldAccess(action)
                        && !appliedModelAssignments.contains(
                        assignment.key)) {
                    result.add(assignment);
                }
            }
            return result;
        }

        private JsonArray dynamicFieldBindingsJson() {
            JsonArray result = new JsonArray();
            for (DynamicFieldBinding binding : dynamicFieldBindings.values()) {
                result.add(binding.toJson());
            }
            for (MapProjectionFieldBinding binding
                    : mapProjectionFieldBindings.values()) {
                result.add(binding.toJson());
            }
            return result;
        }

        /**
         * Owner-wide field hooks may legitimately observe unrelated objects,
         * so a zero identity match is ignored at the hook.  This activation
         * boundary is the complementary fail-closed check: every exact static
         * array selector must have produced exactly one complete dynamic
         * binding for its own activation-local element.
         */
        private void validateContainerElementFieldCoverage() {
            Set<String> declarations = new LinkedHashSet<>();
            for (ContainerElementFieldBindingSpec spec
                    : activation.containerElementFieldBindings) {
                if (!spec.requiresExactCoverage()) continue;
                if (!declarations.add(spec.bindingId)) {
                    addUnresolvedOnce(spec.bindingId
                            + ": duplicate exact container-element field "
                            + "declaration");
                    continue;
                }
                int matches = 0;
                for (DynamicFieldBinding binding
                        : dynamicFieldBindings.values()) {
                    if (binding.containerSelector != null
                            && spec.bindingId.equals(
                            binding.containerSelector.bindingId)
                            && binding.complete
                            && spec.fieldMaterializationSiteId.equals(
                            binding.materializationSiteId)
                            && spec.elementOccurrence
                            == binding.materializationOccurrence
                            && spec.elementIndex
                            == binding.containerSelector.elementIndex) {
                        matches++;
                    }
                }
                if (matches != 1) {
                    addUnresolvedOnce(spec.baseInputSymbol
                            + ": exact container-element declaration "
                            + spec.bindingId + " produced " + matches
                            + " complete runtime bindings; expected 1");
                }
            }
        }

        private void recordModelAssignment(ModelAssignment assignment,
                                           String location,
                                           List<String> path,
                                           Object concreteValue) {
            recordModelAssignment(assignment, assignment.toJson(), location,
                    path, concreteValue);
        }

        /**
         * Records a map-entry assignment using only the selector observed in
         * this execution.  A solver plan may select the exact static
         * base/site/occurrence, but it never authorizes reuse of the seed
         * execution's entry key or object identity.
         */
        private void recordDynamicMapModelAssignment(
                ModelAssignment assignment, String location,
                List<String> path, DynamicFieldBinding binding,
                Object concreteValue) {
            JsonObject row = assignment.toJson();
            if (assignment.usesFreshMapEntryRebinding()) {
                row.remove("expectedEntryKey");
                row.remove("expectedEntryKeyAuthority");
                row.addProperty("dynamicReplayRebindingAuthority",
                        FRESH_MAP_ENTRY_REBINDING_AUTHORITY);
                row.addProperty("sourceEntrySelectorRetained", false);
                row.addProperty("sameSeedEntryClaimed", false);
                row.addProperty("freshEntrySelectorCaptured",
                        binding != null
                                && binding.freshReplaySelectorComplete());
                if (binding != null) {
                    if (!binding.entryReadObservationId.isEmpty()) {
                        row.addProperty("entryReadObservationId",
                                binding.entryReadObservationId);
                    }
                    if (binding.keyExpression != null) {
                        row.add("keyExpression",
                                copyJsonTree(binding.keyExpression));
                    }
                    if (!safe(binding.keyExpressionAuthority).isEmpty()) {
                        row.addProperty("keyExpressionAuthority",
                                binding.keyExpressionAuthority);
                    }
                }
            }
            recordModelAssignment(assignment, row, location, path,
                    concreteValue);
        }

        private void recordModelAssignment(ModelAssignment assignment,
                                           JsonObject row,
                                           String location,
                                           List<String> path,
                                           Object concreteValue) {
            appliedModelAssignments.add(assignment.key);
            row.addProperty("appliedAt", location);
            row.addProperty("branchOverride", false);
            row.addProperty("concreteValueClass", concreteValue == null
                    ? "null" : concreteValue.getClass().getName());
            if (path != null && !path.isEmpty()) {
                row.add("materializationPath", GSON.toJsonTree(path));
            }
            modelAssignmentsApplied.add(row);
        }
    }

    private static final class DynamicFieldSelection {
        private final DynamicFieldBinding binding;
        private final boolean created;

        private DynamicFieldSelection(DynamicFieldBinding binding,
                                      boolean created) {
            this.binding = binding;
            this.created = created;
        }
    }

    private static final class DynamicFieldBinding {
        private static final String AUTHORITY =
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_FIELD_SITE_OCCURRENCE";
        private static final String CONTAINER_AUTHORITY =
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_AND_"
                        + "STABLE_FIELD_SITE_OCCURRENCE";
        private static final String CONTAINER_SITE_BRIDGE_AUTHORITY =
                "STATIC_CONTAINER_SELECTOR_AND_ACTIVATION_LOCAL_EXACT_"
                        + "ELEMENT_IDENTITY_TO_DECLARED_FIELD_HOOK_V1";

        private final int schemaVersion;
        private final String kind;
        private final String authority;
        private final String dynamicBindingId;
        private final String baseInputSymbol;
        private final String dynamicFieldSymbol;
        private final String materializationSiteId;
        private final int materializationOccurrence;
        private final String actualHookSiteId;
        private final int actualHookOccurrence;
        private final String materializationSiteBridgeAuthority;
        private final String materializationSiteBridgeBindingId;
        private final long materializationSiteBridgeElementObjectToken;
        private final String materializationSiteBridgeObjectTokenScope;
        private final String fieldSignature;
        private final List<String> fieldPath;
        private final Object leafOwner;
        private final long leafOwnerObjectToken;
        private final String objectTokenScope;
        private final String entryReadObservationId;
        private final ContainerElementSelector containerSelector;
        private JsonElement keyExpression;
        private String keyExpressionAuthority;
        private boolean complete;

        private DynamicFieldBinding(ActiveRegion active,
                                    SymbolizeAction action,
                                    Object accessOwner, Object leafOwner,
                                    String fieldSignature, String siteId,
                                    int occurrence,
                                    MapIteratorCursor cursor) {
            this.schemaVersion = 1;
            this.kind = "DYNAMIC_MAP_ENTRY_FIELD_BINDING";
            this.authority = AUTHORITY;
            this.baseInputSymbol = action.symbol;
            this.materializationSiteId = safe(siteId);
            this.materializationOccurrence = occurrence;
            this.actualHookSiteId = safe(siteId);
            this.actualHookOccurrence = occurrence;
            this.materializationSiteBridgeAuthority = "";
            this.materializationSiteBridgeBindingId = "";
            this.materializationSiteBridgeElementObjectToken = 0L;
            this.materializationSiteBridgeObjectTokenScope = "";
            this.dynamicFieldSymbol = dynamicFieldSymbolForTests(
                    action.symbol, siteId, occurrence);
            this.dynamicBindingId = "DYNAMIC_FIELD:"
                    + dynamicFieldSymbol;
            this.fieldSignature = safe(fieldSignature);
            this.fieldPath = new ArrayList<>(action.fieldPath);
            this.leafOwner = leafOwner;
            this.leafOwnerObjectToken = active.objectToken(leafOwner);
            this.objectTokenScope = active.activation.activationId;
            this.entryReadObservationId = cursor.entryObservationId;
            this.containerSelector = null;
            this.keyExpression = cursor.keyExpression == null ? null
                    : copyJsonTree(cursor.keyExpression);
            this.keyExpressionAuthority = cursor.keyExpressionAuthority;
            refresh(active, cursor);
        }

        private DynamicFieldBinding(ActiveRegion active,
                                    SymbolizeAction action,
                                    Object accessOwner, Object leafOwner,
                                    String fieldSignature, String siteId,
                                    int occurrence,
                                    ContainerElementFieldBindingSpec spec,
                                    ContainerInputObservation container,
                                    int resolvedElementIndex,
                                    String actualHookSiteId,
                                    int actualHookOccurrence) {
            this.schemaVersion = 2;
            this.kind = "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING";
            this.authority = CONTAINER_AUTHORITY;
            this.baseInputSymbol = action.symbol;
            this.materializationSiteId = safe(siteId);
            this.materializationOccurrence = occurrence;
            this.actualHookSiteId = safe(actualHookSiteId);
            this.actualHookOccurrence = actualHookOccurrence;
            this.materializationSiteBridgeAuthority =
                    CONTAINER_SITE_BRIDGE_AUTHORITY;
            this.materializationSiteBridgeBindingId = spec.bindingId;
            this.dynamicFieldSymbol = dynamicFieldSymbolForTests(
                    action.symbol, siteId, occurrence);
            this.dynamicBindingId = "DYNAMIC_FIELD:" + dynamicFieldSymbol;
            this.fieldSignature = safe(fieldSignature);
            this.fieldPath = new ArrayList<>(action.fieldPath);
            this.leafOwner = leafOwner;
            this.leafOwnerObjectToken = active.objectToken(leafOwner);
            this.objectTokenScope = active.activation.activationId;
            this.materializationSiteBridgeElementObjectToken =
                    this.leafOwnerObjectToken;
            this.materializationSiteBridgeObjectTokenScope =
                    this.objectTokenScope;
            this.entryReadObservationId = "";
            this.containerSelector = new ContainerElementSelector(active,
                    spec, container, leafOwner, resolvedElementIndex,
                    occurrence);
            this.keyExpression = null;
            this.keyExpressionAuthority = "";
            this.complete = !baseInputSymbol.isEmpty()
                    && !dynamicFieldSymbol.isEmpty()
                    && !materializationSiteId.isEmpty()
                    && materializationOccurrence > 0
                    && !this.fieldSignature.isEmpty()
                    && !this.fieldPath.isEmpty()
                    && leafOwnerObjectToken > 0L
                    && !this.actualHookSiteId.isEmpty()
                    && this.actualHookOccurrence > 0
                    && !this.materializationSiteBridgeBindingId.isEmpty()
                    && this.materializationSiteBridgeElementObjectToken
                    == leafOwnerObjectToken
                    && this.materializationSiteBridgeObjectTokenScope.equals(
                    objectTokenScope)
                    && containerSelector.complete;
        }

        private void refresh(ActiveRegion active,
                             MapIteratorCursor cursor) {
            if (cursor != null && cursor.keyExpression != null) {
                keyExpression = copyJsonTree(cursor.keyExpression);
                keyExpressionAuthority = cursor.keyExpressionAuthority;
            }
            complete = cursor != null && cursor.hasCurrent
                    && cursor.valueKnown && cursor.value == leafOwner
                    && !baseInputSymbol.isEmpty()
                    && !dynamicFieldSymbol.isEmpty()
                    && !materializationSiteId.isEmpty()
                    && materializationOccurrence > 0
                    && !fieldSignature.isEmpty() && !fieldPath.isEmpty()
                    && leafOwnerObjectToken > 0L
                    && !entryReadObservationId.isEmpty()
                    && completeRuntimeExpression(keyExpression)
                    && !safe(keyExpressionAuthority).isEmpty()
                    && cursor.entryObservationComplete;
        }

        /**
         * The minimal exact selector available before the field is
         * symbolized.  The entry value expression may become complete only
         * after symbolization, so replay selection relies on the current
         * iterator's key/value ownership and its exact static occurrence; the
         * importer still requires the fully refreshed binding afterward.
         */
        private boolean freshReplaySelectorComplete() {
            return containerSelector == null
                    && !baseInputSymbol.isEmpty()
                    && !dynamicFieldSymbol.isEmpty()
                    && !materializationSiteId.isEmpty()
                    && materializationOccurrence > 0
                    && !fieldSignature.isEmpty() && !fieldPath.isEmpty()
                    && leafOwnerObjectToken > 0L
                    && !entryReadObservationId.isEmpty()
                    && completeRuntimeExpression(keyExpression)
                    && !safe(keyExpressionAuthority).isEmpty();
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", schemaVersion);
            result.addProperty("kind", kind);
            result.addProperty("dynamicBindingId", dynamicBindingId);
            result.addProperty("baseInputSymbol", baseInputSymbol);
            result.addProperty("dynamicFieldSymbol", dynamicFieldSymbol);
            result.addProperty("materializationSiteId",
                    materializationSiteId);
            result.addProperty("materializationOccurrence",
                    materializationOccurrence);
            if (containerSelector != null) {
                result.addProperty("actualHookSiteId", actualHookSiteId);
                result.addProperty("actualHookOccurrence",
                        actualHookOccurrence);
                result.addProperty("effectiveMaterializationSiteId",
                        materializationSiteId);
                result.addProperty("effectiveMaterializationOccurrence",
                        materializationOccurrence);
                result.addProperty("materializationSiteBridgeAuthority",
                        materializationSiteBridgeAuthority);
                result.addProperty("materializationSiteBridgeBindingId",
                        materializationSiteBridgeBindingId);
                result.addProperty(
                        "materializationSiteBridgeElementObjectToken",
                        materializationSiteBridgeElementObjectToken);
                result.addProperty(
                        "materializationSiteBridgeObjectTokenScope",
                        materializationSiteBridgeObjectTokenScope);
            }
            result.addProperty("fieldSignature", fieldSignature);
            result.add("fieldPath", GSON.toJsonTree(fieldPath));
            result.addProperty("leafOwnerObjectToken",
                    leafOwnerObjectToken);
            result.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            result.addProperty("objectTokenScope", objectTokenScope);
            if (!entryReadObservationId.isEmpty()) {
                result.addProperty("entryReadObservationId",
                        entryReadObservationId);
            }
            if (keyExpression != null) {
                result.add("keyExpression", copyJsonTree(keyExpression));
            }
            if (!safe(keyExpressionAuthority).isEmpty()) {
                result.addProperty("keyExpressionAuthority",
                        keyExpressionAuthority);
            }
            if (containerSelector != null) {
                result.add("containerSelector",
                        containerSelector.toJson());
                containerSelector.addFlatCompatibilityFields(result);
            }
            result.addProperty("authority", authority);
            result.addProperty("complete", complete);
            return result;
        }
    }

    private static final class ContainerElementSelector {
        private static final String AUTHORITY =
                "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                        + "ACTIVATION_LOCAL_ELEMENT_IDENTITY";

        private final String bindingId;
        private final String containerInputPort;
        private final String containerInputCell;
        private final String selectorAuthority;
        private final String resolvedFromSelectorAuthority;
        private final int elementIndex;
        private final int elementOccurrence;
        private final String declaredFieldOwnerClass;
        private final String declaredFieldType;
        private final long containerObjectToken;
        private final long elementObjectToken;
        private final String objectTokenScope;
        private final String observationLocation;
        private final boolean complete;

        private ContainerElementSelector(ActiveRegion active,
                                         ContainerElementFieldBindingSpec spec,
                                         ContainerInputObservation container,
                                         Object element,
                                         int resolvedElementIndex,
                                         int materializationOccurrence) {
            this.bindingId = spec.bindingId;
            this.containerInputPort = spec.containerInputPort;
            this.containerInputCell = spec.containerInputCell;
            // Discovery is activation-local evidence gathering.  Once the
            // unique identity lookup succeeds, publish only the replayable
            // exact selector; retain the seed authority as provenance.
            this.selectorAuthority =
                    ContainerElementFieldBindingSpec.EXACT_ARRAY_INDEX;
            this.resolvedFromSelectorAuthority = spec.selectorAuthority;
            this.elementIndex = resolvedElementIndex;
            this.elementOccurrence = materializationOccurrence;
            this.declaredFieldOwnerClass = spec.declaredFieldOwnerClass;
            this.declaredFieldType = spec.declaredFieldType;
            this.containerObjectToken = container == null ? 0L
                    : container.objectToken;
            this.elementObjectToken = active.objectToken(element);
            this.objectTokenScope = active.activation.activationId;
            this.observationLocation = container == null ? ""
                    : container.location;
            this.complete = container != null && !container.ambiguous
                    && !bindingId.isEmpty()
                    && !containerInputPort.isEmpty()
                    && !containerInputCell.isEmpty()
                    && !selectorAuthority.isEmpty()
                    && elementIndex >= 0 && elementOccurrence > 0
                    && !declaredFieldOwnerClass.isEmpty()
                    && !declaredFieldType.isEmpty()
                    && containerObjectToken > 0L
                    && elementObjectToken > 0L
                    && !objectTokenScope.isEmpty();
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("kind", "ARRAY_INDEX");
            result.addProperty("bindingId", bindingId);
            result.addProperty("containerInputPort", containerInputPort);
            result.addProperty("containerInputCell", containerInputCell);
            result.addProperty("selectorAuthority", selectorAuthority);
            result.addProperty("resolvedFromSelectorAuthority",
                    resolvedFromSelectorAuthority);
            result.addProperty("elementIndex", elementIndex);
            result.addProperty("elementOccurrence", elementOccurrence);
            result.addProperty("declaredFieldOwnerClass",
                    declaredFieldOwnerClass);
            result.addProperty("declaredFieldType", declaredFieldType);
            result.addProperty("containerObjectToken",
                    containerObjectToken);
            result.addProperty("elementObjectToken", elementObjectToken);
            result.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            result.addProperty("objectTokenScope", objectTokenScope);
            result.addProperty("containerObservationLocation",
                    observationLocation);
            result.addProperty("authority", AUTHORITY);
            result.addProperty("complete", complete);
            return result;
        }

        private void addFlatCompatibilityFields(JsonObject target) {
            target.addProperty("containerBindingId", bindingId);
            target.addProperty("containerInputPort", containerInputPort);
            target.addProperty("containerInputCell", containerInputCell);
            target.addProperty("selectorAuthority", selectorAuthority);
            target.addProperty("resolvedFromSelectorAuthority",
                    resolvedFromSelectorAuthority);
            target.addProperty("elementIndex", elementIndex);
            target.addProperty("elementOccurrence", elementOccurrence);
            target.addProperty("declaredFieldOwnerClass",
                    declaredFieldOwnerClass);
            target.addProperty("declaredFieldType", declaredFieldType);
        }
    }

    private static final class FieldObservationTarget {
        private final String symbol;
        private final Object owner;
        private final List<String> path;
        private final DynamicFieldBinding binding;

        private FieldObservationTarget(String symbol, Object owner,
                                       List<String> path) {
            this(symbol, owner, path, null);
        }

        private FieldObservationTarget(String symbol, Object owner,
                                       List<String> path,
                                       DynamicFieldBinding binding) {
            this.symbol = symbol;
            this.owner = owner;
            this.path = new ArrayList<>(path);
            this.binding = binding;
        }
    }

    private static final class SymbolizeAction {
        private final String symbol;
        private final String cell;
        private final String location;
        private final String field;
        private final int index;
        private final List<String> fields;
        private final List<List<String>> fieldPaths;
        private final String bindingMode;
        private final String method;
        private final String local;
        private final String leafField;
        private final String leafOwnerClass;
        private final String accessField;
        private final String accessOwnerClass;
        private final String accessFieldType;
        private final String accessFieldSignature;
        private final String accessMethod;
        private final String accessSiteId;
        private final int accessUnitIndex;
        private final String accessSiteAuthority;
        private final String accessorCallerMethod;
        private final String accessorCallSiteId;
        private final int accessorCallUnitIndex;
        private final String accessorDeclaredCallee;
        private final String accessorCallSiteAuthority;
        private final String accessorImplementationMethod;
        private final String accessorImplementationAuthority;
        private final String consumedFieldSiteId;
        private final String consumedFieldMethod;
        private final int consumedFieldUnitIndex;
        private final String consumedFieldSiteAuthority;
        private final String consumedFieldRootAuthority;
        private final List<String> fieldPath;
        private final String javaType;
        private final Map<String, String> leafFieldSignaturesByPath =
                new LinkedHashMap<>();

        private SymbolizeAction(JsonObject json) {
            this.symbol = string(json, "symbol");
            this.cell = string(json, "cell");
            this.location = string(json, "location");
            this.field = string(json, "field");
            this.index = integer(json, "index", -1);
            this.bindingMode = string(json, "bindingMode");
            this.javaType = firstNonBlank(string(json, "javaType"),
                    string(json, "inputJavaType"),
                    inputJavaTypeFromCell(this.cell));
            Matcher localCell = LOCAL_CELL.matcher(this.cell);
            boolean localCellMatches = localCell.matches();
            this.method = firstNonBlank(string(json, "method"),
                    localCellMatches ? localCell.group(1) : "");
            this.local = firstNonBlank(string(json, "local"),
                    localCellMatches ? localCell.group(2) : "");
            this.fieldPath = new ArrayList<>();
            for (JsonElement element : array(json, "fieldPath")) {
                if (element.isJsonPrimitive()) {
                    this.fieldPath.add(element.getAsString());
                }
            }
            String[] declaredField = declaredField(this.cell);
            if (this.fieldPath.isEmpty() && declaredField != null) {
                this.fieldPath.add(declaredField[2]);
                Matcher projection = FIELD_PROJECTION.matcher(this.cell);
                while (projection.find()) {
                    this.fieldPath.add(projection.group(1));
                }
            } else if (this.fieldPath.isEmpty()) {
                Matcher projection = FIELD_PROJECTION.matcher(this.cell);
                while (projection.find()) {
                    this.fieldPath.add(projection.group(1));
                }
            }
            this.accessField = firstNonBlank(string(json, "accessField"),
                    this.fieldPath.isEmpty() ? "" : this.fieldPath.get(0),
                    fieldName(this.cell));
            this.accessOwnerClass = firstNonBlank(
                    string(json, "accessOwnerClass"),
                    declaredField == null ? "" : declaredField[0]);
            this.accessFieldType = string(json, "accessFieldType");
            this.accessFieldSignature = string(json,
                    "accessFieldSignature");
            this.accessMethod = string(json, "accessMethod");
            this.accessSiteId = string(json, "accessSiteId");
            this.accessUnitIndex = integer(json, "accessUnitIndex", -1);
            this.accessSiteAuthority = string(json,
                    "accessSiteAuthority");
            this.accessorCallerMethod = string(json,
                    "accessorCallerMethod");
            this.accessorCallSiteId = string(json,
                    "accessorCallSiteId");
            this.accessorCallUnitIndex = integer(json,
                    "accessorCallUnitIndex", -1);
            this.accessorDeclaredCallee = string(json,
                    "accessorDeclaredCallee");
            this.accessorCallSiteAuthority = string(json,
                    "accessorCallSiteAuthority");
            this.accessorImplementationMethod = string(json,
                    "accessorImplementationMethod");
            this.accessorImplementationAuthority = string(json,
                    "accessorImplementationAuthority");
            String declaredConsumedSite = firstNonBlank(
                    string(json, "consumedFieldSiteId"),
                    string(json, "leafFieldMaterializationSiteId"),
                    string(json, "fieldMaterializationSiteId"));
            this.leafField = firstNonBlank(string(json, "leafField"),
                    this.fieldPath.isEmpty() ? ""
                            : this.fieldPath.get(this.fieldPath.size() - 1),
                    fieldName(this.cell));
            boolean projected = this.fieldPath.size() > 1;
            this.leafOwnerClass = firstNonBlank(
                    string(json, "leafOwnerClass"),
                    declaredField == null ? ""
                            : (projected ? declaredField[1]
                            : declaredField[0]));
            this.fields = new ArrayList<>();
            for (JsonElement element : array(json, "fields")) {
                if (element.isJsonPrimitive()) {
                    this.fields.add(element.getAsString());
                }
            }
            this.fieldPaths = new ArrayList<>();
            for (JsonElement pathElement : array(json, "fieldPaths")) {
                if (!pathElement.isJsonArray()) {
                    continue;
                }
                List<String> path = new ArrayList<>();
                for (JsonElement segment : pathElement.getAsJsonArray()) {
                    if (segment.isJsonPrimitive()) {
                        path.add(segment.getAsString());
                    }
                }
                if (!path.isEmpty()) {
                    this.fieldPaths.add(path);
                }
            }
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
                if (!path.isEmpty() && declaredField(signature) != null) {
                    leafFieldSignaturesByPath.put(joinFieldPath(path),
                            signature);
                    declaredConsumedSite = firstNonBlank(
                            declaredConsumedSite,
                            string(declaration, "consumedFieldSiteId"),
                            string(declaration,
                                    "fieldMaterializationSiteId"),
                            string(declaration, "siteId"));
                }
            }
            String explicitLeafSignature = string(json,
                    "leafFieldSignature");
            if (!this.fieldPath.isEmpty()
                    && declaredField(explicitLeafSignature) != null) {
                leafFieldSignaturesByPath.put(joinFieldPath(
                        this.fieldPath), explicitLeafSignature);
            }
            this.consumedFieldSiteId = safe(declaredConsumedSite);
            this.consumedFieldMethod = string(json,
                    "consumedFieldMethod");
            this.consumedFieldUnitIndex = integer(json,
                    "consumedFieldUnitIndex", -1);
            this.consumedFieldSiteAuthority = string(json,
                    "consumedFieldSiteAuthority");
            this.consumedFieldRootAuthority = string(json,
                    "consumedFieldRootAuthority");
        }

        private DeclaredArrayInputType directArrayType(Object value) {
            String descriptor = javaTypeDescriptor(javaType);
            if (!descriptor.startsWith("[")) {
                return DeclaredArrayInputType.incomplete(
                        "input action javaType is not a declared array type");
            }
            if (value == null || !value.getClass().isArray()
                    || !descriptor.equals(reflectionDescriptor(
                    value.getClass()))) {
                return DeclaredArrayInputType.incomplete(javaType,
                        "input action javaType does not match the live array");
            }
            return DeclaredArrayInputType.exact(javaType,
                    "ACTION_DECLARED_DIRECT_ARRAY_VALUE_TYPE");
        }

        private boolean declaresArrayInput(List<String> actualPath) {
            String pathSignature = leafFieldSignaturesByPath.get(
                    joinFieldPath(actualPath));
            String[] declared = declaredField(pathSignature);
            if (declared != null
                    && javaTypeDescriptor(declared[1]).startsWith("[")) {
                return true;
            }
            for (String signature : new String[]{accessFieldSignature,
                    field, cell}) {
                declared = declaredField(signature);
                if (declared != null
                        && javaTypeDescriptor(declared[1]).startsWith("[")
                        && (actualPath == null || actualPath.isEmpty()
                        || declared[2].equals(actualPath.get(
                        actualPath.size() - 1)))) {
                    return true;
                }
            }
            return javaTypeDescriptor(javaType).startsWith("[");
        }

        private DeclaredArrayInputType exactLeafArrayType(
                Object owner, String field, List<String> actualPath) {
            Set<String> candidates = new LinkedHashSet<>();
            if (!accessFieldSignature.isEmpty()
                    && accessField.equals(field)) {
                candidates.add(accessFieldSignature);
            }
            if (declaredField(this.field) != null) {
                candidates.add(this.field);
            }
            if (declaredField(cell) != null) {
                candidates.add(cell);
            }
            String pathSignature = leafFieldSignaturesByPath.get(
                    joinFieldPath(actualPath));
            if (pathSignature != null) candidates.add(pathSignature);
            if (!accessFieldType.isEmpty() && !accessOwnerClass.isEmpty()
                    && accessField.equals(field)) {
                candidates.add("<" + accessOwnerClass + ": "
                        + accessFieldType + " " + accessField + ">");
            }

            String selectedType = "";
            String selectedSignature = "";
            for (String signature : candidates) {
                String[] declared = declaredField(signature);
                if (declared == null || !declared[2].equals(field)
                        || owner == null || !instanceOfName(
                        owner.getClass(), declared[0])) {
                    continue;
                }
                ExactFieldObservation exact = observeExactField(owner,
                        signature);
                if (!exact.ownerVerified || !exact.typeVerified
                        || !exact.available || exact.fieldType == null
                        || !exact.fieldType.isArray()) {
                    continue;
                }
                if (!selectedSignature.isEmpty()
                        && !selectedSignature.equals(signature)) {
                    return DeclaredArrayInputType.incomplete(
                            "more than one exact leaf array declaration "
                                    + "matches the input action");
                }
                selectedSignature = signature;
                selectedType = declared[1];
            }
            if (selectedSignature.isEmpty()) {
                return DeclaredArrayInputType.incomplete(
                        "exact declared leaf array field is unavailable for "
                                + joinFieldPath(actualPath));
            }
            if (!javaTypeDescriptor(javaType).equals(
                    javaTypeDescriptor(selectedType))) {
                return DeclaredArrayInputType.incomplete(
                        "action javaType does not equal the exact declared "
                                + "leaf array type");
            }
            return DeclaredArrayInputType.exact(selectedType,
                    "EXACT_LEAF_FIELD_SIGNATURE_AND_REFLECTION:"
                            + selectedSignature);
        }

        private DeclaredArrayInputType exactConsumedLeafArrayType(
                Object leafOwner, String actualSignature,
                String actualField) {
            String[] actual = declaredField(actualSignature);
            if (actual == null || !actual[2].equals(safe(actualField))
                    || leafOwner == null || !instanceOfName(
                    leafOwner.getClass(), actual[0])) {
                return DeclaredArrayInputType.incomplete(
                        "consumed getfield has no exact declared leaf "
                                + "signature/owner join");
            }
            boolean declaredByAction = false;
            Set<String> candidates = new LinkedHashSet<>(
                    leafFieldSignaturesByPath.values());
            candidates.add(accessFieldSignature);
            candidates.add(field);
            candidates.add(cell);
            if (!leafOwnerClass.isEmpty() && !leafField.isEmpty()
                    && !javaType.isEmpty()) {
                candidates.add("<" + leafOwnerClass + ": " + javaType
                        + " " + leafField + ">");
            }
            for (String candidate : candidates) {
                String[] declaration = declaredField(candidate);
                if (safe(candidate).equals(safe(actualSignature))
                        && declaration != null
                        && declaration[0].equals(actual[0])
                        && declaration[2].equals(actual[2])
                        && javaTypeDescriptor(declaration[1]).equals(
                        javaTypeDescriptor(actual[1]))) {
                    declaredByAction = true;
                    break;
                }
            }
            if (!declaredByAction) {
                return DeclaredArrayInputType.incomplete(
                        "actual consumed leaf declaration is absent from "
                                + "the symbolize action");
            }
            if (!leafOwnerClass.isEmpty() && !instanceOfName(
                    leafOwner.getClass(), leafOwnerClass)) {
                return DeclaredArrayInputType.incomplete(
                        "actual consumed leaf owner differs from the "
                                + "declared leaf owner class");
            }
            Field reflected = exactDeclaredInstanceField(leafOwner,
                    actualSignature);
            if (reflected == null || Modifier.isStatic(
                    reflected.getModifiers())
                    || !reflected.getType().isArray()
                    || !javaTypeDescriptor(actual[1]).equals(
                    reflectionDescriptor(reflected.getType()))) {
                return DeclaredArrayInputType.incomplete(actual[1],
                        "actual consumed leaf reflection/type is not one "
                                + "exact instance array field");
            }
            if (!javaTypeDescriptor(javaType).equals(
                    javaTypeDescriptor(actual[1]))) {
                return DeclaredArrayInputType.incomplete(actual[1],
                        "action javaType does not equal the exact consumed "
                                + "leaf array type");
            }
            return DeclaredArrayInputType.exact(actual[1],
                    "EXACT_CONSUMED_LEAF_FIELD_SIGNATURE_AND_REFLECTION:"
                            + safe(actualSignature));
        }

        private boolean identifiesConsumedLeaf(
                Object leafOwner, String actualSignature,
                String actualField) {
            String[] actual = declaredField(actualSignature);
            if (actual == null || leafOwner == null
                    || !actual[2].equals(safe(actualField))
                    || !instanceOfName(leafOwner.getClass(), actual[0])) {
                return false;
            }
            Set<String> candidates = new LinkedHashSet<>(
                    leafFieldSignaturesByPath.values());
            candidates.add(accessFieldSignature);
            candidates.add(field);
            candidates.add(cell);
            if (!leafOwnerClass.isEmpty() && !leafField.isEmpty()
                    && !javaType.isEmpty()) {
                candidates.add("<" + leafOwnerClass + ": " + javaType
                        + " " + leafField + ">");
            }
            for (String candidate : candidates) {
                String[] declaration = declaredField(candidate);
                if (safe(candidate).equals(safe(actualSignature))
                        && declaration != null
                        && declaration[0].equals(actual[0])
                        && declaration[2].equals(actual[2])
                        && javaTypeDescriptor(declaration[1]).equals(
                        javaTypeDescriptor(actual[1]))) {
                    return true;
                }
            }
            return false;
        }

        private boolean matchesConsumedFieldSite(String actualMethod,
                                                 int actualUnitIndex) {
            return "RUNTIME_UNIQUE_STATIC_LEAF_GETFIELD_SITE_AND_OWNER_"
                    .concat("WITHIN_REGION_INSTANCE_V1").equals(
                            consumedFieldSiteAuthority)
                    && consumedFieldMethod.equals(safe(actualMethod))
                    && consumedFieldUnitIndex == actualUnitIndex
                    && !consumedFieldSiteId.isEmpty()
                    && consumedFieldSiteId.equals(siteId(actualMethod,
                    actualUnitIndex));
        }

        private List<String> logicalPathForConsumedLeaf(
                String actualSignature, String actualField) {
            for (List<String> path : fieldPaths) {
                if (!path.isEmpty()
                        && safe(actualField).equals(path.get(
                        path.size() - 1))
                        && safe(actualSignature).equals(
                        leafFieldSignaturesByPath.get(
                                joinFieldPath(path)))) {
                    return new ArrayList<>(path);
                }
            }
            if (!fieldPath.isEmpty()
                    && safe(actualField).equals(fieldPath.get(
                    fieldPath.size() - 1))) {
                String declared = leafFieldSignaturesByPath.get(
                        joinFieldPath(fieldPath));
                if (safe(actualSignature).equals(declared)
                        || safe(actualSignature).equals(field)
                        || safe(actualSignature).equals(cell)
                        || safe(actualSignature).equals(
                        accessFieldSignature)) {
                    return new ArrayList<>(fieldPath);
                }
            }
            if (fields.contains(safe(actualField))) {
                return Collections.singletonList(safe(actualField));
            }
            String[] declared = declaredField(actualSignature);
            if (declared != null && safe(actualField).equals(declared[2])
                    && (safe(actualSignature).equals(field)
                    || safe(actualSignature).equals(cell)
                    || safe(actualSignature).equals(
                    accessFieldSignature))) {
                return Collections.singletonList(safe(actualField));
            }
            return Collections.emptyList();
        }

        private boolean matchesLocal(String actualMethod, String actualLocal) {
            return "LOCAL_DEFINITION".equals(bindingMode)
                    && method.equals(safe(actualMethod))
                    && local.equals(safe(actualLocal));
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
                    || !accessSiteId.isEmpty() || accessUnitIndex >= 0
                    || !accessSiteAuthority.isEmpty();
            if (accessSiteConstrained
                    && (!("STATIC_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1"
                    .equals(accessSiteAuthority))
                    || !accessMethod.equals(safe(actualMethod))
                    || accessUnitIndex != actualUnitIndex
                    || !accessSiteId.equals(siteId(actualMethod,
                    actualUnitIndex)))) {
                return false;
            }
            boolean accessorConstrained = !accessorCallerMethod.isEmpty()
                    || !accessorCallSiteId.isEmpty()
                    || accessorCallUnitIndex >= 0
                    || !accessorDeclaredCallee.isEmpty()
                    || !accessorCallSiteAuthority.isEmpty()
                    || !accessorImplementationMethod.isEmpty()
                    || !accessorImplementationAuthority.isEmpty();
            Boolean lightweightContext = accessorContextOverride != null
                    ? null : lightweightAccessorContextMatches(
                    accessorCallerMethod, accessorCallUnitIndex,
                    accessorCallSiteId, accessorDeclaredCallee, owner);
            boolean accessorContextMatches = accessorContextOverride != null
                    ? accessorContextOverride
                    : lightweightContext != null
                    ? lightweightContext
                    : CausynthTraceRecorder.currentCallParentSiteMatches(
                    accessorCallerMethod, accessorCallUnitIndex,
                    accessorCallSiteId, accessorDeclaredCallee);
            if (accessorConstrained
                    && (!("STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                    .concat("ACCESSOR_CALLSITE_V1").equals(
                            accessorCallSiteAuthority))
                    || !"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY"
                    .equals(accessorImplementationAuthority)
                    || !accessorImplementationMethod.equals(
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
    }

    static boolean symbolizeActionMatchesFieldForTests(JsonObject action,
                                                        Object owner,
                                                        String signature,
                                                        String field) {
        return new SymbolizeAction(action).matchesField("", -1, owner,
                signature, field);
    }

    static boolean symbolizeActionMatchesFieldAtSiteForTests(
            JsonObject action, String method, int unitIndex, Object owner,
            String signature, String field) {
        return new SymbolizeAction(action).matchesField(method, unitIndex,
                owner, signature, field);
    }

    static boolean symbolizeActionMatchesFieldAtAccessorCallSiteForTests(
            JsonObject action, String method, int unitIndex, Object owner,
            String signature, String field,
            boolean accessorContextMatches) {
        return new SymbolizeAction(action).matchesField(method, unitIndex,
                owner, signature, field, accessorContextMatches);
    }

    private static String[] declaredField(String cell) {
        String value = safe(cell);
        int projection = value.indexOf("#field:");
        String base = projection < 0 ? value
                : value.substring(0, projection);
        Matcher matcher = FIELD_DETAIL.matcher(base);
        if (!matcher.matches()) {
            return null;
        }
        return new String[]{matcher.group(1).trim(),
                matcher.group(2).trim(), matcher.group(3).trim()};
    }

    private static String exactFieldIdentity(String[] declared) {
        return declared == null || declared.length != 3 ? ""
                : declared[0] + "\u0000" + normalizeFieldType(declared[1])
                + "\u0000" + declared[2];
    }

    /**
     * The frozen JDK API accepts only a field name.  It walks every
     * non-static field in the runtime hierarchy, so an exact Soot signature
     * is safe to pass only when that name occurs once in the whole hierarchy.
     */
    private static boolean uniqueNameResolvesExactDeclaredField(
            Object owner, String fieldSignature) {
        String[] declared = declaredField(fieldSignature);
        Field exact = exactDeclaredInstanceField(owner, fieldSignature);
        if (owner == null || declared == null || exact == null) return false;
        int occurrences = 0;
        Class<?> current = owner.getClass();
        while (current != null) {
            for (Field candidate : current.getDeclaredFields()) {
                if (!Modifier.isStatic(candidate.getModifiers())
                        && declared[2].equals(candidate.getName())) {
                    occurrences++;
                }
            }
            current = current.getSuperclass();
        }
        return occurrences == 1
                && exact.getDeclaringClass().getName().equals(declared[0]);
    }

    /**
     * Finite producer-side projection requested by an exact downstream array
     * element field access.  Unlike ARRAY_ELEMENT_FIELD this declaration owns
     * a backing Map input and a producer output array; it is never interpreted
     * as an ordinary array input selector.
     */
    private static final class MapValueElementProjectionSpec {
        private static final String KIND =
                "MAP_VALUE_TO_OUTPUT_ARRAY_ELEMENT_FIELD";
        private static final String SELECTOR_AUTHORITY =
                "CURRENT_EXECUTION_ENTRY_SNAPSHOT_THEN_EXACT_"
                        + "OUTPUT_INDEX_IDENTITY";

        private final int schemaVersion;
        private final String kind;
        private final String bindingId;
        private final String mapInputPort;
        private final String mapInputCell;
        private final String outputPort;
        private final String outputCell;
        private final List<String> outputFieldPath = new ArrayList<>();
        private final String outputValidationMode;
        private final String mapProjectionOperation;
        private final String mapViewSiteId;
        private final String snapshotSiteId;
        private final String downstreamRegionInstance;
        private final String downstreamInputPort;
        private final String downstreamBaseInputSymbol;
        private final String downstreamContainerBindingId;
        private final String declaredFieldSignature;
        private final String declaredFieldOwnerClass;
        private final String declaredFieldType;
        private final String declaredFieldName;
        private final List<String> fieldPath = new ArrayList<>();
        private final String selectorAuthority;
        private final List<String> projectionProofCausalEdgeIds =
                new ArrayList<>();
        private final boolean complete;

        private MapValueElementProjectionSpec(JsonObject json) {
            this.schemaVersion = integer(json, "schemaVersion", -1);
            this.kind = string(json, "kind");
            this.bindingId = string(json, "bindingId");
            this.mapInputPort = string(json, "mapInputPort");
            this.mapInputCell = string(json, "mapInputCell");
            this.outputPort = string(json, "outputPort");
            this.outputCell = string(json, "outputCell");
            for (JsonElement element : array(json, "outputFieldPath")) {
                if (element.isJsonPrimitive()) {
                    outputFieldPath.add(element.getAsString());
                }
            }
            this.outputValidationMode = string(json,
                    "outputValidationMode");
            this.mapProjectionOperation = string(json,
                    "mapProjectionOperation");
            this.mapViewSiteId = string(json, "mapViewSiteId");
            this.snapshotSiteId = string(json, "snapshotSiteId");
            this.downstreamRegionInstance = string(json,
                    "downstreamRegionInstance");
            this.downstreamInputPort = string(json,
                    "downstreamInputPort");
            this.downstreamBaseInputSymbol = string(json,
                    "downstreamBaseInputSymbol");
            this.downstreamContainerBindingId = string(json,
                    "downstreamContainerBindingId");
            this.declaredFieldSignature = string(json,
                    "declaredFieldSignature");
            this.declaredFieldOwnerClass = string(json,
                    "declaredFieldOwnerClass");
            this.declaredFieldType = normalizeFieldType(string(json,
                    "declaredFieldType"));
            this.declaredFieldName = string(json, "declaredFieldName");
            for (JsonElement element : array(json, "fieldPath")) {
                if (element.isJsonPrimitive()) {
                    fieldPath.add(element.getAsString());
                }
            }
            this.selectorAuthority = string(json, "selectorAuthority");
            for (JsonElement element : array(json,
                    "projectionProofCausalEdgeIds")) {
                if (element.isJsonPrimitive()) {
                    projectionProofCausalEdgeIds.add(
                            element.getAsString());
                }
            }
            this.complete = bool(json, "complete", false);
        }

        private String validationError(Activation activation,
                                       SymbolizeAction action) {
            if (schemaVersion != 1 || !KIND.equals(kind) || !complete) {
                return "unsupported or incomplete projection schema/kind";
            }
            if (bindingId.isEmpty() || mapInputPort.isEmpty()
                    || mapInputCell.isEmpty() || outputPort.isEmpty()
                    || outputCell.isEmpty()) {
                return "projection endpoint identity is incomplete";
            }
            if (!mapInputPort.equals(action.symbol)
                    || !mapInputCell.equals(action.cell)
                    || activation.actionCount(mapInputPort) != 1) {
                return "map input does not identify one exact action";
            }
            if (!"MAP_VALUES_VIEW".equals(mapProjectionOperation)) {
                return "unsupported map projection operation";
            }
            if (!SELECTOR_AUTHORITY.equals(selectorAuthority)
                    || mapViewSiteId.isEmpty() || snapshotSiteId.isEmpty()
                    || projectionProofCausalEdgeIds.isEmpty()) {
                return "projection selector/proof is incomplete";
            }
            if (!("EXACT_REQUESTED_OUTPUT_CAPTURE".equals(
                    outputValidationMode)
                    || "ROOT_RETURN_PROJECTED_FIELD".equals(
                    outputValidationMode))) {
                return "output identity validation mode is unsupported";
            }
            String[] declared = declaredField(declaredFieldSignature);
            if (declared == null
                    || !declaredFieldOwnerClass.equals(declared[0])
                    || !declaredFieldType.equals(normalizeFieldType(
                    declared[1]))
                    || !declaredFieldName.equals(declared[2])
                    || !fieldPath.equals(Collections.singletonList(
                    declaredFieldName))) {
                return "demanded field declaration is not exact";
            }
            if (downstreamRegionInstance.isEmpty()
                    || downstreamInputPort.isEmpty()
                    || downstreamBaseInputSymbol.isEmpty()
                    || downstreamContainerBindingId.isEmpty()) {
                return "downstream selected demand provenance is incomplete";
            }
            String[] outputDeclared = declaredField(outputCell);
            if (outputDeclared != null
                    && !outputFieldPath.equals(Collections.singletonList(
                    outputDeclared[2]))) {
                return "projected output field path is not exact";
            }
            if (outputDeclared == null && !outputFieldPath.isEmpty()) {
                return "non-field output cannot carry a field path";
            }
            return "";
        }

        private String groupId() {
            return mapInputPort + "\n" + outputPort + "\n" + outputCell
                    + "\n" + mapProjectionOperation;
        }

        private String materializationSiteId() {
            return snapshotSiteId + "#map-element:" + bindingId;
        }
    }

    /**
     * Activation-authored selector for one field occurrence owned by an
     * element of an object array input.  This is deliberately a small generic
     * union member rather than an inferred container heuristic: a planner must
     * name both the static field family and its exact owning container port.
     */
    private static final class ContainerElementFieldBindingSpec {
        private static final String KIND = "ARRAY_ELEMENT_FIELD";
        private static final String EXACT_ARRAY_INDEX =
                "EXACT_ARRAY_INDEX";
        private static final String DISCOVER_UNIQUE_IDENTITY_INDEX =
                "DISCOVER_UNIQUE_IDENTITY_INDEX";

        private final int schemaVersion;
        private final String kind;
        private final String bindingId;
        private final String baseInputSymbol;
        private final String containerInputPort;
        private final String containerInputCell;
        private final String selectorAuthority;
        private final int elementIndex;
        private final int elementOccurrence;
        private final String fieldMaterializationSiteId;
        private final List<String> fieldPath = new ArrayList<>();
        private final String declaredFieldOwnerClass;
        private final String declaredFieldType;

        private ContainerElementFieldBindingSpec(JsonObject json) {
            this.schemaVersion = integer(json, "schemaVersion", 1);
            this.kind = string(json, "kind");
            this.bindingId = string(json, "bindingId");
            this.baseInputSymbol = string(json, "baseInputSymbol");
            this.containerInputPort = string(json, "containerInputPort");
            this.containerInputCell = string(json, "containerInputCell");
            this.elementIndex = integer(json, "elementIndex", -1);
            this.selectorAuthority = firstNonBlank(
                    string(json, "selectorAuthority"),
                    this.elementIndex >= 0 ? EXACT_ARRAY_INDEX : "");
            this.elementOccurrence = integer(json, "elementOccurrence",
                    integer(json, "occurrence", -1));
            this.fieldMaterializationSiteId = string(json,
                    "fieldMaterializationSiteId");
            for (JsonElement element : array(json, "fieldPath")) {
                if (element.isJsonPrimitive()) {
                    fieldPath.add(element.getAsString());
                }
            }
            this.declaredFieldOwnerClass = string(json,
                    "declaredFieldOwnerClass");
            this.declaredFieldType = normalizeFieldType(string(json,
                    "declaredFieldType"));
        }

        private String structuralValidationError(Activation activation,
                                                 SymbolizeAction action,
                                                 Object leafOwner,
                                                 String fieldSignature) {
            if (schemaVersion != 1 || !KIND.equals(kind)) {
                return "unsupported generic binding schema/kind";
            }
            if (bindingId.isEmpty() || baseInputSymbol.isEmpty()
                    || containerInputPort.isEmpty()
                    || containerInputCell.isEmpty()) {
                return "binding identity or container endpoint is missing";
            }
            if (fieldMaterializationSiteId.isEmpty()) {
                return "field materialization site is missing";
            }
            if (baseInputSymbol.equals(containerInputPort)) {
                return "base field port cannot also be its container port";
            }
            if (EXACT_ARRAY_INDEX.equals(selectorAuthority)) {
                if (elementIndex < 0 || elementOccurrence < 1) {
                    return "exact array index or occurrence is invalid";
                }
            } else if (DISCOVER_UNIQUE_IDENTITY_INDEX.equals(
                    selectorAuthority)) {
                if (elementIndex != -1 || elementOccurrence == 0
                        || elementOccurrence < -1) {
                    return "identity discovery requires elementIndex=-1 "
                            + "and occurrence=-1 or a positive value";
                }
            } else {
                return "unsupported or missing selector authority";
            }
            if (activation.actionCount(baseInputSymbol) != 1
                    || activation.actionCount(containerInputPort) != 1) {
                return "base or container action is not unique";
            }
            SymbolizeAction containerAction = activation.uniqueAction(
                    containerInputPort);
            if (containerAction == null
                    || !containerInputCell.equals(containerAction.cell)) {
                return "container port/cell does not identify one action";
            }
            if (!baseInputSymbol.equals(action.symbol)
                    || !fieldPath.equals(action.fieldPath)) {
                return "base input or field path does not match action";
            }
            String[] declared = declaredField(fieldSignature);
            if (declared == null
                    || !declaredFieldOwnerClass.equals(declared[0])
                    || !declaredFieldType.equals(
                    normalizeFieldType(declared[1]))
                    || action.fieldPath.isEmpty()
                    || !declared[2].equals(action.leafField)) {
                return "declared owner/type/field does not match hook";
            }
            if (leafOwner == null || !instanceOfName(leafOwner.getClass(),
                    declaredFieldOwnerClass)) {
                return "concrete field owner has the wrong declared type";
            }
            ExactFieldObservation field = observeExactField(leafOwner,
                    fieldSignature);
            if (!field.ownerVerified || !field.typeVerified
                    || !field.available) {
                return "exact declared field reflection failed: "
                        + field.error;
            }
            return "";
        }

        private String effectiveSelectorError(String effectiveSite,
                                              int effectiveOccurrence) {
            if (!fieldMaterializationSiteId.equals(safe(effectiveSite))) {
                return "effective materialization site does not match the "
                        + "static selector";
            }
            if (elementOccurrence > 0
                    && elementOccurrence != effectiveOccurrence) {
                return "effective materialization occurrence does not "
                        + "match the static selector";
            }
            return "";
        }

        private boolean requiresExactCoverage() {
            return schemaVersion == 1 && KIND.equals(kind)
                    && EXACT_ARRAY_INDEX.equals(selectorAuthority)
                    && !bindingId.isEmpty() && !baseInputSymbol.isEmpty()
                    && elementIndex >= 0 && elementOccurrence > 0
                    && !fieldMaterializationSiteId.isEmpty();
        }

        private int resolveElementIndex(Object container,
                                        Object leafOwner) {
            if (container == null || !container.getClass().isArray()) {
                return -1;
            }
            int length = Array.getLength(container);
            if (EXACT_ARRAY_INDEX.equals(selectorAuthority)) {
                if (elementIndex < 0 || elementIndex >= length) return -1;
                return Array.get(container, elementIndex) == leafOwner
                        ? elementIndex : -1;
            }
            if (!DISCOVER_UNIQUE_IDENTITY_INDEX.equals(
                    selectorAuthority)) {
                return -1;
            }
            int selected = -1;
            for (int index = 0; index < length; index++) {
                if (Array.get(container, index) != leafOwner) continue;
                if (selected >= 0) return -1;
                selected = index;
            }
            return selected;
        }

        private String elementResolutionError(Object container,
                                              Object leafOwner) {
            if (container == null || !container.getClass().isArray()) {
                return "container is not an observed array";
            }
            int length = Array.getLength(container);
            if (EXACT_ARRAY_INDEX.equals(selectorAuthority)) {
                if (elementIndex < 0 || elementIndex >= length) {
                    return "element index is outside the observed array";
                }
                return "array element identity does not equal field owner";
            }
            int identities = 0;
            for (int index = 0; index < length; index++) {
                if (Array.get(container, index) == leafOwner) identities++;
            }
            return identities == 0
                    ? "field owner is absent from the observed array"
                    : "field owner occurs more than once in the observed "
                    + "array; identity index is ambiguous";
        }

        /**
         * True only for an ordinary owner-wide hook which cannot be this
         * declaration.  Invalid containers, out-of-range exact selectors,
         * and repeated discovery identities remain fatal rather than being
         * mistaken for unrelated reads.
         */
        private boolean unrelatedOwner(Object container, Object leafOwner) {
            if (container == null || !container.getClass().isArray()) {
                return false;
            }
            int length = Array.getLength(container);
            if (EXACT_ARRAY_INDEX.equals(selectorAuthority)) {
                return elementIndex >= 0 && elementIndex < length
                        && Array.get(container, elementIndex) != leafOwner;
            }
            if (!DISCOVER_UNIQUE_IDENTITY_INDEX.equals(selectorAuthority)) {
                return false;
            }
            for (int index = 0; index < length; index++) {
                if (Array.get(container, index) == leafOwner) {
                    return false;
                }
            }
            return true;
        }
    }

    /** Solver value plus its concrete program-input location. */
    private static final class ModelAssignment {
        private final String key;
        private final String engineSymbol;
        private final String inputSymbol;
        private final String baseInputSymbol;
        private final String valueType;
        private final String value;
        private final String authority;
        private final String modelOperation;
        private final String dynamicBindingId;
        private final String dynamicFieldSymbol;
        private final String materializationSiteId;
        private final int materializationOccurrence;
        private final String entryReadObservationId;
        private final String containerBindingId;
        private final String containerInputPort;
        private final String containerInputCell;
        private final String selectorAuthority;
        private final int elementIndex;
        private final int elementOccurrence;
        private final String declaredFieldOwnerClass;
        private final String declaredFieldType;
        private final String mapProjectionBindingId;
        private final String mapProjectionInputPort;
        private final String mapProjectionInputCell;
        private final String mapProjectionOutputPort;
        private final String mapProjectionOutputCell;
        private final String mapProjectionOperation;
        private final int mapProjectionOutputIndex;
        private final int mapProjectionElementOccurrence;
        private final String mapProjectionSelectorKind;
        private final String mapProjectionSelectorAuthority;
        private final String mapProjectionObjectTokenAuthority;
        private final String mapProjectionObjectTokenScope;
        private final String mapProjectionCrossExecutionOrdinalAuthority;
        private final String mapProjectionDeclaredFieldOwnerClass;
        private final String mapProjectionDeclaredFieldType;
        private final String mapProjectionDeclaredFieldSignature;
        private final long mapProjectionMapObjectToken;
        private final long mapProjectionElementObjectToken;
        private final long mapProjectionOutputArrayObjectToken;
        private final boolean mapProjectionOutputIdentityVerified;
        private final String mapProjectionOutputVerificationAuthority;
        private final JsonElement mapProjectionExpectedMapKey;
        private final String mapProjectionExpectedMapKeyAuthority;
        private final String mapProjectionSourceOutputIndexAuthority;
        private final String mapProjectionReplaySelectionAuthority;
        private final String mapProjectionSourceObjectTokenScope;
        private final String mapProjectionReplayScopeRebindingAuthority;
        private final boolean mapProjectionSelectorCompleteFlag;
        private final JsonElement expectedEntryKey;
        private final String expectedEntryKeyAuthority;
        private final String dynamicReplayRebindingAuthority;
        private final boolean sourceEntrySelectorRetained;
        private final boolean legacyUniqueFieldTarget;
        private final List<String> path = new ArrayList<>();

        private ModelAssignment(JsonObject json) {
            this.engineSymbol = string(json, "engineSymbol");
            this.inputSymbol = string(json, "inputSymbol");
            this.baseInputSymbol = string(json, "baseInputSymbol");
            this.valueType = string(json, "valueType");
            this.value = string(json, "value");
            this.authority = string(json, "authority");
            this.modelOperation = string(json, "modelOperation");
            this.dynamicBindingId = string(json, "dynamicBindingId");
            this.dynamicFieldSymbol = string(json, "dynamicFieldSymbol");
            this.materializationSiteId = string(json,
                    "materializationSiteId");
            this.materializationOccurrence = integer(json,
                    "materializationOccurrence", -1);
            this.entryReadObservationId = string(json,
                    "entryReadObservationId");
            JsonElement selectorElement = json.get("containerSelector");
            JsonObject selector = selectorElement != null
                    && selectorElement.isJsonObject()
                    ? selectorElement.getAsJsonObject() : new JsonObject();
            this.containerBindingId = firstNonBlank(
                    string(selector, "bindingId"),
                    string(json, "containerBindingId"));
            this.containerInputPort = firstNonBlank(
                    string(selector, "containerInputPort"),
                    string(json, "containerInputPort"));
            this.containerInputCell = firstNonBlank(
                    string(selector, "containerInputCell"),
                    string(json, "containerInputCell"));
            this.selectorAuthority = firstNonBlank(
                    string(selector, "selectorAuthority"),
                    string(json, "selectorAuthority"));
            this.elementIndex = selector.has("elementIndex")
                    ? integer(selector, "elementIndex", -1)
                    : integer(json, "elementIndex", -1);
            this.elementOccurrence = selector.has("elementOccurrence")
                    ? integer(selector, "elementOccurrence", -1)
                    : integer(json, "elementOccurrence", -1);
            this.declaredFieldOwnerClass = firstNonBlank(
                    string(selector, "declaredFieldOwnerClass"),
                    string(json, "declaredFieldOwnerClass"));
            this.declaredFieldType = normalizeFieldType(firstNonBlank(
                    string(selector, "declaredFieldType"),
                    string(json, "declaredFieldType")));
            JsonElement mapSelectorElement = json.get(
                    "mapProjectionSelector");
            JsonObject mapSelector = mapSelectorElement != null
                    && mapSelectorElement.isJsonObject()
                    ? mapSelectorElement.getAsJsonObject()
                    : new JsonObject();
            this.mapProjectionBindingId = string(mapSelector,
                    "bindingId");
            this.mapProjectionInputPort = string(mapSelector,
                    "mapInputPort");
            this.mapProjectionInputCell = string(mapSelector,
                    "mapInputCell");
            this.mapProjectionOutputPort = string(mapSelector,
                    "outputPort");
            this.mapProjectionOutputCell = string(mapSelector,
                    "outputCell");
            this.mapProjectionOperation = string(mapSelector,
                    "mapProjectionOperation");
            this.mapProjectionOutputIndex = integer(mapSelector,
                    "outputIndex", -1);
            this.mapProjectionElementOccurrence = integer(mapSelector,
                    "elementOccurrence", -1);
            this.mapProjectionSelectorKind = string(mapSelector, "kind");
            this.mapProjectionSelectorAuthority = string(mapSelector,
                    "authority");
            this.mapProjectionObjectTokenAuthority = string(mapSelector,
                    "objectTokenAuthority");
            this.mapProjectionObjectTokenScope = string(mapSelector,
                    "objectTokenScope");
            this.mapProjectionCrossExecutionOrdinalAuthority = string(
                    mapSelector, "crossExecutionOrdinalAuthority");
            this.mapProjectionDeclaredFieldOwnerClass = string(mapSelector,
                    "declaredFieldOwnerClass");
            this.mapProjectionDeclaredFieldType = normalizeFieldType(string(
                    mapSelector, "declaredFieldType"));
            this.mapProjectionDeclaredFieldSignature = string(mapSelector,
                    "declaredFieldSignature");
            this.mapProjectionMapObjectToken = longInteger(mapSelector,
                    "mapObjectToken", 0L);
            this.mapProjectionElementObjectToken = longInteger(mapSelector,
                    "elementObjectToken", 0L);
            this.mapProjectionOutputArrayObjectToken = longInteger(
                    mapSelector, "outputArrayObjectToken", 0L);
            this.mapProjectionOutputIdentityVerified = bool(mapSelector,
                    "outputIdentityVerified", false);
            this.mapProjectionOutputVerificationAuthority = string(
                    mapSelector, "outputVerificationAuthority");
            JsonElement mapExpectedKey = mapSelector.get("expectedMapKey");
            this.mapProjectionExpectedMapKey = mapExpectedKey == null
                    || mapExpectedKey.isJsonNull() ? null
                    : copyJsonTree(mapExpectedKey);
            this.mapProjectionExpectedMapKeyAuthority = string(mapSelector,
                    "expectedMapKeyAuthority");
            this.mapProjectionSourceOutputIndexAuthority = string(
                    mapSelector, "sourceOutputIndexAuthority");
            this.mapProjectionReplaySelectionAuthority = string(
                    mapSelector, "replaySelectionAuthority");
            this.mapProjectionSourceObjectTokenScope = string(mapSelector,
                    "sourceObjectTokenScope");
            this.mapProjectionReplayScopeRebindingAuthority = string(
                    mapSelector, "replayScopeRebindingAuthority");
            this.mapProjectionSelectorCompleteFlag = bool(mapSelector,
                    "complete", false);
            JsonElement expectedKey = json.get("expectedEntryKey");
            this.expectedEntryKey = expectedKey == null
                    || expectedKey.isJsonNull() ? null
                    : copyJsonTree(expectedKey);
            this.expectedEntryKeyAuthority = string(json,
                    "expectedEntryKeyAuthority");
            this.dynamicReplayRebindingAuthority = string(json,
                    "dynamicReplayRebindingAuthority");
            this.sourceEntrySelectorRetained = bool(json,
                    "sourceEntrySelectorRetained", true);
            this.legacyUniqueFieldTarget = bool(json,
                    "legacyUniqueFieldTarget", false);
            for (JsonElement element : array(json,
                    "materializationPath")) {
                if (element.isJsonPrimitive()) path.add(
                        element.getAsString());
            }
            this.key = firstNonBlank(dynamicBindingId, engineSymbol,
                    inputSymbol + ":" + joinFieldPath(path));
        }

        private boolean matches(SymbolizeAction action,
                                List<String> actualPath) {
            if (hasDynamicMetadata()) return false;
            if (!inputSymbol.equals(action.symbol)) return false;
            if (path.isEmpty()) return actualPath == null
                    || actualPath.isEmpty() || action.fieldPath.equals(
                    actualPath);
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

        private boolean hasDynamicMetadata() {
            return !dynamicBindingId.isEmpty()
                    || !dynamicFieldSymbol.isEmpty()
                    || !materializationSiteId.isEmpty()
                    || materializationOccurrence > 0
                    || !entryReadObservationId.isEmpty()
                    || expectedEntryKey != null
                    || !expectedEntryKeyAuthority.isEmpty()
                    || hasMapProjectionSelectorMetadata();
        }

        private boolean matchesMapProjection(
                MapProjectionFieldBinding binding) {
            return binding != null
                    && binding.snapshot.replayAuthorized(this,
                    binding.outputIndex)
                    && dynamicSelectorComplete()
                    && inputSymbol.equals(binding.baseInputSymbol)
                    && baseInputSymbol.equals(binding.baseInputSymbol)
                    && dynamicBindingId.equals(binding.dynamicBindingId)
                    && dynamicFieldSymbol.equals(
                    binding.dynamicFieldSymbol)
                    && materializationSiteId.equals(
                    binding.materializationSiteId)
                    && materializationOccurrence
                    == binding.materializationOccurrence
                    && fieldPathMatches(binding.fieldPath)
                    && engineSymbolMatches(binding.dynamicFieldSymbol)
                    && mapProjectionSelectorComplete()
                    && mapProjectionBindingId.equals(
                    binding.spec.bindingId)
                    && mapProjectionInputPort.equals(
                    binding.spec.mapInputPort)
                    && mapProjectionInputCell.equals(
                    binding.spec.mapInputCell)
                    && mapProjectionOutputPort.equals(
                    binding.spec.outputPort)
                    && mapProjectionOutputCell.equals(
                    binding.spec.outputCell)
                    && mapProjectionOperation.equals(
                    binding.spec.mapProjectionOperation)
                    && mapProjectionOutputIndex == binding.outputIndex
                    && mapProjectionElementOccurrence
                    == binding.materializationOccurrence
                    && mapProjectionDeclaredFieldOwnerClass.equals(
                    binding.spec.declaredFieldOwnerClass)
                    && mapProjectionDeclaredFieldType.equals(
                    binding.spec.declaredFieldType)
                    && mapProjectionDeclaredFieldSignature.equals(
                    binding.spec.declaredFieldSignature)
                    && mapProjectionExpectedMapKey != null
                    && mapProjectionExpectedMapKey.equals(
                    binding.expectedMapKey)
                    && !stableMapProjectionKeySelector(
                    mapProjectionExpectedMapKey).isEmpty()
                    // Object tokens are activation-local and therefore are
                    // deliberately not compared across executions.  Their
                    // producer activation scope and authority must still be
                    // exact so a downstream instance cannot authorize this
                    // producer-side field write.
                    && mapProjectionObjectTokenScope.equals(
                    binding.objectTokenScope);
        }

        private boolean targetsMapProjection(
                MapValueElementProjectionSpec spec) {
            return spec != null && hasMapProjectionSelectorMetadata()
                    && inputSymbol.equals(spec.mapInputPort)
                    && baseInputSymbol.equals(spec.mapInputPort)
                    && mapProjectionBindingId.equals(spec.bindingId)
                    && mapProjectionInputPort.equals(spec.mapInputPort)
                    && mapProjectionInputCell.equals(spec.mapInputCell)
                    && mapProjectionOutputPort.equals(spec.outputPort)
                    && mapProjectionOutputCell.equals(spec.outputCell)
                    && mapProjectionOperation.equals(
                    spec.mapProjectionOperation);
        }

        private boolean validMapProjectionReplaySelector(
                MapValueElementProjectionSpec spec,
                MapProjectionSnapshot snapshot, int currentIndex) {
            if (!targetsMapProjection(spec)
                    || !mapProjectionSelectorComplete()
                    || currentIndex < 0
                    || currentIndex >= snapshot.elements.length
                    || mapProjectionOutputIndex != currentIndex
                    || mapProjectionElementOccurrence != currentIndex + 1
                    || materializationOccurrence != currentIndex + 1
                    || !materializationSiteId.equals(
                    spec.materializationSiteId())
                    || !fieldPathMatches(spec.fieldPath)
                    || !mapProjectionDeclaredFieldOwnerClass.equals(
                    spec.declaredFieldOwnerClass)
                    || !mapProjectionDeclaredFieldType.equals(
                    spec.declaredFieldType)
                    || !mapProjectionDeclaredFieldSignature.equals(
                    spec.declaredFieldSignature)
                    || !mapProjectionObjectTokenScope.equals(
                    snapshot.objectTokenScope)
                    || !("ROOT_RETURN_PROJECTED_FIELD".equals(
                    spec.outputValidationMode)
                    && "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD"
                    .equals(mapProjectionOutputVerificationAuthority)
                    || "EXACT_REQUESTED_OUTPUT_CAPTURE".equals(
                    spec.outputValidationMode)
                    && ("ACTIVE_TOKEN_EXACT_ORIGINAL_CALL_ARGUMENT".equals(
                    mapProjectionOutputVerificationAuthority)
                    || "ACTIVE_TOKEN_EXACT_POST_INSTANCE_FIELD_ASSIGNMENT"
                    .equals(mapProjectionOutputVerificationAuthority)))) {
                return false;
            }
            String expectedDynamic = dynamicFieldSymbolForTests(
                    spec.mapInputPort, spec.materializationSiteId(),
                    currentIndex + 1);
            return dynamicFieldSymbol.equals(expectedDynamic)
                    && dynamicBindingId.equals(
                    "DYNAMIC_FIELD:" + expectedDynamic)
                    && engineSymbolMatches(expectedDynamic)
                    && mapProjectionExpectedMapKey != null
                    && mapProjectionExpectedMapKey.equals(
                    snapshot.entryKeyExpressions[currentIndex]);
        }

        private boolean hasMapProjectionSelectorMetadata() {
            return !mapProjectionBindingId.isEmpty()
                    || !mapProjectionInputPort.isEmpty()
                    || !mapProjectionInputCell.isEmpty()
                    || !mapProjectionOutputPort.isEmpty()
                    || !mapProjectionOutputCell.isEmpty()
                    || !mapProjectionOperation.isEmpty()
                    || mapProjectionOutputIndex >= 0
                    || mapProjectionElementOccurrence > 0
                    || !mapProjectionSelectorKind.isEmpty()
                    || !mapProjectionSelectorAuthority.isEmpty()
                    || !mapProjectionObjectTokenAuthority.isEmpty()
                    || !mapProjectionObjectTokenScope.isEmpty()
                    || !mapProjectionCrossExecutionOrdinalAuthority
                    .isEmpty()
                    || !mapProjectionDeclaredFieldOwnerClass.isEmpty()
                    || !mapProjectionDeclaredFieldType.isEmpty()
                    || !mapProjectionDeclaredFieldSignature.isEmpty()
                    || mapProjectionMapObjectToken > 0L
                    || mapProjectionElementObjectToken > 0L
                    || mapProjectionOutputArrayObjectToken > 0L
                    || mapProjectionExpectedMapKey != null
                    || !mapProjectionExpectedMapKeyAuthority.isEmpty()
                    || !mapProjectionSourceOutputIndexAuthority.isEmpty()
                    || !mapProjectionReplaySelectionAuthority.isEmpty()
                    || !mapProjectionSourceObjectTokenScope.isEmpty()
                    || !mapProjectionReplayScopeRebindingAuthority.isEmpty()
                    || mapProjectionOutputIdentityVerified
                    || mapProjectionSelectorCompleteFlag;
        }

        private boolean mapProjectionSelectorComplete() {
            return !mapProjectionBindingId.isEmpty()
                    && !mapProjectionInputPort.isEmpty()
                    && !mapProjectionInputCell.isEmpty()
                    && !mapProjectionOutputPort.isEmpty()
                    && !mapProjectionOutputCell.isEmpty()
                    && "MAP_VALUES_VIEW".equals(mapProjectionOperation)
                    && mapProjectionOutputIndex >= 0
                    && mapProjectionElementOccurrence > 0
                    && "MAP_OUTPUT_ARRAY_INDEX".equals(
                    mapProjectionSelectorKind)
                    && MapProjectionFieldBinding.AUTHORITY.equals(
                    mapProjectionSelectorAuthority)
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                    mapProjectionObjectTokenAuthority)
                    && !mapProjectionObjectTokenScope.isEmpty()
                    && "NONE".equals(
                    mapProjectionCrossExecutionOrdinalAuthority)
                    && !mapProjectionDeclaredFieldOwnerClass.isEmpty()
                    && !mapProjectionDeclaredFieldType.isEmpty()
                    && !mapProjectionDeclaredFieldSignature.isEmpty()
                    && mapProjectionMapObjectToken > 0L
                    && mapProjectionElementObjectToken > 0L
                    && mapProjectionOutputArrayObjectToken > 0L
                    && mapProjectionMapObjectToken
                    != mapProjectionElementObjectToken
                    && mapProjectionMapObjectToken
                    != mapProjectionOutputArrayObjectToken
                    && mapProjectionElementObjectToken
                    != mapProjectionOutputArrayObjectToken
                    && !mapProjectionOutputVerificationAuthority.isEmpty()
                    && mapProjectionExpectedMapKey != null
                    && !stableMapProjectionKeySelector(
                    mapProjectionExpectedMapKey).isEmpty()
                    && "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_"
                    .concat("SNAPSHOT").equals(
                    mapProjectionExpectedMapKeyAuthority)
                    && "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                    .concat("POSITIONAL_REFERENCE_EQUALITY").equals(
                    mapProjectionSourceOutputIndexAuthority)
                    && "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_"
                    .concat("AND_EXACT_OUTPUT_IDENTITY").equals(
                    mapProjectionReplaySelectionAuthority)
                    && !mapProjectionSourceObjectTokenScope.isEmpty()
                    && "SOURCE_CASE_SELECTOR_VALIDATED_THEN_REPLAY_"
                    .concat("ACTIVATION_SCOPE_REBOUND_TOKENS_NOT_"
                            + "COMPARED_ACROSS_EXECUTIONS").equals(
                    mapProjectionReplayScopeRebindingAuthority)
                    && mapProjectionOutputIdentityVerified
                    && mapProjectionSelectorCompleteFlag;
        }

        private boolean matchesDynamic(SymbolizeAction action,
                                       DynamicFieldBinding binding) {
            return matchesDynamicExceptExpectedKey(action, binding)
                    && expectedKeyMatches(binding);
        }

        private boolean matchesDynamicExceptExpectedKey(
                SymbolizeAction action, DynamicFieldBinding binding) {
            return matchesDynamicIdentity(action, binding)
                    && containerSelectorMatches(binding)
                    && (entryReadObservationId.isEmpty()
                    || entryReadObservationId.equals(
                    binding.entryReadObservationId));
        }

        private boolean matchesDynamicIdentity(
                SymbolizeAction action, DynamicFieldBinding binding) {
            if (binding == null || !dynamicSelectorComplete()
                    || !inputSymbol.equals(action.symbol)
                    || !baseInputSymbol.equals(binding.baseInputSymbol)
                    || !dynamicBindingId.equals(binding.dynamicBindingId)
                    || !dynamicFieldSymbol.equals(
                    binding.dynamicFieldSymbol)
                    || !materializationSiteId.equals(
                    binding.materializationSiteId)
                    || materializationOccurrence
                    != binding.materializationOccurrence
                    || !fieldPathMatches(action.fieldPath)
                    || !engineSymbolMatches(binding.dynamicFieldSymbol)
                    || usesFreshMapEntryRebinding()
                    && (!freshMapEntryRebindingPlanComplete()
                    || !binding.freshReplaySelectorComplete())) {
                return false;
            }
            return true;
        }

        private boolean containerSelectorMatches(
                DynamicFieldBinding binding) {
            ContainerElementSelector selector = binding.containerSelector;
            if (selector == null) {
                return !hasContainerSelectorMetadata();
            }
            return containerSelectorComplete()
                    && containerBindingId.equals(selector.bindingId)
                    && containerInputPort.equals(selector.containerInputPort)
                    && containerInputCell.equals(selector.containerInputCell)
                    && selectorAuthority.equals(selector.selectorAuthority)
                    && elementIndex == selector.elementIndex
                    && elementOccurrence == selector.elementOccurrence
                    && declaredFieldOwnerClass.equals(
                    selector.declaredFieldOwnerClass)
                    && declaredFieldType.equals(selector.declaredFieldType);
        }

        private boolean hasContainerSelectorMetadata() {
            return !containerBindingId.isEmpty()
                    || !containerInputPort.isEmpty()
                    || !containerInputCell.isEmpty()
                    || !selectorAuthority.isEmpty()
                    || elementIndex >= 0 || elementOccurrence > 0
                    || !declaredFieldOwnerClass.isEmpty()
                    || !declaredFieldType.isEmpty();
        }

        private boolean containerSelectorComplete() {
            return !containerBindingId.isEmpty()
                    && !containerInputPort.isEmpty()
                    && !containerInputCell.isEmpty()
                    && !selectorAuthority.isEmpty()
                    && elementIndex >= 0 && elementOccurrence > 0
                    && !declaredFieldOwnerClass.isEmpty()
                    && !declaredFieldType.isEmpty();
        }

        private boolean dynamicSelectorComplete() {
            return !engineSymbol.isEmpty()
                    && !baseInputSymbol.isEmpty()
                    && !dynamicBindingId.isEmpty()
                    && !dynamicFieldSymbol.isEmpty()
                    && !materializationSiteId.isEmpty()
                    && materializationOccurrence > 0;
        }

        private boolean usesFreshMapEntryRebinding() {
            return FRESH_MAP_ENTRY_REBINDING_AUTHORITY.equals(
                    dynamicReplayRebindingAuthority);
        }

        private boolean freshMapEntryRebindingPlanComplete() {
            return usesFreshMapEntryRebinding()
                    && !sourceEntrySelectorRetained
                    && expectedEntryKey == null
                    && expectedEntryKeyAuthority.isEmpty()
                    && entryReadObservationId.isEmpty()
                    && !hasContainerSelectorMetadata()
                    && !hasMapProjectionSelectorMetadata();
        }

        private boolean fieldPathMatches(List<String> actualPath) {
            return path.isEmpty() || path.equals(actualPath);
        }

        private boolean expectedKeyMatches(DynamicFieldBinding binding) {
            if (usesFreshMapEntryRebinding()) {
                return freshMapEntryRebindingPlanComplete()
                        && binding != null
                        && binding.freshReplaySelectorComplete();
            }
            // Container-element assignments are selected by the exact
            // container binding plus index/occurrence metadata above.  They
            // intentionally have no map-entry key selector.
            if (binding != null && binding.containerSelector != null) {
                return true;
            }
            if (expectedEntryKey == null) {
                return false;
            }
            if (expectedEntryKeyAuthority.isEmpty()
                    || binding.keyExpression == null) {
                return false;
            }
            if (expectedEntryKeyAuthority.equals(
                    binding.keyExpressionAuthority)
                    && expectedEntryKey.equals(binding.keyExpression)) {
                return true;
            }
            String expected = stableImmutableKeySelector(expectedEntryKey,
                    expectedEntryKeyAuthority);
            String observed = stableImmutableKeySelector(
                    binding.keyExpression, binding.keyExpressionAuthority);
            return !expected.isEmpty() && expected.equals(observed);
        }

        private boolean engineSymbolMatches(String dynamicSymbol) {
            return dynamicEngineSymbolMatchesForTests(engineSymbol,
                    dynamicSymbol);
        }

        private boolean isClearOperation() {
            return "MAP_CLEAR".equals(modelOperation)
                    || "COLLECTION_CLEAR".equals(modelOperation);
        }

        private boolean isDetachArrayElementsOperation() {
            return "ARRAY_SHALLOW_COPY_ELEMENTS".equals(modelOperation);
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

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("engineSymbol", engineSymbol);
            result.addProperty("inputSymbol", inputSymbol);
            if (!baseInputSymbol.isEmpty()) {
                result.addProperty("baseInputSymbol", baseInputSymbol);
            }
            result.addProperty("valueType", valueType);
            result.addProperty("value", value);
            result.addProperty("authority", authority);
            if (!modelOperation.isEmpty()) {
                result.addProperty("modelOperation", modelOperation);
            }
            if (!dynamicBindingId.isEmpty()) {
                result.addProperty("dynamicBindingId", dynamicBindingId);
            }
            if (!dynamicFieldSymbol.isEmpty()) {
                result.addProperty("dynamicFieldSymbol",
                        dynamicFieldSymbol);
            }
            if (!materializationSiteId.isEmpty()) {
                result.addProperty("materializationSiteId",
                        materializationSiteId);
            }
            if (materializationOccurrence > 0) {
                result.addProperty("materializationOccurrence",
                        materializationOccurrence);
            }
            if (!entryReadObservationId.isEmpty()) {
                result.addProperty("entryReadObservationId",
                        entryReadObservationId);
            }
            if (hasContainerSelectorMetadata()) {
                JsonObject selector = new JsonObject();
                selector.addProperty("kind", "ARRAY_INDEX");
                selector.addProperty("bindingId", containerBindingId);
                selector.addProperty("containerInputPort",
                        containerInputPort);
                selector.addProperty("containerInputCell",
                        containerInputCell);
                selector.addProperty("selectorAuthority",
                        selectorAuthority);
                selector.addProperty("elementIndex", elementIndex);
                selector.addProperty("elementOccurrence",
                        elementOccurrence);
                selector.addProperty("declaredFieldOwnerClass",
                        declaredFieldOwnerClass);
                selector.addProperty("declaredFieldType",
                        declaredFieldType);
                result.add("containerSelector", selector);
            }
            if (hasMapProjectionSelectorMetadata()) {
                JsonObject selector = new JsonObject();
                selector.addProperty("kind", "MAP_OUTPUT_ARRAY_INDEX");
                selector.addProperty("bindingId",
                        mapProjectionBindingId);
                selector.addProperty("mapInputPort",
                        mapProjectionInputPort);
                selector.addProperty("mapInputCell",
                        mapProjectionInputCell);
                selector.addProperty("outputPort",
                        mapProjectionOutputPort);
                selector.addProperty("outputCell",
                        mapProjectionOutputCell);
                selector.addProperty("mapProjectionOperation",
                        mapProjectionOperation);
                selector.addProperty("outputIndex",
                        mapProjectionOutputIndex);
                selector.addProperty("elementOccurrence",
                        mapProjectionElementOccurrence);
                selector.addProperty("authority",
                        mapProjectionSelectorAuthority);
                selector.addProperty("objectTokenAuthority",
                        mapProjectionObjectTokenAuthority);
                selector.addProperty("objectTokenScope",
                        mapProjectionObjectTokenScope);
                selector.addProperty("crossExecutionOrdinalAuthority",
                        mapProjectionCrossExecutionOrdinalAuthority);
                selector.addProperty("declaredFieldOwnerClass",
                        mapProjectionDeclaredFieldOwnerClass);
                selector.addProperty("declaredFieldType",
                        mapProjectionDeclaredFieldType);
                selector.addProperty("declaredFieldSignature",
                        mapProjectionDeclaredFieldSignature);
                selector.addProperty("mapObjectToken",
                        mapProjectionMapObjectToken);
                selector.addProperty("elementObjectToken",
                        mapProjectionElementObjectToken);
                selector.addProperty("outputArrayObjectToken",
                        mapProjectionOutputArrayObjectToken);
                selector.addProperty("outputIdentityVerified",
                        mapProjectionOutputIdentityVerified);
                selector.addProperty("outputVerificationAuthority",
                        mapProjectionOutputVerificationAuthority);
                if (mapProjectionExpectedMapKey != null) {
                    selector.add("expectedMapKey",
                            copyJsonTree(mapProjectionExpectedMapKey));
                }
                selector.addProperty("expectedMapKeyAuthority",
                        mapProjectionExpectedMapKeyAuthority);
                selector.addProperty("sourceOutputIndexAuthority",
                        mapProjectionSourceOutputIndexAuthority);
                selector.addProperty("replaySelectionAuthority",
                        mapProjectionReplaySelectionAuthority);
                selector.addProperty("sourceObjectTokenScope",
                        mapProjectionSourceObjectTokenScope);
                selector.addProperty("replayScopeRebindingAuthority",
                        mapProjectionReplayScopeRebindingAuthority);
                selector.addProperty("complete",
                        mapProjectionSelectorCompleteFlag);
                result.add("mapProjectionSelector", selector);
            }
            if (expectedEntryKey != null) {
                result.add("expectedEntryKey",
                        copyJsonTree(expectedEntryKey));
            }
            if (!expectedEntryKeyAuthority.isEmpty()) {
                result.addProperty("expectedEntryKeyAuthority",
                        expectedEntryKeyAuthority);
            }
            if (!dynamicReplayRebindingAuthority.isEmpty()) {
                result.addProperty("dynamicReplayRebindingAuthority",
                        dynamicReplayRebindingAuthority);
                result.addProperty("sourceEntrySelectorRetained",
                        sourceEntrySelectorRetained);
            }
            if (legacyUniqueFieldTarget) {
                result.addProperty("legacyUniqueFieldTarget", true);
            }
            result.addProperty("materializeAtRealDefinition", true);
            return result;
        }
    }

    static boolean modelAssignmentTargetsFieldForTests(JsonObject action,
                                                        JsonObject assignment) {
        return new ModelAssignment(assignment).targetsFieldAccess(
                new SymbolizeAction(action));
    }

    static boolean writeModeledFieldForTests(Object owner, String field,
                                              JsonObject assignment) {
        return writeModeledField(owner, field,
                new ModelAssignment(assignment));
    }

    static boolean writeModeledExactFieldForTests(
            Object owner, String fieldSignature, JsonObject assignment) {
        return writeModeledExactField(owner, fieldSignature,
                new ModelAssignment(assignment));
    }

    /** One theory-neutral, occurrence-specific value materialization. */
    private static final class ReplayMaterialization {
        private final String kind;
        private final String method;
        private final int unitIndex;
        private final int occurrence;
        private final String siteId;
        private final String desiredResult;
        private final String operationSemantics;
        private final String resultSymbol;
        private final boolean solverDerived;
        private final String mode;
        private final String authority;
        private final String occurrencePolicy;

        private ReplayMaterialization(JsonObject json) {
            this.kind = string(json, "kind");
            this.method = string(json, "method");
            this.unitIndex = integer(json, "unitIndex", -1);
            this.occurrence = Math.max(1, integer(json, "occurrence", 1));
            this.siteId = firstNonBlank(string(json, "siteId"),
                    this.method + "#u" + this.unitIndex);
            this.desiredResult = string(json, "desiredResult");
            this.operationSemantics = firstNonBlank(
                    string(json, "operationSemantics"),
                    string(json, "producerSemantics"));
            this.resultSymbol = string(json, "resultSymbol");
            this.solverDerived = bool(json, "solverDerived", false);
            this.mode = string(json, "mode");
            this.authority = string(json, "authority");
            this.occurrencePolicy = string(json, "occurrencePolicy");
        }

        private boolean matches(String actualMethod, int actualUnit,
                                int actualOccurrence) {
            return method.equals(safe(actualMethod))
                    && unitIndex == actualUnit
                    && occurrence == actualOccurrence;
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("kind", kind);
            result.addProperty("method", method);
            result.addProperty("unitIndex", unitIndex);
            result.addProperty("siteId", siteId);
            result.addProperty("occurrence", occurrence);
            result.addProperty("desiredResult", desiredResult);
            result.addProperty("operationSemantics", operationSemantics);
            result.addProperty("resultSymbol", resultSymbol);
            result.addProperty("solverDerived", solverDerived);
            result.addProperty("mode", mode);
            result.addProperty("authority", authority);
            result.addProperty("occurrencePolicy", occurrencePolicy);
            return result;
        }
    }

    private static final class ForcedBranch {
        private final String siteId;
        private final int occurrence;
        private final boolean desiredOutcome;

        private ForcedBranch(JsonObject json) {
            this.siteId = string(json, "siteId");
            this.occurrence = Math.max(1, integer(json, "occurrence", 1));
            this.desiredOutcome = bool(json, "desiredOutcome", false);
        }
    }

    private static final class ScheduledTarget {
        private final String siteId;
        private final int occurrence;
        private final boolean desiredOutcome;

        private ScheduledTarget(JsonObject json) {
            this.siteId = string(json, "siteId");
            this.occurrence = Math.max(1, integer(json, "occurrence", 1));
            this.desiredOutcome = bool(json, "desiredOutcome", false);
        }

        private boolean matches(String actualSiteId, int actualOccurrence) {
            return siteId.equals(actualSiteId)
                    && occurrence == actualOccurrence;
        }
    }

    private static final class OutputCaptureRequest {
        private static final String CALL_ARGUMENT = "CALL_ARGUMENT";
        private static final String METHOD_RETURN_VALUE =
                "METHOD_RETURN_VALUE";
        private static final String FIELD_ASSIGNMENT_RHS =
                "FIELD_ASSIGNMENT_RHS";

        private final String captureKind;
        private final String captureBindingId;
        private final String outputPort;
        private final String outputCell;
        private final String method;
        private final String callerMethod;
        private final int unitIndex;
        private final String siteId;
        private final String calleeMethod;
        private final int argumentIndex;
        private final String fieldSignature;
        private final int occurrence;
        private final String occurrenceAuthority;

        private OutputCaptureRequest(JsonObject json) {
            this.captureKind = firstNonBlank(
                    string(json, "captureKind"), CALL_ARGUMENT);
            this.captureBindingId = string(json, "captureBindingId");
            this.outputPort = string(json, "outputPort");
            this.outputCell = string(json, "outputCell");
            this.callerMethod = string(json, "callerMethod");
            this.method = firstNonBlank(string(json, "method"),
                    this.callerMethod);
            this.unitIndex = integer(json, "unitIndex", -1);
            this.siteId = string(json, "siteId");
            this.calleeMethod = string(json, "calleeMethod");
            this.argumentIndex = integer(json, "argumentIndex", -1);
            this.fieldSignature = firstNonBlank(
                    string(json, "fieldSignature"), string(json, "field"));
            this.occurrence = integer(json, "occurrence", 0);
            this.occurrenceAuthority = string(json,
                    "occurrenceAuthority");
        }

        private boolean valid() {
            if (captureBindingId.isEmpty() || outputPort.isEmpty()
                    || outputCell.isEmpty() || unitIndex < 0
                    || siteId.isEmpty() || occurrence <= 0) {
                return false;
            }
            if (FIELD_ASSIGNMENT_RHS.equals(captureKind)) {
                return !method.isEmpty() && !fieldSignature.isEmpty()
                        && declaredField(fieldSignature) != null;
            }
            if (METHOD_RETURN_VALUE.equals(captureKind)) {
                return !method.isEmpty();
            }
            return CALL_ARGUMENT.equals(captureKind)
                    && !callerMethod.isEmpty() && !calleeMethod.isEmpty()
                    && argumentIndex >= 0;
        }

        private boolean matchesCallArgument(
                String actualCaller, int actualUnit, String actualSite,
                String actualCallee, int actualArgument, String actualPort,
                String actualCell, String actualBinding,
                int actualRequestedOccurrence) {
            return CALL_ARGUMENT.equals(captureKind)
                    && callerMethod.equals(safe(actualCaller))
                    && unitIndex == actualUnit
                    && siteId.equals(safe(actualSite))
                    && calleeMethod.equals(safe(actualCallee))
                    && argumentIndex == actualArgument
                    && outputPort.equals(safe(actualPort))
                    && outputCell.equals(safe(actualCell))
                    && captureBindingId.equals(safe(actualBinding))
                    && occurrence == actualRequestedOccurrence;
        }

        private boolean matchesMethodReturn(
                String actualMethod, int actualUnit, String actualSite,
                String actualPort, String actualCell, String actualBinding,
                int actualRequestedOccurrence) {
            return METHOD_RETURN_VALUE.equals(captureKind)
                    && method.equals(safe(actualMethod))
                    && unitIndex == actualUnit
                    && siteId.equals(safe(actualSite))
                    && outputPort.equals(safe(actualPort))
                    && outputCell.equals(safe(actualCell))
                    && captureBindingId.equals(safe(actualBinding))
                    && occurrence == actualRequestedOccurrence;
        }

        private boolean matchesFieldAssignment(
                String actualMethod, int actualUnit, String actualSite,
                String actualFieldSignature, String actualPort,
                String actualCell, String actualBinding,
                int actualRequestedOccurrence) {
            return FIELD_ASSIGNMENT_RHS.equals(captureKind)
                    && method.equals(safe(actualMethod))
                    && unitIndex == actualUnit
                    && siteId.equals(safe(actualSite))
                    && fieldSignature.equals(safe(actualFieldSignature))
                    && outputPort.equals(safe(actualPort))
                    && outputCell.equals(safe(actualCell))
                    && captureBindingId.equals(safe(actualBinding))
                    && occurrence == actualRequestedOccurrence;
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("captureKind", captureKind);
            result.addProperty("captureBindingId", captureBindingId);
            result.addProperty("outputPort", outputPort);
            result.addProperty("outputCell", outputCell);
            result.addProperty("unitIndex", unitIndex);
            result.addProperty("siteId", siteId);
            if (FIELD_ASSIGNMENT_RHS.equals(captureKind)) {
                result.addProperty("method", method);
                result.addProperty("fieldSignature", fieldSignature);
            } else if (METHOD_RETURN_VALUE.equals(captureKind)) {
                result.addProperty("method", method);
            } else {
                result.addProperty("callerMethod", callerMethod);
                result.addProperty("calleeMethod", calleeMethod);
                result.addProperty("argumentIndex", argumentIndex);
            }
            result.addProperty("requestedOccurrence", occurrence);
            if (!occurrenceAuthority.isEmpty()) {
                result.addProperty("occurrenceAuthority",
                        occurrenceAuthority);
            }
            return result;
        }
    }

    /** Stable plan selector that deliberately excludes JVM-assigned tid. */
    private static final class RootContextSelector {
        private final boolean present;
        private final boolean valid;
        private final String error;
        private final String receiverRuntimeClass;
        private final String threadName;
        private final int invocationOrdinalWithinContext;

        private RootContextSelector(boolean present, boolean valid,
                                    String error,
                                    String receiverRuntimeClass,
                                    String threadName,
                                    int invocationOrdinalWithinContext) {
            this.present = present;
            this.valid = valid;
            this.error = safe(error);
            this.receiverRuntimeClass = safe(receiverRuntimeClass);
            this.threadName = safe(threadName);
            this.invocationOrdinalWithinContext =
                    invocationOrdinalWithinContext;
        }

        private static RootContextSelector from(JsonObject activation) {
            boolean present = activation.has("receiverRuntimeClass")
                    || activation.has("invocationOrdinalWithinContext")
                    || activation.has("rootContextSelectionAuthority")
                    || activation.has("threadIdSelectionUsed");
            if (!present) {
                return new RootContextSelector(false, true, "", "", "",
                        -1);
            }
            String receiverClass = strictString(activation,
                    "receiverRuntimeClass");
            String thread = activation.has("threadName")
                    ? strictString(activation, "threadName") : "";
            Integer ordinal = strictInteger(activation,
                    "invocationOrdinalWithinContext", 1);
            String authority = strictString(activation,
                    "rootContextSelectionAuthority");
            JsonElement rawThreadIdUsed = activation.get(
                    "threadIdSelectionUsed");
            boolean explicitNoThreadId = rawThreadIdUsed != null
                    && rawThreadIdUsed.isJsonPrimitive()
                    && rawThreadIdUsed.getAsJsonPrimitive().isBoolean()
                    && !rawThreadIdUsed.getAsBoolean();
            if (receiverClass.isEmpty()
                    || !receiverClass.equals(receiverClass.trim())
                    || activation.has("threadName") && (thread.isEmpty()
                    || !thread.equals(thread.trim()))
                    || ordinal == null
                    || !ROOT_CONTEXT_SELECTION_AUTHORITY.equals(authority)
                    || !explicitNoThreadId || activation.has("threadId")) {
                return new RootContextSelector(true, false,
                        "stable root context requires an exact receiver "
                                + "runtime class, optional non-blank thread "
                                + "name, positive context ordinal, canonical "
                                + "authority, and no thread id",
                        receiverClass, thread,
                        ordinal == null ? -1 : ordinal);
            }
            String legacyReceiver = string(activation, "receiverType");
            if (!legacyReceiver.isEmpty()
                    && !receiverClass.equals(legacyReceiver)) {
                return new RootContextSelector(true, false,
                        "receiverRuntimeClass disagrees with receiverType",
                        receiverClass, thread, ordinal);
            }
            return new RootContextSelector(true, true, "", receiverClass,
                    thread, ordinal);
        }

        private boolean matches(Object receiver, String actualThreadName) {
            if (!present || !valid || receiver == null
                    || !receiverRuntimeClass.equals(
                    receiver.getClass().getName())) {
                return false;
            }
            return threadName.isEmpty()
                    || threadName.equals(safe(actualThreadName));
        }

        private String identity() {
            if (!present) return "LEGACY_NO_STABLE_ROOT_CONTEXT";
            return ROOT_CONTEXT_SELECTION_AUTHORITY + '|'
                    + receiverRuntimeClass.length() + ':'
                    + receiverRuntimeClass + '|'
                    + threadName.length() + ':' + threadName;
        }

        private boolean selects(Integer occurrence) {
            return occurrence != null
                    && invocationOrdinalWithinContext == occurrence;
        }

        private String selectionIdentity() {
            return present ? "contextOrdinal="
                    + invocationOrdinalWithinContext : "legacyContext";
        }
    }

    private static final class RootArgumentSelector {
        private final boolean present;
        private final boolean valid;
        private final String error;
        private final boolean receiverScoped;
        private final int matchOrdinal;
        private final int receiverOrdinal;
        private final int matchOrdinalWithinReceiver;
        private final List<RootArgumentTypePredicate> predicates;

        private RootArgumentSelector(boolean present, boolean valid,
                                     String error, boolean receiverScoped,
                                     int matchOrdinal, int receiverOrdinal,
                                     int matchOrdinalWithinReceiver,
                                     List<RootArgumentTypePredicate> predicates) {
            this.present = present;
            this.valid = valid;
            this.error = safe(error);
            this.receiverScoped = receiverScoped;
            this.matchOrdinal = matchOrdinal;
            this.receiverOrdinal = receiverOrdinal;
            this.matchOrdinalWithinReceiver = matchOrdinalWithinReceiver;
            this.predicates = predicates;
        }

        private static RootArgumentSelector from(JsonObject activation) {
            if (!activation.has("runtimeRootArgumentSelector")) {
                return new RootArgumentSelector(false, true, "", false,
                        -1, -1, -1, Collections.emptyList());
            }
            JsonElement raw = activation.get("runtimeRootArgumentSelector");
            if (raw == null || !raw.isJsonObject()) {
                return invalid("runtimeRootArgumentSelector must be an object");
            }
            JsonObject json = raw.getAsJsonObject();
            String schema = strictString(json, "schema");
            String authority = strictString(json, "authority");
            boolean v1 = ROOT_ARGUMENT_SELECTOR_SCHEMA_V1.equals(schema)
                    && ROOT_ARGUMENT_SELECTOR_AUTHORITY_V1.equals(authority);
            boolean v2 = ROOT_ARGUMENT_SELECTOR_SCHEMA_V2.equals(schema)
                    && ROOT_ARGUMENT_SELECTOR_AUTHORITY_V2.equals(authority);
            if (!v1 && !v2) {
                return invalid("unsupported selector schema/authority pair");
            }
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
                        strictString(predicate, "kind"))) {
                    return invalid("predicate kind must be exact runtime type");
                }
                Integer index = strictInteger(predicate, "argumentIndex", 0);
                String runtimeType = strictString(predicate, "runtimeType");
                if (index == null || runtimeType.isEmpty()
                        || !runtimeType.equals(runtimeType.trim())
                        || !indices.add(index)) {
                    return invalid("predicate index/type is malformed or duplicate");
                }
                predicates.add(new RootArgumentTypePredicate(index,
                        runtimeType));
            }
            predicates.sort((left, right) -> Integer.compare(
                    left.argumentIndex, right.argumentIndex));
            if (v1) {
                Integer matchOrdinal = strictInteger(json,
                        "matchOrdinal", 1);
                if (matchOrdinal == null
                        || json.has("receiverOrdinal")
                        || json.has("matchOrdinalWithinReceiver")) {
                    return invalid("V1 selector requires only a positive "
                            + "matchOrdinal");
                }
                return new RootArgumentSelector(true, true, "", false,
                        matchOrdinal, -1, -1,
                        Collections.unmodifiableList(predicates));
            }
            Integer receiverOrdinal = strictInteger(json,
                    "receiverOrdinal", 1);
            Integer withinReceiver = strictInteger(json,
                    "matchOrdinalWithinReceiver", 1);
            if (receiverOrdinal == null || withinReceiver == null
                    || json.has("matchOrdinal")) {
                return invalid("V2 selector requires positive receiverOrdinal "
                        + "and matchOrdinalWithinReceiver");
            }
            return new RootArgumentSelector(true, true, "", true,
                    -1, receiverOrdinal, withinReceiver,
                    Collections.unmodifiableList(predicates));
        }

        private static RootArgumentSelector invalid(String error) {
            return new RootArgumentSelector(true, false, error, false,
                    -1, -1, -1, Collections.emptyList());
        }

        private boolean matches(Object[] rootArguments) {
            if (!present || !valid || rootArguments == null) return false;
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
            if (!present) return "LEGACY_GLOBAL_INVOCATION_ORDINAL";
            StringBuilder result = new StringBuilder(
                    receiverScoped ? ROOT_ARGUMENT_SELECTOR_SCHEMA_V2
                            : ROOT_ARGUMENT_SELECTOR_SCHEMA_V1).append('|')
                    .append(receiverScoped
                            ? ROOT_ARGUMENT_SELECTOR_AUTHORITY_V2
                            : ROOT_ARGUMENT_SELECTOR_AUTHORITY_V1);
            for (RootArgumentTypePredicate predicate : predicates) {
                result.append('|').append(predicate.argumentIndex)
                        .append('=').append(predicate.runtimeType.length())
                        .append(':').append(predicate.runtimeType);
            }
            return result.toString();
        }

        private boolean selects(SelectorOccurrence occurrence) {
            if (occurrence == null) return false;
            return receiverScoped
                    ? receiverOrdinal == occurrence.receiverOrdinal
                    && matchOrdinalWithinReceiver
                    == occurrence.matchOrdinalWithinReceiver
                    : matchOrdinal == occurrence.matchOrdinal;
        }

        private String selectionIdentity() {
            return receiverScoped
                    ? "receiver=" + receiverOrdinal + ",within="
                    + matchOrdinalWithinReceiver
                    : "globalMatch=" + matchOrdinal;
        }
    }

    private static final class SelectorOccurrence {
        private final int matchOrdinal;
        private final int receiverOrdinal;
        private final int matchOrdinalWithinReceiver;

        private SelectorOccurrence(int matchOrdinal, int receiverOrdinal,
                                   int matchOrdinalWithinReceiver) {
            this.matchOrdinal = matchOrdinal;
            this.receiverOrdinal = receiverOrdinal;
            this.matchOrdinalWithinReceiver = matchOrdinalWithinReceiver;
        }

        private static SelectorOccurrence global(int ordinal) {
            return new SelectorOccurrence(ordinal, -1, -1);
        }

        private static SelectorOccurrence receiver(int receiverOrdinal,
                                                   int withinReceiver) {
            return new SelectorOccurrence(-1, receiverOrdinal,
                    withinReceiver);
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

    private static final class Activation {
        private final String activationId;
        private final String regionId;
        private final String test;
        private final String rootMethod;
        private final String observedRootMethod;
        private final int invocationOrdinal;
        private final RootContextSelector rootContextSelector;
        private final RootArgumentSelector rootArgumentSelector;
        private final boolean replayable;
        private final boolean requiresAllSelection;
        private final boolean concreteReplayOnly;
        private final boolean observationOnlyReplay;
        private final List<SymbolizeAction> symbolize;
        private final Map<String, String> branchPolicies;
        private final List<ForcedBranch> forcedBranches;
        private final List<ReplayMaterialization> replayMaterializations;
        private final List<ModelAssignment> modelAssignments;
        private final List<ContainerElementFieldBindingSpec>
                containerElementFieldBindings;
        private final List<MapValueElementProjectionSpec>
                mapValueElementFieldProjections;
        private final List<OutputCaptureRequest> outputCaptures;
        private final ScheduledTarget targetBranch;

        private Activation(JsonObject json) {
            this.activationId = string(json, "activationId");
            this.regionId = string(json, "regionId");
            this.test = string(json, "test");
            this.rootMethod = string(json, "rootMethod");
            this.observedRootMethod = string(json, "observedRootMethod");
            this.invocationOrdinal = integer(json, "invocationOrdinal", 1);
            this.rootContextSelector = RootContextSelector.from(json);
            this.rootArgumentSelector = RootArgumentSelector.from(json);
            this.replayable = bool(json, "replayable", true);
            this.requiresAllSelection = "ALL".equals(string(json,
                    "activationSelectionRequired"));
            this.concreteReplayOnly = bool(json, "concreteReplayOnly", false);
            this.observationOnlyReplay = bool(json,
                    "observationOnlyReplay", false);
            this.symbolize = new ArrayList<>();
            this.branchPolicies = new LinkedHashMap<>();
            this.forcedBranches = new ArrayList<>();
            this.replayMaterializations = new ArrayList<>();
            this.modelAssignments = new ArrayList<>();
            this.containerElementFieldBindings = new ArrayList<>();
            this.mapValueElementFieldProjections = new ArrayList<>();
            this.outputCaptures = new ArrayList<>();
            JsonElement target = json.get("targetBranch");
            this.targetBranch = target != null && target.isJsonObject()
                    ? new ScheduledTarget(target.getAsJsonObject()) : null;
            JsonArray materializations = array(json, "materializations");
            JsonArray actions = materializations.size() > 0
                    ? materializations : array(json, "symbolize");
            for (JsonElement element : actions) {
                if (element.isJsonObject()) {
                    this.symbolize.add(new SymbolizeAction(element.getAsJsonObject()));
                }
            }
            JsonArray branches = array(json, "branches");
            for (JsonElement element : branches) {
                if (element.isJsonObject()) {
                    JsonObject branch = element.getAsJsonObject();
                    branchPolicies.put(string(branch, "siteId"),
                            string(branch, "policy"));
                }
            }
            for (JsonElement element : array(json, "forcedBranches")) {
                if (element.isJsonObject()) {
                    ForcedBranch forced = new ForcedBranch(
                            element.getAsJsonObject());
                    if (!forced.siteId.isEmpty()) {
                        forcedBranches.add(forced);
                    }
                }
            }
            for (JsonElement element : array(json,
                    "replayMaterializations")) {
                if (element.isJsonObject()) {
                    ReplayMaterialization replay = new ReplayMaterialization(
                            element.getAsJsonObject());
                    if (!replay.method.isEmpty() && replay.unitIndex >= 0) {
                        replayMaterializations.add(replay);
                    }
                }
            }
            for (JsonElement element : array(json, "modelAssignments")) {
                if (element.isJsonObject()) {
                    ModelAssignment assignment = new ModelAssignment(
                            element.getAsJsonObject());
                    if (!assignment.inputSymbol.isEmpty()
                            && !assignment.valueType.isEmpty()) {
                        modelAssignments.add(assignment);
                    }
                }
            }
            // Keep every declared union member, including malformed ones.  A
            // malformed declaration must make the matching base port fail
            // closed; silently dropping it would re-enable the legacy static
            // symbol and collapse distinct concrete owners.
            for (JsonElement element : array(json,
                    "containerElementFieldBindings")) {
                if (element.isJsonObject()) {
                    containerElementFieldBindings.add(
                            new ContainerElementFieldBindingSpec(
                                    element.getAsJsonObject()));
                }
            }
            // Preserve malformed members so the matching map input fails
            // closed instead of silently reverting to shallow map-reference
            // symbolization.
            for (JsonElement element : array(json,
                    "mapValueElementFieldProjections")) {
                if (element.isJsonObject()) {
                    mapValueElementFieldProjections.add(
                            new MapValueElementProjectionSpec(
                                    element.getAsJsonObject()));
                }
            }
            for (JsonElement element : array(json,
                    "requestedOutputCapture")) {
                if (!element.isJsonObject()) continue;
                OutputCaptureRequest request = new OutputCaptureRequest(
                        element.getAsJsonObject());
                if (request.valid()) outputCaptures.add(request);
            }
        }

        private List<ContainerElementFieldBindingSpec>
        containerBindingsForBase(String baseInputSymbol) {
            List<ContainerElementFieldBindingSpec> matches =
                    new ArrayList<>();
            for (ContainerElementFieldBindingSpec binding
                    : containerElementFieldBindings) {
                if (binding.baseInputSymbol.equals(baseInputSymbol)) {
                    matches.add(binding);
                }
            }
            return matches;
        }

        private List<ContainerElementFieldBindingSpec>
        containerBindingsForInput(String containerInputPort) {
            List<ContainerElementFieldBindingSpec> matches =
                    new ArrayList<>();
            for (ContainerElementFieldBindingSpec binding
                    : containerElementFieldBindings) {
                if (binding.containerInputPort.equals(containerInputPort)) {
                    matches.add(binding);
                }
            }
            return matches;
        }

        private List<MapValueElementProjectionSpec>
        mapProjectionsForInput(String mapInputPort) {
            List<MapValueElementProjectionSpec> matches = new ArrayList<>();
            for (MapValueElementProjectionSpec projection
                    : mapValueElementFieldProjections) {
                if (projection.mapInputPort.equals(mapInputPort)) {
                    matches.add(projection);
                }
            }
            return matches;
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

        private String concreteReplayError() {
            if (!concreteReplayOnly) return "";
            if (!forcedBranches.isEmpty()) {
                return "concrete replay forbids branch overrides";
            }
            if (!replayMaterializations.isEmpty()) {
                return "concrete replay forbids reference-result injection";
            }
            if (observationOnlyReplay && !modelAssignments.isEmpty()) {
                return "observation-only concrete replay forbids downstream "
                        + "model assignments";
            }
            return "";
        }

        private String policy(String siteId) {
            String policy = branchPolicies.get(siteId);
            return firstNonBlank(policy, "PATH_ASSUMPTION");
        }

        private ForcedBranch force(String siteId, int occurrence) {
            for (ForcedBranch forced : forcedBranches) {
                if (forced.siteId.equals(siteId)
                        && forced.occurrence == occurrence) {
                    return forced;
                }
            }
            return null;
        }

        private ReplayMaterialization replay(String method, int unitIndex,
                                             int occurrence) {
            for (ReplayMaterialization replay : replayMaterializations) {
                if (replay.matches(method, unitIndex, occurrence)) {
                    return replay;
                }
            }
            return null;
        }

        private ScheduledTarget target(String siteId, int occurrence) {
            return targetBranch != null
                    && targetBranch.matches(siteId, occurrence)
                    ? targetBranch : null;
        }

        private OutputCaptureRequest callArgumentCapture(
                String callerMethod, int unitIndex, String siteId,
                String calleeMethod, int argumentIndex, String outputPort,
                String outputCell, String captureBindingId,
                int requestedOccurrence) {
            OutputCaptureRequest match = null;
            for (OutputCaptureRequest request : outputCaptures) {
                if (!request.matchesCallArgument(callerMethod, unitIndex,
                        siteId, calleeMethod, argumentIndex, outputPort,
                        outputCell, captureBindingId,
                        requestedOccurrence)) {
                    continue;
                }
                if (match != null) return null;
                match = request;
            }
            return match;
        }

        private OutputCaptureRequest fieldAssignmentCapture(
                String method, int unitIndex, String siteId,
                String fieldSignature, String outputPort, String outputCell,
                String captureBindingId, int requestedOccurrence) {
            OutputCaptureRequest match = null;
            for (OutputCaptureRequest request : outputCaptures) {
                if (!request.matchesFieldAssignment(method, unitIndex,
                        siteId, fieldSignature, outputPort, outputCell,
                        captureBindingId, requestedOccurrence)) {
                    continue;
                }
                if (match != null) return null;
                match = request;
            }
            return match;
        }

        private OutputCaptureRequest methodReturnCapture(
                String method, int unitIndex, String siteId,
                String outputPort, String outputCell,
                String captureBindingId, int requestedOccurrence) {
            OutputCaptureRequest match = null;
            for (OutputCaptureRequest request : outputCaptures) {
                if (!request.matchesMethodReturn(method, unitIndex, siteId,
                        outputPort, outputCell, captureBindingId,
                        requestedOccurrence)) {
                    continue;
                }
                if (match != null) return null;
                match = request;
            }
            return match;
        }
    }

    private static final class Configuration {
        private final boolean enabled;
        private final String selectedActivation;
        private final Path resultFile;
        private final List<Activation> activations;

        private Configuration(boolean enabled, String selectedActivation,
                              Path resultFile, List<Activation> activations) {
            this.enabled = enabled;
            this.selectedActivation = selectedActivation;
            this.resultFile = resultFile;
            this.activations = activations;
        }

        private Activation select(String rootMethod, String test, int ordinal,
                                  Object receiver, Object[] rootArguments) {
            List<Activation> candidates = new ArrayList<>();
            for (Activation activation : activations) {
                if (!activation.replayable) {
                    continue;
                }
                if (!selectedActivation.isEmpty()
                        && !selectedActivation.equals(activation.activationId)) {
                    continue;
                }
                String expectedRoot = firstNonBlank(activation.rootMethod,
                        activation.observedRootMethod);
                if (!rootMethod.equals(expectedRoot)) {
                    continue;
                }
                if (!activation.test.isEmpty()
                        && !"unknown-test".equals(test)
                        && !activation.test.equals(test)) {
                    continue;
                }
                candidates.add(activation);
            }

            String actualThreadName = Thread.currentThread().getName();
            Map<String, Integer> contextOccurrences =
                    new LinkedHashMap<>();
            for (Activation activation : candidates) {
                RootContextSelector selector =
                        activation.rootContextSelector;
                if (!selector.present
                        || !selector.matches(receiver, actualThreadName)) {
                    continue;
                }
                String identity = selector.identity();
                if (!contextOccurrences.containsKey(identity)) {
                    contextOccurrences.put(identity,
                            nextRootContextOccurrence(test, rootMethod,
                                    selector));
                }
            }

            // Advance every matching predicate family before selecting a
            // plan row.  Returning as soon as one activation matched used to
            // leave later, overlapping selector families one occurrence
            // behind, making plan order affect future root selection.
            Map<String, SelectorOccurrence> occurrences =
                    new LinkedHashMap<>();
            for (Activation activation : candidates) {
                RootContextSelector contextSelector =
                        activation.rootContextSelector;
                if (contextSelector.present
                        && !contextSelector.matches(receiver,
                        actualThreadName)) {
                    continue;
                }
                RootArgumentSelector selector =
                        activation.rootArgumentSelector;
                if (!selector.present || !selector.matches(rootArguments)) {
                    continue;
                }
                String selectorIdentity = contextSelector.identity() + "\n"
                        + selector.identity();
                if (!occurrences.containsKey(selectorIdentity)) {
                    occurrences.put(selectorIdentity,
                            nextSelectorOccurrence(test, rootMethod,
                                    selector, contextSelector, receiver));
                }
            }

            Activation selected = null;
            for (Activation activation : candidates) {
                RootContextSelector contextSelector =
                        activation.rootContextSelector;
                boolean contextMatches = !contextSelector.present
                        || contextSelector.selects(contextOccurrences.get(
                        contextSelector.identity()));
                if (!contextMatches) continue;
                RootArgumentSelector selector =
                        activation.rootArgumentSelector;
                boolean matches = selector.present
                        ? selector.selects(occurrences.get(
                        contextSelector.identity() + "\n"
                                + selector.identity()))
                        : contextSelector.present
                        || activation.invocationOrdinal == ordinal;
                if (!matches) continue;
                if (selected != null) {
                    throw new IllegalStateException("Ambiguous runtime root "
                            + "selection for " + rootMethod
                            + " activations=" + selected.activationId + ","
                            + activation.activationId);
                }
                selected = activation;
            }
            return selected;
        }

        private static Configuration load() {
            String planValue = firstNonBlank(
                    System.getProperty("causynth.concolic.activation.plan"),
                    System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_PLAN"));
            String selected = firstNonBlank(
                    System.getProperty("causynth.concolic.activation.id"),
                    System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_ID"));
            Path result = Paths.get(firstNonBlank(
                    System.getProperty("causynth.concolic.results"),
                    System.getenv("CAUSYNTH_CONCOLIC_RESULTS"),
                    "target/causynth-trace/concolic_region_results.jsonl"));
            if (planValue.isEmpty()) {
                return new Configuration(false, selected, result,
                        Collections.emptyList());
            }
            Path plan = Paths.get(planValue);
            List<Activation> activations = new ArrayList<>();
            if (Files.isRegularFile(plan)) {
                try (BufferedReader reader = Files.newBufferedReader(plan,
                        StandardCharsets.UTF_8)) {
                    String line;
                    while ((line = reader.readLine()) != null) {
                        if (line.trim().isEmpty()) {
                            continue;
                        }
                        JsonElement parsed = new JsonParser().parse(line);
                        if (parsed.isJsonObject()) {
                            Activation activation = new Activation(parsed.getAsJsonObject());
                            if (!activation.activationId.isEmpty()) {
                                activations.add(activation);
                            }
                        }
                    }
                } catch (IOException | RuntimeException exception) {
                    System.err.println("Causynth could not load activation plan: "
                            + exception);
                }
            }
            validateEffectiveActivationKeys(activations, selected, plan);
            return new Configuration(!activations.isEmpty(), selected, result,
                    activations);
        }

        private static void validateEffectiveActivationKeys(
                List<Activation> activations, String selected, Path plan) {
            Set<String> activationIds = new LinkedHashSet<>();
            Map<String, String> runtimeKeys = new LinkedHashMap<>();
            for (Activation activation : activations) {
                if (!selected.isEmpty()
                        && selected.equals(activation.activationId)
                        && activation.requiresAllSelection) {
                    throw new IllegalStateException("Selected activation "
                            + selected + " belongs to a reachability bundle "
                            + "that requires ALL plan rows in " + plan);
                }
                if (!activation.replayable
                        || (!selected.isEmpty() && !selected.equals(
                        activation.activationId))) {
                    continue;
                }
                if (!activation.rootArgumentSelector.valid) {
                    throw new IllegalStateException("Malformed runtime root "
                            + "argument selector for activation "
                            + activation.activationId + ": "
                            + activation.rootArgumentSelector.error
                            + " in " + plan);
                }
                if (!activation.rootContextSelector.valid) {
                    throw new IllegalStateException("Malformed stable runtime "
                            + "root context for activation "
                            + activation.activationId + ": "
                            + activation.rootContextSelector.error
                            + " in " + plan);
                }
                if (!activationIds.add(activation.activationId)) {
                    throw new IllegalStateException("Duplicate effective "
                            + "activationId " + activation.activationId
                            + " in " + plan);
                }
                String root = firstNonBlank(activation.rootMethod,
                        activation.observedRootMethod);
                RootContextSelector contextSelector =
                        activation.rootContextSelector;
                RootArgumentSelector selector =
                        activation.rootArgumentSelector;
                String selectorIdentity = selector.identity();
                String selectionIdentity = selector.present
                        ? selector.selectionIdentity()
                        : contextSelector.present
                        ? contextSelector.selectionIdentity()
                        : "globalInvocation=" + activation.invocationOrdinal;
                String key = root + "\n" + contextSelector.identity()
                        + "\n" + contextSelector.selectionIdentity() + "\n"
                        + selectorIdentity + "\n" + selectionIdentity;
                String previous = runtimeKeys.put(key,
                        activation.activationId);
                if (previous != null) {
                    throw new IllegalStateException("Ambiguous effective "
                            + "activation runtime key root=" + root
                            + " context=" + contextSelector.identity()
                            + " selector=" + selectorIdentity
                            + " selection=" + selectionIdentity
                            + " activations=" + previous + ","
                            + activation.activationId + " in " + plan);
                }
            }
            if (!selected.isEmpty() && activationIds.isEmpty()) {
                throw new IllegalStateException("Selected activation "
                        + selected + " is absent or non-replayable in "
                        + plan);
            }
        }
    }

    private static final class EngineApi {
        private final Method startRegion;
        private final Method startLegacy;
        private final Method symbolizeWithPrefix;
        private final Method symbolizeLegacy;
        private final Method symbolizeField;
        private final Method getExpression;
        private final Method getSummary;
        private final Method finishRegion;
        private final Method getPathCondition;
        private final Method pausePathCondition;
        private final Method resumePathCondition;
        private final Method markBranch;
        private final Method getBranchEvents;
        private final Method endLegacy;

        private EngineApi(Method startRegion, Method startLegacy,
                          Method symbolizeWithPrefix, Method symbolizeLegacy,
                          Method symbolizeField,
                          Method getExpression, Method getSummary,
                          Method finishRegion, Method getPathCondition,
                          Method pausePathCondition,
                          Method resumePathCondition,
                          Method markBranch, Method getBranchEvents,
                          Method endLegacy) {
            this.startRegion = startRegion;
            this.startLegacy = startLegacy;
            this.symbolizeWithPrefix = symbolizeWithPrefix;
            this.symbolizeLegacy = symbolizeLegacy;
            this.symbolizeField = symbolizeField;
            this.getExpression = getExpression;
            this.getSummary = getSummary;
            this.finishRegion = finishRegion;
            this.getPathCondition = getPathCondition;
            this.pausePathCondition = pausePathCondition;
            this.resumePathCondition = resumePathCondition;
            this.markBranch = markBranch;
            this.getBranchEvents = getBranchEvents;
            this.endLegacy = endLegacy;
        }

        private boolean available() {
            return (startRegion != null || startLegacy != null)
                    && (symbolizeWithPrefix != null || symbolizeLegacy != null)
                    && (finishRegion != null
                    || getPathCondition != null && endLegacy != null)
                    && pausePathCondition != null
                    && resumePathCondition != null;
        }

        private void start(String regionId, String activationId) throws Exception {
            Object status;
            if (startRegion != null) {
                status = startRegion.invoke(null, regionId, activationId);
            } else {
                status = startLegacy.invoke(null);
            }
            if (status instanceof Number
                    && ((Number) status).longValue() != 0L) {
                throw new IllegalStateException(
                        "custom concolic engine rejected region start: "
                                + ((Number) status).longValue());
            }
        }

        private void symbolize(Object value, String prefix) throws Exception {
            if (symbolizeWithPrefix != null) {
                symbolizeWithPrefix.invoke(null, value, prefix);
            } else {
                symbolizeLegacy.invoke(null, value);
            }
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
            if (getExpression == null) {
                return "{\"kind\":\"UNAVAILABLE\",\"symbolic\":false}";
            }
            return String.valueOf(getExpression.invoke(null, value));
        }

        private String finish() throws Exception {
            if (finishRegion != null) {
                return String.valueOf(finishRegion.invoke(null));
            }
            String pc = getPathCondition == null ? "[]"
                    : String.valueOf(getPathCondition.invoke(null));
            if (endLegacy != null) {
                endLegacy.invoke(null);
            }
            return "{\"schemaVersion\":1,\"engine\":\"legacy\","
                    + "\"active\":true,\"pathCondition\":" + pc + "}";
        }

        private String pathCondition() throws Exception {
            if (getPathCondition == null) {
                return "[]";
            }
            return String.valueOf(getPathCondition.invoke(null));
        }

        private void pausePathCondition() throws Exception {
            if (pausePathCondition == null) {
                throw new UnsupportedOperationException(
                        "custom concolic path-condition pause API is unavailable");
            }
            pausePathCondition.invoke(null);
        }

        private void resumePathCondition() throws Exception {
            if (resumePathCondition == null) {
                throw new UnsupportedOperationException(
                        "custom concolic path-condition resume API is unavailable");
            }
            resumePathCondition.invoke(null);
        }

        private boolean exactBranchEventsAvailable() {
            return markBranch != null && getBranchEvents != null;
        }

        private String branchEvents() throws Exception {
            if (getBranchEvents == null) {
                return "{\"schemaVersion\":1,\"active\":false,"
                        + "\"events\":[]}";
            }
            return String.valueOf(getBranchEvents.invoke(null));
        }

        private void forceEnd() {
            if (endLegacy != null) {
                try {
                    endLegacy.invoke(null);
                } catch (Throwable ignored) {
                }
            }
        }

        private static EngineApi load() {
            Class<System> system = System.class;
            return new EngineApi(
                    method(system, "startConcolicRegion", String.class, String.class),
                    method(system, "startConcolic"),
                    method(system, "symbolize", Object.class, String.class),
                    method(system, "symbolize", Object.class),
                    method(system, "symbolizeField", Object.class,
                            String.class, String.class),
                    method(system, "getSymbolicExpression", Object.class),
                    method(system, "getConcolicRegionSummary"),
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

    private static String string(JsonObject object, String field) {
        JsonElement value = object.get(field);
        return value == null || value.isJsonNull() ? "" : value.getAsString();
    }

    private static int integer(JsonObject object, String field, int fallback) {
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longInteger(JsonObject object, String field,
                                    long fallback) {
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsLong();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static boolean bool(JsonObject object, String field,
                                boolean fallback) {
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static JsonArray array(JsonObject object, String field) {
        JsonElement value = object.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static String strictString(JsonObject object, String field) {
        JsonElement value = object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isString()
                ? value.getAsString() : "";
    }

    private static Integer strictInteger(JsonObject object, String field,
                                         int minimum) {
        JsonElement value = object.get(field);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()) {
            return null;
        }
        String text = value.getAsString();
        if (!text.matches("-?(?:0|[1-9][0-9]*)")) {
            return null;
        }
        try {
            int parsed = Integer.parseInt(text);
            return parsed >= minimum ? parsed : null;
        } catch (NumberFormatException ignored) {
            return null;
        }
    }
}
