package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec.DeclaredField;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;

/**
 * Reflective view of the concolic VM's static entry points.
 *
 * <p>Every name below is looked up by reflection so this class remains
 * loadable on a stock JDK. A replay plan requires the complete current
 * broker surface before its workload starts.</p>
 */
final class ConcolicVmBroker {
    /**
     * The broker's own status ABI (expressionBroker.hpp).
     *
     * <p>The numeric values are the VM's, not ours; they are mirrored here so
     * a Java caller can name a failure without linking against the custom
     * JDK.  They live with the broker that returns them -- they used to live
     * beside the gap-row vocabulary that reported them, which is the half
     * that is gone.  -7, -8, -10, -11 and -13..-15 were the identity, shape
     * and fingerprint refusals of a deleted duplicate validation; the numbers
     * stay unassigned because the codes are a shared ABI.</p>
     */
    static final int OK = 0;
    static final int NO_ACTIVE_REGION = -1;
    static final int MISSING_METADATA = -2;
    static final int FIELD_NOT_FOUND = -3;
    static final int NOT_SYMBOLIC = -4;
    static final int FOREIGN_HANDLE = -5;
    static final int UNKNOWN_HANDLE = -6;
    static final int SORT_MISMATCH = -9;
    static final int UNSUPPORTED_TARGET = -12;
    /** Bridge-local statuses, below every value the VM answers. */
    static final int INVOCATION_FAILED = -1001;
    static final int MALFORMED_RESULT = -1002;

    /** Names one broker status, for a message a human reads. */
    static String describe(int status) {
        switch (status) {
            case OK: return "";
            case NO_ACTIVE_REGION: return "NO_ACTIVE_REGION";
            case MISSING_METADATA: return "MISSING_METADATA";
            case FIELD_NOT_FOUND: return "FIELD_NOT_FOUND";
            case NOT_SYMBOLIC: return "NOT_SYMBOLIC";
            case FOREIGN_HANDLE: return "FOREIGN_HANDLE";
            case UNKNOWN_HANDLE: return "UNKNOWN_HANDLE";
            case SORT_MISMATCH: return "SORT_MISMATCH";
            case UNSUPPORTED_TARGET: return "UNSUPPORTED_TARGET";
            case INVOCATION_FAILED: return "INVOCATION_FAILED";
            case MALFORMED_RESULT: return "MALFORMED_RESULT";
            default: return "UNDECLARED_STATUS";
        }
    }

    private static final Object LOCK = new Object();
    private static volatile ConcolicVmBroker engineApi;

    /** The lazily loaded broker for this JVM. */
    static ConcolicVmBroker engine() {
        ConcolicVmBroker current = engineApi;
        if (current != null) {
            return current;
        }
        synchronized (LOCK) {
            if (engineApi == null) {
                engineApi = ConcolicVmBroker.load();
            }
            return engineApi;
        }
    }

    private Method openWorkloadSession;
    private Method closeWorkloadSession;
    private Method workloadSessionStatus;
    private Method startRegion;
    private Method currentContextId;
    private Method currentRegionEnterEventId;
    private Method currentEventId;
    private Method symbolizeWithPrefix;
    private Method symbolizeField;
    private Method symbolizeExactField;
    private Method observeExactPrimitiveField;
    private Method getExpression;
    private Method getFieldExpression;
    private Method finishRegion;
    private Method pausePathCondition;
    private Method resumePathCondition;
    private Method getBranchEvents;
    private Method cleanupEnd;
    private Method export;
    private Method attach;
    private Method range;
    private Method trackedLocations;
    private Method installGuardedStoreSites;

    void requireCurrentCapabilities() {
        List<String> missing = new ArrayList<>();
        for (Field capability : ConcolicVmBroker.class.getDeclaredFields()) {
            if (capability.getType() != Method.class) continue;
            try {
                if (capability.get(this) == null) {
                    missing.add(capability.getName());
                }
            } catch (IllegalAccessException impossible) {
                throw new AssertionError(impossible);
            }
        }
        Collections.sort(missing);
        if (!missing.isEmpty()) {
            throw new IllegalStateException("Concolic task plan requires "
                    + "current custom VM broker capabilities: " + missing);
        }
    }

    /** Positive session id, or a negative VM status. */
    long openWorkloadSession() throws Exception {
        Object status = openWorkloadSession.invoke(null);
        return status instanceof Number
                ? ((Number) status).longValue() : Long.MIN_VALUE;
    }

    /** Zero, or a negative VM status. */
    long closeWorkloadSession() throws Exception {
        Object status = closeWorkloadSession.invoke(null);
        return status instanceof Number
                ? ((Number) status).longValue() : Long.MIN_VALUE;
    }

    /** One JSON snapshot of the session, or {@code ""} when absent. */
    String workloadSessionStatus() {
        if (workloadSessionStatus == null) return "";
        try {
            return safe(String.valueOf(
                    workloadSessionStatus.invoke(null)));
        } catch (Throwable unavailable) {
            return "";
        }
    }

    void start(String regionId, String taskId) throws Exception {
        Object status = startRegion.invoke(null, regionId, taskId);
        if (status instanceof Number
                && ((Number) status).longValue() != 0L) {
            throw new IllegalStateException(
                    "custom concolic engine rejected region start: "
                            + ((Number) status).longValue());
        }
    }

    /**
     * The VM's own context id, or a negative status.
     *
     * <p>A VM answer that is not a number is {@link #MALFORMED_RESULT} and
     * not {@code 0L}: zero is what a VM with no such notion would answer,
     * and the two used to be one value.  Both readings are refused by the
     * caller's {@code <= 0} check, so the answer only becomes nameable --
     * which is the whole difference between "the engine has no context
     * here" and "the engine answered something this bridge cannot read".</p>
     */
    long currentContextId() throws Exception {
        Object value = currentContextId.invoke(null);
        return value instanceof Number
                ? ((Number) value).longValue() : MALFORMED_RESULT;
    }

    /** The region-enter event id, or a negative status; see above. */
    long currentRegionEnterEventId() throws Exception {
        Object value = currentRegionEnterEventId.invoke(null);
        return value instanceof Number
                ? ((Number) value).longValue() : MALFORMED_RESULT;
    }

    /**
     * The id of the last event the VM's symbolic session published.
     *
     * <p>Versions, reads and region entries are numbered from one monotone
     * session counter, so this reading brackets the events that happened
     * while the caller stood where it stood -- which is what aligns the
     * runtime's frame journal with the VM's log (FrameJournal).</p>
     */
    long currentEventId() throws Exception {
        Object value = currentEventId.invoke(null);
        return value instanceof Number
                ? ((Number) value).longValue() : -1L;
    }

    void symbolize(Object value, String prefix) throws Exception {
        symbolizeWithPrefix.invoke(null, value, prefix);
    }

    void symbolizeField(Object owner, String field, String prefix)
            throws Exception {
        symbolizeField.invoke(null, owner, field, prefix);
    }

    void symbolizeExactField(
            Object owner, String fieldSignature, String prefix)
            throws Exception {
        DeclaredField field = FieldPathSpec.declaredField(
                safe(fieldSignature));
        if (field == null) {
            throw new UnsupportedOperationException(
                    "no exact declared field for symbolized leaf: "
                            + safe(fieldSignature));
        }
        symbolizeExactField.invoke(null, owner, field.owner(),
                field.name(), javaTypeDescriptor(field.type()), prefix);
    }

    /**
     * Attaches the value one exact int/long field holds right now as that
     * field's concrete expression.
     *
     * <p>Not a symbolic input: the leaf the VM installs is a
     * {@code ConExpression} over the value the field already has
     * ({@code concolicMngr.cpp:887}).  What it buys is that the location
     * becomes one the VM will version -- retention is by value, so an
     * untracked field's writes leave no version behind at all, and a write
     * site the plan selected would publish nothing.  The write that follows
     * is then a version like any other store's, carrying the expression the
     * VM built from this observed value.</p>
     */
    void observeExactPrimitiveField(Object owner, String fieldSignature)
            throws Exception {
        DeclaredField field = FieldPathSpec.declaredField(
                safe(fieldSignature));
        if (field == null) {
            throw new UnsupportedOperationException(
                    "no exact declared field for observed leaf: "
                            + safe(fieldSignature));
        }
        observeExactPrimitiveField.invoke(null, owner, field.owner(),
                field.name(), javaTypeDescriptor(field.type()));
    }

    String expression(Object value) throws Exception {
        return String.valueOf(getExpression.invoke(null, value));
    }

    String fieldExpression(
            Object owner, String declaringClass, String fieldName,
            String fieldDescriptor, Object value)
            throws Exception {
        return String.valueOf(getFieldExpression.invoke(null, owner,
                declaringClass, fieldName, fieldDescriptor, value));
    }

    String finish() throws Exception {
        return String.valueOf(finishRegion.invoke(null));
    }

    void pausePathCondition() throws Exception {
        pausePathCondition.invoke(null);
    }

    void resumePathCondition() throws Exception {
        resumePathCondition.invoke(null);
    }

    String branchEvents() throws Exception {
        return String.valueOf(getBranchEvents.invoke(null));
    }

    void cleanupAfterFailure() {
        if (cleanupEnd != null) {
            try {
                cleanupEnd.invoke(null);
            } catch (Throwable ignored) {
            }
        }
    }

    /**
     * Exports one field and reports its session-unique endpoint id.
     *
     * <p>A non-numeric answer is {@link #MALFORMED_RESULT}, which is what
     * the caller's {@code exportStatus} already maps a zero to: the status
     * is the same and the value now says which reading produced it.  A
     * legal "no handle" is still 0 and still distinguishable -- it is what
     * a NOT_SYMBOLIC leaf is staged on the wire with, and what
     * {@code attachDeliveredLeaf} reads as "the delivery carried no producer
     * expression".</p>
     */
    long exportExpression(
            Object owner, String declaringClass, String fieldName,
            String descriptor, long[] eventOut) throws Exception {
        Object handle = export.invoke(null, owner, declaringClass,
                fieldName, descriptor, eventOut);
        return handle instanceof Number
                ? ((Number) handle).longValue() : MALFORMED_RESULT;
    }

    /**
     * Attaches one live handle. The return value identifies the export;
     * {@code eventOut} receives this attach's session-unique endpoint id.
     */
    long attachExpression(
            Object owner, String declaringClass, String fieldName,
            String descriptor, long handle, long[] eventOut)
            throws Exception {
        Object answer = attach.invoke(null, owner, declaringClass,
                fieldName, descriptor, handle, eventOut);
        return answer instanceof Number
                ? ((Number) answer).longValue()
                : MALFORMED_RESULT;
    }

    String pathConditionRange(int startIndex, int endIndex)
            throws Exception {
        return String.valueOf(range.invoke(null, startIndex, endIndex));
    }

    /**
     * Every location a symbolic value reached, with its versions and reads.
     *
     * <p>The write log, read out by the object the VM filed it under rather
     * than by a location Java declared.  {@code afterEventId} selects on the
     * session clock over versions and reads, so an activation scopes itself
     * by passing its own entry event and the VM needs no notion of a region;
     * {@code maxBytes} bounds one answer, which then says {@code complete:
     * false} and where to resume.  0 means "everything" and "no bound".</p>
     */
    String trackedLocationVersions(long afterEventId, int maxBytes)
            throws Exception {
        return requiredVmJson(trackedLocations.invoke(null, afterEventId,
                maxBytes), "getTrackedLocationVersions");
    }

    /**
     * Installs the session's guarded-store table and answers how many store
     * methods the VM kept.
     *
     * <p>One line per method: {@code <internal/Class>#<name><descriptor>}
     * followed by that method's guard branch sites, one tab-separated field
     * each.  Installing replaces the table, and with no table no concrete
     * store is ever evidence.  The table's content is
     * {@link GuardedStoreSites}; this is only the call.</p>
     */
    int installGuardedStoreSites(String table) throws Exception {
        Object kept = installGuardedStoreSites.invoke(null, table);
        return kept instanceof Number
                ? ((Number) kept).intValue() : MALFORMED_RESULT;
    }

    private static String requiredVmJson(Object value, String api) {
        if (!(value instanceof String)
                || ((String) value).trim().isEmpty()) {
            throw new IllegalStateException(api
                    + " returned no serialized VM evidence");
        }
        return (String) value;
    }

    private static ConcolicVmBroker load() {
        Class<System> system = System.class;
        ConcolicVmBroker api = new ConcolicVmBroker();
        api.openWorkloadSession = method(system, "openWorkloadSession");
        api.closeWorkloadSession = method(system, "closeWorkloadSession");
        api.workloadSessionStatus =
                method(system, "getWorkloadSessionStatus");
        api.startRegion = method(system, "startConcolicRegion",
                String.class, String.class);
        api.currentContextId = method(system,
                "getCurrentConcolicContextId");
        api.currentRegionEnterEventId = method(system,
                "getCurrentConcolicRegionEnterEventId");
        api.currentEventId = method(system, "currentSymbolicEventId");
        api.symbolizeWithPrefix = method(system, "symbolize",
                Object.class, String.class);
        api.symbolizeField = method(system, "symbolizeField",
                Object.class, String.class, String.class);
        api.symbolizeExactField = method(system, "symbolizeExactField",
                Object.class, String.class, String.class, String.class,
                String.class);
        api.observeExactPrimitiveField = method(system,
                "observeExactPrimitiveField", Object.class, String.class,
                String.class, String.class);
        api.getExpression = method(system, "getSymbolicExpression",
                Object.class);
        api.getFieldExpression = method(system,
                "getSymbolicFieldExpression", Object.class, String.class,
                String.class, String.class, Object.class);
        api.finishRegion = method(system, "finishConcolicRegion");
        api.pausePathCondition =
                method(system, "pauseConcolicPathCondition");
        api.resumePathCondition =
                method(system, "resumeConcolicPathCondition");
        api.getBranchEvents = method(system, "getConcolicBranchEvents");
        api.cleanupEnd = method(system, "endConcolic");
        api.export = method(system, "exportExpression", Object.class,
                String.class, String.class, String.class, long[].class);
        api.attach = method(system, "attachExpression", Object.class,
                String.class, String.class, String.class, long.class,
                long[].class);
        api.trackedLocations = method(system,
                "getTrackedLocationVersions", long.class, int.class);
        api.range = method(system, "getConcolicPathConditionRange",
                int.class, int.class);
        api.installGuardedStoreSites = method(system,
                "installGuardedStoreSites", String.class);
        return api;
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
