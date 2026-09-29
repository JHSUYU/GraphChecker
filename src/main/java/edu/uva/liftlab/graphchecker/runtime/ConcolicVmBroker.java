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
 * Reflective view of the concolic VM's static entry points, so this class
 * loads on a stock JDK.  A replay plan requires the whole surface
 * ({@link #requireCurrentCapabilities}) before its workload starts.
 */
final class ConcolicVmBroker {
    /** The statuses this side reads, mirrored from expressionBroker.hpp. */
    static final int OK = 0;
    static final int MISSING_METADATA = -2;
    static final int NOT_SYMBOLIC = -4;
    /** Bridge-local statuses, below every value the VM answers. */
    static final int INVOCATION_FAILED = -1001;
    static final int MALFORMED_RESULT = -1002;

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

    /** The VM's context id, or a negative status (non-number: MALFORMED). */
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
     * The last event id of the VM's session: one monotone counter for
     * versions, reads and region entries (aligns FrameJournal to the log).
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
     * Attaches the current value of one exact integral field as its concrete
     * expression ({@code ConExpression}, not a symbolic input).  Its point:
     * the VM versions only tracked locations, so without it a selected write
     * site would publish nothing.
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
     * Exports one field and returns its handle, or {@link #MALFORMED_RESULT}
     * for a non-number.  0 is the legal "no handle" of a NOT_SYMBOLIC leaf.
     */
    long exportExpression(
            Object owner, String declaringClass, String fieldName,
            String descriptor, long[] eventOut) throws Exception {
        Object handle = export.invoke(null, owner, declaringClass,
                fieldName, descriptor, eventOut);
        return handle instanceof Number
                ? ((Number) handle).longValue() : MALFORMED_RESULT;
    }

    /** Attaches one live handle; {@code eventOut} gets the endpoint id. */
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
     * The write log: every location a symbolic value reached, with versions
     * and reads after {@code afterEventId} (an activation passes its entry
     * event).  {@code maxBytes} bounds one answer ({@code complete: false}
     * then says where to resume); 0 means no bound.
     */
    String trackedLocationVersions(long afterEventId, int maxBytes)
            throws Exception {
        return requiredVmJson(trackedLocations.invoke(null, afterEventId,
                maxBytes), "getTrackedLocationVersions");
    }

    /**
     * Installs (replaces) the guarded-store table built by
     * {@link GuardedStoreSites} and answers how many methods the VM kept.
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
