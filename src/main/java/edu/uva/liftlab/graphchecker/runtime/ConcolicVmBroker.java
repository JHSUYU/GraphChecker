package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.concolic.RpcExpressionHandoff;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.safe;

/**
 * Reflective view of the concolic VM's static entry points.
 *
 * <p>Every name below is looked up by reflection so this class remains
 * loadable on a stock JDK. A replay plan requires the complete current
 * broker surface before its workload starts.</p>
 */
final class ConcolicVmBroker {
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
    private Method symbolizeWithPrefix;
    private Method symbolizeField;
    private Method symbolizeExactField;
    private Method trackContainer;
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
    private Method selectField;
    private Method armPrimitiveFieldRead;
    private Method confirmPrimitiveFieldRead;
    private Method selectElement;
    private Method selectMap;
    private Method fieldVersions;
    private Method elementVersions;
    private Method mapVersions;

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

    long currentContextId() throws Exception {
        Object value = currentContextId.invoke(null);
        return value instanceof Number
                ? ((Number) value).longValue() : 0L;
    }

    long currentRegionEnterEventId() throws Exception {
        Object value = currentRegionEnterEventId.invoke(null);
        return value instanceof Number
                ? ((Number) value).longValue() : 0L;
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

    boolean trackContainer(Object value, String prefix)
            throws Exception {
        return Boolean.TRUE.equals(trackContainer.invoke(
                null, value, prefix));
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

    /** Exports one field and reports its session-unique endpoint id. */
    long exportExpression(
            Object owner, String declaringClass, String fieldName,
            String descriptor, long[] eventOut) throws Exception {
        Object handle = export.invoke(null, owner, declaringClass,
                fieldName, descriptor, eventOut);
        return handle instanceof Number
                ? ((Number) handle).longValue() : 0L;
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
                : RpcExpressionHandoff.MALFORMED_RESULT;
    }

    String pathConditionRange(int startIndex, int endIndex)
            throws Exception {
        return String.valueOf(range.invoke(null, startIndex, endIndex));
    }

    long selectSharedFieldCarrier(
            Object owner, String declaringClass, String fieldName,
            String descriptor) throws Exception {
        Object version = selectField.invoke(null, owner, declaringClass,
                fieldName, descriptor);
        if (!(version instanceof Number)) {
            throw new IllegalStateException(
                    "selectSharedFieldCarrier returned no numeric version");
        }
        return ((Number) version).longValue();
    }

    /** Arms the concrete operand of the immediately following getfield. */
    long armSharedPrimitiveFieldRead(
            Object owner, String declaringClass, String fieldName,
            String descriptor, long valueBits) throws Exception {
        Object status = armPrimitiveFieldRead.invoke(null, owner,
                declaringClass, fieldName, descriptor, valueBits);
        return status instanceof Number
                ? ((Number) status).longValue() : Long.MIN_VALUE;
    }

    /** Consumes the VM's receipt for one armed concrete field operand. */
    long confirmSharedPrimitiveFieldRead(long token)
            throws Exception {
        Object status = confirmPrimitiveFieldRead.invoke(null, token);
        return status instanceof Number
                ? ((Number) status).longValue() : Long.MIN_VALUE;
    }

    long selectSharedElementCarrier(Object array, int index)
            throws Exception {
        Object version = selectElement.invoke(null, array, index);
        if (!(version instanceof Number)) {
            throw new IllegalStateException(
                    "selectSharedElementCarrier returned no numeric version");
        }
        return ((Number) version).longValue();
    }

    long selectSharedMapCarrier(Object map) throws Exception {
        Object version = selectMap.invoke(null, map);
        if (!(version instanceof Number)) {
            throw new IllegalStateException(
                    "selectSharedMapCarrier returned no numeric version");
        }
        return ((Number) version).longValue();
    }

    String sharedMapVersions(Object map) throws Exception {
        return requiredVmJson(mapVersions.invoke(null, map),
                "getSharedMapVersions");
    }

    String sharedFieldVersions(
            Object owner, String declaringClass, String fieldName,
            String descriptor) throws Exception {
        return requiredVmJson(fieldVersions.invoke(null, owner,
                declaringClass, fieldName, descriptor),
                "getSharedFieldVersions");
    }

    String sharedElementVersions(Object array, int index)
            throws Exception {
        return requiredVmJson(elementVersions.invoke(null, array, index),
                "getSharedElementVersions");
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
        api.symbolizeWithPrefix = method(system, "symbolize",
                Object.class, String.class);
        api.symbolizeField = method(system, "symbolizeField",
                Object.class, String.class, String.class);
        api.symbolizeExactField = method(system, "symbolizeExactField",
                Object.class, String.class, String.class, String.class,
                String.class);
        api.trackContainer = method(system, "trackContainerExpression",
                Object.class, String.class);
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
        api.range = method(system, "getConcolicPathConditionRange",
                int.class, int.class);
        api.selectField = method(system, "selectSharedFieldCarrier",
                Object.class, String.class, String.class, String.class);
        api.armPrimitiveFieldRead = method(system,
                "armSharedPrimitiveFieldRead", Object.class,
                String.class, String.class, String.class, long.class);
        api.confirmPrimitiveFieldRead = method(system,
                "confirmSharedPrimitiveFieldRead", long.class);
        api.selectElement = method(system, "selectSharedElementCarrier",
                Object.class, int.class);
        api.selectMap = method(system, "selectSharedMapCarrier",
                Object.class);
        api.fieldVersions = method(system, "getSharedFieldVersions",
                Object.class, String.class, String.class, String.class);
        api.elementVersions = method(system, "getSharedElementVersions",
                Object.class, int.class);
        api.mapVersions = method(system, "getSharedMapVersions",
                Object.class);
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
