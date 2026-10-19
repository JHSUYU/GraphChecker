package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec.DeclaredField;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;

final class ConcolicVmBroker {
    static final int OK = 0;
    static final int NO_ACTIVE_REGION = -1;
    static final int MISSING_METADATA = -2;
    static final int NOT_SYMBOLIC = -4;
    static final int UNSUPPORTED_TARGET = -12;
    static final int INVOCATION_FAILED = -1001;
    static final int MALFORMED_RESULT = -1002;

    static String statusName(long status) {
        switch (status == (int) status ? (int) status : 0) {
            case -1: return "HANDOFF_NO_ACTIVE_REGION";
            case -2: return "HANDOFF_MISSING_METADATA";
            case -3: return "HANDOFF_FIELD_NOT_FOUND";
            case -4: return "HANDOFF_NOT_SYMBOLIC";
            case -5: return "HANDOFF_FOREIGN_HANDLE";
            case -6: return "HANDOFF_UNKNOWN_HANDLE";
            case -9: return "HANDOFF_SORT_MISMATCH";
            case -12: return "HANDOFF_UNSUPPORTED_TARGET";
            case INVOCATION_FAILED: return "INVOCATION_FAILED";
            case MALFORMED_RESULT: return "MALFORMED_RESULT";
            default: return "status " + status;
        }
    }

    private static final Object LOCK = new Object();
    private static volatile ConcolicVmBroker engineApi;

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
    private Method workloadSessionStatus;
    private Method startRegion;
    private Method currentContextId;
    private Method currentRegionEnterEventId;
    private Method currentEventId;
    private Method symbolizeWithPrefix;
    private Method symbolizeField;
    private Method symbolizeExactField;
    private Method observeField;
    private Method observeContainer;
    private Method getExpression;
    private Method getFieldExpression;
    private Method finishRegion;
    private Method pausePathCondition;
    private Method resumePathCondition;
    private Method pauseBase;
    private Method resumeBase;
    private Method getBranchEvents;
    private Method cleanupEnd;
    private Method export;
    private Method attach;
    private Method range;
    private Method readOutTrackedLocations;
    private Method installGuardedStoreSites;
    private Method forceNextBranch;
    private Method exportLeaf;
    private Method mintLeaf;

    enum SlotKind { FIELD, ELEMENT, ENTRY, POSITION, VALUE }

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

    long openWorkloadSession() throws Exception {
        Object status = openWorkloadSession.invoke(null);
        return status instanceof Number
                ? ((Number) status).longValue() : Long.MIN_VALUE;
    }

    String workloadSessionStatus() {
        if (workloadSessionStatus == null) return "";
        try {
            return nonNull(String.valueOf(
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
                ? ((Number) value).longValue() : MALFORMED_RESULT;
    }

    long currentRegionEnterEventId() throws Exception {
        Object value = currentRegionEnterEventId.invoke(null);
        return value instanceof Number
                ? ((Number) value).longValue() : MALFORMED_RESULT;
    }

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
                nonNull(fieldSignature));
        if (field == null) {
            throw new UnsupportedOperationException(
                    "no exact declared field for symbolized leaf: "
                            + nonNull(fieldSignature));
        }
        symbolizeExactField.invoke(null, owner, field.owner(),
                field.name(), javaTypeDescriptor(field.type()), prefix);
    }

    void observeField(Object owner, String fieldSignature) throws Exception {
        DeclaredField field = FieldPathSpec.declaredField(
                nonNull(fieldSignature));
        if (field == null) {
            throw new UnsupportedOperationException(
                    "no exact declared field for observed leaf: "
                            + nonNull(fieldSignature));
        }
        Object status = observeField.invoke(null, owner, field.owner(),
                field.name(), javaTypeDescriptor(field.type()));
        long answered = status instanceof Number
                ? ((Number) status).longValue() : MALFORMED_RESULT;
        if (answered != OK) {
            throw new IllegalStateException(statusName(answered)
                    + ": the VM did not observe " + nonNull(fieldSignature));
        }
    }

    long observeContainer(Object value, boolean afterMutation)
            throws Exception {
        Object status = observeContainer.invoke(null, value, afterMutation);
        long answered = status instanceof Number
                ? ((Number) status).longValue() : MALFORMED_RESULT;
        if (answered != OK && answered != NO_ACTIVE_REGION
                && answered != UNSUPPORTED_TARGET) {
            throw new IllegalStateException(statusName(answered)
                    + ": the VM did not observe a container");
        }
        return answered;
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

    void pauseBase() throws Exception {
        pauseBase.invoke(null);
    }

    void resumeBase() throws Exception {
        resumeBase.invoke(null);
    }

    static boolean pauseEngineWork() {
        ConcolicVmBroker loaded = engineApi;
        Method pause = loaded == null ? null : loaded.pausePathCondition;
        if (pause == null) return false;
        invokeNative(pause);
        return true;
    }

    static void resumeEngineWork() {
        invokeNative(engineApi.resumePathCondition);
    }

    static void asEngineWork(Runnable work) {
        boolean paused = pauseEngineWork();
        try {
            work.run();
        } finally {
            if (paused) resumeEngineWork();
        }
    }

    private static void invokeNative(Method method) {
        try {
            method.invoke(null);
        } catch (ReflectiveOperationException failed) {
            throw new IllegalStateException(
                    "the VM's " + method.getName() + " failed", failed);
        }
    }

    String branchEvents() throws Exception {
        return String.valueOf(getBranchEvents.invoke(null));
    }

    int forceNextBranch(boolean jump) throws Exception {
        Object status = forceNextBranch.invoke(null, jump);
        return status instanceof Number ? ((Number) status).intValue()
                : MALFORMED_RESULT;
    }

    void cleanupAfterFailure() {
        if (cleanupEnd != null) {
            try {
                cleanupEnd.invoke(null);
            } catch (Throwable ignored) {
            }
        }
    }

    long exportExpression(
            Object owner, String declaringClass, String fieldName,
            String descriptor, long[] eventOut) throws Exception {
        Object handle = export.invoke(null, owner, declaringClass,
                fieldName, descriptor, eventOut);
        return handle instanceof Number
                ? ((Number) handle).longValue() : MALFORMED_RESULT;
    }

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

    String readOutTrackedLocations(long afterEventId, int maxBytes)
            throws Exception {
        return requiredVmJson(readOutTrackedLocations.invoke(null,
                afterEventId, maxBytes), "readOutTrackedLocations");
    }

    int installGuardedStoreSites(String table) throws Exception {
        Object kept = installGuardedStoreSites.invoke(null, table);
        return kept instanceof Number
                ? ((Number) kept).intValue() : MALFORMED_RESULT;
    }

    String exportLeaf(Object parent, SlotKind kind, Object slot)
            throws Exception {
        return requiredVmJson(exportLeaf.invoke(null, parent, kind.ordinal(),
                slot), "exportLeaf");
    }

    String mintLeaf(Object parent, SlotKind kind, Object slot,
                    String template) throws Exception {
        return requiredVmJson(mintLeaf.invoke(null, parent, kind.ordinal(),
                slot, template), "mintLeaf");
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
        api.observeField = method(system, "observeField", Object.class,
                String.class, String.class, String.class);
        api.observeContainer = method(system, "observeContainer",
                Object.class, boolean.class);
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
        api.pauseBase = method(system, "pauseConcolicBase");
        api.resumeBase = method(system, "resumeConcolicBase");
        api.getBranchEvents = method(system, "getConcolicBranchEvents");
        api.cleanupEnd = method(system, "endConcolic");
        api.export = method(system, "exportExpression", Object.class,
                String.class, String.class, String.class, long[].class);
        api.attach = method(system, "attachExpression", Object.class,
                String.class, String.class, String.class, long.class,
                long[].class);
        api.readOutTrackedLocations = method(system,
                "readOutTrackedLocations", long.class, int.class);
        api.range = method(system, "getConcolicPathConditionRange",
                int.class, int.class);
        api.installGuardedStoreSites = method(system,
                "installGuardedStoreSites", String.class);
        api.forceNextBranch = method(system, "forceNextConcolicBranch",
                boolean.class);
        api.exportLeaf = method(system, "exportLeaf", Object.class,
                int.class, Object.class);
        api.mintLeaf = method(system, "mintLeaf", Object.class, int.class,
                Object.class, String.class);
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
