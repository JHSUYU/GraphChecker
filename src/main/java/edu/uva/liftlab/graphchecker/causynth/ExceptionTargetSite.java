package edu.uva.liftlab.graphchecker.causynth;

import java.util.LinkedHashMap;
import java.util.Map;

/** Immutable class-file identity for one annotated exception construction. */
final class ExceptionTargetSite {
    final String id;
    final String className;
    final String methodName;
    final String methodDescriptor;
    final String methodSignature;
    final String exceptionClass;
    final int exceptionConstructionOrdinal;
    final int bytecodeInstructionIndex;
    final int sourceLine;

    ExceptionTargetSite(String id, String className, String methodName,
                        String methodDescriptor, String methodSignature,
                        String exceptionClass,
                        int exceptionConstructionOrdinal,
                        int bytecodeInstructionIndex, int sourceLine) {
        this.id = id == null ? "" : id;
        this.className = className;
        this.methodName = methodName;
        this.methodDescriptor = methodDescriptor;
        this.methodSignature = methodSignature;
        this.exceptionClass = exceptionClass;
        this.exceptionConstructionOrdinal = exceptionConstructionOrdinal;
        this.bytecodeInstructionIndex = bytecodeInstructionIndex;
        this.sourceLine = sourceLine;
    }

    String stableIdentity() {
        return className + "#" + methodName + methodDescriptor + "#new:"
                + exceptionClass + "#" + exceptionConstructionOrdinal;
    }

    Map<String, Object> toMap() {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("id", id);
        row.put("class", className);
        row.put("methodName", methodName);
        row.put("methodDescriptor", methodDescriptor);
        row.put("method", methodSignature);
        row.put("exception", exceptionClass);
        row.put("exceptionConstructionOrdinal",
                exceptionConstructionOrdinal);
        row.put("bytecodeInstructionIndex", bytecodeInstructionIndex);
        row.put("sourceLine", sourceLine);
        row.put("stableIdentity", stableIdentity());
        row.put("authority",
                "CLASSFILE_CAUSYNTH_EXCEPTION_TARGET_TYPE_USE_V1");
        return row;
    }
}
