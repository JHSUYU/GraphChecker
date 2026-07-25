package edu.uva.liftlab.graphchecker.causynth;

/** Immutable class-file identity for one annotated exception construction. */
final class ExceptionTargetSite {
    final String id;
    final String className;
    final String methodName;
    final String methodDescriptor;
    final String methodSignature;
    final String exceptionClass;
    final int exceptionConstructionOrdinal;
    final int sourceLine;

    ExceptionTargetSite(String id, String className, String methodName,
                        String methodDescriptor, String methodSignature,
                        String exceptionClass,
                        int exceptionConstructionOrdinal,
                        int sourceLine) {
        this.id = id == null ? "" : id;
        this.className = className;
        this.methodName = methodName;
        this.methodDescriptor = methodDescriptor;
        this.methodSignature = methodSignature;
        this.exceptionClass = exceptionClass;
        this.exceptionConstructionOrdinal = exceptionConstructionOrdinal;
        this.sourceLine = sourceLine;
    }

    String stableIdentity() {
        return className + "#" + methodName + methodDescriptor + "#new:"
                + exceptionClass + "#" + exceptionConstructionOrdinal;
    }

}
