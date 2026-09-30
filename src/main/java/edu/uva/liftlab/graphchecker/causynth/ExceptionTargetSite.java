package edu.uva.liftlab.graphchecker.causynth;

/**
 * Immutable class-file identity for one declared exception construction
 * ({@link ExceptionTargetLineResolver}); {@code id} is the target's name.
 */
public final class ExceptionTargetSite {
    final String id;
    final String className;
    final String methodName;
    final String methodDescriptor;
    final String methodSignature;
    final String exceptionClass;
    final int exceptionConstructionOrdinal;

    ExceptionTargetSite(String id, String className, String methodName,
                        String methodDescriptor, String methodSignature,
                        String exceptionClass,
                        int exceptionConstructionOrdinal) {
        this.id = id == null ? "" : id;
        this.className = className;
        this.methodName = methodName;
        this.methodDescriptor = methodDescriptor;
        this.methodSignature = methodSignature;
        this.exceptionClass = exceptionClass;
        this.exceptionConstructionOrdinal = exceptionConstructionOrdinal;
    }

    public String stableIdentity() {
        return className + "#" + methodName + methodDescriptor + "#new:"
                + exceptionClass + "#" + exceptionConstructionOrdinal;
    }

}
