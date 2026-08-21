package edu.uva.liftlab.graphchecker.causynth;

/**
 * Immutable class-file identity for one annotated exception construction.
 *
 * <p>Public so that an integration layer - a workload launcher, say - can
 * resolve the same annotated site the analysis resolves, instead of growing a
 * second way to name a target. The fields stay package-private; callers
 * outside this package read the accessors.</p>
 */
public final class ExceptionTargetSite {
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

    public String stableIdentity() {
        return className + "#" + methodName + methodDescriptor + "#new:"
                + exceptionClass + "#" + exceptionConstructionOrdinal;
    }

    public String id() {
        return id;
    }

    public String className() {
        return className;
    }

    public String methodName() {
        return methodName;
    }

    public String methodDescriptor() {
        return methodDescriptor;
    }

    public String exceptionClass() {
        return exceptionClass;
    }

    public int sourceLine() {
        return sourceLine;
    }
}
