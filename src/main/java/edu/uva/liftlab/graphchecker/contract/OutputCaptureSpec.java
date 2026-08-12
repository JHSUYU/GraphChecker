package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** One canonical output endpoint captured by a scheduled execution task. */
public final class OutputCaptureSpec {
    public static final String CALL_ARGUMENT = "CALL_ARGUMENT";
    public static final String MUTATION_STATE = "MUTATION_STATE";
    public static final String FIELD_WRITE_STATE = "FIELD_WRITE_STATE";
    public static final String REGION_ACTIVATION_SCOPE =
            "REGION_ACTIVATION";
    public static final String DEFINITION_INVOCATION_SCOPE =
            "DEFINITION_INVOCATION";

    private final String captureBindingId;
    private final String outputPort;
    private final String captureKind;
    private final String outputCell;
    private final String javaType;
    private final String accessRootInputPort;
    private final List<String> fieldPath;
    private final String fieldSignature;
    private final String definitionFieldSignature;
    private final String leafFieldSignature;
    private final String definitionMethod;
    private final String declaredCallee;
    private final int definitionUnitIndex;
    private final int argumentIndex;
    private final boolean occurrenceScoped;
    private final String occurrenceScope;
    private final String outputSiteId;
    private final int outputOccurrence;
    private final int replayOccurrence;

    static OutputCaptureSpec decodeValidated(JsonObject encoded) {
        return new OutputCaptureSpec(encoded);
    }

    private OutputCaptureSpec(JsonObject encoded) {
        captureBindingId = string(encoded, "captureBindingId");
        outputPort = string(encoded, "outputPort");
        captureKind = string(encoded, "captureKind");
        outputCell = string(encoded, "outputCell");
        javaType = string(encoded, "javaType");
        accessRootInputPort = string(encoded, "accessRootInputPort");
        fieldPath = Collections.unmodifiableList(new ArrayList<>(
                FieldPathSpec.stringArray(encoded, "fieldPath")));
        fieldSignature = string(encoded, "fieldSignature");
        definitionFieldSignature = encoded.has("definitionFieldSignature")
                ? string(encoded, "definitionFieldSignature")
                : fieldSignature;
        leafFieldSignature = encoded.has("leafFieldSignature")
                ? string(encoded, "leafFieldSignature")
                : fieldSignature;
        definitionMethod = string(encoded, "definitionMethod");
        declaredCallee = string(encoded, "declaredCallee");
        definitionUnitIndex = encoded.has("definitionUnitIndex")
                ? encoded.get("definitionUnitIndex").getAsInt() : -1;
        argumentIndex = encoded.has("argumentIndex")
                ? encoded.get("argumentIndex").getAsInt() : -1;
        occurrenceScoped = encoded.has("outputSiteId")
                || encoded.has("outputOccurrence")
                || encoded.has("replayOccurrence");
        occurrenceScope = occurrenceScoped
                ? string(encoded, "occurrenceScope").isEmpty()
                ? REGION_ACTIVATION_SCOPE
                : string(encoded, "occurrenceScope")
                : "";
        outputSiteId = string(encoded, "outputSiteId");
        outputOccurrence = encoded.has("outputOccurrence")
                ? encoded.get("outputOccurrence").getAsInt() : 1;
        replayOccurrence = encoded.has("replayOccurrence")
                ? encoded.get("replayOccurrence").getAsInt()
                : outputOccurrence;
        // The ordinal is recorded provenance, not a replay demand: the goal
        // states the relation without one, and a bounded replay reaches the
        // site a different number of times than the recording did.  Refusing
        // a recorded ordinal past the replay window would discard an output
        // the recording proves for a reason the relation never asserted.
        if (occurrenceScoped && (outputSiteId.isEmpty()
                || outputOccurrence < 1
                || replayOccurrence != outputOccurrence)) {
            throw new IllegalArgumentException(
                    "invalid bounded output capture occurrence");
        }
        if (occurrenceScoped
                && !REGION_ACTIVATION_SCOPE.equals(occurrenceScope)
                && !DEFINITION_INVOCATION_SCOPE.equals(occurrenceScope)) {
            throw new IllegalArgumentException(
                    "unsupported output occurrence scope: "
                            + occurrenceScope);
        }
        if (DEFINITION_INVOCATION_SCOPE.equals(occurrenceScope)
                && !capturesMutationState()) {
            throw new IllegalArgumentException(
                    "definition-invocation scope requires mutation-state "
                            + "capture");
        }
        validateProjectedFieldWrite(encoded);
    }

    public String captureBindingId() {
        return captureBindingId;
    }

    public String outputPort() {
        return outputPort;
    }

    /** Empty is the original region-exit field capture contract. */
    public boolean capturesCallArgument() {
        return CALL_ARGUMENT.equals(captureKind);
    }

    /**
     * Selects one exact mutator occurrence and captures its receiver when the
     * enclosing mutation method completes normally.
     */
    public boolean capturesMutationState() {
        return MUTATION_STATE.equals(captureKind);
    }

    /** Captures the owner field immediately after one putfield assignment. */
    public boolean capturesFieldWriteState() {
        return FIELD_WRITE_STATE.equals(captureKind);
    }

    public boolean capturesExactHeapWrite() {
        return capturesMutationState() || capturesFieldWriteState();
    }

    /** The compatibility endpoint observed only when the region exits. */
    public boolean capturesRegionExitField() {
        return captureKind.isEmpty();
    }

    public String accessRootInputPort() {
        return accessRootInputPort;
    }

    public List<String> fieldPath() {
        return fieldPath;
    }

    public String fieldSignature() {
        return fieldSignature;
    }

    /** Exact field declaration written by the selected {@code putfield}. */
    public String definitionFieldSignature() {
        return definitionFieldSignature;
    }

    /** Primitive semantic leaf captured from the value stored by the write. */
    public String leafFieldSignature() {
        return leafFieldSignature;
    }

    /** True only for an explicit field-write projection below the write. */
    public boolean nestedFieldWriteState() {
        return capturesFieldWriteState()
                && !definitionFieldSignature.equals(leafFieldSignature);
    }

    public String definitionMethod() {
        return definitionMethod;
    }

    public int definitionUnitIndex() {
        return definitionUnitIndex;
    }

    public String declaredCallee() {
        return declaredCallee;
    }

    /**
     * Exact primitive state updated by the arithmetic Atomic RMW summaries.
     *
     * <p>This deliberately names only the small API surface implemented by
     * the custom VM.  In particular, compare-and-set and functional update
     * methods must continue through their ordinary concrete/native path.</p>
     */
    public String atomicArithmeticValueFieldSignature() {
        if (!capturesMutationState()) return "";
        return atomicArithmeticValueFieldSignature(declaredCallee);
    }

    /** Exact primitive state updated by one supported Atomic RMW call. */
    public static String atomicArithmeticValueFieldSignature(
            String declaredCallee) {
        switch (declaredCallee == null ? "" : declaredCallee.trim()) {
            case "<java.util.concurrent.atomic.AtomicInteger: int getAndIncrement()>":
            case "<java.util.concurrent.atomic.AtomicInteger: int getAndDecrement()>":
            case "<java.util.concurrent.atomic.AtomicInteger: int getAndAdd(int)>":
            case "<java.util.concurrent.atomic.AtomicInteger: int incrementAndGet()>":
            case "<java.util.concurrent.atomic.AtomicInteger: int decrementAndGet()>":
            case "<java.util.concurrent.atomic.AtomicInteger: int addAndGet(int)>":
                return "<java.util.concurrent.atomic.AtomicInteger: int value>";
            case "<java.util.concurrent.atomic.AtomicLong: long getAndIncrement()>":
            case "<java.util.concurrent.atomic.AtomicLong: long getAndDecrement()>":
            case "<java.util.concurrent.atomic.AtomicLong: long getAndAdd(long)>":
            case "<java.util.concurrent.atomic.AtomicLong: long incrementAndGet()>":
            case "<java.util.concurrent.atomic.AtomicLong: long decrementAndGet()>":
            case "<java.util.concurrent.atomic.AtomicLong: long addAndGet(long)>":
                return "<java.util.concurrent.atomic.AtomicLong: long value>";
            default:
                return "";
        }
    }

    public int argumentIndex() {
        return argumentIndex;
    }

    public boolean occurrenceScoped() {
        return occurrenceScoped;
    }

    /**
     * True when the replay ordinal is counted inside each concrete
     * invocation of the method that owns the selected mutator.  This avoids
     * turning a long-lived thread root's historical call count into replay
     * identity.
     */
    public boolean definitionInvocationScoped() {
        return DEFINITION_INVOCATION_SCOPE.equals(occurrenceScope);
    }

    public String occurrenceScope() {
        return occurrenceScope;
    }

    public String outputSiteId() {
        return outputSiteId;
    }

    public int outputOccurrence() {
        return outputOccurrence;
    }

    public int replayOccurrence() {
        return replayOccurrence;
    }

    /**
     * Validates the narrow nested-write extension without changing the
     * legacy direct {@code FIELD_WRITE_STATE} wire contract.  The semantic
     * endpoint remains {@code fieldSignature == leafFieldSignature}; the
     * separately declared definition field is used only to select the exact
     * assignment whose stored value owns that leaf.
     */
    private void validateProjectedFieldWrite(JsonObject encoded) {
        boolean hasDefinition = encoded.has("definitionFieldSignature");
        boolean hasLeaf = encoded.has("leafFieldSignature");
        boolean hasPath = encoded.has("fieldPath");
        boolean declaresProjection = hasDefinition || hasLeaf;

        if (!capturesFieldWriteState()) {
            if (declaresProjection) {
                throw new IllegalArgumentException(
                        "field-write projection requires FIELD_WRITE_STATE");
            }
            return;
        }
        // Existing direct captures predate this extension and are still
        // unambiguous because their putfield and semantic leaf are identical.
        if (!declaresProjection) return;
        if (!hasDefinition || !hasLeaf || !hasPath) {
            throw new IllegalArgumentException(
                    "field-write projection requires definition field, "
                            + "leaf field, and complete field path");
        }

        FieldPathSpec.DeclaredField definition =
                FieldPathSpec.declaredField(definitionFieldSignature);
        FieldPathSpec.DeclaredField leaf =
                FieldPathSpec.declaredField(leafFieldSignature);
        if (definition == null || leaf == null || fieldPath.isEmpty()
                || !definition.name().equals(fieldPath.get(0))
                || !leaf.name().equals(fieldPath.get(fieldPath.size() - 1))
                || !leafFieldSignature.equals(fieldSignature)
                || !leafFieldSignature.equals(outputCell)
                || !leaf.type().equals(javaType)) {
            throw new IllegalArgumentException(
                    "inconsistent field-write leaf projection");
        }
        if (definitionFieldSignature.equals(leafFieldSignature)) {
            if (fieldPath.size() != 1) {
                throw new IllegalArgumentException(
                        "direct field-write projection requires one field");
            }
            return;
        }
        if (fieldPath.size() != 2
                || !referenceFieldType(definition.type())
                || !primitiveFieldType(leaf.type())) {
            throw new IllegalArgumentException(
                    "nested field-write projection requires exactly one "
                            + "reference carrier and one primitive leaf");
        }
    }

    private static boolean referenceFieldType(String javaType) {
        String descriptor = javaTypeDescriptor(javaType);
        return descriptor.startsWith("L") && descriptor.endsWith(";");
    }

    private static boolean primitiveFieldType(String javaType) {
        String descriptor = javaTypeDescriptor(javaType);
        return descriptor.length() == 1
                && "ZBCSIJFD".contains(descriptor);
    }

}
