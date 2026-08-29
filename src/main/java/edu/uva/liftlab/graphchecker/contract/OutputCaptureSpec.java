package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** One canonical output endpoint captured by a scheduled execution task. */
public final class OutputCaptureSpec {
    public static final String CALL_ARGUMENT = "CALL_ARGUMENT";
    /** A declared communication effect reached at a normal method return. */
    public static final String COMMUNICATION_EFFECT =
            "COMMUNICATION_EFFECT";
    public static final String MUTATION_STATE = "MUTATION_STATE";
    public static final String FIELD_WRITE_STATE = "FIELD_WRITE_STATE";
    public static final String REGION_EXIT_FIELD = "REGION_EXIT_FIELD";
    /** A structured communication leaf exported by the VM handoff broker: no
     *  Java argument position of its own, so its output boundary is the
     *  successful export of the exact field expression under the exchange,
     *  attempt, direction and leaf path the planned RPC edge states. */
    public static final String HANDOFF_BOUND_LEAF = "HANDOFF_BOUND_LEAF";
    public static final String REGION_ACTIVATION_SCOPE =
            "REGION_ACTIVATION";
    public static final String DEFINITION_INVOCATION_SCOPE =
            "DEFINITION_INVOCATION";
    /** Marks a heap-write demand whose recorded version is an
     *  instance-level historical fact rather than a per-occurrence obligation.
     *
     *  <p>The write site is not loop-body-local to the region's root service
     *  loop (it is reached through a callee, cache-guarded, or executed on a
     *  rare branch), so a once-entered write can never be sampled by every
     *  per-iteration occurrence of a {@code LOOP_BODY_ROOT} region.  A field
     *  belongs to the object, not to the seventh loop iteration: whether the
     *  version was recorded is decided once at instance scope, so an
     *  occurrence that did not observe the write is not incomplete because of
     *  it.  A consumer that reads the value still references a real recorded
     *  version or is refused by name -- the flag never fabricates one.</p> */
    public static final String INSTANCE_SCOPED_PRODUCER =
            "instanceScopedProducer";

    private final String captureBindingId;
    private final String outputPort;
    private final String captureKind;
    private final String outputCell;
    private final String javaType;
    private final String accessRootInputPort;
    private final List<String> fieldPath;
    private final String fieldSignature;
    private final String definitionMethod;
    private final String declaredCallee;
    private final int definitionUnitIndex;
    private final int argumentIndex;
    private final boolean occurrenceScoped;
    private final String occurrenceScope;
    private final boolean instanceScopedProducer;
    private final String outputSiteId;
    private final String leafPath;
    private final String direction;

    static OutputCaptureSpec decodeValidated(JsonObject encoded) {
        return new OutputCaptureSpec(encoded);
    }

    private OutputCaptureSpec(JsonObject encoded) {
        captureBindingId = string(encoded, "captureBindingId");
        outputPort = string(encoded, "outputPort");
        // captureKind is held to the supported set by
        // OutputClosureCodec.validateCaptureLedger, the only path that
        // reaches this constructor: a spec exists only for a binding of a
        // decoded closure, and that ledger refuses every other kind.
        captureKind = string(encoded, "captureKind");
        outputCell = string(encoded, "outputCell");
        javaType = string(encoded, "javaType");
        accessRootInputPort = string(encoded, "accessRootInputPort");
        fieldPath = Collections.unmodifiableList(new ArrayList<>(
                FieldPathSpec.stringArray(encoded, "fieldPath")));
        fieldSignature = string(encoded, "fieldSignature");
        definitionMethod = string(encoded, "definitionMethod");
        declaredCallee = string(encoded, "declaredCallee");
        definitionUnitIndex = encoded.has("definitionUnitIndex")
                ? encoded.get("definitionUnitIndex").getAsInt() : -1;
        argumentIndex = encoded.has("argumentIndex")
                ? encoded.get("argumentIndex").getAsInt() : -1;
        occurrenceScoped = encoded.has("outputSiteId")
                || encoded.has("outputOccurrence");
        occurrenceScope = occurrenceScoped
                ? string(encoded, "occurrenceScope")
                : "";
        outputSiteId = string(encoded, "outputSiteId");
        int outputOccurrence = encoded.has("outputOccurrence")
                ? encoded.get("outputOccurrence").getAsInt() : -1;
        leafPath = string(encoded, "leafPath");
        direction = string(encoded,
                CommunicationCatalogContract.PORT_DIRECTION);
        // The ordinal is recorded provenance, not a replay demand: refusing a
        // recorded ordinal past the replay window would discard an output the
        // recording proves for a reason the relation never asserted.
        if (occurrenceScoped && (outputSiteId.isEmpty()
                || outputOccurrence < 1)) {
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
        instanceScopedProducer = encoded.has(INSTANCE_SCOPED_PRODUCER)
                && encoded.get(INSTANCE_SCOPED_PRODUCER).getAsBoolean();
        if (instanceScopedProducer && !capturesExactHeapWrite()) {
            throw new IllegalArgumentException(
                    "instance-scoped producer requires an exact heap-write "
                            + "capture");
        }
    }

    public String captureBindingId() { return captureBindingId; }

    public String outputPort() { return outputPort; }

    public boolean capturesCallArgument() {
        return CALL_ARGUMENT.equals(captureKind);
    }

    /** Records a communication event; its value is carried only by the VM. */
    public boolean capturesCommunicationEffect() {
        return COMMUNICATION_EFFECT.equals(captureKind);
    }

    /** Selects one exact mutator occurrence and captures its receiver when
     *  the enclosing mutation method completes normally. */
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

    /** The owner field snapshot observed only when the region exits. */
    public boolean capturesRegionExitField() {
        return REGION_EXIT_FIELD.equals(captureKind);
    }

    /** Captures one exact field expression at a successful RPC export. */
    public boolean capturesHandoffBoundLeaf() {
        return HANDOFF_BOUND_LEAF.equals(captureKind);
    }

    public String leafPath() { return leafPath; }

    public String direction() { return direction; }

    public String accessRootInputPort() { return accessRootInputPort; }

    public List<String> fieldPath() { return fieldPath; }

    public String fieldSignature() { return fieldSignature; }

    public String definitionMethod() { return definitionMethod; }

    public int definitionUnitIndex() { return definitionUnitIndex; }

    public String declaredCallee() { return declaredCallee; }

    /** Exact primitive state updated by the arithmetic Atomic RMW summaries;
     *  deliberately only the surface the custom VM implements, so
     *  compare-and-set and functional update stay on their concrete path. */
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

    public int argumentIndex() { return argumentIndex; }

    public boolean occurrenceScoped() { return occurrenceScoped; }

    /** True when this heap-write demand's recorded version is an
     *  instance-level fact, so an occurrence that did not observe the write is
     *  not incomplete because of it (see {@link #INSTANCE_SCOPED_PRODUCER}). */
    public boolean instanceScopedProducer() { return instanceScopedProducer; }

    /** True when the replay ordinal is counted inside each concrete
     *  invocation of the method owning the selected mutator, so a long-lived
     *  root's historical call count never becomes replay identity. */
    public boolean definitionInvocationScoped() {
        return DEFINITION_INVOCATION_SCOPE.equals(occurrenceScope);
    }

    public String outputSiteId() { return outputSiteId; }

}
