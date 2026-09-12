package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;

/** Stable vocabulary for shared-location replay-scope edges. */
public final class SharedFieldFlow {
    /** Authority for a trace-observed match of receiver and declared leaf. */
    public static final String LOCATION_MATCH_AUTHORITY =
            "RUNTIME_SHARED_LOCATION_MATCH_V1";
    /** Declared owner/name address shared by the two observed accesses. */
    public static final String EDGE_LOCATION = "sharedLocation";
    private SharedFieldFlow() {
    }

    /**
     * Whether one declared container field is carried as one whole state
     * rather than as a reference slot.
     *
     * <p>An associative field keeps the rule it always had, unconditionally:
     * widening the test to it would change which map fields are carried
     * whole, which is not what admitting indexed containers is for.  An
     * indexed field additionally has to be reference-stable, because the
     * lazily allocated, per-instance list is exactly the case a state
     * carrier cannot express.</p>
     */
    public static boolean wholeStateCarrierField(String declaringClass,
                                                 String fieldName,
                                                 String javaType) {
        JavaContainerTypes.Shape shape =
                JavaContainerTypes.wholeStateShape(javaType);
        if (shape == JavaContainerTypes.Shape.ASSOCIATIVE) return true;
        return shape == JavaContainerTypes.Shape.INDEXED
                && referenceStableField(declaringClass, fieldName);
    }

    /**
     * Whether one declared field's REFERENCE cannot change after
     * construction, which is what a whole-state carrier requires of it.
     *
     * <p>A field that is assigned after construction is itself shared state:
     * what changes at that store is WHICH container the field names, and a
     * state carrier cannot say that.  It would publish the states of one
     * container while a reader observes another, and a lazily allocated
     * field is simply null at the access that would select it - there is no
     * container to carry yet.  Such a field's reference is the thing readers
     * share, so the reference carrier is the right one.</p>
     *
     * <p>The declaring class is the authority, so this asks the loaded
     * field.  The aggregation process that decides carriers deliberately
     * keeps the workload's class hierarchy on its classpath, exactly as the
     * recorder had it.  A field that cannot be resolved answers false:
     * keeping the reference carrier it already had is conservative, while
     * carrying a mutable reference whole would lose every writer of it.</p>
     */
    public static boolean referenceStableField(String declaringClass,
                                               String fieldName) {
        if (fieldKey(declaringClass, fieldName).isEmpty()) return false;
        try {
            Class<?> declaring = Class.forName(declaringClass.trim(), false,
                    SharedFieldFlow.class.getClassLoader());
            return java.lang.reflect.Modifier.isFinal(declaring
                    .getDeclaredField(fieldName.trim()).getModifiers());
        } catch (Throwable unresolved) {
            return false;
        }
    }

    /** Joins a declared field across static analysis and runtime selection. */
    public static String fieldKey(String declaringClass, String fieldName) {
        if (declaringClass == null || fieldName == null
                || declaringClass.trim().isEmpty()
                || fieldName.trim().isEmpty()) {
            return "";
        }
        return declaringClass.trim() + "#" + fieldName.trim();
    }

    /** Compiler-owned enum ordinal dispatch storage, not application state. */
    public static boolean compilerSwitchDispatchField(String fieldName) {
        String name = fieldName == null ? "" : fieldName.trim();
        // javac and Eclipse ECJ use these two synthetic-field conventions.
        return name.startsWith("$SwitchMap$")
                || name.startsWith("$SWITCH_TABLE$");
    }

    /** Primitive field updated by a VM-modeled Atomic RMW operation. */
    public static String atomicValueField(
            String carrierDeclaration, String declaredCallee) {
        String method = declaredCallee == null ? "" : declaredCallee.trim();
        String value = "";
        if (method.startsWith("<java.util.concurrent.atomic.AtomicInteger: ")
                && atomicArithmetic(method, "int")) {
            value = "<java.util.concurrent.atomic.AtomicInteger: int value>";
        } else if (method.startsWith(
                "<java.util.concurrent.atomic.AtomicLong: ")
                && atomicArithmetic(method, "long")) {
            value = "<java.util.concurrent.atomic.AtomicLong: long value>";
        }
        FieldPathSpec.DeclaredField carrier =
                FieldPathSpec.declaredField(carrierDeclaration);
        FieldPathSpec.DeclaredField leaf =
                FieldPathSpec.declaredField(value);
        return carrier != null && leaf != null
                && carrier.type().equals(leaf.owner())
                ? leaf.signature() : "";
    }

    private static boolean atomicArithmetic(String method, String type) {
        return method.contains(" getAndIncrement()>")
                || method.contains(" getAndDecrement()>")
                || method.contains(" getAndAdd(" + type + ")>")
                || method.contains(" incrementAndGet()>")
                || method.contains(" decrementAndGet()>")
                || method.contains(" addAndGet(" + type + ")>");
    }
}
