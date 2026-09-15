package edu.uva.liftlab.graphchecker.d3.plan;

import edu.uva.liftlab.graphchecker.d3.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.d3.smt.JavaContainerTypes;

/** Stable vocabulary for shared-location replay-scope edges. */
public final class SharedFieldFlow {
    /** Authority for a trace-observed match of receiver and declared leaf. */
    public static final String LOCATION_MATCH_AUTHORITY =
            "RUNTIME_SHARED_LOCATION_MATCH_V1";
    /** Declared owner/name address shared by the two observed accesses. */
    public static final String EDGE_LOCATION = "sharedLocation";
    private SharedFieldFlow() {
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
