package edu.uva.liftlab.graphchecker.plan;

/** Stable vocabulary for shared-location replay-scope edges. */
public final class SharedFieldFlow {
    private SharedFieldFlow() {
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
