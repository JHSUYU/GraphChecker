package edu.uva.liftlab.graphchecker.plan;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

public final class SharedFieldFlow {
    public enum TrackedKind {
        VALUE, REFERENCE, CONTAINER, NONE
    }

    private static final Map<String, String> ATOMIC_VALUES =
            new LinkedHashMap<>();
    private static final Set<String> ATOMIC_WRITES =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "set", "lazySet", "getAndSet", "compareAndSet",
                    "weakCompareAndSet", "updateAndGet", "getAndUpdate",
                    "accumulateAndGet", "getAndAccumulate",
                    "getAndIncrement", "getAndDecrement", "getAndAdd",
                    "incrementAndGet", "decrementAndGet", "addAndGet")));

    static {
        String atomic = "java.util.concurrent.atomic.";
        ATOMIC_VALUES.put(atomic + "AtomicInteger",
                "<" + atomic + "AtomicInteger: int value>");
        ATOMIC_VALUES.put(atomic + "AtomicLong",
                "<" + atomic + "AtomicLong: long value>");
        ATOMIC_VALUES.put(atomic + "AtomicBoolean",
                "<" + atomic + "AtomicBoolean: int value>");
        ATOMIC_VALUES.put(atomic + "AtomicReference",
                "<" + atomic + "AtomicReference: java.lang.Object value>");
    }

    private SharedFieldFlow() {
    }

    public static boolean compilerSwitchDispatchField(String fieldName) {
        String name = fieldName == null ? "" : fieldName.trim();
        return name.startsWith("$SwitchMap$")
                || name.startsWith("$SWITCH_TABLE$");
    }

    public static boolean atomicWrite(String method) {
        String[] call = atomicCall(method);
        return call != null && ATOMIC_WRITES.contains(call[1]);
    }

    public static String atomicRead(String method) {
        String[] call = atomicCall(method);
        return call != null && "get".equals(call[1]) && call[2].isEmpty()
                ? ATOMIC_VALUES.get(call[0]) : "";
    }

    public static String atomicValueField(
            String carrierDeclaration, String declaredCallee) {
        String[] call = atomicCall(declaredCallee);
        FieldPathSpec.DeclaredField carrier =
                FieldPathSpec.declaredField(carrierDeclaration);
        return call != null && ATOMIC_WRITES.contains(call[1])
                && carrier != null && carrier.type().equals(call[0])
                ? ATOMIC_VALUES.get(call[0]) : "";
    }

    private static String[] atomicCall(String method) {
        String value = method == null ? "" : method.trim();
        int colon = value.indexOf(':');
        int open = value.indexOf('(');
        int close = value.lastIndexOf(')');
        if (!value.startsWith("<") || colon < 0 || open < colon
                || close < open) {
            return null;
        }
        String owner = value.substring(1, colon).trim();
        if (!ATOMIC_VALUES.containsKey(owner)) return null;
        String head = value.substring(colon + 1, open).trim();
        return new String[]{owner, head.substring(head.lastIndexOf(' ') + 1),
                value.substring(open + 1, close).trim()};
    }
}
