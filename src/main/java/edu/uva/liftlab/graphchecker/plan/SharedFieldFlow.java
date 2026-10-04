package edu.uva.liftlab.graphchecker.plan;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/** Stable vocabulary for shared-location replay-scope edges. */
public final class SharedFieldFlow {
    /**
     * How the replay versions a field (SYMBOL-SCOPE F2): by the {@code
     * VALUE} it holds -- an integral primitive or its wrapper --, as a
     * {@code REFERENCE} a store re-points, whose referent a reader then
     * queries or projects, or, for a {@code CONTAINER} only its class's
     * construction stores, by the state of the container it holds, which is
     * mutated in place; {@code NONE} is no tracked cell.
     */
    public enum TrackedKind {
        VALUE, REFERENCE, CONTAINER, NONE
    }

    /** Each JDK atomic, with the one field every call of it reads or
     *  writes. */
    private static final Map<String, String> ATOMIC_VALUES =
            new LinkedHashMap<>();
    /** The atomics' writes: a store, a CAS or a read-modify-write of the
     *  value, whatever the atomic ({@code updateAndGet} runs its lambda,
     *  and the CAS publishes the result). */
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

    /** javac/ECJ synthetic enum switch-map field, not application state. */
    public static boolean compilerSwitchDispatchField(String fieldName) {
        String name = fieldName == null ? "" : fieldName.trim();
        return name.startsWith("$SwitchMap$")
                || name.startsWith("$SWITCH_TABLE$");
    }

    /** Whether a call writes its atomic's value. */
    public static boolean atomicWrite(String method) {
        String[] call = atomicCall(method);
        return call != null && ATOMIC_WRITES.contains(call[1]);
    }

    /**
     * The value an atomic's {@code get()} returns, or "": the field it
     * reads -- {@code AtomicReference.get()} is {@code value}, {@code
     * AtomicBoolean.get()} is {@code value != 0} -- a table, since the JDK
     * body need not be loaded to be read.
     */
    public static String atomicRead(String method) {
        String[] call = atomicCall(method);
        return call != null && "get".equals(call[1]) && call[2].isEmpty()
                ? ATOMIC_VALUES.get(call[0]) : "";
    }

    /** The value field an atomic's write stores into, when the carrier
     *  holds that atomic; else "". */
    public static String atomicValueField(
            String carrierDeclaration, String declaredCallee) {
        String[] call = atomicCall(declaredCallee);
        FieldPathSpec.DeclaredField carrier =
                FieldPathSpec.declaredField(carrierDeclaration);
        return call != null && ATOMIC_WRITES.contains(call[1])
                && carrier != null && carrier.type().equals(call[0])
                ? ATOMIC_VALUES.get(call[0]) : "";
    }

    /** {owner, name, parameters} of a call on a JDK atomic, or null. */
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
