package edu.uva.liftlab.graphchecker.plan;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ForkJoinTask;

/**
 * THE list of call shapes that start work, hand it off, or wait.
 *
 * <p>Read by both the INSTRUMENT weave (IDENTITY-V3 SS1, {@code
 * CausynthPipeline.instrumentWorkStarts}) and the recorder's hooks ({@code
 * RuntimeTraceContext.captureAsync}); a shape only one of them recognizes is a
 * lineage hole. Each evaluates it with the {@link Types} it can see (Soot
 * hierarchy or the live object) and adds none of its own.</p>
 */
public final class WorkStartSites {
    private WorkStartSites() {
    }

    /** Whether a type is, or inherits, the named one (Soot hierarchy or {@code
     *  isInstance}). */
    public interface Types {
        boolean is(String typeName);
    }

    /** Receiver-carried starts: a no-argument call whose receiver is the work.
     */
    private static final Map<String, Set<String>> RECEIVER_STARTS =
            receiverStarts();

    private static Map<String, Set<String>> receiverStarts() {
        Map<String, Set<String>> starts = new LinkedHashMap<>();
        starts.put("java.lang.Thread", names("start"));
        starts.put("java.util.concurrent.ForkJoinTask",
                names("fork", "invoke"));
        return starts;
    }

    /** Argument-carried starts: each argument is a start of its own ({@code
     *  invokeAll(t1, t2)}). */
    private static final Set<String> SUBMISSION_NAMES =
            names("execute", "submit", "schedule", "invokeAll");

    /** What can be the work a submission starts; a {@code Collection} is a
     *  batch. */
    private static final List<String> WORK_TYPES = Arrays.asList(
            "java.lang.Runnable",
            "java.util.concurrent.Callable",
            "java.util.concurrent.ForkJoinTask",
            "java.util.Collection");

    private static final Map<String, Class<?>> RUNTIME_TYPES = runtimeTypes();

    private static Map<String, Class<?>> runtimeTypes() {
        Map<String, Class<?>> types = new LinkedHashMap<>();
        types.put("java.lang.Thread", Thread.class);
        types.put("java.util.concurrent.ForkJoinTask", ForkJoinTask.class);
        types.put("java.lang.Runnable", Runnable.class);
        types.put("java.util.concurrent.Callable", Callable.class);
        types.put("java.util.Collection", Collection.class);
        types.put(QUEUE_TYPE, java.util.concurrent.BlockingQueue.class);
        return types;
    }

    private static Set<String> names(String... values) {
        return new LinkedHashSet<>(Arrays.asList(values));
    }

    /** Whether this call starts the work its receiver carries (as the caller
     *  sees its type). */
    public static boolean startsReceiver(String calleeName, int argumentCount,
                                         Types receiverType) {
        return argumentCount == 0 && shaped(RECEIVER_STARTS, calleeName,
                receiverType);
    }

    /** Whether some shape names {@code name} on a type {@code type} is. */
    private static boolean shaped(Map<String, Set<String>> shapes,
                                  String name, Types type) {
        if (name == null || type == null) return false;
        for (Map.Entry<String, Set<String>> shape : shapes.entrySet()) {
            if (shape.getValue().contains(name) && type.is(shape.getKey())) {
                return true;
            }
        }
        return false;
    }

    /** Whether some shape names {@code name}, whatever the type. */
    private static boolean named(Map<String, Set<String>> shapes,
                                 String name) {
        for (Set<String> names : shapes.values()) {
            if (names.contains(name)) return true;
        }
        return false;
    }

    public static boolean submitsArguments(String calleeName,
                                           int argumentCount) {
        return argumentCount >= 1 && calleeName != null
                && SUBMISSION_NAMES.contains(calleeName);
    }

    public static boolean carriesWork(Types type) {
        if (type == null) return false;
        for (String work : WORK_TYPES) {
            if (type.is(work)) return true;
        }
        return false;
    }

    /** The methods started work RUNS: the mirror of {@link #RECEIVER_STARTS}
     *  and {@link #WORK_TYPES}. The running thread never sees the start's
     *  carrier (a pool worker gets it from JDK code), so the work claims its
     *  start frame at the entry of its functional method. */
    private static final Map<String, Set<String>> WORK_ENTRIES =
            workEntries();

    private static Map<String, Set<String>> workEntries() {
        Map<String, Set<String>> entries = new LinkedHashMap<>();
        entries.put("java.lang.Runnable", names("run"));
        entries.put("java.util.concurrent.Callable", names("call"));
        entries.put("java.util.concurrent.ForkJoinTask",
                names("exec", "compute"));
        entries.put("java.lang.Thread", names("run"));
        return entries;
    }

    /** Whether this method is the entry of started work: zero-argument,
     *  instance-bound ({@code this} is the carrier). */
    public static boolean entersWork(String methodName, int argumentCount,
                                     Types declaringType) {
        return argumentCount == 0 && shaped(WORK_ENTRIES, methodName,
                declaringType);
    }


    private static final String QUEUE_TYPE =
            "java.util.concurrent.BlockingQueue";

    /** Queue submissions: the ELEMENT is the work; receiver type checked
     *  ({@code put}/{@code add} are map/list writes too). */
    private static final Set<String> QUEUE_SUBMISSIONS =
            names("put", "offer", "add", "putFirst", "putLast", "offerFirst",
                    "offerLast", "addFirst", "addLast");

    /** Queue claims: the returned value is the work; deque ends count too. */
    private static final Set<String> QUEUE_CLAIMS = names("take", "poll",
            "takeFirst", "takeLast", "pollFirst", "pollLast");

    public static boolean submitsToQueue(String calleeName, int argumentCount,
                                         Types receiverType) {
        return argumentCount >= 1 && calleeName != null
                && receiverType != null
                && QUEUE_SUBMISSIONS.contains(calleeName)
                && receiverType.is(QUEUE_TYPE);
    }

    public static boolean claimsFromQueue(String calleeName,
                                          Types receiverType) {
        return calleeName != null && receiverType != null
                && QUEUE_CLAIMS.contains(calleeName)
                && receiverType.is(QUEUE_TYPE);
    }


    /** Whether a call, read off bytecode without a hierarchy, may be a start or
     *  queue handoff. Deliberately wide: a kept class only goes to the weave,
     *  which asks the exact shapes; a dropped class is a lineage hole ({@code
     *  LineageScan}). */
    public static boolean mayHandOffWork(String ownerInternalName,
                                         String calleeName,
                                         int argumentCount) {
        if (calleeName == null) return false;
        if (argumentCount == 0 && named(RECEIVER_STARTS, calleeName)) {
            return true;
        }
        if (argumentCount >= 1 && SUBMISSION_NAMES.contains(calleeName)) {
            return true;
        }
        boolean concurrent = ownerInternalName != null
                && ownerInternalName.startsWith("java/util/concurrent/");
        return concurrent && (QUEUE_CLAIMS.contains(calleeName)
                || (argumentCount >= 1
                        && QUEUE_SUBMISSIONS.contains(calleeName)));
    }

    /** Bytecode-level {@link #WORK_ENTRIES} test, wide like {@link
     *  #mayHandOffWork}. */
    public static boolean mayEnterWork(String methodName, int argumentCount) {
        return argumentCount == 0 && methodName != null
                && named(WORK_ENTRIES, methodName);
    }


    /**
     * One wait shape and the {@code runtime.TimedWaits} method that replaces
     * it.
     *
     * <p>Timed waits are the schedule's WAKE. The weave replaces the call
     * (receiver first, call site last) because under a schedule prefix the wait
     * must not read the wall clock, which a surrounding hook could not stop.
     * Notifiers and untimed waits are replaced too: a held wait is out of the
     * wait set between turns, so a signal must be state it can read later.</p>
     */
    public static final class TimedWait {
        public final String owner;
        public final String name;
        public final List<String> parameters;
        public final boolean isStatic;
        public final String replacement;
        public final String returns;

        private TimedWait(String owner, String name, boolean isStatic,
                          String returns, String replacement,
                          String... parameters) {
            this.owner = owner;
            this.name = name;
            this.isStatic = isStatic;
            this.returns = returns;
            this.replacement = replacement;
            this.parameters = java.util.Collections.unmodifiableList(
                    Arrays.asList(parameters));
        }

        /** Replacement parameters: receiver type (if any), the call's own, then
         *  the site. */
        public List<String> replacementParameters() {
            List<String> all = new java.util.ArrayList<>();
            if (!isStatic) all.add(owner);
            all.addAll(parameters);
            all.add("java.lang.String");
            return all;
        }
    }

    private static final String CONDITION_TYPE =
            "java.util.concurrent.locks.Condition";

    public static final String TIMED_WAITS_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.TimedWaits";

    private static final List<TimedWait> TIMED_WAITS = Arrays.asList(
            new TimedWait("java.lang.Thread", "sleep", true, "void",
                    "sleep", "long"),
            new TimedWait("java.lang.Thread", "sleep", true, "void",
                    "sleep", "long", "int"),
            new TimedWait("java.util.concurrent.TimeUnit", "sleep", false,
                    "void", "sleep", "long"),
            new TimedWait("java.lang.Object", "wait", false, "void",
                    "waitOn", "long"),
            new TimedWait("java.lang.Object", "wait", false, "void",
                    "waitOn", "long", "int"),
            new TimedWait("java.util.concurrent.locks.LockSupport",
                    "parkNanos", true, "void", "parkNanos", "long"),
            new TimedWait("java.util.concurrent.locks.LockSupport",
                    "parkNanos", true, "void", "parkNanos",
                    "java.lang.Object", "long"),
            new TimedWait(CONDITION_TYPE, "awaitNanos", false, "long",
                    "awaitNanos", "long"),
            new TimedWait(CONDITION_TYPE, "await", false, "boolean", "await",
                    "long", "java.util.concurrent.TimeUnit"),
            new TimedWait(QUEUE_TYPE, "poll", false, "java.lang.Object",
                    "poll", "long", "java.util.concurrent.TimeUnit"),
            // Signals as state (see TimedWait): notifiers and untimed waits;
            // not events.
            new TimedWait("java.lang.Object", "wait", false, "void",
                    "waitOn"),
            new TimedWait("java.lang.Object", "notify", false, "void",
                    "notifyOn"),
            new TimedWait("java.lang.Object", "notifyAll", false, "void",
                    "notifyAllOn"),
            new TimedWait(CONDITION_TYPE, "await", false, "void", "await"),
            new TimedWait(CONDITION_TYPE, "awaitUninterruptibly", false,
                    "void", "awaitUninterruptibly"),
            new TimedWait(CONDITION_TYPE, "signal", false, "void", "signal"),
            new TimedWait(CONDITION_TYPE, "signalAll", false, "void",
                    "signalAll"));

    /** The timed-wait shape of this call (declared parameter types,
     *  static-ness, reference type), or null. */
    public static TimedWait timedWait(String calleeName,
                                      List<String> parameterTypes,
                                      boolean isStatic, Types declaringType) {
        if (calleeName == null || parameterTypes == null
                || declaringType == null) {
            return null;
        }
        for (TimedWait shape : TIMED_WAITS) {
            if (shape.isStatic == isStatic && shape.name.equals(calleeName)
                    && shape.parameters.equals(parameterTypes)
                    && declaringType.is(shape.owner)) {
                return shape;
            }
        }
        return null;
    }

    /** Bytecode-level {@link #TIMED_WAITS} test by name; wide like {@link
     *  #mayHandOffWork}. */
    public static boolean mayWait(String calleeName) {
        if (calleeName == null) return false;
        for (TimedWait shape : TIMED_WAITS) {
            if (shape.name.equals(calleeName)) return true;
        }
        return false;
    }

    public static List<TimedWait> timedWaits() {
        return TIMED_WAITS;
    }

    /** The runtime projection of {@link Types}: the value's own class. */
    public static Types typesOf(final Object value) {
        return new Types() {
            @Override
            public boolean is(String typeName) {
                Class<?> type = RUNTIME_TYPES.get(typeName);
                return type != null && type.isInstance(value);
            }
        };
    }

    /** The callee's name in a Soot method signature, or {@code ""}. */
    public static String calleeName(String declaredCallee) {
        String signature = declaredCallee == null ? "" : declaredCallee;
        int open = signature.indexOf('(');
        if (open < 0) return "";
        int space = signature.lastIndexOf(' ', open);
        if (space < 0 || space + 1 >= open) return "";
        return signature.substring(space + 1, open);
    }

    public static int argumentCount(String declaredCallee) {
        String signature = declaredCallee == null ? "" : declaredCallee;
        int open = signature.indexOf('(');
        int close = signature.lastIndexOf(')');
        if (open < 0 || close <= open) return -1;
        String arguments = signature.substring(open + 1, close).trim();
        if (arguments.isEmpty()) return 0;
        int count = 1;
        for (int index = 0; index < arguments.length(); index++) {
            if (arguments.charAt(index) == ',') count++;
        }
        return count;
    }
}
