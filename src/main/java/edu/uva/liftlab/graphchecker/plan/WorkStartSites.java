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
 * THE list of call shapes that start work, for the weave and for the runtime.
 *
 * <p>A work start is where one activation hands work to another thread: a
 * {@code Thread.start}, an executor submission, a fork-join {@code fork}.
 * Two things read this list and they must read the same one: the INSTRUMENT
 * weave, which files the start-site frame of the work that was started
 * (IDENTITY-V3 SS1, {@code CausynthPipeline.instrumentWorkStarts}), and the
 * recording's own call hooks, which carry the request scope across the same
 * boundary ({@code RuntimeTraceContext.captureAsync}).  They used to carry
 * one list each -- the weave's was narrower, so a start the recorder saw had
 * no frame -- and a start only one of them recognizes is a lineage hole by
 * construction.</p>
 *
 * <p>The list is names, arities and types; each reader evaluates it with the
 * types it can see.  The weave asks Soot about declared types; the recorder
 * asks the live object.  Neither adds a shape of its own.</p>
 */
public final class WorkStartSites {
    private WorkStartSites() {
    }

    /**
     * Whether a type is, or inherits, the named one.
     *
     * <p>Soot answers it over the class hierarchy of a declared type; the
     * runtime answers it with {@code isInstance} on the value itself.</p>
     */
    public interface Types {
        boolean is(String typeName);
    }

    /**
     * The receiver-carried starts: a no-argument call whose RECEIVER is the
     * work.  {@code Thread.start} starts its thread, and a fork-join {@code
     * fork}/{@code invoke} starts its task -- a pool worker that steals such
     * a task inherits nothing from the submission that created the worker.
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

    /**
     * The argument-carried starts: a submission whose ARGUMENTS are the work.
     *
     * <p>Every argument, not only the first: {@code ForkJoinTask.invokeAll(t1,
     * t2)} submits two tasks as two arguments, and each of them is a start
     * of its own -- which is the only thing that tells the two activations
     * apart.</p>
     */
    private static final Set<String> SUBMISSION_NAMES =
            names("execute", "submit", "schedule", "invokeAll");

    /**
     * What can BE the work a submission starts.
     *
     * <p>A {@code Collection} is one submission per element (a batch), which
     * is why it belongs here rather than in the readers.</p>
     */
    private static final List<String> WORK_TYPES = Arrays.asList(
            "java.lang.Runnable",
            "java.util.concurrent.Callable",
            "java.util.concurrent.ForkJoinTask",
            "java.util.Collection");

    /** The classes the runtime projection answers {@link Types} with. */
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

    /**
     * Whether this call starts the work its receiver carries.
     *
     * @param calleeName   the callee's own name, no signature
     * @param argumentCount how many arguments the call passes
     * @param receiverType the receiver's type, as the caller can see it
     */
    public static boolean startsReceiver(String calleeName, int argumentCount,
                                         Types receiverType) {
        if (argumentCount != 0 || calleeName == null
                || receiverType == null) {
            return false;
        }
        for (Map.Entry<String, Set<String>> shape
                : RECEIVER_STARTS.entrySet()) {
            if (shape.getValue().contains(calleeName)
                    && receiverType.is(shape.getKey())) {
                return true;
            }
        }
        return false;
    }

    /** Whether this call submits the work its arguments carry. */
    public static boolean submitsArguments(String calleeName,
                                           int argumentCount) {
        return argumentCount >= 1 && calleeName != null
                && SUBMISSION_NAMES.contains(calleeName);
    }

    /** Whether a value of this type can be the work a submission starts. */
    public static boolean carriesWork(Types type) {
        if (type == null) return false;
        for (String work : WORK_TYPES) {
            if (type.is(work)) return true;
        }
        return false;
    }

    /**
     * The methods a started work RUNS: this list, read from the other side.
     *
     * <p>A start is filed under the object that carries the work
     * ({@code Identity.startWork}), and the thread that runs it never sees
     * that object through any hook of its own -- a pool worker is handed a
     * task by {@code ThreadPoolExecutor}, which is JDK code no weave
     * touches.  So the work claims its own start frame at its own first
     * instruction: the entry of the functional method the start named.  The
     * shapes are the mirror of {@link #RECEIVER_STARTS} and
     * {@link #WORK_TYPES} -- {@code Runnable.run}, {@code Callable.call},
     * a fork-join {@code exec}/{@code compute}, {@code Thread.run} -- and
     * nothing else, so a work shape only one of the two sides recognizes
     * is impossible by construction.</p>
     */
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

    /**
     * Whether this method is the entry of work a start hands to a thread.
     *
     * <p>Zero-argument and instance-bound, because that is what every shape
     * above is: the work is the receiver, so {@code this} is the carrier the
     * start was filed under and the claim needs no argument of its own.</p>
     *
     * @param methodName     the method's own name, no signature
     * @param argumentCount  how many arguments it declares
     * @param declaringType  the declaring class, as the reader can see it
     */
    public static boolean entersWork(String methodName, int argumentCount,
                                     Types declaringType) {
        if (argumentCount != 0 || methodName == null
                || declaringType == null) {
            return false;
        }
        for (Map.Entry<String, Set<String>> shape
                : WORK_ENTRIES.entrySet()) {
            if (shape.getValue().contains(methodName)
                    && declaringType.is(shape.getKey())) {
                return true;
            }
        }
        return false;
    }

    // ---- queue handoffs --------------------------------------------------

    /** The queue a handoff goes through: a producer puts, a consumer takes. */
    private static final String QUEUE_TYPE =
            "java.util.concurrent.BlockingQueue";

    /**
     * The submissions of a queue handoff: the ELEMENT is the work.
     *
     * <p>Any element, not only a {@code Runnable}: what a producer puts on a
     * queue -- an IPC {@code Call}, a command array, a lambda -- is the work
     * the consumer that takes it runs, and the consumer never sees the
     * producer through a hook of its own.  The receiver's type is checked,
     * because {@code put} and {@code add} are the names of a map's and a
     * list's writes too.</p>
     */
    private static final Set<String> QUEUE_SUBMISSIONS =
            names("put", "offer", "add", "putFirst", "putLast", "offerFirst",
                    "offerLast", "addFirst", "addLast");

    /**
     * The claims of a queue handoff: what the call RETURNS is the work.
     *
     * <p>A deque's ends are handoffs too: the DataNode actor puts a
     * KeyUpdateCommand at the head of its command queue ({@code putFirst})
     * and its command processor takes it, and a list without the ends left
     * that key delivery with no cause.</p>
     */
    private static final Set<String> QUEUE_CLAIMS = names("take", "poll",
            "takeFirst", "takeLast", "pollFirst", "pollLast");

    /** Whether this call hands its first argument to a queue's consumer. */
    public static boolean submitsToQueue(String calleeName, int argumentCount,
                                         Types receiverType) {
        return argumentCount >= 1 && calleeName != null
                && receiverType != null
                && QUEUE_SUBMISSIONS.contains(calleeName)
                && receiverType.is(QUEUE_TYPE);
    }

    /** Whether the value this call returns is work a producer handed over. */
    public static boolean claimsFromQueue(String calleeName,
                                          Types receiverType) {
        return calleeName != null && receiverType != null
                && QUEUE_CLAIMS.contains(calleeName)
                && receiverType.is(QUEUE_TYPE);
    }

    // ---- the lineage scan ------------------------------------------------

    /**
     * Whether a call, read off bytecode with no class hierarchy, may be a
     * work start or a queue handoff: the names above, the receiver-carried
     * starts with no argument, the submissions with one, and a queue's by a
     * {@code java.util.concurrent} owner.  It errs wide on purpose -- a class
     * it keeps is only handed to the weave, which asks the exact shapes of
     * {@link #startsReceiver}, {@link #submitsArguments}, {@link
     * #submitsToQueue} and {@link #claimsFromQueue} with the hierarchy in
     * hand; a class it drops is a lineage hole ({@code LineageScan}).
     */
    public static boolean mayHandOffWork(String ownerInternalName,
                                         String calleeName,
                                         int argumentCount) {
        if (calleeName == null) return false;
        if (argumentCount == 0) {
            for (Set<String> starts : RECEIVER_STARTS.values()) {
                if (starts.contains(calleeName)) return true;
            }
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

    /**
     * Whether a method, read off bytecode, may be the entry of started work:
     * a no-argument method named as one of {@link #WORK_ENTRIES}' entries.
     * Wide for the same reason as {@link #mayHandOffWork}.
     */
    public static boolean mayEnterWork(String methodName, int argumentCount) {
        if (argumentCount != 0 || methodName == null) return false;
        for (Set<String> entries : WORK_ENTRIES.values()) {
            if (entries.contains(methodName)) return true;
        }
        return false;
    }

    // ---- timed waits -----------------------------------------------------

    /**
     * One timed-wait shape: the call a service loop waits with, and the
     * method of {@code runtime.TimedWaits} that stands in for it.
     *
     * <p>The WAKE of the schedule: a timed wait that returns hands its thread
     * the loop's next turn.  The weave replaces the call -- the receiver, when
     * there is one, becomes the first argument and the call site the last --
     * because under a schedule prefix the wait must not read the wall clock
     * at all, and a hook placed around the call could not stop it doing
     * so.</p>
     *
     * <p>The same list names the notifiers of those primitives and their
     * untimed waits, replaced the same way: a held wait leaves the wait set
     * between two asks for its turn, so a signal must be state the wait can
     * read afterwards, which only a replaced notifier can write.</p>
     */
    public static final class TimedWait {
        /** The type the callee is declared on, or that the receiver is. */
        public final String owner;
        public final String name;
        public final List<String> parameters;
        public final boolean isStatic;
        /** The {@code TimedWaits} method, and what it returns. */
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

        /**
         * The replacement's parameters: the receiver's declared shape type
         * first when the call has one, then the call's own, then the site.
         */
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

    /** The owner of every replacement. */
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
            // A signal is state (TimedWaits): the notifiers of the same
            // primitives, and their untimed waits, so a held wait -- out of
            // the wait set between two asks for its turn -- still reads a
            // signal sent in that gap.  None of these is an event.
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

    /**
     * The timed-wait shape this call is, or null.
     *
     * @param calleeName     the callee's own name
     * @param parameterTypes the callee's declared parameter types, by name
     * @param isStatic       whether the call is a static invocation
     * @param declaringType  the type the call's reference is declared on
     */
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

    /**
     * Whether a call, read off bytecode, may be one of {@link #TIMED_WAITS}:
     * its name alone, since a wait or a notify on an application object is
     * owned by that object's class.  Wide for the reason {@link
     * #mayHandOffWork} is; the weave asks {@link #timedWait}.
     */
    public static boolean mayWait(String calleeName) {
        if (calleeName == null) return false;
        for (TimedWait shape : TIMED_WAITS) {
            if (shape.name.equals(calleeName)) return true;
        }
        return false;
    }

    /** Every timed-wait shape, for the runtime ABI check. */
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

    /**
     * The callee's name in a Soot method signature, or {@code ""}.
     *
     * <p>{@code <java.util.concurrent.ThreadPoolExecutor: void
     * execute(java.lang.Runnable)>} names {@code execute}.  The recorder
     * holds its callees as these signatures, so the parse lives with the
     * list rather than in the recorder.</p>
     */
    public static String calleeName(String declaredCallee) {
        String signature = declaredCallee == null ? "" : declaredCallee;
        int open = signature.indexOf('(');
        if (open < 0) return "";
        int space = signature.lastIndexOf(' ', open);
        if (space < 0 || space + 1 >= open) return "";
        return signature.substring(space + 1, open);
    }

    /** How many arguments the callee of a Soot method signature takes. */
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
