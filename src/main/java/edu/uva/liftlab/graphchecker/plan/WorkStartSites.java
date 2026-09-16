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
