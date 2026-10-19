package edu.uva.liftlab.graphchecker.plan;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class WorkStartSites {
    private WorkStartSites() {
    }

    public static final Set<String> RANDOM_RECEIVERS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "java.util.Random",
                    "java.util.concurrent.ThreadLocalRandom",
                    "java.security.SecureRandom")));

    public static final Set<String> RANDOM_DRAWS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "nextInt()I", "nextInt(I)I", "nextLong()J",
                    "nextDouble()D", "nextBoolean()Z", "nextFloat()F",
                    "nextGaussian()D", "nextBytes([B)V",
                    "ints()Ljava/util/stream/IntStream;",
                    "ints(J)Ljava/util/stream/IntStream;",
                    "ints(II)Ljava/util/stream/IntStream;",
                    "ints(JII)Ljava/util/stream/IntStream;",
                    "longs()Ljava/util/stream/LongStream;",
                    "longs(J)Ljava/util/stream/LongStream;",
                    "longs(JJ)Ljava/util/stream/LongStream;",
                    "longs(JJJ)Ljava/util/stream/LongStream;",
                    "doubles()Ljava/util/stream/DoubleStream;",
                    "doubles(J)Ljava/util/stream/DoubleStream;",
                    "doubles(DD)Ljava/util/stream/DoubleStream;",
                    "doubles(JDD)Ljava/util/stream/DoubleStream;")));

    public static final Set<String> BOUNDED_DRAWS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "nextInt(II)I", "nextLong(J)J", "nextLong(JJ)J",
                    "nextDouble(D)D", "nextDouble(DD)D")));

    public static final Set<String> STATIC_DRAWS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "java/lang/Math.random()D",
                    "java/util/Collections.shuffle(Ljava/util/List;)V",
                    "java/util/UUID.randomUUID()Ljava/util/UUID;")));

    public static final Set<String> LISTINGS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "list()[Ljava/lang/String;",
                    "list(Ljava/io/FilenameFilter;)[Ljava/lang/String;",
                    "listFiles()[Ljava/io/File;",
                    "listFiles(Ljava/io/FileFilter;)[Ljava/io/File;",
                    "listFiles(Ljava/io/FilenameFilter;)[Ljava/io/File;")));

    public static boolean lists(String owner, String name, String descriptor) {
        return "java/io/File".equals(owner)
                && LISTINGS.contains(name + descriptor);
    }

    public static boolean drawn(String nameAndDescriptor) {
        return RANDOM_DRAWS.contains(nameAndDescriptor)
                || BOUNDED_DRAWS.contains(nameAndDescriptor);
    }

    public static boolean draws(String owner, String name, String descriptor) {
        return RANDOM_RECEIVERS.contains(owner.replace('/', '.'))
                && drawn(name + descriptor)
                || STATIC_DRAWS.contains(owner + "." + name + descriptor)
                || handsRandomOut(owner, descriptor);
    }

    public static boolean handsRandomOut(String owner, String descriptor) {
        return (owner.startsWith("java/") || owner.startsWith("javax/"))
                && descriptor.substring(0, descriptor.indexOf(')'))
                        .contains("Ljava/util/Random;");
    }

    public interface Types {
        boolean is(String typeName);
    }

    private static final Map<String, Set<String>> RECEIVER_STARTS =
            receiverStarts();

    private static Map<String, Set<String>> receiverStarts() {
        Map<String, Set<String>> starts = new LinkedHashMap<>();
        starts.put("java.lang.Thread", names("start"));
        starts.put("java.util.concurrent.ForkJoinTask",
                names("fork", "invoke"));
        return starts;
    }

    private static final Set<String> SUBMISSION_NAMES =
            names("execute", "submit", "schedule", "invokeAll", "newTimeout");

    public static final String TIMER_TASK = "*.netty.util.TimerTask";

    private static final List<String> WORK_TYPES = Arrays.asList(
            "java.lang.Runnable",
            "java.util.concurrent.Callable",
            "java.util.concurrent.ForkJoinTask",
            "java.util.Collection",
            TIMER_TASK);

    private static Set<String> names(String... values) {
        return new LinkedHashSet<>(Arrays.asList(values));
    }

    public static boolean startsReceiver(String calleeName, int argumentCount,
                                         Types receiverType) {
        return argumentCount == 0 && shaped(RECEIVER_STARTS, calleeName,
                receiverType);
    }

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

    public static boolean entersWork(String methodName, int argumentCount,
                                     Types declaringType) {
        return argumentCount == 0 && shaped(WORK_ENTRIES, methodName,
                declaringType)
                || argumentCount == 1 && "run".equals(methodName)
                && declaringType != null && declaringType.is(TIMER_TASK);
    }

    private static final String QUEUE_TYPE =
            "java.util.concurrent.BlockingQueue";

    private static final Set<String> QUEUE_SUBMISSIONS =
            names("put", "offer", "add", "putFirst", "putLast", "offerFirst",
                    "offerLast", "addFirst", "addLast");

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

    public static boolean mayEnterWork(String methodName, int argumentCount) {
        return argumentCount == 0 && methodName != null
                && named(WORK_ENTRIES, methodName)
                || argumentCount == 1 && "run".equals(methodName);
    }

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
}
