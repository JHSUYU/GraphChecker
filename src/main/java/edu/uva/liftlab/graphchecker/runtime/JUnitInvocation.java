package edu.uva.liftlab.graphchecker.runtime;

import java.lang.annotation.Annotation;
import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.Executable;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.BaseStream;

import edu.uva.liftlab.graphchecker.contract.JvmNames;

/**
 * The one invocation of a workload test a case names: {@code m} for a plain
 * test method, {@code m[k]} for the k-th invocation of a Jupiter {@code
 * @ParameterizedTest} m or of a {@code @ParameterizedClass}, {@code m[i][j]}
 * when both are (the class's invocation, then the method's).  k counts from
 * 1 in the order of the argument sources, as JUnit numbers the invocations
 * it shows as {@code [k]}; several sources follow one another in the order
 * they are declared, a repeated one included.  A name names as many
 * invocations as the test has parameterized levels: a parameterized test
 * named bare is refused, never run for every invocation.
 *
 * <p>The arguments are resolved before anything of the test runs, so before
 * the window and alike in both passes, provided a factory states its
 * arguments in one order; the run states which invocation it resolved, its
 * arguments rendered alike in both passes ({@link #stated}), and a replay of
 * a run that resolved another is refused by name ({@code
 * ScheduleLog#invocation}).  A source that throws, yields no invocation or has
 * no k-th one is refused by name: a session would otherwise be published for
 * a workload that never ran.  The sources resolved are {@code @MethodSource}
 * (a static factory, by name or {@code Class#name}, the test method's own
 * name by default; a stream, an iterable, an iterator or an array of {@code
 * Arguments}, of {@code Object[]} or of single values), {@code @ValueSource}
 * and {@code @EnumSource}; any other argument source is refused by name, as
 * is an argument its parameter cannot take as it is (nothing is converted).
 * A method's arguments go to its leading parameters, a class's to its one
 * constructor or to its {@code @Parameter(i)} fields.</p>
 */
final class JUnitInvocation {
    private static final String PARAMS = "org.junit.jupiter.params.";
    private static final String PROVIDER = PARAMS + "provider.";
    static final String PARAMETERIZED_TEST = PARAMS + "ParameterizedTest";
    private static final String PARAMETERIZED_CLASS =
            PARAMS + "ParameterizedClass";
    private static final String PARAMETER = PARAMS + "Parameter";
    /** A class invocation's own lifecycle, which this runner does not run. */
    private static final String[] CLASS_INVOCATION_LIFECYCLE = {
            PARAMS + "BeforeParameterizedClassInvocation",
            PARAMS + "AfterParameterizedClassInvocation"};
    private static final Pattern NAMED =
            Pattern.compile("([^\\[\\]]+)((?:\\[[1-9][0-9]*\\])*)");
    private static final Pattern PICK = Pattern.compile("\\[([0-9]+)\\]");
    /** The one parameter type answered after a test method's arguments. */
    private static final String TEST_INFO = "org.junit.jupiter.api.TestInfo";

    /** The test method's name. */
    final String method;
    /** Which invocation of each parameterized level, from 1. */
    private final List<Integer> picks;
    /** The class invocation's arguments; null where the class is plain. */
    private Object[] ofClass;
    /** The method invocation's arguments; null where the method is plain. */
    private Object[] ofMethod;
    /** JUnit's display name of the innermost invocation, or null. */
    private String display;
    /** The invocation as the run states it: the method, then per level its
     *  pick and its arguments ({@link #rendered}). */
    private final StringBuilder stated = new StringBuilder();
    /** A class invocation's {@code @Parameter} fields; none else. */
    private List<Field> fields = new ArrayList<>();
    /** The constructor a class invocation's arguments go to, else null. */
    private Constructor<?> constructor;

    private JUnitInvocation(String method, List<Integer> picks) {
        this.method = method;
        this.picks = picks;
    }

    /** {@code m}, {@code m[k]} or {@code m[i][j]} (class comment). */
    static JUnitInvocation parse(String named) {
        Matcher matcher = NAMED.matcher(named == null ? "" : named);
        if (!matcher.matches()) {
            throw new IllegalArgumentException("not a test method name: "
                    + named + " (name a method m, or one invocation of a"
                    + " parameterized test as m[k], k from 1)");
        }
        List<Integer> picks = new ArrayList<>();
        Matcher pick = PICK.matcher(matcher.group(2));
        while (pick.find()) {
            picks.add(Integer.valueOf(pick.group(1)));
        }
        return new JUnitInvocation(matcher.group(1), picks);
    }

    /** Whether the name picks no invocation at all. */
    boolean plain() {
        return picks.isEmpty();
    }

    /** The bracketed picks, as the name states them. */
    String picked() {
        StringBuilder label = new StringBuilder();
        for (int pick : picks) {
            label.append('[').append(pick).append(']');
        }
        return label.toString();
    }

    /** JUnit's display name of the invocation, or null for a plain test. */
    String display() {
        return display;
    }

    /** The resolved invocation as the run states it, e.g. {@code
     *  testSimpleEditLog[1](false)}; null for a plain test. */
    String stated() {
        return plain() ? null : method + stated;
    }

    /**
     * Resolves the named invocation of {@code testMethod} of {@code
     * testClass}: what each parameterized level passes this run, checked
     * against the parameters it goes to.
     */
    void resolve(Class<?> testClass, Method testMethod) {
        Class<?> parameterized = declaring(testClass, PARAMETERIZED_CLASS);
        boolean methodLevel = has(testMethod.getDeclaredAnnotations(),
                PARAMETERIZED_TEST);
        int levels = (parameterized != null ? 1 : 0) + (methodLevel ? 1 : 0);
        String test = testClass.getName() + "#" + method;
        if (levels != picks.size()) {
            throw new IllegalArgumentException(test + picked() + " names "
                    + picks.size() + " invocation(s), but the test is"
                    + " parameterized at " + levels + " level(s) (a"
                    + " parameterized class, then a parameterized method):"
                    + " name one invocation per level, as m[k], k from 1");
        }
        int next = 0;
        if (parameterized != null) {
            refuseClassInvocationLifecycle(testClass);
            String where = "class " + testClass.getName();
            ofClass = pick(sets(sourced(testClass), testClass, null, null,
                    where), picks.get(next), where);
            display = display(picks.get(next++), ofClass);
            stated.append("[").append(picks.get(next - 1)).append("](")
                    .append(rendered(ofClass)).append(")");
            fields = parameterFields(testClass);
            if (fields.isEmpty()) {
                constructor = theConstructor(testClass);
                fits(constructor, ofClass, false);
            } else {
                for (Field field : fields) {
                    argument(field);
                }
            }
        }
        if (methodLevel) {
            Class<?>[] types = testMethod.getParameterTypes();
            ofMethod = pick(sets(testMethod.getDeclaredAnnotations(),
                    testClass, testMethod, types.length == 0 ? null
                            : types[0], test), picks.get(next), test);
            display = display(picks.get(next), ofMethod);
            stated.append("[").append(picks.get(next)).append("](")
                    .append(rendered(ofMethod)).append(")");
        }
        fits(testMethod, methodArguments(), true);
    }

    /** A new test instance: the class invocation's, else a plain one. */
    Object newTest(Class<?> testClass) throws Throwable {
        if (constructor != null) {
            return construct(constructor, ofClass);
        }
        Object test = construct(testClass.getDeclaredConstructor(),
                new Object[0]);
        for (Field field : fields) {
            field.setAccessible(true);
            field.set(test, argument(field));
        }
        return test;
    }

    /**
     * The test method's arguments: the invocation's to its leading
     * parameters, {@code rest} answering each parameter after them (a
     * {@code TestInfo}: {@link #resolve} refused anything else).
     */
    Object[] arguments(Method testMethod, Function<Class<?>, Object> rest) {
        Object[] values = methodArguments();
        Class<?>[] types = testMethod.getParameterTypes();
        Object[] bound = new Object[types.length];
        for (int i = 0; i < types.length; i++) {
            bound[i] = i < values.length ? values[i] : rest.apply(types[i]);
        }
        return bound;
    }

    private Object[] methodArguments() {
        return ofMethod == null ? new Object[0] : ofMethod;
    }

    /** The {@code @Parameter} fields of the class and its superclasses. */
    private static List<Field> parameterFields(Class<?> testClass) {
        List<Field> fields = new ArrayList<>();
        for (Class<?> type = testClass; type != null && type != Object.class;
             type = type.getSuperclass()) {
            for (Field field : type.getDeclaredFields()) {
                if (has(field.getDeclaredAnnotations(), PARAMETER)) {
                    fields.add(field);
                }
            }
        }
        return fields;
    }

    /** The one constructor a class invocation's arguments go to. */
    private static Constructor<?> theConstructor(Class<?> testClass) {
        List<Constructor<?>> declared = new ArrayList<>();
        for (Constructor<?> each : testClass.getDeclaredConstructors()) {
            if (!each.isSynthetic()) declared.add(each);
        }
        if (declared.size() != 1) {
            throw new IllegalStateException("parameterized class "
                    + testClass.getName() + " declares " + declared.size()
                    + " constructors and no @Parameter field: its arguments"
                    + " go to its one constructor");
        }
        return declared.get(0);
    }

    /** The argument a {@code @Parameter} field takes, checked. */
    private Object argument(Field field) {
        int index = (Integer) attribute(annotation(
                field.getDeclaredAnnotations(), PARAMETER), "value");
        String where = "@Parameter field " + field.getDeclaringClass()
                .getName() + "#" + field.getName();
        if (index < 0 || index >= ofClass.length) {
            throw new IllegalStateException(where + " takes argument "
                    + index + " of " + ofClass.length + (index < 0
                    ? " (an aggregator, which the workload runner does not"
                    + " build)" : ""));
        }
        return checked(field.getType(), ofClass[index], where);
    }

    /**
     * Whether {@code values} fit the leading parameters of {@code target};
     * a parameter after them is a {@code TestInfo} where {@code testInfo},
     * else refused.  More values than parameters are left unused, as JUnit
     * leaves them.
     */
    private static void fits(Executable target, Object[] values,
                             boolean testInfo) {
        Class<?>[] types = target.getParameterTypes();
        for (int i = 0; i < types.length; i++) {
            if (i < values.length) {
                checked(types[i], values[i], "parameter " + i + " of "
                        + target);
            } else if (!testInfo || !TEST_INFO.equals(types[i].getName())) {
                throw new IllegalStateException(target + " takes a "
                        + types[i].getName() + " beyond its " + values.length
                        + " argument(s): only a TestInfo"
                        + (testInfo ? "" : " of a test method")
                        + " is answered there");
            }
        }
    }

    private static Object construct(Constructor<?> made, Object[] arguments)
            throws Throwable {
        made.setAccessible(true);
        try {
            return made.newInstance(Arrays.copyOf(arguments,
                    made.getParameterCount()));
        } catch (InvocationTargetException exception) {
            throw exception.getCause();
        }
    }

    /** {@code value} as a {@code type} takes it, or refused: nothing is
     *  converted. */
    private static Object checked(Class<?> type, Object value, String where) {
        if (value == null ? !type.isPrimitive()
                : boxed(type).isInstance(value)) {
            return value;
        }
        throw new IllegalArgumentException(where + " is a " + type.getName()
                + ", its argument " + (value == null ? "null"
                : "a " + value.getClass().getName()) + ": the workload runner"
                + " converts no argument");
    }

    private static Class<?> boxed(Class<?> type) {
        if (!type.isPrimitive()) return type;
        return Array.get(Array.newInstance(type, 1), 0).getClass();
    }

    private static Object[] pick(List<Object[]> sets, int k, String where) {
        if (sets.isEmpty()) {
            throw new IllegalStateException("the argument sources of " + where
                    + " yield no invocation");
        }
        if (k > sets.size()) {
            throw new IllegalStateException("the argument sources of " + where
                    + " yield " + sets.size() + " invocation(s): there is no ["
                    + k + "]");
        }
        return sets.get(k - 1);
    }

    /** JUnit's display name of invocation {@code k}: {@code [k] } and its
     *  arguments ({@link #rendered}). */
    private static String display(int k, Object[] arguments) {
        return "[" + k + "] " + rendered(arguments);
    }

    /**
     * Arguments as both passes render them alike: a value by its own {@code
     * toString}, an array element by element, and a value whose class has no
     * {@code toString} of its own by its run-stable class name (an identity
     * hash would differ in every run).
     */
    static String rendered(Object value) {
        if (value == null) return "null";
        if (value instanceof Object[]) {
            StringBuilder shown = new StringBuilder();
            for (Object each : (Object[]) value) {
                if (shown.length() > 0) shown.append(", ");
                shown.append(each != null && each.getClass().isArray()
                        ? "[" + rendered(each) + "]" : rendered(each));
            }
            return shown.toString();
        }
        if (value.getClass().isArray()) {
            Object[] boxed = new Object[Array.getLength(value)];
            for (int i = 0; i < boxed.length; i++) {
                boxed[i] = Array.get(value, i);
            }
            return rendered(boxed);
        }
        try {
            if (value.getClass().getMethod("toString").getDeclaringClass()
                    != Object.class) {
                return String.valueOf(value);
            }
        } catch (NoSuchMethodException unreachable) {
            // Every class has a public toString.
        }
        return JvmNames.stable(value.getClass().getName());
    }

    /** The argument sets of every source in {@code marks}, in order. */
    private static List<Object[]> sets(Annotation[] marks, Class<?> testClass,
                                       Method testMethod,
                                       Class<?> firstParameter,
                                       String where) {
        List<Object[]> sets = new ArrayList<>();
        for (Annotation mark : marks) {
            Annotation[] repeated = repeated(mark);
            if (repeated != null) {
                sets.addAll(sets(repeated, testClass, testMethod,
                        firstParameter, where));
                continue;
            }
            if (!source(mark.annotationType())) continue;
            switch (mark.annotationType().getName()) {
                case PROVIDER + "MethodSource":
                    sets.addAll(factorySets(mark, testClass, testMethod,
                            where));
                    break;
                case PROVIDER + "ValueSource":
                    sets.addAll(valueSets(mark, where));
                    break;
                case PROVIDER + "EnumSource":
                    sets.addAll(enumSets(mark, firstParameter, where));
                    break;
                default:
                    throw new IllegalStateException("argument source @"
                            + mark.annotationType().getSimpleName() + " of "
                            + where + " is not one the workload runner"
                            + " resolves (@MethodSource, @ValueSource,"
                            + " @EnumSource)");
            }
        }
        return sets;
    }

    /** Whether {@code type} is a JUnit argument source. */
    private static boolean source(Class<? extends Annotation> type) {
        return type.getName().equals(PROVIDER + "ArgumentsSource")
                || has(type.getDeclaredAnnotations(),
                PROVIDER + "ArgumentsSource", PROVIDER + "ArgumentsSources");
    }

    /** The sources a repeated source's container holds, else null. */
    private static Annotation[] repeated(Annotation mark) {
        try {
            Method value = mark.annotationType().getDeclaredMethod("value");
            Class<?> held = value.getReturnType().getComponentType();
            if (held == null || !held.isAnnotation()
                    || !source(held.asSubclass(Annotation.class))) {
                return null;
            }
            return (Annotation[]) attribute(mark, "value");
        } catch (NoSuchMethodException none) {
            return null;
        }
    }

    private static List<Object[]> factorySets(Annotation mark,
                                              Class<?> testClass,
                                              Method testMethod,
                                              String where) {
        String[] names = (String[]) attribute(mark, "value");
        if (names.length == 0) {
            if (testMethod == null) {
                throw new IllegalStateException("@MethodSource of " + where
                        + " names no factory");
            }
            names = new String[] {testMethod.getName()};
        }
        List<Object[]> sets = new ArrayList<>();
        for (String name : names) {
            Method factory = factory(testClass, name.trim(), where);
            Object made;
            try {
                factory.setAccessible(true);
                made = factory.invoke(null);
            } catch (InvocationTargetException thrown) {
                throw new IllegalStateException("argument factory " + factory
                        + " of " + where + " threw", thrown.getCause());
            } catch (IllegalAccessException unreachable) {
                throw new IllegalStateException(unreachable);
            }
            for (Object item : items(made, factory)) {
                sets.add(argumentSet(item));
            }
        }
        return sets;
    }

    /** The static zero-argument factory {@code name} or {@code Class#name}
     *  names, most derived first. */
    private static Method factory(Class<?> testClass, String name,
                                  String where) {
        Class<?> owner = testClass;
        String method = name.endsWith("()")
                ? name.substring(0, name.length() - 2) : name;
        int hash = method.indexOf('#');
        if (hash >= 0) {
            try {
                owner = Class.forName(method.substring(0, hash), true,
                        testClass.getClassLoader());
            } catch (ClassNotFoundException missing) {
                throw new IllegalStateException("@MethodSource of " + where
                        + " names a class that is not there: " + name);
            }
            method = method.substring(hash + 1);
        }
        for (Class<?> type = owner; type != null; type = type.getSuperclass()) {
            for (Method candidate : type.getDeclaredMethods()) {
                if (!candidate.getName().equals(method)
                        || candidate.isSynthetic()
                        || candidate.getParameterCount() != 0) {
                    continue;
                }
                if (!Modifier.isStatic(candidate.getModifiers())) {
                    throw new IllegalStateException("argument factory "
                            + candidate + " of " + where + " is not static"
                            + " (an instance factory needs a per-class test"
                            + " instance, which the workload runner does not"
                            + " make)");
                }
                return candidate;
            }
        }
        throw new IllegalStateException("@MethodSource of " + where
                + " names no static zero-argument factory: " + name);
    }

    /** What a factory made, one item per invocation. */
    private static List<Object> items(Object made, Method factory) {
        List<Object> items = new ArrayList<>();
        if (made instanceof BaseStream) {
            try (BaseStream<?, ?> stream = (BaseStream<?, ?>) made) {
                stream.iterator().forEachRemaining(items::add);
            }
        } else if (made instanceof Iterable) {
            ((Iterable<?>) made).forEach(items::add);
        } else if (made instanceof Iterator) {
            ((Iterator<?>) made).forEachRemaining(items::add);
        } else if (made != null && made.getClass().isArray()) {
            for (int i = 0; i < Array.getLength(made); i++) {
                items.add(Array.get(made, i));
            }
        } else {
            throw new IllegalStateException("argument factory " + factory
                    + " made " + (made == null ? "null"
                    : "a " + made.getClass().getName()) + ", not a stream,"
                    + " an iterable, an iterator or an array");
        }
        return items;
    }

    /** One item as JUnit spreads it: {@code Arguments}, an {@code Object[]},
     *  else one value. */
    private static Object[] argumentSet(Object item) {
        if (item instanceof Object[]) return (Object[]) item;
        if (item != null && implementsArguments(item.getClass())) {
            try {
                Method get = item.getClass().getMethod("get");
                get.setAccessible(true);
                return (Object[]) get.invoke(item);
            } catch (ReflectiveOperationException unreachable) {
                throw new IllegalStateException(unreachable);
            }
        }
        return new Object[] {item};
    }

    private static boolean implementsArguments(Class<?> type) {
        for (Class<?> at = type; at != null; at = at.getSuperclass()) {
            for (Class<?> implemented : at.getInterfaces()) {
                if (implemented.getName().equals(PROVIDER + "Arguments")
                        || implementsArguments(implemented)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** {@code @ValueSource}: its one non-empty array, a value each. */
    private static List<Object[]> valueSets(Annotation mark, String where) {
        List<Object[]> sets = null;
        for (Method attribute : mark.annotationType().getDeclaredMethods()) {
            Object values = attribute(mark, attribute.getName());
            if (!values.getClass().isArray() || Array.getLength(values) == 0) {
                continue;
            }
            if (sets != null) {
                throw new IllegalStateException("@ValueSource of " + where
                        + " states more than one array");
            }
            sets = new ArrayList<>();
            for (int i = 0; i < Array.getLength(values); i++) {
                sets.add(new Object[] {Array.get(values, i)});
            }
        }
        if (sets == null) {
            throw new IllegalStateException("@ValueSource of " + where
                    + " states no value");
        }
        return sets;
    }

    /** {@code @EnumSource}: the constants its range, names and mode select,
     *  in declaration order. */
    private static List<Object[]> enumSets(Annotation mark,
                                           Class<?> firstParameter,
                                           String where) {
        Class<?> type = (Class<?>) attribute(mark, "value");
        if (type.getName().equals(PROVIDER + "NullEnum")) {
            type = firstParameter;
        }
        if (type == null || !type.isEnum()) {
            throw new IllegalStateException("@EnumSource of " + where
                    + " names no enum type");
        }
        List<Object> constants = new ArrayList<>(
                Arrays.asList(type.getEnumConstants()));
        String from = optional(mark, "from");
        String to = optional(mark, "to");
        int first = from.isEmpty() ? 0 : ordinal(constants, from, where);
        int last = to.isEmpty() ? constants.size() - 1
                : ordinal(constants, to, where);
        constants = new ArrayList<>(constants.subList(first, last + 1));
        List<String> names = Arrays.asList((String[]) attribute(mark,
                "names"));
        String mode = ((Enum<?>) attribute(mark, "mode")).name();
        if (mode.equals("INCLUDE") || mode.equals("EXCLUDE")) {
            for (String name : names) {
                ordinal(constants, name, where);
            }
        }
        List<Object[]> sets = new ArrayList<>();
        for (Object constant : constants) {
            if (selected(mode, ((Enum<?>) constant).name(), names, where)) {
                sets.add(new Object[] {constant});
            }
        }
        return sets;
    }

    private static boolean selected(String mode, String name,
                                    List<String> names, String where) {
        switch (mode) {
            case "INCLUDE":
                return names.isEmpty() || names.contains(name);
            case "EXCLUDE":
                return !names.contains(name);
            case "MATCH_ALL":
                return names.stream().allMatch(name::matches);
            case "MATCH_ANY":
                return names.stream().anyMatch(name::matches);
            case "MATCH_NONE":
                return names.stream().noneMatch(name::matches);
            default:
                throw new IllegalStateException("@EnumSource of " + where
                        + " has a mode the workload runner does not know: "
                        + mode);
        }
    }

    private static int ordinal(List<Object> constants, String name,
                               String where) {
        for (int i = 0; i < constants.size(); i++) {
            if (((Enum<?>) constants.get(i)).name().equals(name)) return i;
        }
        throw new IllegalStateException("@EnumSource of " + where
                + " names no constant " + name);
    }

    /** A class invocation's own lifecycle is refused, never skipped. */
    private static void refuseClassInvocationLifecycle(Class<?> testClass) {
        for (Class<?> type = testClass; type != null && type != Object.class;
             type = type.getSuperclass()) {
            for (Method method : type.getDeclaredMethods()) {
                if (has(method.getDeclaredAnnotations(),
                        CLASS_INVOCATION_LIFECYCLE)) {
                    throw new IllegalStateException("parameterized class "
                            + testClass.getName() + " declares a class"
                            + " invocation lifecycle method, which the"
                            + " workload runner does not run: "
                            + type.getName() + "#" + method.getName());
                }
            }
        }
    }

    /** The marks of the nearest class in the hierarchy declaring a source
     *  (sources are inherited, as the parameterized class is). */
    private static Annotation[] sourced(Class<?> testClass) {
        for (Class<?> type = testClass; type != null && type != Object.class;
             type = type.getSuperclass()) {
            Annotation[] marks = type.getDeclaredAnnotations();
            for (Annotation mark : marks) {
                if (source(mark.annotationType()) || repeated(mark) != null) {
                    return marks;
                }
            }
        }
        return new Annotation[0];
    }

    /** The nearest class of the hierarchy declaring {@code annotation}. */
    private static Class<?> declaring(Class<?> testClass, String annotation) {
        for (Class<?> type = testClass; type != null && type != Object.class;
             type = type.getSuperclass()) {
            if (has(type.getDeclaredAnnotations(), annotation)) return type;
        }
        return null;
    }

    private static boolean has(Annotation[] marks, String... names) {
        return annotation(marks, names) != null;
    }

    private static Annotation annotation(Annotation[] marks,
                                         String... names) {
        for (Annotation mark : marks) {
            String name = mark.annotationType().getName();
            for (String wanted : names) {
                if (wanted.equals(name)) return mark;
            }
        }
        return null;
    }

    private static Object attribute(Annotation mark, String name) {
        try {
            Method attribute = mark.annotationType().getMethod(name);
            attribute.setAccessible(true);
            return attribute.invoke(mark);
        } catch (ReflectiveOperationException missing) {
            throw new IllegalStateException("@"
                    + mark.annotationType().getSimpleName() + " has no "
                    + name + "()", missing);
        }
    }

    /** A string attribute a JUnit version may lack ({@code @EnumSource}'s
     *  range came in 5.12), "" then. */
    private static String optional(Annotation mark, String name) {
        try {
            mark.annotationType().getMethod(name);
        } catch (NoSuchMethodException older) {
            return "";
        }
        return (String) attribute(mark, name);
    }
}
