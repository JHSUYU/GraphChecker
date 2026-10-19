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

final class JUnitInvocation {
    private static final String PARAMS = "org.junit.jupiter.params.";
    private static final String PROVIDER = PARAMS + "provider.";
    static final String PARAMETERIZED_TEST = PARAMS + "ParameterizedTest";
    private static final String PARAMETERIZED_CLASS =
            PARAMS + "ParameterizedClass";
    private static final String PARAMETER = PARAMS + "Parameter";
    private static final String[] CLASS_INVOCATION_LIFECYCLE = {
            PARAMS + "BeforeParameterizedClassInvocation",
            PARAMS + "AfterParameterizedClassInvocation"};
    private static final Pattern NAMED =
            Pattern.compile("([^\\[\\]]+)((?:\\[[1-9][0-9]*\\])*)");
    private static final Pattern PICK = Pattern.compile("\\[([0-9]+)\\]");
    private static final String TEST_INFO = "org.junit.jupiter.api.TestInfo";

    final String method;
    private final List<Integer> picks;
    private Object[] ofClass;
    private Object[] ofMethod;
    private String display;
    private final StringBuilder stated = new StringBuilder();
    private List<Field> fields = new ArrayList<>();
    private Constructor<?> constructor;

    private JUnitInvocation(String method, List<Integer> picks) {
        this.method = method;
        this.picks = picks;
    }

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

    boolean plain() {
        return picks.isEmpty();
    }

    String picked() {
        StringBuilder label = new StringBuilder();
        for (int pick : picks) {
            label.append('[').append(pick).append(']');
        }
        return label.toString();
    }

    String display() {
        return display;
    }

    String stated() {
        return plain() ? null : method + stated;
    }

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

    private static String display(int k, Object[] arguments) {
        return "[" + k + "] " + rendered(arguments);
    }

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
        }
        return JvmNames.stable(value.getClass().getName());
    }

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

    private static boolean source(Class<? extends Annotation> type) {
        return type.getName().equals(PROVIDER + "ArgumentsSource")
                || has(type.getDeclaredAnnotations(),
                PROVIDER + "ArgumentsSource", PROVIDER + "ArgumentsSources");
    }

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

    private static String optional(Annotation mark, String name) {
        try {
            mark.annotationType().getMethod(name);
        } catch (NoSuchMethodException older) {
            return "";
        }
        return (String) attribute(mark, name);
    }
}
