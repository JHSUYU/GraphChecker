package edu.uva.liftlab.graphchecker.runtime;

import java.io.File;
import java.lang.annotation.Annotation;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Proxy;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * Runs one workload test method by reflection, without a JUnit engine:
 * class setup, test setup, the test, test teardown, class teardown.  Setup
 * runs superclass first, teardown subclass first; an overridden method runs
 * once.
 *
 * <p>Roles are annotation names from both JUnit 4 and Jupiter.  An
 * unrecognized method is refused, never skipped (else a session is published
 * for a workload that never ran).  The workload's own throwable surfaces
 * unwrapped.  Declared timeouts are deliberately ignored: the caller owns the
 * wall clock.  Sessions are {@link JUnitMethodRunner}'s concern.</p>
 *
 * <p>What a Jupiter test class states about its own set-up is honoured too:
 * a {@code @TempDir} field gets a fresh directory, and an extension a
 * {@code @RegisterExtension} field holds gets its lifecycle callbacks around
 * the methods of the same role, with a context that answers what the test
 * is ({@link #context}).  A test method name a helper shares is the
 * {@code @Test} one.  A lifecycle or test method may take Jupiter's {@code
 * TestInfo}, which the same context answers (ZooKeeper's {@code
 * ZKTestCase#starting} logs the test it starts); any other parameter is
 * refused by name.  A parameterized test or class runs the one invocation
 * the case names, {@code m[k]} ({@link JUnitInvocation}): its arguments go to
 * the method's leading parameters and to the class's constructor or
 * {@code @Parameter} fields.</p>
 */
final class JUnitLifecycle {
    /** What marks the method the adapter names, in either vocabulary. */
    private static final String[] TEST = {
            "org.junit.jupiter.api.Test", "org.junit.Test"};
    /** What marks a method run once per argument set. */
    private static final String[] PARAMETERIZED = {
            JUnitInvocation.PARAMETERIZED_TEST};
    private static final String[] TEMP_DIR = {
            "org.junit.jupiter.api.io.TempDir"};
    private static final String[] REGISTER_EXTENSION = {
            "org.junit.jupiter.api.extension.RegisterExtension"};
    private static final String EXTENSIONS =
            "org.junit.jupiter.api.extension.";
    /** The one parameter type a lifecycle or test method may take. */
    private static final String TEST_INFO = "org.junit.jupiter.api.TestInfo";

    /** The four roles; {@code onTheClass} roles are static. */
    private enum Lifecycle {
        BEFORE_ALL(true, true, "BeforeAllCallback",
                "org.junit.jupiter.api.BeforeAll", "org.junit.BeforeClass"),
        BEFORE_EACH(false, true, "BeforeEachCallback",
                "org.junit.jupiter.api.BeforeEach", "org.junit.Before"),
        AFTER_EACH(false, false, "AfterEachCallback",
                "org.junit.jupiter.api.AfterEach", "org.junit.After"),
        AFTER_ALL(true, false, "AfterAllCallback",
                "org.junit.jupiter.api.AfterAll", "org.junit.AfterClass");

        private final boolean onTheClass;
        private final boolean superclassFirst;
        /** The extension callback of this role: an interface of {@link
         *  #EXTENSIONS} whose one method is its name, uncapitalized and
         *  without "Callback". */
        private final String callback;
        private final String[] annotations;

        Lifecycle(boolean onTheClass, boolean superclassFirst,
                  String callback, String... annotations) {
            this.onTheClass = onTheClass;
            this.superclassFirst = superclassFirst;
            this.callback = callback;
            this.annotations = annotations;
        }
    }

    /** The invocation this run is of: one per workload JVM. */
    private static JUnitInvocation running;

    private JUnitLifecycle() {
    }

    static void run(String[] args) throws Exception {
        if (args == null || args.length != 2) {
            throw new IllegalArgumentException(
                    "usage: JUnitMethodRunner <class> <method>[k]...");
        }
        Class<?> testClass = Class.forName(args[0]);
        JUnitInvocation named = JUnitInvocation.parse(args[1]);
        Method testMethod = testMethod(testClass, named.method);
        if (declaresRunner(testClass)) {
            if (!named.plain()) {
                throw new IllegalArgumentException(testClass.getName()
                        + " is run by its own runner, which takes a method"
                        + " name, not an invocation: " + args[1]);
            }
            runWithItsRunner(testClass, testMethod.getName());
            return;
        }
        // Before anything of the test runs, so before its window.
        named.resolve(testClass, testMethod);
        if (!named.plain()) ScheduleLog.invocation(named.stated());
        running = named;
        Throwable failure = null;
        // A static field's extension is the class's; an instance field's,
        // the test's alone.
        List<Object> classExtensions = new ArrayList<>();
        try {
            prepareFields(testClass, null, classExtensions);
            around(Lifecycle.BEFORE_ALL, testClass, null, null,
                    classExtensions);
            invokeAll(null, lifecycleMethods(testClass, Lifecycle.BEFORE_ALL),
                    testClass, null);
            Object test = named.newTest(testClass);
            List<Object> extensions = new ArrayList<>(classExtensions);
            try {
                prepareFields(testClass, test, extensions);
                around(Lifecycle.BEFORE_EACH, testClass, test, testMethod,
                        extensions);
                invokeAll(test,
                        lifecycleMethods(testClass, Lifecycle.BEFORE_EACH),
                        testClass, testMethod);
                call(test, testMethod, named.arguments(testMethod, type
                        -> context(type, testClass, test, testMethod)));
            } catch (Throwable thrown) {
                failure = thrown;
            } finally {
                failure = alsoInvoke(failure, test,
                        lifecycleMethods(testClass, Lifecycle.AFTER_EACH),
                        testClass, testMethod);
                failure = alsoAround(failure, Lifecycle.AFTER_EACH,
                        testClass, test, testMethod, extensions);
            }
        } catch (Throwable thrown) {
            // Class setup or construction failed: class teardown still runs.
            failure = merge(failure, thrown);
        } finally {
            failure = alsoInvoke(failure, null,
                    lifecycleMethods(testClass, Lifecycle.AFTER_ALL),
                    testClass, null);
            failure = alsoAround(failure, Lifecycle.AFTER_ALL, testClass,
                    null, null, classExtensions);
        }
        rethrow(failure);
    }

    /** What names a JUnit 4 class's own runner; it is inherited. */
    private static final String[] RUN_WITH = {"org.junit.runner.RunWith"};

    /** Whether the class or a superclass names the runner that runs it. */
    private static boolean declaresRunner(Class<?> testClass) {
        for (Class<?> type = testClass; type != null;
             type = type.getSuperclass()) {
            if (hasAnnotation(type.getDeclaredAnnotations(), RUN_WITH)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Runs one method of a class that names its runner, by that runner
     * ({@code RandomizedRunner} for every Lucene and Solr test): the rules,
     * the randomized context and the threads the runner gives a test are the
     * test's own, and reflection cannot stand in for them -- a Solr test
     * calls {@code random()}, which only the runner's thread answers.  The
     * runner is the workload's JUnit, reached reflectively.  A method the
     * runner skipped is refused like a missing one: a session would be
     * published for a workload that never ran.
     */
    private static void runWithItsRunner(Class<?> testClass, String method)
            throws Exception {
        ClassLoader loader = testClass.getClassLoader();
        Class<?> requestType = Class.forName("org.junit.runner.Request", true,
                loader);
        Object request = requestType.getMethod("method", Class.class,
                String.class).invoke(null, testClass, method);
        Class<?> coreType = Class.forName("org.junit.runner.JUnitCore", true,
                loader);
        Object result = coreType.getMethod("run", requestType)
                .invoke(coreType.getConstructor().newInstance(), request);
        Class<?> resultType = result.getClass();
        List<?> failures = (List<?>) resultType.getMethod("getFailures")
                .invoke(result);
        Throwable failure = null;
        for (Object each : failures) {
            failure = merge(failure, (Throwable) each.getClass()
                    .getMethod("getException").invoke(each));
        }
        rethrow(failure);
        int ran = (Integer) resultType.getMethod("getRunCount").invoke(result);
        int ignored = (Integer) resultType.getMethod("getIgnoreCount")
                .invoke(result);
        if (ran != 1 || ignored != 0) {
            throw new NoSuchMethodException("its runner ran " + ran
                    + " and ignored " + ignored + " test(s) for "
                    + testClass.getName() + "#" + method);
        }
    }

    /**
     * The named test method, most derived first so an override wins; a
     * same-named helper is passed over; refused if missing or not marked a
     * test.  What its parameters take is {@link JUnitInvocation#resolve}'s.
     */
    private static Method testMethod(Class<?> testClass, String methodName)
            throws NoSuchMethodException {
        boolean named = false;
        for (Class<?> type : hierarchy(testClass, false)) {
            for (Method method : type.getDeclaredMethods()) {
                if (!method.getName().equals(methodName)
                        || method.isSynthetic()) {
                    continue;
                }
                named = true;
                Annotation[] marks = method.getDeclaredAnnotations();
                if (!hasAnnotation(marks, TEST)
                        && !hasAnnotation(marks, PARAMETERIZED)) {
                    continue;
                }
                method.setAccessible(true);
                return method;
            }
        }
        throw new NoSuchMethodException((named ? "not a @Test method: "
                : "no such test method: ") + testClass.getName() + "#"
                + methodName);
    }

    /**
     * The static fields ({@code test} null) or the instance fields of the
     * class: a {@code @TempDir} gets a fresh directory, and a
     * {@code @RegisterExtension}'s extension joins {@code extensions}.
     */
    private static void prepareFields(Class<?> testClass, Object test,
                                      List<Object> extensions)
            throws Exception {
        for (Class<?> type : hierarchy(testClass, true)) {
            for (Field field : type.getDeclaredFields()) {
                if (Modifier.isStatic(field.getModifiers()) != (test == null)
                        || field.isSynthetic()) {
                    continue;
                }
                Annotation[] marks = field.getDeclaredAnnotations();
                field.setAccessible(true);
                if (hasAnnotation(marks, TEMP_DIR)) {
                    Path directory = Files.createTempDirectory("junit");
                    if (field.getType() == Path.class) {
                        field.set(test, directory);
                    } else if (field.getType() == File.class) {
                        field.set(test, directory.toFile());
                    } else {
                        throw new IllegalStateException("@TempDir field is "
                                + "neither a Path nor a File: "
                                + type.getName() + "#" + field.getName());
                    }
                } else if (hasAnnotation(marks, REGISTER_EXTENSION)) {
                    extensions.add(field.get(test));
                }
            }
        }
    }

    /** The {@code role} callback of every extension that has one. */
    private static void around(Lifecycle role, Class<?> testClass,
                               Object test, Method testMethod,
                               List<Object> extensions) throws Throwable {
        for (Object extension : extensions) {
            Class<?> callback = callback(role, extension);
            if (callback == null) continue;
            Method method = callback.getMethods()[0];
            try {
                method.invoke(extension, context(method.getParameterTypes()[0],
                        testClass, test, testMethod));
            } catch (InvocationTargetException exception) {
                throw exception.getCause();
            }
        }
    }

    private static Throwable alsoAround(Throwable failure, Lifecycle role,
                                        Class<?> testClass, Object test,
                                        Method testMethod,
                                        List<Object> extensions) {
        try {
            around(role, testClass, test, testMethod, extensions);
            return failure;
        } catch (Throwable thrown) {
            return merge(failure, thrown);
        }
    }

    /** The extension's callback interface for {@code role}, or null. */
    private static Class<?> callback(Lifecycle role, Object extension) {
        for (Class<?> type = extension.getClass(); type != null;
             type = type.getSuperclass()) {
            for (Class<?> implemented : type.getInterfaces()) {
                if (implemented.getName().equals(
                        EXTENSIONS + role.callback)) {
                    return implemented;
                }
            }
        }
        return null;
    }

    /**
     * The extension context a callback is handed, or the {@code TestInfo} a
     * method takes (a subset of the same questions): which class, instance
     * and method the test is.  What it cannot answer is refused by name, so
     * an extension that needs more fails the workload instead of seeing a
     * lie.
     */
    private static Object context(Class<?> contextType, Class<?> testClass,
                                  Object test, Method testMethod) {
        Object[] self = new Object[1];
        self[0] = Proxy.newProxyInstance(contextType.getClassLoader(),
                new Class<?>[]{contextType}, (proxy, method, arguments) -> {
                    switch (method.getName()) {
                        case "getTestClass":
                            return Optional.of(testClass);
                        case "getRequiredTestClass":
                            return testClass;
                        case "getTestInstance":
                            return Optional.ofNullable(test);
                        case "getRequiredTestInstance":
                            return required(test, "test instance");
                        case "getTestMethod":
                            return Optional.ofNullable(testMethod);
                        case "getRequiredTestMethod":
                            return required(testMethod, "test method");
                        case "getElement":
                            return Optional.of(testMethod == null
                                    ? testClass : testMethod);
                        case "getDisplayName":
                            return testMethod == null
                                    ? testClass.getSimpleName()
                                    : running.display() != null
                                    ? running.display()
                                    : testMethod.getName() + "()";
                        case "getUniqueId":
                            return testClass.getName() + (testMethod == null
                                    ? "" : "#" + testMethod.getName()
                                    + running.picked());
                        case "getParent":
                        case "getExecutionException":
                        case "getConfigurationParameter":
                            return Optional.empty();
                        case "getRoot":
                            return self[0];
                        case "getTags":
                            return Collections.emptySet();
                        case "hashCode":
                            return System.identityHashCode(proxy);
                        case "equals":
                            return proxy == arguments[0];
                        case "toString":
                            return contextType.getSimpleName() + "["
                                    + testClass.getName() + "]";
                        default:
                            throw new UnsupportedOperationException(
                                    "the workload runner's extension context "
                                            + "does not answer "
                                            + method.getName());
                    }
                });
        return self[0];
    }

    private static Object required(Object value, String what) {
        if (value == null) {
            throw new IllegalStateException("no " + what + " at this point"
                    + " of the lifecycle");
        }
        return value;
    }

    /** The methods of one role, in the order the role runs them. */
    private static List<Method> lifecycleMethods(Class<?> testClass,
                                                 Lifecycle role) {
        List<Method> methods = new ArrayList<>();
        Set<String> collected = new LinkedHashSet<>();
        for (Class<?> type : hierarchy(testClass, false)) {
            for (Method method : type.getDeclaredMethods()) {
                if (method.isSynthetic() || !hasAnnotation(
                        method.getDeclaredAnnotations(), role.annotations)) {
                    continue;
                }
                if (!resolvable(method)) {
                    throw new IllegalStateException(
                            "lifecycle method takes parameters: " + role
                                    + " " + type.getName() + "#"
                                    + method.getName());
                }
                if (role.onTheClass
                        != Modifier.isStatic(method.getModifiers())) {
                    throw new IllegalStateException((role.onTheClass
                            ? "lifecycle method is not static: "
                            : "lifecycle method is static: ") + role + " "
                            + type.getName() + "#" + method.getName());
                }
                // Already collected: this one is overridden.
                if (!collected.add(method.getName())) {
                    continue;
                }
                method.setAccessible(true);
                methods.add(method);
            }
        }
        // Collected most derived first, which is teardown's direction.
        return role.superclassFirst
                ? bySuperclassFirst(testClass, methods) : methods;
    }

    private static List<Method> bySuperclassFirst(Class<?> testClass,
                                                  List<Method> methods) {
        List<Method> ordered = new ArrayList<>(methods.size());
        for (Class<?> type : hierarchy(testClass, true)) {
            for (Method method : methods) {
                if (method.getDeclaringClass() == type) {
                    ordered.add(method);
                }
            }
        }
        return ordered;
    }

    private static List<Class<?>> hierarchy(Class<?> testClass,
                                            boolean superclassFirst) {
        List<Class<?>> hierarchy = new ArrayList<>();
        for (Class<?> type = testClass;
             type != null && type != Object.class;
             type = type.getSuperclass()) {
            hierarchy.add(type);
        }
        if (superclassFirst) {
            Collections.reverse(hierarchy);
        }
        return hierarchy;
    }

    private static boolean hasAnnotation(Annotation[] annotations,
                                         String[] names) {
        for (Annotation annotation : annotations) {
            String annotationName = annotation.annotationType().getName();
            for (String name : names) {
                if (name.equals(annotationName)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static void invokeAll(Object receiver, List<Method> methods,
                                  Class<?> testClass, Method testMethod)
            throws Throwable {
        for (Method method : methods) {
            invoke(receiver, method, testClass, testMethod);
        }
    }

    /**
     * Runs teardown even after a failure; the first throwable stands, later
     * ones are suppressed under it.
     */
    private static Throwable alsoInvoke(Throwable failure, Object receiver,
                                        List<Method> methods,
                                        Class<?> testClass,
                                        Method testMethod) {
        Throwable standing = failure;
        for (Method method : methods) {
            try {
                invoke(receiver, method, testClass, testMethod);
            } catch (Throwable thrown) {
                standing = merge(standing, thrown);
            }
        }
        return standing;
    }

    private static Throwable merge(Throwable failure, Throwable thrown) {
        if (failure == null) {
            return thrown;
        }
        if (failure != thrown) {
            failure.addSuppressed(thrown);
        }
        return failure;
    }

    /** Whether every parameter of {@code method} is a {@code TestInfo}. */
    private static boolean resolvable(Method method) {
        for (Class<?> parameter : method.getParameterTypes()) {
            if (!TEST_INFO.equals(parameter.getName())) return false;
        }
        return true;
    }

    /**
     * Calls {@code method} of the test {@code testMethod} names (null for a
     * class role), a {@code TestInfo} parameter answered by its context.
     */
    private static void invoke(Object receiver, Method method,
                               Class<?> testClass, Method testMethod)
            throws Throwable {
        Class<?>[] types = method.getParameterTypes();
        Object[] arguments = new Object[types.length];
        for (int i = 0; i < types.length; i++) {
            arguments[i] = context(types[i], testClass, receiver, testMethod);
        }
        call(receiver, method, arguments);
    }

    /** Calls {@code method}, the workload's own throwable unwrapped. */
    private static void call(Object receiver, Method method,
                             Object[] arguments) throws Throwable {
        try {
            method.invoke(receiver, arguments);
        } catch (InvocationTargetException exception) {
            throw exception.getCause();
        }
    }

    private static void rethrow(Throwable failure) throws Exception {
        if (failure == null) {
            return;
        }
        if (failure instanceof Exception) {
            throw (Exception) failure;
        }
        if (failure instanceof Error) {
            throw (Error) failure;
        }
        throw new RuntimeException(failure);
    }
}
