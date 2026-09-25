package edu.uva.liftlab.graphchecker.runtime;

import java.lang.annotation.Annotation;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
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
 */
final class JUnitLifecycle {
    /** What marks the method the adapter names, in either vocabulary. */
    private static final String[] TEST = {
            "org.junit.jupiter.api.Test", "org.junit.Test"};

    /** The four roles; {@code onTheClass} roles are static. */
    private enum Lifecycle {
        BEFORE_ALL(true, true,
                "org.junit.jupiter.api.BeforeAll", "org.junit.BeforeClass"),
        BEFORE_EACH(false, true,
                "org.junit.jupiter.api.BeforeEach", "org.junit.Before"),
        AFTER_EACH(false, false,
                "org.junit.jupiter.api.AfterEach", "org.junit.After"),
        AFTER_ALL(true, false,
                "org.junit.jupiter.api.AfterAll", "org.junit.AfterClass");

        private final boolean onTheClass;
        private final boolean superclassFirst;
        private final String[] annotations;

        Lifecycle(boolean onTheClass, boolean superclassFirst,
                  String... annotations) {
            this.onTheClass = onTheClass;
            this.superclassFirst = superclassFirst;
            this.annotations = annotations;
        }
    }

    private JUnitLifecycle() {
    }

    static void run(String[] args) throws Exception {
        if (args == null || args.length != 2) {
            throw new IllegalArgumentException(
                    "usage: JUnitMethodRunner <class> <method>");
        }
        Class<?> testClass = Class.forName(args[0]);
        Method testMethod = testMethod(testClass, args[1]);
        Throwable failure = null;
        try {
            invokeAll(null, lifecycleMethods(testClass, Lifecycle.BEFORE_ALL));
            Constructor<?> constructor = testClass.getDeclaredConstructor();
            constructor.setAccessible(true);
            Object test = constructor.newInstance();
            try {
                invokeAll(test,
                        lifecycleMethods(testClass, Lifecycle.BEFORE_EACH));
                invoke(test, testMethod);
            } catch (Throwable thrown) {
                failure = thrown;
            } finally {
                failure = alsoInvoke(failure, test,
                        lifecycleMethods(testClass, Lifecycle.AFTER_EACH));
            }
        } catch (Throwable thrown) {
            // Class setup or construction failed: class teardown still runs.
            failure = merge(failure, thrown);
        } finally {
            failure = alsoInvoke(failure, null,
                    lifecycleMethods(testClass, Lifecycle.AFTER_ALL));
        }
        rethrow(failure);
    }

    /**
     * The named test method, most derived first so an override wins; refused
     * if missing, parameterized or not marked a test.
     */
    private static Method testMethod(Class<?> testClass, String methodName)
            throws NoSuchMethodException {
        for (Class<?> type : hierarchy(testClass, false)) {
            for (Method method : type.getDeclaredMethods()) {
                if (!method.getName().equals(methodName)
                        || method.isSynthetic()) {
                    continue;
                }
                if (method.getParameterCount() != 0) {
                    throw new NoSuchMethodException(
                            "test method takes parameters: "
                                    + testClass.getName() + "#" + methodName);
                }
                if (!hasAnnotation(method, TEST)) {
                    throw new NoSuchMethodException("not a @Test method: "
                            + testClass.getName() + "#" + methodName);
                }
                method.setAccessible(true);
                return method;
            }
        }
        throw new NoSuchMethodException("no such test method: "
                + testClass.getName() + "#" + methodName);
    }

    /** The methods of one role, in the order the role runs them. */
    private static List<Method> lifecycleMethods(Class<?> testClass,
                                                 Lifecycle role) {
        List<Method> methods = new ArrayList<>();
        Set<String> collected = new LinkedHashSet<>();
        for (Class<?> type : hierarchy(testClass, false)) {
            for (Method method : type.getDeclaredMethods()) {
                if (method.isSynthetic()
                        || !hasAnnotation(method, role.annotations)) {
                    continue;
                }
                if (method.getParameterCount() != 0) {
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

    private static boolean hasAnnotation(Method method, String[] names) {
        for (Annotation annotation : method.getDeclaredAnnotations()) {
            String annotationName = annotation.annotationType().getName();
            for (String name : names) {
                if (name.equals(annotationName)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static void invokeAll(Object receiver, List<Method> methods)
            throws Throwable {
        for (Method method : methods) {
            invoke(receiver, method);
        }
    }

    /**
     * Runs teardown even after a failure; the first throwable stands, later
     * ones are suppressed under it.
     */
    private static Throwable alsoInvoke(Throwable failure, Object receiver,
                                        List<Method> methods) {
        Throwable standing = failure;
        for (Method method : methods) {
            try {
                invoke(receiver, method);
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

    private static void invoke(Object receiver, Method method)
            throws Throwable {
        try {
            method.invoke(receiver);
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
