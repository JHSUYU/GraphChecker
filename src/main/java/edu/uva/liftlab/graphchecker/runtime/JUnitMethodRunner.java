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
 * Runs one workload test method by reflection, without a JUnit engine.
 *
 * <p>This is the one runner: it instantiates the workload class and invokes
 * the class-level setup, the per-test setup, the named test method, the
 * per-test teardown and the class-level teardown itself, in the order an
 * engine would. Setup runs superclass first and teardown subclass first, and
 * a method overridden further down the hierarchy runs once, at the
 * overriding declaration.</p>
 *
 * <p>A lifecycle role is a set of annotation names, not an engine: the
 * corpus's workload checkouts are annotated in both JUnit vocabularies --
 * most with Jupiter's {@code @BeforeEach}/{@code @Test}, one with JUnit 4's
 * {@code @Before}/{@code @Test} -- and the two describe the same lifecycle,
 * so one reflective driver covers both by naming both. A method the runner
 * does not recognize is refused by name rather than skipped: the alternative
 * is a session published for a workload that never ran.</p>
 *
 * <p>A failure surfaces as the workload's own throwable rather than as an
 * engine's wrapper, which is what a replay's outcome is read from. A
 * declared timeout ({@code @Timeout}, {@code @Test(timeout=...)}) is
 * deliberately not read: the campaign owns the wall clock, and a replay
 * stopped by the workload's own timer would publish a truncated expression
 * table.</p>
 *
 * <p>This class is also the owner of the workload's symbolic lifetime. The
 * test method is what "the workload" means for GraphChecker, so the
 * workload-wide session opens before the method starts and closes after it
 * ends -- on every exit path, including a failing test. Region entry and exit
 * no longer bound that lifetime, which is what lets one producer's exported
 * expression outlive the producer's thread.</p>
 */
public final class JUnitMethodRunner {
    /** What marks the method the adapter names, in either vocabulary. */
    private static final String[] TEST = {
            "org.junit.jupiter.api.Test", "org.junit.Test"};

    /**
     * The four lifecycle roles, each with the annotations that name it.
     *
     * <p>{@code onTheClass} roles run once around the whole class and are
     * static in both vocabularies; the per-test roles run on the instance.
     * {@code superclassFirst} is setup's direction.</p>
     */
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

    private JUnitMethodRunner() {
    }

    public static void main(String[] args) throws Exception {
        String refusedOpen = ConcolicRegionRuntime.openWorkloadSession();
        if (!refusedOpen.isEmpty()) {
            // A campaign whose session the VM refused would run with
            // per-region symbolic lifetimes and quietly lose every
            // cross-thread expression it exists to record.
            throw new IllegalStateException(refusedOpen);
        }
        try {
            run(args);
        } finally {
            // Publications first: a result still being appended belongs to
            // a region that is still a session member, and closing under it
            // would be refused anyway.
            ConcolicResultPublisher.awaitSelectedResultPublications();
            // And then what only the end of a run can state, on the one
            // exit path every replay takes.  The seed replay also reaches
            // this through the halt after its selected result settled; a
            // focused replay does not halt, and the shutdown hook that
            // would have done it is registered only when some candidate
            // went unaddressed -- so a focused session whose every
            // candidate was addressed closed with no expression table at
            // all (2 bytes, the "{}" written when the session dir was
            // created) while its rows cited 28 refs.  One publication path
            // for both kinds of session; publishRunTotals is once per JVM.
            ConcolicResultPublisher.publishRunTotals();
            reportWorkloadSessionClose();
        }
    }

    /**
     * Closes the workload session and names a refusal on stderr.
     *
     * <p>The refusal is reported rather than thrown: it is discovered while
     * unwinding, possibly already on a failure path, and replacing the
     * workload's own outcome with it would hide the original result.</p>
     */
    private static void reportWorkloadSessionClose() {
        String refusedClose = ConcolicRegionRuntime.closeWorkloadSession();
        if (!refusedClose.isEmpty()) {
            System.err.println(refusedClose);
        }
    }

    private static void run(String[] args) throws Exception {
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
            // Class-level setup, or constructing the test instance: no
            // per-test teardown ran and none should, but the class-level
            // teardown still owes its turn.
            failure = merge(failure, thrown);
        } finally {
            failure = alsoInvoke(failure, null,
                    lifecycleMethods(testClass, Lifecycle.AFTER_ALL));
        }
        rethrow(failure);
    }

    /**
     * Finds the test method the adapter named.
     *
     * <p>Looked up over the whole hierarchy, most derived first, so that an
     * override rather than the method it overrides is what runs. A name that
     * matches nothing, a method that takes parameters, and a method no
     * vocabulary marks as a test are each refused by name.</p>
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

    /**
     * Collects the methods that hold one lifecycle role, in the order the
     * role runs them.
     */
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
                // A name already collected is the overriding declaration of
                // this one; invoking both would run the override twice.
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
     * Runs teardown that owes its turn even on a failure path, and reports
     * the failure that stands: the workload's own throwable if there is one,
     * with a teardown throwable suppressed under it.
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
