package edu.uva.liftlab.graphchecker.runtime;

import java.lang.annotation.Annotation;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Runs one JUnit 4 method without adding JUnit to GraphChecker's API.
 *
 * <p>This class is also the owner of the workload's symbolic lifetime. The
 * JUnit method is what "the workload" means for GraphChecker, so the
 * workload-wide session opens before the method starts and closes after it
 * ends -- on every exit path, including a failing test. Region entry and exit
 * no longer bound that lifetime, which is what lets one producer's exported
 * expression outlive the producer's thread.</p>
 */
public final class JUnitMethodRunner {
    private static final String EXIT_AFTER_RUN_PROPERTY =
            "causynth.junit.exit.after.run";

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
        if (!Boolean.getBoolean(EXIT_AFTER_RUN_PROPERTY)) {
            try {
                run(args);
            } finally {
                reportWorkloadSessionClose();
            }
            return;
        }
        int status = 0;
        try {
            run(args);
        } catch (Throwable failure) {
            failure.printStackTrace(System.err);
            status = 1;
        }
        // Publications first: a result still being appended belongs to a
        // region that is still a session member, and closing under it would
        // be refused anyway.
        ConcolicResultPublisher.awaitSelectedResultPublications();
        // And then what only the end of a run can state, on the one exit
        // path every replay takes.  The seed replay reached this through the
        // halt after its selected result settled; a focused replay does not
        // halt, and the shutdown hook that would have done it is registered
        // only when some candidate went unaddressed -- so a focused session
        // whose every candidate was addressed closed with no expression
        // table at all (2 bytes, the "{}" written when the session dir was
        // created) while its rows cited 28 refs.  One publication path for
        // both kinds of session; publishRunTotals is once per JVM.
        ConcolicResultPublisher.publishRunTotals();
        reportWorkloadSessionClose();
        System.exit(status);
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
        if (Boolean.getBoolean("causynth.junit.ignore.timeout")) {
            runWithoutTimeout(testClass, args[1]);
            return;
        }
        Class<?> requestClass = Class.forName("org.junit.runner.Request");
        Object request = requestClass
                .getMethod("method", Class.class, String.class)
                .invoke(null, testClass, args[1]);
        Class<?> coreClass = Class.forName("org.junit.runner.JUnitCore");
        Object core = coreClass.newInstance();
        Method run = coreClass.getMethod("run", requestClass);
        Object result = run.invoke(core, request);
        Class<?> resultClass = Class.forName("org.junit.runner.Result");
        boolean successful = (Boolean) resultClass
                .getMethod("wasSuccessful").invoke(result);
        if (!successful) {
            @SuppressWarnings("unchecked")
            List<Object> failures = (List<Object>) resultClass
                    .getMethod("getFailures").invoke(result);
            for (Object failure : failures) {
                System.err.println(failure);
            }
            throw new AssertionError("JUnit method failed: "
                    + args[0] + "#" + args[1]);
        }
    }

    private static void runWithoutTimeout(Class<?> testClass,
                                          String methodName)
            throws Exception {
        Object test = testClass.newInstance();
        Throwable failure = null;
        try {
            invokeLifecycle(test, testClass, true,
                    "org.junit.Before", "org.junit.jupiter.api.BeforeEach");
            invoke(test, testClass.getMethod(methodName));
        } catch (Throwable throwable) {
            failure = throwable;
        } finally {
            try {
                invokeLifecycle(test, testClass, false,
                        "org.junit.jupiter.api.AfterEach", "org.junit.After");
            } catch (Throwable throwable) {
                if (failure == null) {
                    failure = throwable;
                } else {
                    failure.addSuppressed(throwable);
                }
            }
        }
        if (failure instanceof Exception) {
            throw (Exception) failure;
        }
        if (failure instanceof Error) {
            throw (Error) failure;
        }
        if (failure != null) {
            throw new RuntimeException(failure);
        }
    }

    private static void invokeLifecycle(Object test, Class<?> testClass,
                                        boolean superclassFirst,
                                        String... annotationNames)
            throws Throwable {
        List<Class<?>> hierarchy = new ArrayList<>();
        for (Class<?> type = testClass; type != null;
             type = type.getSuperclass()) {
            hierarchy.add(type);
        }
        if (superclassFirst) {
            Collections.reverse(hierarchy);
        }
        for (Class<?> type : hierarchy) {
            for (Method method : type.getDeclaredMethods()) {
                if (hasAnnotation(method, annotationNames)) {
                    method.setAccessible(true);
                    invoke(test, method);
                }
            }
        }
    }

    private static boolean hasAnnotation(Method method, String... names) {
        for (Annotation annotation : method.getDeclaredAnnotations()) {
            for (String name : names) {
                if (name.equals(annotation.annotationType().getName())) {
                    return true;
                }
            }
        }
        return false;
    }

    private static void invoke(Object receiver, Method method)
            throws Throwable {
        try {
            method.invoke(receiver);
        } catch (InvocationTargetException exception) {
            throw exception.getCause();
        }
    }
}
