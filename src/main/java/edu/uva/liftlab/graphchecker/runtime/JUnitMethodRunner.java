package edu.uva.liftlab.graphchecker.runtime;

import java.lang.annotation.Annotation;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/** Runs one JUnit 4 method without adding JUnit to GraphChecker's API. */
public final class JUnitMethodRunner {
    private static final String EXIT_AFTER_RUN_PROPERTY =
            "causynth.junit.exit.after.run";

    private JUnitMethodRunner() {
    }

    public static void main(String[] args) throws Exception {
        if (!Boolean.getBoolean(EXIT_AFTER_RUN_PROPERTY)) {
            run(args);
            return;
        }
        int status = 0;
        try {
            run(args);
        } catch (Throwable failure) {
            failure.printStackTrace(System.err);
            status = 1;
        }
        ConcolicRegionRuntime.awaitSelectedResultPublications();
        System.exit(status);
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
            invokeLifecycle(test, testClass, "org.junit.Before", true);
            invoke(test, testClass.getMethod(methodName));
        } catch (Throwable throwable) {
            failure = throwable;
        } finally {
            try {
                invokeLifecycle(test, testClass, "org.junit.After", false);
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
                                        String annotationName,
                                        boolean superclassFirst)
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
                if (hasAnnotation(method, annotationName)) {
                    method.setAccessible(true);
                    invoke(test, method);
                }
            }
        }
    }

    private static boolean hasAnnotation(Method method, String name) {
        for (Annotation annotation : method.getDeclaredAnnotations()) {
            if (name.equals(annotation.annotationType().getName())) {
                return true;
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
