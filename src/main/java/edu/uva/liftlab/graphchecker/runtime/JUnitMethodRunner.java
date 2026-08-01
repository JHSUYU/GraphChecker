package edu.uva.liftlab.graphchecker.runtime;

import java.lang.reflect.Method;
import java.util.List;

/** Runs one JUnit 4 method without adding JUnit to GraphChecker's API. */
public final class JUnitMethodRunner {
    private JUnitMethodRunner() {
    }

    public static void main(String[] args) throws Exception {
        if (args == null || args.length != 2) {
            throw new IllegalArgumentException(
                    "usage: JUnitMethodRunner <class> <method>");
        }
        Class<?> testClass = Class.forName(args[0]);
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
}
