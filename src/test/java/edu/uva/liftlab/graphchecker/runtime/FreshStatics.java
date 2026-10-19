package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Test;
import org.junit.runner.Description;
import org.junit.runner.Runner;
import org.junit.runner.manipulation.Filter;
import org.junit.runner.manipulation.Filterable;
import org.junit.runner.manipulation.NoTestsRemainException;
import org.junit.runner.notification.Failure;
import org.junit.runner.notification.RunListener;
import org.junit.runner.notification.RunNotifier;
import org.junit.runners.BlockJUnit4ClassRunner;
import org.junit.runners.model.FrameworkMethod;
import org.junit.runners.model.TestClass;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.List;

/**
 * Runs each test of a class -- each row of a {@link Rows} test -- in a class
 * loader of its own for the engine's classes, so every static starts as it
 * does in the one JVM a replay is.
 */
public final class FreshStatics extends Runner implements Filterable {
    private static final String ENGINE = "edu.uva.liftlab.graphchecker.";
    private static final String ROW = "graphchecker.test.row";

    /** A test run once per row, each in a fresh loader ({@link #row}). */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.METHOD)
    public @interface Rows {
        int value();
    }

    /** The row of a {@link Rows} test this run is. */
    public static int row() {
        return Integer.parseInt(System.getProperty(ROW, "0"));
    }

    private final Class<?> type;
    private final List<FrameworkMethod> methods = new ArrayList<>();

    public FreshStatics(Class<?> type) {
        this.type = type;
        methods.addAll(new TestClass(type).getAnnotatedMethods(Test.class));
    }

    @Override
    public Description getDescription() {
        Description suite = Description.createSuiteDescription(type);
        for (FrameworkMethod method : methods) suite.addChild(of(method));
        return suite;
    }

    private Description of(FrameworkMethod method) {
        return Description.createTestDescription(type, method.getName());
    }

    @Override
    public void run(RunNotifier notifier) {
        for (FrameworkMethod method : methods) {
            Description test = of(method);
            Rows rows = method.getAnnotation(Rows.class);
            notifier.fireTestStarted(test);
            for (int row = 0; row < (rows == null ? 1 : rows.value()); row++) {
                if (!runRow(method.getName(), row, test, notifier)) break;
            }
            notifier.fireTestFinished(test);
        }
    }

    /** One row in a fresh loader; false once it failed. */
    private boolean runRow(String method, int row, Description test,
                           RunNotifier outer) {
        List<Failure> failures = new ArrayList<>();
        RunNotifier inner = new RunNotifier();
        inner.addListener(new RunListener() {
            @Override
            public void testFailure(Failure failure) {
                failures.add(failure);
            }
        });
        Thread thread = Thread.currentThread();
        ClassLoader context = thread.getContextClassLoader();
        System.setProperty(ROW, Integer.toString(row));
        try {
            Loader loader = new Loader(type);
            thread.setContextClassLoader(loader);
            Class<?> fresh = loader.loadClass(type.getName());
            BlockJUnit4ClassRunner runner = new BlockJUnit4ClassRunner(fresh);
            runner.filter(Filter.matchMethodDescription(
                    Description.createTestDescription(fresh, method)));
            runner.run(inner);
        } catch (Exception e) {
            failures.add(new Failure(test, e));
        } finally {
            thread.setContextClassLoader(context);
            System.clearProperty(ROW);
        }
        for (Failure failure : failures) {
            outer.fireTestFailure(new Failure(test, new AssertionError(
                    "row " + row + ": " + failure.getMessage(),
                    failure.getException())));
        }
        return failures.isEmpty();
    }

    @Override
    public void filter(Filter filter) throws NoTestsRemainException {
        methods.removeIf(method -> !filter.shouldRun(of(method)));
        if (methods.isEmpty()) throw new NoTestsRemainException();
    }

    private static final class Loader extends URLClassLoader {
        Loader(Class<?> type) {
            super(new URL[] {location(type), location(Identity.class)},
                    type.getClassLoader());
        }

        private static URL location(Class<?> type) {
            return type.getProtectionDomain().getCodeSource().getLocation();
        }

        @Override
        protected Class<?> loadClass(String name, boolean resolve)
                throws ClassNotFoundException {
            if (!name.startsWith(ENGINE)) return super.loadClass(name, resolve);
            synchronized (getClassLoadingLock(name)) {
                Class<?> loaded = findLoadedClass(name);
                if (loaded == null) loaded = findClass(name);
                if (resolve) resolveClass(loaded);
                return loaded;
            }
        }
    }
}
