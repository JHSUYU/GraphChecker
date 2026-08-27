package edu.uva.liftlab.graphchecker.launcher;

import edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

/**
 * Main class of the workload JVM.  It registers the launcher's generated
 * configuration resource with Hadoop before handing control to the JUnit
 * runner: doing it in the child is what lets the launcher own the workload's
 * {@code Configuration} without editing the workload, whose test builds its
 * own in a field initializer.  Hadoop is reached reflectively so GraphChecker
 * keeps compiling and testing with no Hadoop on the classpath.
 *
 * <p>Order is load-bearing: Hadoop resolves a default resource by
 * last-registration-wins and registers the HDFS pair from
 * {@code HdfsConfiguration}'s static initializer, so a resource registered
 * before that class is touched would be put back to its Hadoop default - the
 * run then looks configured and is not.  See
 * {@link #CONFIG_DEFAULTS_CLASSES_PROPERTY}.</p>
 */
public final class WorkloadEntryPoint {

    /** Resource name to register, or absent for no configuration override. */
    public static final String CONFIG_RESOURCE_PROPERTY =
            "causynth.launcher.config.resource";

    /**
     * Comma-separated classes whose static initializers register the
     * workload's own default resources; initialized before the launcher
     * registers its own.
     */
    public static final String CONFIG_DEFAULTS_CLASSES_PROPERTY =
            "causynth.launcher.configuration.defaults";

    private static final String CONFIGURATION_CLASS =
            "org.apache.hadoop.conf.Configuration";

    private WorkloadEntryPoint() {
    }

    public static void main(String[] args) throws Exception {
        registerOwnDefaultResources(
                System.getProperty(CONFIG_DEFAULTS_CLASSES_PROPERTY));
        addDefaultResource(System.getProperty(CONFIG_RESOURCE_PROPERTY));
        JUnitMethodRunner.main(args);
    }

    /**
     * Initializes the classes that register the workload's own defaults;
     * loading them is the whole effect.  A named class that cannot be
     * initialized is fatal - the run would otherwise continue under defaults
     * the experiment did not ask for.  Blank or null is a no-op.
     */
    private static void registerOwnDefaultResources(String classNames) {
        if (classNames == null || classNames.trim().isEmpty()) {
            return;
        }
        for (String name : classNames.split(",")) {
            String className = name.trim();
            if (className.isEmpty()) {
                continue;
            }
            try {
                Class.forName(className);
            } catch (ReflectiveOperationException | RuntimeException
                    | LinkageError failure) {
                throw new IllegalStateException("cannot initialize "
                        + className + ", which the launcher was told "
                        + "registers the workload's default configuration "
                        + "resources", failure);
            }
        }
    }

    /**
     * Registers {@code resourceName} as an additional Hadoop default resource.
     * A distinctly named resource is appended after the site files, so it
     * overrides their values and hides none.  Failure is fatal on purpose;
     * blank or null is a no-op.
     */
    private static void addDefaultResource(String resourceName) {
        if (resourceName == null || resourceName.trim().isEmpty()) {
            return;
        }
        try {
            Class<?> configuration = Class.forName(CONFIGURATION_CLASS);
            Method register = configuration.getMethod("addDefaultResource",
                    String.class);
            register.invoke(null, resourceName.trim());
        } catch (InvocationTargetException failure) {
            throw new IllegalStateException(CONFIGURATION_CLASS
                    + ".addDefaultResource(" + resourceName + ") failed",
                    failure.getCause());
        } catch (ReflectiveOperationException | RuntimeException
                | LinkageError failure) {
            throw new IllegalStateException("cannot register the launcher "
                    + "configuration resource " + resourceName + " through "
                    + CONFIGURATION_CLASS, failure);
        }
    }
}
