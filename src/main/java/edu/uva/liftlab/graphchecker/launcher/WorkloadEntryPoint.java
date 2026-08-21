package edu.uva.liftlab.graphchecker.launcher;

import edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

/**
 * Main class of the workload JVM.
 *
 * <p>It does one thing before handing control to the existing JUnit runner:
 * it registers the launcher's generated configuration resource with Hadoop.
 * Doing it here, in the child, is what lets the launcher own the workload's
 * {@code Configuration} without editing the workload. The upstream test
 * builds its own {@code Configuration} in a field initializer, so the
 * resource has to be registered before the test instance exists - which is
 * exactly the moment between JVM start and the runner constructing it.</p>
 *
 * <p>Hadoop is reached reflectively and its class name is a property, not a
 * literal. GraphChecker does not depend on Hadoop, must keep compiling and
 * testing without it, and the indirection is what makes this class
 * exercisable on a classpath that has no Hadoop at all.</p>
 *
 * <h3>Registration order</h3>
 *
 * <p>Hadoop resolves a default resource by <em>last registration wins</em>,
 * and it registers most of them from a static initializer:
 * {@code Configuration} adds {@code core-default.xml} and
 * {@code core-site.xml}, {@code HdfsConfiguration} adds
 * {@code hdfs-default.xml} and {@code hdfs-site.xml}, and the HDFS pair is
 * therefore not registered until something first touches an HDFS class. A
 * resource registered here would land <em>before</em> them, and
 * {@code hdfs-default.xml} would quietly put every launcher override back to
 * its Hadoop default - the run then looks configured and is not. The classes
 * that own those defaults are named by
 * {@link #CONFIG_DEFAULTS_CLASSES_PROPERTY} and initialized first, so the
 * launcher's resource is genuinely last.</p>
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

    /** Class providing {@code addDefaultResource(String)}. */
    public static final String CONFIGURATION_CLASS_PROPERTY =
            "causynth.launcher.configuration.class";

    /** Hadoop's configuration entry point. */
    public static final String DEFAULT_CONFIGURATION_CLASS =
            "org.apache.hadoop.conf.Configuration";

    private WorkloadEntryPoint() {
    }

    public static void main(String[] args) throws Exception {
        registerOwnDefaultResources(
                System.getProperty(CONFIG_DEFAULTS_CLASSES_PROPERTY));
        addDefaultResource(
                System.getProperty(CONFIGURATION_CLASS_PROPERTY,
                        DEFAULT_CONFIGURATION_CLASS),
                System.getProperty(CONFIG_RESOURCE_PROPERTY));
        JUnitMethodRunner.main(args);
    }

    /**
     * Initializes the classes that register the workload's own default
     * configuration resources.
     *
     * <p>Loading them is the whole effect: their static initializers are what
     * call {@code Configuration.addDefaultResource}. A named class that cannot
     * be initialized is fatal, for the same reason a rejected resource is -
     * the run would continue under defaults the experiment did not ask for and
     * would still look successful.</p>
     *
     * @param classNames comma-separated class names; blank or null is a no-op
     */
    static void registerOwnDefaultResources(String classNames) {
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
     * Registers {@code resourceName} as an additional default configuration
     * resource.
     *
     * <p>Registering a distinctly named resource appends it after the site
     * files, so its values override theirs and it hides none of them. A
     * failure here is fatal on purpose: continuing would run the workload
     * under settings the experiment did not ask for, and the run would look
     * successful.</p>
     *
     * @param resourceName the resource to register; blank or null is a no-op
     */
    static void addDefaultResource(String configurationClassName,
                                   String resourceName) {
        if (resourceName == null || resourceName.trim().isEmpty()) {
            return;
        }
        try {
            Class<?> configuration = Class.forName(configurationClassName);
            Method register = configuration.getMethod("addDefaultResource",
                    String.class);
            register.invoke(null, resourceName.trim());
        } catch (InvocationTargetException failure) {
            throw new IllegalStateException(configurationClassName
                    + ".addDefaultResource(" + resourceName + ") failed",
                    failure.getCause());
        } catch (ReflectiveOperationException | RuntimeException
                | LinkageError failure) {
            throw new IllegalStateException("cannot register the launcher "
                    + "configuration resource " + resourceName + " through "
                    + configurationClassName, failure);
        }
    }
}
