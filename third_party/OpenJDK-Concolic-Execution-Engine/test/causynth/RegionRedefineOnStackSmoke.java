import java.io.File;
import java.io.FileOutputStream;
import java.lang.instrument.Instrumentation;
import java.lang.management.ManagementFactory;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.List;
import java.util.jar.Attributes;
import java.util.jar.JarOutputStream;
import java.util.jar.Manifest;

/**
 * A redefined class's old methods live while a Zero frame still runs them.
 *
 * <p>mockito-inline retransforms every superclass of a mocked type,
 * java.lang.Object included, while other threads sit in Object.wait.  Zero's
 * interpreter frames have no pc and no code blob, and frame::metadata_do
 * asked for both, so MetadataOnStackMark marked no interpreted method on any
 * stack: the redefinition kept no previous version of Object, and the next
 * class-unloading GC freed the old methods under the waiting thread's frames
 * and crashed walking them (an HDFS seed replay, OopMapCache::lookup through
 * the freed holder).  Here a thread waits in Object.wait while this JVM
 * attaches an agent to itself, retransforms Object and collects; the thread
 * must then wake and return through the old frames, and a collection after it
 * returned frees the old version.</p>
 */
public final class RegionRedefineOnStackSmoke {
    private static volatile Instrumentation instrumentation;
    private static final Object LOCK = new Object();
    private static boolean released;

    public static void agentmain(String args, Instrumentation inst) {
        instrumentation = inst;
    }

    public static void main(String[] args) throws Exception {
        attachSelf();
        require(instrumentation != null, "the agent did not start");
        require(instrumentation.isRetransformClassesSupported()
                && instrumentation.isModifiableClass(Object.class),
                "Object cannot be retransformed here");

        final List<Throwable> failures = new ArrayList<Throwable>();
        Thread waiter = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    synchronized (LOCK) {
                        while (!released) {
                            LOCK.wait();
                        }
                    }
                } catch (Throwable t) {
                    failures.add(t);
                }
            }
        }, "old-wait");
        waiter.start();
        while (waiter.getState() != Thread.State.WAITING) {
            Thread.sleep(10);
        }

        for (int round = 0; round < 3; round++) {
            instrumentation.retransformClasses(Object.class);
            churn();
            System.gc();
        }
        synchronized (LOCK) {
            released = true;
            LOCK.notifyAll();
        }
        waiter.join(60000);
        require(!waiter.isAlive(), "the waiter never returned from Object.wait");
        require(failures.isEmpty(), "the waiter failed: " + failures);
        // The old versions are off every stack now: this collection frees
        // them, and nothing may still walk them.
        churn();
        System.gc();
        System.gc();
        System.out.println("RegionRedefineOnStackSmoke passed");
    }

    // Loads and drops a few classes so the collection has metadata to free
    // and the freed blocks are reused.
    private static void churn() throws Exception {
        for (int i = 0; i < 8; i++) {
            ClassLoader loader = new URLClassLoader(new URL[] {
                    RegionRedefineOnStackSmoke.class.getProtectionDomain()
                            .getCodeSource().getLocation() }, null);
            Class<?> c = Class.forName("RegionRedefineOnStackSmoke", true,
                    loader);
            require(c != RegionRedefineOnStackSmoke.class, "not a fresh copy");
        }
    }

    // The attach API from this image's tools.jar, by reflection, onto an
    // agent jar written here whose Agent-Class is this class.
    private static void attachSelf() throws Exception {
        File jar = File.createTempFile("redefine-on-stack", ".jar");
        jar.deleteOnExit();
        Manifest manifest = new Manifest();
        Attributes main = manifest.getMainAttributes();
        main.put(Attributes.Name.MANIFEST_VERSION, "1.0");
        main.putValue("Agent-Class", RegionRedefineOnStackSmoke.class.getName());
        main.putValue("Can-Redefine-Classes", "true");
        main.putValue("Can-Retransform-Classes", "true");
        new JarOutputStream(new FileOutputStream(jar), manifest).close();

        File tools = new File(System.getProperty("java.home"),
                "../lib/tools.jar");
        require(tools.isFile(), "no tools.jar at " + tools);
        ClassLoader attach = new URLClassLoader(
                new URL[] { tools.toURI().toURL() });
        Class<?> vm = attach.loadClass("com.sun.tools.attach.VirtualMachine");
        String pid = ManagementFactory.getRuntimeMXBean().getName()
                .split("@")[0];
        Object machine = vm.getMethod("attach", String.class).invoke(null, pid);
        Method load = vm.getMethod("loadAgent", String.class);
        load.invoke(machine, jar.getAbsolutePath());
        vm.getMethod("detach").invoke(machine);
    }

    private static void require(boolean condition, String message) {
        if (!condition) {
            throw new AssertionError(message);
        }
    }
}
