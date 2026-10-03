package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.net.URL;
import java.net.URLClassLoader;

import static org.junit.Assert.assertEquals;

/**
 * The verifier gate passes over a woven class only when it cannot load in the
 * workload anyway: a class it names is on no classpath and is none of the
 * engine's.  Anything else that fails to link is a refusal.
 */
public class VerifyWovenClassesTest {
    @Test
    public void onlyAMissingNonEngineClassIsUnloadable() {
        ClassLoader loader = new URLClassLoader(new URL[0],
                VerifyWovenClassesTest.class.getClassLoader());
        Object[][] table = {
            {new NoClassDefFoundError("org/eclipse/jetty/servlet/Missing"),
                true},
            // A hook class the weave names must be there: never passed over.
            {new NoClassDefFoundError(
                    "edu/uva/liftlab/graphchecker/runtime/Missing"), false},
            // Present on the classpath: the failure is the class's own.
            {new NoClassDefFoundError("java/lang/String"), false},
            {new NoClassDefFoundError("Could not initialize class a.B"),
                false},
            {new VerifyError("Bad type on operand stack"), false},
        };
        for (Object[] row : table) {
            assertEquals(String.valueOf(row[0]), row[1],
                    VerifyWovenClasses.unloadable(loader, (Throwable) row[0]));
        }
    }
}
