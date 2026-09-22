package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import edu.uva.liftlab.graphchecker.plan.WorkStartSites;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;
import org.junit.Test;

/**
 * Every timed-wait shape the weave replaces has its stand-in, with exactly
 * the signature the weave calls: the receiver first, the call's own
 * parameters, the site last, and the call's return type.  A mismatch is a
 * NoSuchMethodError inside a replay, which is the one place it cannot be
 * seen.
 */
public class TimedWaitsAbiTest {
    @Test
    public void everyShapeHasItsStandIn() throws Exception {
        for (WorkStartSites.TimedWait shape : WorkStartSites.timedWaits()) {
            List<Class<?>> parameters = new ArrayList<Class<?>>();
            for (String name : shape.replacementParameters()) {
                parameters.add(type(name));
            }
            Method method = TimedWaits.class.getMethod(shape.replacement,
                    parameters.toArray(new Class<?>[0]));
            assertTrue(shape.replacement + " is static",
                    Modifier.isStatic(method.getModifiers()));
            assertEquals(shape.replacement + " returns what the call did",
                    type(shape.returns), method.getReturnType());
        }
        assertEquals(WorkStartSites.TIMED_WAITS_CLASS,
                TimedWaits.class.getName());
    }

    private static Class<?> type(String name) throws ClassNotFoundException {
        switch (name) {
            case "void": return void.class;
            case "long": return long.class;
            case "int": return int.class;
            case "boolean": return boolean.class;
            default: return Class.forName(name);
        }
    }
}
