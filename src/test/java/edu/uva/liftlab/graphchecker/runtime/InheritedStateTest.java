package edu.uva.liftlab.graphchecker.runtime;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

/**
 * A new thread inherits the engine's state from its creator: inherit() runs
 * in Thread.init, on the creator, and its value is the child's.  On a stock
 * JDK there is no propagation to pause, so it just runs; on the concolic VM
 * the creator's objects stay unshadowed (VM smoke RegionInheritedStateSmoke).
 */
public class InheritedStateTest {
    @Test
    public void aChildInheritsWhatItsCreatorHeld() throws Exception {
        List<String> ranOn = Collections.synchronizedList(
                new ArrayList<String>());
        InheritedState<String> scope = new InheritedState<String>() {
            @Override
            protected String initialValue() {
                return "root";
            }

            @Override
            protected String inherit(String parent) {
                ranOn.add(Thread.currentThread().getName());
                return parent + "/child";
            }
        };
        scope.set("creator");
        String[] seen = new String[1];
        Thread child = new Thread(() -> seen[0] = scope.get(), "child");
        child.start();
        child.join();

        assertEquals("creator/child", seen[0]);
        assertEquals("inherit runs in Thread.init, on the creator",
                Collections.singletonList(Thread.currentThread().getName()),
                ranOn);
        assertEquals("the creator keeps its own", "creator", scope.get());
        assertFalse("a stock JDK has no propagation to pause",
                ConcolicVmBroker.pauseEngineWork());
    }
}
