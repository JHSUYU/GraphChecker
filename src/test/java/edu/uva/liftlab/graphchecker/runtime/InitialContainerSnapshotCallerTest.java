package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * The caller that tells the VM what a shared container held.
 *
 * <p>The VM can publish a whole-state carrier's initial content, but it never
 * iterates a Java collection: without this call its INITIAL version is an
 * opaque root and membership over the container's initial state is
 * undecidable. These cases pin what is sent, and pin that a container this
 * runtime cannot state exactly is declined out loud rather than approximated.
 * A snapshot that names a member the container did not hold is a false
 * premise, and one false premise makes the whole formula unsatisfiable.</p>
 */
public class InitialContainerSnapshotCallerTest {

    /** One recorded call to {@code snapshotContainerExpression}. */
    private static final class FakeVm
            implements InitialContainerSnapshot.Installer {
        private final int answer;
        Object container;
        Object[] keys;
        Object[] values;
        int kind = -1;
        int calls;

        FakeVm() {
            this(InitialContainerSnapshot.INSTALLED);
        }

        FakeVm(int answer) {
            this.answer = answer;
        }

        @Override
        public int install(Object container, Object[] keys,
                           Object[] values, int kind) {
            this.container = container;
            this.keys = keys;
            this.values = values;
            this.kind = kind;
            this.calls++;
            return answer;
        }
    }

    @Before
    public void forgetPreviousContainers() {
        InitialContainerSnapshot.forgetOfferedContainers();
        System.clearProperty(InitialContainerSnapshot.BOUND_PROPERTY);
    }

    /** A two-entry map is sent as key/value pairs in iteration order. */
    @Test
    public void aTwoEntryMapIsStatedAsItsEntries() {
        Map<Integer, String> allKeys = new LinkedHashMap<>();
        allKeys.put(7, "k7");
        allKeys.put(9, "k9");
        FakeVm vm = new FakeVm();

        InitialContainerSnapshot.Outcome outcome =
                InitialContainerSnapshot.install(vm, allKeys, null, true);

        assertTrue(outcome.reason, outcome.stated);
        assertEquals(2, outcome.entries);
        assertEquals(1, vm.calls);
        assertTrue(vm.container == allKeys);
        assertEquals(InitialContainerSnapshot.KIND_ASSOCIATIVE, vm.kind);
        assertArrayEquals(new Object[]{7, 9}, vm.keys);
        assertArrayEquals(new Object[]{"k7", "k9"}, vm.values);
    }

    /**
     * An answer this runtime does not know is never read as a stated one.
     *
     * <p>A newer VM may add an outcome that carries no base.  Defaulting to
     * "stated" would reintroduce exactly the conflation this vocabulary
     * exists to remove, one VM version later.</p>
     */
    @Test
    public void anUnknownAnswerIsNeverReadAsStated() {
        List<Object> rows = new ArrayList<Object>(Arrays.asList("a"));
        FakeVm vm = new FakeVm(97);

        InitialContainerSnapshot.Outcome outcome =
                InitialContainerSnapshot.install(vm, rows, null, true);

        assertFalse(outcome.stated);
        assertTrue(outcome.declined());
        assertEquals(InitialContainerSnapshot.VM_DECLINED, outcome.reason);
        assertEquals("UNKNOWN_97",
                InitialContainerSnapshot.skipRow(outcome, "carrier")
                        .get("answer").getAsString());
    }

    private static void assertStated(int answer, String event) {
        InitialContainerSnapshot.forgetOfferedContainers();
        List<Object> rows = new ArrayList<Object>(Arrays.asList("a"));
        InitialContainerSnapshot.Outcome outcome =
                InitialContainerSnapshot.install(new FakeVm(answer), rows,
                        null, true);
        assertTrue(InitialContainerSnapshot.answerName(answer),
                outcome.stated);
        assertFalse(InitialContainerSnapshot.answerName(answer),
                outcome.declined());
        assertEquals(event, outcome.statedEvent());
        assertEquals(InitialContainerSnapshot.answerName(answer),
                InitialContainerSnapshot.statedRow(outcome, "carrier")
                        .get("answer").getAsString());
    }

    private static void assertDeclined(int answer, String reason) {
        InitialContainerSnapshot.forgetOfferedContainers();
        List<Object> rows = new ArrayList<Object>(Arrays.asList("a"));
        InitialContainerSnapshot.Outcome outcome =
                InitialContainerSnapshot.install(new FakeVm(answer), rows,
                        null, true);
        assertFalse(InitialContainerSnapshot.answerName(answer),
                outcome.stated);
        assertTrue(InitialContainerSnapshot.answerName(answer),
                outcome.declined());
        assertEquals(reason, outcome.reason);
        assertEquals(InitialContainerSnapshot.answerName(answer),
                InitialContainerSnapshot.skipRow(outcome, "carrier")
                        .get("answer").getAsString());
    }

}
