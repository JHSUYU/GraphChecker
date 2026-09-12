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
        private final boolean answer;
        Object container;
        Object[] keys;
        Object[] values;
        int kind = -1;
        int calls;

        FakeVm() {
            this(true);
        }

        FakeVm(boolean answer) {
            this.answer = answer;
        }

        @Override
        public boolean install(Object container, Object[] keys,
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

        assertTrue(outcome.reason, outcome.installed);
        assertEquals(2, outcome.entries);
        assertEquals(1, vm.calls);
        assertTrue(vm.container == allKeys);
        assertEquals(InitialContainerSnapshot.KIND_ASSOCIATIVE, vm.kind);
        assertArrayEquals(new Object[]{7, 9}, vm.keys);
        assertArrayEquals(new Object[]{"k7", "k9"}, vm.values);
    }

    /** A two-element list is sent as values alone, in index order. */
    @Test
    public void aTwoElementListIsStatedInIndexOrder() {
        List<String> rows = new ArrayList<>(Arrays.asList("e0", "e1"));
        FakeVm vm = new FakeVm();

        InitialContainerSnapshot.Outcome outcome =
                InitialContainerSnapshot.install(vm, rows, null, true);

        assertTrue(outcome.reason, outcome.installed);
        assertEquals(2, outcome.entries);
        assertEquals(InitialContainerSnapshot.KIND_INDEXED, vm.kind);
        assertNull(vm.keys);
        assertArrayEquals(new Object[]{"e0", "e1"}, vm.values);
    }

    /**
     * Past the VM's own bound nothing is sent, and the row says how many
     * members went unstated - "held nothing" and "held more than this engine
     * states" are different facts.
     */
    @Test
    public void aContainerPastTheBoundIsDeclinedWithItsSize() {
        System.setProperty(InitialContainerSnapshot.BOUND_PROPERTY, "1");
        Map<Integer, String> wide = new LinkedHashMap<>();
        wide.put(1, "a");
        wide.put(2, "b");
        FakeVm vm = new FakeVm();

        InitialContainerSnapshot.Outcome outcome =
                InitialContainerSnapshot.install(vm, wide, null, true);

        assertFalse(outcome.installed);
        assertTrue(outcome.declined());
        assertEquals(InitialContainerSnapshot.OVER_BOUND, outcome.reason);
        assertEquals(2, outcome.entries);
        assertEquals(0, vm.calls);

        JsonObject row = InitialContainerSnapshot.skipRow(outcome,
                "MAP_STATE BlockTokenSecretManager#allKeys");
        assertEquals(InitialContainerSnapshot.SKIPPED_EVENT,
                row.get("kind").getAsString());
        assertEquals(InitialContainerSnapshot.OVER_BOUND,
                row.get("reason").getAsString());
        assertEquals(2, row.get("entries").getAsInt());
        assertEquals(1, row.get("maxEntries").getAsInt());
    }

    /**
     * A class whose mutations the VM's container algebra does not version is
     * declined: a snapshot of it would be a constant that stops being true at
     * the first unwatched write.
     */
    @Test
    public void aClassTheRecorderDoesNotWatchIsDeclined() {
        Map<Integer, String> sorted = new TreeMap<>();
        sorted.put(1, "a");
        FakeVm vm = new FakeVm();

        InitialContainerSnapshot.Outcome outcome =
                InitialContainerSnapshot.install(vm, sorted, null, true);

        assertFalse(outcome.installed);
        assertEquals(InitialContainerSnapshot.CLASS_NOT_ALLOWLISTED,
                outcome.reason);
        assertEquals("java.util.TreeMap", outcome.detail);
        assertEquals(0, vm.calls);
    }

    /** A pointer carrier over a container states nothing, and says so. */
    @Test
    public void aCarrierThatIsNotWholeStateIsDeclined() {
        FakeVm vm = new FakeVm();
        InitialContainerSnapshot.Outcome outcome =
                InitialContainerSnapshot.install(vm,
                        new LinkedHashMap<Integer, String>(), null, false);

        assertFalse(outcome.installed);
        assertEquals(InitialContainerSnapshot.NOT_A_WHOLE_STATE_CARRIER,
                outcome.reason);
        assertEquals(0, vm.calls);
    }

    /**
     * A pointer selection of a container must not spend the one chance the
     * whole-state selection has to state its content.
     */
    @Test
    public void aPointerSelectionDoesNotConsumeTheWholeStateOffer() {
        Map<Integer, String> allKeys = new LinkedHashMap<>();
        allKeys.put(7, "k7");
        FakeVm vm = new FakeVm();

        assertEquals(InitialContainerSnapshot.NOT_A_WHOLE_STATE_CARRIER,
                InitialContainerSnapshot.install(vm, allKeys, null, false)
                        .reason);
        InitialContainerSnapshot.Outcome whole =
                InitialContainerSnapshot.install(vm, allKeys, null, true);
        assertTrue(whole.reason, whole.installed);
        assertEquals(1, vm.calls);
        // And the pointer answer is given once, not at every access.
        assertFalse(InitialContainerSnapshot.install(
                vm, new LinkedHashMap<Integer, String>(), null, false)
                .reason.isEmpty());
    }

    /** A scalar carrier has no content, and is not worth a row. */
    @Test
    public void aScalarCarrierSaysNothing() {
        FakeVm vm = new FakeVm();
        InitialContainerSnapshot.Outcome outcome =
                InitialContainerSnapshot.install(vm, "a value", null, true);

        assertFalse(outcome.installed);
        assertFalse(outcome.declined());
        assertEquals(0, vm.calls);
    }

    /**
     * The chain may only be installed before the INITIAL version exists, so a
     * container is offered exactly once however often it is selected.
     */
    @Test
    public void aContainerIsOfferedOnlyOnce() {
        Map<Integer, String> allKeys = new LinkedHashMap<>();
        allKeys.put(7, "k7");
        FakeVm vm = new FakeVm();

        assertTrue(InitialContainerSnapshot.install(vm, allKeys, null, true)
                .installed);
        InitialContainerSnapshot.Outcome second =
                InitialContainerSnapshot.install(vm, allKeys, null, true);
        assertFalse(second.installed);
        assertFalse(second.declined());
        assertEquals(1, vm.calls);
    }

    /** A synchronized view delegates both questions to what it wraps. */
    @Test
    public void aSynchronizedViewIsStatedThroughItsBackingMap() {
        Map<Integer, String> backing = new LinkedHashMap<>();
        backing.put(3, "c");
        Map<Integer, String> guarded =
                Collections.synchronizedMap(backing);
        FakeVm vm = new FakeVm();

        InitialContainerSnapshot.Outcome outcome =
                InitialContainerSnapshot.install(vm, guarded, null, true);

        assertTrue(outcome.reason, outcome.installed);
        // The snapshot is attached to the object the carrier names.
        assertTrue(vm.container == guarded);
        assertArrayEquals(new Object[]{3}, vm.keys);
    }

    /** The content is read while the workload's own monitor is held. */
    @Test
    public void theContentIsReadUnderTheDeclaringReceiversMonitor()
            throws Exception {
        final Map<Integer, String> allKeys = new LinkedHashMap<>();
        allKeys.put(1, "a");
        final Object receiver = new Object();
        final boolean[] heldDuringTheWalk = {false};
        InitialContainerSnapshot.Installer vm =
                (container, keys, values, kind) -> {
                    heldDuringTheWalk[0] =
                            Thread.holdsLock(receiver);
                    return true;
                };

        assertTrue(InitialContainerSnapshot.install(
                vm, allKeys, receiver, true).installed);
        assertTrue(heldDuringTheWalk[0]);
    }

    /** A VM that refuses the call leaves the opaque root and says so. */
    @Test
    public void aRefusedCallIsReportedRatherThanAssumed() {
        Map<Integer, String> allKeys = new LinkedHashMap<>();
        allKeys.put(1, "a");
        FakeVm vm = new FakeVm(false);

        InitialContainerSnapshot.Outcome outcome =
                InitialContainerSnapshot.install(vm, allKeys, null, true);

        assertFalse(outcome.installed);
        assertEquals(InitialContainerSnapshot.VM_DECLINED, outcome.reason);
    }

    /** A stock JDK has no such entry point, and that is a declared answer. */
    @Test
    public void aVmWithoutTheEntryPointIsDeclared() {
        InitialContainerSnapshot.Outcome outcome =
                InitialContainerSnapshot.install(null,
                        new LinkedHashMap<Integer, String>(), null, true);

        assertFalse(outcome.installed);
        assertEquals(InitialContainerSnapshot.VM_DECLINED, outcome.reason);
    }
}
