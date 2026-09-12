package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Test;

import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * A published object id says which object a planned receiver anchor names.
 * Two independent recordings of one workload observe that same object, so
 * they have to publish the same id for it.
 *
 * <p>The recorder's own {@code identity()} counter cannot do that: it hands
 * out numbers in the order objects happen to be touched, so hdfs-17899's
 * {@code BlockTokenSecretManager.allKeys} receiver was object 313 in one
 * recording of bug3 and object 300 in the next.  The naming under test
 * replaces that counter with the address of the object's first observation
 * plus an ordinal within that address, which is the same shape the plan
 * already uses for activation-local site occurrences.</p>
 */
public class RuntimeObjectIdentityContentTest {
    private static final String SOURCE = "hdfs-17899/target-dn#epoch0";
    private static final String METHOD =
            "<example.Keys: byte[] retrieve(int)>";
    private static final String SITE = METHOD + "#u4";
    private static final String FIELD = "<example.Keys: java.util.Map all>";

    private static String receiverAddress() {
        return RuntimeObjectIdentity.address(SOURCE, "FIELD_READ", METHOD,
                SITE, -1, FIELD, "", "fieldReceiverObjectId");
    }

    private static String valueAddress() {
        return RuntimeObjectIdentity.address(SOURCE, "FIELD_READ", METHOD,
                SITE, -1, FIELD, "", "valueObjectId");
    }

    /**
     * One object, two recordings, one published id.
     *
     * <p>The two recordings below differ in exactly what a recording decides
     * -- how many objects were touched before this one, and therefore what
     * number the counter had reached -- and agree on what the workload
     * decides: the source, the event, the method, the static site, the field
     * and the slot.  That is the difference between two recordings of one
     * obligation.</p>
     */
    @Test
    public void twoRecordingsPublishOneObjectName() {
        RuntimeObjectIdentity first = new RuntimeObjectIdentity();
        first.observe(313, receiverAddress());

        RuntimeObjectIdentity second = new RuntimeObjectIdentity();
        second.observe(300, receiverAddress());

        assertNotEquals("the recorded counters address one recording each "
                        + "and are expected to differ", 313, 300);
        assertEquals("two recordings of one object must publish one id",
                first.nameOf(313), second.nameOf(300));
    }

    /**
     * A recording that touched unrelated objects first still agrees.
     *
     * <p>This is the actual shape of the drift: the second recording rolled
     * more objects before reaching the planned receiver, so every later
     * counter value shifted.  The address does not shift with it.</p>
     */
    @Test
    public void unrelatedObjectsAheadOfItDoNotMoveTheName() {
        RuntimeObjectIdentity lean = new RuntimeObjectIdentity();
        lean.observe(313, receiverAddress());

        RuntimeObjectIdentity busy = new RuntimeObjectIdentity();
        for (int id = 200; id < 300; id++) {
            busy.observe(id, RuntimeObjectIdentity.address(SOURCE,
                    "CALL_SITE_RETURN", METHOD, METHOD + "#u" + id, -1, "",
                    "java.lang.Object", "objectId"));
        }
        busy.observe(300, receiverAddress());

        assertEquals(lean.nameOf(313), busy.nameOf(300));
    }

    /**
     * The naming stays injective: two objects of one site keep two ids.
     *
     * <p>The planned receiver index and the shared-field flow grouping both
     * ask only whether two published ids are the same object, so collapsing
     * two receivers of one field onto one id would silently merge two
     * locations.  The ordinal within the address is what prevents that.</p>
     */
    @Test
    public void twoObjectsAtOneAddressKeepTwoNames() {
        RuntimeObjectIdentity identity = new RuntimeObjectIdentity();
        identity.observe(313, receiverAddress());
        identity.observe(314, receiverAddress());

        assertNotEquals("two receivers of one field are two locations",
                identity.nameOf(313), identity.nameOf(314));
        assertEquals(2, identity.size());
    }

    /** And two recordings agree on which of the two is which. */
    @Test
    public void twoRecordingsAgreeOnBothObjectsOfOneAddress() {
        RuntimeObjectIdentity first = new RuntimeObjectIdentity();
        first.observe(313, receiverAddress());
        first.observe(314, receiverAddress());

        RuntimeObjectIdentity second = new RuntimeObjectIdentity();
        second.observe(300, receiverAddress());
        second.observe(301, receiverAddress());

        assertEquals(first.nameOf(313), second.nameOf(300));
        assertEquals(first.nameOf(314), second.nameOf(301));
    }

    /** Different slots of one event are different objects. */
    @Test
    public void theSlotSeparatesAReceiverFromItsValue() {
        RuntimeObjectIdentity identity = new RuntimeObjectIdentity();
        identity.observe(313, receiverAddress());
        identity.observe(324, valueAddress());

        assertNotEquals(identity.nameOf(313), identity.nameOf(324));
    }

    /**
     * The first observation is the address; later ones do not rename it.
     *
     * <p>One object is read at many sites, and the planned receiver index
     * refuses a carrier whose anchors resolve to different receivers, so an
     * id that moved with each read would unname every receiver read twice.
     * </p>
     */
    @Test
    public void alaterObservationDoesNotRenameTheObject() {
        RuntimeObjectIdentity identity = new RuntimeObjectIdentity();
        identity.observe(313, receiverAddress());
        int named = identity.nameOf(313);

        identity.observe(313, valueAddress());

        assertEquals(named, identity.nameOf(313));
    }

    /** 0 is "no object" and stays 0; an unobserved id keeps its value. */
    @Test
    public void absentAndUnobservedIdsAreLeftAlone() {
        RuntimeObjectIdentity identity = new RuntimeObjectIdentity();

        assertEquals(0, identity.nameOf(0));
        assertEquals(-1, identity.nameOf(-1));
        assertEquals(77, identity.nameOf(77));
    }

    /** Names are positive and clear of the recorder's counter range. */
    @Test
    public void namesArePositiveAndDistinctFromCounterValues() {
        RuntimeObjectIdentity identity = new RuntimeObjectIdentity();
        Set<Integer> names = new LinkedHashSet<>();
        for (int id = 1; id <= 500; id++) {
            identity.observe(id, RuntimeObjectIdentity.address(SOURCE,
                    "CALL_SITE_RETURN", METHOD, METHOD + "#u" + id, -1, "",
                    "java.lang.Object", "objectId"));
            int named = identity.nameOf(id);
            assertTrue("name must be positive: " + named, named > 0);
            assertTrue("name must be clear of the counter range: " + named,
                    named >= 1 << 20);
            names.add(named);
        }
        assertEquals("the naming must stay injective", 500, names.size());
    }
}
