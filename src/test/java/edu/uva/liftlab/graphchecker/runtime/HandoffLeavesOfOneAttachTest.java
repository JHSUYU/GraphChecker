package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract;
import org.junit.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * A port that crosses on a reference is one attach and several variables.
 *
 * <p>Lane 17897 and lane 11741: {@code exportAllKeys} delivers a
 * {@code BlockKey[]} on {@code XCH....resp.block-key-array}, and the mint
 * refused it for not being a primitive, so the port published no row and the
 * planned handoff read as "not reproduced" 12 and 55 times. What the
 * consumer's formula actually reads are the leaves -- {@code [i].keyId},
 * {@code [i].expiryDate} -- so each leaf is its own handoff occurrence, with
 * the leaf in its element path, and each joins its own family.</p>
 */
public class HandoffLeavesOfOneAttachTest {
    /** Two keys, each with an int and a long leaf, as the wire delivers. */
    public static final class Key {
        public int keyId;
        public long expiryDate;
        public Object unusedReference;

        Key(int keyId, long expiryDate) {
            this.keyId = keyId;
            this.expiryDate = expiryDate;
        }
    }

    /** The carrier field one declared port crosses on. */
    public static final class Carrier {
        public Object o;
        public int i;
    }

    /** An array of two objects with two primitive leaves each: four rows. */
    @Test
    public void anArrayPortMintsOneVariablePerPrimitiveLeaf()
            throws Exception {
        Carrier carrier = new Carrier();
        carrier.o = new Key[] {new Key(119980, 7L), new Key(119981, 9L)};

        List<String> paths = leafPaths(carrier, "o");

        assertEquals("two elements, two primitive leaves each", 4,
                paths.size());
        assertTrue(paths.toString(), paths.get(0).startsWith("[0]"));
        assertTrue(paths.toString(), paths.get(2).startsWith("[1]"));
        assertTrue(paths.toString(), paths.get(0).contains("int keyId"));
        assertTrue(paths.toString(),
                paths.get(1).contains("long expiryDate"));
        assertTrue("a reference leaf is not one the VM can mint on",
                paths.toString().indexOf("unusedReference") < 0);

        // Four leaves, four handoff occurrences: one variable each.
        Set<String> phases = new LinkedHashSet<>();
        for (int index = 0; index < paths.size(); index++) {
            phases.add(HandoffPhaseContract.phaseId("XCH.port",
                    "hdfs-17897/nn0#epoch0/region/REGION.a56f78d6#1",
                    1, paths.get(index)));
        }
        assertEquals("one variable per leaf", 4, phases.size());
    }

    /** A primitive destination is one leaf: itself, unchanged. */
    @Test
    public void aPrimitivePortIsStillOneLeaf() throws Exception {
        Carrier carrier = new Carrier();
        carrier.i = 119982;

        List<String> paths = leafPaths(carrier, "i");

        assertEquals(1, paths.size());
        assertTrue(paths.get(0), paths.get(0).contains("int i"));
        assertTrue("its own signature, unprefixed",
                paths.get(0).startsWith("<"));
    }

    /** An array of primitives addresses no field, and says so by silence. */
    @Test
    public void anArrayOfPrimitivesExposesNoLeaf() throws Exception {
        Carrier carrier = new Carrier();
        carrier.o = new int[] {1, 2, 3};

        assertTrue("the caller names this loss rather than minting",
                leafPaths(carrier, "o").isEmpty());
    }

    private static List<String> leafPaths(Object owner, String fieldName)
            throws Exception {
        Field element = Carrier.class.getDeclaredField(fieldName);
        Method leaves = ConcolicRegionRuntime.class.getDeclaredMethod(
                "handoffLeaves", Object.class, Field.class);
        leaves.setAccessible(true);
        List<?> found = (List<?>) leaves.invoke(null, owner, element);
        List<String> paths = new ArrayList<>();
        for (Object leaf : found) {
            Field path = leaf.getClass().getDeclaredField("path");
            path.setAccessible(true);
            paths.add((String) path.get(leaf));
        }
        return paths;
    }
}
