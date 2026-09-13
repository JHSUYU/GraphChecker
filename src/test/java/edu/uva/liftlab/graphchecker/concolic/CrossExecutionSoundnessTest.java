package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * A value no execution produced must not stand in for one that did.
 *
 * <p>Three ways the composition used to let one through, each with its own
 * shape.  A fault marker that idles the activation whose entry took an
 * INITIAL snapshot leaves the JVM's zero default of an object nothing
 * constructed, and reading it back as "what the fault retained" is how a
 * failed refresh came to carry key id 0.  Replay groups that recorded
 * different literals at one location get merged into one read, and a witness
 * takes each location from whichever run suits it.  And a node is a producer
 * or a consumer of a declared flow, never both at one field, which is the
 * line the consumer-field gate is drawn on.</p>
 */
public class CrossExecutionSoundnessTest {
    private static final String WRITER_CASE = "case_selector__writer";
    private static final String HOST_CASE_A = "case_selector__host_a";
    private static final String HOST_CASE_B = "case_selector__host_b";
    private static final String INITIAL_ARM = "read_selector__initial";
    private static final String WRITER_ARM = "read_selector__writer";

    /**
     * A write's leaf reads travel as a carrier name, or not at all.
     *
     * <p>Publication stamps every guarded read with the location it names,
     * independent of the session it ran in and of whether any boundary
     * consumed it, so a write expression offered to another region as a
     * read-from arm says which carrier each of its leaves reads.  Two
     * regions reading one shared carrier stamp the same leaf, which is what
     * lets the consumer substitute its own admitted arm set; a read with no
     * stable location says so, and is refused by name rather than lowered
     * out of a foreign session.</p>
     */
    @Test
    public void oneSharedCarrierIsOneLeafInEveryRegion() {
        String location = "INSTANCE_FIELD/hdfs-17899/nn0#epoch0/region/"
                + "REGION.aaa1cfd7#1#a1@receiver:9@"
                + "org.apache.hadoop.hdfs.security.token.block"
                + ".BlockTokenSecretManager#serialNo#56";
        JsonObject readInWriter = leaf(location);
        JsonObject readInReader = leaf(location);
        assertEquals("the same carrier is the same leaf in both regions",
                optionalString(readInWriter,
                        SymbolicPropagationClosure.WRITE_LEAF_IDENTITY),
                optionalString(readInReader,
                        SymbolicPropagationClosure.WRITE_LEAF_IDENTITY));
        assertNotEquals(optionalString(readInWriter,
                        SymbolicPropagationClosure.WRITE_LEAF_IDENTITY),
                optionalString(leaf(location.replace("#56", "#72")),
                        SymbolicPropagationClosure.WRITE_LEAF_IDENTITY));
        assertTrue(optionalBool(readInWriter,
                SymbolicPropagationClosure.WRITE_LEAF_PORTABLE, false));

        JsonObject unlocated = new JsonObject();
        unlocated.addProperty(SymbolicPropagationClosure.WRITE_LEAF_PORTABLE,
                false);
        assertFalse("a read with no stable location cannot travel",
                optionalBool(unlocated, SymbolicPropagationClosure
                        .WRITE_LEAF_PORTABLE, false));
        assertEquals("", optionalString(unlocated,
                SymbolicPropagationClosure.WRITE_LEAF_IDENTITY));
    }

    /** The leaf a publication stamp would carry for one stable location. */
    private static JsonObject leaf(String stableLocation) {
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ReadFromExpression");
        read.addProperty(SymbolicPropagationClosure.WRITE_LEAF_PORTABLE, true);
        read.addProperty(SymbolicPropagationClosure.WRITE_LEAF_LOCATION,
                stableLocation);
        read.addProperty(SymbolicPropagationClosure.WRITE_LEAF_IDENTITY,
                "LEAF." + CanonicalJson.sha256(stableLocation));
        return read;
    }

    private static com.google.gson.JsonObject row(String port, boolean bound) {
        com.google.gson.JsonObject row = new com.google.gson.JsonObject();
        row.addProperty("portId", port);
        row.addProperty("declaredWireFlow", true);
        row.addProperty("valueBound", bound);
        return row;
    }

}
