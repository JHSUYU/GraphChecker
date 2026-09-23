package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * An ambient attach is keyed like a selected one: (port, consumer
 * occurrence, k-th attach of this element, element path).
 *
 * <p>k was the constant 1, so the four block keys target-dn's heartbeat
 * delivered in one occurrence -- one {@code convert(BlockKeyProto)} each --
 * were one variable, and a witness put every key under one key id
 * (hdfs-17899 bug1, 17967 A, B, C).</p>
 */
public class AmbientHandoffIdentityTest {
    private static final String PORT = "XCH.1174244c.resp.block-key-id";
    private static final String CONSUMER =
            "hdfs-17899/target-dn#epoch0/region/REGION.16ba41cf/ctx:Anchor:ab@HADOOP_IPC/heartbeat/idx:";

    @Before
    @After
    public void reset() {
        HandoffMint.resetForTests();
    }

    @Test
    public void eachElementOneOccurrenceReceivesIsItsOwnVariable() {
        String first = HandoffMint.ambientMintKey(PORT, CONSUMER, "keyId");
        String second = HandoffMint.ambientMintKey(PORT, CONSUMER, "keyId");
        String third = HandoffMint.ambientMintKey(PORT, CONSUMER, "keyId");
        assertFalse("two elements, two variables", first.equals(second));
        assertFalse(second.equals(third));
        assertFalse(first.equals(third));
    }

    @Test
    public void aSelectedAttachCountsOnTheOccurrenceNotTheActivation() {
        // Four activations -- one convert(BlockKeyProto) each -- folding
        // into one consumer occurrence: the count runs on across them.
        assertEquals(1, HandoffMint.nextAttach(CONSUMER, PORT, "keyId"));
        assertEquals(2, HandoffMint.nextAttach(CONSUMER, PORT, "keyId"));
        assertEquals(3, HandoffMint.nextAttach(CONSUMER, PORT, "keyId"));
        assertEquals(4, HandoffMint.nextAttach(CONSUMER, PORT, "keyId"));
        assertEquals("another consumer counts its own", 1,
                HandoffMint.nextAttach(CONSUMER + "other", PORT, "keyId"));
    }

    @Test
    public void theOrdinalIsPerElementPathAndPerConsumer() {
        String key = HandoffMint.ambientMintKey(PORT, CONSUMER, "keyId");
        String expiry = HandoffMint.ambientMintKey(PORT, CONSUMER,
                "expiryDate");
        String elsewhere = HandoffMint.ambientMintKey(PORT,
                CONSUMER + "other", "keyId");
        HandoffMint.resetForTests();
        assertEquals("the same run mints the same first key again",
                key, HandoffMint.ambientMintKey(PORT, CONSUMER, "keyId"));
        assertEquals(expiry, HandoffMint.ambientMintKey(PORT, CONSUMER,
                "expiryDate"));
        assertEquals(elsewhere, HandoffMint.ambientMintKey(PORT,
                CONSUMER + "other", "keyId"));
    }
}
