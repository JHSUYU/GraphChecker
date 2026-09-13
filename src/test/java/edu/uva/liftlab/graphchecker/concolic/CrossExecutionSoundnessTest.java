package edu.uva.liftlab.graphchecker.concolic;

import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
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
     * An INITIAL arm survives while any case of its host activation may run.
     *
     * <p>The snapshot is what the object held when that activation was
     * entered.  A marker that idles one of the activation's cases has not
     * said the activation never ran, so the snapshot still names a value;
     * only idling all of them does.</p>
     */
    @Test
    public void initialArmDiesOnlyWhenEveryHostCaseIsIdled() {
        List<String> hosts = Arrays.asList(HOST_CASE_A, HOST_CASE_B);
        assertFalse(ConcolicSmtComposer.armIdled(
                Collections.<String>emptyList(), hosts,
                Collections.singleton(HOST_CASE_A)));
        assertTrue(ConcolicSmtComposer.armIdled(
                Collections.<String>emptyList(), hosts,
                new LinkedHashSet<>(hosts)));
        // An arm with no host is a writer arm and answers to its writer.
        assertFalse(ConcolicSmtComposer.armIdled(
                Collections.singletonList(WRITER_CASE),
                Collections.<String>emptyList(),
                new LinkedHashSet<>(hosts)));
        assertTrue(ConcolicSmtComposer.armIdled(
                Collections.singletonList(WRITER_CASE),
                Collections.<String>emptyList(),
                Collections.singleton(WRITER_CASE)));
    }

    /**
     * A read whose every arm the marker idles is starved, and the INITIAL arm
     * among them is named: it is the one a reader would otherwise take for a
     * retained prior version.
     */
    @Test
    public void closureNamesTheInitialArmItsMarkerUnhosted() {
        Map<String, Map<String, List<String>>> arms = new LinkedHashMap<>();
        Map<String, List<String>> read = new LinkedHashMap<>();
        read.put(WRITER_ARM, Collections.singletonList(WRITER_CASE));
        read.put(INITIAL_ARM, Collections.<String>emptyList());
        arms.put("read_key_id", read);
        Map<String, List<String>> hosts = new LinkedHashMap<>();
        hosts.put(INITIAL_ARM, Collections.singletonList(HOST_CASE_A));

        ConcolicSmtComposer.FaultIdleClosure idled =
                ConcolicSmtComposer.faultIdleClosure(
                        Arrays.asList(WRITER_CASE, HOST_CASE_A), arms,
                        Collections.<String, List<String>>emptyMap(), hosts);

        assertEquals(Collections.singleton("read_key_id"),
                idled.starvedReads);
        assertEquals(Collections.singletonList(INITIAL_ARM),
                idled.hostIdledInitialArms.get("read_key_id"));

        // The host still runs: the INITIAL arm is a value, and the read is
        // not starved even though its writer is gone.
        ConcolicSmtComposer.FaultIdleClosure alive =
                ConcolicSmtComposer.faultIdleClosure(
                        Collections.singletonList(WRITER_CASE), arms,
                        Collections.<String, List<String>>emptyMap(), hosts);
        assertTrue(alive.starvedReads.isEmpty());
        assertTrue(alive.hostIdledInitialArms.isEmpty());
    }

    /**
     * Only a recorded literal compares across replay groups.
     *
     * <p>A symbolic term is the same expression in every group by
     * construction, and a per-group VM witness is scoped to its own JVM, so
     * neither says anything about whether the groups agree.</p>
     */
    @Test
    public void onlyRecordedLiteralsCompareAcrossGroups() {
        assertTrue(ConcolicSmtComposer.isLiteralTerm("119980"));
        assertTrue(ConcolicSmtComposer.isLiteralTerm("(- 7)"));
        assertTrue(ConcolicSmtComposer.isLiteralTerm("(VInt 1210003169)"));
        assertTrue(ConcolicSmtComposer.isLiteralTerm("(VLong 1789288850045)"));
        assertTrue(ConcolicSmtComposer.isLiteralTerm("true"));
        assertFalse(ConcolicSmtComposer.isLiteralTerm(
                "merged_boundary__7ee24ab4360a529f9b76"));
        assertFalse(ConcolicSmtComposer.isLiteralTerm("(+ x 1)"));
        assertFalse(ConcolicSmtComposer.isLiteralTerm(null));
        assertFalse(ConcolicSmtComposer.isLiteralTerm(""));
    }

    /** The node an occurrence names is the side of the wire it sits on. */
    @Test
    public void occurrenceNamesItsNode() {
        assertEquals("hdfs-17899/target-dn#epoch0",
                ConcolicSmtComposer.occurrenceSourceKey(
                        "hdfs-17899/target-dn#epoch0/region/REGION.1f69#6#a1"));
        assertEquals("hdfs-17899/nn0#epoch0",
                ConcolicSmtComposer.occurrenceSourceKey(
                        "hdfs-17899/nn0#epoch0/region/REGION.695d#6#a1"));
        assertEquals("", ConcolicSmtComposer.occurrenceSourceKey("nothing"));
        assertEquals("", ConcolicSmtComposer.occurrenceSourceKey(null));
    }

    /** A port's declared field is joined on the flow id it ends with. */
    @Test
    public void portJoinsItsFlowBySuffix() {
        Map<String, String> fields = new LinkedHashMap<>();
        fields.put("block-key-id",
                "org.apache.hadoop.security.token.delegation"
                        + ".DelegationKey#keyId");
        fields.put("block-key-expiry-date",
                "org.apache.hadoop.security.token.delegation"
                        + ".DelegationKey#expiryDate");
        assertEquals("org.apache.hadoop.security.token.delegation"
                        + ".DelegationKey#keyId",
                ConcolicSmtComposer.consumerFieldOf(
                        "XCH.1174244c.resp.block-key-id", fields));
        assertEquals("", ConcolicSmtComposer.consumerFieldOf(
                "XCH.da84e470.req.data-encryption-key-id", fields));
    }

    /** One bound handoff answers for the flow, not for every receiver. */
    @Test
    public void oneBoundHandoffStillAnswersForTheFlow() {
        com.google.gson.JsonArray ledger = new com.google.gson.JsonArray();
        ledger.add(row("XCH.a.resp.block-key-id", true));
        ledger.add(row("XCH.a.resp.block-key-id", false));
        assertEquals(Collections.<String>emptyList(),
                ConcolicSmtComposer.unboundDeclaredPorts(ledger));

        com.google.gson.JsonArray none = new com.google.gson.JsonArray();
        none.add(row("XCH.a.resp.block-key-id", false));
        assertEquals(Collections.singletonList("XCH.a.resp.block-key-id"),
                ConcolicSmtComposer.unboundDeclaredPorts(none));
    }

    private static com.google.gson.JsonObject row(String port, boolean bound) {
        com.google.gson.JsonObject row = new com.google.gson.JsonObject();
        row.addProperty("portId", port);
        row.addProperty("declaredWireFlow", true);
        row.addProperty("valueBound", bound);
        return row;
    }

    /** What the closure returns is a finding, not a working set. */
    @Test
    public void closureSetsAreUnmodifiable() {
        Set<String> idled = ConcolicSmtComposer.faultIdleClosure(
                Collections.singletonList(WRITER_CASE),
                Collections.<String, Map<String, List<String>>>emptyMap(),
                Collections.<String, List<String>>emptyMap())
                .idledCaseSelectors;
        try {
            idled.add("case_selector__other");
            throw new AssertionError("closure set accepted a write");
        } catch (UnsupportedOperationException expected) {
            assertTrue(expected instanceof UnsupportedOperationException);
        }
    }
}
