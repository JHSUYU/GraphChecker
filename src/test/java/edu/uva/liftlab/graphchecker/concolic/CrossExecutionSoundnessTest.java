package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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

    /**
     * A case-private read is not missing its own siblings' writes.
     *
     * <p>The nn0 {@code updateKeys()} occurrence is lowered as three local
     * cases -- the recorded one and the two the clock-root flips produced --
     * and each of its reads of {@code serialNo} / {@code currentKey} /
     * {@code nextKey} is lowered inside one of them, with that case as its
     * activation guard; the consumer merges the three per-case reads over the
     * occurrence's exactly-one partition.  Asked per read, the gate used to
     * name the other two cases of every one of the 21 such reads: 42 refusals
     * of a composition in which each case reads exactly what it wrote.</p>
     *
     * <p>The fatal read is the shape the gate is for.  It lives in the target
     * DataNode's {@code retrieveDataEncryptionKey}, is demanded whichever case
     * of the target's {@code addKeys} runs, and carries arms from only one of
     * them -- so the other two really would leave it at its INITIAL map.</p>
     */
    @Test
    public void siblingCasesOfACasePrivateReadAreNotUnlinked() {
        Set<String> updateKeys = new LinkedHashSet<>(Arrays.asList(
                "case_selector__c69de9c3", "case_selector__a7c0aa52",
                "case_selector__dc645336"));

        // The serialNo read lowered inside the recorded case: its siblings
        // cannot be selected while it is demanded.
        Set<String> recordedCaseRead = Collections.singleton(
                "case_selector__c69de9c3");
        assertTrue(ConcolicSmtComposer.writerCaseExclusiveOfRead(
                updateKeys, recordedCaseRead, "case_selector__a7c0aa52"));
        assertTrue(ConcolicSmtComposer.writerCaseExclusiveOfRead(
                updateKeys, recordedCaseRead, "case_selector__dc645336"));

        // ... and the same read under each flip case.
        assertTrue(ConcolicSmtComposer.writerCaseExclusiveOfRead(updateKeys,
                Collections.singleton("case_selector__a7c0aa52"),
                "case_selector__c69de9c3"));
        assertTrue(ConcolicSmtComposer.writerCaseExclusiveOfRead(updateKeys,
                Collections.singleton("case_selector__dc645336"),
                "case_selector__c69de9c3"));

        // The case that owns the read is never excluded by itself.
        assertFalse(ConcolicSmtComposer.writerCaseExclusiveOfRead(
                updateKeys, recordedCaseRead, "case_selector__c69de9c3"));

        // The fatal read: owned by a case of another occurrence, so every
        // addKeys case has to own an arm of it.
        Set<String> addKeys = new LinkedHashSet<>(Arrays.asList(
                "case_selector__6e03d61d", "case_selector__33f0a2fe",
                "case_selector__385409e3"));
        assertFalse(ConcolicSmtComposer.writerCaseExclusiveOfRead(addKeys,
                Collections.singleton("case_selector__44b881f9"),
                "case_selector__33f0a2fe"));

        // A read demanded under a case of this partition and one outside it
        // is not private to the partition either.
        assertFalse(ConcolicSmtComposer.writerCaseExclusiveOfRead(updateKeys,
                new LinkedHashSet<>(Arrays.asList("case_selector__c69de9c3",
                        "case_selector__44b881f9")),
                "case_selector__a7c0aa52"));

        // A read no case claims says nothing, so nothing is excluded: the
        // fatal read is guarded by a target-path case this map never sees.
        assertFalse(ConcolicSmtComposer.writerCaseExclusiveOfRead(
                updateKeys, Collections.<String>emptySet(),
                "case_selector__a7c0aa52"));
        assertFalse(ConcolicSmtComposer.writerCaseExclusiveOfRead(
                updateKeys, null, "case_selector__a7c0aa52"));
        assertFalse(ConcolicSmtComposer.writerCaseExclusiveOfRead(
                null, recordedCaseRead, "case_selector__a7c0aa52"));
    }

    /**
     * A guard names its case however the case was spelled.
     *
     * <p>A case observed in one replay is guarded by its own selector; one
     * whose observations were kept apart is guarded by each observation, and
     * a read's guard pairs either with the read selector that reached it.
     * All three spellings have to answer with the case.</p>
     */
    @Test
    public void everySpellingOfAGuardNamesItsCase() {
        assertEquals(Collections.singleton("case_selector__a7c0aa52"),
                ConcolicSmtComposer.caseGuardsIn("case_selector__a7c0aa52"));
        assertEquals(Collections.singleton("case_observation__66a048ca"),
                ConcolicSmtComposer.caseGuardsIn(
                        "case_observation__66a048ca"));
        assertEquals(Collections.singleton("case_observation__66a048ca"),
                ConcolicSmtComposer.caseGuardsIn(
                        "(and case_observation__66a048ca"
                                + " read_selector__7e4fb6f2)"));
        assertEquals(new LinkedHashSet<>(Arrays.asList(
                        "case_selector__a7c0aa52",
                        "case_observation__66a048ca")),
                ConcolicSmtComposer.caseGuardsIn(
                        "(or case_selector__a7c0aa52"
                                + " case_observation__66a048ca)"));
        assertTrue(ConcolicSmtComposer.caseGuardsIn(
                "read_selector__7e4fb6f2").isEmpty());
        assertTrue(ConcolicSmtComposer.caseGuardsIn(null).isEmpty());
    }

    /**
     * A snapshot with no host cannot be what a fault retained.
     *
     * <p>An INITIAL arm is the value an object held when some activation was
     * entered, and which activation that was is what lets a marker say the
     * snapshot never happened.  Without it the arm answers every marker with
     * the same value while the fault idles the region around it -- the same
     * step {@code FAULT_IDLE_INITIAL_HOST_IDLED} refuses when the host is
     * known.  With no marker at all nothing idles anything and the fact is
     * not needed.</p>
     */
    @Test
    public void anInitialArmWithoutAHostIsRefusedOnceAMarkerExists() {
        assertTrue(ConcolicSmtComposer.initialArmRefusable(true, false));
        assertFalse("a known host is the fact the rule wants",
                ConcolicSmtComposer.initialArmRefusable(true, true));
        assertFalse("with no marker nothing can idle the host",
                ConcolicSmtComposer.initialArmRefusable(false, false));
        assertFalse(ConcolicSmtComposer.initialArmRefusable(false, true));

        // armIdled is the other half: it retires an INITIAL arm only when it
        // knows the host and every case of it is idled.
        Set<String> idled = new LinkedHashSet<>(Arrays.asList(HOST_CASE_A,
                HOST_CASE_B));
        assertFalse("no host, nothing to idle",
                ConcolicSmtComposer.armIdled(Collections.<String>emptySet(),
                        Collections.<String>emptySet(), idled));
        assertTrue(ConcolicSmtComposer.armIdled(
                Collections.<String>emptySet(),
                Arrays.asList(HOST_CASE_A, HOST_CASE_B), idled));
    }

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

    /**
     * The slice reads a lowered term for the names it was built from.
     *
     * <p>Only names this composition declared or defined count: an SMT
     * keyword, a sort and a literal are not symbols, and a name that merely
     * contains a known one is a different symbol.</p>
     */
    @Test
    public void sliceReadsOnlyTheNamesTheFormulaDeclares() {
        Set<String> known = new LinkedHashSet<>(Arrays.asList(
                "merged_boundary__abc", "rf_value__RFC_1", "sym__X"));
        assertEquals(new LinkedHashSet<>(Arrays.asList(
                        "merged_boundary__abc", "sym__X")),
                ConcolicSmtComposer.Emitter.symbolsIn(
                        "(ite (= (VInt merged_boundary__abc) (VInt 7))"
                                + " sym__X (VRef nullRef))", known));
        // A longer name that starts with a known one is not that symbol.
        assertTrue(ConcolicSmtComposer.Emitter.symbolsIn(
                "(= sym__X2 3)", known).isEmpty());
        assertTrue(ConcolicSmtComposer.Emitter.symbolsIn("", known).isEmpty());
        assertTrue(ConcolicSmtComposer.Emitter.symbolsIn(null, known)
                .isEmpty());
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
