package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.candidate;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.constant;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.guardedRead;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.sum;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.symbol;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Admission of the VM's recorded shared-state evidence.
 *
 * <p>The interesting half is the refusals. An envelope that cannot prove its
 * own claim must not be repaired into one that can: a writer set silently read
 * as complete, or a cyclic relation read as an order, would let an
 * under-approximate answer be reported as a conclusion.</p>
 */
public class SharedStateEvidenceTest {

    private static final String OCCURRENCE =
            "cluster0/nn0#epoch1/region/REGION.shared#1";

    @Test
    public void mapStateSymbolUsesItsExactOccurrenceInputPort() {
        String occurrence = "cluster0/dn0#epoch1/region/REGION.3#1";
        String input = "REGION.3.in.allKeys";
        JsonObject binding = new JsonObject();
        binding.addProperty("locationKey", "MAP_STATE/" + occurrence
                + "@" + ALL_KEYS + "#-3");
        binding.addProperty(SharedStateEvidence.SESSION_LOCATION_FIELD,
                "MAP_STATE/2147#-3");
        binding.addProperty("toOccurrenceId", occurrence);
        binding.addProperty("toInputPort", input);

        JsonObject receiver = new JsonObject();
        receiver.addProperty("_type", "SymbolExpression");
        receiver.addProperty("_java_type", "java/util/HashMap");
        receiver.addProperty("_exp", "M_L'java/util/HashMap'_2147");
        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("shape", "ASSOCIATIVE");
        state.addProperty("operation", "STATE");
        state.add("receiver", receiver);

        JsonObject summary = new JsonObject();
        summary.addProperty("occurrenceId", occurrence);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        summary.add("edgeBindings", bindings);
        JsonArray path = new JsonArray();
        path.add(state);
        summary.add("pathCondition", path);

        assertTrue(SharedStateEvidence
                .canonicalizeContainerStateSymbols(summary).isEmpty());
        assertEquals(input, summary.getAsJsonArray("pathCondition").get(0)
                .getAsJsonObject().getAsJsonObject("receiver")
                .get("_exp").getAsString());
    }

    @Test
    public void aGuardedReadWithoutItsUnknownArmIsRefused() {
        JsonArray closedOverObservedWriters = new JsonArray();
        closedOverObservedWriters.add(candidate("rf1", 11L,
                sum(symbol("A"), constant(1)), null, 21L, 12L));
        closedOverObservedWriters.add(candidate("rf2", 12L,
                sum(symbol("B"), constant(2)), null, 21L, 11L));

        JsonObject node = guardedRead(21L, 7L, 24,
                closedOverObservedWriters);

        // Without rf_unknown the disjunction asserts that this one run saw
        // every writer, which turns an under-approximate UNSAT into a claim
        // about the program.
        assertEquals("guarded read must carry exactly one unknown-writer arm",
                SharedStateEvidence.guardedReadFault(node));
        assertFalse(SharedStateEvidence.isGuardedRead(node));
    }

    // ---- Cross-session location identity -----------------------------

    private static JsonObject binding(String edgeId, String locationKey,
                                      String field, long receiver) {
        JsonObject row = new JsonObject();
        row.addProperty("edgeId", edgeId);
        row.addProperty("locationKey", locationKey);
        row.addProperty(RecordedReadFrom.EDGE_FIELD, field);
        row.addProperty("receiverObjectId", receiver);
        return row;
    }

    private static JsonObject versionRow(String locationKey) {
        JsonObject row = new JsonObject();
        row.addProperty("locationKey", locationKey);
        return row;
    }

    private static JsonObject summary(JsonObject binding,
                                      JsonObject versionRow) {
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        JsonArray versions = new JsonArray();
        versions.add(versionRow);
        JsonObject recorded = new JsonObject();
        recorded.add("versions", versions);
        JsonObject summary = new JsonObject();
        summary.addProperty("occurrenceId", OCCURRENCE);
        summary.add("edgeBindings", bindings);
        summary.add(SharedStateEvidence.RECORDED_FIELD, recorded);
        return summary;
    }

    private static final String ALL_KEYS =
            "org.apache.hadoop.hdfs.security.token.block."
                    + "BlockTokenSecretManager#allKeys";

    /**
     * Two replays of one occurrence name the same map with different VM rids,
     * because the rid is a per-session allocation ordinal. Left alone they
     * index as two locations and the read-from arm is contested away.
     */
    @Test
    public void twoSessionsOfOneLocationCanonicaliseToOneName() {
        JsonObject sessionA = summary(
                binding("RF.1", "MAP_STATE/2136#-3", ALL_KEYS, 100474L),
                versionRow("MAP_STATE/2136#-3"));
        JsonObject sessionB = summary(
                binding("RF.1", "MAP_STATE/2139#-3", ALL_KEYS, 100474L),
                versionRow("MAP_STATE/2139#-3"));

        assertTrue("the two sessions must start out disagreeing, or this "
                        + "test proves nothing",
                !locationOf(sessionA).equals(locationOf(sessionB)));

        assertTrue(SharedStateEvidence.canonicalizeLocations(sessionA)
                .isEmpty());
        assertTrue(SharedStateEvidence.canonicalizeLocations(sessionB)
                .isEmpty());

        assertEquals("one location must carry one name across sessions",
                locationOf(sessionA), locationOf(sessionB));
        assertEquals("the version row must be renamed with its edge",
                locationOf(sessionA), versionLocationOf(sessionA));
        assertEquals("the VM's own triple is kept as provenance",
                "MAP_STATE/2139#-3",
                SharedStateEvidence.sessionLocationKey(
                        bindingOf(sessionB)));
    }

    /**
     * Three managers declare {@code allKeys}; the receiver is what tells them
     * apart. Keying on the field alone would merge the NameNode's map with a
     * DataNode's, which is the whole reason the index is two-level.
     */
    @Test
    public void twoReceiversOfOneFieldStayTwoLocations() {
        JsonObject namenode = summary(
                binding("RF.1", "MAP_STATE/2136#-3", ALL_KEYS, 100474L),
                versionRow("MAP_STATE/2136#-3"));
        JsonObject datanode = summary(
                binding("RF.2", "MAP_STATE/2136#-3", ALL_KEYS, 100999L),
                versionRow("MAP_STATE/2136#-3"));

        SharedStateEvidence.canonicalizeLocations(namenode);
        SharedStateEvidence.canonicalizeLocations(datanode);

        assertFalse("two receivers of one declared field must not merge",
                locationOf(namenode).equals(locationOf(datanode)));
    }

    @Test
    public void oneSessionLocationClaimedByTwoReceiversStaysUnresolved() {
        JsonObject first = binding("RF.1", "MAP_STATE/2136#-3", ALL_KEYS,
                100474L);
        JsonObject second = binding("RF.2", "MAP_STATE/2136#-3", ALL_KEYS,
                100999L);
        JsonArray bindings = new JsonArray();
        bindings.add(first);
        bindings.add(second);
        JsonArray versions = new JsonArray();
        versions.add(versionRow("MAP_STATE/2136#-3"));
        JsonObject recorded = new JsonObject();
        recorded.add("versions", versions);
        JsonObject summary = new JsonObject();
        summary.addProperty("occurrenceId", OCCURRENCE);
        summary.add("edgeBindings", bindings);
        summary.add(SharedStateEvidence.RECORDED_FIELD, recorded);

        assertEquals(java.util.Collections.singletonList(
                        "MAP_STATE/2136#-3"),
                new java.util.ArrayList<>(
                        SharedStateEvidence.canonicalizeLocations(summary)));
        assertEquals("MAP_STATE/2136#-3",
                first.get("locationKey").getAsString());
        assertEquals("MAP_STATE/2136#-3",
                second.get("locationKey").getAsString());
    }

    /**
     * Without a receiver id the row cannot be named across sessions. It stays
     * under its own session key and is reported - never defaulted onto the
     * field, which would merge every manager that declares it.
     */
    @Test
    public void aRowWithoutItsReceiverStaysUnresolvedAndIsNamed() {
        JsonObject anonymous = summary(
                binding("RF.1", "MAP_STATE/2136#-3", ALL_KEYS, 0L),
                versionRow("MAP_STATE/2136#-3"));

        assertEquals("the unnameable location must be reported",
                java.util.Collections.singletonList("MAP_STATE/2136#-3"),
                new java.util.ArrayList<>(
                        SharedStateEvidence.canonicalizeLocations(anonymous)));
        assertEquals("an unresolved row keeps the VM's own key",
                "MAP_STATE/2136#-3", locationOf(anonymous));

        JsonObject named = summary(
                binding("RF.2", "MAP_STATE/2136#-3", ALL_KEYS, 100474L),
                versionRow("MAP_STATE/2136#-3"));
        SharedStateEvidence.canonicalizeLocations(named);
        assertFalse("an unresolved row must not join a named one",
                locationOf(anonymous).equals(locationOf(named)));
    }

    /**
     * A summary carrying no edge binding has no name to borrow, yet its
     * version rows describe the same locations as a summary that does. The
     * carrier is recorded where the read-out happens and holds the receiver
     * the VM's location triple omits, so the row names itself.
     */
    @Test
    public void aVersionRowNamesItsOwnLocationFromItsCarrier() {
        JsonObject withEdge = summary(
                binding("RF.1", "MAP_STATE/2136#-3", ALL_KEYS, 100474L),
                versionRow("MAP_STATE/2136#-3"));
        JsonObject edgeless = edgelessSummary(
                carrierRow("MAP_STATE/2147#-3", 100474L));

        assertTrue("the two sessions must start out disagreeing, or this "
                        + "test proves nothing",
                !versionLocationOf(withEdge)
                        .equals(versionLocationOf(edgeless)));

        assertTrue(SharedStateEvidence.canonicalizeLocations(withEdge)
                .isEmpty());
        assertTrue("a self-naming row leaves nothing unresolved",
                SharedStateEvidence.canonicalizeLocations(edgeless)
                        .isEmpty());

        assertEquals("a row must name its location without an edge to "
                        + "borrow from",
                versionLocationOf(withEdge), versionLocationOf(edgeless));
        assertEquals("the VM's own triple is kept as provenance",
                "MAP_STATE/2147#-3",
                SharedStateEvidence.sessionLocationKey(versionOf(edgeless)));
    }

    /**
     * A carrier without a receiver id names nothing. The row keeps its own
     * session key and is reported, rather than defaulting onto the declared
     * field and merging every manager that declares it.
     */
    @Test
    public void aCarrierWithoutItsReceiverStaysUnresolved() {
        JsonObject anonymous = edgelessSummary(
                carrierRow("MAP_STATE/2147#-3", 0L));

        assertEquals("the unnameable location must be reported",
                java.util.Collections.singletonList("MAP_STATE/2147#-3"),
                new java.util.ArrayList<>(
                        SharedStateEvidence.canonicalizeLocations(anonymous)));
        assertEquals("an unresolved row keeps the VM's own key",
                "MAP_STATE/2147#-3", versionLocationOf(anonymous));

        JsonObject named = edgelessSummary(
                carrierRow("MAP_STATE/2147#-3", 100474L));
        SharedStateEvidence.canonicalizeLocations(named);
        assertFalse("an unresolved row must not join a named one",
                versionLocationOf(anonymous)
                        .equals(versionLocationOf(named)));
    }

    private static JsonObject carrierRow(String locationKey, long receiver) {
        int split = ALL_KEYS.indexOf('#');
        JsonObject carrier = new JsonObject();
        carrier.addProperty("declaringClass", ALL_KEYS.substring(0, split));
        carrier.addProperty("fieldName", ALL_KEYS.substring(split + 1));
        carrier.addProperty("receiverObjectId", receiver);
        JsonObject row = versionRow(locationKey);
        row.add("carrier", carrier);
        return row;
    }

    private static JsonObject edgelessSummary(JsonObject versionRow) {
        JsonArray versions = new JsonArray();
        versions.add(versionRow);
        JsonObject recorded = new JsonObject();
        recorded.add("versions", versions);
        JsonObject summary = new JsonObject();
        summary.addProperty("occurrenceId", OCCURRENCE);
        summary.add("edgeBindings", new JsonArray());
        summary.add(SharedStateEvidence.RECORDED_FIELD, recorded);
        return summary;
    }

    /**
     * README {@code EVENT-1}: selected ledger truncation and saturation are
     * gaps in their own right.  Both fail closed, but they fail closed for
     * different reasons - one execution outran a bound, the other never
     * admitted the edges - and a blocker that calls either a malformed
     * envelope sends the reader to look at the VM answer instead.
     */
    @Test
    public void ledgerTruncationAndSaturationAreNamedApartFromMalformed() {
        JsonArray events = new JsonArray();
        events.add(RecordedSharedStateFixtures.event(11L, "VOLATILE_WRITE",
                101L, "REGION.shared"));
        JsonObject sound = RecordedSharedStateFixtures.ledgerEnvelope(
                events, new JsonArray());
        assertEquals("", SharedStateEvidence.ledgerFault(sound));
        assertEquals(SharedStateEvidence.OK,
                SharedStateEvidence.ledgerFaultStatus(sound,
                        SharedStateEvidence.ledgerFault(sound)));

        JsonObject truncated = sound.deepCopy();
        truncated.addProperty("truncated", true);
        String truncatedFault = SharedStateEvidence.ledgerFault(truncated);
        assertFalse(truncatedFault.isEmpty());
        assertEquals(SharedStateEvidence.LEDGER_LOG_TRUNCATED,
                SharedStateEvidence.ledgerFaultStatus(truncated,
                        truncatedFault));

        JsonObject saturated = sound.deepCopy();
        saturated.addProperty("domainSaturated", true);
        String saturatedFault = SharedStateEvidence.ledgerFault(saturated);
        assertFalse(saturatedFault.isEmpty());
        assertEquals(SharedStateEvidence.LEDGER_DOMAIN_SATURATED,
                SharedStateEvidence.ledgerFaultStatus(saturated,
                        saturatedFault));

        JsonObject cyclic = sound.deepCopy();
        cyclic.addProperty("acyclic", false);
        assertEquals(SharedStateEvidence.MALFORMED_ENVELOPE,
                SharedStateEvidence.ledgerFaultStatus(cyclic,
                        SharedStateEvidence.ledgerFault(cyclic)));

        assertEquals("SHARED_STATE_LEDGER_LOG_TRUNCATED",
                SharedStateEvidence.reason(
                        SharedStateEvidence.LEDGER_LOG_TRUNCATED));
        assertEquals("SHARED_STATE_LEDGER_DOMAIN_SATURATED",
                SharedStateEvidence.reason(
                        SharedStateEvidence.LEDGER_DOMAIN_SATURATED));
    }

    private static JsonObject versionOf(JsonObject summary) {
        return summary.getAsJsonObject(SharedStateEvidence.RECORDED_FIELD)
                .getAsJsonArray("versions").get(0).getAsJsonObject();
    }

    private static JsonObject bindingOf(JsonObject summary) {
        return summary.getAsJsonArray("edgeBindings").get(0)
                .getAsJsonObject();
    }

    private static String locationOf(JsonObject summary) {
        return bindingOf(summary).get("locationKey").getAsString();
    }

    private static String versionLocationOf(JsonObject summary) {
        return summary.getAsJsonObject(SharedStateEvidence.RECORDED_FIELD)
                .getAsJsonArray("versions").get(0).getAsJsonObject()
                .get("locationKey").getAsString();
    }
}
