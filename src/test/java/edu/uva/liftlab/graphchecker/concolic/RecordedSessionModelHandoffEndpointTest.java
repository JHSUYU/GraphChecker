package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * README {@code RPC-1}: a handoff order assertion names the exact pair of
 * endpoints the VM recorded.
 *
 * <p>One exported expression may be attached at several explicit receivers,
 * and each attach records its own {@code VALUE_HANDOFF} edge.  Recovering the
 * receive endpoint from the export alone therefore does not identify a
 * receive: scanning the order domain returns whichever attach sorts first,
 * which is routinely a different receiver's, and the emitted
 * {@code send < receive} then constrains the wrong one.</p>
 */
public class RecordedSessionModelHandoffEndpointTest {
    private static final String REGION = "REGION.receiver";
    private static final String OCCURRENCE =
            RecordedSharedStateFixtures.occurrenceOf(REGION);
    private static final String CASE_ID = "CASE.receive";
    private static final String PORT = "REGION.receiver.in.0";
    private static final long EXPORT = 41L;
    /** The attach this case actually performed - the higher-numbered one. */
    private static final long OWN_ATTACH = 52L;
    /** Another receiver's attach of the same export, recorded earlier. */
    private static final long OTHER_ATTACH = 42L;

    @Test
    public void exactEndpointPairIsAssertedAndAnyOtherIsRefused() {
        RecordedSessionModel model = model(true);
        String selector = RecordedSessionModel.caseSelector(caseOwner());

        String own = model.handoffOrderAssertion(EXPORT, OWN_ATTACH,
                selector);
        String other = model.handoffOrderAssertion(EXPORT, OTHER_ATTACH,
                selector);

        assertFalse("the recorded pair must produce an order assertion",
                own.isEmpty());
        assertFalse(other.isEmpty());
        assertNotEquals("two receivers of one export are two assertions",
                own, other);
        assertTrue(own, own.startsWith("recorded_order__"));

        // The pair is asserted, never completed: an attach the domain holds
        // no direct edge to is a gap for the caller, not a proposed order.
        assertEquals("", model.handoffOrderAssertion(EXPORT, 999L, selector));
        assertEquals("", model.handoffOrderAssertion(EXPORT, 0L, selector));
        assertEquals("", model.handoffOrderAssertion(0L, OWN_ATTACH,
                selector));
        // OTHER_ATTACH is an attach, not an export: reversing the endpoints
        // names no recorded edge.
        assertEquals("", model.handoffOrderAssertion(OWN_ATTACH, EXPORT,
                selector));
    }

    @Test
    public void eachReceiverOfOneExportGetsItsOwnOrderAssertion() {
        String selector = RecordedSessionModel.caseSelector(caseOwner());
        RecordedSessionModel fannedOut = model(true);

        // README RPC-1: one export may be attached at several receivers, and
        // naming both endpoints is what gives each receive its own
        // send-before-receive edge.  The two answers must differ; a shared
        // answer would be the defect where one receiver's order is asserted
        // for another receiver's attach.
        String own = fannedOut.handoffOrderAssertion(EXPORT, OWN_ATTACH,
                selector);
        String other = fannedOut.handoffOrderAssertion(EXPORT, OTHER_ATTACH,
                selector);
        assertFalse(own.isEmpty());
        assertFalse(other.isEmpty());
        assertFalse(own.equals(other));

        // Fanning out changes nothing about the pair a single receiver names.
        assertEquals(model(false).handoffOrderAssertion(EXPORT, OWN_ATTACH,
                selector), own);
    }

    @Test
    public void anotherCaseMayNotBorrowThisCasesHandoffOrder() {
        RecordedSessionModel model = model(true);

        assertEquals("", model.handoffOrderAssertion(EXPORT, OWN_ATTACH,
                "case_selector_of_no_case"));
    }

    private static String caseOwner() {
        return RecordedSessionModel.caseOwner(REGION, OCCURRENCE, CASE_ID, 0);
    }

    /**
     * One receiving case that attached {@link #EXPORT} at {@link #OWN_ATTACH},
     * over a session ledger in which that export was
     * {@code fanOut ? also : not} attached at another receiver.
     */
    private static RecordedSessionModel model(boolean fanOut) {
        JsonObject summary = new JsonObject();
        summary.addProperty("regionId", REGION);
        summary.addProperty("occurrenceId", OCCURRENCE);
        JsonObject caseRow = new JsonObject();
        caseRow.addProperty("caseId", CASE_ID);
        caseRow.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", "M_I_field_REMOTE_keyId");
        VmHandoffEvidence.writeTo(caseRow, Collections.singletonList(
                VmHandoffEvidence.event(PORT, EXPORT, OWN_ATTACH, expression,
                        "TASK.producer",
                        RecordedSharedStateFixtures.occurrenceOf(
                                "REGION.sender"))));

        JsonArray events = new JsonArray();
        events.add(RecordedSharedStateFixtures.event(EXPORT,
                "HANDOFF_EXPORT", 101L, "REGION.sender"));
        events.add(RecordedSharedStateFixtures.event(OWN_ATTACH,
                "HANDOFF_ATTACH", 102L, REGION));
        JsonArray order = new JsonArray();
        order.add(RecordedSharedStateFixtures.edge(EXPORT, OWN_ATTACH,
                "VALUE_HANDOFF"));
        if (fanOut) {
            events.add(RecordedSharedStateFixtures.event(OTHER_ATTACH,
                    "HANDOFF_ATTACH", 103L, "REGION.other"));
            order.add(RecordedSharedStateFixtures.edge(EXPORT, OTHER_ATTACH,
                    "VALUE_HANDOFF"));
        }
        caseRow.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(
                                RecordedSharedStateFixtures.ledgerEnvelope(
                                        events, order),
                                RecordedSharedStateFixtures.identity(
                                        REGION, 1L))));

        JsonArray cases = new JsonArray();
        cases.add(caseRow);
        JsonObject relation = new JsonObject();
        relation.add("cases", cases);
        summary.add("regionRelation", relation);
        return RecordedSessionModel.of(Collections.singletonList(summary),
                null, REGION);
    }
}
