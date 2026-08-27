package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Case-local references to the VM's own symbolic handoffs.
 *
 * <p>The VM is the single propagation authority.  A sender exports an
 * expression to a live broker handle; a receiver attaches that handle, and
 * from then on the receiver's location <em>denotes the sender's
 * expression</em> - receiver arithmetic, branches, container accesses and
 * later exports build on it with no further help.  The session ledger records
 * the pair once, as {@code VALUE_HANDOFF(exportEvent, attachEvent)}.</p>
 *
 * <p>Each row carries the reference a case needs into that ledger - the
 * declared receiving port, <em>both</em> endpoints of the exact VM edge, and
 * the producer task/occurrence transported beside the handle - together with
 * the exact expression read back from the receiving storage after attach.
 * The two producer strings are path-provenance authority, never value
 * authority: only the broker handle and its VM ledger edge establish the
 * propagated value.  It performs no pairing.  There is no export-by-receive
 * search, no {@code (site, exchange, attempt, direction, leafPath)} tuple to
 * narrow, no delivery ordinal, and no second "attested delivery" proof after
 * the VM's attach already succeeded.  The expression is value evidence from
 * that exact destination, not another way to recover which send reached
 * it.</p>
 *
 * <p>Both endpoints are carried because one export may be attached at several
 * explicit receivers, each recording its own edge (README {@code RPC-1}).  A
 * row naming only the export therefore does not name a receive, and the only
 * way to finish it afterwards is to search the order domain for an edge out
 * of that export - which returns whichever attach sorts first, commonly a
 * different receiver's.  The VM already knows both; it says both.</p>
 *
 */
public final class VmHandoffEvidence {

    /**
     * Schema 4 adds the required {@code attachEventId}.  Schema 3 rows are
     * not upgraded: the endpoint they are missing cannot be recovered from
     * anything they carry, and inferring it is the exact defect the version
     * bump exists to refuse.
     */
    public static final int SCHEMA_VERSION = 4;
    /** Kind of one case-local handoff reference. */
    public static final String KIND = "VM_HANDOFF_EVENT";
    /** Authority of one VM-propagated expression. */
    public static final String AUTHORITY = "VM_VALUE_HANDOFF_V1";
    /**
     * Member the references travel in, on a raw region result and on each
     * guarded case of an imported summary alike.
     */
    public static final String FIELD = "vmHandoffEvents";
    /** Exact VM expression read from the receiving storage after attach. */
    public static final String EXPRESSION = "expression";
    /** The exact export endpoint of the VM's {@code VALUE_HANDOFF} edge. */
    public static final String EXPORT_EVENT_ID = "exportEventId";
    /**
     * The exact attach endpoint of that same edge - this receive, not any
     * other receive of the same export.
     */
    public static final String ATTACH_EVENT_ID = "attachEventId";
    /** Exact producer execution that exported the live handle. */
    public static final String PRODUCER_TASK_ID = "producerTaskId";
    public static final String PRODUCER_OCCURRENCE_ID =
            "producerOccurrenceId";
    /** Kind of the composed value binding one reference is lowered into. */
    public static final String BINDING_KIND = "VM_HANDOFF_VALUE_BINDING";
    /**
     * Authority of an edge binding the frozen plan did not declare and a
     * replay recorded.
     *
     * <p>The scheduler declares such a member out of the sender task's own
     * frozen binding for that port, re-addressed to the receiver occurrence
     * the handoff attached at, so nothing is minted -- the edge id still
     * names the one traced exchange it was decoded from.  These four fields
     * are the whole of what re-derives the member from the carry file, and
     * they are what lets a consumer tell an evidence-backed pairing from a
     * pairing the region plan declared.</p>
     */
    public static final String ABSORBED_AUTHORITY_FIELD =
            "absorbedAuthority";
    public static final String ABSORBED_AUTHORITY = "OBSERVED_VM_HANDOFF_V1";
    public static final String ABSORBED_FROM_TASK_ID = "absorbedFromTaskId";
    public static final String ABSORBED_EXPORT_EVENT_ID =
            "absorbedExportEventId";
    public static final String ABSORBED_ATTACH_EVENT_ID =
            "absorbedAttachEventId";

    /**
     * Whether this edge binding is one a replay recorded and the scheduler
     * absorbed.
     *
     * <p>Fully stamped or not absorbed: the exemptions this answers exist
     * because the two VM ledger events below name the exact send and receive,
     * so a row that does not carry them is judged as any other binding.</p>
     */
    public static boolean absorbed(JsonObject binding) {
        if (binding == null || !ABSORBED_AUTHORITY.equals(
                string(binding, ABSORBED_AUTHORITY_FIELD))) {
            return false;
        }
        return !string(binding, ABSORBED_FROM_TASK_ID).isEmpty()
                && longInteger(binding, ABSORBED_EXPORT_EVENT_ID, -1L) >= 0
                && longInteger(binding, ABSORBED_ATTACH_EVENT_ID, -1L) >= 0;
    }
    /**
     * A handoff whose receiving destination no region port declares.
     *
     * <p>One name for one fact, published by the runtime when it files the
     * reference and by the Composer when it refuses to bind an SMT term to
     * it.  The edge is real either way; what is missing is a declaration to
     * carry it into the query.</p>
     */
    public static final String PORT_UNDECLARED =
            "HANDOFF_RECEIVING_PORT_UNDECLARED";

    private VmHandoffEvidence() {
    }

    /**
     * One reference to the VM handoff a selected receive site attached.
     *
     * @param portId        the declared port the attached value landed on
     * @param exportEventId  the VM ledger event of the matching export, as the
     *                       broker itself reported it on the attach
     * @param attachEventId  the VM ledger event of this exact attach, as the
     *                       broker reported it on the same call; the other
     *                       endpoint of the one {@code VALUE_HANDOFF} edge
     *                       this receive recorded
     * @param exactExpression exact VM expression read from the attached
     *                        destination storage
     * @param producerTaskId exact accepted producer execution task
     * @param producerOccurrenceId exact producer region occurrence
     */
    public static JsonObject event(String portId, long exportEventId,
                                   long attachEventId,
                                   JsonElement exactExpression,
                                   String producerTaskId,
                                   String producerOccurrenceId) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", KIND);
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("authority", AUTHORITY);
        row.addProperty("portId", nonNull(portId));
        row.addProperty(EXPORT_EVENT_ID, exportEventId);
        row.addProperty(ATTACH_EVENT_ID, attachEventId);
        row.addProperty(PRODUCER_TASK_ID, nonNull(producerTaskId));
        row.addProperty(PRODUCER_OCCURRENCE_ID,
                nonNull(producerOccurrenceId));
        row.add(EXPRESSION, exactExpression == null ? null
                : exactExpression.deepCopy());
        return row;
    }

    /**
     * Whether {@code row} is one admissible reference.
     *
     * <p>Admission is exactly "the VM said so": this authority, a declared
     * port, both endpoints of a real edge the ledger can be asked about, an
     * exact producer execution, and the exact expression read from the
     * attached destination.  A row missing any of them is refused rather than
     * completed from another field - and the attach endpoint in particular
     * may never be completed, because recovering it means choosing among the
     * receivers of one export.</p>
     */
    public static boolean isEvent(JsonObject row) {
        return row != null
                && KIND.equals(string(row, "kind"))
                && AUTHORITY.equals(string(row, "authority"))
                && integer(row, "schemaVersion", -1) == SCHEMA_VERSION
                && !string(row, "portId").isEmpty()
                && longInteger(row, EXPORT_EVENT_ID, 0L) > 0L
                && longInteger(row, ATTACH_EVENT_ID, 0L) > 0L
                && !string(row, PRODUCER_TASK_ID).isEmpty()
                && !string(row, PRODUCER_OCCURRENCE_ID).isEmpty()
                && row.has(EXPRESSION)
                && row.get(EXPRESSION).isJsonObject()
                && !SharedStateEvidence.containsVmSerializationTruncation(
                row.get(EXPRESSION));
    }

    /** The admissible references carried by one case or result row. */
    public static List<JsonObject> eventsOf(JsonObject owner) {
        List<JsonObject> events = new ArrayList<>();
        if (owner == null) return events;
        JsonElement raw = owner.get(FIELD);
        if (raw == null || !raw.isJsonArray()) return events;
        for (JsonElement element : raw.getAsJsonArray()) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if (isEvent(row)) events.add(row);
        }
        return events;
    }

    /**
     * Writes the references onto {@code owner}, deduplicated by their whole
     * payload and ordered canonically, or writes nothing when there are none.
     */
    public static void writeTo(JsonObject owner,
                               Collection<JsonObject> events) {
        if (owner == null || events == null || events.isEmpty()) return;
        Map<String, JsonObject> byPayload = new LinkedHashMap<>();
        for (JsonObject event : events) {
            if (!isEvent(event)) continue;
            byPayload.put(CanonicalJson.render(event), event.deepCopy());
        }
        if (byPayload.isEmpty()) return;
        List<String> keys = new ArrayList<>(byPayload.keySet());
        java.util.Collections.sort(keys);
        JsonArray rows = new JsonArray();
        for (String key : keys) rows.add(byPayload.get(key));
        owner.add(FIELD, rows);
    }

    /** The exact attach endpoint one admitted reference names. */
    public static long attachEventOf(JsonObject event) {
        return isEvent(event) ? longInteger(event, ATTACH_EVENT_ID, 0L) : 0L;
    }
}
