package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.shallowCopy;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

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
    public static final int SCHEMA_VERSION = 5;
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
    /** Replay-independent identity assigned by the Java evidence join. */
    public static final String BOUNDARY_FAMILY_KEY = "boundaryFamilyKey";
    /** Frozen topology epoch in which the family was observed. */
    public static final String TOPOLOGY_EPOCH = "topologyEpoch";
    /** Exact producer execution that exported the live handle. */
    public static final String PRODUCER_TASK_ID = "producerTaskId";
    public static final String PRODUCER_OCCURRENCE_ID =
            "producerOccurrenceId";
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
        row.add(EXPRESSION, exactExpression);
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
        return eventFault(row).isEmpty();
    }

    /**
     * Names the first reason one claimed handoff reference is inadmissible.
     *
     * <p>{@link #eventsOf(JsonObject)} is intentionally a filtered view for
     * callers that only consume admitted rows.  A completeness gate must
     * also distinguish "no handoff" from "a handoff was stated but was
     * malformed"; this method provides that fail-closed half without adding
     * a second decoder.</p>
     */
    public static String eventFault(JsonObject row) {
        if (row == null) return "handoff reference is not an object";
        if (!KIND.equals(optionalString(row, "kind"))) {
            return "handoff reference has no declared kind";
        }
        if (!AUTHORITY.equals(optionalString(row, "authority"))) {
            return "handoff reference has no VM propagation authority";
        }
        if (optionalInteger(row, "schemaVersion", -1) != SCHEMA_VERSION) {
            return "handoff reference has an unsupported schema";
        }
        if (optionalString(row, "portId").isEmpty()) {
            return "handoff reference names no receiving port";
        }
        if (optionalLongInteger(row, EXPORT_EVENT_ID, 0L) <= 0L) {
            return "handoff reference names no export event";
        }
        if (optionalLongInteger(row, ATTACH_EVENT_ID, 0L) <= 0L) {
            return "handoff reference names no attach event";
        }
        if (optionalString(row, PRODUCER_TASK_ID).isEmpty()) {
            return "handoff reference names no producer task";
        }
        if (optionalString(row, PRODUCER_OCCURRENCE_ID).isEmpty()) {
            return "handoff reference names no producer occurrence";
        }
        if (!row.has(EXPRESSION) || !row.get(EXPRESSION).isJsonObject()) {
            return "handoff reference carries no exact expression";
        }
        JsonElement expression = row.get(EXPRESSION);
        if (VmExpressionIr.isConsumerBoundaryReference(expression)) {
            JsonObject raw = shallowCopy(expression.getAsJsonObject());
            raw.addProperty("_type", VmExpressionIr.CONSUMER_BOUNDARY_TYPE);
            expression = raw;
        }
        return VmExpressionIr.consumerBoundaryFault(expression,
                VmExpressionIr.RPC_ATTACH,
                optionalLongInteger(row, ATTACH_EVENT_ID, -1L));
    }

    /**
     * Adds the stable family identity after the session-local event has been
     * joined with its exact consumer occurrence and port.
     */
    public static JsonObject withBoundaryFamily(JsonObject event,
                                                String familyKey,
                                                String topologyEpoch) {
        JsonObject result = event == null ? new JsonObject()
                : shallowCopy(event);
        result.addProperty(BOUNDARY_FAMILY_KEY, nonNull(familyKey));
        result.addProperty(TOPOLOGY_EPOCH, nonNull(topologyEpoch));
        JsonElement raw = result.get(EXPRESSION);
        if (raw != null && raw.isJsonObject()) {
            result.add(EXPRESSION, VmExpressionIr.boundaryReference(
                    raw.getAsJsonObject(), familyKey));
        }
        return result;
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
        SharedExpressionTable.Anchors anchors =
                new SharedExpressionTable.Anchors();
        for (JsonObject event : events) {
            if (!isEvent(event)) continue;
            JsonObject identity = shallowCopy(event);
            JsonElement expression = identity.remove(EXPRESSION);
            identity.addProperty(SharedExpressionTable.ANCHOR,
                    anchors.contentAnchor(expression));
            byPayload.put(CanonicalJson.render(identity), event);
        }
        if (byPayload.isEmpty()) return;
        List<String> keys = new ArrayList<>(byPayload.keySet());
        java.util.Collections.sort(keys);
        JsonArray rows = new JsonArray();
        for (String key : keys) rows.add(byPayload.get(key));
        owner.add(FIELD, rows);
    }

}
