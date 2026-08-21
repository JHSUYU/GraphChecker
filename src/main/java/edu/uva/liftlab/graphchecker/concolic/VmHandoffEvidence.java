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
 * declared receiving port and the exact VM export event - together with the
 * exact expression read back from the receiving storage after attach.  It
 * performs no pairing.  There is no export-by-receive search, no
 * {@code (site, exchange, attempt, direction, leafPath)} tuple to narrow, no
 * delivery ordinal, and no second "attested delivery" proof after the VM's
 * attach already succeeded.  The expression is value evidence from that
 * exact destination, not another way to recover which send reached it.</p>
 *
 */
public final class VmHandoffEvidence {

    public static final int SCHEMA_VERSION = 2;
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
    /** Kind of the composed value binding one reference is lowered into. */
    public static final String BINDING_KIND = "VM_HANDOFF_VALUE_BINDING";
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
     * @param exactExpression exact VM expression read from the attached
     *                        destination storage
     */
    public static JsonObject event(String portId, long exportEventId,
                                   JsonElement exactExpression) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", KIND);
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("authority", AUTHORITY);
        row.addProperty("portId", text(portId));
        row.addProperty("exportEventId", exportEventId);
        row.add(EXPRESSION, exactExpression == null ? null
                : exactExpression.deepCopy());
        return row;
    }

    /**
     * Whether {@code row} is one admissible reference.
     *
     * <p>Admission is exactly "the VM said so": this authority, a declared
     * port, a real export event the ledger can be asked about, and the exact
     * expression read from the attached destination.  A row without either
     * the event id or expression is refused rather than completed from another
     * field.</p>
     */
    public static boolean isEvent(JsonObject row) {
        return row != null
                && KIND.equals(string(row, "kind"))
                && AUTHORITY.equals(string(row, "authority"))
                && integer(row, "schemaVersion", -1) == SCHEMA_VERSION
                && !string(row, "portId").isEmpty()
                && longInteger(row, "exportEventId", 0L) > 0L
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

    /** The VM export events referenced by these cases or result rows. */
    public static List<Long> exportEvents(Collection<JsonObject> owners) {
        List<Long> events = new ArrayList<>();
        if (owners == null) return events;
        for (JsonObject owner : owners) {
            for (JsonObject event : eventsOf(owner)) {
                Long id = Long.valueOf(longInteger(event, "exportEventId",
                        0L));
                if (!events.contains(id)) events.add(id);
            }
        }
        return events;
    }

    private static String text(String value) {
        return value == null ? "" : value;
    }
}
