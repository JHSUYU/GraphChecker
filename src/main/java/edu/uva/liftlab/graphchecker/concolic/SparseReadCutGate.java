package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Compiles one guarded read's candidate cuts into replay gates, and refuses
 * the ones that cannot be enforced safely.
 *
 * <p>When a solver selects a competing writer, replay has to enforce only the
 * sparse read cut that choice needs: the selected write precedes the read, and
 * every other write happens before it or after the read. Nothing else is
 * ordered. This class turns each candidate arm into that gate, or into a named
 * refusal, using only what the session recorded.</p>
 *
 * <p>The refusals are the point:</p>
 *
 * <ul>
 *   <li>a gate never writes a program field or replaces a returned value;</li>
 *   <li>a candidate without a cross-run identity is not installable;</li>
 *   <li>a cut the recorded order already contradicts is refused rather than
 *   waited for, because no execution satisfies it.</li>
 * </ul>
 *
 * <p>A gate only observes; it never waits, writes a program field, replaces a
 * value the program computed, or substitutes an RPC return. Those are
 * invariants of every gate this class emits, recorded on each one so a
 * consumer can check rather than assume them. The concrete read version and
 * exchange must still be observed by the replay: a gate that let the value be
 * supplied instead of observed would validate its own guess.</p>
 *
 * <p>Every gate also carries the identity a <em>different</em> session can
 * re-derive it from. Event ids, field version ids and object ids belong to the
 * execution that recorded them - a second session restarts them - so a gate
 * keyed only by them could be installed and never validated. The identity that
 * survives is the one {@link RecordedReadFrom} already joins on: the declared
 * field, the writer's region occurrence and the reader's. A candidate arm that
 * cannot supply all three is refused rather than gated.</p>
 */
public final class SparseReadCutGate {

    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "SPARSE_READ_CUT_GATE_PLAN";
    public static final String AUTHORITY = "SPARSE_READ_CUT_GATE_V1";
    public static final String GAP_KIND = "READ_CUT_GATE_GAP";

    /** The gate sits immediately before the selected access. */
    public static final String BEFORE_SELECTED_ACCESS =
            "BEFORE_SELECTED_ACCESS";
    /** The recorded order already contradicts this cut. */
    public static final String CUT_CONTRADICTS_RECORDED_ORDER =
            "GATE_CUT_CONTRADICTS_RECORDED_ORDER";
    /** A competing write is recorded strictly inside the cut. */
    public static final String COMPETITOR_INSIDE_CUT =
            "GATE_COMPETITOR_INSIDE_CUT";
    /** The arm names a writer this run never observed. */
    public static final String UNKNOWN_WRITER_SELECTED =
            "GATE_UNKNOWN_WRITER_SELECTED";
    /** The cut names an event the order domain does not hold. */
    public static final String EVENT_OUTSIDE_ORDER_DOMAIN =
            "GATE_EVENT_OUTSIDE_ORDER_DOMAIN";
    /** The arm carries no identity a second session could re-derive. */
    public static final String NO_CROSS_RUN_READ_IDENTITY =
            "GATE_NO_CROSS_RUN_READ_IDENTITY";
    /** An installation was offered a row this class did not compile. */
    public static final String NOT_A_COMPILED_GATE =
            "GATE_NOT_A_COMPILED_GATE";
    /** An offered gate contradicts one of the invariants it must state. */
    public static final String INVARIANT_VIOLATED =
            "GATE_INVARIANT_VIOLATED";

    private final List<JsonObject> gates = new ArrayList<>();
    private final List<JsonObject> refusals = new ArrayList<>();
    private final long readEventId;
    private final String locationKey;
    private final String readFromField;
    private final String readerRegionId;

    private SparseReadCutGate(long readEventId, String locationKey,
                              String readFromField, String readerRegionId) {
        this.readEventId = readEventId;
        this.locationKey = locationKey;
        this.readFromField = readFromField;
        this.readerRegionId = readerRegionId;
    }

    /**
     * Compiles every candidate arm of one admitted guarded read.
     *
     * <p>Every arm is compiled, not only the one a solver happens to pick:
     * knowing before the solve which selections replay could enforce is worth
     * more than discovering after it that the chosen one cannot be.</p>
     *
     * @param readFromField the declared field of the read location, as
     *                      {@link RecordedReadFrom#fieldKey} states it. It is
     *                      the only part of the gate's identity the VM's own
     *                      location key cannot supply, and without it no later
     *                      session can decide whether the arm was realised.
     */
    public static SparseReadCutGate compile(JsonObject guardedRead,
                                            SessionOrderDomain domain,
                                            String readFromField) {
        long readEventId = longInteger(guardedRead, "readEventId", 0L);
        SessionOrderDomain order = domain == null
                ? SessionOrderDomain.empty() : domain;
        SparseReadCutGate plan = new SparseReadCutGate(readEventId,
                SharedStateEvidence.locationKey(guardedRead),
                readFromField == null ? "" : readFromField.trim(),
                order.regionOf(readEventId));
        if (!SharedStateEvidence.isGuardedRead(guardedRead)
                || !order.knows(readEventId)) {
            plan.refuse(EVENT_OUTSIDE_ORDER_DOMAIN, "",
                    "read " + readEventId
                            + " has no admitted guarded term in the order "
                            + "domain");
            return plan;
        }
        for (JsonElement element : array(guardedRead, "candidates")) {
            JsonObject candidate = element.getAsJsonObject();
            plan.compileCandidate(candidate, order);
        }
        return plan;
    }

    private void compileCandidate(JsonObject candidate,
                                  SessionOrderDomain domain) {
        String selector = string(candidate, "selector");
        if (bool(candidate, "unknown", false)) {
            // Nothing to wait for: no recorded write means no event to order
            // against.  The arm stays in the formula - it is what keeps the
            // disjunction open - but replay cannot validate a selection of it.
            refuse(UNKNOWN_WRITER_SELECTED, selector,
                    "the unknown-writer arm names no recorded write to gate");
            return;
        }
        long version = longInteger(candidate, "fieldVersionId", 0L);
        if (!domain.knows(version)) {
            refuse(EVENT_OUTSIDE_ORDER_DOMAIN, selector,
                    "candidate write " + version
                            + " is not in the recorded order domain");
            return;
        }
        String writerRegionId = JsonFields.firstNonBlank(
                string(candidate, "regionId"), domain.regionOf(version));
        String missing = missingCrossRunIdentity(writerRegionId);
        if (!missing.isEmpty()) {
            // Event ids restart in a second session, so a gate keyed only by
            // them can be installed and never validated.  Refusing here is
            // what keeps "installed" and "confirmed" the same claim.
            refuse(NO_CROSS_RUN_READ_IDENTITY, selector,
                    "the cut of read " + readEventId + " on write " + version
                            + " names " + missing
                            + ", so a replay could not re-derive it");
            return;
        }
        if (domain.orderedBefore(readEventId, version)) {
            // The run recorded the read before this write.  No execution puts
            // the write first without contradicting an observed edge.
            refuse(CUT_CONTRADICTS_RECORDED_ORDER, selector,
                    "the recorded order places read " + readEventId
                            + " before write " + version);
            return;
        }
        List<Long> competitors = competitors(candidate);
        for (Long competitor : competitors) {
            if (!domain.knows(competitor)) {
                refuse(EVENT_OUTSIDE_ORDER_DOMAIN, selector,
                        "competing write " + competitor
                                + " is not in the recorded order domain");
                return;
            }
            if (domain.orderedBefore(version, competitor)
                    && domain.orderedBefore(competitor, readEventId)) {
                refuse(COMPETITOR_INSIDE_CUT, selector,
                        "competing write " + competitor
                                + " is recorded between write " + version
                                + " and read " + readEventId);
                return;
            }
        }
        gates.add(gate(selector, version, competitors, writerRegionId));
    }

    /** Which half of the cross-run identity this arm lacks, or "". */
    private String missingCrossRunIdentity(String writerRegionId) {
        List<String> missing = new ArrayList<>();
        if (readFromField.isEmpty()) missing.add("no declared field");
        if (writerRegionId.isEmpty()) missing.add("no writer region");
        if (readerRegionId.isEmpty()) missing.add("no reader region");
        return String.join(" and ", missing);
    }

    private JsonObject gate(String selector, long version,
                            List<Long> competitors, String writerRegionId) {
        JsonObject gate = new JsonObject();
        gate.addProperty("schemaVersion", SCHEMA_VERSION);
        gate.addProperty("kind", "SPARSE_READ_CUT_GATE");
        gate.addProperty("authority", AUTHORITY);
        gate.addProperty("gateId", "GATE." + readEventId + "." + selector);
        gate.addProperty("selector", selector);
        gate.addProperty("readEventId", readEventId);
        gate.addProperty("locationKey", locationKey);
        gate.addProperty("fieldVersionId", version);
        // The session-local ids above address this run; the three below are
        // what a replay session can key on, and validation uses only them.
        gate.addProperty("readFromField", readFromField);
        gate.addProperty("writerRegionId", writerRegionId);
        gate.addProperty("readerRegionId", readerRegionId);
        gate.addProperty("placement", BEFORE_SELECTED_ACCESS);
        JsonArray outside = new JsonArray();
        for (Long competitor : competitors) outside.add(competitor);
        gate.add("competingWrites", outside);
        // Invariants of every gate this class emits, recorded so a consumer
        // checks them rather than trusting the name of the class.
        gate.addProperty("observesOnly", true);
        gate.addProperty("writesProgramField", false);
        gate.addProperty("replacesRpcReturnValue", false);
        gate.addProperty("requiresObservedReadVersion", true);
        gate.addProperty("requiresObservedExchange", true);
        return gate;
    }

    private void refuse(String reason, String selector, String detail) {
        JsonObject subject = new JsonObject();
        subject.addProperty("readEventId", readEventId);
        subject.addProperty("locationKey", locationKey);
        subject.addProperty("readFromField", readFromField);
        subject.addProperty("readerRegionId", readerRegionId);
        subject.addProperty("selector", selector);
        refusals.add(refusal(reason, subject, detail));
    }

    /** One named refusal in this family, for a consumer of a compiled plan. */
    public static JsonObject refusal(String reason, JsonObject gate,
                                     String detail) {
        JsonObject gap = new JsonObject();
        gap.addProperty("kind", GAP_KIND);
        gap.addProperty("schemaVersion", SCHEMA_VERSION);
        gap.addProperty("reason", reason);
        gap.addProperty("authority", AUTHORITY);
        JsonObject subject = gate == null ? new JsonObject() : gate;
        gap.addProperty("readEventId",
                longInteger(subject, "readEventId", 0L));
        gap.addProperty("locationKey", string(subject, "locationKey"));
        gap.addProperty("readFromField", string(subject, "readFromField"));
        gap.addProperty("readerRegionId", string(subject, "readerRegionId"));
        gap.addProperty("selector", string(subject, "selector"));
        gap.addProperty("detail", detail == null ? "" : detail);
        return gap;
    }

    /**
     * Why {@code gate} must not be installed, or "" when it may be.
     *
     * <p>The invariants are checked, never assumed. A row that merely
     * <em>says</em> it observes only is refused here.</p>
     */
    public static String unsafeGateReason(JsonObject gate) {
        if (gate == null
                || !"SPARSE_READ_CUT_GATE".equals(string(gate, "kind"))
                || !AUTHORITY.equals(string(gate, "authority"))
                || JsonFields.integer(gate, "schemaVersion", -1)
                != SCHEMA_VERSION
                || longInteger(gate, "readEventId", 0L) <= 0L
                || longInteger(gate, "fieldVersionId", 0L) <= 0L
                || string(gate, "selector").isEmpty()) {
            return NOT_A_COMPILED_GATE;
        }
        if (!bool(gate, "observesOnly", false)
                || bool(gate, "writesProgramField", true)
                || bool(gate, "replacesRpcReturnValue", true)
                || !bool(gate, "requiresObservedReadVersion", false)
                || !bool(gate, "requiresObservedExchange", false)) {
            return INVARIANT_VIOLATED;
        }
        String placement = string(gate, "placement");
        if (!BEFORE_SELECTED_ACCESS.equals(placement)) {
            return NOT_A_COMPILED_GATE;
        }
        if (string(gate, "readFromField").isEmpty()
                || string(gate, "writerRegionId").isEmpty()
                || string(gate, "readerRegionId").isEmpty()) {
            return NO_CROSS_RUN_READ_IDENTITY;
        }
        return "";
    }

    /** Whether {@code gate} is a compiled gate that may be installed. */
    public static boolean installable(JsonObject gate) {
        return unsafeGateReason(gate).isEmpty();
    }

    private static List<Long> competitors(JsonObject candidate) {
        Set<Long> outside = new TreeSet<>();
        for (JsonElement element : array(candidate, "orderConstraints")) {
            JsonObject constraint = element.getAsJsonObject();
            if ("OTHER_WRITE_OUTSIDE_CUT".equals(
                    string(constraint, "kind"))) {
                outside.add(longInteger(constraint, "otherEventId", 0L));
            }
        }
        return new ArrayList<>(outside);
    }

    /** Named refusals, one per arm that cannot be gated safely. */
    public List<JsonObject> refusals() {
        return Collections.unmodifiableList(refusals);
    }

    /** Whether any candidate arm of this read can be enforced. */
    public boolean enforceable() {
        return !gates.isEmpty();
    }

    /** The gate for one selector, or an empty object. */
    public JsonObject gateFor(String selector) {
        for (JsonObject gate : gates) {
            if (string(gate, "selector").equals(selector)) {
                return gate.deepCopy();
            }
        }
        return new JsonObject();
    }

    /** The plan as one artifact-ready object. */
    public JsonObject toJson() {
        JsonObject plan = new JsonObject();
        plan.addProperty("schemaVersion", SCHEMA_VERSION);
        plan.addProperty("kind", KIND);
        plan.addProperty("authority", AUTHORITY);
        plan.addProperty("readEventId", readEventId);
        plan.addProperty("locationKey", locationKey);
        plan.addProperty("readFromField", readFromField);
        plan.addProperty("readerRegionId", readerRegionId);
        plan.addProperty("enforceable", enforceable());
        JsonArray enforced = new JsonArray();
        for (JsonObject gate : gates) enforced.add(gate.deepCopy());
        plan.add("gates", enforced);
        JsonArray refused = new JsonArray();
        for (JsonObject gap : refusals) refused.add(gap.deepCopy());
        plan.add("refusals", refused);
        return plan;
    }
}
