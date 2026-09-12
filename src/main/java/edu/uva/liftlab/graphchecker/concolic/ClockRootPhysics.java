package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * What a wall clock can physically have returned.
 *
 * <p>A {@code Timer.now()} return is symbolized like any other external call,
 * and its only constraint was the 64-bit integral domain.  A solver is
 * therefore free to answer {@code Long.MIN_VALUE} at one read and
 * {@code -60002} at the next, and a witness built on that reads as a causal
 * story when it is arithmetic noise: no clock runs backwards by 2^63
 * milliseconds between two statements of one method.</p>
 *
 * <p>Two facts the recording already carries fix that without pinning the
 * clock to what it happened to read:</p>
 *
 * <ul>
 *   <li><b>Monotonicity.</b> Successive reads on one node, in the recorded
 *   program order, are non-decreasing.  {@code System.currentTimeMillis} is
 *   not guaranteed monotonic across an NTP step, but a step large enough to
 *   reorder two reads inside one replayed region is not the mechanism any of
 *   these workloads is about, and leaving the order free admits far more
 *   nonsense than it admits real behaviour.</li>
 *   <li><b>A session window.</b> Each read stays within a configurable skew
 *   of the value that read actually returned.</li>
 * </ul>
 *
 * <p>The window is deliberately per read and per node rather than one global
 * clock: <em>cross-node clock skew is a real failure mechanism</em> for the
 * workloads this checker targets, so two nodes' windows are anchored
 * separately and may be separated by up to twice the skew.  Nothing here
 * pins a clock to its recorded value; the point is to keep the explorable
 * space physical.</p>
 */
public final class ClockRootPhysics {
    public static final String MANIFEST_FIELD = "clockRootPhysics";
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "CLOCK_ROOT_PHYSICS";
    public static final String AUTHORITY =
            "RECORDED_CLOCK_WINDOW_AND_ORDER_V1";
    /** Default half-width of a clock's window: five minutes. */
    public static final long DEFAULT_SKEW_MILLIS = 300000L;

    /** Declared callees whose return value is a wall clock in milliseconds. */
    private static final List<String> CLOCK_CALLEES = java.util.Arrays.asList(
            "<org.apache.hadoop.util.Timer: long now()>",
            "<java.lang.System: long currentTimeMillis()>",
            "<org.apache.hadoop.util.Time: long now()>",
            "<org.apache.hadoop.util.Time: long monotonicNow()>");

    /** One symbolized wall-clock read. */
    public static final class ClockRead {
        public final String sourceKey;
        public final String portId;
        public final String siteId;
        public final String occurrenceId;
        public final long eventSeq;
        public final long recordedValue;

        ClockRead(String sourceKey, String portId, String siteId,
                  String occurrenceId, long eventSeq, long recordedValue) {
            this.sourceKey = sourceKey;
            this.portId = portId;
            this.siteId = siteId;
            this.occurrenceId = occurrenceId;
            this.eventSeq = eventSeq;
            this.recordedValue = recordedValue;
        }
    }

    private ClockRootPhysics() {
    }

    public static boolean clockCallee(String declaredCallee) {
        return declaredCallee != null && CLOCK_CALLEES.contains(declaredCallee);
    }

    /**
     * Every wall-clock read the plan symbolizes, grouped by node and ordered
     * by the recorded event sequence within it.
     *
     * <p>The plan states each read once per {@code portId}: the port is what
     * mints the manual root, so two rows for one port are one symbol and are
     * reduced to the earliest recorded event.</p>
     */
    public static Map<String, List<ClockRead>> readsByNode(
            Collection<JsonObject> planRows) {
        Map<String, ClockRead> byPort = new LinkedHashMap<>();
        for (JsonObject plan : planRows == null
                ? java.util.Collections.<JsonObject>emptyList() : planRows) {
            if (plan == null) continue;
            for (com.google.gson.JsonElement goal
                    : array(plan, "closureGoals")) {
                if (!goal.isJsonObject()) continue;
                for (com.google.gson.JsonElement encoded
                        : array(goal.getAsJsonObject(), "symbolize")) {
                    if (!encoded.isJsonObject()) continue;
                    JsonObject row = encoded.getAsJsonObject();
                    if (!clockCallee(optionalString(row, "declaredCallee"))) {
                        continue;
                    }
                    String port = optionalString(row, "portId");
                    String node = optionalString(row, "sourceKey");
                    long eventSeq = optionalLongInteger(row, "eventSeq", -1L);
                    String recorded = optionalString(row, "primitiveValue");
                    if (port.isEmpty() || node.isEmpty() || eventSeq < 0L
                            || recorded.isEmpty()) {
                        continue;
                    }
                    long value;
                    try {
                        value = Long.parseLong(recorded.trim());
                    } catch (NumberFormatException notIntegral) {
                        continue;
                    }
                    ClockRead read = new ClockRead(node, port,
                            optionalString(row, "siteId"),
                            optionalString(row, "occurrenceId"), eventSeq,
                            value);
                    ClockRead held = byPort.get(port);
                    if (held == null || read.eventSeq < held.eventSeq) {
                        byPort.put(port, read);
                    }
                }
            }
        }
        Map<String, List<ClockRead>> byNode = new LinkedHashMap<>();
        for (ClockRead read : byPort.values()) {
            byNode.computeIfAbsent(read.sourceKey,
                    ignored -> new ArrayList<>()).add(read);
        }
        for (List<ClockRead> reads : byNode.values()) {
            reads.sort(Comparator.comparingLong(read -> read.eventSeq));
        }
        return byNode;
    }

    /** The window one read's value may take, as an SMT constraint. */
    static String window(String term, long recordedValue, long skewMillis) {
        return "(and (>= " + term + " " + literal(recordedValue - skewMillis)
                + ") (<= " + term + " "
                + literal(recordedValue + skewMillis) + "))";
    }

    private static String literal(long value) {
        return value < 0L ? "(- " + Math.negateExact(value) + ")"
                : Long.toString(value);
    }

    /**
     * The composition-time ledger a witness reader needs: which solver term
     * is which node's clock, and what that read actually returned.
     */
    public static JsonObject manifest(long skewMillis,
                                      Collection<JsonObject> rows) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        result.addProperty("authority", AUTHORITY);
        result.addProperty("clockSkewMillis", skewMillis);
        JsonArray reads = new JsonArray();
        for (JsonObject row : rows) reads.add(row);
        result.add("clockReads", reads);
        return result;
    }

    /** One ledger row for a lowered clock read. */
    public static JsonObject ledgerRow(ClockRead read, String solverTerm,
                                       String windowAssertion,
                                       String orderAssertion) {
        JsonObject row = new JsonObject();
        row.addProperty("sourceKey", read.sourceKey);
        row.addProperty("portId", read.portId);
        row.addProperty("siteId", read.siteId);
        row.addProperty("occurrenceId", read.occurrenceId);
        row.addProperty("eventSeq", read.eventSeq);
        row.addProperty("recordedValue", read.recordedValue);
        row.addProperty("solverTerm", solverTerm);
        row.addProperty("windowAssertion", windowAssertion);
        row.addProperty("orderAssertion", orderAssertion);
        return row;
    }

    /** Whether the plan declares any wall-clock root at all. */
    public static boolean declaresClock(Collection<JsonObject> planRows) {
        return !readsByNode(planRows).isEmpty();
    }

    /** Reads the configured skew from a manifest row, for consumers. */
    public static long skewOf(JsonObject manifest) {
        JsonObject row = object(manifest, MANIFEST_FIELD);
        return row.size() == 0 ? DEFAULT_SKEW_MILLIS
                : optionalLongInteger(row, "clockSkewMillis",
                DEFAULT_SKEW_MILLIS);
    }
}
