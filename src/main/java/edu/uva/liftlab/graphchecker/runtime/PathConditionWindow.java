package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.VmExpressionTable;
import java.util.ArrayList;
import java.util.List;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;

/**
 * Indexed access to a window of the VM's path condition: the total count,
 * and the elements a branch event's indices name.
 */
final class PathConditionWindow {
    static final PathConditionWindow EMPTY =
            new PathConditionWindow(new JsonArray());

    private final JsonArray tree;
    /** Absolute index of element 0, and the exclusive end of the window. */
    private final int base;
    private final int windowEnd;
    /** Conditions the thread has accumulated, window or not. */
    private final int size;

    private PathConditionWindow(JsonArray tree) {
        this(tree, 0, tree.size(), tree.size());
    }

    private PathConditionWindow(JsonArray tree, int base, int windowEnd,
                                  int size) {
        this.tree = tree;
        this.base = base;
        this.windowEnd = windowEnd;
        this.size = size;
    }

    /**
     * One {@code CONCOLIC_PATH_CONDITION_RANGE} envelope, or null.  Read as
     * its conditions beside its table ({@link
     * VmExpressionTable.Store#importRecords}): the table repeats the whole
     * closure of the window's conditions, and a node an earlier window or
     * page expanded is not read again, so a branch costs what is new to it
     * (A2's SB19 seed replay: every branch of CreateCollectionCmd's
     * replica-position loop re-imported its closure whole).
     */
    static PathConditionWindow window(String envelope, int expectedStart,
                                        VmExpressionTable.Store store) {
        if (envelope == null) return null;
        try {
            JsonArray conditions = new JsonArray();
            JsonObject decoded = store.importRecords(envelope, "conditions",
                    stated -> true, conditions::add);
            int start = optionalInteger(decoded, "startIndex", -1);
            int end = optionalInteger(decoded, "endIndex", -1);
            int watermark = optionalInteger(decoded,
                    "pathConditionWatermark", -1);
            int declaredCount = optionalInteger(decoded, "conditionCount", -1);
            if (start != expectedStart || end < start
                    || watermark < 0
                    || conditions.size() != end - start
                    || declaredCount != conditions.size()) {
                return null;
            }
            return new PathConditionWindow(conditions, start, end,
                    watermark);
        } catch (RuntimeException malformed) {
            return null;
        }
    }

    int size() {
        return size;
    }

    JsonElement get(int index) {
        if (index < base || index >= windowEnd) {
            throw new IndexOutOfBoundsException(
                    "path condition index " + index + " outside ["
                            + base + "," + windowEnd + ") of " + size);
        }
        return tree.get(index - base);
    }

    /**
     * The window one VM branch event owns: empty when it names no condition
     * or its indices are not contiguous (the event stream is the authority).
     */
    static PathConditionWindow forEvent(VmExpressionTable.Store store,
                                        ConcolicVmBroker api,
                                        List<Integer> eventConditionIndices) {
        if (!contiguousConditionIndices(eventConditionIndices)) return EMPTY;
        int start = eventConditionIndices.get(0);
        int end = eventConditionIndices.get(
                eventConditionIndices.size() - 1) + 1;
        String windowed;
        try {
            windowed = api.pathConditionRange(start, end);
        } catch (Throwable refused) {
            windowed = null;
        }
        PathConditionWindow exact = window(windowed, start, store);
        return exact == null ? EMPTY : exact;
    }

    /** The records of one event stream numbered {@code eventId}. */
    static List<JsonObject> eventsNumbered(JsonObject stream, long eventId) {
        List<JsonObject> numbered = new ArrayList<>();
        for (JsonElement candidate : array(stream, "events")) {
            if (!candidate.isJsonObject()) continue;
            JsonObject event = candidate.getAsJsonObject();
            if (optionalLongInteger(event, "eventId", -1L) == eventId) {
                numbered.add(event);
            }
        }
        return numbered;
    }

    /** The one event's condition indices, or null when not exactly one. */
    static List<Integer> vmEventConditionIndices(
            JsonElement parsed, long eventId) {
        if (!parsed.isJsonObject()) return null;
        List<JsonObject> numbered = eventsNumbered(parsed.getAsJsonObject(),
                eventId);
        if (numbered.size() != 1) return null;
        JsonObject selected = numbered.get(0);
        JsonArray raw = array(selected, "conditionIndices");
        if (optionalInteger(selected, "conditionCount", -1) != raw.size()) {
            return null;
        }
        List<Integer> indices = new ArrayList<>();
        for (JsonElement value : raw) {
            try {
                indices.add(value.getAsInt());
            } catch (RuntimeException malformed) {
                return null;
            }
        }
        return indices;
    }

    static boolean contiguousConditionIndices(List<Integer> indices) {
        if (indices == null || indices.isEmpty()) return false;
        int expected = indices.get(0);
        if (expected < 0) return false;
        for (Integer index : indices) {
            if (index == null || index != expected) return false;
            expected++;
        }
        return true;
    }
}
