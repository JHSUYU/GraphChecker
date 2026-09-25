package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.VmExpressionTable;
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

    /** One {@code CONCOLIC_PATH_CONDITION_RANGE} envelope, or null. */
    static PathConditionWindow window(String envelope, int expectedStart,
                                        VmExpressionTable.Store store) {
        if (envelope == null) return null;
        try {
            JsonObject decoded = store.importEnvelope(envelope);
            int start = optionalInteger(decoded, "startIndex", -1);
            int end = optionalInteger(decoded, "endIndex", -1);
            int watermark = optionalInteger(decoded,
                    "pathConditionWatermark", -1);
            JsonArray conditions = array(decoded, "conditions");
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

    /** One branch hook's exact, VM-owned condition window. */
    static final class Read {
        final PathConditionWindow conditions;

        Read(PathConditionWindow conditions) {
            this.conditions = conditions;
        }
    }

    /**
     * The window one VM branch event owns: empty when it names no condition
     * or its indices are not contiguous (the event stream is the authority).
     */
    static Read forEvent(VmExpressionTable.Store store, ConcolicVmBroker api,
                         List<Integer> eventConditionIndices)
            throws Exception {
        if (eventConditionIndices != null && eventConditionIndices.isEmpty()) {
            return new Read(PathConditionWindow.EMPTY);
        }
        if (!contiguousConditionIndices(eventConditionIndices)) {
            return new Read(PathConditionWindow.EMPTY);
        }
        int start = eventConditionIndices.get(0);
        int end = eventConditionIndices.get(
                eventConditionIndices.size() - 1) + 1;
        return readPathConditionRange(store, api, start, end);
    }

    /** Reads only the absolute indices named by an exact VM branch event. */
    static Read readPathConditionRange(
            VmExpressionTable.Store store, ConcolicVmBroker api,
            int start, int end)
            throws Exception {
        if (start < 0 || end <= start) {
            return new Read(PathConditionWindow.EMPTY);
        }
        String windowed;
        try {
            windowed = api.pathConditionRange(start, end);
        } catch (Throwable refused) {
            windowed = null;
        }
        PathConditionWindow exact =
                PathConditionWindow.window(windowed, start, store);
        if (exact == null) {
            return new Read(PathConditionWindow.EMPTY);
        }
        return new Read(exact);
    }

    static List<Integer> vmEventConditionIndices(
            JsonElement parsed, long eventId) {
        if (!parsed.isJsonObject()) return null;
        JsonObject selected = null;
        int matches = 0;
        for (JsonElement candidate : array(
                parsed.getAsJsonObject(), "events")) {
            if (!candidate.isJsonObject()) continue;
            JsonObject event = candidate.getAsJsonObject();
            if (optionalLongInteger(event, "eventId", -1L) == eventId) {
                selected = event;
                matches++;
            }
        }
        if (matches != 1 || selected == null) return null;
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
