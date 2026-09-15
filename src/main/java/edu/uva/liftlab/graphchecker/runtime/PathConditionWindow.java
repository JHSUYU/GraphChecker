package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.plan.VmExpressionTable;
import java.util.ArrayList;
import java.util.List;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalLongInteger;

/**
 * Indexed access to a serialized path condition without materializing
 * every element.
 *
 * <p>A branch hook needs exactly two facts from that document: how many
 * conditions the VM has accumulated, and the one element the VM's exact
 * event says this branch owns - an index the event stream, a few kilobytes
 * wide, already carries.</p>
 */
final class PathConditionWindow {
    static final PathConditionWindow EMPTY =
            new PathConditionWindow(new JsonArray());
    private static final String TREE_MODE = "TREE";
    private static final String WINDOW_MODE = "WINDOW_SCAN";

    private final JsonArray tree;
    /** Absolute index of element 0, and the exclusive end of the window. */
    private final int base;
    private final int windowEnd;
    /** Conditions the thread has accumulated, window or not. */
    private final int size;
    private final boolean windowed;

    private PathConditionWindow(JsonArray tree) {
        this(tree, 0, tree.size(), tree.size(), false);
    }

    private PathConditionWindow(JsonArray tree, int base, int windowEnd,
                                  int size, boolean windowed) {
        this.tree = tree;
        this.base = base;
        this.windowEnd = windowEnd;
        this.size = size;
        this.windowed = windowed;
    }

    /**
     * Reads one {@code CONCOLIC_PATH_CONDITION_RANGE} envelope as the
     * conditions at absolute indices {@code [startIndex, endIndex)}.
     *
     * <p>The VM always writes the window through the session expression
     * table, so the envelope is decoded once by the shared importer and
     * never rescanned by hand.</p>
     */
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
                    watermark, true);
        } catch (RuntimeException malformed) {
            return null;
        }
    }

    /** Conditions the thread has accumulated, not just this window's. */
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

    /** Which reader answered, for the replay's own diagnostics. */
    String mode() {
        return windowed ? WINDOW_MODE : TREE_MODE;
    }

    /** One branch hook's exact, VM-owned condition window. */
    static final class Read {
        final PathConditionWindow conditions;
        final int chars;
        final String source;

        Read(PathConditionWindow conditions, int chars, String source) {
            this.conditions = conditions;
            this.chars = chars;
            this.source = source;
        }
    }

    /** Told the exact range a read is about to take, for a tracing caller. */
    interface RangeTrace {
        void range(int start, int end);
    }

    /**
     * The condition window one VM branch event owns.  An event that named no
     * condition contributes none; an event whose condition indices are not
     * contiguous is not an exact range, and the event stream is the only
     * authority on which conditions belong to the branch, so neither is read
     * from the store.  Both branch hooks used to spell this out themselves.
     */
    static Read forEvent(VmExpressionTable.Store store, ConcolicVmBroker api,
                         List<Integer> eventConditionIndices,
                         RangeTrace trace) throws Exception {
        if (eventConditionIndices != null && eventConditionIndices.isEmpty()) {
            return new Read(PathConditionWindow.EMPTY, 0,
                    "CONDITIONLESS_EVENT");
        }
        if (!contiguousConditionIndices(eventConditionIndices)) {
            return new Read(PathConditionWindow.EMPTY, -1,
                    "EXACT_RANGE_UNAVAILABLE");
        }
        int start = eventConditionIndices.get(0);
        int end = eventConditionIndices.get(
                eventConditionIndices.size() - 1) + 1;
        if (trace != null) trace.range(start, end);
        return readPathConditionRange(store, api, start, end);
    }

    /** Reads only the absolute indices named by an exact VM branch event. */
    static Read readPathConditionRange(
            VmExpressionTable.Store store, ConcolicVmBroker api,
            int start, int end)
            throws Exception {
        if (start < 0 || end <= start) {
            return new Read(PathConditionWindow.EMPTY, -1,
                    "EXACT_RANGE_UNAVAILABLE");
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
            return new Read(PathConditionWindow.EMPTY,
                    windowed == null ? -1 : windowed.length(),
                    "EXACT_RANGE_REFUSED");
        }
        return new Read(exact, windowed.length(),
                "EXACT_EVENT_RANGE");
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
