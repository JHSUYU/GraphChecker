import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Verifies {@code System.getLiveSharedVersion}: the version live at a
 * container's whole state and at a field moves with every write, a removal
 * through an iterator moves the container's own version, and asking through
 * the iterator names the container it iterates.
 */
public final class RegionLiveSharedVersionSmoke {
    private static final class State {
        private final Map<Integer, Long> entries =
                new LinkedHashMap<Integer, Long>();
        private long stamp;
    }

    public static void main(String[] args) {
        State state = new State();
        state.entries.put(7, 10L);
        state.entries.put(8, 30L);

        System.startConcolicRegion("REGION.live", "ACT.live");
        System.symbolizeField(state, "entries", "live_map");
        System.symbolizeField(state, "stamp", "live_stamp");
        long untouched = live(state.entries);
        state.entries.put(9, state.stamp);
        long afterPut = live(state.entries);
        Iterator<Map.Entry<Integer, Long>> iterator =
                state.entries.entrySet().iterator();
        iterator.next();
        iterator.remove();
        long afterRemove = live(state.entries);
        long throughView = live(iterator);
        state.stamp = state.stamp + 1;
        long firstStamp = field(state);
        state.stamp = state.stamp + 1;
        long secondStamp = field(state);
        String summary = System.finishConcolicRegion();

        require(afterPut > 0L && afterPut > untouched,
                "a put leaves a newer live version: " + untouched + " -> "
                        + afterPut + " " + summary);
        require(afterRemove > afterPut,
                "an iterator's removal moves the map's version: " + afterPut
                        + " -> " + afterRemove);
        require(throughView == afterRemove,
                "the iterator names the map it iterates: " + throughView
                        + " vs " + afterRemove);
        require(firstStamp > 0L && secondStamp > firstStamp,
                "a field's live version moves with its writes: "
                        + firstStamp + " -> " + secondStamp);
        require(System.getLiveSharedVersion(new Object(), null, null, null,
                -1) == 0L, "an object the session never tracked has none");
        System.out.println("CAUSYNTH_REGION_LIVE_SHARED_VERSION_SMOKE_OK");
    }

    private static long live(Object container) {
        return System.getLiveSharedVersion(container, null, null, null, -1);
    }

    private static long field(State state) {
        return System.getLiveSharedVersion(state, State.class.getName(),
                "stamp", "J", -1);
    }

    private static void require(boolean condition, String detail) {
        if (!condition) {
            throw new AssertionError(detail);
        }
    }
}
