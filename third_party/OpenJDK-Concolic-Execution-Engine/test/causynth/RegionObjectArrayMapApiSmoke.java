import java.util.HashMap;
import java.util.Map;

/**
 * Neutral regression for the symbolic propagation chain used by producer
 * regions: object-array load -> primitive element field -> boxing -> Map.put.
 */
public final class RegionObjectArrayMapApiSmoke {
    private static final class Entry {
        final int keyId;

        private Entry(int keyId) {
            this.keyId = keyId;
        }

        int getKeyId() {
            return keyId;
        }
    }

    private static final class Input {
        final Entry[] entries = {new Entry(7), new Entry(11)};
    }

    public static void main(String[] args) {
        Input input = new Input();
        Map<Integer, Entry> map = new HashMap<Integer, Entry>();

        System.startConcolicRegion("REGION.object-array-map",
                "ACT.object-array-map");
        System.symbolizeField(input, "entries", "object_array_map_entries");
        for (int i = 0; i < input.entries.length; i++) {
            Entry entry = input.entries[i];
            map.put(entry.getKeyId(), entry);
        }
        String relation = System.getSymbolicExpression(map);
        String summary = System.finishConcolicRegion();

        require(relation.contains("\"operation\":\"PUT\""), relation);
        require(relation.contains("ContainerRelation"), relation);
        require(relation.contains("\"_type\":\"FieldAccessExpression\""),
                relation);
        require(summary.contains("\"complete\":true"), summary);
        System.out.println("CAUSYNTH_REGION_OBJECT_ARRAY_MAP_API_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) {
            throw new AssertionError(detail);
        }
    }
}
