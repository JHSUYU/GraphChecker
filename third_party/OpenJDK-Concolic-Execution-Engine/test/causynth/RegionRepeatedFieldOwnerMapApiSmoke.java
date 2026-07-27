import java.util.HashMap;
import java.util.Map;

/**
 * Verifies that one Java field declaration can be symbolized independently
 * on several concrete owners during one concolic region.  The runtime region
 * planner relies on this property when one container operation consumes
 * several independently named primitive leaves.
 */
public final class RegionRepeatedFieldOwnerMapApiSmoke {
    private static final class Key {
        private int keyId;

        private Key(int keyId) {
            this.keyId = keyId;
        }
    }

    public static void main(String[] args) {
        Key[] keys = new Key[] {
                new Key(11), new Key(12), new Key(13), new Key(14)
        };
        Map<Integer, Key> values = new HashMap<Integer, Key>();

        System.startConcolicRegion("REGION.repeated-field-owner-map",
                "ACT.repeated-field-owner-map");
        for (int index = 0; index < keys.length; index++) {
            String symbol = "container_key_index_" + index;
            System.symbolizeField(keys[index], "keyId", symbol);
            values.put(keys[index].keyId, keys[index]);
        }
        String relation = System.getSymbolicExpression(values);
        System.finishConcolicRegion();

        require(values.size() == 4, "concrete map size");
        require(relation.contains("\"_type\":\"ContainerRelation\""),
                relation);
        require(relation.contains("\"operation\":\"PUT\""), relation);
        for (int index = 0; index < keys.length; index++) {
            String symbol = "container_key_index_" + index;
            require(relation.contains(symbol), relation);
        }
        System.out.println(
                "CAUSYNTH_REGION_REPEATED_FIELD_OWNER_MAP_API_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
