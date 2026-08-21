import java.util.LinkedHashMap;
import java.util.Map;

/** One NN key source shared by its field, Map index and promoted copy. */
public final class RegionSymbolicKeySourceSmoke {
    private static final String SOURCE = "HDFS11741.SOURCE.KEY.ID";

    private static final class Key {
        private int keyId;
        private Key(int keyId) { this.keyId = keyId; }
    }

    public static void main(String[] args) {
        Map<Integer, Key> allKeys = new LinkedHashMap<Integer, Key>();
        Key next = new Key(1307341805);
        allKeys.put(Integer.valueOf(next.keyId), next);

        require(System.startConcolicRegion(
                "REGION.symbolic-key-source", "TASK.symbolic-key-source")
                == 0L, "region rejected");
        require(System.selectSharedMapCarrier(allKeys) > 0L,
                "map carrier rejected");

        int concreteKeyId = next.keyId;
        System.symbolizeExactField(next, Key.class.getName(), "keyId", "I",
                SOURCE);
        Key indexed = allKeys.remove(Integer.valueOf(concreteKeyId));
        require(indexed == next, "baseline key was not indexed");
        allKeys.put(Integer.valueOf(next.keyId), indexed);

        // This is the HDFS rotation step: old nextKey becomes currentKey.
        Key current = new Key(next.keyId);
        allKeys.put(Integer.valueOf(current.keyId), current);

        String nextField = System.getSymbolicFieldExpression(next,
                Key.class.getName(), "keyId", "I",
                Integer.valueOf(next.keyId));
        String currentField = System.getSymbolicFieldExpression(current,
                Key.class.getName(), "keyId", "I",
                Integer.valueOf(current.keyId));
        String map = System.getSymbolicExpression(allKeys);
        require(nextField.contains(SOURCE), nextField);
        require(currentField.contains(SOURCE), currentField);
        require(map.contains(SOURCE), map);
        require(map.contains("REMOVE") && map.contains("PUT"), map);
        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "summary incomplete");
        System.out.println("CAUSYNTH_SYMBOLIC_KEY_SOURCE_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
