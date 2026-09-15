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

        int concreteKeyId = next.keyId;
        System.symbolizeExactField(next, Key.class.getName(), "keyId", "I",
                SOURCE);
        Key indexed = allKeys.remove(Integer.valueOf(concreteKeyId));
        require(indexed == next, "baseline key was not indexed");
        allKeys.put(Integer.valueOf(next.keyId), indexed);

        // This is the HDFS rotation step: old nextKey becomes currentKey.
        // The remove above took a concrete key, so no relation records it: a
        // mutation joins the chain when one of its operands is symbolic.
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
        // The chain the map carries: the base the recorder walked before the
        // first symbolic mutation, then one PUT per symbolically keyed put --
        // the re-index of `next` and the promotion of `current`.
        require(map.contains("\"operation\":\"SNAPSHOT_BASE\""), map);
        require(count(map, "\"operation\":\"PUT\"") == 2, map);
        require(map.contains("\"shape\":\"ASSOCIATIVE\""), map);
        require(System.finishConcolicRegion().contains("\"complete\":true"),
                "summary incomplete");
        System.out.println("CAUSYNTH_SYMBOLIC_KEY_SOURCE_SMOKE_OK");
    }

    private static int count(String text, String fragment) {
        int matches = 0;
        int cursor = 0;
        while ((cursor = text.indexOf(fragment, cursor)) >= 0) {
            matches++;
            cursor += fragment.length();
        }
        return matches;
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
