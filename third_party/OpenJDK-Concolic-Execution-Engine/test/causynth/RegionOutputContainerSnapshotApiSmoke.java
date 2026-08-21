import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/** Exact normal-exit snapshots for containers created inside a region. */
public final class RegionOutputContainerSnapshotApiSmoke {
    public static void main(String[] args) {
        long status = System.startConcolicRegion(
                "REGION.container-output", "TASK.container-output");
        require(status == 0L, "region start rejected");

        Map<Integer, Integer> map = new LinkedHashMap<Integer, Integer>();
        map.put(Integer.valueOf(7), Integer.valueOf(11));
        require(System.snapshotContainerExpression(map,
                        new Object[]{Integer.valueOf(7)},
                        new Object[]{Integer.valueOf(11)}, 1),
                "map snapshot rejected");
        map.put(Integer.valueOf(9), Integer.valueOf(13));

        Map<Integer, Integer> trackedMap =
                new LinkedHashMap<Integer, Integer>();
        trackedMap.put(Integer.valueOf(53), Integer.valueOf(59));
        require(System.trackContainerExpression(trackedMap, "inputMap"),
                "tracked map rejected");
        trackedMap.remove(Integer.valueOf(53));
        trackedMap.put(Integer.valueOf(61), Integer.valueOf(67));
        require(System.snapshotContainerExpression(trackedMap,
                        new Object[]{Integer.valueOf(61)},
                        new Object[]{Integer.valueOf(67)}, 1),
                "tracked map snapshot rejected");

        List<Integer> list = new ArrayList<Integer>();
        list.add(Integer.valueOf(17));
        list.add(Integer.valueOf(19));
        require(System.snapshotContainerExpression(list, null,
                        list.toArray(), 0),
                "list snapshot rejected");

        List<Integer> linkedList = new LinkedList<Integer>();
        linkedList.add(Integer.valueOf(37));
        linkedList.add(Integer.valueOf(41));
        require(System.snapshotContainerExpression(linkedList, null,
                        linkedList.toArray(), 0),
                "linked-list snapshot rejected");

        Map<Integer, Integer> treeMap = new TreeMap<Integer, Integer>();
        treeMap.put(Integer.valueOf(43), Integer.valueOf(47));
        require(System.snapshotContainerExpression(treeMap,
                        new Object[]{Integer.valueOf(43)},
                        new Object[]{Integer.valueOf(47)}, 1),
                "tree-map snapshot rejected");

        Set<Integer> set = new LinkedHashSet<Integer>();
        set.add(Integer.valueOf(23));
        Object[] setElements = set.toArray();
        require(System.snapshotContainerExpression(set, setElements,
                        new Object[setElements.length], 2),
                "set snapshot rejected");

        int[] array = new int[]{29, 31};
        require(System.snapshotContainerExpression(array, null,
                        new Object[]{Integer.valueOf(29),
                                Integer.valueOf(31)}, 3),
                "array snapshot rejected");

        require(relation(map, "\"operation\":\"PUT\""),
                "map relation: " + System.getSymbolicExpression(map));
        require(System.getSymbolicExpression(map).contains(
                        "\"operation\":\"SNAPSHOT_BASE\""),
                "map snapshot base missing");
        require(relation(trackedMap, "\"operation\":\"PUT\""),
                "tracked map relation");
        require(relation(list, "\"operation\":\"APPEND\""),
                "list relation");
        require(relation(linkedList, "\"operation\":\"APPEND\""),
                "linked-list relation");
        require(relation(treeMap, "\"operation\":\"PUT\""),
                "tree-map relation");
        require(relation(set, "\"operation\":\"PUT\""),
                "set relation");
        require(relation(array, "\"operation\":\"WRITE\""),
                "array relation");

        String summary = System.finishConcolicRegion();
        require(summary.contains("\"complete\":true"), summary);
        System.out.println(
                "CAUSYNTH_REGION_OUTPUT_CONTAINER_SNAPSHOT_API_SMOKE_OK");
    }

    private static boolean relation(Object value, String operation) {
        String expression = System.getSymbolicExpression(value);
        return expression.contains("\"kind\":\"CONTAINER_RELATION\"")
                && expression.contains(operation);
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
