import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** One smoke contract for every activation-local container shape. */
public final class RegionContainerRelationApiSmoke {
    private static final class Input {
        int[] array = {3, 7};
        Map<Integer, Integer> map = new LinkedHashMap<Integer, Integer>();
        List<Integer> list = new ArrayList<Integer>();
        Set<Integer> set = new HashSet<Integer>();
        ArrayDeque<Integer> queue = new ArrayDeque<Integer>();

        Input() {
            map.put(Integer.valueOf(7), Integer.valueOf(11));
            list.add(Integer.valueOf(13));
            list.add(Integer.valueOf(17));
            set.add(Integer.valueOf(19));
            queue.add(Integer.valueOf(23));
        }
    }

    public static void main(String[] args) {
        Input input = new Input();
        System.startConcolicRegion("REGION.container-v2",
                "TASK.container-v2");
        System.symbolizeField(input, "array", "container_array");
        System.symbolizeField(input, "map", "container_map");
        System.symbolizeField(input, "list", "container_list");
        System.symbolizeField(input, "set", "container_set");
        System.symbolizeField(input, "queue", "container_queue");

        input.array[1] = input.array[0] + 2;
        input.map.put(Integer.valueOf(9), input.map.get(Integer.valueOf(7)));
        Iterator<Map.Entry<Integer, Integer>> mapIterator =
                input.map.entrySet().iterator();
        require(mapIterator.hasNext(), "map iterator");
        Map.Entry<Integer, Integer> entry = mapIterator.next();
        require(entry.getKey() != null && entry.getValue() != null,
                "map entry");
        mapIterator.remove();

        input.list.set(1, input.list.get(0));
        Iterator<Integer> listIterator = input.list.iterator();
        require(listIterator.hasNext(), "list iterator");
        require(listIterator.next() != null, "list next");
        listIterator.remove();

        require(input.set.contains(Integer.valueOf(19)), "set contains");
        Iterator<Integer> setIterator = input.set.iterator();
        require(setIterator.hasNext(), "set iterator");
        require(setIterator.next() != null, "set next");
        setIterator.remove();

        input.queue.offer(Integer.valueOf(29));
        require(input.queue.peek() != null, "queue peek");
        require(input.queue.poll() != null, "queue poll");

        String arrayRelation = System.getSymbolicExpression(input.array);
        String mapRelation = System.getSymbolicExpression(input.map);
        require(relation(arrayRelation), "array relation");
        require(relation(mapRelation), "map relation");
        require(relation(System.getSymbolicExpression(input.list)),
                "list relation");
        require(relation(System.getSymbolicExpression(input.set)),
                "set relation");
        require(relation(System.getSymbolicExpression(input.queue)),
                "queue relation");
        require(mapRelation.contains("\"operation\":\"REMOVE_AT\""),
                mapRelation);
        String summary = System.finishConcolicRegion();
        require(summary.contains("ContainerRelation"), summary);
        System.out.println("CAUSYNTH_REGION_CONTAINER_RELATION_API_SMOKE_OK");
    }

    private static boolean relation(String expression) {
        return expression.contains("\"kind\":\"CONTAINER_RELATION\"")
                && expression.contains("\"_type\":\"ContainerRelation\"");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
