import java.util.ArrayDeque;
import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Queue;

/** Container live-ins drive symbolic method results from one canonical state. */
public final class RegionContainerLiveInApiSmoke {
    public static void main(String[] args) {
        Map<Integer, Object[]> map = new LinkedHashMap<Integer, Object[]>();
        map.put(Integer.valueOf(211),
                new Object[]{Integer.valueOf(223)});

        List<Integer> list = new ArrayList<Integer>();
        list.add(Integer.valueOf(227));

        Queue<Integer> queue = new ArrayDeque<Integer>();
        queue.offer(Integer.valueOf(229));
        queue.offer(Integer.valueOf(233));

        long status = System.startConcolicRegion(
                "REGION.container-live-in", "TASK.container-live-in");
        require(status == 0L, "region start rejected");
        require(System.trackContainerExpression(
                        map, "REGION.container.in.map"),
                "map live-in rejected");
        require(System.trackContainerExpression(
                        list, "REGION.container.in.list"),
                "list live-in rejected");
        require(System.trackContainerExpression(
                        queue, "REGION.container.in.queue"),
                "queue live-in rejected");

        require(relation(map, "REGION.container.in.map"),
                "map canonical identity");
        Object[] mapResult = map.get(Integer.valueOf(211));
        require(read(mapResult), "Map.get result");
        require(System.getSymbolicExpression(mapResult).contains(
                        "\"_exp\":\"Y_I_211\""),
                "Map.get lost concrete boxed key");
        Iterator<Map.Entry<Integer, Object[]>> entries =
                map.entrySet().iterator();
        Map.Entry<Integer, Object[]> entry = entries.next();
        require(relation(entry, "\"operation\":\"NEXT\""),
                "Map iterator entry result");
        Integer entryKey = entry.getKey();
        require(relation(entryKey, "\"operation\":\"KEY\""),
                "Map entry key result");
        Integer listResult = list.get(0);
        require(read(listResult), "List.get result");
        Iterator<Integer> listIterator = list.iterator();
        Integer iterated = listIterator.next();
        require(relation(iterated, "\"operation\":\"NEXT\""),
                "List iterator result");
        ListIterator<Integer> indexedIterator = list.listIterator();
        require(indexedIterator.nextIndex() == 0,
                "ListIterator initial index");
        Integer indexed = indexedIterator.next();
        require(relation(indexed, "\"operation\":\"NEXT\""),
                "ListIterator result");
        require(indexedIterator.nextIndex() == 1,
                "ListIterator advanced index");
        indexedIterator.remove();
        require(indexedIterator.nextIndex() == 0,
                "ListIterator index after removal");
        List<Integer> abstractList = new FixedAbstractList();
        require(System.trackContainerExpression(
                        abstractList, "REGION.container.in.abstract-list"),
                "AbstractList live-in rejected");
        ListIterator<Integer> abstractIterator = abstractList.listIterator();
        require(abstractIterator.nextIndex() == 0,
                "AbstractList iterator initial index");
        require(relation(abstractIterator.next(),
                        "\"operation\":\"NEXT\""),
                "AbstractList iterator result");
        Integer peekResult = queue.peek();
        require(read(peekResult), "Queue.peek result");
        Integer pollResult = queue.poll();
        require(read(pollResult), "Queue.poll result");
        require(relation(queue, "\"operation\":\"REMOVE\""),
                "Queue.poll state");
        require(System.trackContainerExpression(
                        queue, "REGION.container.in.redundant"),
                "repeated queue live-in rejected");
        String queueState = System.getSymbolicExpression(queue);
        require(queueState.contains("\"operation\":\"REMOVE\"")
                        && queueState.contains("REGION.container.in.queue")
                        && !queueState.contains(
                        "REGION.container.in.redundant"),
                "repeated tracking reset canonical state: " + queueState);

        String summary = System.finishConcolicRegion();
        require(summary.contains("\"complete\":true"), summary);
        System.out.println("CAUSYNTH_REGION_CONTAINER_LIVE_IN_API_SMOKE_OK");
    }

    private static boolean read(Object value) {
        return relation(value, "\"operation\":\"READ\"");
    }

    private static boolean relation(Object value, String operation) {
        String expression = System.getSymbolicExpression(value);
        boolean matches = expression.contains("\"symbolic\":true")
                && expression.contains(operation);
        if (!matches) {
            System.err.println("missing " + operation + " in " + expression);
        }
        return matches;
    }

    private static final class FixedAbstractList
            extends AbstractList<Integer> {
        public Integer get(int index) {
            if (index != 0) throw new IndexOutOfBoundsException();
            return Integer.valueOf(239);
        }

        public int size() {
            return 1;
        }
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
