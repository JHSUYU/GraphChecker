import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * A tracked container's mutations are the model's whatever object reaches
 * the container, and what no model can state is named
 * ({@code ContainerSupport::admits}, {@code start_log}).
 *
 * <p>Every cursor and view here is built before the container's log begins
 * ({@code System.observeContainer}), so no model aliased it.  An ArrayList
 * iterator's {@code remove()} and a ConcurrentHashMap key iterator's are
 * versions; a HashSet's iterator walks the set's private HashMap, which the
 * set's log start made the set, so its {@code remove()} is a version of the
 * set.  A list iterator's {@code set()}, a deque iterator's {@code remove()}
 * (its index is the circular buffer's) and a key view's {@code remove(k)}
 * are no relation a model states: each leaves the container's log
 * incomplete by name.  A container a model abandoned is not taken again: a
 * later concrete add or put publishes nothing.</p>
 *
 * <p>The INITIAL an observation states: a view and a {@code Collections}
 * wrapper stand for their map; past the snapshot bound it is truncated; a
 * class the walk cannot read (a LinkedList) and a ConcurrentHashMap caught
 * mid-resize are refusals by name.</p>
 */
public final class RegionContainerAdmissionSmoke {
    public static void main(String[] args) throws Exception {
        List<String> list = new ArrayList<String>(Arrays.asList("a", "b", "c"));
        Iterator<String> listWalk = list.iterator();
        List<String> cursorList = new ArrayList<String>(Arrays.asList("x", "y"));
        ListIterator<String> listCursor = cursorList.listIterator();
        ArrayDeque<String> deque =
                new ArrayDeque<String>(Arrays.asList("p", "q"));
        Iterator<String> dequeWalk = deque.iterator();
        Set<String> set = new HashSet<String>(Arrays.asList("s1", "s2"));
        Iterator<String> setWalk = set.iterator();
        Map<String, Integer> keyed = new HashMap<String, Integer>();
        keyed.put("k1", 1);
        keyed.put("k2", 2);
        Set<String> keys = keyed.keySet();
        ConcurrentHashMap<String, Integer> concurrent =
                new ConcurrentHashMap<String, Integer>();
        concurrent.put("c1", 1);
        concurrent.put("c2", 2);
        Iterator<String> concurrentWalk = concurrent.keySet().iterator();
        Map<String, Integer> viewed = new HashMap<String, Integer>();
        viewed.put("v", 1);
        Map<String, Integer> wrapped = new HashMap<String, Integer>();
        wrapped.put("w", 1);
        Map<Integer, Integer> large = new HashMap<Integer, Integer>();
        for (int index = 0; index < 65; index++) {
            large.put(Integer.valueOf(index), Integer.valueOf(index));
        }
        LinkedList<String> linked = new LinkedList<String>();
        linked.add("l");
        ConcurrentHashMap<String, Integer> resizing =
                new ConcurrentHashMap<String, Integer>();
        resizing.put("r", 1);
        forwardOneBin(resizing);
        Map<String, Integer> abandoned = new HashMap<String, Integer>();
        abandoned.put("a1", 1);
        abandoned.put("a2", 2);

        require(System.startConcolicRegion("REGION.container-admission",
                "TASK.container-admission") == 0L, "region start rejected");
        Object[] observed = {list, cursorList, deque, set, keyed, concurrent,
                viewed.keySet(), Collections.unmodifiableMap(wrapped), large,
                linked, resizing, abandoned};
        for (Object container : observed) {
            require(System.observeContainer(container, false) == 0,
                    "no log started for " + container.getClass().getName());
        }

        listWalk.next();
        listWalk.remove();
        listCursor.next();
        listCursor.set("z");
        dequeWalk.next();
        dequeWalk.remove();
        setWalk.next();
        setWalk.remove();
        keys.remove("k1");
        concurrentWalk.next();
        concurrentWalk.remove();

        abandoned.values().removeIf(value -> value.intValue() == 1);

        // The list and the map the cursor and the key view abandoned: a
        // later concrete mutation is not taken again.
        String cursorAbandoned = System.getSharedMapVersions(cursorList);
        String keyedAbandoned = System.getSharedMapVersions(keyed);
        cursorList.add("w");
        keyed.put("k3", 3);

        String listLog = System.getSharedMapVersions(list);
        String cursorLog = System.getSharedMapVersions(cursorList);
        String dequeLog = System.getSharedMapVersions(deque);
        String setLog = System.getSharedMapVersions(set);
        String keyedLog = System.getSharedMapVersions(keyed);
        String concurrentLog = System.getSharedMapVersions(concurrent);
        String viewedLog = System.getSharedMapVersions(viewed);
        String wrappedLog = System.getSharedMapVersions(wrapped);
        String largeLog = System.getSharedMapVersions(large);
        String linkedLog = System.getSharedMapVersions(linked);
        String resizingLog = System.getSharedMapVersions(resizing);
        String abandonedLog = System.getSharedMapVersions(abandoned);
        System.endConcolic();

        modeled("an ArrayList iterator's remove()", listLog);
        modeled("a HashSet iterator's remove(), through the set's map", setLog);
        modeled("a ConcurrentHashMap iterator's remove()", concurrentLog);
        named("a list iterator's set()", cursorLog,
                "INDEXED_LIST_ITERATOR_MUTATOR_UNSUPPORTED");
        named("a deque iterator's remove()", dequeLog,
                "INDEXED_VIEW_OWNER_MISSING");
        named("a key view's remove(k)", keyedLog,
                "ASSOCIATIVE_REMOVE_OVERLOAD_UNSUPPORTED");
        require(viewedLog.contains("\"selected\":true")
                        && viewedLog.contains("\"stated\":true,\"entries\":1"),
                "a view's observation is not its map's: " + viewedLog);
        require(wrappedLog.contains("\"selected\":true")
                        && wrappedLog.contains("\"stated\":true,\"entries\":1"),
                "a wrapper's observation is not its map's: " + wrappedLog);
        require(largeLog.contains("\"truncated\":true"),
                "a map past the snapshot bound is not truncated: " + largeLog);
        require(linkedLog.contains("\"stated\":false")
                        && linkedLog.contains(
                                "\"unsupportedClass\":\"java/util/LinkedList\""),
                "an unreadable class is not refused by name: " + linkedLog);
        require(resizingLog.contains("\"unsupportedClass\":\"RESIZING\""),
                "a resize in flight is not refused by name: " + resizingLog);
        named("a values view's removeIf", abandonedLog,
                "ASSOCIATIVE_VALUES_REMOVE_IF_UNMODELED");
        require(count(cursorLog, "\"writerContextId\"")
                        == count(cursorAbandoned, "\"writerContextId\"")
                        && count(keyedLog, "\"writerContextId\"")
                        == count(keyedAbandoned, "\"writerContextId\""),
                "an abandoned container was taken again: " + cursorLog
                        + " / " + keyedLog);
        System.out.println("CAUSYNTH_REGION_CONTAINER_ADMISSION_SMOKE_OK");
    }

    /** A ConcurrentHashMap forwarding node in an empty bin: what a resize
     *  in flight leaves behind. */
    private static void forwardOneBin(ConcurrentHashMap<?, ?> map)
            throws Exception {
        Field table = ConcurrentHashMap.class.getDeclaredField("table");
        table.setAccessible(true);
        Object[] bins = (Object[]) table.get(map);
        Class<?> forwarding = Class.forName(
                "java.util.concurrent.ConcurrentHashMap$ForwardingNode");
        Constructor<?> make =
                forwarding.getDeclaredConstructor(bins.getClass());
        make.setAccessible(true);
        for (int index = 0; index < bins.length; index++) {
            if (bins[index] == null) {
                bins[index] = make.newInstance(new Object[]{Array.newInstance(
                        bins.getClass().getComponentType(), bins.length * 2)});
                return;
            }
        }
        throw new AssertionError("no empty bin to forward");
    }

    private static void modeled(String what, String log) {
        require(log.contains("\"selected\":true")
                        && log.contains("\"versionKind\":\"STATE_REMOVE\"")
                        && log.contains("\"writerSetComplete\":true"),
                what + " is no version of its container: " + log);
    }

    private static void named(String what, String log, String reason) {
        require(log.contains("\"writerSetComplete\":false")
                        && log.contains(reason),
                what + " is not named on its container's log: " + log);
    }

    private static int count(String text, String needle) {
        int found = 0;
        for (int at = text.indexOf(needle); at >= 0;
             at = text.indexOf(needle, at + needle.length())) {
            found++;
        }
        return found;
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
