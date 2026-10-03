package edu.uva.liftlab.graphchecker.smt;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * The JDK container contracts, by interface (R3-REFCONT SS2.1): what a call
 * on a container does is its interface's -- a query reads the container's
 * state, a mutation changes it -- whatever class answers it.  Which
 * interfaces a class honors is the Soot hierarchy's answer where the caller
 * has one, else the fixed list of JDK classes below.  Whether the VM models
 * the class (its capability, and an application subclass is refused) is
 * decided at run time, never here: the static side classifies by interface
 * only.  A call is named by its name and parameters, never its return type,
 * which an implementation narrows ({@code ConcurrentHashMap.keySet()} returns
 * a {@code KeySetView}).
 *
 * <p>A stream is a query over its source: every call of a {@code
 * java.util.stream} pipeline ({@code BaseStream} and its subtypes) and of
 * {@code Collectors} reads its receiver and its arguments, and a collection
 * hands its state to one by {@code stream()} or {@code parallelStream()}.
 * A functional argument of any of these calls (a filter's predicate, a
 * {@code computeIfAbsent}'s function) is the analyzer's to enter.</p>
 */
public final class JavaContainerTypes {
    public enum Shape {
        NONE, INDEXED, ASSOCIATIVE
    }

    /** One interface's contract: its shape and the calls it states. */
    private enum Contract {
        MAP(Shape.ASSOCIATIVE), SET(Shape.ASSOCIATIVE), LIST(Shape.INDEXED),
        QUEUE(Shape.INDEXED), DEQUE(Shape.INDEXED), ITERATOR(Shape.NONE),
        ENTRY(Shape.NONE), COLLECTION(Shape.NONE), ITERABLE(Shape.NONE),
        STREAM(Shape.NONE, true);

        private final Shape shape;
        /** Every call is a query: a stream pipeline's. */
        private final boolean everyCallQueries;
        private final Set<String> queries = new LinkedHashSet<>();
        private final Set<String> mutations = new LinkedHashSet<>();

        Contract(Shape shape) {
            this(shape, false);
        }

        Contract(Shape shape, boolean everyCallQueries) {
            this.shape = shape;
            this.everyCallQueries = everyCallQueries;
        }

        private void state(Collection<String> read, Collection<String> write) {
            queries.addAll(read);
            mutations.addAll(write);
        }
    }

    private static final String OBJECT = "java.lang.Object";

    static {
        Contract.ITERABLE.state(calls("iterator()",
                "forEach(java.util.function.Consumer)", "spliterator()"),
                Collections.<String>emptySet());
        Contract.COLLECTION.state(Contract.ITERABLE.queries,
                Contract.ITERABLE.mutations);
        Contract.COLLECTION.state(calls(
                "contains(K)", "containsAll(java.util.Collection)",
                "isEmpty()", "size()", "toArray()", "toArray(K[])",
                "stream()", "parallelStream()"), calls(
                "add(K)", "remove(K)", "addAll(java.util.Collection)",
                "removeAll(java.util.Collection)",
                "retainAll(java.util.Collection)", "clear()",
                "removeIf(java.util.function.Predicate)"));
        for (Contract collection : EnumSet.of(Contract.SET, Contract.LIST,
                Contract.QUEUE, Contract.DEQUE)) {
            collection.state(Contract.COLLECTION.queries,
                    Contract.COLLECTION.mutations);
        }
        Contract.MAP.state(calls("forEach(java.util.function.BiConsumer)"),
                Collections.<String>emptySet());
        Contract.MAP.state(calls(
                "get(K)", "getOrDefault(K,K)", "containsKey(K)", "size()",
                "isEmpty()", "mappingCount()", "put(K,K)", "remove(K)",
                "remove(K,K)", "replace(K,K)", "replace(K,K,K)",
                "putIfAbsent(K,K)",
                "computeIfAbsent(K,java.util.function.Function)",
                "computeIfPresent(K,java.util.function.BiFunction)",
                "compute(K,java.util.function.BiFunction)",
                "merge(K,K,java.util.function.BiFunction)", "keySet()",
                "keySet(K)", "values()", "entrySet()", "firstKey()",
                "lastKey()", "floorKey(K)", "ceilingKey(K)", "lowerKey(K)",
                "higherKey(K)", "firstEntry()", "lastEntry()",
                "floorEntry(K)", "ceilingEntry(K)", "lowerEntry(K)",
                "higherEntry(K)", "pollFirstEntry()", "pollLastEntry()",
                "headMap(K)", "headMap(K,boolean)", "tailMap(K)",
                "tailMap(K,boolean)", "subMap(K,K)",
                "subMap(K,boolean,K,boolean)", "descendingMap()",
                "navigableKeySet()", "descendingKeySet()"), calls(
                "put(K,K)", "remove(K)", "remove(K,K)", "clear()",
                "putAll(java.util.Map)", "putIfAbsent(K,K)", "replace(K,K)",
                "replace(K,K,K)",
                "computeIfAbsent(K,java.util.function.Function)",
                "computeIfPresent(K,java.util.function.BiFunction)",
                "compute(K,java.util.function.BiFunction)",
                "merge(K,K,java.util.function.BiFunction)",
                "replaceAll(java.util.function.BiFunction)",
                "pollFirstEntry()", "pollLastEntry()"));
        Contract.SET.state(calls(
                "add(K)", "contains(K)", "isEmpty()", "remove(K)", "size()",
                "iterator()", "removeIf(java.util.function.Predicate)",
                "first()", "last()", "floor(K)", "ceiling(K)", "lower(K)",
                "higher(K)", "pollFirst()", "pollLast()", "headSet(K)",
                "headSet(K,boolean)", "tailSet(K)", "tailSet(K,boolean)",
                "subSet(K,K)", "subSet(K,boolean,K,boolean)",
                "descendingSet()", "descendingIterator()"), calls(
                "add(K)", "remove(K)", "clear()", "addAll(java.util.Collection)",
                "removeIf(java.util.function.Predicate)", "pollFirst()",
                "pollLast()"));
        Contract.LIST.state(calls(
                "add(K)", "contains(K)", "isEmpty()", "size()", "get(int)",
                "remove(int)", "set(int,K)", "iterator()", "listIterator()"),
                calls("add(K)", "add(int,K)", "remove(int)", "set(int,K)",
                        "clear()", "addAll(java.util.Collection)"));
        Contract.QUEUE.state(calls(
                "add(K)", "offer(K)", "contains(K)", "isEmpty()", "size()",
                "element()", "peek()", "poll()", "remove()", "take()",
                "iterator()"), calls(
                "add(K)", "offer(K)", "put(K)", "poll()", "remove()",
                "take()", "clear()", "addAll(java.util.Collection)"));
        Contract.DEQUE.state(Contract.QUEUE.queries,
                Contract.QUEUE.mutations);
        Contract.DEQUE.state(calls(
                "offerFirst(K)", "offerLast(K)", "pop()", "pollFirst()",
                "pollLast()", "peekFirst()", "peekLast()", "removeFirst()",
                "removeLast()", "getFirst()", "getLast()",
                "descendingIterator()"), calls(
                "addFirst(K)", "addLast(K)", "offerFirst(K)", "offerLast(K)",
                "push(K)", "pop()", "pollFirst()", "pollLast()",
                "removeFirst()", "removeLast()"));
        Contract.ITERATOR.state(calls("hasNext()", "next()", "nextIndex()"),
                Collections.<String>emptySet());
        Contract.ENTRY.state(calls("getKey()", "getValue()"),
                Collections.<String>emptySet());
    }

    /** The interfaces, each with its contract. */
    private static final Map<String, Contract> INTERFACES =
            new LinkedHashMap<>();
    /** The JDK classes, each with the contracts it honors: the answer when
     *  no hierarchy is at hand (COMPOSE reads recorded types). */
    private static final Map<String, Set<Contract>> CLASSES =
            new LinkedHashMap<>();

    static {
        interfaces(Contract.MAP, "java.util.Map", "java.util.SortedMap",
                "java.util.NavigableMap", "java.util.concurrent.ConcurrentMap",
                "java.util.concurrent.ConcurrentNavigableMap");
        interfaces(Contract.SET, "java.util.Set", "java.util.SortedSet",
                "java.util.NavigableSet");
        interfaces(Contract.LIST, "java.util.List");
        interfaces(Contract.QUEUE, "java.util.Queue",
                "java.util.concurrent.BlockingQueue",
                "java.util.concurrent.TransferQueue");
        interfaces(Contract.DEQUE, "java.util.Deque",
                "java.util.concurrent.BlockingDeque");
        interfaces(Contract.ITERATOR, "java.util.Iterator",
                "java.util.ListIterator");
        interfaces(Contract.ENTRY, "java.util.Map$Entry",
                "java.util.Map.Entry");
        interfaces(Contract.COLLECTION, "java.util.Collection");
        interfaces(Contract.ITERABLE, "java.lang.Iterable");
        interfaces(Contract.STREAM, "java.util.stream.BaseStream",
                "java.util.stream.Stream", "java.util.stream.IntStream",
                "java.util.stream.LongStream",
                "java.util.stream.DoubleStream");
        classes(EnumSet.of(Contract.STREAM), "java.util.stream.Collectors");
        classes(EnumSet.of(Contract.MAP), "java.util.AbstractMap",
                "java.util.HashMap", "java.util.LinkedHashMap",
                "java.util.TreeMap", "java.util.Hashtable",
                "java.util.IdentityHashMap", "java.util.WeakHashMap",
                "java.util.EnumMap", "java.util.concurrent.ConcurrentHashMap",
                "java.util.concurrent.ConcurrentSkipListMap");
        classes(EnumSet.of(Contract.SET), "java.util.AbstractSet",
                "java.util.HashSet", "java.util.LinkedHashSet",
                "java.util.TreeSet", "java.util.EnumSet",
                "java.util.concurrent.ConcurrentSkipListSet",
                "java.util.concurrent.CopyOnWriteArraySet",
                "java.util.concurrent.ConcurrentHashMap$KeySetView");
        classes(EnumSet.of(Contract.LIST), "java.util.AbstractList",
                "java.util.AbstractSequentialList", "java.util.ArrayList",
                "java.util.Vector", "java.util.Stack",
                "java.util.concurrent.CopyOnWriteArrayList");
        classes(EnumSet.of(Contract.LIST, Contract.DEQUE),
                "java.util.LinkedList");
        classes(EnumSet.of(Contract.QUEUE), "java.util.AbstractQueue",
                "java.util.PriorityQueue",
                "java.util.concurrent.ConcurrentLinkedQueue",
                "java.util.concurrent.LinkedBlockingQueue",
                "java.util.concurrent.ArrayBlockingQueue",
                "java.util.concurrent.PriorityBlockingQueue",
                "java.util.concurrent.DelayQueue",
                "java.util.concurrent.LinkedTransferQueue",
                "java.util.concurrent.SynchronousQueue");
        classes(EnumSet.of(Contract.DEQUE), "java.util.ArrayDeque",
                "java.util.concurrent.ConcurrentLinkedDeque",
                "java.util.concurrent.LinkedBlockingDeque");
    }

    private JavaContainerTypes() {
    }

    /** The shape of a type by the fixed list alone. */
    public static Shape shape(String type) {
        return shape(type, null);
    }

    /**
     * The shape of a type: an array is indexed; a map or a set is
     * associative; a list, queue or deque is indexed.
     *
     * @param hierarchy a class's supertypes, itself included, or empty
     *                  when it is not loaded; null: the fixed list alone
     */
    public static Shape shape(String type,
                              Function<String, ? extends Collection<String>>
                                      hierarchy) {
        String value = JavaPrimitiveSmtSemantics.typeName(type);
        if (value.startsWith("[") || value.endsWith("[]")) {
            return Shape.INDEXED;
        }
        Shape found = Shape.NONE;
        for (Contract contract : contracts(value, hierarchy)) {
            if (contract.shape == Shape.ASSOCIATIVE) return Shape.ASSOCIATIVE;
            if (contract.shape == Shape.INDEXED) found = Shape.INDEXED;
        }
        return found;
    }

    /** Whether a call's result is read off its receiver container's state:
     *  its value depends on the receiver as much as on its arguments. */
    public static boolean query(String signature,
                                Function<String, ? extends Collection<String>>
                                        hierarchy) {
        Call call = Call.parse(signature);
        if (call == null) return false;
        for (Contract contract : contracts(call.owner, hierarchy)) {
            if (contract.everyCallQueries
                    || contract.queries.contains(call.name)) {
                return true;
            }
        }
        return false;
    }

    /** Whether a call changes its receiver container's state, with its
     *  arguments. */
    public static boolean mutation(String signature,
                                   Function<String, ? extends
                                           Collection<String>> hierarchy) {
        Call call = Call.parse(signature);
        if (call == null) return false;
        for (Contract contract : contracts(call.owner, hierarchy)) {
            if (contract.mutations.contains(call.name)) return true;
        }
        return false;
    }

    /** The contracts a class honors: its own and its supertypes'. */
    private static Set<Contract> contracts(
            String owner,
            Function<String, ? extends Collection<String>> hierarchy) {
        Set<String> names = new LinkedHashSet<>();
        names.add(owner);
        if (hierarchy != null) {
            Collection<String> stated = hierarchy.apply(owner);
            if (stated != null) names.addAll(stated);
        }
        Set<Contract> found = EnumSet.noneOf(Contract.class);
        for (String name : names) {
            Contract contract = INTERFACES.get(name);
            if (contract != null) found.add(contract);
            Set<Contract> known = CLASSES.get(name);
            if (known != null) found.addAll(known);
        }
        return found;
    }

    private static void interfaces(Contract contract, String... names) {
        for (String name : names) INTERFACES.put(name, contract);
    }

    private static void classes(Set<Contract> contracts, String... names) {
        for (String name : names) CLASSES.put(name, contracts);
    }

    /** Calls spelled with {@code K} for {@code java.lang.Object}. */
    private static Set<String> calls(String... calls) {
        Set<String> spelled = new LinkedHashSet<>();
        for (String call : Arrays.asList(calls)) {
            spelled.add(call.replaceAll("\\bK\\b", OBJECT));
        }
        return spelled;
    }

    /** One call: its owner, and its name with its parameter types. */
    private static final class Call {
        private final String owner;
        private final String name;

        private Call(String owner, String name) {
            this.owner = owner;
            this.name = name;
        }

        /** A Soot method signature {@code <owner: ret name(params)>}, or
         *  null. */
        private static Call parse(String signature) {
            String value = signature == null ? "" : signature.trim();
            int ownerEnd = value.indexOf(':');
            if (!value.startsWith("<") || !value.endsWith(">")
                    || ownerEnd <= 1) {
                return null;
            }
            String subsignature = value.substring(ownerEnd + 1,
                    value.length() - 1).trim();
            int separator = subsignature.indexOf(' ');
            if (separator <= 0 || separator + 1 >= subsignature.length()) {
                return null;
            }
            return new Call(JavaPrimitiveSmtSemantics.typeName(
                    value.substring(1, ownerEnd)),
                    subsignature.substring(separator + 1).trim());
        }
    }
}
