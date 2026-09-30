package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.smt.JavaContainerTypes;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.function.Function;

import static org.junit.Assert.assertEquals;

/** R3-REFCONT WP1: containers by interface, JDK atomics by table. */
public class ReferenceCellTest {
    private static final String CHM = "java.util.concurrent.ConcurrentHashMap";
    private static final String BOOL = "java.util.concurrent.atomic.AtomicBoolean";
    private static final String VALUE = "<" + BOOL + ": int value>";

    /** The contracts are the interfaces': a class's own, its supertypes',
     *  or the fixed list's when no hierarchy is at hand. */
    @Test
    public void aContainerCallIsItsInterfacesContract() {
        Function<String, Collection<String>> none =
                name -> Collections.<String>emptySet();
        Function<String, Collection<String>> mine = name -> Arrays.asList(
                "a.MyMap", "java.util.AbstractMap", "java.util.Map");
        Object[][] rows = {
                {"CHM's keySet, whatever view it returns", true,
                        JavaContainerTypes.query("<" + CHM + ": " + CHM
                                + "$KeySetView keySet()>", null)},
                {"CHM's getOrDefault", true, JavaContainerTypes.query("<"
                        + CHM + ": java.lang.Object getOrDefault("
                        + "java.lang.Object,java.lang.Object)>", none)},
                {"a TreeMap's floorKey", true, JavaContainerTypes.query(
                        "<java.util.TreeMap: java.lang.Object floorKey("
                                + "java.lang.Object)>", null)},
                {"a view's removeIf writes its map", true,
                        JavaContainerTypes.mutation("<java.util.Set: boolean"
                                + " removeIf(java.util.function.Predicate)>",
                                null)},
                {"CHM's merge writes", true, JavaContainerTypes.mutation("<"
                        + CHM + ": java.lang.Object merge(java.lang.Object,"
                        + "java.lang.Object,java.util.function.BiFunction)>",
                        null)},
                {"an ArrayDeque's push writes", true,
                        JavaContainerTypes.mutation("<java.util.ArrayDeque:"
                                + " void push(java.lang.Object)>", null)},
                {"a list states no poll", false, JavaContainerTypes.query(
                        "<java.util.List: java.lang.Object poll()>", null)},
                {"an application class states nothing by name", false,
                        JavaContainerTypes.mutation("<a.App: void put("
                                + "java.lang.Object,java.lang.Object)>",
                                none)},
                {"a class reaching Map is a map", true,
                        JavaContainerTypes.query("<a.MyMap: java.lang.Object"
                                + " get(java.lang.Object)>", mine)},
                {"CHM is associative", JavaContainerTypes.Shape.ASSOCIATIVE,
                        JavaContainerTypes.shape("L" + CHM.replace('.', '/')
                                + ";")},
                {"LinkedList is indexed", JavaContainerTypes.Shape.INDEXED,
                        JavaContainerTypes.shape("java.util.LinkedList")},
                {"an array is indexed", JavaContainerTypes.Shape.INDEXED,
                        JavaContainerTypes.shape("[J")},
                {"any other class is none", JavaContainerTypes.Shape.NONE,
                        JavaContainerTypes.shape("a.Foo")},
                {"an atomic's CAS writes its value", true,
                        SharedFieldFlow.atomicWrite("<java.util.concurrent"
                                + ".atomic.AtomicReference: boolean"
                                + " compareAndSet(java.lang.Object,"
                                + "java.lang.Object)>")},
                {"AtomicBoolean.get() reads its int value", VALUE,
                        SharedFieldFlow.atomicRead("<" + BOOL
                                + ": boolean get()>")},
                {"an AtomicLong's set stores its value",
                        "<java.util.concurrent.atomic.AtomicLong: long value>",
                        SharedFieldFlow.atomicValueField("<a.X: java.util"
                                + ".concurrent.atomic.AtomicLong n>",
                                "<java.util.concurrent.atomic.AtomicLong:"
                                        + " void set(long)>")},
                {"of the atomic the carrier holds only", "",
                        SharedFieldFlow.atomicValueField("<a.X: java.util"
                                + ".concurrent.atomic.AtomicInteger n>",
                                "<java.util.concurrent.atomic.AtomicLong:"
                                        + " void set(long)>")}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }
}
