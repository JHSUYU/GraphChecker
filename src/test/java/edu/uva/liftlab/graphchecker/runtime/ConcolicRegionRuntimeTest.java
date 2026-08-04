package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import org.junit.Test;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertEquals;

public class ConcolicRegionRuntimeTest {
    private static final String RESULT_FIELD =
            "<test.State: int result>";
    private static final String OTHER_FIELD =
            "<test.State: int other>";

    @Test
    public void inactiveBackedgeHookDoesNotChangeWorkloadExecution() {
        ConcolicRegionRuntime.resetForTests();

        ConcolicRegionRuntime.checkLoopBackedge(
                "<test.Loop: void run()>#backedge:u4->u1", 1);
    }

    @Test
    public void backedgeBudgetAllowsKTraversalsAndCutsAttemptKPlusOne() {
        ConcolicRegionRuntime.LoopBackedgeBudget budget =
                new ConcolicRegionRuntime.LoopBackedgeBudget(
                        LoopBoundPolicy.cfgBackedges(2));
        String edge = "<test.Loop: void run()>#backedge:u4->u1";

        assertEquals(1L, budget.recordTraversal(edge));
        assertEquals(2L, budget.recordTraversal(edge));
        assertEquals(3L, budget.recordTraversal(edge));
        // A denied attempt is not reported as a completed traversal.
        assertEquals(2, budget.toJson().get(edge).getAsInt());

        ConcolicRegionRuntime.LoopBoundCut cut =
                new ConcolicRegionRuntime.LoopBoundCut(
                        edge, 2, 3L,
                        "MAX_BACKEDGE_TRAVERSALS_EXCEEDED");
        JsonObject encoded = cut.toJson();
        assertEquals("LOOP_BOUND", encoded.get("kind").getAsString());
        assertEquals(3L, encoded.get("attemptedTraversal").getAsLong());
        assertEquals("MAX_BACKEDGE_TRAVERSALS_EXCEEDED",
                encoded.get("reason").getAsString());
        assertEquals("CUT",
                ConcolicRegionRuntime.exceptionalExitKind(cut));
        assertEquals("THROW", ConcolicRegionRuntime.exceptionalExitKind(
                new IllegalStateException("workload failure")));
    }

    @Test
    public void sparseIndexedAssignmentsMutateOnlyRequestedElements() {
        int[] array = new int[]{3, 5, 7};
        List<Integer> list = new ArrayList<>(Arrays.asList(11, 13, 17));
        Object arrayIdentity = array;
        Object listIdentity = list;

        assertTrue(ConcolicRegionRuntime.writeIndexedContainerElement(
                array, 0, "INT", "19"));
        assertTrue(ConcolicRegionRuntime.writeIndexedContainerElement(
                array, 2, "INT", "23"));
        assertTrue(ConcolicRegionRuntime.writeIndexedContainerElement(
                list, 1, "INT", "29"));

        assertSame(arrayIdentity, array);
        assertSame(listIdentity, list);
        assertArrayEquals(new int[]{19, 5, 23}, array);
        assertEquals(Arrays.asList(11, 29, 17), list);
    }

    @Test
    public void invalidIndexedTargetsFailWithoutReplacingContainers() {
        int[] array = new int[]{3};
        List<Integer> immutable = Collections.singletonList(5);

        assertFalse(ConcolicRegionRuntime.writeIndexedContainerElement(
                array, 1, "INT", "7"));
        assertFalse(ConcolicRegionRuntime.writeIndexedContainerElement(
                immutable, 0, "INT", "7"));
        assertFalse(ConcolicRegionRuntime.writeIndexedContainerElement(
                new Object(), 0, "INT", "7"));

        assertArrayEquals(new int[]{3}, array);
        assertEquals(Collections.singletonList(5), immutable);
    }

    @Test
    public void replayWriteSuppressesOnlyTheSameExactFieldLiveIn() {
        Object writtenOwner = new Object();
        Object otherOwner = new Object();
        ConcolicRegionRuntime.ReplayFieldWrites writes =
                new ConcolicRegionRuntime.ReplayFieldWrites();

        writes.add(writtenOwner, RESULT_FIELD);

        assertTrue(writes.contains(writtenOwner, RESULT_FIELD));
        assertFalse(writes.contains(writtenOwner, OTHER_FIELD));
        assertFalse(writes.contains(otherOwner, RESULT_FIELD));
        assertFalse(writes.contains(writtenOwner, "result"));
    }

    @Test
    public void associativeReplayNeverCreatesAnAbsentKey() {
        Map<Integer, Object> values = new LinkedHashMap<>();
        values.put(3, null);

        assertTrue(ConcolicRegionRuntime.writeContainerTarget(values,
                associativeAssignment(7, "NULL", false), null));
        assertFalse(values.containsKey(7));
        assertTrue(values.containsKey(3));
        assertEquals(null, values.get(3));

        assertFalse(ConcolicRegionRuntime.writeContainerTarget(values,
                associativeAssignment(7,
                        "CONTAINER_REFERENCE_ALIAS", true), new Object()));
        assertFalse(values.containsKey(7));
    }

    @Test
    public void referenceReplayReplacesOnlyExistingContainerSlots() {
        Object oldIndexed = new Object();
        Object sourceIndexed = new Object();
        List<Object> indexed = new ArrayList<>(
                Collections.singletonList(oldIndexed));
        ConcolicRegionRuntime.ModelAssignment indexedAssignment =
                indexedReferenceAssignment(0);

        assertTrue(ConcolicRegionRuntime.writeContainerTarget(indexed,
                indexedAssignment, sourceIndexed));
        assertEquals(1, indexed.size());
        assertSame(sourceIndexed, indexed.get(0));
        assertFalse(ConcolicRegionRuntime.writeContainerTarget(indexed,
                indexedReferenceAssignment(1), new Object()));
        assertEquals(1, indexed.size());

        Object oldMapped = new Object();
        Object sourceMapped = new Object();
        Map<Integer, Object> mapped = new LinkedHashMap<>();
        mapped.put(3, oldMapped);

        assertTrue(ConcolicRegionRuntime.writeContainerTarget(mapped,
                associativeAssignment(3,
                        "CONTAINER_REFERENCE_ALIAS", true), sourceMapped));
        assertEquals(1, mapped.size());
        assertSame(sourceMapped, mapped.get(3));
    }

    @Test
    public void orderedAssociativeReplayWritesTheSelectedCursor() {
        Set<Integer> set = new LinkedHashSet<>(Arrays.asList(3, 5));
        assertFalse(ConcolicRegionRuntime.writeContainerTarget(set,
                iterationAssignment(0, "KEY", 5), null));
        assertEquals(Arrays.asList(3, 5), new ArrayList<>(set));
        assertTrue(ConcolicRegionRuntime.writeContainerTarget(set,
                iterationAssignment(0, "KEY", 13), null));
        assertEquals(Arrays.asList(13, 5), new ArrayList<>(set));

        Map<Integer, Integer> map = new LinkedHashMap<>();
        map.put(3, 7);
        map.put(5, 11);
        assertFalse(ConcolicRegionRuntime.writeContainerTarget(map,
                iterationAssignment(0, "KEY", 5), null));
        assertEquals(Arrays.asList(3, 5),
                new ArrayList<>(map.keySet()));
        assertTrue(ConcolicRegionRuntime.writeContainerTarget(map,
                iterationAssignment(0, "KEY", 17), null));
        assertEquals(Arrays.asList(17, 5),
                new ArrayList<>(map.keySet()));
        assertTrue(ConcolicRegionRuntime.writeContainerTarget(map,
                iterationAssignment(1, "VALUE", 19), null));
        assertEquals(Integer.valueOf(19), map.get(5));
    }

    @Test
    public void modelReplayWritesTheDeclaredHiddenFieldOnly() {
        HiddenDerived owner = new HiddenDerived();
        JsonObject encoded = new JsonObject();
        encoded.addProperty("modelAssignmentKey", "hidden-base");
        encoded.addProperty("inputSymbol", "REGION.0.in.0");
        encoded.addProperty("valueType", "INT");
        encoded.addProperty("value", "7");
        ConcolicRegionRuntime.ModelAssignment assignment =
                new ConcolicRegionRuntime.ModelAssignment(encoded);
        String baseField = "<" + HiddenBase.class.getName()
                + ": int value>";

        assertTrue(ConcolicRegionRuntime.writeModeledField(
                owner, baseField, assignment));
        assertEquals(7, ((HiddenBase) owner).value);
        assertEquals(2, owner.value);
    }

    private static class HiddenBase {
        int value = 1;
    }

    private static final class HiddenDerived extends HiddenBase {
        int value = 2;
    }

    private static final class InheritedOnlyDerived extends HiddenBase {
    }

    @Test
    public void modelReplayResolvesAnInheritedFieldReferenceOwner() {
        InheritedOnlyDerived owner = new InheritedOnlyDerived();
        JsonObject encoded = new JsonObject();
        encoded.addProperty("modelAssignmentKey", "inherited-base");
        encoded.addProperty("inputSymbol", "REGION.0.in.0");
        encoded.addProperty("valueType", "INT");
        encoded.addProperty("value", "11");
        ConcolicRegionRuntime.ModelAssignment assignment =
                new ConcolicRegionRuntime.ModelAssignment(encoded);
        String inheritedReference = "<" + InheritedOnlyDerived.class.getName()
                + ": int value>";

        assertTrue(ConcolicRegionRuntime.writeModeledField(
                owner, inheritedReference, assignment));
        assertEquals(11, owner.value);
    }

    @Test
    public void nestedReferenceSourceUsesTheExistingFieldPathResolver() {
        NestedRoot root = new NestedRoot();

        assertSame(root.holder,
                ConcolicRegionRuntime.resolveFieldPathLeafOwner(root,
                        Arrays.asList("holder", "values")));
        assertSame(root.holder.values,
                ConcolicRegionRuntime.resolveFieldPathLeafOwner(root,
                        Arrays.asList("holder", "values", "[0]")));
    }

    private static ConcolicRegionRuntime.ModelAssignment
    indexedReferenceAssignment(int index) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("modelAssignmentKey", "indexed-" + index);
        encoded.addProperty("inputSymbol", "REGION.0.in.0");
        encoded.addProperty("valueType", "CONTAINER_REFERENCE_ALIAS");
        encoded.addProperty("referenceSourceInputSymbol", "REGION.0.in.1");
        JsonObject target = new JsonObject();
        target.addProperty("shape", "INDEXED");
        target.addProperty("index", index);
        target.addProperty("sourceShape", "INDEXED");
        target.addProperty("sourceIndex", 0);
        encoded.add("containerTarget", target);
        return new ConcolicRegionRuntime.ModelAssignment(encoded);
    }

    private static ConcolicRegionRuntime.ModelAssignment
    associativeAssignment(int key, String valueType, boolean alias) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("modelAssignmentKey", "test-" + key + "-"
                + valueType);
        encoded.addProperty("inputSymbol", "REGION.0.in.0");
        encoded.addProperty("valueType", valueType);
        if (alias) {
            encoded.addProperty("referenceSourceInputSymbol",
                    "REGION.0.in.1");
        }
        JsonObject target = new JsonObject();
        target.addProperty("shape", "ASSOCIATIVE");
        target.addProperty("keyJavaType", "I");
        target.addProperty("keyValue", Integer.toString(key));
        if (alias) {
            target.addProperty("sourceShape", "ASSOCIATIVE");
            target.addProperty("sourceKeyJavaType", "I");
            target.addProperty("sourceKeyValue", "3");
        }
        encoded.add("containerTarget", target);
        return new ConcolicRegionRuntime.ModelAssignment(encoded);
    }

    private static ConcolicRegionRuntime.ModelAssignment
    iterationAssignment(int index, String projection, int value) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("modelAssignmentKey", "iteration-" + index);
        encoded.addProperty("inputSymbol", "REGION.0.in.0");
        encoded.addProperty("valueType", "INT");
        encoded.addProperty("value", Integer.toString(value));
        JsonObject target = new JsonObject();
        target.addProperty("shape", "ASSOCIATIVE");
        target.addProperty("selectorKind", "ITERATION_INDEX");
        target.addProperty("index", index);
        target.addProperty("projection", projection);
        encoded.add("containerTarget", target);
        return new ConcolicRegionRuntime.ModelAssignment(encoded);
    }

    private static final class NestedRoot {
        private final NestedHolder holder = new NestedHolder();
    }

    private static final class NestedHolder {
        private final List<Object> values = new ArrayList<>(
                Collections.singletonList(new Object()));
    }
}
