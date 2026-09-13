package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.After;
import org.junit.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * Transcripts for the bodies that used to exist twice in
 * {@link ConcolicRegionRuntime}.
 *
 * <p>Each group below was two or three implementations of one question that
 * differed only in a parameter - a field name, an exception message, an
 * unresolved label, a container shape.  Folding them is only safe if the one
 * surviving body still answers exactly what each caller used to answer for
 * itself, so every test here drives the survivor from both of the old call
 * sites and pins the answers, including the strings that reach artifacts.</p>
 */
public class RuntimeDedupeFoldTest {
    private static final String METHOD = "<a.B: void run(int)>";

    private final Deque<Long> opened = new ArrayDeque<>();

    @After
    public void releaseRegions() throws Exception {
        while (!opened.isEmpty()) {
            ConcolicRegionRuntime.ACTIVE.remove(opened.pop());
        }
        currentTokens().clear();
    }

    // ---------- group: one null-safe hook identity ----------

    /**
     * {@code sameSelector} and {@code sameRootMethod} were byte-identical,
     * and {@code popRootInvocationFrame} carried a third copy inline for the
     * root method.  One comparison answers for both halves of the identity,
     * and ownership is still refused when either half differs.
     */
    @Test
    public void oneHookIdentityComparisonAnswersForBothHalves()
            throws Exception {
        assertTrue(ConcolicRegionRuntime.sameHookIdentity(null, null));
        assertFalse(ConcolicRegionRuntime.sameHookIdentity(null, "sel"));
        assertFalse(ConcolicRegionRuntime.sameHookIdentity("sel", null));
        assertTrue(ConcolicRegionRuntime.sameHookIdentity("sel", "sel"));
        assertFalse(ConcolicRegionRuntime.sameHookIdentity("sel", "other"));

        // A frame is popped only when the selector AND the root method match;
        // either half alone must never expose an outer selected frame.
        pushRootFrame("sel", METHOD);
        assertNull("a foreign selector owns nothing",
                popRootFrame("other", METHOD));
        assertNull("a foreign root method owns nothing",
                popRootFrame("sel", "<a.B: void other()>"));
        assertNull("a null root method owns nothing",
                popRootFrame("sel", null));
        assertTrue(popRootFrame("sel", METHOD) != null);
        assertNull("the stack is empty again", popRootFrame("sel", METHOD));
    }

    // ---------- group: one sibling-hook accounting ----------

    /**
     * Both root stacks absorbed the extra hooks instrumentation emits at one
     * physical Java entry with the same nine-line body, differing only in
     * the name of the group-key field.  Both now inherit it, and both still
     * absorb exactly {@code hookCount - 1} siblings of their own group and
     * nothing of any other.
     */
    @Test
    public void bothRootStacksAbsorbSiblingHooksIdentically()
            throws Exception {
        for (Object entry : Arrays.asList(rootFrame("sel", METHOD, "G", 2),
                loopRootContext("G", 2))) {
            Method claims = entry.getClass().getSuperclass()
                    .getDeclaredMethod("claimsSiblingHook", String.class);
            claims.setAccessible(true);
            assertFalse(entry.getClass().getSimpleName()
                            + " must not absorb another group's hook",
                    (Boolean) claims.invoke(entry, "OTHER"));
            assertTrue((Boolean) claims.invoke(entry, "G"));
            assertTrue((Boolean) claims.invoke(entry, "G"));
            assertFalse("the group's own hooks are exhausted",
                    (Boolean) claims.invoke(entry, "G"));
        }

        // A one-hook group has no sibling to absorb at all.
        Object single = loopRootContext("G", 0);
        Method claim = single.getClass().getSuperclass()
                .getDeclaredMethod("claimsSiblingHook", String.class);
        claim.setAccessible(true);
        assertFalse((Boolean) claim.invoke(single, "G"));
    }

    // ---------- group: one activation-stack ownership proof ----------

    /**
     * Three readers of the activation stack each re-proved that the region
     * they were handed is the innermost one, differing only in the message
     * of the {@code IllegalStateException} they raise.  One proof serves all
     * three, and each keeps its own message.
     */
    @Test
    public void everyActivationStackReaderProvesTheSameOwnership()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion outer = region();
        ConcolicRegionRuntime.ActiveRegion inner = region();

        assertTrue("the inner region has a caller",
                (Boolean) stackCall("hasEnclosingActiveRegion", inner));
        assertSame(outer, stackCall("enclosingActiveRegion", inner));

        // The outer region is not innermost, so all three refuse it, each
        // with the message its own caller has always raised.
        assertRefuses("hasEnclosingActiveRegion", outer,
                "selected regions must close in strict LIFO order");
        assertRefuses("enclosingActiveRegion", outer,
                "selected regions must inspect callers in strict LIFO order");
        assertRefuses("popActiveRegion", outer,
                "selected region stack does not own token " + outer.token);

        stackCall("popActiveRegion", inner);
        assertFalse("the outer region is alone now",
                (Boolean) stackCall("hasEnclosingActiveRegion", outer));
        assertNull(stackCall("enclosingActiveRegion", outer));
    }

    // ---------- group: one container-element coercion ----------

    /**
     * The "null the element out, refuse an absent one, otherwise coerce
     * against the live element's own type" triple was written three times.
     * One body now answers for the indexed list, the associative map and the
     * ordered iteration target.
     */
    @Test
    public void oneContainerElementCoercionServesEveryShape() {
        List<Object> list = new ArrayList<>(Arrays.asList(
                (Object) Integer.valueOf(7), Integer.valueOf(8)));
        assertTrue(ConcolicRegionRuntime.writeIndexedContainerElement(
                list, 1, "INT", "42"));
        assertEquals(Integer.valueOf(42), list.get(1));
        assertTrue(ConcolicRegionRuntime.writeIndexedContainerElement(
                list, 0, "NULL", ""));
        assertNull("a NULL model nulls the element out", list.get(0));
        assertFalse("an already-null element has no type to coerce against",
                ConcolicRegionRuntime.writeIndexedContainerElement(
                        list, 0, "INT", "42"));
        assertFalse("an out-of-range index writes nothing",
                ConcolicRegionRuntime.writeIndexedContainerElement(
                        list, 9, "INT", "42"));

        Map<Object, Object> map = new LinkedHashMap<>();
        map.put("k", Integer.valueOf(1));
        assertTrue(ConcolicRegionRuntime.writeAssociativeContainerTarget(
                map, "k", associativeModel("INT", "5")));
        assertEquals(Integer.valueOf(5), map.get("k"));
        assertTrue(ConcolicRegionRuntime.writeAssociativeContainerTarget(
                map, "k", associativeModel("NULL", "")));
        assertNull(map.get("k"));
        assertFalse("a present-null value has no type to coerce against",
                ConcolicRegionRuntime.writeAssociativeContainerTarget(
                        map, "k", associativeModel("INT", "5")));
        assertFalse("an absent key is not turned into a present-null entry",
                ConcolicRegionRuntime.writeAssociativeContainerTarget(
                        map, "absent", associativeModel("INT", "5")));
        assertTrue("a NULL model of an absent key is already true",
                ConcolicRegionRuntime.writeAssociativeContainerTarget(
                        map, "absent", associativeModel("NULL", "")));
        assertFalse("an absent key stays absent",
                map.containsKey("absent"));
    }

    /**
     * Both ordered-iteration arms refused a rewrite that would merge two live
     * entries into one, with the same inequality-and-membership test spelled
     * out twice.  One test now serves both, and each container keeps its own
     * membership question.
     */
    @Test
    public void oneCollisionTestGuardsBothIterationArms() {
        LinkedHashSet<Object> keys = new LinkedHashSet<>(
                Arrays.asList((Object) "a", "b"));
        assertFalse("rewriting 'a' to the live 'b' would lose an element",
                ConcolicRegionRuntime.writeContainerTarget(keys,
                        iteration("KEY", 0, "STRING", "\"b\"")));
        assertEquals(2, keys.size());
        assertTrue(ConcolicRegionRuntime.writeContainerTarget(keys,
                iteration("KEY", 0, "STRING", "\"c\"")));
        assertEquals(Arrays.asList("c", "b"), new ArrayList<>(keys));

        LinkedHashMap<Object, Object> entries = new LinkedHashMap<>();
        entries.put("a", Integer.valueOf(1));
        entries.put("b", Integer.valueOf(2));
        assertFalse("rewriting key 'a' to the live key 'b' would lose an entry",
                ConcolicRegionRuntime.writeContainerTarget(entries,
                        iteration("KEY", 0, "STRING", "\"b\"")));
        assertEquals(2, entries.size());
        assertTrue(ConcolicRegionRuntime.writeContainerTarget(entries,
                iteration("KEY", 0, "STRING", "\"c\"")));
        assertEquals(Arrays.asList("c", "b"),
                new ArrayList<>(entries.keySet()));
        assertEquals(Integer.valueOf(1), entries.get("c"));

        // Replacing a value is never a structural change, so no collision
        // test applies to the VALUE projection at all.
        LinkedHashMap<Object, Object> values = new LinkedHashMap<>();
        values.put("a", Integer.valueOf(1));
        values.put("b", Integer.valueOf(2));
        assertTrue(ConcolicRegionRuntime.writeContainerTarget(values,
                iteration("VALUE", 0, "INT", "2")));
        assertEquals(Integer.valueOf(2), values.get("a"));
        assertEquals(2, values.size());
    }

    // ---------- group: one reference-model spine ----------

    /**
     * {@code materializeArgument} (twice) and {@code materializeMethodArgument}
     * each looked the assignment up, applied it, filed an unresolved on a
     * model that cannot be replayed as a reference, and recorded it
     * otherwise.  Only the unresolved label differed, so it is the parameter;
     * all three labels are pinned here because they reach the artifacts.
     */
    @Test
    public void oneReferenceModelSpineServesEveryMaterialization()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(
                model("sym.a", "STRING", "\"z\""),
                model("sym.b", "INT", "7"));
        ConcolicRegionRuntime.SymbolizeAction unmodeled = action("sym.none");
        ConcolicRegionRuntime.SymbolizeAction modeled = action("sym.a");
        ConcolicRegionRuntime.SymbolizeAction refused = action("sym.b");

        assertSame("a solve that named no assignment models nothing",
                missingValue(), modeledReference(active, unmodeled, "live",
                        "root reference"));
        assertTrue(active.unresolved.isEmpty());

        assertEquals("z", modeledReference(active, modeled, "live",
                "root reference"));
        assertEquals("an applied assignment is spent", 1,
                applied(active).size());
        assertSame("the same assignment does not apply twice",
                missingValue(), modeledReference(active, modeled, "live",
                        "root reference"));

        assertSame(unsupportedReplayValue(), modeledReference(active, refused,
                "live", "root reference"));
        assertEquals(java.util.Collections.singletonList(
                        "sym.b: unsupported root reference model INT=7"),
                new ArrayList<>(active.unresolved));

        // The other two call sites differ only in this label.
        ConcolicRegionRuntime.ActiveRegion method = region(
                model("sym.b", "INT", "7"));
        modeledReference(method, refused, "live", "method argument");
        assertEquals(java.util.Collections.singletonList(
                        "sym.b: unsupported method argument model INT=7"),
                new ArrayList<>(method.unresolved));

        ConcolicRegionRuntime.ActiveRegion local = region(
                model("sym.b", "INT", "7"));
        modeledReference(local, refused, "live", "local reference");
        assertEquals(java.util.Collections.singletonList(
                        "sym.b: unsupported local reference model INT=7"),
                new ArrayList<>(local.unresolved));

        // UNCHANGED is a reference model that keeps the live identity, which
        // is a replayable answer and not a refusal.
        ConcolicRegionRuntime.ActiveRegion kept = region(
                model("sym.a", "UNCHANGED", ""));
        Object live = new Object();
        assertSame(live, modeledReference(kept, modeled, live,
                "root reference"));
        assertTrue(kept.unresolved.isEmpty());
    }

    // ---------- group: one unique-assignment selector ----------

    /**
     * The input lookup and the configured-source lookup each walked the
     * activation's assignments, skipped the spent ones, and refused two
     * survivors as ambiguous.  One selector now does that, parameterised by
     * the match, by whether the assignment is reusable, and by the subject
     * each names in its own ambiguity note.
     */
    @Test
    public void oneSelectorServesBothAssignmentLookups() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(
                model("sym.a", "STRING", "\"one\""),
                model("sym.a", "STRING", "\"two\""));
        assertNull("two survivors address nothing",
                assignment(active, action("sym.a")));
        assertEquals(java.util.Collections.singletonList(
                        "sym.a: ambiguous model assignments"),
                new ArrayList<>(active.unresolved));

        // A configured-source model is declared by the source catalogue
        // rather than by an input action, so these two are handed straight to
        // the activation the same way the plan decoder would.
        ConcolicRegionRuntime.ActiveRegion sources = region();
        declareConfiguredSources(sources, 2);
        assertNull(configuredSourceAssignment(sources, "P", "S",
                "<a.B: int f>"));
        assertEquals(java.util.Collections.singletonList(
                        "P: ambiguous configured source models"),
                new ArrayList<>(sources.unresolved));

        // One survivor still resolves, and is spent by the first application.
        ConcolicRegionRuntime.ActiveRegion single = region(
                model("sym.a", "STRING", "\"one\""));
        ConcolicRegionRuntime.ModelAssignment only =
                assignment(single, action("sym.a"));
        assertTrue(only != null);
        applied(single).add(only.key);
        assertNull("a spent assignment is not selected again",
                assignment(single, action("sym.a")));
        assertTrue(single.unresolved.isEmpty());
    }

    // ---------- group: one muted-observation guard ----------

    /**
     * The four loop-accounting hooks each opened with the same guard.  A hook
     * reached from GraphChecker's own muted bookkeeping still accounts for
     * nothing - no traversal charged, no cut, no unresolved - even though a
     * region is active.
     */
    @Test
    public void theMutedObservationGuardStopsEveryAccountingHook()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region();
        ConcolicRegionRuntime.pauseObservation();
        try {
            ConcolicRegionRuntime.checkLoopBackedge("edge", 4);
            ConcolicRegionRuntime.checkReplayLoopBody("loop", 4);
            ConcolicRegionRuntime.recordLoopCardinality("loop", 3);
            ConcolicRegionRuntime.completeLoopCardinality("loop");
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
        assertTrue("a muted hook charges nothing",
                active.unresolved.isEmpty());
        assertNull(active.replayResourceCut);
        assertFalse("the region is still live", active.abandoned);
    }

    // ---------- harness ----------

    @SuppressWarnings("unchecked")
    private static Deque<Long> currentTokens() throws Exception {
        Field field = ConcolicRegionRuntime.class
                .getDeclaredField("CURRENT_TOKENS");
        field.setAccessible(true);
        return ((ThreadLocal<Deque<Long>>) field.get(null)).get();
    }

    private ConcolicRegionRuntime.ActiveRegion region(
            JsonObject... assignments) throws Exception {
        ConcolicTaskPlan.RuntimeTask runtime =
                new ConcolicTaskPlan.RuntimeTask(task(assignments));
        long token = 910000L + opened.size() + 1;
        ConcolicRegionRuntime.ActiveRegion active =
                new ConcolicRegionRuntime.ActiveRegion(token, runtime, null,
                        Thread.currentThread(), false);
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        currentTokens().push(token);
        opened.push(token);
        return active;
    }

    private static ExecutionTask task(JsonObject... assignments) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        encoded.addProperty("regionId", "REGION.1");
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", "dn0#epoch0");
        encoded.addProperty("occurrenceId", "REGION.1@dn0#epoch0#1");
        encoded.addProperty("rootMethod", METHOD);
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "dn0#epoch0");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        encoded.add("loopBound", loopBound);
        encoded.add("inputActions", new JsonArray());
        JsonArray models = new JsonArray();
        for (JsonObject assignment : assignments) models.add(assignment);
        encoded.add("modelAssignments", models);
        return ExecutionTask.decode(encoded);
    }

    private static int keys;

    private static JsonObject model(String symbol, String valueType,
                                    String value) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("modelAssignmentKey", symbol + "#" + ++keys);
        assignment.addProperty("engineSymbol", symbol);
        assignment.addProperty("inputSymbol", symbol);
        assignment.addProperty("valueType", valueType);
        assignment.addProperty("value", value);
        return assignment;
    }

    @SuppressWarnings("unchecked")
    private static void declareConfiguredSources(
            ConcolicRegionRuntime.ActiveRegion active, int count)
            throws Exception {
        Field activation = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredField("activation");
        activation.setAccessible(true);
        Field models = ConcolicTaskPlan.RuntimeTask.class
                .getDeclaredField("modelAssignments");
        models.setAccessible(true);
        List<Object> declared = (List<Object>)
                models.get(activation.get(active));
        for (int index = 0; index < count; index++) {
            JsonObject assignment = model("SOURCE_PHASE:P", "INT", "1");
            assignment.addProperty("configuredSourcePhaseId", "P");
            assignment.addProperty("configuredSourceId", "S");
            assignment.addProperty("configuredSourceFieldSignature",
                    "<a.B: int f>");
            declared.add(new ConcolicRegionRuntime.ModelAssignment(
                    assignment));
        }
    }

    private static JsonObject associative(String valueType, String value) {
        JsonObject assignment = model("sym.c", valueType, value);
        JsonObject target = new JsonObject();
        target.addProperty("shape", "ASSOCIATIVE");
        assignment.add("containerTarget", target);
        return assignment;
    }

    private static ConcolicRegionRuntime.ModelAssignment associativeModel(
            String valueType, String value) {
        return new ConcolicRegionRuntime.ModelAssignment(
                associative(valueType, value));
    }

    private static ConcolicRegionRuntime.ModelAssignment iteration(
            String projection, int index, String valueType, String value) {
        JsonObject assignment = model("sym.c", valueType, value);
        JsonObject target = new JsonObject();
        target.addProperty("shape", "ASSOCIATIVE");
        target.addProperty("selectorKind", "ITERATION_INDEX");
        target.addProperty("projection", projection);
        target.addProperty("index", index);
        assignment.add("containerTarget", target);
        return new ConcolicRegionRuntime.ModelAssignment(assignment);
    }

    private static ConcolicRegionRuntime.SymbolizeAction action(
            String symbol) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("symbol", symbol);
        encoded.addProperty("mode", "SYMBOLIC");
        return new ConcolicRegionRuntime.SymbolizeAction(encoded);
    }

    // ---------- reflection ----------

    @SuppressWarnings("unchecked")
    private static java.util.Set<String> applied(
            ConcolicRegionRuntime.ActiveRegion active) throws Exception {
        Field field = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredField("appliedModelAssignments");
        field.setAccessible(true);
        return (java.util.Set<String>) field.get(active);
    }

    private static Object missingValue() {
        return ConcolicRegionRuntime.MissingValue.INSTANCE;
    }

    private static Object unsupportedReplayValue() throws Exception {
        Field instance = nested("UnsupportedReplayValue")
                .getDeclaredField("INSTANCE");
        instance.setAccessible(true);
        return instance.get(null);
    }

    private static Object modeledReference(
            ConcolicRegionRuntime.ActiveRegion active,
            ConcolicRegionRuntime.SymbolizeAction action, Object concrete,
            String label) throws Exception {
        Method method = ConcolicRegionRuntime.class.getDeclaredMethod(
                "modeledReference",
                ConcolicRegionRuntime.ActiveRegion.class,
                ConcolicRegionRuntime.SymbolizeAction.class, Object.class,
                String.class);
        method.setAccessible(true);
        return method.invoke(null, active, action, concrete, label);
    }

    private static ConcolicRegionRuntime.ModelAssignment assignment(
            ConcolicRegionRuntime.ActiveRegion active,
            ConcolicRegionRuntime.SymbolizeAction action) throws Exception {
        Method method = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredMethod("assignment",
                        ConcolicRegionRuntime.SymbolizeAction.class,
                        List.class);
        method.setAccessible(true);
        return (ConcolicRegionRuntime.ModelAssignment)
                method.invoke(active, action, null);
    }

    private static Object configuredSourceAssignment(
            ConcolicRegionRuntime.ActiveRegion active, String phase,
            String source, String fieldSignature) throws Exception {
        Method method = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredMethod("configuredSourceAssignment", String.class,
                        String.class, String.class);
        method.setAccessible(true);
        return method.invoke(active, phase, source, fieldSignature);
    }

    private Object stackCall(String name,
                             ConcolicRegionRuntime.ActiveRegion active)
            throws Exception {
        Method method = ConcolicRegionRuntime.class.getDeclaredMethod(name,
                ConcolicRegionRuntime.ActiveRegion.class);
        method.setAccessible(true);
        return method.invoke(null, active);
    }

    private void assertRefuses(String name,
                               ConcolicRegionRuntime.ActiveRegion active,
                               String message) throws Exception {
        try {
            stackCall(name, active);
            fail(name + " must refuse a region that is not innermost");
        } catch (java.lang.reflect.InvocationTargetException wrapped) {
            Throwable cause = wrapped.getCause();
            assertTrue(name + " raised " + cause,
                    cause instanceof IllegalStateException);
            assertEquals(message, cause.getMessage());
        }
    }

    private static Class<?> nested(String simpleName) throws Exception {
        return Class.forName("edu.uva.liftlab.graphchecker.runtime"
                + ".ConcolicRegionRuntime$" + simpleName);
    }

    private static Object rootFrame(String selector, String rootMethod,
                                    String groupKey, int siblings)
            throws Exception {
        Constructor<?> constructor = nested("RootInvocationFrame")
                .getDeclaredConstructor(String.class, String.class,
                        String.class, int.class, long.class);
        constructor.setAccessible(true);
        return constructor.newInstance(selector, rootMethod, groupKey,
                siblings, 0L);
    }

    private static Object loopRootContext(String groupKey, int siblings)
            throws Exception {
        Constructor<?> constructor = nested("LoopRootInvocationContext")
                .getDeclaredConstructor(long.class, String.class, int.class,
                        java.util.Set.class);
        constructor.setAccessible(true);
        return constructor.newInstance(1L, groupKey, siblings,
                new LinkedHashSet<String>());
    }

    @SuppressWarnings("unchecked")
    private static void pushRootFrame(String selector, String rootMethod)
            throws Exception {
        Field field = ConcolicRegionRuntime.class
                .getDeclaredField("ROOT_INVOCATION_FRAMES");
        field.setAccessible(true);
        ((ThreadLocal<Deque<Object>>) field.get(null)).get()
                .push(rootFrame(selector, rootMethod, "G", 0));
    }

    private static Object popRootFrame(String selector, String rootMethod)
            throws Exception {
        Method method = ConcolicRegionRuntime.class.getDeclaredMethod(
                "popRootInvocationFrame", String.class, String.class);
        method.setAccessible(true);
        return method.invoke(null, selector, rootMethod);
    }
}
