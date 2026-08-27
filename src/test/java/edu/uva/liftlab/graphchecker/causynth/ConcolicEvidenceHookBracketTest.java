package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections
        .ConcolicMaterializationSelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections
        .InstrumentationPlan;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.Body;
import soot.G;
import soot.IntType;
import soot.BooleanType;
import soot.Local;
import soot.Modifier;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.Jimple;
import soot.jimple.Stmt;

import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Every evidence hook the concolic pass emits runs inside a muted subtree.
 *
 * <p>A hook is this layer's own control flow over the workload's own objects:
 * it compares receivers against {@code null} and against declared classes,
 * walks its own stacks and compares its own strings.  Unmuted, each of those
 * decisions is appended to the path condition of whichever thread executed the
 * hook, so a segment window quotes conditions the program never evaluated and
 * a relation is stated over guards that belong to GraphChecker.  This has
 * happened three times; the boundary that prevents it is the
 * {@code pauseObservation}/{@code resumeObservation} bracket, and it belongs
 * around the hook at the site that emits it rather than inside each runtime
 * entry point one at a time.</p>
 *
 * <p>The two hooks pinned here are the ones that were emitted bare: the region
 * entry hook, whose admission decision re-runs on every plan row naming one
 * root, and the accessor call-context pair, which brackets a getter inside the
 * workload's own fragment.</p>
 */
public class ConcolicEvidenceHookBracketTest {

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String RUNTIME_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime";
    private static final String PAUSE = "pauseObservation";
    private static final String RESUME = "resumeObservation";

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void regionEntryAndAccessorContextHooksAreMuted()
            throws Exception {
        SootMethod root = regionRoot();
        InstrumentationPlan plan = planFor(root);

        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicCampaign", List.class);
        instrument.setAccessible(true);
        instrument.invoke(new CausynthPipeline(null),
                Collections.singletonList(plan));

        Body body = root.getActiveBody();
        List<String> hooks = hookNames(body);
        assertEquals(1, count(hooks, "enterRegionFrame"));

        // Admission, and everything it decides on the way in, happens while
        // the workload's path condition is not recording.
        assertMuted(hooks, "enterRegionFrame");
        // The two exits that already had a bracket keep it, so the boundary
        // stays one rule for the family rather than a special case.
        assertMuted(hooks, "exitRegionFrame");
        assertMuted(hooks, "throwRegionFrame");
    }

    @Test
    public void accessorCallContextIsMutedOnBothEdges() throws Exception {
        SootMethod caller = accessorCaller();
        ConcolicMaterializationSelection selection =
                new ConcolicMaterializationSelection();
        selection.addAccessorCallTarget(accessorAction(caller));

        Method hookCatalog = Class.forName(CausynthPipeline.class.getName()
                + "$HookCatalog").getDeclaredMethod("concolic");
        hookCatalog.setAccessible(true);
        Object refs = hookCatalog.invoke(null);
        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicAccessorCallContexts",
                ConcolicMaterializationSelection.class, refs.getClass());
        instrument.setAccessible(true);
        instrument.invoke(new CausynthPipeline(null), selection, refs);

        List<String> hooks = hookNames(caller.getActiveBody());
        assertEquals(1, count(hooks, "enterAccessorCallContext"));
        // Normal and exceptional close, so an accessor that throws does not
        // leave the workload's own frames recording GraphChecker's cleanup.
        assertEquals(2, count(hooks, "exitAccessorCallContext"));
        assertMuted(hooks, "enterAccessorCallContext");
        assertMuted(hooks, "exitAccessorCallContext");
        // The materialization the context exists for stays inside the same
        // mute rather than opening a second one.
        assertTrue(hooks.contains("materializeField"));
    }

    @Test
    public void configuredSourceHelperGetsOneExactMutedCallContext()
            throws Exception {
        ConfiguredSourceFixture fixture = configuredSourceFixture();
        InstrumentationPlan plan = planForConfiguredSource(fixture);

        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicCampaign", List.class);
        instrument.setAccessible(true);
        instrument.invoke(new CausynthPipeline(null),
                Collections.singletonList(plan));

        List<String> hooks = hookNames(fixture.helper.getActiveBody());
        assertEquals(1, count(hooks,
                "enterConfiguredSourcePhaseCallSite"));
        assertEquals(1, count(hooks,
                "exitConfiguredSourcePhaseCallSite"));
        assertEquals(1, count(hooks,
                "throwConfiguredSourcePhaseCallSite"));
        assertMuted(hooks, "enterConfiguredSourcePhaseCallSite");
        assertMuted(hooks, "exitConfiguredSourcePhaseCallSite");
        // The exceptional close is reached directly from the selected
        // invocation's trap and therefore inherits the pause opened before
        // entry.  A linear unit walk sees the unreachable normal resume just
        // before the handler; assertConfiguredSourceCleanup pins the actual
        // handler close/resume sequence instead.
        assertConfiguredSourceCleanup(hooks);
        assertInvocationInsideMute(fixture.helper.getActiveBody(),
                fixture.hook.getSignature());
        assertTrue(plan.envelopeMethods().contains(
                fixture.helper.getSignature()));
    }

    private static void assertConfiguredSourceCleanup(List<String> hooks) {
        int enter = hooks.indexOf("enterConfiguredSourcePhaseCallSite");
        assertTrue("configured source entry was not found", enter > 0);
        assertEquals(PAUSE, hooks.get(enter - 1));
        // The source invocation itself is not a runtime hook and sits between
        // entry and the first exit.  The first exit/resume is the normal edge;
        // the second pair is reached directly from the invocation's trap, so
        // its inherited pause is not visible in this linear hook list.
        assertEquals("exitConfiguredSourcePhaseCallSite",
                hooks.get(enter + 1));
        assertEquals(RESUME, hooks.get(enter + 2));
        assertEquals("throwConfiguredSourcePhaseCallSite",
                hooks.get(enter + 3));
        assertEquals(RESUME, hooks.get(enter + 4));
    }

    private static void assertInvocationInsideMute(Body body,
                                                   String signature) {
        List<String> invocations = new ArrayList<>();
        int selected = -1;
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()) continue;
            soot.SootMethodRef ref = ((Stmt) unit).getInvokeExpr()
                    .getMethodRef();
            String encoded = ref.getSignature();
            if (signature.equals(encoded)) selected = invocations.size();
            invocations.add(encoded);
        }
        assertTrue("configured source invocation was not found",
                selected >= 0);
        assertEquals("configured source helper was not muted on entry",
                PAUSE, nearestRuntimeBoundary(invocations, selected, -1));
        assertEquals("configured source helper was not muted on exit",
                RESUME, nearestRuntimeBoundary(invocations, selected, 1));
    }

    private static String nearestRuntimeBoundary(List<String> invocations,
                                                 int from, int step) {
        for (int index = from + step;
             index >= 0 && index < invocations.size(); index += step) {
            String signature = invocations.get(index);
            if (signature.contains(RUNTIME_CLASS + ": void " + PAUSE
                    + "()")) return PAUSE;
            if (signature.contains(RUNTIME_CLASS + ": void " + RESUME
                    + "()")) return RESUME;
        }
        return "<none>";
    }

    /**
     * Asserts every occurrence of {@code hook} runs inside a muted subtree.
     *
     * <p>The nearest mute boundary before the hook must be a pause and the
     * nearest one after it a resume.  That is the property the bracket exists
     * for, and it is deliberately not "the hook is adjacent to a pause": one
     * bracket may legitimately hold several hooks of the same evidence call -
     * opening an accessor context and materializing the field it exists for
     * are one bookkeeping subtree, not two - while a hook emitted with no
     * bracket at all reaches a boundary of the wrong kind, or none.</p>
     */
    private static void assertMuted(List<String> hooks, String hook) {
        boolean seen = false;
        for (int index = 0; index < hooks.size(); index++) {
            if (!hook.equals(hooks.get(index))) continue;
            seen = true;
            assertEquals(hook + " is not inside a muted subtree",
                    PAUSE, nearestBoundary(hooks, index, -1));
            assertEquals(hook + " does not leave its muted subtree",
                    RESUME, nearestBoundary(hooks, index, 1));
        }
        assertTrue(hook + " was never emitted", seen);
    }

    private static String nearestBoundary(List<String> hooks, int from,
                                          int step) {
        for (int index = from + step; index >= 0 && index < hooks.size();
             index += step) {
            String name = hooks.get(index);
            if (PAUSE.equals(name) || RESUME.equals(name)) return name;
        }
        return "<none>";
    }

    private static SootMethod regionRoot() {
        G.reset();
        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        Scene.v().addClass(new SootClass("java.lang.String",
                Modifier.PUBLIC));
        SootClass owner = new SootClass("example.Region", Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static SootMethod accessorCaller() {
        G.reset();
        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        Scene.v().addClass(new SootClass("java.lang.String",
                Modifier.PUBLIC));
        SootClass box = new SootClass("example.Box", Modifier.PUBLIC);
        box.setApplicationClass();
        SootField value = new SootField("value", IntType.v(),
                Modifier.PUBLIC);
        box.addField(value);
        SootMethod reader = new SootMethod("value", Collections.emptyList(),
                IntType.v(), Modifier.PUBLIC);
        box.addMethod(reader);
        Scene.v().addClass(box);

        SootClass owner = new SootClass("example.Caller", Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootMethod method = new SootMethod("read",
                Collections.<soot.Type>singletonList(box.getType()),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local held = Jimple.v().newLocal("held", box.getType());
        Local read = Jimple.v().newLocal("read", IntType.v());
        body.getLocals().add(held);
        body.getLocals().add(read);
        body.getUnits().add(Jimple.v().newIdentityStmt(held,
                Jimple.v().newParameterRef(box.getType(), 0)));
        body.getUnits().add(Jimple.v().newAssignStmt(read,
                Jimple.v().newVirtualInvokeExpr(held, reader.makeRef())));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static ConfiguredSourceFixture configuredSourceFixture() {
        G.reset();
        SootClass object = new SootClass("java.lang.Object", Modifier.PUBLIC);
        Scene.v().addClass(object);
        SootClass string = new SootClass("java.lang.String", Modifier.PUBLIC);
        Scene.v().addClass(string);
        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));

        SootClass hookOwner = new SootClass("example.SourceHook",
                Modifier.PUBLIC);
        SootMethod hook = new SootMethod("symbolize", Arrays.asList(
                string.getType(), object.getType(), string.getType()),
                BooleanType.v(), Modifier.PUBLIC | Modifier.STATIC);
        hookOwner.addMethod(hook);
        Scene.v().addClass(hookOwner);

        SootClass helperOwner = new SootClass("example.SourceDeclarations",
                Modifier.PUBLIC);
        helperOwner.setApplicationClass();
        Scene.v().addClass(helperOwner);
        SootMethod helper = new SootMethod("declare",
                Collections.<soot.Type>singletonList(object.getType()),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        helperOwner.addMethod(helper);
        Body helperBody = Jimple.v().newBody(helper);
        helper.setActiveBody(helperBody);
        Local owner = Jimple.v().newLocal("owner", object.getType());
        Local result = Jimple.v().newLocal("result", BooleanType.v());
        helperBody.getLocals().add(owner);
        helperBody.getLocals().add(result);
        helperBody.getUnits().add(Jimple.v().newIdentityStmt(owner,
                Jimple.v().newParameterRef(object.getType(), 0)));
        helperBody.getUnits().add(Jimple.v().newAssignStmt(result,
                Jimple.v().newStaticInvokeExpr(hook.makeRef(),
                        soot.jimple.StringConstant.v("SOURCE.A"), owner,
                        soot.jimple.StringConstant.v(
                                "<example.Producer: int value>"))));
        helperBody.getUnits().add(Jimple.v().newReturnVoidStmt());

        SootClass producer = new SootClass("example.Producer",
                Modifier.PUBLIC);
        producer.setApplicationClass();
        Scene.v().addClass(producer);
        SootMethod root = new SootMethod("produce", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        producer.addMethod(root);
        Body rootBody = Jimple.v().newBody(root);
        root.setActiveBody(rootBody);
        rootBody.getUnits().add(Jimple.v().newReturnVoidStmt());
        return new ConfiguredSourceFixture(root, helper, hook);
    }

    private static JsonObject accessorAction(SootMethod caller) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "PORT.accessor");
        action.addProperty("accessorCallerMethod", caller.getSignature());
        action.addProperty("accessorCallUnitIndex", 1);
        action.addProperty("accessorDeclaredCallee",
                "<example.Box: int value()>");
        action.addProperty("accessorImplementationMethod",
                "<example.Box: int value()>");
        action.addProperty("accessFieldSignature", "<example.Box: int value>");
        return action;
    }

    private InstrumentationPlan planFor(SootMethod root) throws Exception {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.SEED.bracket");
        task.addProperty("goalId", "GOAL.TARGET_REACH.bracket");
        task.addProperty("sourceKey", "test/node#epoch0");
        task.addProperty("occurrenceId", "test/node#epoch0/region/R#1");
        task.addProperty("relationKey", "test/node/relation/R/segment/S#0");
        task.addProperty("regionId", "R");
        task.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        task.addProperty("targetMethod", root.getSignature());
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "STATIC_CONTEXT");
        selector.addProperty("method", root.getSignature());
        task.add("rootSelector", selector);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);

        Path plan = folder.newFile("task-plan.jsonl").toPath();
        Files.write(plan, Collections.singletonList(task.toString()),
                StandardCharsets.UTF_8);
        List<InstrumentationPlan> campaign = InstrumentationPlan.campaign(
                plan, "TASK.SEED.bracket");
        assertEquals(1, campaign.size());
        return campaign.get(0);
    }

    private InstrumentationPlan planForConfiguredSource(
            ConfiguredSourceFixture fixture) throws Exception {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.SEED.source-helper");
        task.addProperty("goalId", "GOAL.TARGET_REACH.source-helper");
        task.addProperty("sourceKey", "test/node#epoch0");
        String occurrenceId = "test/node#epoch0/region/R#1";
        task.addProperty("occurrenceId", occurrenceId);
        task.addProperty("relationKey", "test/node/relation/R/segment/S#0");
        task.addProperty("regionId", "R");
        task.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        task.addProperty("targetMethod", fixture.root.getSignature());
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "STATIC_CONTEXT");
        selector.addProperty("method", fixture.root.getSignature());
        task.add("rootSelector", selector);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);

        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                "SOURCE.A", "<example.Producer: int value>",
                fixture.helper.getSignature(), 1));
        ConfiguredSourcePhaseContract.Declaration decoded =
                ConfiguredSourcePhaseContract.declarationsOf(
                        declarations).get(0);
        JsonObject occurrence =
                ConfiguredSourcePhaseContract.occurrence(decoded,
                        occurrenceId, 1, 10L, 9L, 11L,
                        fixture.hook.getSignature(),
                        Collections.singletonList(9L));
        JsonArray phases = new JsonArray();
        phases.add(occurrence);
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);

        Path plan = folder.newFile("source-helper-task-plan.jsonl").toPath();
        Files.write(plan, Collections.singletonList(task.toString()),
                StandardCharsets.UTF_8);
        List<InstrumentationPlan> campaign = InstrumentationPlan.campaign(
                plan, "TASK.SEED.source-helper");
        assertEquals(1, campaign.size());
        return campaign.get(0);
    }

    private static final class ConfiguredSourceFixture {
        private final SootMethod root;
        private final SootMethod helper;
        private final SootMethod hook;

        private ConfiguredSourceFixture(SootMethod root, SootMethod helper,
                                        SootMethod hook) {
            this.root = root;
            this.helper = helper;
            this.hook = hook;
        }
    }

    private static List<String> hookNames(Body body) {
        List<String> result = new ArrayList<>();
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            soot.SootMethodRef ref = ((Stmt) unit).getInvokeExpr()
                    .getMethodRef();
            if (RUNTIME_CLASS.equals(ref.declaringClass().getName())) {
                result.add(ref.name());
            }
        }
        return result;
    }

    private static int count(List<String> values, String expected) {
        int result = 0;
        for (String value : values) {
            if (expected.equals(value)) result++;
        }
        return result;
    }
}
