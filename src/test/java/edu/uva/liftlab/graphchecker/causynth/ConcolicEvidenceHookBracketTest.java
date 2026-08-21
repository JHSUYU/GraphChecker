package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections
        .ConcolicMaterializationSelection;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections
        .InstrumentationPlan;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.Body;
import soot.G;
import soot.IntType;
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
import java.util.Collections;
import java.util.List;

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
