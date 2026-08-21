package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections
        .InstrumentationPlan;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.Body;
import soot.G;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

/**
 * The concolic pass rewrites the campaign's envelope, and nothing else.
 *
 * <p>The pass this pins used to walk every application method once per plan
 * row, and its associative-read branch wrapped every {@code Map.get} it
 * walked past in
 * {@code pauseObservation -> materializeAssociativeRead -> resumeObservation}
 * - two reflective calls into a native VM gate - whether or not the task had
 * selected that read.  The hook returns immediately when no region is active,
 * but only after both of those calls have been made, so an HDFS startup paid
 * them on every hash lookup {@code MiniDFSCluster.waitActive()} makes while a
 * three-thread fixture, which makes almost none, stayed fast.</p>
 *
 * <p>Four properties keep that from returning: a method outside the envelope
 * is not rewritten at all; an associative read is wrapped only where the plan
 * named an exact method and unit; one site named by two tasks is rewritten
 * once; and the emitted site is the hook alone, because the mute now belongs
 * to the hook, which takes it only after its own region check.</p>
 */
public class ConcolicEnvelopeScopeTest {

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String RUNTIME_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime";
    private static final String ASSOCIATIVE_READ = "materializeAssociativeRead";
    /** The unit index of the {@code Map.get} in a reader body built here. */
    private static final int READ_UNIT = 2;

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void anUnselectedMapReadInsideTheEnvelopeIsLeftAlone()
            throws Exception {
        scene();
        SootMethod reader = mapReader("example.Reader");
        // The plan names this method - it owns a selected local - but names
        // a different unit.  A selected method is not a selected site.
        instrument(campaign(localAction(reader, "other", READ_UNIT + 1)));

        assertEquals(0, count(hookNames(reader.getActiveBody()),
                ASSOCIATIVE_READ));
    }

    @Test
    public void theExactSelectedMapReadSiteIsWrappedOnce() throws Exception {
        scene();
        SootMethod reader = mapReader("example.Reader");
        instrument(campaign(localAction(reader, "value", READ_UNIT)));

        List<String> hooks = hookNames(reader.getActiveBody());
        assertEquals(1, count(hooks, ASSOCIATIVE_READ));
        // The hook is emitted alone.  It owns its own mute and takes it only
        // after its thread-local region check has admitted the call, so a
        // bracket here would put a native VM gate call back in front of that
        // check - which is exactly what an inactive thread must not pay on
        // every hash lookup.
        int index = hooks.indexOf(ASSOCIATIVE_READ);
        assertFalse(hooks.toString(), index > 0
                && "pauseObservation".equals(hooks.get(index - 1)));
        assertFalse(hooks.toString(), index + 1 < hooks.size()
                && "resumeObservation".equals(hooks.get(index + 1)));
    }

    @Test
    public void aMapReadOutsideTheEnvelopeIsNotRewritten() throws Exception {
        scene();
        SootMethod reader = mapReader("example.Reader");
        SootMethod outsider = mapReader("example.Outsider");
        instrument(campaign(localAction(reader, "value", READ_UNIT)));

        assertEquals(1, count(hookNames(reader.getActiveBody()),
                ASSOCIATIVE_READ));
        // Not one hook of any kind: the pass never opened this body.
        assertEquals(Collections.<String>emptyList(),
                hookNames(outsider.getActiveBody()));
    }

    @Test
    public void oneSiteNamedByTwoTasksIsRewrittenOnce() throws Exception {
        scene();
        SootMethod reader = mapReader("example.Reader");
        instrument(campaign(localAction(reader, "value", READ_UNIT),
                localAction(reader, "value", READ_UNIT)));

        assertEquals(1, count(hookNames(reader.getActiveBody()),
                ASSOCIATIVE_READ));
    }

    private void instrument(List<InstrumentationPlan> campaign)
            throws Exception {
        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicCampaign", List.class);
        instrument.setAccessible(true);
        instrument.invoke(new CausynthPipeline(null), campaign);
    }

    private static void scene() {
        G.reset();
        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        Scene.v().addClass(new SootClass("java.lang.String",
                Modifier.PUBLIC));
        SootClass map = new SootClass("java.util.Map",
                Modifier.PUBLIC | Modifier.INTERFACE);
        map.addMethod(new SootMethod("get",
                Collections.<Type>singletonList(
                        RefType.v("java.lang.Object")),
                RefType.v("java.lang.Object"),
                Modifier.PUBLIC | Modifier.ABSTRACT));
        Scene.v().addClass(map);
        map.setApplicationClass();

        SootClass owner = new SootClass("example.Region", Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootMethod root = new SootMethod("run", Collections.<Type>emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(root);
        Body body = Jimple.v().newBody(root);
        root.setActiveBody(body);
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
    }

    /**
     * A static reader whose unit {@value #READ_UNIT} is one {@code Map.get}.
     *
     * <pre>
     *   u0: map   := @parameter0
     *   u1: key   := @parameter1
     *   u2: value  = interfaceinvoke map.get(key)
     *   u3: return
     * </pre>
     */
    private static SootMethod mapReader(String className) {
        RefType mapType = RefType.v("java.util.Map");
        RefType objectType = RefType.v("java.lang.Object");
        SootClass owner = new SootClass(className, Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootMethod method = new SootMethod("read",
                Arrays.<Type>asList(mapType, objectType), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local map = Jimple.v().newLocal("map", mapType);
        Local key = Jimple.v().newLocal("key", objectType);
        Local value = Jimple.v().newLocal("value", objectType);
        body.getLocals().add(map);
        body.getLocals().add(key);
        body.getLocals().add(value);
        body.getUnits().add(Jimple.v().newIdentityStmt(map,
                Jimple.v().newParameterRef(mapType, 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(key,
                Jimple.v().newParameterRef(objectType, 1)));
        body.getUnits().add(Jimple.v().newAssignStmt(value,
                Jimple.v().newInterfaceInvokeExpr(map,
                        Scene.v().getMethod(
                                "<java.util.Map: java.lang.Object "
                                        + "get(java.lang.Object)>").makeRef(),
                        key)));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static JsonObject localAction(SootMethod owner, String local,
                                          int unitIndex) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "PORT." + local);
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("bindingMode", "LOCAL_DEFINITION");
        action.addProperty("method", owner.getSignature());
        action.addProperty("local", local);
        JsonObject site = new JsonObject();
        site.addProperty("unitIndex", unitIndex);
        JsonArray sites = new JsonArray();
        sites.add(site);
        action.add("definitionSites", sites);
        return action;
    }

    /** One task per supplied action, all rooted at the same region root. */
    private List<InstrumentationPlan> campaign(JsonObject... actions)
            throws Exception {
        List<String> rows = new ArrayList<>();
        List<String> ids = new ArrayList<>();
        for (int index = 0; index < actions.length; index++) {
            String taskId = "TASK.SEED.envelope" + index;
            ids.add(taskId);
            JsonObject task = new JsonObject();
            task.addProperty("taskId", taskId);
            task.addProperty("goalId", "GOAL.TARGET_REACH.envelope" + index);
            task.addProperty("sourceKey", "test/node#epoch0");
            task.addProperty("occurrenceId",
                    "test/node#epoch0/region/R#" + (index + 1));
            task.addProperty("relationKey",
                    "test/node/relation/R/segment/S#" + index);
            task.addProperty("regionId", "R");
            task.addProperty("goalKind", "TARGET_REACH_CLOSURE");
            task.addProperty("targetMethod", "<example.Region: void run()>");
            JsonObject selector = new JsonObject();
            selector.addProperty("kind", "STATIC_CONTEXT");
            selector.addProperty("method", "<example.Region: void run()>");
            task.add("rootSelector", selector);
            JsonArray inputActions = new JsonArray();
            inputActions.add(actions[index]);
            task.add("inputActions", inputActions);
            task.add("branches", new JsonArray());
            LoopBoundPolicy.cfgBackedges(8).writeTo(task);
            JsonObject admission = new JsonObject();
            admission.addProperty("state", "EXECUTABLE");
            task.add("admission", admission);
            rows.add(task.toString());
        }
        Path plan = folder.newFile("task-plan.jsonl").toPath();
        Files.write(plan, rows, StandardCharsets.UTF_8);
        List<InstrumentationPlan> campaign = InstrumentationPlan.campaign(
                plan, String.join(",", ids));
        assertEquals(actions.length, campaign.size());
        return campaign;
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
