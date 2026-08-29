package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Collections;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConcolicInstrumentationSelectionsTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    /**
     * One instrumentation pass covers the union of the campaign's regions and
     * each task keeps its own selections, so a campaign of one is the
     * ordinary single-task run.  Every plan that fails to state a bounded
     * campaign is refused by name before any class is rewritten.
     */
    @Test
    public void oneInstrumentationPassCoversEveryAdmittedCampaignTask()
            throws Exception {
        Path plan = folder.newFile().toPath();
        Files.write(plan, (campaignTask("TASK.A", "<a.Producer: void run()>")
                        + campaignTask("TASK.B", "<b.Consumer: void run()>"))
                        .getBytes(StandardCharsets.UTF_8));
        List<ConcolicInstrumentationSelections.InstrumentationPlan> campaign =
                withPlan(plan, "TASK.A,TASK.B");
        assertEquals(2, campaign.size());
        assertEquals("<a.Producer: void run()>",
                campaign.get(0).rootMethod());
        assertEquals("<b.Consumer: void run()>",
                campaign.get(1).rootMethod());
        Set<String> applicationClasses = withPlanClasses(plan,
                "TASK.A,TASK.B");
        assertEquals(2, applicationClasses.size());
        assertTrue(applicationClasses.contains("a.Producer"));
        assertTrue(applicationClasses.contains("b.Consumer"));

        Path single = folder.newFile().toPath();
        Files.write(single, campaignTask("TASK.A", "<a.Producer: void run()>")
                .getBytes(StandardCharsets.UTF_8));
        assertEquals(1, withPlan(single, "TASK.A").size());

        Path duplicate = folder.newFile().toPath();
        Files.write(duplicate,
                (campaignTask("TASK.A", "<a.Producer: void run()>")
                        + campaignTask("TASK.A", "<b.Consumer: void run()>"))
                        .getBytes(StandardCharsets.UTF_8));
        assertCampaignRefused(duplicate, "TASK.A",
                "malformed plan: duplicate execution task TASK.A");

        System.setProperty(
                ConcolicInstrumentationSelections.MAX_TASKS_PROPERTY, "1");
        try {
            assertCampaignRefused(plan, "TASK.A,TASK.B",
                    "malformed plan: campaign in "
                            + plan.toAbsolutePath().normalize()
                            + " exceeds its bound of 1 tasks");
        } finally {
            System.clearProperty(
                    ConcolicInstrumentationSelections.MAX_TASKS_PROPERTY);
        }
    }

    @Test
    public void concreteSharedCarrierAddsOnlyItsExactReadSite()
            throws Exception {
        String root = "<example.Root: void run()>";
        String access = "<example.Keys: byte[] create()>";
        String field = "<example.Keys: example.Key currentKey>";
        String row = campaignTask("TASK.CARRIER", root)
                .replace("\"inputActions\":[]",
                        "\"inputActions\":[{"
                                + "\"mode\":\"CONCRETE\","
                                + "\"location\":\"HEAP_OBJECT_FIELD\","
                                + "\"bindingMode\":\"FIELD_ACCESS\","
                                + "\"accessFieldSignature\":\"" + field
                                + "\",\"staticAccessSiteId\":\"" + access
                                + "#u3\",\"accessSites\":[\"" + access
                                + "#u3\"]}]")
                .replace("\"admission\":{",
                        "\"sharedCarriers\":[{"
                                + "\"kind\":\"DECLARED_FIELD\","
                                + "\"declaringClass\":\"example.Keys\","
                                + "\"fieldName\":\"currentKey\","
                                + "\"descriptor\":\"Lexample/Key;\","
                                + "\"sourceKind\":"
                                + "\"ACTIVATION_FIELD_RECEIVER\","
                                + "\"fieldPath\":[]}],\"admission\":{");
        Path plan = folder.newFile().toPath();
        Files.write(plan, row.getBytes(StandardCharsets.UTF_8));

        ConcolicInstrumentationSelections.InstrumentationPlan selected =
                withPlan(plan, "TASK.CARRIER").get(0);
        assertTrue(selected.envelopeMethods().contains(access));
    }

    @Test
    public void concreteOutputCaptureAnchorAddsOnlyItsAccessorHook()
            throws Exception {
        String anchoredPort = "REGION.1.in.anchored";
        String unrelatedPort = "REGION.1.in.unrelated";
        String anchoredCaller = "<example.Keys: int anchored()>";
        String unrelatedCaller = "<example.Keys: int unrelated()>";
        JsonArray actions = new JsonArray();
        actions.add(accessorAction(anchoredPort, anchoredCaller, 3));
        actions.add(accessorAction(unrelatedPort, unrelatedCaller, 4));

        ConcolicInstrumentationSelections.ConcolicMaterializationSelection
                selected = new ConcolicInstrumentationSelections
                .ConcolicMaterializationSelection();
        selected.addCapturePrerequisiteTargets(
                exactHeapClosure(anchoredPort), actions);

        assertEquals(1, selected.accessorCalls().size());
        ConcolicInstrumentationSelections.AccessorCallTarget target =
                selected.accessorCalls().iterator().next();
        assertEquals(anchoredCaller, target.callerMethod);
        assertEquals(3, target.callUnitIndex);
        assertTrue(selected.accessorCallerMethods().contains(
                anchoredCaller));
        assertTrue(!selected.accessorCallerMethods().contains(
                unrelatedCaller));
    }

    @Test
    public void configuredSourceHelperIsPartOfTheReplayEnvelope()
            throws Exception {
        String root = "<example.Producer: long produce()>";
        String helper = "<example.SourceDeclarations: void declare()>";
        String callee = "<example.SourceHook: boolean symbolize(java.lang.String,java.lang.Object,java.lang.String)>";
        JsonObject task = JsonParser.parseString(
                campaignTask("TASK.SOURCE", root)).getAsJsonObject();
        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                "SOURCE.A", "<example.Producer: int value>",
                helper, 2));
        ConfiguredSourcePhaseContract.Declaration decoded =
                ConfiguredSourcePhaseContract.declarationsOf(
                        declarations).get(0);
        JsonArray phases = new JsonArray();
        phases.add(ConfiguredSourcePhaseContract.occurrence(decoded,
                task.get("occurrenceId").getAsString(), 1,
                10L, 9L, 11L, callee,
                Collections.singletonList(9L)));
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        Path plan = folder.newFile().toPath();
        Files.write(plan, (task.toString() + "\n")
                .getBytes(StandardCharsets.UTF_8));

        ConcolicInstrumentationSelections.InstrumentationPlan selected =
                withPlan(plan, "TASK.SOURCE").get(0);
        assertTrue(selected.envelopeMethods().contains(root));
        assertTrue(selected.envelopeMethods().contains(helper));
        assertEquals(1, selected.configuredSourcePhases().size());
        Set<String> applicationClasses = withPlanClasses(
                plan, "TASK.SOURCE");
        assertTrue(applicationClasses.contains("example.Producer"));
        assertTrue(applicationClasses.contains("example.SourceDeclarations"));
    }

    private static void assertCampaignRefused(Path plan, String selected,
                                              String expected) {
        try {
            withPlan(plan, selected);
            fail("a malformed campaign plan must be refused");
        } catch (RuntimeException refused) {
            String message = String.valueOf(refused.getCause() == null
                    ? refused.getMessage() : refused.getCause().getMessage());
            assertTrue(message + " must name: " + expected,
                    message.contains(expected));
        }
    }

    private static List<ConcolicInstrumentationSelections.InstrumentationPlan>
    withPlan(Path plan, String selected) {
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", selected);
        try {
            return ConcolicInstrumentationSelections
                    .instrumentationCampaignFromEnvironment();
        } finally {
            System.clearProperty("causynth.concolic.task.plan");
            System.clearProperty("causynth.concolic.task.id");
        }
    }

    private static Set<String> withPlanClasses(Path plan, String selected) {
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", selected);
        try {
            return ConcolicInstrumentationSelections
                    .applicationClassesFromEnvironment();
        } finally {
            System.clearProperty("causynth.concolic.task.plan");
            System.clearProperty("causynth.concolic.task.id");
        }
    }

    private static JsonObject accessorAction(String symbol, String caller,
                                             int unitIndex) {
        String field = "<example.Key: int value>";
        JsonObject action = new JsonObject();
        action.addProperty("mode", "CONCRETE");
        action.addProperty("symbol", symbol);
        action.addProperty("portId", symbol);
        action.addProperty("cell", field);
        action.addProperty("javaType", "int");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessFieldSignature", field);
        action.addProperty("accessorCallerMethod", caller);
        action.addProperty("accessorCallUnitIndex", unitIndex);
        action.addProperty("accessorDeclaredCallee",
                "<example.Key: int getValue()>");
        action.addProperty("accessorImplementationMethod",
                "<example.Key: int getValue()>");
        return action;
    }

    private static OutputClosureContract exactHeapClosure(String anchor) {
        String port = "REGION.1.out.value";
        String field = "<example.Output: int value>";
        String method = "<example.Output: void set(int)>";
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.anchor");
        capture.addProperty("outputPort", port);
        capture.addProperty("captureKind",
                OutputCaptureSpec.FIELD_WRITE_STATE);
        capture.addProperty("outputCell", field);
        capture.addProperty("javaType", "int");
        capture.addProperty("fieldSignature", field);
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("value");
        capture.add("fieldPath", fieldPath);
        capture.addProperty("definitionMethod", method);
        capture.addProperty("definitionUnitIndex", 2);
        capture.addProperty("outputSiteId", method + "#u2");
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("occurrenceScope",
                OutputCaptureSpec.REGION_ACTIVATION_SCOPE);
        capture.addProperty(OutputCaptureSpec.INSTANCE_SCOPED_PRODUCER,
                true);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", field);
        slice.addProperty("captureAnchorPort", anchor);
        for (String name : new String[]{"sites", "staticSites",
                "causalEdgeIds", "captureBindingIssues"}) {
            slice.add(name, new JsonArray());
        }
        JsonArray inputs = new JsonArray();
        inputs.add(anchor);
        slice.add("inputPorts", inputs);
        JsonArray methods = new JsonArray();
        methods.add(method);
        slice.add("methods", methods);
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        return OutputClosureCodec.singleton("test/relation/TASK.ANCHOR",
                "REGION.1", Collections.<String>emptyList(), port, field,
                "HEAP_STATE", "int", slice);
    }

    /** One minimal executable campaign row. */
    private static String campaignTask(String taskId, String rootMethod) {
        return "{\"taskId\":\"" + taskId + "\",\"goalId\":\"GOAL." + taskId
                + "\",\"sourceKey\":\"TEST_DRIVER/test#epoch0\","
                + "\"occurrenceId\":"
                + "\"TEST_DRIVER/test#epoch0/region/REGION.1#1\","
                + "\"relationKey\":\"test/relation/" + taskId + "\","
                + "\"regionId\":\"REGION.1\","
                + "\"goalKind\":\"TARGET_REACH_CLOSURE\","
                + "\"rootSelector\":{\"kind\":\"RECEIVER_CONTEXT\","
                + "\"method\":\"" + rootMethod + "\","
                + "\"receiverClass\":\"java.lang.Object\","
                + "\"causalAnchor\":{"
                + "\"sourceKey\":\"TEST_DRIVER/test#epoch0\","
                + "\"kind\":\"REGISTERED_SOURCE\"}},"
                + "\"inputActions\":[],\"branches\":[],"
                + "\"loopBound\":{\"schemaVersion\":1,"
                + "\"kind\":\"CFG_BACKEDGE\","
                + "\"scope\":\"ALL_EXECUTION_SCOPE_LOOPS\","
                + "\"maxBackedgeTraversals\":8,\"onLimit\":\"CUT_PATH\"},"
                + "\"admission\":{\"state\":\"EXECUTABLE\"}}\n";
    }
}
