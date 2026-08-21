package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
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
        assertTrue(selected.materializations().matchesSharedCarrierSite(
                access, 3, "example.Keys", "currentKey"));
        assertTrue(!selected.materializations().matchesSharedCarrierSite(
                access, 4, "example.Keys", "currentKey"));
        assertTrue(!selected.materializations().matchesSharedCarrierSite(
                access, 3, "example.Keys", "otherKey"));
        assertTrue(selected.materializations()
                .selectsSharedCarrierDeclaration(
                        "example.Keys", "currentKey"));
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
