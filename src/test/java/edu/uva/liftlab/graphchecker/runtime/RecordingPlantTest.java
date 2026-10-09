package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/**
 * A native reproduction's plant: which rows a plant file may hold, which
 * enclosing occurrence of a marker call or hook a row plants at, and which
 * enclosing occurrence of a fatal decision is the anchor's.
 */
public class RecordingPlantTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String SITE = "<o.a.h.ipc.Client: void send()>#u16";
    private static final String GUARD = "<o.a.h.Sasl: void handle()>#u4";
    private static final String OUTER = address("REGION.outer");
    private static final String INNER = address("REGION.inner");
    private static final String ID = OccurrenceAddress.parse(OUTER).id();

    /** A plant file: its markers, hooks, fatal arms and anchor, or
     *  refused. */
    @Test
    public void aPlantHoldsRootsOrdersAndOneTarget() throws Exception {
        String marker = "{\"kind\":\"ROOT\",\"category\":\"FAULT\","
                + "\"rootId\":\"FAULT:IPC\",\"occurrence\":\"" + ID
                + "\",\"siteId\":\"" + SITE + "\",\"value\":\"true\","
                + "\"row\":0}\n";
        String hook = "{\"kind\":\"ROOT\",\"category\":\"HOOK\","
                + "\"rootId\":\"HDFS.X\",\"occurrence\":\"" + ID
                + "\",\"value\":\"false\",\"row\":1}\n";
        String order = "{\"kind\":\"ORDER\",\"before\":\"b|\","
                + "\"after\":\"a|\",\"row\":2}\n";
        String event = "{\"kind\":\"WAKE\",\"context\":\"c\","
                + "\"site\":\"s\",\"k\":0}";
        String realized = "{\"kind\":\"ORDER\",\"scope\":\"EVENT\","
                + "\"before\":" + event + ",\"after\":" + event
                + ",\"row\":5}\n";
        String target = target(ID, "false", 3);
        Map<String, Map<String, RecordingPlant.Root>> markers =
                Collections.singletonMap(SITE, Collections.singletonMap(ID,
                        new RecordingPlant.Root(0, "true")));
        Map<String, RecordingPlant.Root> hooks = Collections.singletonMap(
                "HDFS.X", new RecordingPlant.Root(1, "false"));
        Object[][] files = {
                {marker + hook + order + target, markers, hooks},
                {order + target, Collections.emptyMap(),
                        Collections.emptyMap()},
                // The confirmed world's realized order, between events.
                {realized + target, Collections.emptyMap(),
                        Collections.emptyMap()},
                // A root of a category no native run plants, a marker
                // without its call site or with no boolean, a row without
                // its number, an order naming no activation, one naming
                // no event.
                {marker.replace("FAULT", "CONFIG") + target, null, null},
                {marker.replace(SITE, "") + target, null, null},
                {marker.replace("\"true\"", "\"1\"") + target, null, null},
                {hook.replace(",\"row\":1", "") + target, null, null},
                // One root stated twice.
                {hook + hook.replace("\"row\":1", "\"row\":4") + target,
                        null, null},
                {order.replace("\"b|\"", "\"\"") + target, null, null},
                // An event without its k.
                {realized.replaceFirst(",\"k\":0", "") + target, null,
                        null},
                {"{\"kind\":\"CLOCK\",\"row\":0}\n" + target, null, null},
                // A clock root without its skew, a configuration without
                // its getters, one site named with two callees.
                {clock(OUTER, "", 0) + target, null, null},
                {"{\"kind\":\"ROOT\",\"category\":\"CONFIG\",\"rootId\":"
                        + "\"CONFIG:k\",\"occurrence\":\"" + ID + "\","
                        + "\"value\":\"7\",\"sites\":[],\"row\":0}\n"
                        + target, null, null},
                {clock(OUTER, "5", 0) + reading(CLOCK_SITE_ID,
                        "<a.Other: long now()>", 1) + target, null, null},
                // No target: the run could not tell what it reproduced.
                {marker, null, null},
                {marker + target + target("other", "true", 4), null, null},
        };
        for (Object[] file : files) {
            File plant = folder.newFile();
            Files.write(plant.toPath(),
                    ((String) file[0]).getBytes(StandardCharsets.UTF_8));
            try {
                RecordingPlant.Plant read = RecordingPlant.read(plant.toPath());
                if (file[1] == null) fail("accepted " + file[0]);
                assertEquals((String) file[0], file[1], read.markers);
                assertEquals((String) file[0], file[2], read.hooks);
                assertEquals((String) file[0],
                        Collections.singletonMap(GUARD, false),
                        read.fatalArms);
                assertEquals((String) file[0], ID, read.anchor);
                // The anchor and every root's mint occurrence are focused.
                assertEquals((String) file[0],
                        Collections.singleton(ID), read.focused);
            } catch (IOException refused) {
                if (file[1] != null) throw refused;
            }
        }
    }

    /** The occurrences enclosing a call, innermost first, and the one a
     *  plant of {@code planted} answers for. */
    @Test
    public void theInnermostPlantedEnclosingOccurrenceAnswers() {
        Object[][] calls = {
                {Arrays.asList(INNER, OUTER), OUTER, OUTER},
                {Arrays.asList(INNER, OUTER), INNER, INNER},
                {Collections.singletonList(INNER), OUTER, null},
                {Collections.<String>emptyList(), OUTER, null},
        };
        for (Object[] call : calls) {
            Map<String, RecordingPlant.Root> rows = Collections.singletonMap(
                    OccurrenceAddress.parse((String) call[1]).id(),
                    new RecordingPlant.Root(0, "true"));
            @SuppressWarnings("unchecked")
            List<String> enclosing = (List<String>) call[0];
            assertEquals(Arrays.toString(call), call[2],
                    RecordingPlant.plantedOccurrence(rows, enclosing));
        }
        assertEquals(null, RecordingPlant.plantedOccurrence(null,
                Collections.singletonList(OUTER)));
    }

    /** A hook plants under an enclosing occurrence the confirmation
     *  focuses, the innermost one, as a replay's mint does. */
    @Test
    public void aHookPlantsUnderAnyFocusedEnclosingOccurrence() {
        Object[][] calls = {
                {Arrays.asList(INNER, OUTER), OUTER},
                {Collections.singletonList(INNER), null},
                {Collections.<String>emptyList(), null},
        };
        for (Object[] call : calls) {
            @SuppressWarnings("unchecked")
            List<String> enclosing = (List<String>) call[0];
            assertEquals(Arrays.toString(call), call[1],
                    RecordingPlant.focusedOccurrence(
                            Collections.singleton(ID), enclosing));
        }
    }

    /** A fatal decision is at the anchor when an occurrence enclosing it,
     *  at any depth, is the anchor's. */
    @Test
    public void aFatalDecisionIsAtTheAnchorInsideItsOccurrence() {
        Object[][] decisions = {
                {Arrays.asList(INNER, OUTER), OUTER},
                {Collections.singletonList(OUTER), OUTER},
                {Collections.singletonList(INNER), null},
                {Collections.<String>emptyList(), null},
        };
        for (Object[] decision : decisions) {
            @SuppressWarnings("unchecked")
            List<String> enclosing = (List<String>) decision[0];
            assertEquals(Arrays.toString(decision), decision[1],
                    RecordingPlant.anchorOf(enclosing, ID));
        }
    }

    private static final String CLOCK_SITE_ID = "<a.Keys: void roll()>#u3";
    private static final String CLOCK_CALLEE =
            "<java.lang.System: long currentTimeMillis()>";
    private static final String DN2 = address("REGION.outer", "wl/dn2#epoch0");

    private static String clock(String occurrence, String skew, int row) {
        return "{\"kind\":\"ROOT\",\"category\":\"CLOCK\",\"rootId\":"
                + "\"REGION.outer.in.c\",\"occurrence\":\""
                + OccurrenceAddress.parse(occurrence).id() + "\",\"siteId\":\""
                + CLOCK_SITE_ID + "\",\"callee\":\"" + CLOCK_CALLEE
                + "\",\"javaType\":\"long\",\"clock\":{\"nanos\":1000000,"
                + "\"source\":\"currentTimeMillis\"},\"skew\":\"" + skew
                + "\",\"row\":" + row + "}\n";
    }

    private static String reading(String site, String callee, int row) {
        return "{\"kind\":\"CLOCK_SITE\",\"siteId\":\"" + site + "\","
                + "\"callee\":\"" + callee + "\",\"javaType\":\"long\","
                + "\"clock\":{\"nanos\":1000000,\"source\":"
                + "\"currentTimeMillis\"},\"regions\":[\"REGION.outer\"],"
                + "\"row\":" + row + "}\n";
    }

    /**
     * Values at calls' returns: a clock root's first reading under its mint
     * occurrence is the host plus its skew and jumps its node's clock; every
     * later declared reading of that clock on that node runs on from it
     * (none before it, none on another node, none outside a declaring
     * region); a configuration is its value at every getter call; an
     * accessor's read its value under its occurrence; any other call, or a
     * call of another callee at the site, returns what it returned.
     */
    @Test
    public void callReturnsReadThePlantedWorld() throws Exception {
        RecordingPlant.resetForTests();
        String config = "{\"kind\":\"ROOT\",\"category\":\"CONFIG\","
                + "\"rootId\":\"CONFIG:k\",\"occurrence\":\"" + ID + "\","
                + "\"sites\":[{\"siteId\":\"<a.Conf: void f()>#u1\","
                + "\"callee\":\"<a.Conf: int getInt()>\"}],"
                + "\"javaType\":\"int\",\"value\":\"7\",\"row\":2}\n";
        String read = "{\"kind\":\"ROOT\",\"category\":\"READ\","
                + "\"rootId\":\"READ.r\",\"occurrence\":\"" + ID + "\","
                + "\"siteId\":\"<a.Conf: void g()>#u2\",\"callee\":"
                + "\"<a.Box: java.lang.String name()>\",\"javaType\":"
                + "\"java.lang.String\",\"value\":\"planted\",\"row\":3}\n";
        File file = folder.newFile();
        Files.write(file.toPath(), (clock(OUTER, "100", 0)
                + reading(CLOCK_SITE_ID, CLOCK_CALLEE, 1) + config + read
                + target(ID, "false", 4)).getBytes(StandardCharsets.UTF_8));
        RecordingPlant.Plant plant = RecordingPlant.read(file.toPath());
        String other = address("REGION.outer", "wl/dn1#epoch1");
        Object[][] calls = {
                // Before the jump: the host.
                {CLOCK_SITE_ID, CLOCK_CALLEE, Arrays.asList(other), 5L, 5L},
                // The mint: host plus skew, and the node's clock jumps.
                {CLOCK_SITE_ID, CLOCK_CALLEE, Arrays.asList(INNER, OUTER),
                        10L, 110L},
                // Later readings of that node's clock run on from it.
                {CLOCK_SITE_ID, CLOCK_CALLEE, Arrays.asList(OUTER), 20L,
                        120L},
                // Another node, no region declaring it, another callee.
                {CLOCK_SITE_ID, CLOCK_CALLEE, Arrays.asList(DN2), 30L, 30L},
                {CLOCK_SITE_ID, CLOCK_CALLEE, Arrays.asList(INNER), 40L, 40L},
                {CLOCK_SITE_ID, "<a.Other: long now()>", Arrays.asList(OUTER),
                        50L, 50L},
                {"<a.Conf: void f()>#u1", "<a.Conf: int getInt()>",
                        Collections.<String>emptyList(), 3, 7},
                {"<a.Conf: void g()>#u2", "<a.Box: java.lang.String name()>",
                        Arrays.asList(OUTER), "recorded", "planted"},
                {"<a.Conf: void g()>#u2", "<a.Box: java.lang.String name()>",
                        Arrays.asList(INNER), "recorded", "recorded"},
                {"<a.Conf: void h()>#u9", CLOCK_CALLEE, Arrays.asList(OUTER),
                        60L, 60L},
        };
        for (Object[] call : calls) {
            @SuppressWarnings("unchecked")
            List<String> enclosing = (List<String>) call[2];
            assertEquals(Arrays.toString(call), call[4],
                    RecordingPlant.returnedAt(plant, (String) call[0],
                            (String) call[1], enclosing, call[3]));
        }
        // The agent rewrites each caller class at the callees it calls.
        Map<String, java.util.Set<String>> intercepted =
                RecordingPlant.interceptions(plant);
        assertEquals(Arrays.asList("a/Keys", "a/Conf"),
                new java.util.ArrayList<String>(intercepted.keySet()));
        assertEquals(new java.util.TreeSet<String>(Arrays.asList(
                "a/Conf.getInt ()I", "a/Box.name ()Ljava/lang/String;")),
                new java.util.TreeSet<String>(intercepted.get("a/Conf")));
        RecordingPlant.resetForTests();
    }

    /**
     * An answer at a port's call-return capture: the value carried as a
     * replay's attach carries it, its leaf named by the endpoint a replay's
     * attach names it by in the occurrence of a region declaring the port,
     * and written when the plant answers that endpoint.
     */
    @Test
    public void anAnswerIsWrittenAtTheEndpointAReplayNames() throws Exception {
        RecordingPlant.resetForTests();
        final String port = "XCH.1.resp.key-id";
        final String[] expected = new String[1];
        Thread naming = new Thread(() -> expected[0] = Identity.endpointAt(
                OccurrenceAddress.parse(OUTER), port, 0).id());
        naming.start();
        naming.join();
        File file = folder.newFile();
        Files.write(file.toPath(), ("{\"kind\":\"ANSWER\",\"endpoint\":\""
                + expected[0] + "\",\"port\":\"" + port + "\",\"siteId\":"
                + "\"<a.H: void h()>#u4\",\"callee\":\"<a.Msg: long keyId()>"
                + "\",\"regions\":[\"REGION.outer\"],\"value\":\"9\","
                + "\"row\":0}\n" + target(ID, "false", 1))
                .getBytes(StandardCharsets.UTF_8));
        final RecordingPlant.Plant plant = RecordingPlant.read(file.toPath());
        final Object[] answered = new Object[3];
        Thread planting = new Thread(() -> {
            answered[0] = RecordingPlant.returnedAt(plant, "<a.H: void h()>#u4",
                    "<a.Msg: long keyId()>", Arrays.asList(INNER, OUTER), 4L);
            // The next attach there is another endpoint: not answered.
            answered[1] = RecordingPlant.returnedAt(plant, "<a.H: void h()>#u4",
                    "<a.Msg: long keyId()>", Arrays.asList(INNER, OUTER), 4L);
            // Outside a declaring region nothing attaches.
            answered[2] = RecordingPlant.returnedAt(plant, "<a.H: void h()>#u4",
                    "<a.Msg: long keyId()>", Arrays.asList(INNER), 4L);
        });
        planting.start();
        planting.join();
        assertEquals(Arrays.asList(9L, 4L, 4L), Arrays.asList(answered));
        RecordingPlant.resetForTests();
    }

    private static String target(String occurrence, String arm, int row) {
        return "{\"kind\":\"TARGET\",\"occurrence\":\"" + occurrence
                + "\",\"siteId\":\"" + GUARD + "\",\"value\":" + arm
                + ",\"row\":" + row + "}\n";
    }

    private static String address(String region) {
        return address(region, "wl/dn1#epoch0");
    }

    private static String address(String region, String node) {
        return OccurrenceAddress.of(NodeId.parse(node), region,
                CausalContext.of(Role.of("CLIENT"), "heartbeat", 1),
                ExecutionIndex.empty()).render();
    }
}
