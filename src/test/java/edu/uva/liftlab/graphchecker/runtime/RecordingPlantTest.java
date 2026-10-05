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
        String target = target(ID, "false", 3);
        Map<String, Map<String, RecordingPlant.Root>> markers =
                Collections.singletonMap(SITE, Collections.singletonMap(ID,
                        new RecordingPlant.Root(0, "true")));
        Map<String, Map<String, RecordingPlant.Root>> hooks =
                Collections.singletonMap("HDFS.X", Collections.singletonMap(
                        ID, new RecordingPlant.Root(1, "false")));
        Map<String, Map<String, RecordingPlant.Root>> none =
                Collections.emptyMap();
        Object[][] files = {
                {marker + hook + order + target, markers, hooks},
                {order + target, none, none},
                // A root of a category no native run plants, a marker
                // without its call site or with no boolean, a row without
                // its number, an order naming no activation.
                {marker.replace("FAULT", "CONFIG") + target, null, null},
                {marker.replace(SITE, "") + target, null, null},
                {marker.replace("\"true\"", "\"1\"") + target, null, null},
                {hook.replace(",\"row\":1", "") + target, null, null},
                {order.replace("\"b|\"", "\"\"") + target, null, null},
                {"{\"kind\":\"CLOCK\",\"row\":0}\n" + target, null, null},
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

    private static String target(String occurrence, String arm, int row) {
        return "{\"kind\":\"TARGET\",\"occurrence\":\"" + occurrence
                + "\",\"siteId\":\"" + GUARD + "\",\"value\":" + arm
                + ",\"row\":" + row + "}\n";
    }

    private static String address(String region) {
        return OccurrenceAddress.of(NodeId.parse("wl/dn1#epoch0"), region,
                CausalContext.of(Role.of("CLIENT"), "heartbeat", 1),
                ExecutionIndex.empty()).render();
    }
}
