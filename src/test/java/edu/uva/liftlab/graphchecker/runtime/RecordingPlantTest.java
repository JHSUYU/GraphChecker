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
 * enclosing occurrence of a marker call a row plants, and which enclosing
 * occurrence of a fatal decision is the anchor's.
 */
public class RecordingPlantTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String SITE = "<o.a.h.ipc.Client: void send()>#u16";
    private static final String GUARD = "<o.a.h.Sasl: void handle()>#u4";
    private static final String OUTER = address("REGION.outer");
    private static final String INNER = address("REGION.inner");
    private static final String ID = OccurrenceAddress.parse(OUTER).id();

    /** A plant file: its markers, fatal arms and anchor, or refused. */
    @Test
    public void aPlantHoldsMarkersAndOneTarget() throws Exception {
        String marker = row("MARKER", ID, SITE, "true");
        String target = row("TARGET", ID, GUARD, "false");
        Object[][] files = {
                {marker + target, Collections.singletonMap(SITE,
                        Collections.singletonMap(ID, true)),
                        Collections.singletonMap(GUARD, false)},
                {row("CLOCK", ID, SITE, "true") + target, null, null},
                {row("MARKER", ID, SITE, "\"true\"") + target, null, null},
                {row("MARKER", ID, "", "true") + target, null, null},
                // No target: the run could not tell what it reproduced.
                {marker, null, null},
                {marker + target + row("TARGET", "other", GUARD, "true"),
                        null, null},
        };
        for (Object[] file : files) {
            File plant = folder.newFile();
            Files.write(plant.toPath(),
                    ((String) file[0]).getBytes(StandardCharsets.UTF_8));
            try {
                RecordingPlant.Plant read = RecordingPlant.read(plant.toPath());
                if (file[1] == null) fail("accepted " + file[0]);
                assertEquals((String) file[0], file[1], read.markers);
                assertEquals((String) file[0], file[2], read.fatalArms);
                assertEquals((String) file[0], ID, read.anchor);
            } catch (IOException refused) {
                if (file[1] != null) throw refused;
            }
        }
    }

    /** The occurrences enclosing a call, innermost first, and the one a
     *  plant of {@code planted} at {@code site} answers for. */
    @Test
    public void theInnermostPlantedEnclosingOccurrenceAnswers() {
        Object[][] calls = {
                {SITE, Arrays.asList(INNER, OUTER), OUTER, OUTER},
                {SITE, Arrays.asList(INNER, OUTER), INNER, INNER},
                {SITE, Collections.singletonList(INNER), OUTER, null},
                {SITE + "7", Arrays.asList(INNER, OUTER), OUTER, null},
        };
        for (Object[] call : calls) {
            Map<String, Map<String, Boolean>> rows = Collections.singletonMap(
                    SITE, Collections.singletonMap(
                            OccurrenceAddress.parse((String) call[2]).id(),
                            true));
            @SuppressWarnings("unchecked")
            List<String> enclosing = (List<String>) call[1];
            assertEquals(Arrays.toString(call), call[3],
                    RecordingPlant.plantedOccurrence(rows, (String) call[0],
                            enclosing));
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

    private static String row(String kind, String occurrence, String site,
                              String value) {
        return "{\"kind\":\"" + kind + "\",\"occurrence\":\"" + occurrence
                + "\",\"siteId\":\"" + site + "\",\"value\":" + value + "}\n";
    }

    private static String address(String region) {
        return OccurrenceAddress.of(NodeId.parse("wl/dn1#epoch0"), region,
                CausalContext.of(Role.of("CLIENT"), "heartbeat", 1),
                ExecutionIndex.empty()).render();
    }
}
