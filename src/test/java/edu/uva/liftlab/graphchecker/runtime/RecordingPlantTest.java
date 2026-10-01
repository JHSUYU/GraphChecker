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
 * A native reproduction's plant: which rows a plant file may hold, and which
 * enclosing occurrence of a marker call a row plants.
 */
public class RecordingPlantTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String SITE = "<o.a.h.ipc.Client: void send()>#u16";
    private static final String OUTER = address("REGION.outer");
    private static final String INNER = address("REGION.inner");

    /** A plant row per file line: accepted, or the row refused. */
    @Test
    public void aPlantHoldsMarkerRowsOnly() throws Exception {
        String id = OccurrenceAddress.parse(OUTER).id();
        Object[][] files = {
                {"{\"kind\":\"MARKER\",\"occurrence\":\"" + id
                        + "\",\"siteId\":\"" + SITE + "\",\"value\":true}",
                        Collections.singletonMap(SITE,
                                Collections.singletonMap(id, true))},
                {"{\"kind\":\"CLOCK\",\"occurrence\":\"" + id
                        + "\",\"siteId\":\"" + SITE + "\",\"value\":true}",
                        null},
                {"{\"kind\":\"MARKER\",\"occurrence\":\"" + id
                        + "\",\"siteId\":\"" + SITE + "\",\"value\":\"true\"}",
                        null},
                {"{\"kind\":\"MARKER\",\"occurrence\":\"" + id
                        + "\",\"value\":true}", null},
        };
        for (Object[] file : files) {
            File plant = folder.newFile();
            Files.write(plant.toPath(), ((String) file[0] + "\n")
                    .getBytes(StandardCharsets.UTF_8));
            try {
                assertEquals((String) file[0], file[1],
                        RecordingPlant.read(plant.toPath()));
                if (file[1] == null) fail("accepted " + file[0]);
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

    private static String address(String region) {
        return OccurrenceAddress.of(NodeId.parse("wl/dn1#epoch0"), region,
                CausalContext.of(Role.of("CLIENT"), "heartbeat", 1),
                ExecutionIndex.empty()).render();
    }
}
