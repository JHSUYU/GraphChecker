package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * A manual root is declared by the site it is read at, not by a region hash.
 *
 * <p>A region id is minted by the planner from what the recording selected,
 * so it moves whenever the retained selection moves -- and a campaign file
 * that spells one has to be re-derived by hand every time.  That is what
 * refused bug3's clock declaration at PLAN.  A static site -- the class and
 * method the cell is read in -- is what the experiment actually knows, and
 * the plan is what resolves it to the regions that cover it.</p>
 */
public class ManualRootSiteResolutionTest {

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String CLASS =
            "org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager";
    private static final String UPDATE_KEYS = "boolean updateKeys()";
    private static final String UPDATE_SIGNATURE =
            "<" + CLASS + ": " + UPDATE_KEYS + ">";
    private static final String CLOCK_CELL =
            "<org.apache.hadoop.util.Timer: long now()>.return";
    private static final String NN = "REGION.nn";
    private static final String NN_TWIN = "REGION.nn-twin";
    private static final String DN = "REGION.dn";

    /** One method planned twice on one node is two regions, and both mean it. */
    @Test
    public void aSiteDeclaresItsRootInEveryRegionThatCoversIt()
            throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection = read(
                "{\"class\":\"" + CLASS + "\",\"method\":\"" + UPDATE_KEYS
                        + "\",\"cells\":[\"" + CLOCK_CELL + "\"]}");

        assertTrue(selection.declares(NN, CLOCK_CELL));
        assertTrue(selection.declares(NN_TWIN, CLOCK_CELL));
        assertFalse(selection.declares(DN, CLOCK_CELL));
    }

    /** The whole Soot signature is the same declaration as class + method. */
    @Test
    public void theWholeSignatureNamesTheSameSite() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection = read(
                "{\"method\":\"" + UPDATE_SIGNATURE + "\",\"cells\":[\""
                        + CLOCK_CELL + "\"]}");

        assertTrue(selection.declares(NN, CLOCK_CELL));
        assertTrue(selection.declares(NN_TWIN, CLOCK_CELL));
    }

    /** A node scope narrows the same site to the regions planned there. */
    @Test
    public void aNodeScopeNarrowsTheSiteToThatNode() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection = read(
                "{\"class\":\"" + CLASS + "\",\"method\":\"void addKeys()\","
                        + "\"node\":\"dn0\",\"epoch\":\"0\",\"cells\":[\""
                        + CLOCK_CELL + "\"]}");

        assertTrue(selection.declares(DN, CLOCK_CELL));
        assertFalse(selection.declares(NN, CLOCK_CELL));
    }

    /**
     * A site no planned region covers is refused by name.  The campaign asked
     * for a root the plan cannot carry; running on would drop it in silence.
     */
    @Test
    public void aSiteNoRegionCoversIsARefusalNamingTheSite() throws Exception {
        try {
            read("{\"class\":\"" + CLASS + "\",\"method\":\"long absent()\","
                    + "\"cells\":[\"" + CLOCK_CELL + "\"]}");
            fail("a site outside every planned region was admitted");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains("no planned region covers"));
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains("long absent()"));
        }
    }

    /** The region-id form still reads, and asks to be rewritten as a site. */
    @Test
    public void theRegionIdFormIsReadAndAsksForTheSiteForm() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection = read(
                "{\"regionId\":\"" + NN + "\",\"cells\":[\"" + CLOCK_CELL
                        + "\"]}");

        assertTrue(selection.declares(NN, CLOCK_CELL));
        assertFalse(selection.declares(NN_TWIN, CLOCK_CELL));
        List<JsonObject> asked = selection.declarationDiagnostics();
        assertEquals(1, asked.size());
        assertEquals(ConcolicScheduler.REGION_ID_DECLARATION,
                asked.get(0).get("code").getAsString());
        assertEquals(NN, asked.get(0).get("subject").getAsString());
    }

    private ConcolicScheduler.SymbolicInputSelection read(String... rows)
            throws IOException {
        Path path = folder.newFile("symbolic-inputs.jsonl").toPath();
        StringBuilder text = new StringBuilder();
        for (String row : rows) text.append(row).append('\n');
        Files.write(path, text.toString().getBytes(StandardCharsets.UTF_8));
        return ConcolicScheduler.SymbolicInputSelection.read(path, catalog(),
                plans());
    }

    private static List<JsonObject> catalog() {
        List<JsonObject> regions = new ArrayList<>();
        for (String regionId : Arrays.asList(NN, NN_TWIN, DN)) {
            JsonObject region = new JsonObject();
            region.addProperty("regionId", regionId);
            regions.add(region);
        }
        return regions;
    }

    /** Two nn0 regions of one method, and one dn0 region of another. */
    private static List<RegionInstancePlan> plans() {
        return Arrays.asList(
                plan(NN, UPDATE_SIGNATURE, "wl/nn0#epoch0", 1),
                plan(NN_TWIN, UPDATE_SIGNATURE, "wl/nn0#epoch0", 2),
                plan(DN, "<" + CLASS + ": void addKeys()>", "wl/dn0#epoch0",
                        1));
    }

    private static RegionInstancePlan plan(String regionId, String method,
                                           String sourceKey, int occurrence) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "CONCOLIC_REGION_PLAN");
        row.addProperty("regionId", regionId);
        row.addProperty("targetMethod", method);
        row.addProperty("sourceKey", sourceKey);
        row.addProperty("occurrenceId",
                sourceKey + "/region/" + regionId + "#" + occurrence);
        row.addProperty("relationKey", sourceKey + "/relation/" + regionId);
        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", "GOAL." + regionId + "#" + occurrence);
        goal.addProperty("kind", "REGION_PATH_CLOSURE");
        goal.add("runtimeDefinitionMethods", new JsonArray());
        goal.add("branches", new JsonArray());
        goal.add("symbolize", new JsonArray());
        goal.add("sharedCarriers", new JsonArray());
        goal.add("edgeBindingIds", new JsonArray());
        JsonArray goals = new JsonArray();
        goals.add(goal);
        row.add("closureGoals", goals);
        return RegionInstancePlan.decode(row);
    }
}
