package edu.uva.liftlab.graphchecker.d3.plan;


import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.AbstractMap;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * What an experiment's {@code symbolic-inputs.jsonl} governs.
 *
 * <p>TRACK -- symbolize the read so the VM publishes its candidates -- is
 * the default for every carrier.  MINT belongs to three authorities only: a
 * fault marker in the workload's source, a field a hook owns, and a name
 * this file declares.  The file narrows mint, never tracking.</p>
 */
public class SymbolicRootPolicyTest {

    private static final String NN = "REGION.nn";
    private static final String NN_TWIN = "REGION.nn-twin";
    private static final String DN = "REGION.dn";
    private static final String CLOCK_CELL =
            "<org.apache.hadoop.util.Timer: long now()>.return";
    private static final String KEY_ID = "<org.apache.hadoop.security.token"
            + ".delegation.DelegationKey: int keyId>";
    private static final String CLASS = "org.apache.hadoop.hdfs.security"
            + ".token.block.BlockTokenSecretManager";
    private static final String UPDATE_KEYS = "boolean updateKeys()";
    private static final String ROOT = InputActionCatalog
            .DECLARED_SYMBOLIC_ROOT;

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    /**
     * A declared cell is stamped so the replay knows the row was named by hand
     * rather than proposed, while a declared wire-flow cut port hands over a
     * producer expression: it is tracked and mints no root, so refusing it
     * would only cut propagation.
     */
    @Test
    public void theFileGovernsMintAndNeverTracking() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection = read(
                "{\"regionId\":\"" + NN + "\",\"cells\":[\"" + CLOCK_CELL
                        + "\"]}");
        JsonArray selected = selection.select(NN, proposals());

        assertTrue("the declared clock carries the mint marker",
                selected.get(0).getAsJsonObject().get(ROOT).getAsBoolean());
        assertFalse("a tracked carrier never carries it",
                selected.get(1).getAsJsonObject().has(ROOT));
        assertFalse("nor does the exempt fault marker, whose mint the "
                        + "runtime finds by sourceKind",
                selected.get(2).getAsJsonObject().has(ROOT));
        JsonArray actions = proposals();
        actions.add(action("COMMUNICATION_SITE_PORT", "<C: int getKeyId()>#u2",
                "<C: int getKeyId()>.return"));
        JsonObject cut = selection.select(DN, actions).get(3).getAsJsonObject();
        assertEquals("SYMBOLIC", cut.get("mode").getAsString());
        assertFalse(cut.get("mintEligible").getAsBoolean());

        // A declaration names a VALUE, and the graph names one value once
        // per local it is copied into: the case knows the accessor's own
        // return cell, while the port that materializes it names the local
        // the value lands in.  Soot proves which edges are exact copies, so
        // following only those renames the declaration onto the port --
        // which is how hdfs-17960's declared region input stops matching
        // nothing.
        JsonObject accessorPort = accessorPort();
        assertTrue("the proven rename selects the port",
                renamed(exactCopy()).select(NN, actions(accessorPort))
                        .get(0).getAsJsonObject().get(ROOT).getAsBoolean());
        assertFalse("an edge Soot did not prove a copy is not a rename",
                renamed(plainCopy()).select(NN, actions(accessorPort))
                        .get(0).getAsJsonObject().has(ROOT));
    }

    /** The accessor's return cell, as a case declares a manual read. */
    private static final String ACCESSOR_RETURN =
            "<S: int getNumSnapshots()>.return";
    /** The local the accessor copies it into, which the port names. */
    private static final String ACCESSOR_LOCAL =
            "<S: int getNumSnapshots()>::$i0";

    /** One declaration of {@link #ACCESSOR_RETURN}, seeded over one graph. */
    private ConcolicScheduler.SymbolicInputSelection renamed(JsonObject edge)
            throws IOException {
        ConcolicScheduler.SymbolicInputSelection selection = read(
                "{\"regionId\":\"" + NN + "\",\"cells\":[\""
                        + ACCESSOR_RETURN + "\"]}");
        selection.seedCarrierSlice(Collections.singletonList(edge),
                Collections.<Map.Entry<String, JsonArray>>singletonList(
                        new AbstractMap.SimpleImmutableEntry<>(NN,
                                actions(accessorPort()))));
        return selection;
    }

    private static JsonArray actions(JsonObject action) {
        JsonArray actions = new JsonArray();
        actions.add(action.deepCopy());
        return actions;
    }

    /** The accessor-return port: its cell is the Atomic's value leaf. */
    private static JsonObject accessorPort() {
        JsonObject port = action("ACCESSOR_RETURN",
                "<S: int getNumSnapshots()>#u2",
                "<java.util.concurrent.atomic.AtomicInteger: int value>");
        port.addProperty("accessFieldSignature",
                "<java.util.concurrent.atomic.AtomicInteger: int value>");
        JsonArray cells = new JsonArray();
        cells.add(ACCESSOR_LOCAL);
        port.add("dependencyCells", cells);
        return port;
    }

    private static JsonObject exactCopy() {
        JsonObject edge = plainCopy();
        edge.addProperty("valueFlowAuthority",
                "SOOT_EXACT_LOCAL_DIRECT_COPY_V1");
        return edge;
    }

    private static JsonObject plainCopy() {
        return json("{\"kind\":\"local_def_use\",\"transferKind\":"
                + "\"VALUE_PASS\",\"fromCell\":\"" + ACCESSOR_LOCAL
                + "\",\"toCell\":\"" + ACCESSOR_RETURN + "\"}");
    }

    /**
     * A manual root is declared by the site it is read at, not by a region hash.
     *
     * <p>A region id moves whenever the retained selection moves; a static
     * site is what the experiment knows, and the plan resolves it to the
     * regions covering it -- one method planned twice is two regions, and
     * both mean it.</p>
     */
    @Test
    public void aManualRootIsDeclaredByItsSite() throws Exception {
        declaresAt("\"class\":\"" + CLASS + "\",\"method\":\"" + UPDATE_KEYS
                + "\"", Arrays.asList(NN, NN_TWIN), Arrays.asList(DN));
        // a node scope narrows the same site to the regions planned there
        declaresAt("\"class\":\"" + CLASS + "\",\"method\":\"void addKeys()\","
                        + "\"node\":\"dn0\",\"epoch\":\"0\"",
                Arrays.asList(DN), Arrays.asList(NN, NN_TWIN));

        // A site no planned region covers is refused by name: the campaign
        // asked for a root the plan cannot carry, and running on would drop it.
        try {
            read("{\"class\":\"" + CLASS + "\",\"method\":\"long absent()\","
                    + "\"cells\":[\"" + CLOCK_CELL + "\"]}");
            fail("a site outside every planned region was admitted");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains("no planned region covers"));
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains("long absent()"));
        }
    }

    /** One site declaration, and the regions it must and must not reach. */
    private void declaresAt(String site, List<String> declaring,
            List<String> silent) throws IOException {
        ConcolicScheduler.SymbolicInputSelection selection =
                read("{" + site + ",\"cells\":[\"" + CLOCK_CELL + "\"]}");
        for (String id : declaring) assertTrue(site, selection.declares(id, CLOCK_CELL));
        for (String id : silent) assertFalse(site, selection.declares(id, CLOCK_CELL));
    }

    /** One declaration row, written where the campaign would put the file. */
    private ConcolicScheduler.SymbolicInputSelection read(String row)
            throws IOException {
        Path path = folder.newFolder().toPath().resolve("symbolic-inputs.jsonl");
        Files.write(path, (row + "\n").getBytes(StandardCharsets.UTF_8));
        return ConcolicScheduler.SymbolicInputSelection.read(path,
                Arrays.asList(json("{\"regionId\":\"" + NN + "\"}"),
                        json("{\"regionId\":\"" + NN_TWIN + "\"}"),
                        json("{\"regionId\":\"" + DN + "\"}")), plans());
    }

    /** Two nn0 regions of one method, and one dn0 region of another. */
    private static List<RegionInstancePlan> plans() {
        String updateKeys = "<" + CLASS + ": " + UPDATE_KEYS + ">";
        return Arrays.asList(plan(NN, updateKeys, "wl/nn0#epoch0", 1),
                plan(NN_TWIN, updateKeys, "wl/nn0#epoch0", 2),
                plan(DN, "<" + CLASS + ": void addKeys()>", "wl/dn0#epoch0", 1));
    }

    private static RegionInstancePlan plan(String regionId, String method,
            String key, int occurrence) {
        String id = key + "/region/" + regionId + "#" + occurrence;
        return RegionInstancePlan.decode(json("{\"regionId\":\"" + regionId
                + "\",\"targetMethod\":\"" + method + "\",\"sourceKey\":\""
                + key + "\",\"occurrenceId\":\"" + id + "\",\"relationKey\":\""
                + key + "/relation/" + regionId + "\",\"closureGoals\":[{"
                + "\"goalId\":\"GOAL." + id + "\",\"kind\":"
                + "\"REGION_PATH_CLOSURE\",\"runtimeDefinitionMethods\":[]}]}"));
    }

    /** One automatic clock return, one accessor field, one fault marker. */
    private static JsonArray proposals() {
        JsonArray actions = new JsonArray();
        JsonObject clock = action("EXTERNAL_CALL_RETURN",
                "<C: void removeExpiredKeys()>#u2", CLOCK_CELL);
        clock.addProperty("declaredCallee", "<org.apache.hadoop.util.Timer: long now()>");
        actions.add(clock);
        JsonObject field = action("ACCESSOR_RETURN", "<C: boolean f()>#u9", KEY_ID);
        field.addProperty("accessFieldSignature", KEY_ID);
        actions.add(field);
        actions.add(action("EXPLICIT_SYMBOLIC_FAULT",
                "<C: void sendRpcRequest(D)>#u17",
                "<C: void sendRpcRequest(D)>::$z5"));
        return actions;
    }

    private static JsonObject action(String sourceKind, String siteId,
            String cell) {
        return json("{\"mode\":\"SYMBOLIC\",\"sourceKind\":\"" + sourceKind
                + "\",\"siteId\":\"" + siteId + "\",\"portId\":\"port."
                + siteId + "\",\"symbol\":\"port." + siteId + "\",\"cell\":\""
                + cell + "\"}");
    }

    private static JsonObject json(String row) {
        return JsonParser.parseString(row).getAsJsonObject();
    }
}
