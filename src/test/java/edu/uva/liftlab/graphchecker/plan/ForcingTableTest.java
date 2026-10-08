package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonParser;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;

/**
 * The declared throw's forcing table (PIPELINE §2): each guard at its fatal
 * arm, each chain guard at its arm toward the guard it controls, a helper's
 * deciding arm whose verdict the guard wants (else its open arm, nested
 * deciders alike, each with the method that calls its helper), a switch
 * guard at the case the throw is reachable from; a fault call (no arm, no
 * case) is not forced.  SEED writes it on the TARGET_SITE row and the map
 * reads it back whole.
 */
public class ForcingTableTest {
    private static final String M = "<a.T: void check(int)>";
    private static final String H = "<a.T: boolean expired()>";
    private static final String N = "<a.T: int age()>";
    private static final String CALLER = "<a.T: void run(int)>";

    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    @Test
    public void theTableNamesTheArmOfEveryBranchOnTheWayToTheThrow()
            throws IOException {
        // check: u3 a switch (case 7 reaches the throw), u5 a fault call,
        // u8 `if (!expired())` deciding the throw at u9; expired(): u1 tests
        // age(), whose u2 decides; run: u4 calls check.
        String row = "{\"schemaVersion\":1,\"kind\":\"STATIC_SCOPE_SITE\","
                + "\"role\":\"TARGET_SITE\",\"regionId\":\"R\","
                + "\"siteId\":\"" + M + "#u9\",\"vmSite\":\"\","
                + "\"cell\":\"\",\"carrier\":\"\",\"portId\":\"\","
                + "\"guards\":[\"" + M + "#u8\",\"" + M + "#u5\"],"
                + "\"guardOutcomes\":[false,null],"
                + "\"guardDeciders\":{\"" + M + "#u8\":["
                + "{\"siteId\":\"" + H + "#u1\",\"outcome\":true,"
                + "\"verdict\":true},"
                + "{\"siteId\":\"" + H + "#u1\",\"outcome\":false,"
                + "\"deciders\":[{\"siteId\":\"" + N + "#u2\","
                + "\"outcome\":true,\"verdict\":false},{\"siteId\":\""
                + N + "#u2\",\"outcome\":false}]}]},"
                + "\"chain\":[{\"siteId\":\"" + M + "#u3\",\"outcome\":null},"
                + "{\"siteId\":\"" + CALLER + "#u4\",\"outcome\":true}]}";
        StaticScopeMap.Site target = read(row).targetSites().get(0);
        StaticScopeMap.Guards switches = new StaticScopeMap.Guards() {
            @Override
            public List<StaticScopeMap.Guard> of(String siteId) {
                return Collections.emptyList();
            }

            @Override
            public String switchCase(String switchSiteId, String siteId) {
                return (M + "#u3").equals(switchSiteId) ? "7" : null;
            }
        };
        Map<String, ForcingTable.Arm> table = ForcingTable.read(
                ForcingTable.of(target, switches));
        Object[][] rows = {
                {"the guard, at its fatal arm", M + "#u8", "=false"},
                {"the helper's decider at the arm whose verdict the guard "
                        + "wants (false: expired() returns false)",
                        H + "#u1", "=false via " + M},
                {"under that open arm, the nested decider at the arm whose "
                        + "verdict it wants", N + "#u2", "=true via " + H},
                {"a chain switch: the case the throw is reachable from",
                        M + "#u3", " case 7"},
                {"a caller's chain guard", CALLER + "#u4", "=true"},
                {"a fault call: no arm to force", M + "#u5", null}};
        for (Object[] expected : rows) {
            ForcingTable.Arm arm = table.get((String) expected[1]);
            assertEquals((String) expected[0], expected[2], arm == null ? null
                    : arm.toString().substring(((String) expected[1])
                    .length()));
        }
        assertEquals("one arm per site", 5, table.size());

        // Stated on the row, read back by the map whole.
        JsonArray force = ForcingTable.of(target, switches);
        assertEquals(force, read(row.substring(0, row.length() - 1)
                + ",\"force\":" + force + "}").forcing());
        assertEquals("no target, no table", new JsonArray(),
                StaticScopeMap.empty().forcing());
    }

    /** An occurrence that entered the throw's method is forced by its own
     *  branches and the deciders only; one that never did, by its callers'
     *  guards too. */
    @Test
    public void anOccurrenceInsideTheThrowsMethodLeavesItsCallersGuards() {
        JsonArray table = JsonParser.parseString("[{\"siteId\":\"" + M
                + "#u8\",\"arm\":false},{\"siteId\":\"" + CALLER
                + "#u4\",\"arm\":true},{\"siteId\":\"" + H
                + "#u1\",\"arm\":false,\"via\":\"" + M + "\"}]")
                .getAsJsonArray();
        Set<String> throwing = Collections.singleton(M);
        Object[][] rows = {
                {"it decided a branch of the throw's method",
                        Collections.singleton(M + "#u3"), 2},
                {"it never entered it", Collections.singleton(
                        CALLER + "#u2"), 3},
                {"it decided nothing", Collections.<String>emptySet(), 3}};
        for (Object[] row : rows) {
            @SuppressWarnings("unchecked")
            Set<String> observed = (Set<String>) row[1];
            Map<String, ForcingTable.Arm> kept = ForcingTable.read(
                    ForcingTable.forOccurrence(table, throwing, observed));
            assertEquals((String) row[0], row[2], kept.size());
            assertEquals((String) row[0], (Integer) row[2] == 3,
                    kept.containsKey(CALLER + "#u4"));
        }
    }

    @Test
    public void aTableIsReadByItsKindOfArm() {
        JsonArray json = JsonParser.parseString("[{\"siteId\":\"a#u1\","
                + "\"arm\":true},{\"siteId\":\"a#u2\",\"case\":-3},"
                + "{\"siteId\":\"a#u3\",\"default\":true,\"via\":\"<m>\"},"
                + "{\"siteId\":\"a#u1\",\"arm\":false},{\"siteId\":\"\"},"
                + "{\"siteId\":\"a#u4\"}]").getAsJsonArray();
        Map<String, ForcingTable.Arm> table = ForcingTable.read(json);
        Object[][] rows = {
                {"a#u1", ForcingTable.ARM, 1, ""},
                {"a#u2", ForcingTable.CASE, -3, ""},
                {"a#u3", ForcingTable.DEFAULT, 0, "<m>"}};
        for (Object[] row : rows) {
            ForcingTable.Arm arm = table.get((String) row[0]);
            assertEquals((String) row[0] + " kind", row[1], arm.kind);
            assertEquals((String) row[0] + " value", row[2], arm.value);
            assertEquals((String) row[0] + " via", row[3], arm.via);
        }
        assertEquals("the first arm of a site, none without an arm", 3,
                table.size());
    }

    private StaticScopeMap read(String row) throws IOException {
        Path file = tree.newFile().toPath();
        Files.write(file, (row + "\n").getBytes(StandardCharsets.UTF_8));
        return StaticScopeMap.read(file);
    }
}
