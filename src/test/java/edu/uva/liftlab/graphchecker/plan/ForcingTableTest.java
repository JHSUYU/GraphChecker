package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import edu.uva.liftlab.graphchecker.causynth.JimpleScene;
import edu.uva.liftlab.graphchecker.causynth.SiteControlDependence;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.G;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.Map;

import static org.junit.Assert.assertEquals;

public class ForcingTableTest {
    private static final String M = "<a.T: void check(int)>";
    private static final String H = "<a.T: boolean expired()>";
    private static final String N = "<a.T: int age()>";
    private static final String CALLER = "<a.T: void run(int)>";
    private static final String X = "<a.T: boolean aged()>";

    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    @Test
    public void theTableNamesTheArmOfEveryBranchOnTheWayToTheThrow()
            throws IOException {
        String row = "{\"schemaVersion\":1,\"kind\":\"STATIC_SCOPE_SITE\","
                + "\"role\":\"TARGET_SITE\",\"regionId\":\"R\","
                + "\"siteId\":\"" + M + "#u9\",\"vmSite\":\"\","
                + "\"cell\":\"\",\"carrier\":\"\",\"portId\":\"\","
                + "\"guards\":[\"" + M + "#u8\",\"" + M + "#u5\"],"
                + "\"guardOutcomes\":[false,null],"
                + "\"guardDeciders\":{\"" + M + "#u8\":["
                + "{\"siteId\":\"" + H + "#u1\",\"outcome\":true,"
                + "\"verdict\":true,\"via\":\"" + M + "\"},"
                + "{\"siteId\":\"" + H + "#u1\",\"outcome\":false,"
                + "\"via\":\"" + M + "\","
                + "\"deciders\":[{\"siteId\":\"" + N + "#u2\","
                + "\"outcome\":true,\"verdict\":false,\"via\":\"" + X
                + "\"},{\"siteId\":\"" + N + "#u2\",\"outcome\":false,"
                + "\"via\":\"" + X + "\"}]}]},"
                + "\"chain\":[{\"siteId\":\"" + M + "#u3\",\"outcome\":null},"
                + "{\"siteId\":\"" + CALLER + "#u4\",\"outcome\":true}]}";
        StaticScopeMap.Site target = read(row).targetSites().get(0);
        Map<String, ForcingTable.Arm> table = ForcingTable.read(
                ForcingTable.of(target, Collections.<String>emptySet()));
        Object[][] rows = {
                {"the guard, at its fatal arm", M + "#u8", "=false"},
                {"the helper's decider at the arm whose verdict the guard "
                        + "wants (false: expired() returns false)",
                        H + "#u1", "=false via " + M},
                {"under that open arm, the nested decider at the arm whose "
                        + "verdict it wants; its other arm is open, so "
                        + "neither leaves the way: passable; via as SEED "
                        + "stated it (its helper is called from X, not from "
                        + "H, whose branch it decides)", N + "#u2",
                        "=true via " + X + " passable"},
                {"a chain switch: never forced", M + "#u3", null},
                {"a caller's chain guard", CALLER + "#u4", "=true"},
                {"a fault call: no arm to force", M + "#u5", null}};
        for (Object[] expected : rows) {
            ForcingTable.Arm arm = table.get((String) expected[1]);
            assertEquals((String) expected[0], expected[2], arm == null ? null
                    : arm.toString().substring(((String) expected[1])
                    .length()));
        }
        assertEquals("one arm per site", 4, table.size());

        JsonArray force = ForcingTable.of(target,
                Collections.<String>emptySet());
        assertEquals(force, read(row.substring(0, row.length() - 1)
                + ",\"force\":" + force + "}").forcing(M + "#u9"));
        assertEquals("no target, no table", new JsonArray(),
                StaticScopeMap.empty().forcing(M + "#u9"));
    }

    private static String target(String site, String guard, String force) {
        return "{\"schemaVersion\":1,\"kind\":\"STATIC_SCOPE_SITE\","
                + "\"role\":\"TARGET_SITE\",\"regionId\":\"R\","
                + "\"siteId\":\"" + site + "\",\"vmSite\":\"\","
                + "\"cell\":\"\",\"carrier\":\"\",\"portId\":\"\","
                + "\"guards\":[\"" + guard + "\"],\"guardOutcomes\":[true],"
                + "\"force\":" + force + "}";
    }

    @Test
    public void aBranchBothOfWhoseArmsReachTheThrowIsNeverForced()
            throws IOException {
        String check = "<a.A: void check(int)>";
        String thrown = check + "#u7";
        try {
            assertBody();
            StaticScopeMap.Site target = read("{\"schemaVersion\":1,"
                    + "\"kind\":\"STATIC_SCOPE_SITE\","
                    + "\"role\":\"TARGET_SITE\",\"regionId\":\"R\","
                    + "\"siteId\":\"" + thrown + "\",\"vmSite\":\"\","
                    + "\"cell\":\"\",\"carrier\":\"\",\"portId\":\"\"}")
                    .targetSites().get(0);
            JsonArray force = StaticScopeMap.rows(
                    Collections.singletonList(target),
                    SiteControlDependence.over(Collections.singleton(thrown)),
                    method -> false).get(0).getAsJsonArray("force");
            Map<String, ForcingTable.Arm> table = ForcingTable.read(force);
            Object[][] rows = {
                    {"$assertionsDisabled: both arms reach the throw",
                            check + "#u2", "=true passable"},
                    {"the assert's own test: its other arm returns",
                            check + "#u3", "=true"},
                    {"the throw's own first test: its healthy arm reaches"
                            + " the throw through u6", check + "#u5",
                            "=true passable"},
                    {"the throw's other guard, at its fatal arm",
                            check + "#u6", "=false"}};
            for (Object[] expected : rows) {
                ForcingTable.Arm arm = table.get((String) expected[1]);
                assertEquals((String) expected[0], expected[2], arm == null
                        ? null : arm.toString().substring(
                        ((String) expected[1]).length()));
            }
            assertEquals("a passable branch is no forced site",
                    new java.util.LinkedHashSet<String>(Arrays.asList(
                            check + "#u6", check + "#u3")),
                    read("{\"schemaVersion\":1,\"kind\":\"STATIC_SCOPE_SITE\","
                            + "\"role\":\"TARGET_SITE\",\"regionId\":\"R\","
                            + "\"siteId\":\"" + thrown + "\",\"vmSite\":\"\","
                            + "\"cell\":\"\",\"carrier\":\"\",\"portId\":\"\","
                            + "\"force\":" + force + "}").forcedSites());
        } finally {
            G.reset();
        }
    }

    private static void assertBody() {
        JimpleScene.load("application public class a.A { static final"
                + " boolean $assertionsDisabled; public void check(int) {"
                + " int i0; boolean z0; a.X r1; i0 := @parameter0: int;"
                + " z0 = <a.A: boolean $assertionsDisabled>;"
                + " if z0 != 0 goto label1; if i0 != 0 goto label1; return;"
                + " label1: if i0 > 5 goto label2; if i0 >= -5 goto label3;"
                + " label2: r1 = new a.X; throw r1; label3: return; } }");
    }

    private StaticScopeMap read(String row) throws IOException {
        Path file = tree.newFile().toPath();
        Files.write(file, (row + "\n").getBytes(StandardCharsets.UTF_8));
        return StaticScopeMap.read(file);
    }
}
