package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;

/**
 * A batch's plans grouped into seed replays: a target joins the first group
 * whose union it agrees with, occurrence by occurrence and observed site by
 * observed site; a group's union is every task once, every task observing
 * every site, under one replay group.
 */
public class PlanUnionTest {
    /** Per target: its tasks as "taskId@occurrence" and its observed sites
     *  as "site:cell"; then the groups expected. */
    @Test
    public void targetsJoinTheFirstGroupTheyAgreeWith() {
        Object[][] targets = {
                {"a", new String[]{"T1@o1", "T2@o2"}, new String[]{"s1:c1"}},
                {"b", new String[]{"T1@o1", "T3@o3"},
                        new String[]{"s1:c1", "s2:c2"}},
                // Another task at o1: a replay of its own.
                {"c", new String[]{"T4@o1"}, new String[]{}},
                // s1 observed otherwise than the first group does.
                {"d", new String[]{"T5@o5"}, new String[]{"s1:c9"}},
        };
        Map<String, List<JsonObject>> plans =
                new LinkedHashMap<String, List<JsonObject>>();
        for (Object[] target : targets) {
            plans.put((String) target[0],
                    plan((String[]) target[1], (String[]) target[2]));
        }
        List<PlanUnion.Group> groups = PlanUnion.groups(plans);
        Object[][] expected = {
                {Arrays.asList("a", "b"), Arrays.asList("T1", "T2", "T3"),
                        Arrays.asList("c1", "c2")},
                {Arrays.asList("c", "d"), Arrays.asList("T4", "T5"),
                        Arrays.asList("c9")},
        };
        assertEquals(expected.length, groups.size());
        for (int index = 0; index < expected.length; index++) {
            PlanUnion.Group group = groups.get(index);
            assertEquals(expected[index][0], group.targets);
            List<String> ids = new ArrayList<String>();
            Set<String> ledgers = new LinkedHashSet<String>();
            for (JsonObject row : group.rows()) {
                ids.add(row.get("taskId").getAsString());
                ledgers.add(row.get(ConcolicScheduler.REPLAY_GROUP_ID)
                        .getAsString());
                List<String> cells = new ArrayList<String>();
                for (com.google.gson.JsonElement site
                        : row.getAsJsonArray(ExecutionTask.OBSERVED_SITES)) {
                    cells.add(site.getAsJsonObject().get("cell").getAsString());
                }
                assertEquals("every task observes every site of its group",
                        expected[index][2], cells);
            }
            assertEquals(expected[index][1], ids);
            assertEquals("one replay group per union", 1, ledgers.size());
        }
    }

    private static List<JsonObject> plan(String[] tasks, String[] sites) {
        JsonArray observed = new JsonArray();
        for (String site : sites) {
            JsonObject row = new JsonObject();
            row.addProperty("siteId", site.split(":")[0]);
            row.addProperty("cell", site.split(":")[1]);
            observed.add(row);
        }
        List<JsonObject> rows = new ArrayList<JsonObject>();
        for (String task : tasks) {
            JsonObject row = new JsonObject();
            row.addProperty("taskId", task.split("@")[0]);
            row.addProperty("occurrenceId", task.split("@")[1]);
            row.addProperty(ConcolicScheduler.REPLAY_GROUP_ID, "own");
            row.add(ExecutionTask.OBSERVED_SITES, observed.deepCopy());
            rows.add(row);
        }
        return rows;
    }
}
