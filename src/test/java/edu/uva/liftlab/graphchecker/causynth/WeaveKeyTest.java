package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

/**
 * GROW weaves a generation only where its plan's weave key is not its tree's
 * (run_engine.sh campaign_stream_grow): the key is what the weave reads of a
 * plan -- the tasks' instrumentation values, a repeated one once -- and
 * nothing per occurrence.
 */
public class WeaveKeyTest {
    private static final String ROOT =
            "<a.Queue: java.util.List peekElements(int)>";
    private static final String BRANCHES = "<a.Queue: boolean ready()>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @After
    public void clearPlan() {
        System.clearProperty("causynth.concolic.task.plan");
        System.clearProperty("causynth.concolic.task.id");
        System.clearProperty("causynth.concolic.campaign.max.tasks");
    }

    /**
     * SGF8-adhoc-19 g4-g11: more planned occurrences of a region whose hook
     * the plan holds, a grown input at a hook it holds, a doors-only mark
     * dropped -- the tree woven before; a new branch method, a new region or
     * a new local is a new tree.
     */
    @Test
    public void theKeyIsWhatTheWeaveReads() throws IOException {
        JsonObject first = row("T.1", "R#62", BRANCHES, "$z0", 12);
        String held = key(first);
        assertEquals("another occurrence of the region, under its own task, "
                        + "goal and input symbol",
                held, key(first, row("T.2", "R#67", BRANCHES, "$z0", 12)));
        JsonObject marked = row("T.2", "R#67", BRANCHES, "$z0", 12);
        marked.addProperty("doorsOnly", true);
        assertEquals("a doors-only mark is no weave", key(first, marked),
                key(first, row("T.2", "R#67", BRANCHES, "$z0", 12)));
        assertNotEquals("a branch method more",
                held, key(first, row("T.2", "R#67",
                        "<a.Queue: boolean empty()>", "$z0", 12)));
        assertNotEquals("a local more", held,
                key(first, row("T.2", "R#67", BRANCHES, "$z1", 12)));
        JsonObject other = row("T.2", "S#1", BRANCHES, "$z0", 12);
        other.addProperty("regionId", "S");
        assertNotEquals("a region more: a root hook group more",
                held, key(first, other));
    }

    private String key(JsonObject... rows) throws IOException {
        Path plan = folder.newFile().toPath();
        List<String> lines = new ArrayList<>();
        List<String> ids = new ArrayList<>();
        for (JsonObject row : rows) {
            lines.add(row.toString());
            ids.add(row.get("taskId").getAsString());
        }
        Files.write(plan, lines, StandardCharsets.UTF_8);
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id",
                String.join(",", ids));
        System.setProperty("causynth.concolic.campaign.max.tasks", "8");
        return ConcolicInstrumentationSelections.weaveKeyFromEnvironment();
    }

    /** A task of region R rooted at {@link #ROOT}, its occurrence {@code
     *  occurrence}, one symbolic input at {@code local}'s definition. */
    private static JsonObject row(String task, String occurrence,
                                  String branchMethod, String local,
                                  int unit) {
        JsonObject row = new JsonObject();
        row.addProperty("sourceKey", "nn0");
        row.addProperty("occurrenceId", "nn0/region/R/" + occurrence);
        row.addProperty("relationKey", "nn0/relation/R");
        row.addProperty("regionId", "R");
        row.addProperty("taskId", task);
        row.addProperty("goalId", "GOAL." + task);
        JsonObject selector = new JsonObject();
        selector.addProperty("method", ROOT);
        selector.addProperty("invocationOrdinal", occurrence.hashCode());
        row.add("rootSelector", selector);
        row.addProperty("targetMethod", ROOT);
        JsonArray branches = new JsonArray();
        branches.add(branchMethod);
        row.add("branchMethods", branches);
        JsonObject input = new JsonObject();
        input.addProperty("mode", "SYMBOLIC");
        input.addProperty("symbol", "R.in." + occurrence);
        input.addProperty("occurrenceId", "nn0/region/R/" + occurrence);
        input.addProperty("bindingMode", "LOCAL_DEFINITION");
        input.addProperty("method", ROOT);
        input.addProperty("local", local);
        JsonObject site = new JsonObject();
        site.addProperty("unitIndex", unit);
        JsonArray sites = new JsonArray();
        sites.add(site);
        input.add("definitionSites", sites);
        JsonArray inputs = new JsonArray();
        inputs.add(input);
        row.add("inputActions", inputs);
        JsonObject bound = new JsonObject();
        bound.addProperty("schemaVersion", 1);
        bound.addProperty("defaultBackedgeTraversals", 8);
        row.add("loopBound", bound);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        row.add("admission", admission);
        return row;
    }
}
