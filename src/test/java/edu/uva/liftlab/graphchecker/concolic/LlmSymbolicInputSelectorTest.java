package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class LlmSymbolicInputSelectorTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void keepsOnlyTheValidatedCandidateSubset() throws Exception {
        File command = selector("valid-selector.sh",
                "jq '{schemaVersion:1, "
                        + "kind:\"GRAPH_CHECKER_SYMBOLIC_INPUT_SELECTION_RESPONSE\", "
                        + "decisionId:.decisionId, "
                        + "candidateSetSha256:.candidateSetSha256, "
                        + "selectedCandidateIds:[.candidates[] | "
                        + "select(.symbol == \"keep\") | .candidateId], "
                        + "rationale:\"minimal\"}'\n");
        LlmSymbolicInputSelector selector = new LlmSymbolicInputSelector(
                command.toPath(), null, true, 5000L);

        JsonArray selected = selector.select(goal(), new JsonArray(),
                actions());

        assertEquals("SYMBOLIC", mode(selected, "keep"));
        assertEquals("CONCRETE", mode(selected, "drop"));
        assertEquals(1, selector.auditRows().size());
        assertEquals("SELECTED", selector.auditRows().get(0)
                .get("status").getAsString());
    }

    @Test
    public void requiredModeRejectsAnUnknownCandidate() throws Exception {
        File command = selector("invalid-selector.sh",
                "jq '{schemaVersion:1, "
                        + "kind:\"GRAPH_CHECKER_SYMBOLIC_INPUT_SELECTION_RESPONSE\", "
                        + "decisionId:.decisionId, "
                        + "candidateSetSha256:.candidateSetSha256, "
                        + "selectedCandidateIds:[\"unknown\"], "
                        + "rationale:\"invalid\"}'\n");
        LlmSymbolicInputSelector selector = new LlmSymbolicInputSelector(
                command.toPath(), null, true, 5000L);
        try {
            selector.select(goal(), new JsonArray(), actions());
            fail("required selector must reject an unknown candidate");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "LLM symbolic input selection failed"));
        }
    }

    private File selector(String name, String body) throws Exception {
        File file = folder.newFile(name);
        Files.write(file.toPath(), ("#!/usr/bin/env bash\nset -euo pipefail\n"
                + body).getBytes(StandardCharsets.UTF_8));
        assertTrue(file.setExecutable(true));
        return file;
    }

    private static JsonObject goal() {
        JsonObject goal = new JsonObject();
        goal.addProperty("selectionRole", "TARGET_REACH");
        goal.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        goal.addProperty("regionId", "REGION.test");
        goal.addProperty("goalId", "GOAL.test");
        return goal;
    }

    private static JsonArray actions() {
        JsonArray result = new JsonArray();
        result.add(action("keep"));
        result.add(action("drop"));
        return result;
    }

    private static JsonObject action(String symbol) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("location", "ARGUMENT");
        action.addProperty("bindingMode", "ROOT_ENTRY");
        action.addProperty("cell", "<T: void f(boolean)>.param0:boolean");
        action.addProperty("javaType", "boolean");
        action.addProperty("sourceKind", "PARAMETER");
        action.addProperty("dependencyRole", "VALUE_FRONTIER");
        action.addProperty("symbolicDemand",
                "EXACT_EXPLORED_GUARD_DEPENDENCE");
        return action;
    }

    private static String mode(JsonArray actions, String symbol) {
        for (JsonElement element : actions) {
            JsonObject action = element.getAsJsonObject();
            if (symbol.equals(action.get("symbol").getAsString())) {
                return action.get("mode").getAsString();
            }
        }
        return "";
    }
}
