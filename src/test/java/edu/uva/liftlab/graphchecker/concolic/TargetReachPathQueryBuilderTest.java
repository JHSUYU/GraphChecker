package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

/** Focused coverage of target worklist-to-activation closure identity. */
public class TargetReachPathQueryBuilderTest {

    @Test
    public void parallelTargetOccurrencesAreScopedBeforeDecision() {
        JsonObject selected = readySeed("source/dn1#epoch0", "target#2",
                "GOAL.dn1.2");
        List<JsonObject> seeds = Arrays.asList(
                readySeed("source/dn0#epoch0", "target#1", "GOAL.dn0.1"),
                readySeed("source/dn0#epoch0", "target#2", "GOAL.dn0.2"),
                readySeed("source/dn1#epoch0", "target#1", "GOAL.dn1.1"),
                selected);
        JsonObject manifest = targetIdentity("target#2");
        manifest.addProperty("sourceKey", "source/dn1#epoch0");
        manifest.addProperty("goalId", "GOAL.dn1.2");

        List<JsonObject> scoped =
                TargetReachPathQueryBuilder.solverReadySeedsForScope(
                        seeds, manifest);

        assertEquals(1, scoped.size());
        assertSame(selected, scoped.get(0));

        JsonObject sameScope = readySeed("source/dn1#epoch0", "target#2",
                "GOAL.dn1.2");
        scoped = TargetReachPathQueryBuilder.solverReadySeedsForScope(
                Arrays.asList(selected, sameScope), manifest);
        assertEquals(2, scoped.size());
    }

    private static JsonObject closedManifest(String occurrence) {
        JsonObject row = targetIdentity(occurrence);
        row.addProperty("state", "CLOSED");
        row.addProperty("coverageState", "CLOSED");
        row.add("gaps", new JsonArray());
        row.add("coverageGaps", new JsonArray());
        return row;
    }

    private static JsonObject targetSummary(String occurrence) {
        return targetIdentity(occurrence);
    }

    private static JsonObject readySeed(String source, String occurrence,
                                        String goal) {
        JsonObject row = targetIdentity(occurrence);
        row.addProperty("sourceKey", source);
        row.addProperty("goalId", goal);
        row.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        row.addProperty("readyForSolver", true);
        return row;
    }

    private static JsonObject targetIdentity(String occurrence) {
        JsonObject row = new JsonObject();
        row.addProperty("sourceKey", "source/dn0#epoch0");
        row.addProperty("regionId", "REGION.target");
        row.addProperty("occurrenceId", occurrence);
        row.addProperty("goalId", "GOAL.target");
        return row;
    }
}
