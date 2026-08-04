package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.file.Path;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class ConcolicSummaryImporterTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void loopBoundCutNeverBecomesComposableRelation()
            throws Exception {
        Path directory = folder.newFolder("cut-import").toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");

        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.CUT");
        task.addProperty("goalId", "GOAL.CUT");
        task.addProperty("regionId", "REGION.CUT");
        task.addProperty("regionInstanceId", "REGION.CUT@test#call1");
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(task);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        LoopBoundPolicy.cfgBackedges(2).writeTo(task);

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.CUT");

        JsonObject cut = new JsonObject();
        cut.addProperty("event", "CONCOLIC_REGION_RESULT");
        cut.addProperty("taskId", "TASK.CUT");
        cut.addProperty("exitKind", "CUT");
        cut.addProperty("exceptionType", "");
        JsonObject pathCut = new JsonObject();
        pathCut.addProperty("kind", "LOOP_BOUND");
        pathCut.addProperty("backedgeId", "<L: void run()>#backedge:u4->u1");
        pathCut.addProperty("maxBackedgeTraversals", 2);
        pathCut.addProperty("attemptedTraversal", 3);
        pathCut.addProperty("reason", "MAX_BACKEDGE_TRAVERSALS_EXCEEDED");
        cut.add("pathCut", pathCut);
        // Even a VM-complete prefix must not be admitted as a relation.
        JsonObject engine = new JsonObject();
        engine.addProperty("complete", true);
        engine.addProperty("aborted", false);
        engine.add("pathCondition", new JsonArray());
        cut.add("engineSummary", engine);
        cut.add("unresolvedInputs", new JsonArray());
        cut.add("branchMappings", new JsonArray());

        ArtifactIO.replaceJsonl(tasks, Collections.singletonList(task));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(cut));

        ConcolicSummaryImporter.ImportResult imported =
                ConcolicSummaryImporter.importSummaries(results, tasks,
                        regions, output, diagnostics);

        assertEquals(1, imported.rawResultCount);
        assertEquals(0, imported.validSummaryCount);
        assertEquals(1, imported.diagnosticCount);
        assertEquals(0, ArtifactIO.readJsonl(output).size());
        List<JsonObject> rejected = ArtifactIO.readJsonl(diagnostics);
        assertEquals("LOOP_BOUND_PATH_CUT",
                rejected.get(0).get("code").getAsString());
    }
}
