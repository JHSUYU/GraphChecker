package edu.uva.liftlab.graphchecker.d3.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.Obligation;
import edu.uva.liftlab.graphchecker.d3.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.Verdict;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

/**
 * ONE obligation: build its query, solve it, say what the replay must apply.
 *
 * <pre>
 *   --obligations &lt;file&gt;      the wave's obligations.jsonl
 *   --obligation-id &lt;id&gt;      which row of it this worker owns
 *   --sessions &lt;dir&gt;          the corpus every wave so far has written
 *   --output-dir &lt;dir&gt;        obligation_result.jsonl, obligation.jsonl,
 *                             obligation_query.smt2, execution_task_plan.jsonl
 *   --root-domains &lt;file&gt;     what the CASE says each root may be: the same
 *                             declaration the wave was planned under
 *   --z3 &lt;path&gt; --solver-timeout-ms &lt;n&gt; --clock-skew-ms &lt;n|unbounded&gt;
 * </pre>
 *
 * <p>One process per obligation: a solve is what an obligation costs before
 * any replay runs, and the wave's queries are independent, so the campaign
 * runs as many as it has workers.  The verdict is this worker's output, and
 * it is always written -- UNSAT and NOT_ADMITTED are recorded terminal
 * outcomes the next wave reads, never a failure of the run.</p>
 */
public final class ObligationSolverMain {
    private ObligationSolverMain() {
    }

    public static void main(String[] argv) throws Exception {
        Map<String, String> options = ExploreMain.options(argv);
        Path obligations = ExploreMain.path(options, "obligations");
        String obligationId = ExploreMain.value(options, "obligation-id", "");
        Path sessions = ExploreMain.path(options, "sessions");
        Path out = ExploreMain.path(options, "output-dir");
        if (obligations == null || obligationId.isEmpty() || sessions == null
                || out == null) {
            throw new IllegalArgumentException("--obligations, "
                    + "--obligation-id, --sessions and --output-dir are "
                    + "required");
        }
        Path iteration = sessions.getParent();
        JsonObject result = solve(iteration,
                ExploreMain.path(options, "root-domains"), obligations,
                obligationId, out,
                Paths.get(ExploreMain.value(options, "z3", "z3")),
                ExploreMain.number(options, "solver-timeout-ms",
                        ObligationFactory.DEFAULT_TIMEOUT_MILLIS));
        System.out.println(ExploreMain.pretty(result));
    }

    /** Solves one published obligation and writes every artifact of it. */
    public static JsonObject solve(Path iteration, Path rootDomains,
                                   Path obligations, String obligationId,
                                   Path out, Path z3, long timeoutMillis)
            throws IOException {
        Files.createDirectories(out);
        Obligation proposal = null;
        for (Obligation row : RowCodec.readAll(obligations,
                ExploreCodec::readObligation)) {
            if (row.obligationId().equals(obligationId)) proposal = row;
        }
        if (proposal == null) {
            throw new IOException("the wave has no obligation " + obligationId
                    + ": " + obligations);
        }
        Corpus corpus = Corpus.read(iteration, rootDomains);
        ObligationFactory.Candidate candidate =
                ObligationFactory.locate(corpus, proposal);
        if (candidate == null) {
            // The corpus no longer states the path this obligation was cut
            // from.  That is this obligation's own admission gap, recorded
            // as its verdict, and nothing about any other task.
            return publish(out, proposal, ObligationResult.of(obligationId,
                            Verdict.NOT_ADMITTED, "",
                            "no session of this corpus still states path "
                                    + proposal.pathId() + " of task "
                                    + proposal.taskId()), "",
                    Collections.singletonList(GapRow.of(ExploreCodec.EXPLORATION,
                            GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                            obligationId, "the obligation names a path the "
                                    + "corpus does not hold")));
        }
        ObligationFactory.Outcome outcome = ObligationFactory.solve(corpus,
                candidate, z3, timeoutMillis);
        return publish(out, outcome.issued() ? outcome.obligation : proposal,
                outcome.result, outcome.smt2, outcome.gaps);
    }

    /**
     * Writes the worker's artifacts: the verdict row the campaign reads, the
     * completed obligation, the query whatever its verdict, and -- only for a
     * satisfiable one -- the plan the focused replay is run from.
     */
    private static JsonObject publish(Path out, Obligation obligation,
                                      ObligationResult result, String smt2,
                                      List<GapRow> gaps) throws IOException {
        JsonObject row = ExploreCodec.writeResult(result);
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "OBLIGATION_RESULT");
        RowCodec.writeJsonl(out.resolve("obligation_result.jsonl"),
                Collections.singletonList(row));
        RowCodec.writeAll(out.resolve("obligation.jsonl"),
                Collections.singletonList(obligation),
                ExploreCodec::writeObligation);
        RowCodec.writeAll(out.resolve("gaps.jsonl"),
                ExploreMain.distinct(new ArrayList<GapRow>(gaps)),
                RowCodec::writeGap);
        // Always written, whatever the verdict: an UNSAT obligation is the
        // one a reader most needs the query for, because what a flip
        // asserted that contradicts negating its decision is not derivable
        // from the verdict.
        Files.write(out.resolve("obligation_query.smt2"),
                (smt2.isEmpty()
                        ? "; no query was encoded: " + result.verdict() + " "
                        + result.detail() + System.lineSeparator()
                        : smt2).getBytes(StandardCharsets.UTF_8));
        List<JsonObject> plan = new ArrayList<JsonObject>();
        if (result.verdict() == Verdict.SAT_MODEL_READY) {
            plan.add(replayTask(obligation));
        }
        RowCodec.writeJsonl(out.resolve("execution_task_plan.jsonl"), plan);
        return row;
    }

    /**
     * The focused replay this obligation asks for.
     *
     * <p>One task: the obligation's own focused occurrence, the decision it
     * flips, the value to apply at every mint and the value to answer at
     * every attach.  A handoff the corpus cannot produce is named rather than
     * hidden, so a replay that rests on one is a known hypothesis.</p>
     */
    private static JsonObject replayTask(Obligation obligation) {
        JsonObject task = new JsonObject();
        task.addProperty("schemaVersion", 1);
        task.addProperty("kind", "EXECUTION_TASK");
        task.addProperty("taskId", obligation.taskId());
        task.addProperty("obligationId", obligation.obligationId());
        task.addProperty("pathId", obligation.pathId());
        JsonObject flip = new JsonObject();
        flip.addProperty("siteId", obligation.siteId());
        flip.addProperty("ordinal", obligation.ordinal());
        flip.addProperty("outcome", obligation.flippedOutcome());
        task.add("flip", flip);
        JsonObject roots = new JsonObject();
        for (Map.Entry<String, String> assignment
                : obligation.rootAssignments().entrySet()) {
            roots.addProperty(assignment.getKey(), assignment.getValue());
        }
        task.add("rootAssignments", roots);
        JsonObject answers = new JsonObject();
        for (Map.Entry<String, String> answer
                : obligation.answers().entrySet()) {
            answers.addProperty(answer.getKey(), answer.getValue());
        }
        task.add("answers", answers);
        JsonArray unproducible = new JsonArray();
        for (String endpoint : obligation.unproducible()) {
            unproducible.add(endpoint);
        }
        task.add("unproducible", unproducible);
        return task;
    }
}
