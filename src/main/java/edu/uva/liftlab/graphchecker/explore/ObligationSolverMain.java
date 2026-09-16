package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.Z3;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;

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
 *                             obligation_query.smt2, focused_task.jsonl
 *   --root-domains &lt;file&gt;     what the CASE says each root may be: the same
 *                             declaration the wave was planned under
 *   --z3 &lt;path&gt; --solver-timeout-ms &lt;n&gt;
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
                        Z3.DEFAULT_TIMEOUT_MILLIS));
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
            return publish(out, null, proposal,
                    ObligationResult.of(obligationId,
                            Verdict.NOT_ADMITTED, "",
                            "no session of this corpus still states path "
                                    + proposal.pathId() + " of task "
                                    + proposal.taskId()), "",
                    Collections.<String, String>emptyMap(),
                    Collections.<String, String>emptyMap(),
                    Collections.singletonList(GapRow.of(ExploreCodec.EXPLORATION,
                            GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                            obligationId, "the obligation names a path the "
                                    + "corpus does not hold")));
        }
        ObligationFactory.Outcome outcome = ObligationFactory.solve(corpus,
                candidate, z3, timeoutMillis);
        return publish(out, candidate.task,
                outcome.issued() ? outcome.obligation : proposal,
                outcome.result, outcome.smt2, outcome.clockDeltas,
                outcome.rootMints, outcome.gaps);
    }

    /**
     * Writes the worker's artifacts: the verdict row the campaign reads, the
     * completed obligation, the query whatever its verdict, and -- only for a
     * satisfiable one -- the FOCUS row the replay is run from.
     *
     * <p>The focus row is {@code focused_task.jsonl} and not {@code
     * execution_task_plan.jsonl}: that name belongs to the PLAN, whose rows
     * are {@code plan.ExecutionTask}s, and the workload session opener
     * decodes whatever stands under it ({@code runtime.ConcolicTaskPlan.load}
     * -> {@code ExecutionTask.decode}).  Writing a focus row there made every
     * obligation replay die on "execution task requires sourceKey" before it
     * started.  One file, one shape.</p>
     */
    private static JsonObject publish(Path out, Task task,
                                      Obligation obligation,
                                      ObligationResult result, String smt2,
                                      Map<String, String> clockDeltas,
                                      Map<String, String> rootMints,
                                      List<GapRow> gaps) throws IOException {
        JsonObject row = RowCodec.writeObligationResult(result);
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "OBLIGATION_RESULT");
        RowCodec.writeJsonl(out.resolve(ObligationDir.RESULT),
                Collections.singletonList(row));
        RowCodec.writeAll(out.resolve(ObligationDir.OBLIGATION),
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
        List<JsonObject> focus = new ArrayList<JsonObject>();
        if (result.verdict() == Verdict.SAT_MODEL_READY) {
            focus.add(replayTask(task, obligation, clockDeltas,
                    rootMints));
        }
        RowCodec.writeJsonl(out.resolve(ObligationDir.FOCUSED_TASK), focus);
        return row;
    }

    /**
     * The focused replay this obligation asks for.
     *
     * <p>One task: the obligation's own focused occurrence, its factor
     * members, the MINT OCCURRENCE of every root the model assigns, the
     * decision it flips, the value to apply at every mint (a clock's as the
     * skew to add to the replay's own reading) and the value to answer at
     * every attach.  A handoff the corpus cannot produce is named rather
     * than hidden, so a replay that rests on one is a known hypothesis.</p>
     *
     * <p>The mints are on the row because the focused set is what the
     * replay is told, not what it derives: a focused replay is one run of
     * the WHOLE workload, so nn0's key rotation can be focused in the same
     * replay as the balancer occurrence whose guard the flip is about --
     * which is the only way the balancer's flip ever runs under the serial
     * the obligation assigns.</p>
     */
    private static JsonObject replayTask(Task focused,
                                         Obligation obligation,
                                         Map<String, String> clockDeltas,
                                         Map<String, String> rootMints) {
        JsonObject task = new JsonObject();
        task.addProperty("schemaVersion", 1);
        task.addProperty("kind", "FOCUSED_TASK");
        task.addProperty("taskId", obligation.taskId());
        // The Task's own fields, so the replay knows WHICH occurrence it
        // focuses without re-deriving a closure: the render is what
        // OccurrenceAddress.parse reads back, the id is what a reader greps.
        if (focused != null) {
            task.addProperty("focused", focused.focused().render());
            task.addProperty("focusedOccurrenceId", focused.focused().id());
            task.addProperty("seedSessionId", focused.seedSessionId());
            JsonArray factor = new JsonArray();
            for (OccurrenceAddress member : focused.factor()) {
                factor.add(member.render());
            }
            task.add("factor", factor);
        }
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
        // A clock's counterfactual is a SKEW, never an instant: the replay
        // reads the clock for itself and moves that reading by this much.
        // Written apart from rootAssignments so nothing has to guess which
        // of the two a value is.
        JsonObject clocks = new JsonObject();
        for (Map.Entry<String, String> delta : clockDeltas.entrySet()) {
            clocks.addProperty(delta.getKey(), delta.getValue());
        }
        task.add("clockDeltas", clocks);
        JsonObject answers = new JsonObject();
        for (Map.Entry<String, String> answer
                : obligation.answers().entrySet()) {
            answers.addProperty(answer.getKey(), answer.getValue());
        }
        task.add("answers", answers);
        // Where each assigned root is MINTED, so the replay focuses those
        // occurrences too: an assignment is planted at its mint, and a mint
        // that runs unfocused reads the recording's value under an
        // obligation asking for another one.  A CLOCK's skew names its mint
        // here as well -- the two are one focused set, however the value is
        // stated.
        JsonObject mints = new JsonObject();
        for (Map.Entry<String, String> mint : rootMints.entrySet()) {
            mints.addProperty(mint.getKey(), mint.getValue());
        }
        task.add("rootMints", mints);
        JsonArray unproducible = new JsonArray();
        for (String endpoint : obligation.unproducible()) {
            unproducible.add(endpoint);
        }
        task.add("unproducible", unproducible);
        return task;
    }
}
