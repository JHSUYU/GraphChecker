package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.Z3;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ReadsFrom;
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
                    Collections.<Corpus.Flip>emptyList(),
                    Collections.<ReadsFrom>emptyList(),
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
                outcome.rootMints, outcome.inheritedFlips, outcome.versions,
                outcome.gaps);
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
                                      List<Corpus.Flip> inheritedFlips,
                                      List<ReadsFrom> versions,
                                      List<GapRow> gaps)
            throws IOException {
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
        Path focus = out.resolve(ObligationDir.FOCUSED_TASK);
        if (result.verdict() == Verdict.SAT_MODEL_READY) {
            ExploreCodec.writeFocusFile(focus, ExploreCodec.writeFocusRow(
                    task, obligation, clockDeltas, rootMints, inheritedFlips,
                    versions));
        } else {
            RowCodec.writeJsonl(focus, Collections.<JsonObject>emptyList());
        }
        return row;
    }
}
