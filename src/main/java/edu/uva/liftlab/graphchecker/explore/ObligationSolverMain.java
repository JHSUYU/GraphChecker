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
 * <p>One process per obligation (queries are independent). The verdict is
 * always written: UNSAT and NOT_ADMITTED are terminal outcomes the next wave
 * reads, never a run failure.</p>
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
            // The path is gone from the corpus: this obligation's own admission
            // gap.
            return publish(out, null, proposal,
                    ObligationResult.of(obligationId,
                            Verdict.NOT_ADMITTED, "",
                            "no session of this corpus still states path "
                                    + proposal.pathId() + " of task "
                                    + proposal.taskId()), "",
                    Collections.<String, String>emptyMap(),
                    Collections.<String, String>emptyMap(),
                    Collections.<Corpus.Flip>emptyList(),
                    Collections.singletonList(GapRow.of(ExploreCodec.EXPLORATION,
                            GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                            obligationId, "the obligation names a path the "
                                    + "corpus does not hold")), null);
        }
        ObligationFactory.Outcome outcome = ObligationFactory.solve(corpus,
                candidate, z3, timeoutMillis);
        // The schedule half of the world (SchedulePrefix).
        SchedulePrefix.Cut cut = null;
        if (outcome.result.verdict() == Verdict.SAT_MODEL_READY) {
            cut = SchedulePrefix.write(iteration, candidate.path.sessionId,
                    targetOccurrences(candidate), out);
        }
        return publish(out, candidate.task,
                outcome.issued() ? outcome.obligation : proposal,
                outcome.result, outcome.smt2, outcome.clockDeltas,
                outcome.rootMints, outcome.inheritedFlips, outcome.gaps, cut);
    }

    /** Where the prefix is cut: the TARGET (flip occurrence, focus, factor),
     *  not where a value is planted. Trap: cutting at an early mint lets
     *  daemons run free and the target occurrence may never run (hdfs-17967
     *  path B). */
    private static List<String> targetOccurrences(
            ObligationFactory.Candidate candidate) {
        List<String> ids = new ArrayList<String>();
        ids.add(candidate.path.occurrence.id());
        ids.add(candidate.task.focused().id());
        for (OccurrenceAddress member : candidate.task.factor()) {
            ids.add(member.id());
        }
        return ids;
    }

    /** Writes the verdict row, the completed obligation, the query (always)
     *  and, when satisfiable, the focus row. The focus row is {@code
     *  focused_task.jsonl}, never {@code execution_task_plan.jsonl}: that name
     *  is decoded as a PLAN {@code ExecutionTask} by the session opener. */
    private static JsonObject publish(Path out, Task task,
                                      Obligation obligation,
                                      ObligationResult result, String smt2,
                                      Map<String, String> clockDeltas,
                                      Map<String, String> rootMints,
                                      List<Corpus.Flip> inheritedFlips,
                                      List<GapRow> gaps,
                                      SchedulePrefix.Cut cut)
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
        // Always written: an UNSAT query is the one a reader most needs.
        Files.write(out.resolve("obligation_query.smt2"),
                (smt2.isEmpty()
                        ? "; no query was encoded: " + result.verdict() + " "
                        + result.detail() + System.lineSeparator()
                        : smt2).getBytes(StandardCharsets.UTF_8));
        List<JsonObject> focus = new ArrayList<JsonObject>();
        if (result.verdict() == Verdict.SAT_MODEL_READY) {
            JsonObject replay = replayTask(task, obligation, clockDeltas,
                    rootMints, inheritedFlips);
            // Which session's order the replay is held to; the prefix sits
            // beside this row.
            if (cut != null) replay.add("schedulePrefix", cut.toJson());
            focus.add(replay);
        }
        RowCodec.writeJsonl(out.resolve(ObligationDir.FOCUSED_TASK), focus);
        return row;
    }

    /** The focused replay this obligation asks for: focus, factor, the mint
     *  occurrence of every assigned root, the flip, mint values (a clock as a
     *  skew), attach answers, and unproducible handoffs named. Mints are
     *  listed, not derived: one whole-workload run can focus several
     *  occurrences so each root is planted where it is minted. */
    private static JsonObject replayTask(Task focused,
                                         Obligation obligation,
                                         Map<String, String> clockDeltas,
                                         Map<String, String> rootMints,
                                         List<Corpus.Flip> inheritedFlips) {
        JsonObject task = new JsonObject();
        task.addProperty("schemaVersion", 1);
        task.addProperty("kind", "FOCUSED_TASK");
        task.addProperty("taskId", obligation.taskId());
        // Task fields: render for OccurrenceAddress.parse, id for grep.
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
        // Inherited flips: held like the primary flip (a wrong arm un-admits),
        // their occurrences run symbolic. Still ONE verdict row: the primary
        // flip's.
        JsonArray inherited = new JsonArray();
        for (Corpus.Flip carried : inheritedFlips) {
            inherited.add(ExploreCodec.writeFlip(carried));
        }
        task.add("inheritedFlips", inherited);
        JsonObject roots = new JsonObject();
        for (Map.Entry<String, String> assignment
                : obligation.rootAssignments().entrySet()) {
            roots.addProperty(assignment.getKey(), assignment.getValue());
        }
        task.add("rootAssignments", roots);
        // A clock's counterfactual is a SKEW off the replay's own reading, kept
        // apart from rootAssignments.
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
        // Each root's mint occurrence (clocks included) is focused, or it would
        // read the recorded value.
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
