package edu.uva.liftlab.graphchecker.explore;

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
import edu.uva.liftlab.graphchecker.option.LongOptions;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

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
        LongOptions options = LongOptions.parse(argv);
        Path obligations = options.path("obligations");
        String obligationId = options.value("obligation-id", "");
        Path sessions = options.path("sessions");
        Path out = options.path("output-dir");
        if (obligations == null || obligationId.isEmpty() || sessions == null
                || out == null) {
            throw new IllegalArgumentException("--obligations, "
                    + "--obligation-id, --sessions and --output-dir are "
                    + "required");
        }
        Path iteration = sessions.getParent();
        JsonObject result = solve(iteration,
                options.path("root-domains"), obligations,
                obligationId, out,
                Paths.get(options.value("z3", "z3")),
                options.number("solver-timeout-ms",
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
            return publish(out, proposal,
                    ObligationResult.of(obligationId,
                            Verdict.NOT_ADMITTED, "",
                            "no session of this corpus still states path "
                                    + proposal.pathId() + " of task "
                                    + proposal.taskId()), "",
                    Collections.singletonList(GapRow.of(
                            ExploreCodec.EXPLORATION, GapKind.ADMISSION_GAP,
                            GapClass.DIAGNOSTIC, obligationId,
                            "the obligation names a path the corpus does "
                                    + "not hold")), null);
        }
        ObligationFactory.Outcome outcome = ObligationFactory.solve(corpus,
                candidate, z3, timeoutMillis);
        if (!outcome.issued()) {
            return publish(out, proposal, outcome.result, outcome.smt2,
                    outcome.gaps, null);
        }
        // The schedule half of the world (SchedulePrefix). Mints are listed,
        // not derived: one whole-workload run can focus several occurrences
        // so each root is planted where it is minted.
        SchedulePrefix.Cut cut = SchedulePrefix.write(iteration,
                candidate.path.sessionId, targetOccurrences(candidate), out);
        Task task = candidate.task;
        return publish(out, outcome.obligation, outcome.result, outcome.smt2,
                outcome.gaps, ExploreCodec.writeFocusRow(task.focused(),
                        task.seedSessionId(), task.factor(),
                        outcome.obligation, outcome.inheritedFlips,
                        outcome.clockDeltas, outcome.rootMints, cut));
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

    /** Writes the verdict row, the obligation, the query (always) and the
     *  focus row ({@code focus} null: an empty file). The focus row is {@code
     *  focused_task.jsonl}, never {@code execution_task_plan.jsonl}: that name
     *  is decoded as a PLAN {@code ExecutionTask} by the session opener. */
    private static JsonObject publish(Path out, Obligation obligation,
                                      ObligationResult result, String smt2,
                                      List<GapRow> gaps, JsonObject focus)
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
        RowCodec.writeJsonl(out.resolve(ObligationDir.FOCUSED_TASK),
                focus == null ? Collections.<JsonObject>emptyList()
                        : Collections.singletonList(focus));
        return row;
    }
}
