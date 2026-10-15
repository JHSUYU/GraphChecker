package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
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
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
import edu.uva.liftlab.graphchecker.runtime.FocusedReplay;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * An obligation's question: build its query, solve it, say what the replay
 * must apply.  One obligation, or every obligation one host's workers ask
 * within an exploration, over the corpus as it stands when each is taken.
 *
 * <pre>
 *   --sessions &lt;dir&gt;          the corpus the exploration has landed so far
 *   --root-domains &lt;file&gt;     what the CASE says each root may be: the same
 *                             declaration the round was planned under
 *   --z3 &lt;path&gt; --solver-timeout-ms &lt;n&gt;
 *   --z3-room-mb &lt;n&gt;         what the JVM's charge holds for its z3
 *                             processes, a question's two engines half
 *                             each ({@code smt.Z3}); required
 *   one obligation:
 *   --obligations &lt;file&gt;      the round's obligations.jsonl
 *   --obligation-id &lt;id&gt;      which row of it this worker owns
 *   --output-dir &lt;dir&gt;        obligation_result.jsonl, obligation.jsonl,
 *                             obligation_query.smt2, gaps.jsonl,
 *                             focused_task.jsonl, the schedule cut, the
 *                             pairings' expected_edges.jsonl, and
 *                             question.txt (a decided verdict of its own
 *                             settles its question) or question.asked (SAT)
 *   or a host's share of them ({@link Service}):
 *   --serve &lt;dir&gt;             answer the questions put there, each into its
 *                             own output directory, until none has come for
 *   --idle-seconds &lt;n&gt;
 *   --retire-past-mb &lt;n&gt;     or until a question needs a corpus of more
 *                             than n MB of session files, which the heap it
 *                             was started at does not hold (0: never)
 * </pre>
 *
 * <p>Queries are independent: a question's files are the same whichever
 * questions the JVM answered before it.  The verdict is always written: UNSAT
 * and NOT_ADMITTED are terminal outcomes the next round reads, never a run
 * failure.</p>
 */
public final class ObligationSolverMain {
    private ObligationSolverMain() {
    }

    public static void main(String[] argv) throws Exception {
        LongOptions options = LongOptions.parse(argv);
        Path sessions = options.path("sessions");
        if (sessions == null) {
            throw new IllegalArgumentException("--sessions is required");
        }
        Path iteration = sessions.getParent();
        Path rootDomains = options.path("root-domains");
        Path z3 = Paths.get(options.value("z3", "z3"));
        long timeoutMillis = options.number("solver-timeout-ms",
                Z3.DEFAULT_TIMEOUT_MILLIS);
        int z3RoomMb = (int) options.number("z3-room-mb", 0L);
        if (z3RoomMb <= 0) {
            throw new IllegalArgumentException("--z3-room-mb is required: "
                    + "what this JVM's charge holds for its z3 processes");
        }
        Path serve = options.path("serve");
        if (serve != null) {
            Service.serve(serve,
                    options.number("idle-seconds", 0L) * 1000L,
                    answerer(sessions, rootDomains, z3, timeoutMillis,
                            z3RoomMb, options.number("retire-past-mb", 0L)
                                    << 20));
            return;
        }
        Path obligations = options.path("obligations");
        String obligationId = options.value("obligation-id", "");
        Path out = options.path("output-dir");
        if (obligations == null || obligationId.isEmpty() || out == null) {
            throw new IllegalArgumentException("--serve, or --obligations, "
                    + "--obligation-id and --output-dir, are required");
        }
        JsonObject result = solve(Corpus.read(iteration, rootDomains),
                iteration, obligations, obligationId, out, z3,
                timeoutMillis, z3RoomMb);
        System.out.println(ExploreMain.pretty(result));
    }

    /**
     * A host's answers for one exploration.  The corpus is read when the
     * first question is taken, and read again only when a question's round
     * was planned over a session the read did not hold (its {@link
     * #ROUND_CORPUS}, the sessions that still stand of it), or a session the
     * read held has left the corpus: a round's question needs no session
     * that landed after the round was planned, and sessions land every few
     * seconds while a re-read costs 10-16 s (solr-adhoc-39 PV7, 208
     * sessions; read again after every landing, a host's solver re-read
     * before nearly every question).  A read takes every session that
     * stands then, those the read before held from it, unread ({@link
     * Corpus#read(Path, Path, Corpus, java.util.Collection)}); otherwise the
     * question starts from the corpus as read ({@link
     * Corpus#freshLowerings}).  Either way its files are the ones a JVM of
     * its own, reading that corpus, would write.  A read past {@code
     * retirePastBytes} of session files (0: none) is not made: the question
     * is given back ({@link Service.Outgrown}) for a solver sized anew.
     */
    private static Service.Answerer answerer(Path sessions,
                                             Path rootDomains, Path z3,
                                             long timeoutMillis,
                                             int z3RoomMb,
                                             long retirePastBytes) {
        Path iteration = sessions.getParent();
        return new Service.Answerer() {
            private Corpus corpus;
            /** Each session the corpus was read from -> its files' bytes. */
            private final Map<String, Long> read =
                    new HashMap<String, Long>();

            @Override
            public void answer(JsonObject question, Path out)
                    throws Exception {
                Path obligations = Paths.get(JsonFields.primitiveString(
                        question, "obligations"));
                List<String> now = listing(sessions);
                if (corpus == null || stale(read.keySet(), now,
                        round(obligations, now))) {
                    Map<String, Long> reading = new HashMap<String, Long>();
                    long bytes = 0L;
                    for (String name : now) {
                        Long held = read.get(name);
                        long size = held != null ? held
                                : bytes(sessions.resolve(name));
                        reading.put(name, size);
                        bytes += size;
                    }
                    if (retirePastBytes > 0L && bytes > retirePastBytes) {
                        throw new Service.Outgrown("its corpus is "
                                + (bytes >> 20) + " MB of sessions, past the "
                                + (retirePastBytes >> 20) + " MB its heap "
                                + "was started for");
                    }
                    corpus = Corpus.read(iteration, rootDomains, corpus,
                            null);
                    read.clear();
                    read.putAll(reading);
                } else {
                    corpus.freshLowerings();
                }
                solve(corpus, iteration, obligations,
                        JsonFields.primitiveString(question, "obligationId"),
                        out, z3, timeoutMillis, z3RoomMb);
            }
        };
    }

    /** Whether a corpus read from the sessions {@code read} lacks one the
     *  {@code round} needs, or holds one that is no longer standing {@code
     *  now}. */
    static boolean stale(Set<String> read, List<String> now,
                         List<String> round) {
        return !read.containsAll(round) || !now.containsAll(read);
    }

    /**
     * The sessions a round was planned over, beside its obligations
     * ({@code run_engine.sh campaign_stream_round_start}).
     */
    static final String ROUND_CORPUS = "corpus.txt";

    /** Of the sessions standing {@code now}, those the round of {@code
     *  obligations} was planned over; all of them where it names none. */
    static List<String> round(Path obligations, List<String> now)
            throws IOException {
        Path named = obligations.resolveSibling(ROUND_CORPUS);
        if (!Files.isRegularFile(named)) return now;
        Set<String> round = new HashSet<String>();
        for (String line : Files.readAllLines(named,
                StandardCharsets.UTF_8)) {
            if (!line.trim().isEmpty()) round.add(line.trim());
        }
        List<String> standing = new ArrayList<String>();
        for (String name : now) {
            if (round.contains(name)) standing.add(name);
        }
        return standing;
    }

    /** The bytes of one session's files. */
    private static long bytes(Path session) throws IOException {
        long bytes = 0L;
        try (DirectoryStream<Path> files = Files.newDirectoryStream(session)) {
            for (Path file : files) {
                if (Files.isRegularFile(file)) bytes += Files.size(file);
            }
        }
        return bytes;
    }

    /** The session directory names of a corpus, sorted. */
    static List<String> listing(Path sessions) throws IOException {
        List<String> names = new ArrayList<String>();
        try (DirectoryStream<Path> entries =
                     Files.newDirectoryStream(sessions)) {
            for (Path entry : entries) {
                if (Files.isDirectory(entry)) {
                    names.add(entry.getFileName().toString());
                }
            }
        }
        Collections.sort(names);
        return names;
    }

    /** Solves one published obligation over the corpus of {@code
     *  iteration} and writes every artifact of it. */
    public static JsonObject solve(Corpus corpus, Path iteration,
                                   Path obligations, String obligationId,
                                   Path out, Path z3, long timeoutMillis,
                                   int z3RoomMb)
            throws IOException {
        Files.createDirectories(out);
        Obligation proposal = null;
        for (Obligation row : RowCodec.readAll(obligations,
                ExploreCodec::readObligation)) {
            if (row.obligationId().equals(obligationId)) proposal = row;
        }
        if (proposal == null) {
            throw new IOException("the round has no obligation " + obligationId
                    + ": " + obligations);
        }
        if (proposal.force()) {
            return force(corpus, iteration, obligations, proposal, out);
        }
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
        OccurrenceAddress declared = declaredTarget(obligations);
        // What the replay is given besides the corpus, as the question
        // keys it: the declared occurrence, and the plan generation its
        // class tree is woven from (GROW appends to the plan and re-weaves).
        Path plan = iteration.resolve(PLAN);
        String given = "declared " + (declared == null ? ""
                : declared.render()) + "\nplan " + (Files.isRegularFile(plan)
                ? ArtifactIO.sha256(plan) : "");
        ObligationFactory.Outcome outcome = ObligationFactory.solve(corpus,
                candidate, z3, timeoutMillis, z3RoomMb, given,
                ObligationDir.answered(iteration));
        if (!outcome.issued()) {
            JsonObject published = publish(out, proposal, outcome.result,
                    outcome.smt2, outcome.gaps, null);
            // Last: a verdict that settles its question says so only once
            // it is written.
            if (outcome.settles) {
                ask(out.resolve(ObligationDir.QUESTION), outcome.question);
            }
            return published;
        }
        // The schedule half of the world (SchedulePrefix), followed only up
        // to the first occurrence the world's pairings reorder. Mints are
        // listed, not derived: one whole-workload run can focus several
        // occurrences so each root is planted where it is minted.
        List<String> cutAt = targetOccurrences(candidate);
        cutAt.addAll(outcome.holding.reordered);
        SchedulePrefix.Cut cut = SchedulePrefix.write(iteration,
                candidate.path.sessionId, cutAt, outcome.holding.cutBefore,
                true, out);
        // The pairings, held and compared as CONFIRM's edges are
        // (runtime.Confirmation).
        if (!outcome.holding.edges.isEmpty()) {
            RowCodec.writeJsonl(out.resolve(Confirmation.FILE),
                    outcome.holding.edges);
        }
        Task task = candidate.task;
        JsonObject focus = ExploreCodec.writeFocusRow(task.focused(),
                declared, task.seedSessionId(), task.factor(),
                outcome.obligation, outcome.inheritedFlips,
                outcome.clockDeltas, outcome.rootMints, outcome.pairings,
                cut);
        // An open decider arm's flip: its replay may refute its world
        // (FocusedReplay#refuted).
        if (outcome.openArm) focus.addProperty(FocusedReplay.OPEN_ARM, true);
        JsonObject published = publish(out, outcome.obligation,
                outcome.result, outcome.smt2, outcome.gaps, focus);
        // Asked, and settled only by what its replay decides: its worker
        // makes it the settled question then (run_engine.sh
        // campaign_obligation_replay).
        ask(out.resolve(ObligationDir.QUESTION_ASKED), outcome.question);
        return published;
    }

    /**
     * A FORCE run's worker (PIPELINE §7.10): no query; the replay is the
     * seed's world held to the seed's schedule up to the declared
     * occurrence, whose branches the focus row's {@code force} has forced.
     */
    private static JsonObject force(Corpus corpus, Path iteration,
                                    Path obligations, Obligation proposal,
                                    Path out) throws IOException {
        Task task = ClosurePlanner.taskOf(corpus, proposal.taskId());
        if (task == null) {
            return publish(out, proposal, ObligationResult.of(
                    proposal.obligationId(), Verdict.NOT_ADMITTED, "",
                    ForcedFlip.FORCE + ": no task " + proposal.taskId()
                            + " in this corpus"), "",
                    Collections.<GapRow>emptyList(), null);
        }
        OccurrenceAddress declared = declaredTarget(obligations);
        SchedulePrefix.Cut cut = SchedulePrefix.write(iteration,
                corpus.seedSessionId(), targetOccurrences(task), true, out);
        JsonObject focus = ExploreCodec.writeFocusRow(task.focused(),
                declared, task.seedSessionId(), task.factor(), proposal,
                Collections.<Corpus.Flip>emptyList(),
                Collections.<String, String>emptyMap(),
                Collections.<String, String>emptyMap(),
                Collections.<String, String>emptyMap(), cut);
        focus.addProperty(ExploreCodec.FORCE, true);
        JsonObject published = publish(out, proposal, ObligationResult.of(
                proposal.obligationId(), Verdict.SAT_MODEL_READY, "",
                ForcedFlip.FORCE + ": the recording's world, the declared "
                        + "occurrence's branches forced to the throw"), "",
                Collections.<GapRow>emptyList(), focus);
        // Named by its flip, as a flip's question is (ForcedFlip#flip).
        ask(out.resolve(ObligationDir.QUESTION_ASKED), ForcedFlip.flip(proposal)
                + ":" + ForcedFlip.FORCE + " " + proposal.obligationId());
        return published;
    }

    /** The iteration's task plan, which GROW appends to. */
    private static final String PLAN = "execution_task_plan.jsonl";

    private static void ask(Path file, String question) throws IOException {
        Files.write(file, (question + System.lineSeparator())
                .getBytes(StandardCharsets.UTF_8));
    }

    /**
     * The case's declared occurrence, as the wave planned it: the one anchor
     * {@code explore_manifest.json} resolved beside the wave's obligations
     * (a selector or {@code first} already resolved), or null.
     */
    private static OccurrenceAddress declaredTarget(Path obligations)
            throws IOException {
        Path manifest = obligations.resolveSibling(
                ExploreMain.MANIFEST_FILE);
        if (!Files.isRegularFile(manifest)) return null;
        JsonArray anchors = JsonFields.array(
                ExploreCodec.readObject(manifest), "anchors");
        return anchors.size() == 1
                ? OccurrenceAddress.parse(anchors.get(0).getAsString()) : null;
    }

    /** Where the prefix is cut: the TARGET (flip occurrence, focus, factor),
     *  not where a value is planted. Trap: cutting at an early mint lets
     *  daemons run free and the target occurrence may never run (hdfs-17967
     *  path B). */
    private static List<String> targetOccurrences(
            ObligationFactory.Candidate candidate) {
        List<String> ids = new ArrayList<String>();
        ids.add(candidate.path.occurrence.id());
        ids.addAll(targetOccurrences(candidate.task));
        return ids;
    }

    /** A task's: its focus and factor. */
    private static List<String> targetOccurrences(Task task) {
        List<String> ids = new ArrayList<String>();
        ids.add(task.focused().id());
        for (OccurrenceAddress member : task.factor()) ids.add(member.id());
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
        ExploreCodec.writeFocusFile(out.resolve(ObligationDir.FOCUSED_TASK),
                focus);
        return row;
    }
}
