package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.Z3;

import edu.uva.liftlab.graphchecker.contract.HeapWatch;
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
 * must apply.  Every obligation one host's workers ask within an
 * exploration, over the corpus as it read it ({@link Service}); or one
 * flip's hard-lane ask, over its first ask's query alone ({@link #decide}).
 *
 * <pre>
 *   --z3 &lt;path&gt; --solver-timeout-ms &lt;n&gt;
 *   --z3-room-mb &lt;n&gt;         what the JVM's charge holds for its z3
 *                             processes, a question's two engines half
 *                             each ({@code smt.Z3}); required
 *   a host's share of the questions:
 *   --sessions &lt;dir&gt;          the corpus the exploration has landed so far
 *   --root-domains &lt;file&gt;     what the CASE says each root may be: the same
 *                             declaration the round was planned under
 *   --serve &lt;dir&gt;             answer the questions put there, each into its
 *                             own output directory (obligation_result.jsonl,
 *                             obligation.jsonl, obligation_query.smt2,
 *                             gaps.jsonl, focused_task.jsonl, the schedule
 *                             cut, the pairings' expected_edges.jsonl,
 *                             question.txt or question.asked, and a first
 *                             ask undecided at its budget its {@link
 *                             HardAsk}), until none has come for
 *   --idle-seconds &lt;n&gt;
 *   --retire-past-mb &lt;n&gt;     or until a question needs a corpus of more
 *                             than n MB of session files, which the heap it
 *                             was started at does not hold (0: never)
 *   or one flip's hard-lane ask, no corpus read ({@link #decide}):
 *   --decide &lt;worker&gt; --obligations &lt;file&gt; --obligation-id &lt;id&gt;
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
        HeapWatch.start();
        LongOptions options = LongOptions.parse(argv);
        Path z3 = Paths.get(options.value("z3", "z3"));
        long timeoutMillis = options.number("solver-timeout-ms",
                Z3.DEFAULT_TIMEOUT_MILLIS);
        int z3RoomMb = (int) options.number("z3-room-mb", 0L);
        if (z3RoomMb <= 0) {
            throw new IllegalArgumentException("--z3-room-mb is required: "
                    + "what this JVM's charge holds for its z3 processes");
        }
        Path decide = options.path("decide");
        if (decide != null) {
            decide(options.path("obligations"),
                    options.value("obligation-id", ""), decide, z3,
                    timeoutMillis, z3RoomMb);
            return;
        }
        Path sessions = options.path("sessions");
        if (sessions == null) {
            throw new IllegalArgumentException("--sessions is required");
        }
        Path iteration = sessions.getParent();
        Path rootDomains = options.path("root-domains");
        Path serve = options.path("serve");
        if (serve != null) {
            Service.serve(serve,
                    options.number("idle-seconds", 0L) * 1000L,
                    answerer(sessions, rootDomains, z3, timeoutMillis,
                            z3RoomMb, options.number("retire-past-mb", 0L)
                                    << 20));
            return;
        }
        throw new IllegalArgumentException("--serve or --decide is required");
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
     *
     * <p>THE CORPUS STANDS WITHOUT WHAT GROW WITHDREW ({@link #standing}),
     * and a read is of whole sessions: GROW's swaps withdraw sessions while
     * solvers serve ({@code run_engine.sh campaign_stream_swap}), each named
     * in {@link #WITHDRAWN} before its directory leaves.  A session the
     * journal names once the read is done -- or one gone under it, failing
     * the read -- may have been read in part (a file missing reads as no
     * rows), and the corpus is read again without it; a session leaves once
     * and never returns, so one still unnamed after the read stood whole
     * while it was read.  The journal, not the listing, says what left: a
     * peer's listing of the directory may be its NFS client's, up to a
     * minute old, while a file's open reads it as the head closed it.</p>
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
                List<String> now = standing(sessions);
                if (corpus == null || stale(read.keySet(), now,
                        round(obligations, now))) {
                    while (true) {
                        Map<String, Long> reading =
                                new HashMap<String, Long>();
                        Corpus next;
                        try {
                            long bytes = 0L;
                            for (String name : now) {
                                Long held = read.get(name);
                                long size = held != null ? held
                                        : bytes(sessions.resolve(name));
                                reading.put(name, size);
                                bytes += size;
                            }
                            if (retirePastBytes > 0L
                                    && bytes > retirePastBytes) {
                                throw new Service.Outgrown("its corpus is "
                                        + (bytes >> 20) + " MB of sessions, "
                                        + "past the " + (retirePastBytes >> 20)
                                        + " MB its heap was started for");
                            }
                            next = Corpus.read(iteration, rootDomains,
                                    corpus, now);
                        } catch (IOException failed) {
                            if (Collections.disjoint(withdrawn(iteration),
                                    now)) {
                                throw failed;
                            }
                            now = standing(sessions);
                            continue;
                        }
                        // Its sessions whole stand in the next read too.
                        corpus = next;
                        if (Collections.disjoint(withdrawn(iteration), now)) {
                            read.clear();
                            read.putAll(reading);
                            break;
                        }
                        now = standing(sessions);
                    }
                } else {
                    corpus.freshLowerings();
                }
                // A flip the hard lane found sat, finished with its model.
                String decided = JsonFields.optionalString(question,
                        "decided");
                solve(corpus, iteration, obligations,
                        JsonFields.primitiveString(question, "obligationId"),
                        out, z3, timeoutMillis, z3RoomMb, decided.isEmpty()
                                ? null : HardAsk.Model.read(
                                Paths.get(decided)));
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

    /**
     * The sessions GROW's swaps withdrew from the corpus, one per line,
     * beside it: each appended by the head before its directory leaves
     * ({@code run_engine.sh campaign_stream_swap}).
     */
    static final String WITHDRAWN = "withdrawn.txt";

    /** The sessions {@link #WITHDRAWN} names. */
    static Set<String> withdrawn(Path iteration) throws IOException {
        Set<String> named = new HashSet<String>();
        Path journal = iteration.resolve(WITHDRAWN);
        if (!Files.isRegularFile(journal)) return named;
        for (String line : Files.readAllLines(journal,
                StandardCharsets.UTF_8)) {
            if (!line.trim().isEmpty()) named.add(line.trim());
        }
        return named;
    }

    /** The session directory names of a corpus, sorted, but those GROW
     *  withdrew ({@link #WITHDRAWN}). */
    static List<String> standing(Path sessions) throws IOException {
        List<String> names = new ArrayList<String>();
        try (DirectoryStream<Path> entries =
                     Files.newDirectoryStream(sessions)) {
            for (Path entry : entries) {
                if (Files.isDirectory(entry)) {
                    names.add(entry.getFileName().toString());
                }
            }
        }
        names.removeAll(withdrawn(sessions.getParent()));
        Collections.sort(names);
        return names;
    }

    /** The round's row of one obligation. */
    private static Obligation proposal(Path obligations, String obligationId)
            throws IOException {
        Obligation proposal = null;
        for (Obligation row : RowCodec.readAll(obligations,
                ExploreCodec::readObligation)) {
            if (row.obligationId().equals(obligationId)) proposal = row;
        }
        if (proposal == null) {
            throw new IOException("the round has no obligation " + obligationId
                    + ": " + obligations);
        }
        return proposal;
    }

    /**
     * THE HARD LANE: one flip's ask at the full budget, z3 alone, over the
     * query its first ask published and the record beside it ({@link
     * HardAsk}), in a JVM that reads no corpus.  Its answer is mapped as the
     * corpus's ask maps one ({@code ObligationFactory#settled}) and published
     * into the worker as that ask publishes it: UNSAT settling its question,
     * or no verdict by name.  A sat answer leaves its model ({@link
     * HardAsk.Model}) and no answer: its host's solver finishes the flip.  A
     * record of another obligation or another query is refused by name
     * ({@link #HARD_ASK_MISMATCH}), with no z3 run.
     */
    static void decide(Path obligations, String obligationId, Path worker,
                       Path z3, long timeoutMillis, int z3RoomMb)
            throws IOException {
        Obligation proposal = proposal(obligations, obligationId);
        HardAsk ask = HardAsk.read(worker.resolve(HardAsk.FILE));
        // The query is streamed to z3, never held: a query past tens of MB
        // held twice over (its text and its body) outgrew the JVM's heap.
        Path query = worker.resolve(QUERY);
        byte[] suffix = Z3.modelQuery("", ask.modelSymbols)
                .getBytes(StandardCharsets.UTF_8);
        long body = Files.size(query) - suffix.length;
        String sha = ArtifactIO.sha256(query);
        if (!ask.obligationId.equals(obligationId)
                || !sha.equals(ask.querySha256) || !endsWith(query, suffix)) {
            String why = HARD_ASK_MISMATCH + ": the record of "
                    + ask.obligationId + " over query " + ask.querySha256
                    + " is not obligation " + obligationId + "'s query "
                    + sha;
            List<GapRow> gaps = new ArrayList<GapRow>(ask.gaps);
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, obligationId,
                    why));
            publish(worker, proposal, ObligationResult.of(obligationId,
                    Verdict.NOT_ADMITTED, "", why), null, gaps, null);
            return;
        }
        long budget = timeoutMillis <= 0 ? Z3.DEFAULT_TIMEOUT_MILLIS
                : timeoutMillis;
        Z3 solver = new Z3(z3, budget, z3RoomMb);
        Z3.Answer answer = solver.ask(output -> {
            try (java.io.Reader in = new java.io.InputStreamReader(
                    new java.io.BufferedInputStream(
                            new LimitedInput(Files.newInputStream(query),
                                    body)), StandardCharsets.UTF_8)) {
                char[] buffer = new char[1 << 16];
                for (int read; (read = in.read(buffer)) > 0; ) {
                    output.write(buffer, 0, read);
                }
            }
        }, ask.modelSymbols, false);
        // The query stays as its first ask published it.
        ObligationFactory.Outcome settled = ObligationFactory.settled(ask,
                answer, budget, solver, null);
        if (settled == null) {
            new HardAsk.Model(ask.querySha256, answer.values(), budget,
                    z3RoomMb).write(worker.resolve(HardAsk.Model.FILE));
            return;
        }
        publish(worker, proposal, settled.result, null, settled.gaps, null);
        if (settled.settles) {
            ask(worker.resolve(ObligationDir.QUESTION), settled.question);
        }
    }

    /** Whether the file ends with these bytes. */
    private static boolean endsWith(Path file, byte[] tail) throws IOException {
        long size = Files.size(file);
        if (size < tail.length) return false;
        try (java.nio.channels.FileChannel channel =
                     java.nio.channels.FileChannel.open(file)) {
            java.nio.ByteBuffer read = java.nio.ByteBuffer.allocate(
                    tail.length);
            channel.position(size - tail.length);
            while (read.hasRemaining() && channel.read(read) > 0) {
                continue;
            }
            return java.util.Arrays.equals(read.array(), tail);
        }
    }

    /** The first {@code limit} bytes of a stream. */
    private static final class LimitedInput extends java.io.FilterInputStream {
        private long left;

        LimitedInput(java.io.InputStream in, long limit) {
            super(in);
            this.left = limit;
        }

        @Override
        public int read() throws IOException {
            if (left <= 0) return -1;
            int value = super.read();
            if (value >= 0) left--;
            return value;
        }

        @Override
        public int read(byte[] buffer, int at, int length) throws IOException {
            if (left <= 0) return -1;
            int read = super.read(buffer, at, (int) Math.min(length, left));
            if (read > 0) left -= read;
            return read;
        }
    }

    /** A hard-lane record that does not belong to its worker's query. */
    static final String HARD_ASK_MISMATCH = "HARD_ASK_MISMATCH";

    /** The query a worker's ask published. */
    static final String QUERY = "obligation_query.smt2";

    /** A flip's focus row: the session its path ran in, by which a replay
     *  owed on a path whose session GROW withdrew is dropped ({@code
     *  run_engine.sh campaign_stream_replay_drop}). */
    static final String PATH_SESSION = "pathSessionId";

    /** Solves one published obligation over the corpus of {@code
     *  iteration} and writes every artifact of it; {@code decided}, the
     *  hard lane's model of its flip, finishes it without z3's verdict. */
    public static JsonObject solve(Corpus corpus, Path iteration,
                                   Path obligations, String obligationId,
                                   Path out, Path z3, long timeoutMillis,
                                   int z3RoomMb, HardAsk.Model decided)
            throws IOException {
        Files.createDirectories(out);
        Obligation proposal = proposal(obligations, obligationId);
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
                ObligationDir.answered(iteration), decided);
        if (!outcome.issued()) {
            JsonObject published = publish(out, proposal, outcome.result,
                    outcome.smt2, outcome.gaps, null);
            // Undecided at its budget: what its hard-lane ask reads.
            if (outcome.owed != null) {
                outcome.owed.write(out.resolve(HardAsk.FILE));
            }
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
        focus.addProperty(PATH_SESSION, candidate.path.sessionId);
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
        // Always written -- but by a hard-lane ask (null), which keeps its
        // first ask's: an UNSAT query is the one a reader most needs.
        if (smt2 != null) {
            Files.write(out.resolve(QUERY), (smt2.isEmpty()
                    ? "; no query was encoded: " + result.verdict() + " "
                    + result.detail() + System.lineSeparator()
                    : smt2).getBytes(StandardCharsets.UTF_8));
        }
        ExploreCodec.writeFocusFile(out.resolve(ObligationDir.FOCUSED_TASK),
                focus);
        return row;
    }
}
