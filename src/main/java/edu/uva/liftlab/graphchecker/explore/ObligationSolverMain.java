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
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.option.LongOptions;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
import edu.uva.liftlab.graphchecker.runtime.FocusedReplay;

import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.nio.charset.StandardCharsets;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
                    (int) options.number("seats", 1L),
                    answerer(sessions, rootDomains, z3, timeoutMillis,
                            new Z3.Rooms(z3RoomMb),
                            (int) options.number("question-room-mb",
                                    z3RoomMb),
                            options.number("retire-past-mb", 0L) << 20));
            return;
        }
        throw new IllegalArgumentException("--serve or --decide is required");
    }

    private static Service.Answerer answerer(Path sessions,
                                             Path rootDomains, Path z3,
                                             long timeoutMillis,
                                             Z3.Rooms rooms,
                                             int questionRoomMb,
                                             long retirePastBytes) {
        Path iteration = sessions.getParent();
        return new Service.Answerer() {
            private Corpus corpus;
            private final Map<String, Long> read =
                    new HashMap<String, Long>();

            @Override
            public void answer(JsonObject question, Path out)
                    throws Exception {
                Path obligations = Paths.get(JsonFields.primitiveString(
                        question, "obligations"));
                Corpus asked = current(question, obligations);
                String decided = JsonFields.optionalString(question,
                        "decided");
                HardAsk.Model model = decided.isEmpty() ? null
                        : HardAsk.Model.read(Paths.get(decided));
                asked.asking(() -> solve(asked, iteration, obligations,
                        JsonFields.primitiveString(question, "obligationId"),
                        out, new Z3(z3, timeoutMillis, rooms, questionRoomMb),
                        model));
            }

            private synchronized Corpus current(JsonObject question,
                                                Path obligations)
                    throws Exception {
                List<String> now = standing(sessions);
                if (corpus == null || stale(read.keySet(), now,
                        round(obligations, now))) {
                    Whole<Map<String, Long>> whole = readWhole(sessions, now,
                            standing -> {
                        Map<String, Long> reading =
                                new HashMap<String, Long>();
                        long bytes = 0L;
                        for (String name : standing) {
                            Long held = read.get(name);
                            long size = held != null ? held
                                    : bytes(sessions.resolve(name));
                            reading.put(name, size);
                            bytes += size;
                        }
                        if (retirePastBytes > 0L && bytes > retirePastBytes) {
                            throw new Service.Outgrown("its corpus is "
                                    + (bytes >> 20) + " MB of sessions, past "
                                    + "the " + (retirePastBytes >> 20)
                                    + " MB its heap was started for");
                        }
                        corpus = Corpus.read(iteration, rootDomains, corpus,
                                standing);
                        return reading;
                    });
                    read.clear();
                    read.putAll(whole.read);
                    stateLive(iteration, read);
                    if (!whole.left.isEmpty()) {
                        System.err.println("ObligationSolverMain: question "
                                + JsonFields.primitiveString(question,
                                "obligationId") + ": the corpus was read "
                                + whole.again + " time(s) more, GROW having "
                                + "withdrawn " + whole.left + " under the "
                                + "read");
                    }
                }
                return corpus;
            }
        };
    }

    static final String LIVE = "solver_live";

    static void stateLive(Path iteration, Map<String, Long> read) {
        long corpus = 0L;
        for (long bytes : read.values()) corpus += bytes;
        long live = HeapWatch.liveAfterCollection();
        String self = ManagementFactory.getRuntimeMXBean().getName()
                .replace('@', '.');
        try {
            Path dir = iteration.resolve(LIVE);
            Files.createDirectories(dir);
            ArtifactIO.replace(dir.resolve(self),
                    (live >> 20) + " " + (corpus >> 20) + "\n");
        } catch (IOException unstated) {
            System.err.println("ObligationSolverMain: its live set not "
                    + "stated: " + unstated);
        }
    }

    interface Reading<T> {
        T read(List<String> standing) throws Exception;
    }

    static final class Whole<T> {
        final T read;
        final Set<String> left;
        final int again;

        Whole(T read, Set<String> left, int again) {
            this.read = read;
            this.left = left;
            this.again = again;
        }
    }

    static <T> Whole<T> readWhole(Path sessions, List<String> now,
                                  Reading<T> reading) throws Exception {
        Path iteration = sessions.getParent();
        List<String> standing = now;
        Set<String> left = new LinkedHashSet<String>();
        for (int again = 0; ; again++) {
            T read;
            Set<String> gone;
            try {
                read = reading.read(standing);
            } catch (IOException failed) {
                gone = SessionDir.withdrawn(iteration);
                gone.retainAll(standing);
                if (gone.isEmpty()) throw failed;
                left.addAll(gone);
                standing = standing(sessions);
                continue;
            }
            gone = SessionDir.withdrawn(iteration);
            gone.retainAll(standing);
            if (gone.isEmpty()) return new Whole<T>(read, left, again);
            left.addAll(gone);
            standing = standing(sessions);
        }
    }

    static boolean stale(Set<String> read, List<String> now,
                         List<String> round) {
        return !read.containsAll(round) || !now.containsAll(read);
    }

    static final String ROUND_CORPUS = "corpus.txt";

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

    private static long bytes(Path session) throws IOException {
        long bytes = 0L;
        try (DirectoryStream<Path> files = Files.newDirectoryStream(session)) {
            for (Path file : files) {
                if (Files.isRegularFile(file)) {
                    bytes += ArtifactIO.decodedSize(file);
                }
            }
        }
        return bytes;
    }

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
        names.removeAll(SessionDir.withdrawn(sessions.getParent()));
        Collections.sort(names);
        return names;
    }

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

    static void decide(Path obligations, String obligationId, Path worker,
                       Path z3, long timeoutMillis, int z3RoomMb)
            throws IOException {
        Obligation proposal = proposal(obligations, obligationId);
        HardAsk ask = HardAsk.read(worker.resolve(HardAsk.FILE));
        Path query = worker.resolve(QUERY);
        byte[] suffix = Z3.modelQuery("", ask.modelSymbols)
                .getBytes(StandardCharsets.UTF_8);
        QueryText text = QueryText.of(query, suffix.length);
        long body = text.size - suffix.length;
        String sha = text.sha256;
        if (!ask.obligationId.equals(obligationId)
                || !sha.equals(ask.querySha256)
                || !java.util.Arrays.equals(text.tail, suffix)) {
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
        Z3.Answer answer = Solved.at(ask.solved).answer(ask.solvedKey,
                ask.modelSymbols, () -> solver.ask(
                        output -> body(query, body, output),
                        ask.modelSymbols, false));
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

    private static void body(Path query, long body, java.io.Writer output)
            throws IOException {
        try (java.io.Reader in = new java.io.InputStreamReader(
                new LimitedInput(ArtifactIO.input(query), body),
                StandardCharsets.UTF_8)) {
            char[] buffer = new char[1 << 16];
            for (int read; (read = in.read(buffer)) > 0; ) {
                output.write(buffer, 0, read);
            }
        }
    }

    static final class QueryText {
        final String sha256;
        final long size;
        final byte[] tail;

        private QueryText(String sha256, long size, byte[] tail) {
            this.sha256 = sha256;
            this.size = size;
            this.tail = tail;
        }

        static QueryText of(Path query, int tailLength) throws IOException {
            java.security.MessageDigest digest;
            try {
                digest = java.security.MessageDigest.getInstance("SHA-256");
            } catch (java.security.NoSuchAlgorithmException missing) {
                throw new IllegalStateException(missing);
            }
            byte[] tail = new byte[tailLength];
            long size = 0L;
            try (java.io.InputStream in = ArtifactIO.input(query)) {
                byte[] buffer = new byte[1 << 16];
                for (int read; (read = in.read(buffer)) > 0; ) {
                    digest.update(buffer, 0, read);
                    if (read >= tailLength) {
                        System.arraycopy(buffer, read - tailLength, tail, 0,
                                tailLength);
                    } else {
                        System.arraycopy(tail, read, tail, 0,
                                tailLength - read);
                        System.arraycopy(buffer, 0, tail, tailLength - read,
                                read);
                    }
                    size += read;
                }
            }
            if (size < tailLength) {
                tail = java.util.Arrays.copyOfRange(tail,
                        (int) (tailLength - size), tailLength);
            }
            return new QueryText(String.format("%064x",
                    new java.math.BigInteger(1, digest.digest())), size, tail);
        }
    }

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

    static final String HARD_ASK_MISMATCH = "HARD_ASK_MISMATCH";

    static final String QUERY = "obligation_query.smt2.gz";

    static final String PATH_SESSION = "pathSessionId";

    public static JsonObject solve(Corpus corpus, Path iteration,
                                   Path obligations, String obligationId,
                                   Path out, Path z3, long timeoutMillis,
                                   int z3RoomMb, HardAsk.Model decided)
            throws IOException {
        return corpus.asking(() -> solve(corpus, iteration, obligations,
                obligationId, out, new Z3(z3, timeoutMillis, z3RoomMb),
                decided));
    }

    static JsonObject solve(Corpus corpus, Path iteration, Path obligations,
                            String obligationId, Path out, Z3 solver,
                            HardAsk.Model decided) throws IOException {
        Files.createDirectories(out);
        Obligation proposal = proposal(obligations, obligationId);
        if (proposal.force()) {
            return force(corpus, iteration, obligations, proposal, out);
        }
        ObligationFactory.Candidate candidate =
                ObligationFactory.locate(corpus, proposal);
        if (candidate == null) {
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
        Path plan = iteration.resolve(PLAN);
        String given = "declared " + (declared == null ? ""
                : declared.render()) + "\nplan " + (Files.isRegularFile(plan)
                ? ArtifactIO.sha256(plan) : "");
        ObligationFactory.Outcome outcome = ObligationFactory.solve(corpus,
                candidate, solver, Solved.in(iteration), given,
                ObligationDir.answered(iteration), decided);
        if (!outcome.issued()) {
            JsonObject published = publish(out, proposal, outcome.result,
                    outcome.smt2, outcome.gaps, null);
            if (outcome.owed != null) {
                outcome.owed.write(out.resolve(HardAsk.FILE));
            }
            if (outcome.settles) {
                ask(out.resolve(ObligationDir.QUESTION), outcome.question);
            }
            return published;
        }
        List<String> cutAt = targetOccurrences(candidate);
        cutAt.addAll(outcome.holding.reordered);
        SchedulePrefix.Cut cut = SchedulePrefix.write(iteration,
                candidate.path.sessionId, cutAt, outcome.holding.cutBefore,
                true, out);
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
        if (outcome.openArm) focus.addProperty(FocusedReplay.OPEN_ARM, true);
        focus.addProperty(PATH_SESSION, candidate.path.sessionId);
        JsonObject published = publish(out, outcome.obligation,
                outcome.result, outcome.smt2, outcome.gaps, focus);
        ask(out.resolve(ObligationDir.QUESTION_ASKED), outcome.question);
        return published;
    }

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
        ask(out.resolve(ObligationDir.QUESTION_ASKED), ForcedFlip.flip(proposal)
                + ":" + ForcedFlip.FORCE + " " + proposal.obligationId());
        return published;
    }

    private static final String PLAN = "execution_task_plan.jsonl";

    private static void ask(Path file, String question) throws IOException {
        Files.write(file, (question + System.lineSeparator())
                .getBytes(StandardCharsets.UTF_8));
    }

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

    private static List<String> targetOccurrences(
            ObligationFactory.Candidate candidate) {
        List<String> ids = new ArrayList<String>();
        ids.add(candidate.path.occurrence.id());
        ids.addAll(targetOccurrences(candidate.task));
        return ids;
    }

    private static List<String> targetOccurrences(Task task) {
        List<String> ids = new ArrayList<String>();
        ids.add(task.focused().id());
        for (OccurrenceAddress member : task.factor()) ids.add(member.id());
        return ids;
    }

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
        RowCodec.writeAll(out.resolve(ObligationDir.GAPS),
                ExploreMain.distinct(new ArrayList<GapRow>(gaps)),
                RowCodec::writeGap);
        if (smt2 != null) {
            Files.write(out.resolve(QUERY), ArtifactIO.gzip((smt2.isEmpty()
                    ? "; no query was encoded: " + result.verdict() + " "
                    + result.detail() + System.lineSeparator()
                    : smt2).getBytes(StandardCharsets.UTF_8)));
        }
        ExploreCodec.writeFocusFile(out.resolve(ObligationDir.FOCUSED_TASK),
                focus);
        return row;
    }
}
