package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import edu.uva.liftlab.graphchecker.option.LongOptions;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.io.Reader;
import java.nio.charset.StandardCharsets;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * IMPORT's gate: the row contract, checked once per session before any stage
 * reads its rows.
 *
 * <pre>
 *   --iteration &lt;dir&gt;      the epoch's iteration directory: its
 *                          withdrawn.txt names the sessions GROW's swaps took
 *                          out of the epoch
 *   --gate-list &lt;file&gt;     the sessions to gate, one per line: the
 *                          session's directory, wherever it is staged (in
 *                          the corpus, or in the worker that replayed it,
 *                          before it lands), and, each a tab after it, the
 *                          obligation workers whose answers name it, in
 *                          wave and name order -- their focus rows are the
 *                          ask its session ran under and the flips it owes;
 *                          none for the seed
 *   --replaced &lt;file&gt;     the sessions the ones gated now replace, one id
 *                          per line: GROW's exposing sessions, each swapped
 *                          out once its re-run's session is gated (and named
 *                          in withdrawn.txt then); none: no session
 *   --gated &lt;dir&gt;          the ledger: what each session gated before left
 *                          the gate ({@link RowInvariants.Gated}), one
 *                          record per session, read, and written for the
 *                          ones gated now; none: no session was, and none is
 *                          recorded
 *   --out &lt;file&gt;           campaign_gaps.jsonl, appended to
 *   --topology-epoch &lt;id&gt;  the epoch these sessions belong to
 * </pre>
 *
 * <p>A session is judged once: one the ledger holds is not judged again, and
 * the rules over the set are judged against the sessions the ledger holds
 * that are still in the epoch -- every one but those GROW withdrew -- by what
 * each left the gate, never by reading it again ({@link
 * RowInvariants#check}): a gate's cost is its own sessions'.  Appends every
 * violation, records the sessions gated now, and prints a summary of this
 * gate's own sessions; the stage fails on BLOCKING &gt; 0.  Exits 0 whatever it
 * found (the gate reports, the stage decides), nonzero only if a session is
 * unreadable.  Append-only: an overwritten gap row was never evidence.</p>
 */
public final class ImportGateMain {
    /** A gated session's record in the ledger: whether it states SEED and
     *  the roots it mints. */
    static final String RECORD = ".json";
    /** The symbols it names, each with one citation. */
    static final String NAMED = ".named.json.gz";

    private ImportGateMain() {
    }

    public static void main(String[] argv) throws Exception {
        LongOptions options = LongOptions.parse(argv);
        Path iteration = options.path("iteration");
        if (iteration == null) {
            throw new IllegalArgumentException("Missing --iteration");
        }
        Path list = options.path("gate-list");
        if (list == null) {
            throw new IllegalArgumentException("Missing --gate-list");
        }
        Path out = options.path("out");
        if (out == null) {
            throw new IllegalArgumentException("Missing --out");
        }
        Path replaced = options.path("replaced");
        JsonObject summary = gate(iteration, gates(list),
                replaced == null ? Collections.<String>emptySet()
                        : new HashSet<String>(Files.readAllLines(replaced,
                                StandardCharsets.UTF_8)),
                options.path("gated"), out,
                options.value("topology-epoch", ""));
        System.out.println(new GsonBuilder().disableHtmlEscaping()
                .setPrettyPrinting().create().toJson(summary));
    }

    /** One session to gate: its directory, and the workers whose answers
     *  name it (none for the seed). */
    public static final class Gate {
        final Path session;
        final List<Path> workers;

        public Gate(Path session, List<Path> workers) {
            this.session = session;
            this.workers = workers;
        }
    }

    /** The lines of a gate list ({@code --gate-list}). */
    static List<Gate> gates(Path list) throws IOException {
        List<Gate> gates = new ArrayList<Gate>();
        for (String line : Files.readAllLines(list, StandardCharsets.UTF_8)) {
            if (line.trim().isEmpty()) continue;
            String[] fields = line.split("\t", -1);
            List<Path> workers = new ArrayList<Path>();
            for (int at = 1; at < fields.length; at++) {
                if (!fields[at].isEmpty()) workers.add(Paths.get(fields[at]));
            }
            gates.add(new Gate(Paths.get(fields[0]), workers));
        }
        return gates;
    }

    /**
     * Gates the sessions {@code gates} names of one epoch (each one the
     * ledger does not hold yet), appends their violations, records them in
     * the ledger, and reports the counts.  They are judged against the
     * sessions the ledger holds that are still in the epoch: neither
     * withdrawn nor {@code replaced} by one of them (a re-run's session is
     * gated before its swap withdraws the session it replaces, and the two
     * are never in the epoch together).
     */
    public static JsonObject gate(Path iteration, List<Gate> gates,
                                  Set<String> replaced, Path ledger,
                                  Path out, String topologyEpoch)
            throws IOException {
        Set<String> before = ledger == null ? Collections.<String>emptySet()
                : recorded(ledger);
        List<SessionDir> gated = new ArrayList<SessionDir>();
        Map<String, List<JsonObject>> focus =
                new LinkedHashMap<String, List<JsonObject>>();
        Set<String> named = new LinkedHashSet<String>();
        for (Gate gate : gates) {
            SessionDir dir = SessionDir.at(gate.session);
            if (before.contains(dir.sessionId())
                    || !named.add(dir.sessionId())) {
                continue;
            }
            if (!Files.isDirectory(dir.dir())) {
                throw new NoSuchFileException(dir.dir().toString(), null,
                        "a session named to the gate is not there");
            }
            gated.add(dir);
            // Its focus rows, by the session each worker's own result row
            // names (never a directory name): the first is the ask its
            // session ran under (invariant 6), each one a flip it owes (10).
            for (Path asked : gate.workers) {
                ObligationDir worker = ObligationDir.of(asked);
                if (!dir.sessionId().equals(worker.sessionId())) {
                    throw new IllegalArgumentException("the worker " + asked
                            + " names session " + worker.sessionId()
                            + ", not " + dir.sessionId());
                }
                focus.computeIfAbsent(dir.sessionId(),
                        key -> new ArrayList<JsonObject>())
                        .addAll(worker.focus());
            }
        }
        Set<String> withdrawn = SessionDir.withdrawn(iteration);
        List<RowInvariants.Gated> admitted =
                new ArrayList<RowInvariants.Gated>();
        for (String id : before) {
            if (!withdrawn.contains(id) && !replaced.contains(id)) {
                admitted.add(record(ledger, id));
            }
        }
        RowInvariants.Checked checked = RowInvariants.check(admitted, gated,
                focus);

        StringBuilder text = new StringBuilder();
        int blocking = 0;
        String first = "";
        JsonArray blockers = new JsonArray();
        Map<String, Integer> byKind = new LinkedHashMap<String, Integer>();
        for (GapRow gap : checked.gaps) {
            if (gap.blocking()) {
                blocking++;
                if (first.isEmpty()) first = gap.subject();
                if (blockers.size() < 8) blockers.add(gap.subject());
            }
            byKind.merge(gap.kind().name(), 1, Integer::sum);
            JsonObject row = RowCodec.writeGap(gap);
            row.addProperty("topologyEpoch", topologyEpoch);
            text.append(RowCodec.toLine(row)).append(System.lineSeparator());
        }
        append(out, text);
        if (ledger != null) {
            for (RowInvariants.Judged judged : checked.judged) {
                record(ledger, judged);
            }
        }
        JsonObject summary = new JsonObject();
        summary.addProperty("topologyEpoch", topologyEpoch);
        summary.addProperty("sessions", gated.size());
        summary.addProperty("violations", checked.gaps.size());
        summary.addProperty("blocking", blocking);
        summary.addProperty("diagnostic", checked.gaps.size() - blocking);
        summary.addProperty("firstBlockingSubject", first);
        JsonObject kinds = new JsonObject();
        for (Map.Entry<String, Integer> entry : byKind.entrySet()) {
            kinds.addProperty(entry.getKey(), entry.getValue());
        }
        summary.add("gaps", kinds);
        summary.add("blockingSubjects", blockers);
        return summary;
    }

    /** The sessions the ledger holds a record of, in name order. */
    static Set<String> recorded(Path ledger) throws IOException {
        List<String> ids = new ArrayList<String>();
        if (!Files.isDirectory(ledger)) return new LinkedHashSet<String>();
        try (DirectoryStream<Path> entries =
                     Files.newDirectoryStream(ledger, "*" + RECORD)) {
            for (Path entry : entries) {
                String name = entry.getFileName().toString();
                ids.add(name.substring(0, name.length() - RECORD.length()));
            }
        }
        Collections.sort(ids);
        return new LinkedHashSet<String>(ids);
    }

    /** What session {@code id} left the gate, read from the ledger: its
     *  record now, the symbols it named when a gate needs them. */
    static RowInvariants.Gated record(Path ledger, String id)
            throws IOException {
        JsonObject record = parse(ledger.resolve(id + RECORD));
        boolean seed = record.get("seed").getAsBoolean();
        Map<String, String> roots = new LinkedHashMap<String, String>();
        for (JsonElement root : record.getAsJsonArray("roots")) {
            JsonArray pair = root.getAsJsonArray();
            roots.put(pair.get(0).getAsString(), pair.get(1).getAsString());
        }
        Map<String, String> fixed = Collections.unmodifiableMap(roots);
        Path named = ledger.resolve(id + NAMED);
        return new RowInvariants.Gated() {
            @Override
            public String sessionId() {
                return id;
            }

            @Override
            public boolean seed() {
                return seed;
            }

            @Override
            public Map<String, String> roots() {
                return fixed;
            }

            @Override
            public Map<String, String> named() throws IOException {
                Map<String, String> where =
                        new LinkedHashMap<String, String>();
                for (Map.Entry<String, JsonElement> entry
                        : parse(named).entrySet()) {
                    where.put(entry.getKey(), entry.getValue().getAsString());
                }
                return where;
            }
        };
    }

    /** One session's record into the ledger: what it names first, its
     *  record last, each whole, so a record there is a session gated. */
    static void record(Path ledger, RowInvariants.Judged judged)
            throws IOException {
        JsonObject named = new JsonObject();
        for (Map.Entry<String, String> entry : judged.named().entrySet()) {
            named.addProperty(entry.getKey(), entry.getValue());
        }
        byte[] text = (named + "\n").getBytes(StandardCharsets.UTF_8);
        ArtifactIO.atomicWrite(ledger.resolve(judged.sessionId() + NAMED),
                output -> output.write(ArtifactIO.gzip(text)));
        JsonObject record = new JsonObject();
        record.addProperty("sessionId", judged.sessionId());
        record.addProperty("seed", judged.seed());
        JsonArray roots = new JsonArray();
        for (Map.Entry<String, String> root : judged.roots().entrySet()) {
            JsonArray pair = new JsonArray();
            pair.add(root.getKey());
            pair.add(root.getValue());
            roots.add(pair);
        }
        record.add("roots", roots);
        ArtifactIO.replace(ledger.resolve(judged.sessionId() + RECORD),
                record + "\n");
    }

    private static JsonObject parse(Path file) throws IOException {
        try (Reader in = ArtifactIO.lines(file)) {
            return JsonParser.parseReader(in).getAsJsonObject();
        }
    }

    /** Appends {@code text} to {@code file}; nothing, not even the file,
     *  when there is none. */
    private static void append(Path file, CharSequence text)
            throws IOException {
        if (text.length() == 0) return;
        if (file.getParent() != null) {
            Files.createDirectories(file.getParent());
        }
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE, StandardOpenOption.APPEND);
    }
}
