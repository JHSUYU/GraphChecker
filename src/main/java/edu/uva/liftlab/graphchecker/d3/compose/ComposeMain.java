package edu.uva.liftlab.graphchecker.d3.compose;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.CompositionManifest;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.RootDomain;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * COMPOSE and DECIDE for one declared occurrence.
 *
 * <pre>
 *   --iteration &lt;dir&gt;            the corpus: &lt;dir&gt;/sessions/&lt;id&gt;/...
 *   --target-occurrence &lt;addr&gt;   the anchor, v2 or v1 spelling
 *   --root-domains &lt;file&gt;        what the CASE says each root may be
 *   --max-valuations &lt;n&gt;         how many questions to ask
 *   --out &lt;dir&gt;                  candidate.smt2, manifest.json, claim.json
 *   --z3 &lt;path&gt;                  default "z3"
 *   --timeout-ms &lt;n&gt;             per solver run, default 20000
 * </pre>
 *
 * <p>Every outcome is an artifact.  A declared occurrence no session
 * reached, a corpus with no sessions, a root the case declares nothing
 * about -- each is written out as a claim with the gaps that explain it,
 * because a campaign that loses its answer to an exception has told the
 * reader nothing.</p>
 */
public final class ComposeMain {

    private ComposeMain() {
    }

    public static void main(String[] argv) throws IOException {
        Arguments arguments = Arguments.parse(argv);
        Result result = run(arguments);
        System.out.println(result.summary);
    }

    /** What one run wrote, for a caller inside the JVM. */
    public static final class Result {
        public final Path smt2;
        public final Path manifest;
        public final Path claim;
        public final CompositionManifest composed;
        public final ClaimPolicy.Decision decision;
        public final String summary;

        Result(Path smt2, Path manifest, Path claim,
               CompositionManifest composed, ClaimPolicy.Decision decision,
               String summary) {
            this.smt2 = smt2;
            this.manifest = manifest;
            this.claim = claim;
            this.composed = composed;
            this.decision = decision;
            this.summary = summary;
        }
    }

    public static Result run(Arguments arguments) throws IOException {
        CorpusIndex corpus = CorpusIndex.of(arguments.iteration);
        OccurrenceAddress anchor =
                OccurrenceAddress.parse(arguments.targetOccurrence);
        Composer.Composition composition = Composer.compose(corpus, anchor,
                declaredDomains(arguments.rootDomains),
                arguments.maxValuations);
        Solver solver = new Solver(arguments.z3, arguments.timeoutMillis);
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver);

        Files.createDirectories(arguments.out);
        Path smt2 = arguments.out.resolve("candidate.smt2");
        Solver.save(smt2, candidate(composition));
        CompositionManifest manifest = CompositionManifest.of(anchor,
                composition.paths(), composition.families(),
                composition.roots(), composition.valuations().size(),
                decision.claim(), smt2.toString());
        Path manifestPath = arguments.out.resolve("manifest.json");
        write(manifestPath, GSON.toJsonTree(manifest).getAsJsonObject());
        Path claimPath = arguments.out.resolve("claim.json");
        write(claimPath, claimRows(composition, decision, solver));
        return new Result(smt2, manifestPath, claimPath, manifest, decision,
                summary(anchor, composition, decision, solver));
    }

    /**
     * The composed query, at the valuation the run happened under.
     *
     * <p>One file, one named conjunct per assertion, so an unsat core reads
     * as the list of the things that closed it.  The other valuations
     * differ from this file by their {@code valuation__*} assertions alone,
     * and the manifest lists them.</p>
     */
    private static String candidate(Composer.Composition composition) {
        StringBuilder query = new StringBuilder(composition.body());
        if (!composition.valuations().isEmpty()) {
            query.append("; valuation 0: the run as it happened\n");
            for (String assertion
                    : composition.valuations().get(0).assertions()) {
                query.append(assertion).append('\n');
            }
        }
        return query.append("(check-sat)\n").toString();
    }

    private static JsonObject claimRows(Composer.Composition composition,
                                        ClaimPolicy.Decision decision,
                                        Solver solver) {
        JsonObject row = new JsonObject();
        row.addProperty("anchor", composition.anchor().render());
        row.add("claim", GSON.toJsonTree(decision.claim()));
        row.addProperty("solverRuns", solver.runs());
        row.addProperty("seedSessionId",
                composition.seedSessionId() == null ? ""
                        : composition.seedSessionId());
        JsonArray valuations = new JsonArray();
        for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
            JsonObject answer = new JsonObject();
            answer.addProperty("ordinal", outcome.valuation().ordinal());
            answer.addProperty("status", outcome.answer().status());
            answer.add("moved",
                    GSON.toJsonTree(outcome.valuation().moved()));
            answer.addProperty("selectedPathId", outcome.selected() == null
                    ? "" : outcome.selected().path().pathId());
            answer.addProperty("selectedSessionId", outcome.selected() == null
                    ? "" : outcome.selected().path().sessionId());
            answer.addProperty("fatalObserved", outcome.selected() != null
                    && outcome.selected().fatalObserved());
            JsonArray core = new JsonArray();
            for (String name : outcome.answer().core()) core.add(name);
            answer.add("unsatCore", core);
            valuations.add(answer);
        }
        row.add("valuations", valuations);
        JsonArray gaps = new JsonArray();
        for (GapRow gap : decision.claim().gaps()) {
            gaps.add(RowCodec.writeGap(gap));
        }
        row.add("gaps", gaps);
        return row;
    }

    private static String summary(OccurrenceAddress anchor,
                                  Composer.Composition composition,
                                  ClaimPolicy.Decision decision,
                                  Solver solver) {
        return "anchor " + anchor.render()
                + " paths=" + composition.paths().size()
                + " families=" + composition.families().size()
                + " roots=" + composition.roots().size()
                + " valuations=" + composition.valuations().size()
                + " solverRuns=" + solver.runs()
                + " claim=" + decision.claim().kind()
                + (decision.claim().blocked() ? " BLOCKED" : "")
                + " gaps=" + decision.claim().gaps().size();
    }

    private static void write(Path file, JsonObject row) throws IOException {
        Files.write(file, (GSON.toJson(row) + "\n")
                .getBytes(StandardCharsets.UTF_8));
    }

    /**
     * What the CASE says each of its roots may be.
     *
     * <p>One JSONL row per root: {@code rootId} (or {@code symbol}) and the
     * two bounds, in either spelling and either form -- an absolute value,
     * or {@code +k}/{@code -k} steps from what the recording read.  The
     * recording says what a root WAS; only the case can say what else it
     * could have been, so the two are joined rather than either overwriting
     * the other.</p>
     */
    static Map<String, RootDomain> declaredDomains(Path file)
            throws IOException {
        Map<String, RootDomain> domains =
                new LinkedHashMap<String, RootDomain>();
        if (file == null || !Files.isRegularFile(file)) return domains;
        for (JsonObject row : RowCodec.readJsonl(file)) {
            String key = JsonText.firstNonBlank(
                    JsonText.string(row, "rootId"),
                    JsonText.string(row, "symbol"),
                    JsonText.string(row, "sourceId"));
            if (key.isEmpty()) continue;
            String min = JsonText.firstNonBlank(
                    JsonText.string(row, "min"),
                    JsonText.string(row, "declaredDomainMin"));
            String max = JsonText.firstNonBlank(
                    JsonText.string(row, "max"),
                    JsonText.string(row, "declaredDomainMax"));
            domains.put(key, RootDomain.of(key, RootKind.INTEGRAL, "",
                    min.isEmpty() ? null : min,
                    max.isEmpty() ? null : max));
        }
        return domains;
    }

    /** The CLI. */
    public static final class Arguments {
        public Path iteration;
        public String targetOccurrence = "";
        public Path rootDomains;
        public int maxValuations = 64;
        public Path out;
        public Path z3 = Paths.get("z3");
        public long timeoutMillis = 20000L;

        public static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<String, String>();
            for (int index = 0; index < argv.length; index++) {
                String key = argv[index];
                if (!key.startsWith("--")) continue;
                String name = key.substring(2);
                String value = index + 1 < argv.length
                        && !argv[index + 1].startsWith("--")
                        ? argv[++index] : "";
                values.put(name, value);
            }
            Arguments arguments = new Arguments();
            arguments.iteration = path(values.get("iteration"));
            arguments.targetOccurrence = values.containsKey(
                    "target-occurrence")
                    ? values.get("target-occurrence") : "";
            arguments.rootDomains = path(values.get("root-domains"));
            arguments.out = path(values.get("out"));
            arguments.z3 = values.containsKey("z3")
                    && !values.get("z3").isEmpty()
                    ? Paths.get(values.get("z3")) : Paths.get("z3");
            arguments.maxValuations = integer(values.get("max-valuations"),
                    64);
            arguments.timeoutMillis = integer(values.get("timeout-ms"),
                    20000);
            if (arguments.iteration == null) {
                throw new IllegalArgumentException("--iteration is required");
            }
            if (arguments.targetOccurrence.isEmpty()) {
                throw new IllegalArgumentException(
                        "--target-occurrence is required");
            }
            if (arguments.out == null) {
                throw new IllegalArgumentException("--out is required");
            }
            return arguments;
        }

        private static Path path(String value) {
            return value == null || value.isEmpty() ? null
                    : Paths.get(value);
        }

        private static int integer(String value, int absent) {
            if (value == null || value.isEmpty()) return absent;
            try {
                return Integer.parseInt(value.trim());
            } catch (NumberFormatException notAnInteger) {
                return absent;
            }
        }
    }

    private static final Gson GSON = new GsonBuilder()
            .setPrettyPrinting().create();
}
