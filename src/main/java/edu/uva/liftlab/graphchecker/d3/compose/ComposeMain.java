package edu.uva.liftlab.graphchecker.d3.compose;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.plan.SelectorResolution;
import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.Claim;
import edu.uva.liftlab.graphchecker.d3.contract.ClaimKind;
import edu.uva.liftlab.graphchecker.d3.contract.CompositionManifest;
import edu.uva.liftlab.graphchecker.d3.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.NodeId;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.Role;
import edu.uva.liftlab.graphchecker.d3.contract.Selector;
import edu.uva.liftlab.graphchecker.d3.contract.RootDomain;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionReader;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * COMPOSE, SOLVE and DECIDE for one declared occurrence.
 *
 * <p>One anchor, one query, one claim.  There is no election to make and no
 * ranking to publish: which execution of the annotated site a campaign is
 * about is the case's declaration, and the claim about it is whatever its
 * own formula decided.  There is no VALIDATE stage behind it either (owner
 * ruling): the composed {@code .smt2} and z3's verdicts on it ARE the
 * deliverable, which is why the solving happens here rather than in a
 * separate pass over the artifact.</p>
 *
 * <pre>
 *   --sessions &lt;dir&gt;      the corpus (also: --iteration &lt;dir&gt;, its parent)
 *   --anchor &lt;addr&gt;       the declared occurrence (also: --target-occurrence)
 *   --output &lt;file&gt;       the composed query   (also: --out &lt;dir&gt;)
 *   --manifest &lt;file&gt;     the composition manifest
 *   --root-domains &lt;file&gt; what the CASE says each root may be
 *   --z3 &lt;path&gt;           default "z3"
 *   --max-valuations &lt;n&gt;  how many questions to ask, default 64
 *   --timeout-ms &lt;n&gt;      per solver run, default 20000
 *   --runtime-plan &lt;file&gt; accepted, not read (see the manifest note)
 *   --clock-skew-ms &lt;n&gt;   accepted, not read: a clock has a floor, no window
 * </pre>
 *
 * <p>Every outcome is an artifact.  A declared occurrence no session
 * reached, a corpus with no sessions, a root the case declares nothing
 * about -- each is written out as a claim with the gaps that explain it,
 * because a campaign that loses its answer to an exception has told the
 * reader nothing.  The exit code is 0 whenever the artifacts were written;
 * whether the claim is acceptable is the campaign's question, and it reads
 * it out of them.</p>
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
        OccurrenceAddress anchor = anchorOf(arguments.anchor, corpus);
        Composer.Composition composition = Composer.compose(corpus, anchor,
                declaredDomains(arguments.rootDomains),
                arguments.maxValuations);
        Solver solver = new Solver(arguments.z3, arguments.timeoutMillis);
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver);

        Solver.save(arguments.output, candidate(composition, decision));
        CompositionManifest composed = CompositionManifest.of(anchor,
                composition.paths(), composition.families(),
                composition.roots(), composition.valuations().size(),
                decision.claim(), arguments.output.toString());
        write(arguments.manifest,
                manifest(composed, composition, decision, solver));
        Path claimPath = arguments.manifest.resolveSibling("claim.json");
        write(claimPath, claim(composition, decision, solver));
        return new Result(arguments.output, arguments.manifest, claimPath,
                composed, decision,
                summary(anchor, composition, decision, solver));
    }

    /**
     * The occurrence the case declared: a full id, or a selector.
     *
     * <p>Humans do not write execution indexes.  A case declares the v1
     * spelling -- a node, a region, an api when the request matters, and
     * which of the matching activations -- and it is resolved HERE, against
     * the SEED session, because the seed is the recording the declaration
     * was written about.  What comes out is an OccurrenceId, and everything
     * downstream corresponds by that id alone.</p>
     *
     * <p>A selector that matches nothing is not an exception: it becomes a
     * degraded address of the region it names, which no session's rows will
     * equal, so the composition answers DECLARATION_MISSING and the campaign
     * reads why out of the artifact instead of out of a stack trace.</p>
     */
    static OccurrenceAddress anchorOf(String declared, CorpusIndex corpus) {
        String seed = corpus.seedSessionId();
        SessionReader session = seed == null ? null : corpus.session(seed);
        return SelectorResolution.resolve(declared,
                session == null ? null : session.activations());
    }

    /**
     * The composed query, at the valuation the run happened under.
     *
     * <p>One file, one named conjunct per assertion, so an unsat core reads
     * as the list of the things that closed it.  The other valuations
     * differ from this file by their {@code valuation__*} assertions alone,
     * and the manifest lists every one of them beside the verdict it got.</p>
     *
     * <p>A BLOCKED composition closes the question instead of leaving it
     * open.  A file with no path in it, or one whose claim a blocking gap
     * withheld, asserts nothing about the anchor -- and a query that
     * asserts nothing is satisfiable, so a reader who ran {@code z3} on the
     * file by hand read "sat" off a composition that had refused to answer.
     * The blocker is asserted false, so the file answers the way the claim
     * does, and it is NAMED in the comment beside it, so the reader gets the
     * reason and not just the verdict.</p>
     */
    static String candidate(Composer.Composition composition,
                            ClaimPolicy.Decision decision) {
        StringBuilder query = new StringBuilder(composition.body());
        if (!composition.valuations().isEmpty()) {
            query.append("; valuation 0: the run as it happened\n");
            for (String assertion
                    : composition.valuations().get(0).assertions()) {
                query.append(assertion).append('\n');
            }
        }
        String blocker = blocker(composition, decision);
        if (!blocker.isEmpty()) {
            query.append("(assert false) ; fail closed: ")
                    .append(blocker).append('\n');
        }
        return query.append("(check-sat)\n").toString();
    }

    /**
     * What closed this composition, as one comment line, or "".
     *
     * <p>The first BLOCKING gap, by the name it was recorded under: the
     * manifest and the claim carry every one of them, and this is the one
     * the file's own verdict is about.  A composition with no path and no
     * blocking gap is named by the declaration it reached nothing for,
     * because a refusal nobody can read is the silence the process rules
     * forbid.  CR and LF are folded to a space: the name rides in a
     * comment, and a comment is one line.</p>
     */
    private static String blocker(Composer.Composition composition,
                                  ClaimPolicy.Decision decision) {
        boolean pathless = composition.disjuncts().isEmpty();
        if (!pathless && !decision.claim().blocked()) return "";
        for (GapRow gap : decision.claim().gaps()) {
            if (!gap.blocking()) continue;
            return oneLine(gap.kind().name() + ":" + gap.subject());
        }
        return pathless
                ? oneLine(decision.claim().kind().name() + ":"
                + composition.anchor().render()) : "";
    }

    private static String oneLine(String text) {
        return text.replace('\r', ' ').replace('\n', ' ');
    }

    // ------------------------------------------------------------------
    // The manifest the campaign reads.
    // ------------------------------------------------------------------

    /**
     * The composition, its claim, and the verdicts the claim was read off.
     *
     * <p>The solver's answers live under {@code solver} in the one manifest
     * rather than in a second artifact: there is one anchor, so there is one
     * document, and a reader asking "why this claim" never has to join two
     * files to find out.</p>
     */
    private static JsonObject manifest(CompositionManifest composed,
                                       Composer.Composition composition,
                                       ClaimPolicy.Decision decision,
                                       Solver solver) {
        JsonObject row = GSON.toJsonTree(composed).getAsJsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "D3_COMPOSITION_MANIFEST");
        row.addProperty("anchor", composition.anchor().render());
        // The RESOLVED id, beside the render a human reads: exploration and
        // composition correspond by id, and a reader checking that two runs
        // anchored on the same occurrence compares this and nothing else.
        row.addProperty("anchorId", composition.anchor().id());
        row.addProperty("seedSessionId",
                composition.seedSessionId() == null ? ""
                        : composition.seedSessionId());
        // Every value in the formula was propagated inside some replay and
        // published as that replay's expression; a cut is named, and a path
        // that rests on one is not in the disjunction.
        row.addProperty("symbolicPropagationComplete",
                blocking(decision.claim()) == 0);
        row.addProperty("finalStatus", blocking(decision.claim()) == 0
                ? "FINAL_READY" : "FINAL_REFUSED");
        row.add("finalStatusRefusals", refusals(decision.claim()));
        row.add("gaps", gaps(composition.gaps()));
        row.add("solver", solverRows(composition, decision, solver));
        return row;
    }

    private static JsonObject solverRows(Composer.Composition composition,
                                         ClaimPolicy.Decision decision,
                                         Solver solver) {
        boolean decided = true;
        boolean anySat = false;
        String state = "unknown";
        for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
            if (!outcome.answer().decided()) decided = false;
            if (outcome.answer().sat()) anySat = true;
        }
        if (anySat) state = "sat";
        else if (decided && !decision.outcomes().isEmpty()) state = "unsat";
        JsonObject row = new JsonObject();
        row.addProperty("state", state);
        row.addProperty("reachability", anySat ? "EXACT_REACHABLE"
                : decided && !decision.outcomes().isEmpty()
                ? "NO_EXACT_REACHABILITY" : "UNKNOWN");
        row.addProperty("unsatClosureComplete",
                decided && !anySat && !decision.outcomes().isEmpty());
        row.addProperty("solverRuns", solver.runs());
        // A model of the declared roots, published without SMT terms.  The
        // valuation IS the model here: the composer asks one question per
        // valuation, so a satisfying answer names the values it was asked
        // about rather than values the solver chose.
        row.add("symbolicVariableModels",
                symbolicVariableModels(composition, decision));
        row.add("valuations", valuations(decision));
        row.add("campaignClaim", campaignClaim(decision, anySat, decided));
        return row;
    }

    /**
     * The claim, in the vocabulary acceptance is decided in.
     *
     * <p>Two questions, not one.  WHICH MECHANISM the formula supports is
     * the {@link ClaimKind}; WHETHER the run produced an accepted candidate
     * is this, and a blocking gap withholds it whatever the mechanism
     * was.</p>
     */
    private static JsonObject campaignClaim(ClaimPolicy.Decision decision,
                                            boolean anySat, boolean decided) {
        Claim claim = decision.claim();
        int blockers = blocking(claim);
        String kind;
        String reason;
        if (blockers > 0) {
            kind = "INCONCLUSIVE_PARTIAL";
            reason = "the composition named " + blockers
                    + " blocking gap(s); the claim it reached is "
                    + claim.kind();
        } else if (claim.kind() != ClaimKind.NO_SUPPORTED_WITNESS) {
            kind = "SAT_CANDIDATE";
            reason = "valuation " + claim.valuationOrdinal() + " reaches the"
                    + " fatal arm: " + claim.kind()
                    + (claim.movedRoots().isEmpty() ? ""
                    : " " + claim.movedRoots())
                    + (claim.polarityDecides()
                    ? ", and the recorded valuation refutes the recording"
                    : "");
        } else if (decided && !anySat && !decision.outcomes().isEmpty()) {
            kind = "UNSAT_CLOSED";
            reason = "every enumerated valuation is decided and unsat: the"
                    + " declared roots do not reach the fatal arm on the"
                    + " paths this corpus admits";
        } else {
            kind = "INCONCLUSIVE_PARTIAL";
            reason = decision.outcomes().isEmpty()
                    ? "no path of this corpus reached the declared"
                    + " occurrence"
                    : "the solver left a valuation undecided, so neither a"
                    + " witness nor a refutation is closed";
        }
        JsonObject row = new JsonObject();
        row.addProperty("claim", kind);
        row.addProperty("claimReason", reason);
        row.addProperty("findingKind", claim.kind().name());
        row.addProperty("valuationOrdinal", claim.valuationOrdinal());
        row.addProperty("polarityDecides", claim.polarityDecides());
        row.add("movedRoots", GSON.toJsonTree(claim.movedRoots()));
        row.add("blockers", refusals(claim));
        row.addProperty("blockerCount", blockers);
        row.addProperty("whyNotAccepted",
                "SAT_CANDIDATE".equals(kind) || "UNSAT_CLOSED".equals(kind)
                        ? "" : reason);
        JsonArray findings = new JsonArray();
        if (claim.kind() != ClaimKind.NO_SUPPORTED_WITNESS) {
            JsonObject finding = new JsonObject();
            finding.addProperty("findingKind", claim.kind().name());
            finding.addProperty("valuationOrdinal",
                    claim.valuationOrdinal());
            finding.add("movedRoots", GSON.toJsonTree(claim.movedRoots()));
            finding.addProperty("polarityDecides", claim.polarityDecides());
            findings.add(finding);
        }
        row.add("witnessFindings", findings);
        JsonObject rootSpace = new JsonObject();
        rootSpace.addProperty("acceptedFindingKind",
                claim.kind() == ClaimKind.NO_SUPPORTED_WITNESS ? ""
                        : claim.kind().name());
        rootSpace.add("reportedFindings", findings);
        row.add("rootSpace", rootSpace);
        return row;
    }

    private static JsonArray symbolicVariableModels(
            Composer.Composition composition,
            ClaimPolicy.Decision decision) {
        JsonArray models = new JsonArray();
        Claim claim = decision.claim();
        if (claim.kind() == ClaimKind.NO_SUPPORTED_WITNESS) return models;
        for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
            if (outcome.valuation().ordinal() != claim.valuationOrdinal()
                    || !outcome.answer().sat()) {
                continue;
            }
            JsonObject model = new JsonObject();
            model.addProperty("schemaVersion", 1);
            model.addProperty("kind", "SYMBOLIC_VARIABLE_MODEL");
            model.addProperty("valuationOrdinal",
                    outcome.valuation().ordinal());
            JsonArray variables = new JsonArray();
            for (Map.Entry<String, String> value
                    : outcome.valuation().assignment().entrySet()) {
                RootDomain domain = null;
                for (RootDomain candidate : composition.roots()) {
                    if (candidate.rootId().equals(value.getKey())) {
                        domain = candidate;
                        break;
                    }
                }
                JsonObject variable = new JsonObject();
                variable.addProperty("inputKind", "CONFIGURED_SOURCE_FIELD");
                variable.addProperty("sourceKey", value.getKey());
                variable.addProperty("sourceId", value.getKey());
                variable.addProperty("sourcePhaseId",
                        composition.anchor().render());
                variable.addProperty("fieldSignature", domain == null
                        ? value.getKey() : domain.kind().name());
                variable.addProperty("value", value.getValue());
                variables.add(variable);
            }
            model.add("variables", variables);
            models.add(model);
        }
        return models;
    }

    private static JsonArray valuations(ClaimPolicy.Decision decision) {
        JsonArray valuations = new JsonArray();
        for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
            JsonObject answer = new JsonObject();
            answer.addProperty("ordinal", outcome.valuation().ordinal());
            answer.addProperty("status", outcome.answer().status());
            answer.add("assignment",
                    GSON.toJsonTree(outcome.valuation().assignment()));
            answer.add("moved",
                    GSON.toJsonTree(outcome.valuation().moved()));
            answer.addProperty("selectedPathId", outcome.selected() == null
                    ? "" : outcome.selected().path().pathId());
            answer.addProperty("selectedSessionId",
                    outcome.selected() == null ? ""
                            : outcome.selected().path().sessionId());
            answer.addProperty("fatalObserved", outcome.selected() != null
                    && outcome.selected().fatalObserved());
            JsonArray core = new JsonArray();
            for (String name : outcome.answer().core()) core.add(name);
            answer.add("unsatCore", core);
            valuations.add(answer);
        }
        return valuations;
    }

    private static JsonObject claim(Composer.Composition composition,
                                    ClaimPolicy.Decision decision,
                                    Solver solver) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "D3_CLAIM");
        row.addProperty("anchor", composition.anchor().render());
        row.add("claim", GSON.toJsonTree(decision.claim()));
        row.addProperty("solverRuns", solver.runs());
        row.addProperty("seedSessionId",
                composition.seedSessionId() == null ? ""
                        : composition.seedSessionId());
        row.add("valuations", valuations(decision));
        row.add("gaps", gaps(decision.claim().gaps()));
        return row;
    }

    private static int blocking(Claim claim) {
        int blockers = 0;
        for (GapRow gap : claim.gaps()) {
            if (gap.cls() == GapClass.BLOCKING) blockers++;
        }
        return blockers;
    }

    private static JsonArray refusals(Claim claim) {
        JsonArray rows = new JsonArray();
        for (GapRow gap : claim.gaps()) {
            if (gap.cls() != GapClass.BLOCKING) continue;
            JsonObject row = new JsonObject();
            row.addProperty("kind", gap.kind().name());
            row.addProperty("subject", gap.subject());
            row.addProperty("detail", gap.detail());
            row.addProperty("sessionId", gap.sessionId());
            rows.add(row);
        }
        return rows;
    }

    private static JsonArray gaps(java.util.List<GapRow> gaps) {
        JsonArray rows = new JsonArray();
        for (GapRow gap : gaps) rows.add(RowCodec.writeGap(gap));
        return rows;
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
        if (file.getParent() != null) {
            Files.createDirectories(file.getParent());
        }
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

    /** The CLI, in both the campaign's spelling and the brief's. */
    public static final class Arguments {
        /** The iteration directory; {@code --sessions} names its child. */
        public Path iteration;
        public String anchor = "";
        public Path rootDomains;
        public int maxValuations = 64;
        public Path output;
        public Path manifest;
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
            // --sessions names <iteration>/sessions; --iteration names the
            // directory that holds it.  Both spellings, one corpus.
            Path sessions = path(values.get("sessions"));
            arguments.iteration = sessions != null
                    ? sessions.getParent() == null ? sessions
                    : sessions.getParent()
                    : path(values.get("iteration"));
            arguments.anchor = text(values, "anchor",
                    text(values, "target-occurrence", ""));
            arguments.rootDomains = path(values.get("root-domains"));
            arguments.z3 = values.containsKey("z3")
                    && !values.get("z3").isEmpty()
                    ? Paths.get(values.get("z3")) : Paths.get("z3");
            arguments.maxValuations = integer(values.get("max-valuations"),
                    64);
            arguments.timeoutMillis = integer(values.get("timeout-ms"),
                    20000);
            Path out = path(values.get("out"));
            arguments.output = path(values.get("output"));
            arguments.manifest = path(values.get("manifest"));
            if (out != null) {
                if (arguments.output == null) {
                    arguments.output = out.resolve("candidate.smt2");
                }
                if (arguments.manifest == null) {
                    arguments.manifest = out.resolve("manifest.json");
                }
            }
            if (arguments.iteration == null) {
                throw new IllegalArgumentException(
                        "--sessions (or --iteration) is required");
            }
            if (arguments.anchor.isEmpty()) {
                throw new IllegalArgumentException(
                        "--anchor (or --target-occurrence) is required: the"
                                + " declared occurrence is the anchor");
            }
            if (arguments.output == null || arguments.manifest == null) {
                throw new IllegalArgumentException(
                        "--output and --manifest (or --out) are required");
            }
            return arguments;
        }

        private static String text(Map<String, String> values, String key,
                                   String absent) {
            String value = values.get(key);
            return value == null || value.isEmpty() ? absent : value;
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
