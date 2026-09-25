package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.plan.SelectorResolution;
import edu.uva.liftlab.graphchecker.contract.Claim;
import edu.uva.liftlab.graphchecker.contract.ClaimKind;
import edu.uva.liftlab.graphchecker.contract.CompositionManifest;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.Z3;
import edu.uva.liftlab.graphchecker.explore.Corpus;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * COMPOSE, SOLVE and DECIDE for one declared occurrence: one anchor, one
 * query, one claim.  The {@code .smt2} and z3's verdicts on it ARE the
 * deliverable (no VALIDATE stage).
 *
 * <pre>
 *   --sessions &lt;dir&gt;      the corpus
 *   --anchor &lt;addr&gt;       the declared occurrence
 *   --output &lt;file&gt;       the composed query
 *   --manifest &lt;file&gt;     the composition manifest
 *   --root-domains &lt;file&gt; what the CASE says each root may be
 *   --z3 &lt;path&gt;           default "z3"
 *   --max-valuations &lt;n&gt;  how many questions to ask, default 64
 *   --solver-timeout-ms &lt;n&gt; per solver run, default 20000
 * </pre>
 *
 * <p>Every outcome, failures included, is written as a claim with its gaps,
 * never an exception; exit 0 means the artifacts were written, not that the
 * claim is acceptable.</p>
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
        // Root domains are read once, here, and handed to the composer only.
        Corpus corpus = Corpus.read(arguments.iteration, null);
        OccurrenceAddress anchor = anchorOf(arguments.anchor, corpus);
        Composer.Composition composition = Composer.compose(corpus, anchor,
                RootDomain.declared(arguments.rootDomains),
                arguments.maxValuations);
        Z3 solver = new Z3(arguments.z3, arguments.timeoutMillis);
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver);

        ArtifactIO.replace(arguments.output,
                candidate(composition, decision));
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
     * The declared occurrence (a full id, or a selector resolved against the
     * SEED session, the recording it was written about).  An unmatched
     * selector yields a degraded address, so the composition answers
     * DECLARATION_MISSING instead of throwing.
     */
    static OccurrenceAddress anchorOf(String declared, Corpus corpus) {
        String seed = corpus.seedSessionId();
        SessionReader session = seed.isEmpty() ? null : corpus.session(seed);
        return SelectorResolution.resolve(declared,
                session == null ? null : session.activations());
    }

    /**
     * The composed query at valuation 0 (the run as it happened); other
     * valuations differ only in their {@code valuation__*} assertions.  A
     * BLOCKED or pathless composition asserts false with the blocker named,
     * since an empty query would read "sat" by hand.
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
        if (!decision.outcomes().isEmpty()
                && !decision.outcomes().get(0).pinned().isEmpty()) {
            query.append("; held at the recording: the clocks the witness "
                    + "does not need, and each path's own pairing where the "
                    + "recording decides the arm\n");
            for (String pin : decision.outcomes().get(0).pinned()) {
                query.append(pin).append('\n');
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
     * What closed this composition as one comment line, or "": the first
     * BLOCKING gap, else (pathless) the claim kind and anchor.
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

    /** The composition, its claim, and the solver verdicts, in one document. */
    private static JsonObject manifest(CompositionManifest composed,
                                       Composer.Composition composition,
                                       ClaimPolicy.Decision decision,
                                       Z3 solver) {
        JsonObject row = GSON.toJsonTree(composed).getAsJsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "COMPOSITION_MANIFEST");
        row.addProperty("anchor", composition.anchor().render());
        // Runs correspond by the RESOLVED id, not the render.
        row.addProperty("anchorId", composition.anchor().id());
        row.addProperty("seedSessionId",
                composition.seedSessionId() == null ? ""
                        : composition.seedSessionId());
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
                                         Z3 solver) {
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
        // One question per valuation, so the valuation IS the model.
        row.add("valuations", valuations(decision));
        row.add("campaignClaim", campaignClaim(decision, anySat, decided));
        return row;
    }

    /**
     * WHETHER the run produced an accepted candidate (the {@link ClaimKind}
     * says which mechanism); a blocking gap withholds it regardless.
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
        return row;
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
                    ? "" : outcome.selected().path().pathId);
            answer.addProperty("selectedSessionId",
                    outcome.selected() == null ? ""
                            : outcome.selected().path().sessionId);
            answer.addProperty("fatalObserved", outcome.selected() != null
                    && outcome.selected().fatalObserved());
            // The arm of each family the model took: the causal chain.
            JsonArray arms = new JsonArray();
            for (Map.Entry<String, ComposedFamilies.ArmChoice> taken
                    : outcome.selectedArms().entrySet()) {
                ComposedFamilies.ArmChoice arm = taken.getValue();
                JsonObject row = new JsonObject();
                row.addProperty("selector", taken.getKey());
                row.addProperty("family", arm.family());
                row.addProperty("groupId", arm.groupId());
                JsonArray ports = new JsonArray();
                for (String port : arm.attachEndpointIds()) ports.add(port);
                row.add("attachEndpointIds", ports);
                row.addProperty("sessionId", arm.sessionId());
                JsonArray sessions = new JsonArray();
                for (String session : arm.sessionIds()) sessions.add(session);
                row.add("sessionIds", sessions);
                row.addProperty("producerPathId", arm.producerPathId());
                JsonArray slots = new JsonArray();
                for (String slot : arm.interactionIds()) slots.add(slot);
                row.add("interactionIds", slots);
                JsonArray refs = new JsonArray();
                for (String ref : arm.expressionRefs()) refs.add(ref);
                row.add("expressionRefs", refs);
                row.addProperty("attested", arm.attested());
                arms.add(row);
            }
            answer.add("selectedArms", arms);
            JsonArray core = new JsonArray();
            for (String name : outcome.answer().core()) core.add(name);
            answer.add("unsatCore", core);
            valuations.add(answer);
        }
        return valuations;
    }

    private static JsonObject claim(Composer.Composition composition,
                                    ClaimPolicy.Decision decision,
                                    Z3 solver) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "CLAIM");
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
                                  Z3 solver) {
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

    /** The CLI: one spelling per option, the one the campaign passes. */
    public static final class Arguments {
        /** The iteration directory; {@code --sessions} names its child. */
        public Path iteration;
        public String anchor = "";
        public Path rootDomains;
        public int maxValuations = 64;
        public Path output;
        public Path manifest;
        public Path z3 = Paths.get("z3");
        public long timeoutMillis = Z3.DEFAULT_TIMEOUT_MILLIS;

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
            // --sessions names <iteration>/sessions; one spelling per option.
            Path sessions = path(values.get("sessions"));
            arguments.iteration = sessions == null ? null
                    : sessions.getParent() == null ? sessions
                    : sessions.getParent();
            arguments.anchor = text(values, "anchor", "");
            arguments.rootDomains = path(values.get("root-domains"));
            arguments.z3 = values.containsKey("z3")
                    && !values.get("z3").isEmpty()
                    ? Paths.get(values.get("z3")) : Paths.get("z3");
            arguments.maxValuations = integer(values.get("max-valuations"),
                    64);
            arguments.timeoutMillis = integer(
                    values.get("solver-timeout-ms"),
                    (int) Z3.DEFAULT_TIMEOUT_MILLIS);
            arguments.output = path(values.get("output"));
            arguments.manifest = path(values.get("manifest"));
            if (arguments.iteration == null) {
                throw new IllegalArgumentException("--sessions is required");
            }
            if (arguments.anchor.isEmpty()) {
                throw new IllegalArgumentException(
                        "--anchor is required: the declared occurrence is"
                                + " the anchor");
            }
            if (arguments.output == null || arguments.manifest == null) {
                throw new IllegalArgumentException(
                        "--output and --manifest are required");
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

        /** One numeric option; a passed non-number is refused, never defaulted. */
        private static int integer(String value, int absent) {
            if (value == null || value.isEmpty()) return absent;
            try {
                return Integer.parseInt(value.trim());
            } catch (NumberFormatException notAnInteger) {
                throw new IllegalArgumentException("this bound was passed as"
                        + " \"" + value + "\", which is not a number: a"
                        + " mistyped bound is refused, never read as the"
                        + " default " + absent, notAnInteger);
            }
        }
    }

    private static final Gson GSON = new GsonBuilder()
            .setPrettyPrinting().create();
}
