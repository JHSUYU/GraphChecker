package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.plan.SelectorResolution;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.contract.Claim;
import edu.uva.liftlab.graphchecker.contract.ClaimKind;
import edu.uva.liftlab.graphchecker.contract.CompositionManifest;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.Z3;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.option.LongOptions;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
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
 *   --static-scope-map &lt;file&gt; the epoch's static facts: where a
 *                          reference write's construction guard is
 *   --z3 &lt;path&gt;           default "z3"
 *   --max-valuations &lt;n&gt;  how many questions to ask, default 64
 *   --solver-timeout-ms &lt;n&gt; per solver run, default 20000
 * </pre>
 *
 * <p>Parsed by {@link LongOptions}.  Every outcome, failures included, is written as a claim with its gaps,
 * never an exception; exit 0 means the artifacts were written, not that the
 * claim is acceptable.</p>
 */
public final class ComposeMain {
    /** A selected arm's member: consumer endpoint id -> the text the model
     *  delivers there, for each held leaf ({@link ComposedFamilies#texts}). */
    public static final String TEXTS = "texts";

    private ComposeMain() {
    }

    public static void main(String[] argv) throws IOException {
        System.out.println(run(Arguments.parse(argv)));
    }

    /** Writes the query, the manifest and the claim; answers one summary line. */
    static String run(Arguments arguments) throws IOException {
        long started = System.nanoTime();
        // Root domains are read once, here, and handed to the composer only.
        Corpus corpus = Corpus.read(arguments.iteration, null);
        System.err.println("compose: read " + corpus.sessions().size()
                + " session(s) in " + seconds(System.nanoTime() - started)
                + " s");
        OccurrenceAddress anchor = anchorOf(arguments.anchor, corpus);
        Composer.Composition composition = Composer.compose(corpus, anchor,
                RootDomain.declared(arguments.rootDomains),
                arguments.maxValuations,
                StaticScopeMap.read(arguments.scopeMap));
        long lowered = System.nanoTime();
        System.err.println("compose: " + composition.disjuncts().size()
                + " path(s) composed, a " + composition.body().length()
                / (1024 * 1024) + " MB body and " + composition.valuations()
                .size() + " valuation(s), in " + seconds(lowered - started)
                + " s; deciding");
        Z3 solver = new Z3(arguments.z3, arguments.timeoutMillis);
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver);
        long decided = System.nanoTime();
        System.err.println("compose: decided " + decision.claim().kind()
                + " with " + solver.runs() + " z3 run(s) in "
                + seconds(decided - lowered) + " s");

        ArtifactIO.atomicReplace(arguments.output,
                candidate(composition, decision));
        CompositionManifest composed = CompositionManifest.of(anchor,
                composition.paths(), composition.families(),
                composition.roots(), composition.valuations().size(),
                decision.claim(), arguments.output.toString());
        write(arguments.manifest,
                manifest(composed, composition, decision, solver));
        write(arguments.manifest.resolveSibling("claim.json"),
                claim(composition, decision, solver));
        return summary(anchor, composition, decision, solver)
                + " composeSeconds=" + seconds(lowered - started)
                + " solveSeconds=" + seconds(decided - lowered);
    }

    /** Where COMPOSE's time went, for the summary line ({@code
     *  tools/analysis/timeline.py}). */
    private static long seconds(long nanos) {
        return java.util.concurrent.TimeUnit.NANOSECONDS.toSeconds(nanos);
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
     * THE COMPOSED FORMULA: the disjunction of the admitted paths, the fatal
     * arm asserted, every root free over its domain -- the formula whose z3
     * answer is the verdict ({@code ClaimPolicy#closed}), so a standalone
     * z3 re-solves it to the same answer.  A witness's valuation is the
     * claim's ({@code claim.json}), never part of the file.  A BLOCKED or
     * pathless composition asserts false with the blocker named, since an
     * empty query would read "sat" by hand.
     */
    static ArtifactIO.Body candidate(Composer.Composition composition,
                                     ClaimPolicy.Decision decision) {
        String blocker = blocker(composition, decision);
        return output -> {
            output.write(composition.body());
            if (!blocker.isEmpty()) {
                output.write("(assert false) ; fail closed: " + blocker
                        + "\n");
            }
            output.write("(check-sat)\n");
        };
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
                JsonFields.nonNull(composition.seedSessionId()));
        boolean complete = !decision.claim().blocked();
        row.addProperty("symbolicPropagationComplete", complete);
        row.addProperty("finalStatus",
                complete ? "FINAL_READY" : "FINAL_REFUSED");
        row.add("finalStatusRefusals", refusals(decision.claim()));
        row.add("gaps", gaps(composition.gaps()));
        // What the composed paths rest on concretely (Composer.Concrete).
        row.add("concrete", GSON.toJsonTree(composition.concrete()));
        row.add("solver", solverRows(composition, decision, solver));
        return row;
    }

    private static JsonObject solverRows(Composer.Composition composition,
                                         ClaimPolicy.Decision decision,
                                         Z3 solver) {
        // The formula's own answer where it was asked, else the witness's
        // valuations: a sat one is the formula sat.
        Z3.Answer formula = decision.formula();
        boolean anySat = formula != null && formula.sat();
        boolean decided = formula != null && formula.decided();
        for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
            if (outcome.answer().sat()) {
                anySat = true;
                decided = true;
            }
        }
        JsonObject row = new JsonObject();
        row.addProperty("state",
                anySat ? "sat" : decided ? "unsat" : "unknown");
        row.addProperty("reachability", anySat ? "EXACT_REACHABLE"
                : decided ? "NO_EXACT_REACHABILITY" : "UNKNOWN");
        row.addProperty("unsatClosureComplete", decided && !anySat);
        row.addProperty("solverRuns", solver.runs());
        // One question per valuation, so the valuation IS the model.
        row.add("valuations", valuations(composition, decision));
        row.add("campaignClaim",
                campaignClaim(composition, decision));
        return row;
    }

    /**
     * WHETHER the run produced an accepted candidate (the {@link ClaimKind}
     * says which mechanism).  The formula decides, SAT or UNSAT; a blocking
     * gap is a defect of the run or the engine that leaves no verdict
     * (RUN_DEFECT), named until it is fixed, never a verdict of its own.
     */
    static JsonObject campaignClaim(
            Composer.Composition composition, ClaimPolicy.Decision decision) {
        Claim claim = decision.claim();
        JsonArray refusals = refusals(claim);
        int blockers = refusals.size();
        String kind;
        String reason;
        JsonArray restsOnRefutations = new JsonArray();
        JsonArray openChain = new JsonArray();
        JsonArray offWitness = new JsonArray();
        // An UNSAT left no verdict by a model CONFIRM gave none on.
        boolean besideRefused = false;
        if (blockers > 0) {
            kind = "RUN_DEFECT";
            reason = "the composition named " + blockers
                    + " defect(s) that leave no verdict; the claim it reached"
                    + " is " + claim.kind();
        } else if (claim.kind() != ClaimKind.NO_SUPPORTED_WITNESS) {
            reason = "valuation " + claim.valuationOrdinal() + " reaches the"
                    + " fatal arm: " + claim.kind()
                    + (claim.movedRoots().isEmpty() ? ""
                    : " " + claim.movedRoots())
                    + (claim.polarityDecides()
                    ? ", and the recorded valuation refutes the recording"
                    : "");
            // A claim never stands on a value no attested producer made: the
            // witness's chain is closed first (EXPLORE grows its producers,
            // PIPELINE §7.9), else no verdict, named.  A SAT is judged on the
            // path it claims; the other paths' open links are stated.
            ClaimPolicy.Outcome witness = witness(decision);
            for (JsonObject link : composition.openChain(witness)) {
                openChain.add(link);
            }
            for (JsonObject link : composition.offWitness(witness)) {
                offWitness.add(link);
            }
            if (openChain.size() == 0) {
                kind = "SAT_CANDIDATE";
            } else {
                kind = "RUN_DEFECT";
                reason += ", but its causal chain is open: the claimed"
                        + " path's fatal condition rests on "
                        + openChain.size() + " handoff value(s) no producer"
                        + " the corpus attests made (openChain)";
            }
        } else if (decision.formula() != null
                && decision.formula().unsat()) {
            // WHAT UNSAT_CLOSED MEANS, exactly: no world of the explored
            // corpus reaches the fatal -- each composed path under the
            // marker valuation its own run ran (Composer#valuationOf), every
            // declared root free over its domain, every clock over its
            // window, every value COMPOSE could not bind free where its
            // stated producer moves and held at its recorded value where no
            // row states it (concrete[], SmtLowering#unbound) -- and nothing
            // about a path the exploration did not admit, or an admitted one
            // COMPOSE refused, each named (refusedPaths).
            kind = "UNSAT_CLOSED";
            reason = "the composed formula is unsat: no world of the explored"
                    + " corpus reaches the fatal arm, given the marker"
                    + " valuations each path ran and the values concrete[]"
                    + " holds"
                    + (composition.refusedPaths().isEmpty() ? ""
                    : "; " + composition.refusedPaths().size() + " admitted"
                    + " path(s) were refused by name and are no part of it"
                    + " (refusedPaths)");
            // A model the formula excludes is a region the UNSAT rests on
            // beside the corpus, named where its core names it.  One CONFIRM
            // gave no verdict on (refused_claim__) was never run: an UNSAT
            // resting on it -- or one whose core is unknown while it
            // excludes one -- is no verdict.
            JsonArray rests = new JsonArray();
            int refused = 0;
            for (JsonObject excluded : composition.restsOn(
                    decision.formula().core())) {
                rests.add(excluded);
                if (excluded.get("name").getAsString()
                        .startsWith(Composer.REFUSED_CLAIM)) {
                    refused++;
                }
            }
            restsOnRefutations = rests;
            // An UNSAT rests on every path: each one's fatal condition is
            // closed, or there is no verdict, its open links named.
            for (JsonObject link : composition.openChain(null)) {
                openChain.add(link);
            }
            if (openChain.size() > 0) {
                kind = "RUN_DEFECT";
                reason = "the composed formula is unsat, but the fatal"
                        + " conditions it rests on name " + openChain.size()
                        + " handoff value(s) no producer the corpus attests"
                        + " made (openChain): no verdict";
            } else if (refused > 0) {
                kind = "RUN_DEFECT";
                besideRefused = true;
                reason = "the composed formula is unsat only beside " + refused
                        + " model(s) CONFIRM gave no verdict on, which no run"
                        + " decided (restsOnRefutations): no verdict";
            } else if (composition.excludesRefused()
                    && !decision.formula().coreKnown()) {
                kind = "RUN_DEFECT";
                besideRefused = true;
                reason = "the composed formula is unsat, it excludes models"
                        + " CONFIRM gave no verdict on, and its unsat core is"
                        + " unknown (the core run did not say unsat), so"
                        + " nothing shows it does not rest on one: no verdict";
            } else if (rests.size() > 0) {
                reason += ", and on " + rests.size() + " refuted claim(s)"
                        + " it excludes (restsOnRefutations)";
            }
        } else {
            // No claim and no unsat: never a refutation.
            kind = "RUN_DEFECT";
            reason = "the composed formula is not unsat ("
                    + (decision.formula() == null ? "never asked"
                    : decision.formula().status()) + ") and no witness is"
                    + " named";
        }
        JsonObject row = new JsonObject();
        row.addProperty("claim", kind);
        row.addProperty("claimReason", reason);
        row.add("restsOnRefutations", restsOnRefutations);
        // Named only where it holds: EMIT lists it as a defect.
        if (besideRefused) row.addProperty("unsatBesideRefused", true);
        if (openChain.size() > 0) row.add("openChain", openChain);
        if (offWitness.size() > 0) row.add("unboundOffWitness", offWitness);
        JsonArray refused = new JsonArray();
        for (JsonObject path : composition.refusedPaths()) refused.add(path);
        row.add("refusedPaths", refused);
        row.addProperty("findingKind", claim.kind().name());
        row.addProperty("valuationOrdinal", claim.valuationOrdinal());
        row.addProperty("polarityDecides", claim.polarityDecides());
        row.add("movedRoots", GSON.toJsonTree(claim.movedRoots()));
        row.add("movedRootCategories", categories(composition, claim));
        // The one rule a configuration-only witness ranks by
        // (Composer#configurationOnly); triage and findings read it here.
        row.addProperty("configurationOnly",
                composition.configurationOnly(claim.movedRoots().keySet()));
        row.add("blockers", refusals);
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


    /** The outcome the claim names, by its valuation; null where none. */
    private static ClaimPolicy.Outcome witness(ClaimPolicy.Decision decision) {
        for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
            if (outcome.valuation().ordinal()
                    == decision.claim().valuationOrdinal()) {
                return outcome;
            }
        }
        return null;
    }

    /**
     * Each moved root's category ({@link RootCategory}): what moving it means,
     * where its kind says only how.  A sweep ranks a witness whose moved
     * roots are all CONFIG after pairings and faults.
     */
    private static JsonObject categories(Composer.Composition composition,
                                         Claim claim) {
        JsonObject categories = new JsonObject();
        for (String moved : claim.movedRoots().keySet()) {
            RootCategory category = composition.categoryOf(moved);
            if (category != null) {
                categories.addProperty(moved, category.name());
            }
        }
        return categories;
    }

    /**
     * The states a model's queries through a re-pointable read saw of the
     * object a chosen state arm delivered: one row per read a query
     * answered, what CONFIRM holds that read to (the write of that version,
     * {@code explore.ConfirmMain}); a query no read row answered is one row
     * with no reader, which CONFIRM refuses by name.  An arm that chose none
     * states no {@code referentStates}.
     */
    private static JsonArray referentStates(
            ComposedFamilies.ArmChoice arm) {
        JsonArray states = new JsonArray();
        for (SmtLowering.StateChoice state : arm.states()) {
            List<String> readers = new ArrayList<String>();
            for (ReadRow read : state.readers) {
                readers.add(read.endpoint().id());
            }
            if (readers.isEmpty()) readers.add("");
            for (String reader : readers) {
                JsonObject row = new JsonObject();
                row.addProperty("selector", state.selector);
                row.addProperty("reader", reader);
                row.addProperty("writer", state.state.endpoint().id());
                row.addProperty("location",
                        SmtLowering.locationKey(state.state.location()));
                row.addProperty("version", state.state.version());
                states.add(row);
            }
        }
        return states;
    }

    private static JsonArray valuations(Composer.Composition composition,
                                        ClaimPolicy.Decision decision) {
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
            Map<String, String> received = ComposedFamilies.texts(
                    outcome.selectedArms().values(),
                    outcome.answer().values(), composition.anchor().id());
            for (Map.Entry<String, ComposedFamilies.ArmChoice> taken
                    : outcome.selectedArms().entrySet()) {
                ComposedFamilies.ArmChoice arm = taken.getValue();
                JsonObject row = new JsonObject();
                row.addProperty("selector", taken.getKey());
                row.addProperty("family", arm.family());
                row.addProperty("groupId", arm.groupId());
                row.add("attachEndpointIds",
                        GSON.toJsonTree(arm.attachEndpointIds()));
                row.addProperty("sessionId", arm.sessionId());
                row.add("sessionIds", GSON.toJsonTree(arm.sessionIds()));
                row.addProperty("producerPathId", arm.producerPathId());
                row.add("interactionIds",
                        GSON.toJsonTree(arm.interactionIds()));
                row.add("expressionRefs",
                        GSON.toJsonTree(arm.expressionRefs()));
                row.addProperty("attested", arm.attested());
                JsonArray states = referentStates(arm);
                if (states.size() > 0) row.add("referentStates", states);
                // What each of its held leaves must receive in CONFIRM.
                JsonObject texts = new JsonObject();
                for (String consumer : arm.leaves().keySet()) {
                    String text = received.get(consumer);
                    if (text != null) texts.addProperty(consumer, text);
                }
                if (texts.size() > 0) row.add(TEXTS, texts);
                arms.add(row);
            }
            answer.add("selectedArms", arms);
            // What a pairing kind moved: the arms taken that are no pairing
            // the selected path's own run had.
            answer.add("repairedArms", GSON.toJsonTree(
                    outcome.selected() == null
                            ? Collections.<String>emptyList()
                            : composition.repaired(outcome.selected()
                            .selector(), outcome.selectedArms().keySet())));
            answer.add("unsatCore", GSON.toJsonTree(outcome.answer().core()));
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
                JsonFields.nonNull(composition.seedSessionId()));
        row.add("valuations", valuations(composition, decision));
        row.add("gaps", gaps(decision.claim().gaps()));
        return row;
    }

    private static JsonArray refusals(Claim claim) {
        JsonArray rows = new JsonArray();
        for (GapRow gap : claim.gaps()) {
            if (!gap.blocking()) continue;
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
    static final class Arguments {
        /** The iteration directory; {@code --sessions} names its child. */
        final Path iteration;
        final String anchor;
        final Path rootDomains;
        final Path scopeMap;
        final int maxValuations;
        final Path output;
        final Path manifest;
        /** Null: {@link Z3}'s own default. */
        final Path z3;
        final long timeoutMillis;

        private Arguments(LongOptions options) {
            Path sessions = options.path("sessions");
            iteration = sessions == null || sessions.getParent() == null
                    ? sessions : sessions.getParent();
            anchor = options.value("anchor", "");
            rootDomains = options.path("root-domains");
            scopeMap = options.path("static-scope-map");
            maxValuations = integer(options.value("max-valuations", null),
                    64);
            output = options.path("output");
            manifest = options.path("manifest");
            z3 = options.path("z3");
            timeoutMillis = integer(options.value("solver-timeout-ms", null),
                    (int) Z3.DEFAULT_TIMEOUT_MILLIS);
        }

        static Arguments parse(String[] argv) {
            Arguments arguments = new Arguments(LongOptions.parse(argv));
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
            // Fail closed: without the map no reference write is known to
            // rest on the decisions that built its referent.
            if (arguments.scopeMap == null
                    || !Files.isRegularFile(arguments.scopeMap)) {
                throw new IllegalArgumentException("--static-scope-map "
                        + "names no file: PLAN publishes "
                        + StaticScopeMap.FILE + " per epoch, and a reference "
                        + "write's construction guard is read from it");
            }
            return arguments;
        }

        /** One numeric option; a passed non-number is refused, never defaulted. */
        private static int integer(String value, int absent) {
            if (value == null) return absent;
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
