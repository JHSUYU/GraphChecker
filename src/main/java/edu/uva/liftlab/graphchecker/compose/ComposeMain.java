package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.plan.SelectorResolution;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.contract.HeapWatch;
import edu.uva.liftlab.graphchecker.contract.Claim;
import edu.uva.liftlab.graphchecker.contract.ClaimKind;
import edu.uva.liftlab.graphchecker.contract.CompositionManifest;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
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
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class ComposeMain {
    public static final String TEXTS = "texts";

    private ComposeMain() {
    }

    public static void main(String[] argv) throws IOException {
        HeapWatch.start();
        System.out.println(run(Arguments.parse(argv)));
    }

    static String run(Arguments arguments) throws IOException {
        long started = System.nanoTime();
        String inputs = CompositionInputs.of(arguments);
        System.err.println("compose: inputs " + inputs + " digested in "
                + seconds(System.nanoTime() - started) + " s");
        if (arguments.reuse != null
                && inputs.equals(CompositionInputs.of(arguments.reuse))) {
            return reuse(arguments, inputs, started);
        }
        Corpus corpus = Corpus.holding(arguments.iteration,
                arguments.rootDomains,
                (long) (HELD_ROWS * Runtime.getRuntime().maxMemory()));
        System.err.println("compose: read " + corpus.sessions().size()
                + " session(s) in " + seconds(System.nanoTime() - started)
                + " s, holding " + corpus.held() / (1024 * 1024) + " of at"
                + " most " + corpus.holdable() / (1024 * 1024) + " MB of"
                + " their reads' and writes' text");
        OccurrenceAddress anchor = anchorOf(arguments.anchor, corpus);
        StaticScopeMap scope = StaticScopeMap.read(arguments.scopeMap);
        Composer.Composition composition = Composer.compose(corpus, anchor,
                arguments.maxValuations, scope,
                Collections.<String>emptySet(), arguments.maxPaths);
        long lowered = System.nanoTime();
        long[] again = corpus.readAgain();
        System.err.println("compose: " + composition.disjuncts().size()
                + " path(s) composed, a " + composition.body().length()
                / (1024 * 1024) + " MB body and " + composition.valuations()
                .size() + " valuation(s), in " + seconds(lowered - started)
                + " s, " + again[0] + " session(s) let go of read again ("
                + again[1] / (1024 * 1024) + " MB); deciding");
        Z3 solver = solver(arguments);
        ClaimPolicy.Decision decision = ClaimPolicy.decide(composition,
                solver);
        Set<String> refused = ClaimPolicy.refusedPaths(decision.claim());
        if (!refused.isEmpty()
                && refused.size() < composition.disjuncts().size()) {
            System.err.println("compose: z3 refused " + refused.size()
                    + " path(s)' own question; composing without them");
            composition = Composer.compose(corpus, anchor,
                    arguments.maxValuations, scope, refused,
                    arguments.maxPaths);
            solver = solver(arguments);
            decision = ClaimPolicy.decide(composition, solver);
        }
        long decided = System.nanoTime();
        System.err.println("compose: decided " + decision.claim().kind()
                + " with " + solver.runs() + " z3 run(s) in "
                + seconds(decided - lowered) + " s");

        ArtifactIO.atomicReplace(arguments.output,
                candidate(composition, decision));
        CompositionManifest composed = CompositionManifest.of(anchor,
                composition.paths(), composition.families(),
                composition.roots(), composition.valuations().size(),
                decision.claim());
        write(arguments.manifest,
                manifest(composed, composition, decision, solver));
        write(arguments.manifest.resolveSibling(CLAIM),
                claim(composition, decision, solver));
        Path stated = arguments.manifest.resolveSibling(
                CompositionInputs.FILE);
        if (inputs.equals(CompositionInputs.of(arguments))) {
            ArtifactIO.replace(stated, inputs + "\n");
        } else {
            Files.deleteIfExists(stated);
            System.err.println("compose: an input changed while it was"
                    + " read; no " + CompositionInputs.FILE + " stated");
        }
        return summary(anchor, composition, decision, solver)
                + " composeSeconds=" + seconds(lowered - started)
                + " solveSeconds=" + seconds(decided - lowered);
    }

    static final String CLAIM = "claim.json";

    static final double HELD_ROWS = 0.15;

    private static Z3 solver(Arguments arguments) {
        return new Z3(arguments.z3, arguments.timeoutMillis,
                arguments.z3RoomMb, arguments.z3Hosts,
                arguments.output.toAbsolutePath().getParent());
    }

    private static String reuse(Arguments arguments, String inputs,
                                long started) throws IOException {
        copy(arguments.reuse.resolve(arguments.output.getFileName()),
                arguments.output);
        copy(arguments.reuse.resolve(arguments.manifest.getFileName()),
                arguments.manifest);
        copy(arguments.reuse.resolve(CLAIM),
                arguments.manifest.resolveSibling(CLAIM));
        copy(arguments.reuse.resolve(CompositionInputs.FILE),
                arguments.manifest.resolveSibling(CompositionInputs.FILE));
        return "reused the composition in " + arguments.reuse + ": its"
                + " inputs are this one's (" + CompositionInputs.FILE + " "
                + inputs + "), nothing composed or solved, in "
                + seconds(System.nanoTime() - started) + " s";
    }

    private static void copy(Path from, Path to) throws IOException {
        Path target = to.toAbsolutePath().normalize();
        Files.createDirectories(target.getParent());
        Path staged = Files.createTempFile(target.getParent(),
                "artifact-" + target.getFileName(), ".tmp");
        try {
            Files.copy(from, staged, StandardCopyOption.REPLACE_EXISTING);
            Files.move(staged, target, StandardCopyOption.ATOMIC_MOVE,
                    StandardCopyOption.REPLACE_EXISTING);
        } finally {
            Files.deleteIfExists(staged);
        }
    }

    private static long seconds(long nanos) {
        return java.util.concurrent.TimeUnit.NANOSECONDS.toSeconds(nanos);
    }

    static OccurrenceAddress anchorOf(String declared, Corpus corpus) {
        String seed = corpus.seedSessionId();
        SessionReader session = seed.isEmpty() ? null : corpus.session(seed);
        return SelectorResolution.resolve(declared,
                session == null ? null : session.activations());
    }

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


    private static JsonObject manifest(CompositionManifest composed,
                                       Composer.Composition composition,
                                       ClaimPolicy.Decision decision,
                                       Z3 solver) {
        JsonObject row = GSON.toJsonTree(composed).getAsJsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "COMPOSITION_MANIFEST");
        row.addProperty("anchor", composition.anchor().render());
        row.addProperty("anchorId", composition.anchor().id());
        row.addProperty("seedSessionId",
                JsonFields.nonNull(composition.seedSessionId()));
        boolean complete = !decision.claim().blocked();
        row.addProperty("symbolicPropagationComplete", complete);
        row.addProperty("finalStatus",
                complete ? "FINAL_READY" : "FINAL_REFUSED");
        row.add("finalStatusRefusals", refusals(decision.claim()));
        row.add("gaps", gaps(composition.gaps()));
        row.add("concrete", GSON.toJsonTree(composition.concrete()));
        row.add("solver", solverRows(composition, decision, solver));
        return row;
    }

    private static JsonObject solverRows(Composer.Composition composition,
                                         ClaimPolicy.Decision decision,
                                         Z3 solver) {
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
        row.add("valuations", valuations(composition, decision));
        row.add("campaignClaim",
                campaignClaim(composition, decision));
        return row;
    }

    static JsonObject campaignClaim(
            Composer.Composition composition, ClaimPolicy.Decision decision) {
        Claim claim = decision.claim();
        JsonArray refusals = refusals(claim);
        int blockers = refusals.size();
        String kind;
        String reason;
        JsonArray restsOnRefutations = new JsonArray();
        boolean restsKnown = true;
        JsonArray openChain = new JsonArray();
        JsonArray offWitness = new JsonArray();
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
            ClaimPolicy.Outcome witness = witness(decision);
            for (JsonObject link : composition.openChain(witness)) {
                openChain.add(link);
            }
            for (JsonObject link : composition.offWitness(witness)) {
                offWitness.add(link);
            }
            kind = "SAT_CANDIDATE";
            if (openChain.size() > 0) {
                reason += "; its causal chain is open: the claimed path's"
                        + " fatal condition rests on " + openChain.size()
                        + " handoff value(s) no producer the corpus attests"
                        + " made (openChain)";
            }
        } else if (decision.formula() != null
                && decision.formula().unsat()) {
            kind = "UNSAT_CLOSED";
            reason = "the composed formula is unsat: no world of the explored"
                    + " corpus reaches the fatal arm, given the marker"
                    + " valuations each path ran and the values concrete[]"
                    + " holds"
                    + (composition.refusedPaths().isEmpty() ? ""
                    : "; " + composition.refusedPaths().size() + " admitted"
                    + " path(s) were refused by name and are no part of it"
                    + " (refusedPaths)");
            JsonArray rests = new JsonArray();
            boolean restsUnknown = composition.assertsRefutations()
                    && !decision.formula().coreKnown();
            for (JsonObject excluded : restsUnknown
                    ? Collections.<JsonObject>emptyList()
                    : composition.restsOn(decision.formula().core())) {
                rests.add(excluded);
            }
            restsOnRefutations = rests;
            if (restsUnknown) restsKnown = false;
            for (JsonObject link : composition.openChain(null)) {
                openChain.add(link);
            }
            if (openChain.size() > 0) {
                reason += ", over " + openChain.size() + " handoff value(s)"
                        + " no producer the corpus attests made, free in it"
                        + " (openChain)";
            }
            if (restsUnknown) {
                reason += "; it excludes refuted claim(s) and its core is not"
                        + " known (" + decision.formula().status() + "), so"
                        + " which of them it rests on is not known"
                        + " (restsOnRefutationsKnown false)";
            } else if (rests.size() > 0) {
                reason += ", and on " + rests.size() + " refuted claim(s)"
                        + " it excludes (restsOnRefutations)";
            }
        } else {
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
        if (!restsKnown) row.addProperty("restsOnRefutationsKnown", false);
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


    private static ClaimPolicy.Outcome witness(ClaimPolicy.Decision decision) {
        for (ClaimPolicy.Outcome outcome : decision.outcomes()) {
            if (outcome.valuation().ordinal()
                    == decision.claim().valuationOrdinal()) {
                return outcome;
            }
        }
        return null;
    }

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
                JsonObject texts = new JsonObject();
                for (String consumer : arm.leaves().keySet()) {
                    String text = received.get(consumer);
                    if (text != null) texts.addProperty(consumer, text);
                }
                if (texts.size() > 0) row.add(TEXTS, texts);
                arms.add(row);
            }
            answer.add("selectedArms", arms);
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

    static final class Arguments {
        final Path iteration;
        final String anchor;
        final Path rootDomains;
        final Path scopeMap;
        final int maxValuations;
        final int maxPaths;
        final Path output;
        final Path manifest;
        final Path z3;
        final long timeoutMillis;
        final int z3RoomMb;
        final Map<String, Integer> z3Hosts;
        final Path reuse;

        private Arguments(LongOptions options) {
            Path sessions = options.path("sessions");
            iteration = sessions == null || sessions.getParent() == null
                    ? sessions : sessions.getParent();
            anchor = options.value("anchor", "");
            rootDomains = options.path("root-domains");
            scopeMap = options.path("static-scope-map");
            maxValuations = integer(options.value("max-valuations", null),
                    64);
            maxPaths = integer(options.value("max-paths", null), 0);
            output = options.path("output");
            manifest = options.path("manifest");
            z3 = options.path("z3");
            timeoutMillis = integer(options.value("solver-timeout-ms", null),
                    (int) Z3.DEFAULT_TIMEOUT_MILLIS);
            z3RoomMb = integer(options.value("z3-room-mb", null), 0);
            z3Hosts = hosts(options.value("z3-hosts", ""));
            reuse = options.path("reuse");
        }

        static Map<String, Integer> hosts(String value) {
            Map<String, Integer> hosts = new LinkedHashMap<String, Integer>();
            for (String room : value.trim().isEmpty() ? new String[0]
                    : value.trim().split(",")) {
                int at = room.indexOf('=');
                String host = at < 0 ? "" : room.substring(0, at).trim();
                int mb = at < 0 ? 0 : integer(room.substring(at + 1), 0);
                if (host.isEmpty() || mb <= 0 || hosts.containsKey(host)) {
                    throw new IllegalArgumentException("--z3-hosts names \""
                            + room + "\": each room is host=mb, a host"
                            + " once");
                }
                hosts.put(host, mb);
            }
            return hosts;
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
            if (arguments.z3RoomMb <= 0) {
                throw new IllegalArgumentException("--z3-room-mb is required:"
                        + " what this JVM's charge holds for its z3"
                        + " processes");
            }
            if (arguments.scopeMap == null
                    || !Files.isRegularFile(arguments.scopeMap)) {
                throw new IllegalArgumentException("--static-scope-map "
                        + "names no file: PLAN publishes "
                        + StaticScopeMap.FILE + " per epoch, and a reference "
                        + "write's construction guard is read from it");
            }
            return arguments;
        }

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
