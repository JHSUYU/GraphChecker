package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * The family of one handoff occurrence, selected from a corpus of replays.
 *
 * <p>A value that crossed a wire is a free variable {@code v_H} of the
 * consumer's formula.  What ties it back to the world is the family: across
 * every replay of the campaign, the rows published at that same handoff
 * occurrence state the pairs {@code (pi_q, e_q)} -- the producer replay's
 * root-dependent prefix up to the export, the valuation it ran under, and
 * the expression it delivered.  {@code OR_q (pi_q AND v_H = e_q)} says the
 * received value is one some producer of this corpus actually delivers, and
 * under the conditions that made it deliver that one.</p>
 *
 * <p>This class is only the <em>row selection</em> and the arm payload: the
 * join key is the handoff occurrence and nothing else, a row that states no
 * exact occurrence is refused rather than matched on a port or an ordinal,
 * and a delivery that carried no element ({@code elementAbsent}) contributes
 * no arm because it delivered nothing.  It is deliberately free of any SMT
 * spelling so that both readers of the family -- the composition, which
 * merges paths, and the exploration, which asks for one flip -- can select
 * the same rows and lower them in their own host.  {@link PathMergeComposer}
 * states the same selection inline today; this is the shared form it can
 * adopt without either host being able to drift from the other.</p>
 *
 * <p>Why exploration needs it at all: an obligation is a flip query whose
 * model assigns the consumer's {@code v_H}, and the next replay applies that
 * value at the attach.  Left free, the solver answered 17897's five block-key
 * handoffs with {@code 1, 1, 1, 1, 0} -- values no producer of that corpus
 * can deliver -- so the replay threw, the path was explored, and the
 * composition then refused it because no family arm can reach a 0 or a 1.
 * Waves were spent on values the system does not produce.  Constrained by
 * its family, the model answers a handoff only with a value some producer
 * can deliver under a root move.</p>
 */
final class HandoffFamilyRows {
    /** Member one handoff control carries its producer arms in. */
    static final String ARMS = "producerArms";
    /**
     * Member stating that this corpus has no producer arm for the control.
     *
     * <p>{@code elementAbsent} rows, a producer outside the slice, a phase
     * nothing exported: the control stays free, and the obligation says so,
     * because a later composition refusing that path is then expected rather
     * than a surprise.</p>
     */
    static final String UNPRODUCIBLE = "unproducible";
    /** Member the obligation carries the roots its arms name in. */
    static final String ROOTS = "handoffFamilyRoots";
    /** The producer's delivered expression, resolved in its own session. */
    static final String DELIVERED = "delivered";
    /** The delivering replay's root-dependent decisions before the export. */
    static final String PREFIX = "prefix";
    /** The valuation of the varied roots the delivering replay ran under. */
    static final String VALUATION = "valuation";
    /** Whether one valuation row is a wall-clock reading. */
    static final String WALL_CLOCK = "wallClock";
    /** Why one handoff of the formula has no arm in this corpus. */
    static final String REFUSALS = "familyRefusals";

    private HandoffFamilyRows() {
    }

    /**
     * One wave's replays, indexed for family selection.
     *
     * <p>Built once per wave: the resolvers are per replay (a version id is
     * session-local, so mixing replays would let one execution answer
     * another's read), and the root readings are the whole corpus's, because
     * "this root varied" is a statement about the corpus and not about one
     * replay.</p>
     */
    static final class Corpus {
        private final List<JsonObject> summaries;
        private final Map<String, InSessionReadResolver> resolvers;
        /** The configured and manual roots, by raw symbol. */
        private final Map<String, JsonObject> rootRows =
                new LinkedHashMap<>();
        /** Every distinct value some replay read at each root. */
        private final Map<String, Set<String>> readings =
                new LinkedHashMap<>();
        /** What the case says each root may be, by source id. */
        private final Map<String, JsonObject> declaredDomains;

        private Corpus(List<JsonObject> summaries,
                       Map<String, InSessionReadResolver> resolvers,
                       Map<String, JsonObject> declaredDomains) {
            this.summaries = summaries;
            this.resolvers = resolvers;
            this.declaredDomains = declaredDomains;
        }

        /**
         * Indexes one wave.
         *
         * @param summaries every summary of the wave, in any order
         * @param rootDomains the case's {@code root-domains.jsonl}, or null
         */
        static Corpus of(Collection<JsonObject> summaries, Path rootDomains)
                throws IOException {
            List<JsonObject> rows = new ArrayList<>();
            if (summaries != null) {
                for (JsonObject summary : summaries) {
                    if (summary != null) rows.add(summary);
                }
            }
            Corpus corpus = new Corpus(rows,
                    ResolvedFlipQuery.resolversByReplay(rows),
                    declaredDomains(rootDomains));
            for (JsonObject summary : rows) corpus.index(summary);
            return corpus;
        }

        private void index(JsonObject summary) {
            for (JsonObject event
                    : SymbolicSourceEvidence.eventsOf(summary)) {
                String raw = optionalString(event, "rawSymbol");
                if (raw.isEmpty()) continue;
                rootRows.putIfAbsent(raw, event);
                String value = SymbolicSourceEvidence.recordedValueOf(event);
                if (!value.isEmpty()) reading(raw, value);
            }
            // A manual symbolic input is the member every replay publishes
            // its own reading on; the mint evidence carries the seeding
            // activation's alone, so judging variation from the mint said
            // "one value" about a root nine replays read nine ways.
            for (JsonElement encoded
                    : array(summary, "manualSymbolicInputObservations")) {
                if (!encoded.isJsonObject()) continue;
                JsonObject row = encoded.getAsJsonObject();
                String raw = optionalString(row, "rawSymbol");
                String value = optionalString(row, "recordedValue");
                if (raw.isEmpty() || value.isEmpty()) continue;
                reading(raw, value);
            }
        }

        private void reading(String raw, String value) {
            Set<String> values = readings.get(raw);
            if (values == null) {
                values = new LinkedHashSet<>();
                readings.put(raw, values);
            }
            values.add(value);
        }

        /** Whether replays of this corpus read this root differently. */
        private boolean varied(String raw) {
            Set<String> values = readings.get(raw);
            return values != null && values.size() > 1;
        }

        /** The roots a producer prefix may be about. */
        private Set<String> rootSymbols() {
            return rootRows.keySet();
        }

        /**
         * The producer arms of one handoff variable, by the same row
         * selection the composition merges.
         *
         * @param handoffSymbol the raw {@code v_H} the obligation reads
         * @param refusals      filled with the reason of each row refused
         */
        JsonArray armsOf(String handoffSymbol, List<String> refusals) {
            JsonArray arms = new JsonArray();
            if (handoffSymbol == null || handoffSymbol.isEmpty()) return arms;
            Set<String> seen = new LinkedHashSet<>();
            for (JsonObject summary : summaries) {
                for (JsonElement encoded
                        : array(summary, VmHandoffEvidence.FIELD)) {
                    if (!encoded.isJsonObject()) continue;
                    JsonObject event = encoded.getAsJsonObject();
                    if (!handoffSymbol.equals(optionalString(event,
                            InSessionReadResolver.HANDOFF_SYMBOL))) {
                        continue;
                    }
                    JsonObject arm = arm(summary, event, refusals, seen);
                    if (arm != null) arms.add(arm);
                }
            }
            return arms;
        }

        private JsonObject arm(JsonObject summary, JsonObject event,
                               List<String> refusals, Set<String> seen) {
            String phase = optionalString(event,
                    InSessionReadResolver.HANDOFF_PHASE_ID);
            long export = optionalLongInteger(event, "exportEventId", -1L);
            long attach = optionalLongInteger(event, "attachEventId", -1L);
            // H's identity IS the handoff phase id.  A consumer that minted
            // v_H from a value no producer of this run exported states that
            // phase and no VM edge, because there is no edge to state: it
            // joins its family by the phase and contributes no arm.  A row
            // that is not elementAbsent and still names no attach states no
            // occurrence at all, and stays refused.
            boolean elementAbsent = VmHandoffEvidence.isElementAbsent(event);
            if (phase.isEmpty()
                    || !elementAbsent && (export <= 0L || attach <= 0L)) {
                add(refusals, "states no exact occurrence to join on");
                return null;
            }
            if (elementAbsent) return null;
            String replay = ResolvedFlipQuery.replayKey(summary);
            if (!seen.add(replay + "\n" + export + "\n" + attach)) return null;
            InSessionReadResolver resolver = resolvers.get(replay);
            if (resolver == null) {
                add(refusals, "no session to resolve the delivery of "
                        + replay);
                return null;
            }
            List<String> unresolved = new ArrayList<>();
            JsonElement delivered = resolver.resolve(
                    event.get(VmHandoffEvidence.EXPRESSION));
            ResolvedFlipQuery.collectUnresolved(delivered, unresolved);
            if (!unresolved.isEmpty()) {
                add(refusals, "delivered a value this replay did not state: "
                        + unresolved.get(0));
                return null;
            }
            JsonObject arm = new JsonObject();
            arm.addProperty("replayGroupId", replay);
            arm.addProperty(InSessionReadResolver.HANDOFF_PHASE_ID, phase);
            arm.addProperty("deliveredValue", optionalString(event,
                    "recordedValue"));
            arm.add(DELIVERED, delivered);
            arm.add(PREFIX, producerPrefix(replay, resolver, export));
            arm.add(VALUATION, deliveringValuation(replay));
            return arm;
        }

        /**
         * The delivering replay's root-dependent decisions before the
         * export.
         *
         * <p>Every activation of the replay group is read: a decision the
         * delivery rests on is published by whichever activation took it,
         * and conjunction is order-free.  A decision taken after the export
         * is excluded by its own session clock, which is the only order two
         * activations of one replay share.</p>
         */
        private JsonArray producerPrefix(String replay,
                                         InSessionReadResolver resolver,
                                         long exportEventId) {
            JsonArray prefix = new JsonArray();
            Set<String> roots = rootSymbols();
            if (roots.isEmpty()) return prefix;
            for (JsonObject summary : summaries) {
                if (!replay.equals(ResolvedFlipQuery.replayKey(summary))) {
                    continue;
                }
                Map<Integer, Long> clocks = decisionClocks(summary);
                JsonArray conditions = array(summary, "pathCondition");
                for (int index = 0; index < conditions.size(); index++) {
                    Long clock = clocks.get(index);
                    if (clock == null || clock <= 0L
                            || clock >= exportEventId) {
                        continue;
                    }
                    List<String> unresolved = new ArrayList<>();
                    JsonElement decision = resolver.resolve(
                            conditions.get(index), clock);
                    ResolvedFlipQuery.collectUnresolved(decision, unresolved);
                    if (unresolved.isEmpty()
                            && mentionsRoot(decision, roots)) {
                        prefix.add(decision);
                    }
                }
            }
            return prefix;
        }

        /**
         * The valuation one delivering replay ran under.
         *
         * <p>A delivery is not available under every root valuation: the
         * replay that sent one key id ran with each root at the value its
         * obligation applied.  Only roots this corpus <em>varied</em> are
         * stated as equalities -- a root every replay read the same way
         * separates no arm from another -- and a clock read is never an
         * equality, because every execution reads it fresh.</p>
         */
        private JsonArray deliveringValuation(String replay) {
            JsonArray valuation = new JsonArray();
            Set<String> stated = new LinkedHashSet<>();
            for (JsonObject summary : summaries) {
                if (!replay.equals(ResolvedFlipQuery.replayKey(summary))) {
                    continue;
                }
                for (String member : new String[]{
                        SymbolicSourceEvidence.FIELD,
                        "manualSymbolicInputObservations"}) {
                    for (JsonElement encoded : array(summary, member)) {
                        if (!encoded.isJsonObject()) continue;
                        JsonObject row = encoded.getAsJsonObject();
                        String raw = optionalString(row, "rawSymbol");
                        String value = executionReading(row);
                        if (raw.isEmpty() || value.isEmpty()
                                || !rootRows.containsKey(raw)
                                || !stated.add(raw)) {
                            continue;
                        }
                        boolean clock = ClockRootPhysics.clockCallee(
                                optionalString(row, SymbolicSourceEvidence
                                        .DECLARED_CALLEE));
                        if (!clock && !varied(raw)) continue;
                        JsonObject stated_row = new JsonObject();
                        stated_row.addProperty("rawSymbol", raw);
                        stated_row.addProperty("javaType", optionalString(
                                rootRows.get(raw), "javaType"));
                        stated_row.addProperty("value", value);
                        stated_row.addProperty(WALL_CLOCK, clock);
                        valuation.add(stated_row);
                    }
                }
            }
            return valuation;
        }

        /**
         * The roots one set of arms names, each with the domain the case
         * declares for it.
         *
         * <p>A family arm is only as constraining as the roots inside it: an
         * arm {@code v_H = serialNo} says nothing at all while
         * {@code serialNo} is free.  The rule is the composition's: a
         * Boolean marker is free over both its values, a clock read is
         * carried by the arm's own valuation, a root the case declares a
         * domain for is free inside it -- relative bounds resolved against
         * what the recording read -- and every other root is pinned to its
         * recorded value.</p>
         */
        JsonArray rootsOf(JsonArray arms) {
            Set<String> named = new LinkedHashSet<>();
            for (JsonElement arm : arms) {
                if (!arm.isJsonObject()) continue;
                JsonObject row = arm.getAsJsonObject();
                collectRoots(row.get(DELIVERED), named);
                collectRoots(row.get(PREFIX), named);
                for (JsonElement stated : array(row, VALUATION)) {
                    if (!stated.isJsonObject()) continue;
                    String raw = optionalString(stated.getAsJsonObject(),
                            "rawSymbol");
                    if (rootRows.containsKey(raw)) named.add(raw);
                }
            }
            JsonArray roots = new JsonArray();
            for (String raw : named) {
                JsonObject declared = rootRows.get(raw);
                if (declared == null) continue;
                String recorded = SymbolicSourceEvidence.recordedValueOf(
                        declared);
                JsonObject row = new JsonObject();
                row.addProperty("rawSymbol", raw);
                row.addProperty("javaType",
                        optionalString(declared, "javaType"));
                row.addProperty("sourceId",
                        optionalString(declared, "sourceId"));
                row.addProperty("recordedValue", recorded);
                row.addProperty(WALL_CLOCK, ClockRootPhysics.clockCallee(
                        optionalString(declared, SymbolicSourceEvidence
                                .DECLARED_CALLEE)));
                JsonObject domain = declaredDomains.get(
                        optionalString(declared, "sourceId"));
                String min = bound(domain, PathMergeComposer
                        .DECLARED_DOMAIN_MIN, recorded);
                String max = bound(domain, PathMergeComposer
                        .DECLARED_DOMAIN_MAX, recorded);
                if (!min.isEmpty() && !max.isEmpty()) {
                    row.addProperty(PathMergeComposer.DECLARED_DOMAIN_MIN,
                            min);
                    row.addProperty(PathMergeComposer.DECLARED_DOMAIN_MAX,
                            max);
                }
                roots.add(row);
            }
            return roots;
        }

        private void collectRoots(JsonElement value, Set<String> into) {
            if (value == null || value.isJsonNull()) return;
            if (value.isJsonArray()) {
                for (JsonElement child : value.getAsJsonArray()) {
                    collectRoots(child, into);
                }
                return;
            }
            if (!value.isJsonObject()) return;
            JsonObject node = value.getAsJsonObject();
            String raw = optionalString(node, "_exp");
            if (rootRows.containsKey(raw)) into.add(raw);
            for (Map.Entry<String, JsonElement> member : node.entrySet()) {
                collectRoots(member.getValue(), into);
            }
        }
    }

    /**
     * One bound of a root's declared domain, as an absolute integer.
     *
     * <p>Two spellings, one notion, exactly as the composition reads them.
     * An absolute bound is the value itself; a bound written {@code +k} or
     * {@code -k} is that many steps from what the recording read, which is
     * the only way a case can state the domain of a counter whose zero
     * nobody chose.</p>
     */
    private static String bound(JsonObject domain, String member,
                                String recorded) {
        if (domain == null) return "";
        String stated = optionalString(domain, member).trim();
        if (stated.isEmpty()) return "";
        if (stated.startsWith("+") || stated.startsWith("-")) {
            String offset = stated.startsWith("+")
                    ? stated.substring(1) : stated;
            try {
                return new BigInteger(recorded.trim())
                        .add(new BigInteger(offset.trim())).toString();
            } catch (NumberFormatException malformed) {
                return "";
            }
        }
        try {
            return new BigInteger(stated).toString();
        } catch (NumberFormatException malformed) {
            return "";
        }
    }

    /** What the case says each declared root may be, by source id. */
    private static Map<String, JsonObject> declaredDomains(Path file)
            throws IOException {
        Map<String, JsonObject> bySource = new LinkedHashMap<>();
        if (file == null || !Files.isRegularFile(file)) return bySource;
        for (JsonObject row : ArtifactIO.readJsonl(file,
                "Malformed root domain %1$s:%2$d",
                "Non-object root domain %1$s:%2$d")) {
            String sourceId = optionalString(row, "sourceId");
            if (!sourceId.isEmpty()) bySource.put(sourceId, row);
        }
        return bySource;
    }

    /**
     * Attaches the family of every handoff control of one obligation.
     *
     * <p>Each control gains the arms its phase has in this corpus; one with
     * none is marked {@link #UNPRODUCIBLE} rather than left silently free,
     * so that a composition later refusing that path is an expected outcome
     * the obligation already stated.</p>
     */
    static void attach(JsonObject task, Corpus corpus) {
        if (task == null || corpus == null) return;
        JsonArray controls = array(task,
                RegionPathWorklist.HANDOFF_CONTROLS);
        if (controls.size() == 0) return;
        JsonArray every = new JsonArray();
        for (JsonElement encoded : controls) {
            if (!encoded.isJsonObject()) continue;
            JsonObject control = encoded.getAsJsonObject();
            List<String> refusals = new ArrayList<>();
            JsonArray arms = corpus.armsOf(
                    optionalString(control, "rawSymbol"), refusals);
            control.add(ARMS, arms);
            if (arms.size() == 0) {
                control.addProperty(UNPRODUCIBLE, true);
                JsonArray reasons = new JsonArray();
                for (String reason : refusals) reasons.add(reason);
                control.add(REFUSALS, reasons);
            }
            for (JsonElement arm : arms) every.add(arm);
        }
        JsonArray roots = corpus.rootsOf(every);
        if (roots.size() > 0) task.add(ROOTS, roots);
    }

    /** Whether one expression names a root of this corpus. */
    private static boolean mentionsRoot(JsonElement expression,
                                        Set<String> roots) {
        if (expression == null || expression.isJsonNull()) return false;
        if (expression.isJsonArray()) {
            for (JsonElement child : expression.getAsJsonArray()) {
                if (mentionsRoot(child, roots)) return true;
            }
            return false;
        }
        if (!expression.isJsonObject()) return false;
        JsonObject node = expression.getAsJsonObject();
        if (roots.contains(optionalString(node, "_exp"))) return true;
        for (Map.Entry<String, JsonElement> member : node.entrySet()) {
            if (mentionsRoot(member.getValue(), roots)) return true;
        }
        return false;
    }

    /** The session clock of each published decision of one summary. */
    private static Map<Integer, Long> decisionClocks(JsonObject summary) {
        Map<Integer, Long> clocks = new LinkedHashMap<>();
        for (JsonElement element : array(summary, "branchMappings")) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            int index = JsonFields.exactInteger(mapping,
                    "summaryPcIndex", -1);
            long clock = optionalLongInteger(mapping,
                    InSessionReadResolver.SESSION_EVENT_ID, 0L);
            if (index >= 0 && clock > 0L) clocks.putIfAbsent(index, clock);
        }
        return clocks;
    }

    /**
     * What THIS execution read at one mint.
     *
     * <p>{@code recordedValue} on a clock row is the RECORDING's reading;
     * what this execution read is {@code observedValue} where the runtime
     * states one.</p>
     */
    private static String executionReading(JsonObject row) {
        String observed = optionalString(row,
                SymbolicSourceEvidence.OBSERVED_VALUE);
        return observed.isEmpty()
                ? optionalString(row, "recordedValue") : observed;
    }

    private static void add(List<String> refusals, String reason) {
        if (!refusals.contains(reason)) refusals.add(reason);
    }

    /** The empty corpus, for a planner with no summaries to select from. */
    static Corpus none() {
        try {
            return Corpus.of(Collections.<JsonObject>emptyList(), null);
        } catch (IOException impossible) {
            throw new IllegalStateException(impossible);
        }
    }
}
