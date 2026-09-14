package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.primitiveInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.primitiveString;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requiredObject;

/** Immutable natural replay request derived from one source branch witness. */
public final class BranchReplayContract {
    public static final int SCHEMA_VERSION = 3;
    public static final String KIND = "BINARY_BRANCH_REPLAY_CONTRACT";

    private final List<BranchWitness> orderedPrefix;
    private final List<ExactConcreteBranchObservation> runtimePrefix;
    private final BranchWitness source;
    private final SolverPathContext solverPathContext;

    private BranchReplayContract(List<BranchWitness> orderedPrefix,
                                 List<ExactConcreteBranchObservation>
                                         runtimePrefix,
                                 BranchWitness source,
                                 SolverPathContext solverPathContext) {
        if (source == null) {
            throw new IllegalArgumentException("source witness is required");
        }
        if (orderedPrefix == null) {
            throw new IllegalArgumentException("ordered prefix is required");
        }
        if (runtimePrefix == null) {
            throw new IllegalArgumentException("runtime prefix is required");
        }
        if (source.isPcPredicateDecision()) {
            throw new IllegalArgumentException(
                    "replay source must be a source-level branch event");
        }
        List<BranchWitness> prefixCopy = new ArrayList<>(orderedPrefix);
        Set<String> events = new LinkedHashSet<>();
        for (BranchWitness witness : prefixCopy) {
            if (witness == null || !events.add(eventIdentity(witness))) {
                throw new IllegalArgumentException(
                        "ordered prefix contains a missing or duplicate event");
            }
        }
        if (!events.add(eventIdentity(source))) {
            throw new IllegalArgumentException(
                    "source branch event must not appear in ordered prefix");
        }
        List<ExactConcreteBranchObservation> runtimeCopy =
                new ArrayList<>(runtimePrefix);
        Set<String> runtimeEvents = new LinkedHashSet<>();
        for (ExactConcreteBranchObservation observation : runtimeCopy) {
            if (observation == null
                    || !runtimeEvents.add(runtimeIdentity(observation))) {
                throw new IllegalArgumentException(
                        "runtime prefix contains a missing or duplicate event");
            }
        }
        if (runtimeEvents.contains(sourceIdentity(source))) {
            throw new IllegalArgumentException(
                    "source branch event must not appear in runtime prefix");
        }
        for (BranchWitness witness : prefixCopy) {
            if (witness.isPcPredicateDecision()) continue;
            requireWitnessedInRuntimePrefix(runtimeCopy,
                    sourceIdentity(witness), witness.sourceTakenOutcome(),
                    witness.siteId() + "#" + witness.occurrence());
        }
        this.orderedPrefix = Collections.unmodifiableList(prefixCopy);
        this.runtimePrefix = Collections.unmodifiableList(runtimeCopy);
        this.source = source;
        this.solverPathContext = solverPathContext;
    }

    /** A contract for one source event whose replay has no witnessed
     *  prefix; {@link #fromSummary} builds every contract that has one. */
    public static BranchReplayContract atSource(BranchWitness source) {
        return new BranchReplayContract(
                Collections.<BranchWitness>emptyList(),
                Collections.<ExactConcreteBranchObservation>emptyList(),
                source, null);
    }

    /** One witnessed source-level decision must appear in the runtime
     *  prefix with the same identity and the same taken outcome. */
    private static void requireWitnessedInRuntimePrefix(
            List<ExactConcreteBranchObservation> runtimePrefix,
            String identity, boolean takenOutcome, String label) {
        for (ExactConcreteBranchObservation observation : runtimePrefix) {
            if (identity.equals(runtimeIdentity(observation))
                    && !observation.isSwitchObservation()
                    && observation.sourceTakenOutcome() == takenOutcome) {
                return;
            }
        }
        throw new IllegalArgumentException(
                "runtime prefix omits witnessed event " + label);
    }

    public static BranchReplayContract fromSummary(
            JsonObject summary, String siteId, int occurrence) {
        List<SummaryBranchMapping> mappings =
                SummaryBranchMapping.fromSummary(summary);
        for (SummaryBranchMapping mapping : mappings) {
            if (siteId.equals(mapping.siteId())
                    && occurrence == mapping.occurrence()) {
                return fromSummary(summary, mappings, mapping);
            }
        }
        throw new IllegalArgumentException("target branch mapping is missing");
    }

    static BranchReplayContract fromSummary(
            JsonObject summary, List<SummaryBranchMapping> mappings,
            SummaryBranchMapping selected) {
        if (selected == null || !selected.isWitnessed()) {
            throw new IllegalArgumentException(
                    "target branch has no immutable witness");
        }
        int targetPosition = selected.summaryPcIndex();
        Map<Integer, BranchWitness> prefixByPosition = new TreeMap<>();
        for (SummaryBranchMapping mapping : mappings) {
            if (mapping.isWitnessed()
                    && mapping.summaryPcIndex() < targetPosition) {
                prefixByPosition.put(mapping.summaryPcIndex(),
                        mapping.witness());
            }
        }
        SolverPathContext context = SolverPathContext.fromPath(
                summary.getAsJsonArray("pathCondition"),
                prefixByPosition.keySet(),
                targetPosition);
        List<ExactConcreteBranchObservation> runtimePrefix =
                new ArrayList<>();
        for (SummaryBranchMapping mapping : mappings) {
            if (mapping.decisionIdentity().equals(
                    selected.decisionIdentity())) {
                break;
            }
            if (mapping.isConcreteObservation()) {
                runtimePrefix.add(mapping.concreteObservation());
            } else if (!mapping.witness().isPcPredicateDecision()) {
                runtimePrefix.add(binaryObservation(mapping.witness(),
                        mapping.sourceTakenOutcome()));
            }
        }
        return new BranchReplayContract(
                new ArrayList<>(prefixByPosition.values()), runtimePrefix,
                selected.witness(), context);
    }

    public static BranchReplayContract fromJson(JsonObject json) {
        return fromJson(json, false);
    }

    /**
     * Decodes only the concrete branch schedule needed inside the replay JVM.
     * The source predicate can be a large propagated expression DAG; replay
     * matching needs its branch address and opposite outcome, not that value.
     */
    public static RuntimeSchedule runtimeScheduleFromJson(JsonObject json) {
        return runtimeScheduleFromJson(json, new JsonArray());
    }

    /**
     * Decodes the replay schedule and its statically proved bounded-loop
     * ranges. A loop predicate with symbolic support can then follow the
     * equivalent propagated value when iteration order changes; every other
     * event keeps its exact occurrence address.
     */
    public static RuntimeSchedule runtimeScheduleFromJson(
            JsonObject json, JsonArray retainedLoops) {
        if (primitiveInteger(json, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(primitiveString(json, "kind"))) {
            throw new IllegalArgumentException(
                    "unsupported binary branch replay contract schema");
        }
        JsonElement prefixElement = json.get("orderedPrefix");
        if (prefixElement == null || !prefixElement.isJsonArray()) {
            throw new IllegalArgumentException(
                    "orderedPrefix must be an array");
        }
        List<RuntimeWitness> prefix = new ArrayList<>();
        Set<String> events = new LinkedHashSet<>();
        for (JsonElement element : prefixElement.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "orderedPrefix entries must be witnesses");
            }
            RuntimeWitness witness = RuntimeWitness.from(
                    element.getAsJsonObject());
            if (!events.add(witness.decisionIdentity())) {
                throw new IllegalArgumentException(
                        "ordered prefix contains a missing or duplicate event");
            }
            prefix.add(witness);
        }
        JsonElement runtimeElement = json.get("runtimePrefix");
        if (runtimeElement == null || !runtimeElement.isJsonArray()) {
            throw new IllegalArgumentException(
                    "runtimePrefix must be an array");
        }
        List<ExactConcreteBranchObservation> runtimePrefix =
                new ArrayList<>();
        Set<String> runtimeEvents = new LinkedHashSet<>();
        for (JsonElement element : runtimeElement.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "runtimePrefix entries must be observations");
            }
            ExactConcreteBranchObservation observation =
                    ExactConcreteBranchObservation.fromJson(
                            element.getAsJsonObject());
            if (!runtimeEvents.add(runtimeIdentity(observation))) {
                throw new IllegalArgumentException(
                        "runtime prefix contains a missing or duplicate event");
            }
            runtimePrefix.add(observation);
        }
        RuntimeWitness source = RuntimeWitness.from(
                requiredObject(json, "source"));
        if (source.decisionOrdinal != 0) {
            throw new IllegalArgumentException(
                    "replay source must be a source-level branch witness");
        }
        if (!events.add(source.decisionIdentity())) {
            throw new IllegalArgumentException(
                    "source branch event must not appear in ordered prefix");
        }
        if (runtimeEvents.contains(source.runtimeIdentity())) {
            throw new IllegalArgumentException(
                    "source branch event must not appear in runtime prefix");
        }
        for (RuntimeWitness witness : prefix) {
            if (witness.decisionOrdinal > 0) continue;
            requireWitnessedInRuntimePrefix(runtimePrefix,
                    witness.runtimeIdentity(), witness.sourceTakenOutcome,
                    witness.siteId + "#" + witness.occurrence);
        }
        Map<String, RuntimeWitness> witnessed = new TreeMap<>();
        for (RuntimeWitness witness : prefix) {
            if (witness.decisionOrdinal == 0) {
                witnessed.put(witness.runtimeIdentity(), witness);
            }
        }
        LoopMembership loopCatalog = LoopMembership.decode(retainedLoops);
        LoopMembership loops = loopCatalog.fresh();
        List<RuntimeDecision> decisions = new ArrayList<>();
        for (ExactConcreteBranchObservation observation : runtimePrefix) {
            RuntimeWitness witness = witnessed.get(
                    runtimeIdentity(observation));
            String loopIdentity = loops.currentIdentity(
                    observation.siteId());
            decisions.add(RuntimeDecision.prefix(observation,
                    witness == null ? "" : witness.symbolicSupportDigest,
                    loopIdentity,
                    loops.isExitSite(observation.siteId())));
            loops.advance(observation.siteId(),
                    observation.exactDecisionToken());
        }
        String sourceToken = ExactConcreteBranchObservation
                .binaryDecisionToken(!source.sourceTakenOutcome);
        decisions.add(RuntimeDecision.source(source.siteId,
                source.occurrence, !source.sourceTakenOutcome,
                source.symbolicSupportDigest,
                loops.currentIdentity(source.siteId),
                loops.isExitSite(source.siteId)));
        loops.advance(source.siteId, sourceToken);
        enableBoundedLoopSupport(decisions);
        return new RuntimeSchedule(decisions, source.siteId, loopCatalog);
    }

    /**
     * Inside one proved bounded-loop invocation, propagated symbolic support
     * is the value address. Physical iteration ordinals are not stable for
     * unordered containers, and several elements may legitimately carry the
     * same propagated expression.
     *
     * <p>The prefix only, never the flipped decision.  A prefix event must
     * be reproduced as recorded -- same element, same outcome -- so the
     * element's own expression is the right address for it.  The source
     * event is the one event the replay must decide <em>differently</em>,
     * and it was being addressed by the support digest the SEED recorded at
     * it, so admission demanded the recorded value's digest and the flipped
     * outcome at once.  A support digest is a content hash over a fresh
     * JVM's own symbols and is not stable between two runs: in lane VM10 two
     * flip replays of the same planned occurrence published
     * BRANCH_SUPPORT.v1.ce0d0b14... and BRANCH_SUPPORT.v1.ba9e60ac... at the
     * same {@code removeExpiredKeys()#u15#1}, so the source event of every
     * primary matched nothing and six obligations were refused as "prefix
     * not yet complete: observed 2 of 3, still waiting for ... (the flipped
     * source decision)" while the site had executed all along.</p>
     *
     * <p>So the flipped decision is addressed the way every other occurrence
     * is -- its site, its loop invocation and its k -- and honoured by its
     * outcome: the flipped token admits, the recorded token is refused by
     * name as the wrong decision at that site.</p>
     */
    private static void enableBoundedLoopSupport(
            List<RuntimeDecision> decisions) {
        for (RuntimeDecision decision : decisions) {
            decision.supportAddressed = !decision.source
                    && !decision.loopIdentity.isEmpty()
                    && !decision.loopBoundary
                    && !decision.symbolicSupportDigest.isEmpty();
        }
    }

    /** Exact static membership plus seed-observed dynamic invocation groups. */
    private static final class LoopMembership {
        private final Map<String, String> loopByBranch = new TreeMap<>();
        private final Map<String, Set<String>> exitedLoopsByDecision =
                new TreeMap<>();
        private final Set<String> exitSites = new LinkedHashSet<>();
        private final Map<String, Integer> invocation = new TreeMap<>();

        private LoopMembership fresh() {
            LoopMembership copy = new LoopMembership();
            copy.loopByBranch.putAll(loopByBranch);
            copy.exitSites.addAll(exitSites);
            for (Map.Entry<String, Set<String>> entry
                    : exitedLoopsByDecision.entrySet()) {
                copy.exitedLoopsByDecision.put(entry.getKey(),
                        new LinkedHashSet<>(entry.getValue()));
            }
            return copy;
        }

        private String currentIdentity(String siteId) {
            String loop = loopByBranch.get(siteId);
            return loop == null || loop.isEmpty() ? ""
                    : loop + "\u0000" + invocation.getOrDefault(loop, 1);
        }

        private void advance(String siteId, String decisionToken) {
            Set<String> exited = exitedLoopsByDecision.get(
                    siteId + "\u0000" + decisionToken);
            if (exited != null) {
                for (String exitedLoop : exited) {
                    invocation.put(exitedLoop,
                            invocation.getOrDefault(exitedLoop, 1) + 1);
                }
            }
        }

        private boolean isExitSite(String siteId) {
            return exitSites.contains(siteId);
        }

        private static LoopMembership decode(JsonArray retainedLoops) {
            LoopMembership result = new LoopMembership();
            if (retainedLoops == null) return result;
            for (JsonElement element : retainedLoops) {
                if (element == null || !element.isJsonObject()) continue;
                JsonObject loop = element.getAsJsonObject();
                String identity = primitiveString(loop,
                        LoopBoundPolicy.RUNTIME_LOOP_ID);
                JsonElement members = loop.get(
                        LoopBoundPolicy.LOOP_INNERMOST_BRANCH_SITE_IDS);
                if (identity.isEmpty() || members == null
                        || !members.isJsonArray()) {
                    continue;
                }
                for (JsonElement member : members.getAsJsonArray()) {
                    if (member == null || !member.isJsonPrimitive()
                            || !member.getAsJsonPrimitive().isString()
                            || member.getAsString().trim().isEmpty()) {
                        throw new IllegalArgumentException(
                                "retained loop has malformed branch "
                                        + "membership");
                    }
                    String site = member.getAsString().trim();
                    String held = result.loopByBranch.put(site, identity);
                    if (held != null && !held.equals(identity)) {
                        throw new IllegalArgumentException(
                                "branch belongs to multiple innermost loops: "
                                        + site);
                    }
                }
                JsonElement encodedExits = loop.get(
                        LoopBoundPolicy.LOOP_EXIT_DECISIONS);
                if (encodedExits == null || !encodedExits.isJsonArray()) {
                    continue;
                }
                for (JsonElement encodedExit
                        : encodedExits.getAsJsonArray()) {
                    if (encodedExit == null
                            || !encodedExit.isJsonObject()) {
                        throw new IllegalArgumentException(
                                "retained loop has malformed exit decision");
                    }
                    JsonObject exit = encodedExit.getAsJsonObject();
                    String site = primitiveString(exit, "siteId");
                    String token = primitiveString(exit, "decisionToken");
                    if (site.isEmpty() || token.isEmpty()) {
                        throw new IllegalArgumentException(
                                "retained loop has incomplete exit decision");
                    }
                    result.exitSites.add(site);
                    result.exitedLoopsByDecision.computeIfAbsent(
                            site + "\u0000" + token,
                            ignored -> new LinkedHashSet<>()).add(identity);
                }
            }
            return result;
        }
    }

    /** Branch metadata needed to validate replay order without its SMT DAG. */
    private static final class RuntimeWitness {
        private final String siteId;
        private final int occurrence;
        private final boolean sourceTakenOutcome;
        private final int decisionOrdinal;
        private final String symbolicSupportDigest;

        private RuntimeWitness(String siteId, int occurrence,
                               boolean sourceTakenOutcome,
                               int decisionOrdinal,
                               String symbolicSupportDigest) {
            this.siteId = siteId;
            this.occurrence = occurrence;
            this.sourceTakenOutcome = sourceTakenOutcome;
            this.decisionOrdinal = decisionOrdinal;
            this.symbolicSupportDigest = symbolicSupportDigest;
        }

        private static RuntimeWitness from(JsonObject json) {
            if (primitiveInteger(json, "schemaVersion", -1)
                    != BranchWitness.SCHEMA_VERSION
                    || !BranchWitness.KIND.equals(primitiveString(json,
                    "kind"))) {
                throw new IllegalArgumentException(
                        "unsupported binary branch witness schema");
            }
            JsonObject site = requiredObject(json, "site");
            String siteId = primitiveString(site, "siteId");
            String method = primitiveString(site, "method");
            int unitIndex = primitiveInteger(site, "unitIndex", -1);
            int occurrence = primitiveInteger(site, "occurrence", -1);
            int vmPcIndex = primitiveInteger(json, "vmPcIndex", -1);
            int decisionOrdinal = primitiveInteger(json,
                    "decisionOrdinal", 0);
            String normalization = primitiveString(json,
                    "predicateNormalization");
            JsonElement outcome = json.get("sourceTakenOutcome");
            JsonElement predicate = json.get("sourceSatisfiedPredicate");
            boolean pcPredicate = BranchWitness.PC_PREDICATE_NORMALIZATION
                    .equals(normalization);
            String support = primitiveString(json,
                    "symbolicSupportDigest");
            if (siteId.isEmpty() || method.isEmpty() || unitIndex < 0
                    || occurrence <= 0 || vmPcIndex < 0
                    || outcome == null || !outcome.isJsonPrimitive()
                    || !outcome.getAsJsonPrimitive().isBoolean()
                    || predicate == null || predicate.isJsonNull()
                    || !BranchWitness.IDENTITY_NORMALIZATION.equals(
                    normalization)
                    && !BranchWitness.CMP_NORMALIZATION.equals(normalization)
                    && !pcPredicate
                    || decisionOrdinal < 0
                    || decisionOrdinal == 0 && pcPredicate
                    || decisionOrdinal > 0 && !pcPredicate
                    || !support.isEmpty()
                    && !BranchPredicateAlgebra.validSymbolicSupportDigest(
                    support)) {
                throw new IllegalArgumentException(
                        "replay branch witness schedule is incomplete");
            }
            return new RuntimeWitness(siteId, occurrence,
                    outcome.getAsBoolean(), decisionOrdinal,
                    support);
        }

        private String decisionIdentity() {
            return runtimeIdentity() + "\u0000" + decisionOrdinal;
        }

        private String runtimeIdentity() {
            return siteId + "\u0000" + occurrence;
        }
    }

    static BranchReplayContract fromImmutableJson(JsonObject json) {
        return fromJson(json, true);
    }

    private static BranchReplayContract fromJson(JsonObject json,
                                                 boolean immutablePredicates) {
        if (primitiveInteger(json, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(primitiveString(json, "kind"))) {
            throw new IllegalArgumentException(
                    "unsupported binary branch replay contract schema");
        }
        JsonElement prefixElement = json.get("orderedPrefix");
        if (prefixElement == null || !prefixElement.isJsonArray()) {
            throw new IllegalArgumentException(
                    "orderedPrefix must be an array");
        }
        List<BranchWitness> prefix = new ArrayList<>();
        for (JsonElement element : prefixElement.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "orderedPrefix entries must be witnesses");
            }
            prefix.add(immutablePredicates
                    ? BranchWitness.fromImmutableJson(
                    element.getAsJsonObject())
                    : BranchWitness.fromJson(element.getAsJsonObject()));
        }
        JsonElement runtimeElement = json.get("runtimePrefix");
        if (runtimeElement == null || !runtimeElement.isJsonArray()) {
            throw new IllegalArgumentException(
                    "runtimePrefix must be an array");
        }
        List<ExactConcreteBranchObservation> runtimePrefix =
                new ArrayList<>();
        for (JsonElement element : runtimeElement.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "runtimePrefix entries must be observations");
            }
            runtimePrefix.add(ExactConcreteBranchObservation.fromJson(
                    element.getAsJsonObject()));
        }
        JsonObject encodedSource = requiredObject(json, "source");
        BranchWitness source = immutablePredicates
                ? BranchWitness.fromImmutableJson(encodedSource)
                : BranchWitness.fromJson(encodedSource);
        return new BranchReplayContract(prefix, runtimePrefix, source, null);
    }

    public JsonObject toJson() {
        return toJson(true);
    }

    /** Artifact-builder view which preserves decoder-owned expression DAGs. */
    JsonObject toImmutableJsonView() {
        return toJson(false);
    }

    private JsonObject toJson(boolean defensivePredicates) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        JsonArray prefix = new JsonArray();
        for (BranchWitness witness : orderedPrefix) {
            prefix.add(defensivePredicates ? witness.toJson()
                    : witness.toImmutableJsonView());
        }
        result.add("orderedPrefix", prefix);
        JsonArray runtime = new JsonArray();
        for (ExactConcreteBranchObservation observation : runtimePrefix) {
            runtime.add(observation.toJson());
        }
        result.add("runtimePrefix", runtime);
        result.add("source", defensivePredicates ? source.toJson()
                : source.toImmutableJsonView());
        return defensivePredicates
                ? (JsonObject) CanonicalJson.copy(result) : result;
    }

    public void addTo(JsonObject target) {
        if (solverPathContext == null) {
            throw new IllegalStateException(
                    "solver context is unavailable for parsed contract");
        }
        target.add("replayContract", toJson(false));
        target.add("solverPathContext", solverPathContext.toJson());
    }

    public List<BranchWitness> orderedPrefix() {
        return orderedPrefix;
    }

    /** Exact source-level decisions that must precede the flipped branch. */
    /** Predicate-free projection consumed by the runtime replay matcher. */
    public static final class RuntimeSchedule {
        private final List<RuntimeDecision> decisions;
        private final String sourceSiteId;
        private final LoopMembership loopMembership;

        private RuntimeSchedule(
                List<RuntimeDecision> decisions,
                String sourceSiteId,
                LoopMembership loopMembership) {
            this.decisions = Collections.unmodifiableList(
                    new ArrayList<>(decisions));
            this.sourceSiteId = sourceSiteId;
            this.loopMembership = loopMembership == null
                    ? new LoopMembership() : loopMembership.fresh();
        }

        /** Compact events consumed by the runtime replay matcher. */
        public List<RuntimeDecision> decisions() { return decisions; }

        public String sourceSiteId() { return sourceSiteId; }

    }

    /** Predicate-free replay event plus its small, capture-time support id. */
    public static final class RuntimeDecision {
        private final String siteId;
        private final int occurrence;
        private final String decisionToken;
        private final String symbolicSupportDigest;
        private final String loopIdentity;
        private final boolean loopBoundary;
        private final boolean source;
        private boolean supportAddressed;

        private RuntimeDecision(String siteId, int occurrence,
                                String decisionToken,
                                String symbolicSupportDigest,
                                String loopIdentity, boolean loopBoundary,
                                boolean source) {
            this.siteId = siteId;
            this.occurrence = occurrence;
            this.decisionToken = decisionToken;
            this.symbolicSupportDigest = symbolicSupportDigest == null
                    ? "" : symbolicSupportDigest;
            this.loopIdentity = loopIdentity == null ? "" : loopIdentity;
            this.loopBoundary = loopBoundary;
            this.source = source;
        }

        private static RuntimeDecision prefix(
                ExactConcreteBranchObservation observation,
                String support, String loopIdentity, boolean loopBoundary) {
            return new RuntimeDecision(observation.siteId(),
                    observation.occurrence(), observation.exactDecisionToken(),
                    support, loopIdentity, loopBoundary, false);
        }

        private static RuntimeDecision source(
                String siteId, int occurrence, boolean outcome,
                String support, String loopIdentity, boolean loopBoundary) {
            return new RuntimeDecision(siteId, occurrence,
                    ExactConcreteBranchObservation.binaryDecisionToken(
                            outcome), support, loopIdentity, loopBoundary,
                    true);
        }

        public String siteId() { return siteId; }
        public int occurrence() { return occurrence; }
        public String decisionToken() { return decisionToken; }
        public String symbolicSupportDigest() {
            return symbolicSupportDigest;
        }
        public String loopIdentity() { return loopIdentity; }
        public boolean supportAddressed() { return supportAddressed; }
        public boolean source() { return source; }
    }

    /**
     * One replay matcher shared by the runtime and importer. A supported
     * branch inside a statically retained loop follows the propagated value
     * and required decision when iteration order changes. Every other branch
     * keeps the exact source-level occurrence address.
     */
    public static final class ReplayProgress {
        /** The replay has not yet seen any event of the required prefix. */
        static final String PREFIX_UNOBSERVED = "prefix not yet observed";
        /** The replay is mid-prefix: some required event is outstanding. */
        static final String PREFIX_INCOMPLETE = "prefix not yet complete";

        private final List<ReplayEvent> expected = new ArrayList<>();
        private final LoopMembership actualLoops;
        private String failure = PREFIX_UNOBSERVED;
        private boolean contradiction;

        public ReplayProgress(RuntimeSchedule contract) {
            actualLoops = contract == null ? new LoopMembership()
                    : contract.loopMembership.fresh();
            if (contract == null) return;
            for (RuntimeDecision decision : contract.decisions()) {
                add(decision);
            }
        }

        private void add(RuntimeDecision decision) {
            ReplayEvent event = new ReplayEvent(decision.siteId(),
                    decision.occurrence(), decision.decisionToken(),
                    decision.symbolicSupportDigest(),
                    decision.loopIdentity(), decision.supportAddressed(),
                    decision.source());
            if (!expected.isEmpty()
                    && expected.get(expected.size() - 1)
                    .sameOccurrence(event)) {
                ReplayEvent prior = expected.get(expected.size() - 1);
                if (!prior.decisionToken.equals(event.decisionToken)
                        || prior.source != event.source) {
                    throw new IllegalArgumentException(
                            "conflicting replay events at " + event.siteId
                                    + '#' + event.occurrence);
                }
                return;
            }
            expected.add(event);
        }

        public boolean observeBinary(
                String siteId, int occurrence, boolean outcome) {
            return observeBinary(siteId, occurrence, outcome, "");
        }

        public boolean observeBinary(
                String siteId, int occurrence, boolean outcome,
                String symbolicSupportDigest) {
            return observeDecision(siteId, occurrence,
                    ExactConcreteBranchObservation.binaryDecisionToken(
                            outcome), symbolicSupportDigest);
        }

        public boolean observeSwitch(
                String siteId, int occurrence, String branchKind,
                List<Integer> caseKeys, int observedSuccessorIndex) {
            return observeDecision(siteId, occurrence,
                    ExactConcreteBranchObservation.switchDecisionToken(
                            branchKind, caseKeys, observedSuccessorIndex), "");
        }

        /** True exactly when this observation consumed the planned source. */
        public boolean observeDecision(
                String siteId, int occurrence, String decisionToken,
                String symbolicSupportDigest) {
            if (expected.isEmpty()) return true;
            String actualLoopIdentity = actualLoops.currentIdentity(
                    empty(siteId));
            ReplayEvent actual = new ReplayEvent(siteId, occurrence,
                    decisionToken, empty(symbolicSupportDigest),
                    actualLoopIdentity, false, false);
            // The task's exact CFG catalog proves this (site, decision) is a
            // physical loop exit even when replay divergence makes it absent
            // from the expected prefix. Advance after naming this event's
            // current invocation and before observing the next one.
            actualLoops.advance(empty(siteId), empty(decisionToken));
            if (failed() || complete()) return false;
            // Nothing after the flipped decision is part of the contract,
            // later turns of its own loop included.  A flip at #u15#1
            // changes what the rest of that loop does -- that is what a flip
            // is for -- and #u15#2 is then an execution the recording never
            // had, not a prefix event to reproduce.  It was being compared:
            // a prefix event inside a bounded loop is addressed by the
            // propagated value of the element it tested, and the same
            // element decided again on a later turn carries the same
            // digest, so the later turn matched an earlier expectation and
            // refused on its outcome -- "wrong decision at
            // removeExpiredKeys()#u15#2", nine times on lane VM12, each of
            // them a flip working.
            if (afterFlippedDecision(actual)) return false;
            int selected = matchingEvent(actual);
            if (selected < 0) return false;
            ReplayEvent wanted = expected.get(selected);
            int blocked = precedingBarrier(selected, wanted);
            if (blocked >= 0) {
                ReplayEvent barrier = expected.get(blocked);
                failure = "reached " + empty(siteId) + '#' + occurrence
                        + " before replay prefix event " + barrier.siteId
                        + '#' + barrier.occurrence;
                return false;
            }
            if (!wanted.decisionToken.equals(empty(decisionToken))) {
                failure = "wrong decision at " + empty(siteId) + '#'
                        + occurrence;
                return false;
            }
            wanted.consumed = true;
            if (wanted.source && wanted.supportAddressed) {
                // The source terminates the required prefix.  Earlier seed
                // iterations of this same dynamic loop invocation have
                // become replay suffix once their element moves after it;
                // the flipped branch may prevent them from executing at all.
                for (ReplayEvent event : expected) {
                    if (!event.consumed && wanted.loopIdentity.equals(
                            event.loopIdentity)) {
                        event.consumed = true;
                    }
                }
            }
            failure = complete() ? "" : incomplete();
            return wanted.source;
        }

        /** Whether this observation is past the flipped decision. */
        private boolean afterFlippedDecision(ReplayEvent actual) {
            for (ReplayEvent event : expected) {
                if (!event.source) continue;
                return event.siteId.equals(actual.siteId)
                        && actual.occurrence > event.occurrence;
            }
            return false;
        }

        private int matchingEvent(ReplayEvent actual) {
            for (int index = 0; index < expected.size(); index++) {
                ReplayEvent candidate = expected.get(index);
                if (!candidate.consumed && candidate.matches(actual)) {
                    return index;
                }
            }
            return -1;
        }

        /** A loop case may move only across cases of that same exact loop. */
        private int precedingBarrier(int selected, ReplayEvent wanted) {
            for (int index = 0; index < selected; index++) {
                ReplayEvent prior = expected.get(index);
                if (prior.consumed) continue;
                if (!wanted.loopIdentity.isEmpty()
                        && wanted.loopIdentity.equals(prior.loopIdentity)) {
                    continue;
                }
                return index;
            }
            return -1;
        }

        public boolean complete() {
            if (contradiction) return false;
            for (ReplayEvent event : expected) {
                if (!event.consumed) return false;
            }
            return true;
        }

        /**
         * What the prefix is still waiting for, as a reader can act on.
         *
         * <p>Every shortfall used to publish the bare words {@code prefix
         * not yet complete}, which the runtime forwards verbatim into
         * {@code REGION_REPLAY_PREFIX_UNMATCHED} and the campaign into a
         * {@code PATH_FLIP_REPLAY_NOT_ADMITTED} gap.  Ten abandoned
         * obligations then carry ten identical strings, and nothing says
         * whether the replay stopped short of the flipped decision, took a
         * different route to it, or reached it and left an earlier recorded
         * decision behind -- which are three different defects with three
         * different fixes.  The expected list is right here, so name how
         * much of it was observed and the first event still outstanding.
         * The sentence still begins with the original words, so anything
         * matching on that prefix keeps working.</p>
         */
        private String incomplete() {
            int observed = 0;
            ReplayEvent outstanding = null;
            for (ReplayEvent event : expected) {
                if (event.consumed) {
                    observed++;
                } else if (outstanding == null) {
                    outstanding = event;
                }
            }
            if (outstanding == null) return PREFIX_INCOMPLETE;
            return PREFIX_INCOMPLETE + ": observed " + observed + " of "
                    + expected.size() + ", still waiting for "
                    + outstanding.siteId + '#' + outstanding.occurrence
                    + (outstanding.source
                    ? " (the flipped source decision)" : "");
        }

        public boolean failed() {
            return contradiction || !complete()
                    && !failure.startsWith(PREFIX_UNOBSERVED)
                    && !failure.startsWith(PREFIX_INCOMPLETE);
        }

        public String failure() { return failure; }
    }

    private static final class ReplayEvent {
        private final String siteId;
        private final int occurrence;
        private final String decisionToken;
        private final String symbolicSupportDigest;
        private final String loopIdentity;
        private final boolean supportAddressed;
        private final boolean source;
        private boolean consumed;

        private ReplayEvent(String siteId, int occurrence,
                            String decisionToken,
                            String symbolicSupportDigest,
                            String loopIdentity, boolean supportAddressed,
                            boolean source) {
            this.siteId = empty(siteId);
            this.occurrence = occurrence;
            this.decisionToken = empty(decisionToken);
            this.symbolicSupportDigest = empty(symbolicSupportDigest);
            this.loopIdentity = empty(loopIdentity);
            this.supportAddressed = supportAddressed;
            this.source = source;
        }

        private boolean sameOccurrence(ReplayEvent other) {
            return other != null && occurrence == other.occurrence
                    && siteId.equals(other.siteId);
        }

        private boolean matches(ReplayEvent actual) {
            if (actual == null || !siteId.equals(actual.siteId)) {
                return false;
            }
            if (!loopIdentity.isEmpty()
                    && !loopIdentity.equals(actual.loopIdentity)) {
                return false;
            }
            return supportAddressed
                    ? !actual.symbolicSupportDigest.isEmpty()
                    && loopIdentity.equals(actual.loopIdentity)
                    && symbolicSupportDigest.equals(
                    actual.symbolicSupportDigest)
                    && decisionToken.equals(actual.decisionToken)
                    : occurrence == actual.occurrence;
        }

    }

    private static String empty(String value) {
        return value == null ? "" : value;
    }

    public BranchWitness source() {
        return source;
    }

    public boolean requiredTakenOutcome() {
        return !source.sourceTakenOutcome();
    }

    public JsonElement requiredSatisfiedPredicate() {
        return BranchPredicateAlgebra.complementView(
                source.sourceSatisfiedPredicateView());
    }

    public JsonArray requiredPathPredicates() {
        JsonArray result = new JsonArray();
        for (BranchWitness witness : orderedPrefix) {
            result.add(witness.sourceSatisfiedPredicateView());
        }
        result.add(requiredSatisfiedPredicate());
        return result;
    }

    private static String eventIdentity(BranchWitness witness) {
        return witness.decisionIdentity();
    }

    private static ExactConcreteBranchObservation binaryObservation(
            BranchWitness witness, boolean outcome) {
        return ExactConcreteBranchObservation.attested(witness.siteId(),
                witness.method(), witness.unitIndex(), witness.occurrence(),
                outcome);
    }

    private static String sourceIdentity(BranchWitness witness) {
        return witness.siteId() + "\u0000" + witness.occurrence();
    }

    private static String runtimeIdentity(
            ExactConcreteBranchObservation observation) {
        return observation.siteId() + "\u0000" + observation.occurrence();
    }

}
