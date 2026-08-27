package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.concolic.ContainerSmtCodec;
import edu.uva.liftlab.graphchecker.concolic.InitialContainerObservation;
import edu.uva.liftlab.graphchecker.concolic.VmHandoffEvidence;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import edu.uva.liftlab.graphchecker.concolic.SummaryBranchMapping;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Immutable, once-decoded view of one imported concolic path summary.  The
 * original summary is retained only as the attested replay payload.
 */
public final class PathObservation {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private final JsonObject raw;
    private final Scope scope;
    private final List<SummaryBranchMapping> branchMappings;
    private final String branchMappingIssue;
    private final AlphaNormalizer alpha;
    private final String pathKey;
    private final List<Integer> relationPathPositions;
    private final JsonArray relationPathCondition;
    private final String relationGuardKey;
    private final String relationKey;

    private PathObservation(JsonObject summary, JsonObject task) {
        this.raw = summary.deepCopy();
        this.scope = Scope.decode(raw, task);
        List<SummaryBranchMapping> decoded = Collections.emptyList();
        String issue = "";
        try {
            decoded = SummaryBranchMapping.fromSummary(raw);
        } catch (IllegalArgumentException malformed) {
            issue = firstNonBlank(malformed.getMessage(), "UNKNOWN");
        }
        this.branchMappings = Collections.unmodifiableList(decoded);
        this.branchMappingIssue = issue;
        this.alpha = new AlphaNormalizer(raw);
        this.pathKey = stablePathKey(raw, scope,
                raw.get("pathCondition"), alpha);
        this.relationPathPositions = Collections.unmodifiableList(
                projectRelationPathCondition(raw, scope, branchMappings,
                        alpha));
        this.relationPathCondition = conditionsAt(
                array(raw, "pathCondition"), relationPathPositions);
        String containerCapacityIssue = InitialContainerObservation
                .failureRelevantCapacityIssue(relationPathCondition,
                        raw.get("outputExpressions"));
        if (!containerCapacityIssue.isEmpty()) {
            throw new IllegalArgumentException(containerCapacityIssue);
        }
        this.relationGuardKey = CanonicalJson.sha256(alphaCanonical(
                relationPathCondition, new AlphaNormalizer(raw)));
        this.relationKey = stablePathKey(raw, scope,
                relationPathCondition, new AlphaNormalizer(raw));
    }

    public static PathObservation decode(JsonObject summary, JsonObject task) {
        if (summary == null) {
            throw new IllegalArgumentException("summary is required");
        }
        return new PathObservation(summary, task);
    }

    public String regionId() {
        return scope.outputClosure == null ? string(raw, "regionId")
                : scope.outputClosure.producer().regionId();
    }
    public String sourceTaskId() { return string(raw, "taskId"); }
    public String occurrenceId() { return string(raw, "occurrenceId"); }

    /**
     * OCC-1: one task's address may be entered several times, and every
     * compatible activation is published as its own occurrence rather than
     * one being answered and the rest reported as an ambiguous address.
     *
     * <p>These three members travel together.  A row that states no
     * {@link #ACTIVATION_ORDINAL} is a pre-OCC-1 row and is read exactly as
     * before: one occurrence, the planned one.</p>
     */
    public static final String ACTIVATION_ORDINAL = "activationOrdinal";
    /** The address the task planned, shared by every activation of it. */
    public static final String PLANNED_OCCURRENCE_ID = "plannedOccurrenceId";
    /** Whether this activation exited through the selected target throw. */
    public static final String TARGET_REACHED = "targetReached";

    /** This activation's ordinal, or 0 when the row states none. */
    public int activationOrdinal() {
        return integer(raw, ACTIVATION_ORDINAL, 0);
    }

    /** Whether this observation is one activation among a task's several. */
    public boolean statesActivation() { return activationOrdinal() >= 1; }

    /** The planned address; the occurrence itself when none is stated. */
    public String plannedOccurrenceId() {
        String planned = string(raw, PLANNED_OCCURRENCE_ID);
        return planned.isEmpty() ? occurrenceId() : planned;
    }

    /** Whether this activation reached the target; false when unstated. */
    public boolean targetReached() {
        return bool(raw, TARGET_REACHED, false);
    }

    /**
     * OCC-1: the planned address behind one occurrence id.
     *
     * <p>An activation occurrence is named {@code <plannedAddress>#a<ordinal>}.
     * A relation, a target reach query and a region plan are all keyed on the
     * planned address the campaign scheduled, so a match between one of them
     * and a per-activation summary is made on the address, not the activation.
     * A string that carries no activation suffix -- a pre-OCC-1 occurrence --
     * is returned unchanged.</p>
     */
    public static String plannedOccurrenceOf(String occurrenceId) {
        String value = occurrenceId == null ? "" : occurrenceId;
        int marker = value.lastIndexOf("#a");
        if (marker <= 0 || marker + 2 >= value.length()) return value;
        for (int index = marker + 2; index < value.length(); index++) {
            if (!Character.isDigit(value.charAt(index))) return value;
        }
        return value.substring(0, marker);
    }
    public String sourceKey() { return string(raw, "sourceKey"); }
    public boolean relationallyComplete() {
        return bool(raw, "relationallyComplete", false);
    }
    public Scope scope() { return scope; }
    public String pathKey() { return pathKey; }
    public List<SummaryBranchMapping> branchMappings() {
        return branchMappings;
    }
    public String branchMappingIssue() { return branchMappingIssue; }
    public JsonObject outputExpressions() {
        return object(raw, "outputExpressions").deepCopy();
    }
    public JsonArray interactionEvents() {
        return array(raw, RelationSummary.INTERACTION_EVENTS).deepCopy();
    }
    /** The C2 free roots this case reported; empty when it reported none.
     *  The census itself is required: a summary that never stated it is
     *  refused by {@link SymbolicSourceEvidence#freeSymbolsOf}. */
    public JsonArray freeSymbols() {
        JsonArray result = new JsonArray();
        for (JsonObject free : SymbolicSourceEvidence.freeSymbolsOf(raw)) {
            result.add(free);
        }
        return result;
    }
    public JsonArray symbolicSourceEvidence() {
        return array(raw, SymbolicSourceEvidence.FIELD).deepCopy();
    }
    public JsonArray pathLoopCounts() {
        return array(raw, LoopBoundPolicy.PATH_LOOP_COUNTS).deepCopy();
    }
    /** Missing/ambiguous loop-count evidence; coverage, not a case rewrite. */
    public JsonArray pathLoopCountGaps() {
        return array(raw, LoopBoundPolicy.PATH_LOOP_COUNT_GAPS).deepCopy();
    }
    public JsonArray relationPathCondition() {
        return relationPathCondition.deepCopy();
    }
    /** Recorded-path positions {@link #relationPathCondition()} kept.  README
     *  PC-1 drops rows from inside the prefix, so a consumer cutting the
     *  projected guard must cut on these recorded positions. */
    public List<Integer> relationPathConditionPositions() {
        return relationPathPositions;
    }
    public String relationGuardKey() { return relationGuardKey; }
    public String relationKey() { return relationKey; }
    public JsonArray edgeBindings() {
        return array(raw, "edgeBindings").deepCopy();
    }

    public TargetReachEvent targetReachEvent() {
        JsonElement encoded = raw.get(TargetReachEvent.FIELD);
        return encoded == null ? null : TargetReachEvent.decode(encoded);
    }

    /** Canonical carrier for the runtime event that makes a target path
     *  eligible for composition.  Stricter than the generic accessors:
     *  target identity is an authority, so unknown members and coercions are
     *  schema errors. */
    public static final class TargetReachEvent {
        public static final String FIELD = "targetReach";
        public static final String KIND = "TARGET_REACH_EVENT";

        private final String siteId;
        private final int occurrence;
        private final boolean outcome;

        private TargetReachEvent(String siteId, int occurrence,
                                 boolean outcome) {
            this.siteId = siteId;
            this.occurrence = occurrence;
            this.outcome = outcome;
        }

        public static TargetReachEvent decode(JsonElement encoded) {
            if (encoded == null || !encoded.isJsonObject()) {
                throw new IllegalArgumentException(
                        FIELD + " must be an object");
            }
            JsonObject event = encoded.getAsJsonObject();
            if (event.size() != 4
                    || !event.has("kind") || !event.has("siteId")
                    || !event.has("occurrence") || !event.has("outcome")) {
                throw new IllegalArgumentException(
                        FIELD + " must contain exactly kind, siteId, "
                                + "occurrence and outcome");
            }
            JsonElement kind = event.get("kind");
            JsonElement site = event.get("siteId");
            JsonElement ordinal = event.get("occurrence");
            JsonElement taken = event.get("outcome");
            if (!kind.isJsonPrimitive()
                    || !kind.getAsJsonPrimitive().isString()
                    || !KIND.equals(kind.getAsString())) {
                throw new IllegalArgumentException(
                        FIELD + ".kind must be " + KIND);
            }
            if (!site.isJsonPrimitive()
                    || !site.getAsJsonPrimitive().isString()
                    || site.getAsString().trim().isEmpty()) {
                throw new IllegalArgumentException(
                        FIELD + ".siteId must be a nonempty string");
            }
            final int occurrence;
            try {
                if (!ordinal.isJsonPrimitive()
                        || !ordinal.getAsJsonPrimitive().isNumber()) {
                    throw new ArithmeticException("not a number");
                }
                occurrence = new BigDecimal(
                        ordinal.getAsString()).intValueExact();
            } catch (RuntimeException malformed) {
                throw new IllegalArgumentException(
                        FIELD + ".occurrence must be an exact integer",
                        malformed);
            }
            if (occurrence < 1) {
                throw new IllegalArgumentException(
                        FIELD + ".occurrence must be positive");
            }
            if (!taken.isJsonPrimitive()
                    || !taken.getAsJsonPrimitive().isBoolean()) {
                throw new IllegalArgumentException(
                        FIELD + ".outcome must be a boolean");
            }
            return new TargetReachEvent(site.getAsString(), occurrence,
                    taken.getAsBoolean());
        }

        public String siteId() { return siteId; }
        public int occurrence() { return occurrence; }
        public boolean outcome() { return outcome; }

        public boolean matches(String site, int ordinal, boolean taken) {
            return siteId.equals(site) && occurrence == ordinal
                    && outcome == taken;
        }

        public JsonObject toJson() {
            JsonObject event = new JsonObject();
            event.addProperty("kind", KIND);
            event.addProperty("siteId", siteId);
            event.addProperty("occurrence", occurrence);
            event.addProperty("outcome", outcome);
            return event;
        }
    }

    /** Published field versions, resolved reads and the session event ledger
     *  this path recorded.  Case-local: two paths never share it. */
    public JsonObject recordedSharedState() {
        return object(raw, SharedStateEvidence.RECORDED_FIELD).deepCopy();
    }

    /**
     * Where this path's execution actually ended.  README
     * {@code case_k = ... AND terminal_k}: case-local, because two paths of
     * one occurrence routinely end differently and a summary stating only the
     * guard and the outputs cannot tell a completed case from a bounded
     * prefix.  Derived here so the importer's three exit members have one
     * reading.
     */
    public JsonObject terminal() {
        JsonObject terminal = new JsonObject();
        String thrown = string(raw, "exceptionType");
        terminal.addProperty("kind", !thrown.isEmpty() ? "THROW"
                : bool(raw, "boundedExit", false) ? "BOUND"
                : bool(raw, "normalExit", false) ? "NORMAL" : "UNSTATED");
        if (!thrown.isEmpty()) terminal.addProperty("exceptionType", thrown);
        return terminal;
    }

    /** VM handoffs this path attached, as case-local references into the
     *  session ledger: another path's handoff is that path's event. */
    public java.util.List<JsonObject> vmHandoffEvents() {
        return VmHandoffEvidence.eventsOf(raw);
    }

    /** The output ports this path actually produced: a lowered expression or
     *  a declared interaction event is equally a production of the port. */
    public Set<String> producedOutputPorts() {
        Set<String> covered = new TreeSet<>(
                object(raw, "outputExpressions").keySet());
        for (JsonElement element : interactionEvents()) {
            if (!element.isJsonObject()) continue;
            String port = string(element.getAsJsonObject(), "portId");
            if (!port.isEmpty()) covered.add(port);
        }
        return covered;
    }

    public boolean hasExactOutputSet(Set<String> outputPorts) {
        return producedOutputPorts().equals(new TreeSet<>(outputPorts));
    }

    public JsonArray prefixBefore(int conditionIndex) {
        JsonArray prefix = new JsonArray();
        JsonArray conditions = array(raw, "pathCondition");
        for (int index = 0; index < conditionIndex; index++) {
            prefix.add(conditions.get(index).deepCopy());
        }
        return prefix;
    }

    public String flipKey(SummaryBranchMapping mapping,
                          boolean desiredOutcome) {
        StringBuilder value = new StringBuilder();
        component(value, regionId());
        component(value, sourceKey());
        component(value, occurrenceId());
        component(value, scope.identity);
        component(value, alphaCanonical(
                prefixBefore(mapping.summaryPcIndex()), alpha));
        component(value, mapping.siteId());
        component(value, String.valueOf(mapping.occurrence()));
        component(value, String.valueOf(mapping.decisionOrdinal()));
        component(value, String.valueOf(desiredOutcome));
        return CanonicalJson.sha256(value.toString());
    }

    public JsonObject replayPayload() { return raw.deepCopy(); }
    public static final class Scope {
        private final ClosureGoalKind goalKind;
        private final String goalId;
        private final LoopBoundPolicy loopBound;
        private final OutputClosureContract outputClosure;
        private final Set<String> branchSites;
        private final String identity;

        private Scope(ClosureGoalKind goalKind, String goalId,
                      LoopBoundPolicy loopBound,
                      OutputClosureContract outputClosure,
                      Set<String> branchSites, String identity) {
            this.goalKind = goalKind;
            this.goalId = goalId;
            this.loopBound = loopBound;
            this.outputClosure = outputClosure;
            this.branchSites = Collections.unmodifiableSet(branchSites);
            this.identity = identity;
        }

        public static Scope decode(JsonObject summary, JsonObject task) {
            JsonObject canonical = summary != null ? summary : task;
            if (canonical == null) {
                throw new IllegalArgumentException(
                        "closure goal is required");
            }
            ClosureGoalKind goalKind = ClosureGoalKind.fromTask(canonical);
            String goalId = string(canonical, "goalId");
            if (goalId.isEmpty()) {
                throw new IllegalArgumentException(
                        "closure goal is required");
            }
            JsonObject loopBoundSource = canonical.has(
                    LoopBoundPolicy.FIELD) ? canonical : task;
            LoopBoundPolicy loopBound = LoopBoundPolicy.decode(
                    loopBoundSource);
            if (goalKind.capturesTargetReach()) {
                JsonObject source = task != null ? task : canonical;
                Set<String> sites = new LinkedHashSet<>();
                String targetMethod = string(source, "targetMethod");
                for (JsonElement element : array(source, "branches")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject branch = element.getAsJsonObject();
                    if (!"EXPLORE".equals(string(branch, "policy"))) continue;
                    String site = string(branch, "siteId");
                    if (!site.isEmpty() && (targetMethod.isEmpty()
                            || site.startsWith(targetMethod + "#"))) {
                        sites.add(site);
                    }
                }
                String region = firstNonBlank(string(source, "regionId"),
                        string(canonical, "regionId"));
                String occurrence = firstNonBlank(string(source,
                        "occurrenceId"), string(canonical,
                        "occurrenceId"));
                return new Scope(goalKind, goalId, loopBound, null, sites,
                        "TARGET_REACH_CLOSURE_V1\n" + goalId + "\n"
                                + region + "\n" + occurrence + "\n"
                                + targetMethod + "\n"
                                + loopBound.identity());
            }
            OutputClosureContract contract = OutputClosureCodec.decode(
                    canonical);
            return new Scope(goalKind, goalId, loopBound, contract,
                    new LinkedHashSet<>(
                            contract.executionScope().branchSites()),
                    "OUTPUT_RELATION_CLOSURE_V1\n" + goalId + "\n"
                            + contract.demandKey() + "\n"
                            + contract.closureFingerprint() + "\n"
                            + loopBound.identity());
        }

        public ClosureGoalKind goalKind() { return goalKind; }
        public String goalId() { return goalId; }
        public LoopBoundPolicy loopBound() { return loopBound; }
        public OutputClosureContract outputClosure() { return outputClosure; }
        public Set<String> branchSites() { return branchSites; }
        public String identity() { return identity; }
        public String outputClosureIdentity() {
            return outputClosure == null ? ""
                    : outputClosure.closureFingerprint();
        }
    }

    private static String stablePathKey(
            JsonObject summary, Scope scope, JsonElement pathCondition,
            AlphaNormalizer alpha) {
        StringBuilder value = new StringBuilder();
        component(value, scope.outputClosure == null
                ? string(summary, "regionId")
                : scope.outputClosure.producer().regionId());
        component(value, string(summary, "sourceKey"));
        component(value, string(summary, "occurrenceId"));
        component(value, scope.identity);
        component(value, alphaCanonical(pathCondition, alpha));
        component(value, alphaCanonical(summary.get("outputExpressions"),
                alpha));
        component(value, alphaCanonical(summary.get(
                RelationSummary.INTERACTION_EVENTS), alpha));
        component(value, alphaCanonical(summary.get(
                TargetReachEvent.FIELD), alpha));
        component(value, string(summary, "normalExit"));
        component(value, string(summary, "exceptionType"));
        return CanonicalJson.sha256(value.toString());
    }

    /**
     * The failure slice of one recorded case, as recorded-path positions.
     * README PC-1 for every goal kind: keeping the whole recorded prefix
     * emits the transport, SASL and startup noise the acceptance condition
     * forbids.  The kinds differ only in what {@code demanded} is seeded from.
     */
    private static List<Integer> projectRelationPathCondition(
            JsonObject summary, Scope scope,
            List<SummaryBranchMapping> mappings, AlphaNormalizer alpha) {
        JsonArray full = array(summary, "pathCondition");
        Map<Integer, SummaryBranchMapping> owners = new LinkedHashMap<>();
        Set<Integer> selected = new LinkedHashSet<>();
        for (SummaryBranchMapping mapping : mappings) {
            if (mapping.isWitnessed()) {
                owners.put(mapping.summaryPcIndex(), mapping);
                if (mapping.isExplore()
                        && scope.branchSites.contains(mapping.siteId())) {
                    selected.add(mapping.summaryPcIndex());
                }
            }
        }
        if (scope.goalKind.capturesTargetReach()) {
            // A target case selects every decision this execution recorded.
            // A witnessed row is by construction a *selected* branch site, so
            // it is never transport or startup noise; dropping one weakens a
            // reachability query into admitting a model that never reaches
            // the target, which is unsound rather than merely wide.
            for (SummaryBranchMapping mapping : mappings) {
                int position = mapping.summaryPcIndex();
                if (mapping.isWitnessed() && position >= 0
                        && position < full.size()) {
                    selected.add(position);
                }
            }
        }
        for (int index = 0; index < full.size(); index++) {
            if (referencesSelectedInput(full.get(index), alpha)) {
                selected.add(index);
            }
        }

        // The task fixes non-selected inputs to witnessed concrete values, so
        // a guard holds the selected symbolic decisions plus only the local
        // definitions they depend on.
        Set<String> demanded = new LinkedHashSet<>();
        Set<String> selectedTokens = new LinkedHashSet<>();
        // What the case has to explain seeds the slice: a relation case its
        // declared outputs; a target case the branch predicate its fatal
        // query is about, already in `selected` above.
        if (scope.goalKind.capturesOutputRelation()) {
            Set<String> outputTokens = dependencyTokens(
                    summary.get("outputExpressions"));
            selectedTokens.addAll(outputTokens);
            addNonBoundaryTokens(demanded, outputTokens);
        }
        for (Integer position : selected) {
            Set<String> tokens = dependencyTokens(full.get(position));
            selectedTokens.addAll(tokens);
            addNonBoundaryTokens(demanded, tokens);
        }
        Set<Integer> dependencies = new LinkedHashSet<>();
        Set<String> exactFieldDefinitions = new LinkedHashSet<>();
        boolean changed;
        do {
            changed = false;
            for (int index = full.size() - 1; index >= 0; index--) {
                if (selected.contains(index) || owners.containsKey(index)
                        || dependencies.contains(index)) {
                    continue;
                }
                Set<String> tokens = dependencyTokens(full.get(index));
                boolean exactSelectedFieldDefinition =
                        exactFieldBindingDefinesAny(full.get(index),
                                selectedTokens);
                String exactField = exactFieldBindingIdentity(
                        full.get(index), alpha);
                boolean exactFieldCoDefinition = !exactField.isEmpty()
                        && exactFieldDefinitions.contains(exactField);
                if (!exactSelectedFieldDefinition
                        && !exactFieldCoDefinition
                        && !overlaps(tokens, demanded)) {
                    continue;
                }
                dependencies.add(index);
                int before = demanded.size();
                addNonBoundaryTokens(demanded, tokens);
                changed |= demanded.size() != before;
                if (!exactField.isEmpty()) {
                    changed |= exactFieldDefinitions.add(exactField);
                }
            }
        } while (changed);

        List<Integer> projected = new ArrayList<>();
        for (int index = 0; index < full.size(); index++) {
            if (selected.contains(index) || dependencies.contains(index)) {
                projected.add(index);
            }
        }
        return projected;
    }

    private static JsonArray conditionsAt(JsonArray full,
                                          List<Integer> positions) {
        JsonArray conditions = new JsonArray();
        for (Integer position : positions) {
            conditions.add(full.get(position).deepCopy());
        }
        return conditions;
    }

    /** Keeps constraints over inputs the replay materialized as symbolic even
     *  when the output is concrete and the controlling VM branch has no
     *  branch-mapping hook. */
    private static boolean referencesSelectedInput(
            JsonElement expression, AlphaNormalizer alpha) {
        for (String token : dependencyTokens(expression)) {
            if (token.startsWith("SYMBOL:")
                    && alpha.containsCanonicalInput(
                            token.substring("SYMBOL:".length()))) {
                return true;
            }
        }
        return false;
    }

    /**
     * Keeps the VM's exact materialization of a boundary input that directly
     * controls a selected semantic branch.  Canonical {@code REGION.in.*}
     * symbols normally terminate slicing, but dropping this definition makes
     * the scalar free in the merged relation.  Only the symbol side satisfies
     * the demand: the container side would pull in every unrelated field read.
     */
    private static boolean exactFieldBindingDefinesAny(
            JsonElement expression, Set<String> demandedTokens) {
        if (!ContainerSmtCodec.handlesFieldBinding(expression)) return false;
        JsonObject binary = expression.getAsJsonObject();
        JsonElement left = binary.get("_left");
        JsonElement right = binary.get("_right");
        JsonElement symbol = ContainerSmtCodec.handlesField(left)
                ? right : left;
        Set<String> defined = dependencyTokens(symbol);
        return overlaps(defined, demandedTokens);
    }

    /** Canonical identity of the field term one exact materialization
     *  defines, so co-definitions keep two boundary symbols equal without
     *  admitting unrelated inputs. */
    private static String exactFieldBindingIdentity(
            JsonElement expression, AlphaNormalizer alpha) {
        if (!ContainerSmtCodec.handlesFieldBinding(expression)) return "";
        JsonObject binary = expression.getAsJsonObject();
        JsonElement left = binary.get("_left");
        JsonElement right = binary.get("_right");
        JsonElement field = ContainerSmtCodec.handlesField(left)
                ? left : right;
        return alphaCanonical(field, alpha);
    }

    private static void addNonBoundaryTokens(Set<String> target,
                                             Set<String> tokens) {
        for (String token : tokens) {
            if (!boundaryToken(token)) target.add(token);
        }
    }

    private static boolean boundaryToken(String token) {
        if (token.startsWith("PLACEHOLDER:")) return true;
        if (!token.startsWith("SYMBOL:")) return false;
        return declaredPortSymbol(token.substring("SYMBOL:".length()));
    }

    /**
     * A symbol naming a declared port, and therefore a boundary leaf rather
     * than a local definition to chase.  README section 3 sends cut values
     * through ports named after the exchange <em>site</em>, so a cut port
     * carries no region id and the region test alone reads it as an ordinary
     * symbol; chasing it would walk past the cut.
     * {@link CommunicationCatalogContract#declaredPortId} is the minter.
     */
    private static boolean declaredPortSymbol(String symbol) {
        return (symbol.contains("REGION.")
                && (symbol.contains(".in.") || symbol.contains(".out.")))
                || CommunicationCatalogContract.declaredPortId(symbol);
    }

    private static boolean overlaps(Set<String> left, Set<String> right) {
        for (String token : left) {
            if (right.contains(token)) return true;
        }
        return false;
    }

    private static Set<String> dependencyTokens(JsonElement expression) {
        Set<String> result = new LinkedHashSet<>();
        collectDependencyTokens(expression, result);
        return result;
    }

    private static void collectDependencyTokens(JsonElement expression,
                                                Set<String> result) {
        if (expression == null || expression.isJsonNull()) return;
        if (expression.isJsonArray()) {
            for (JsonElement child : expression.getAsJsonArray()) {
                collectDependencyTokens(child, result);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        if ("SymbolExpression".equals(type)) {
            String symbol = string(object, "_exp");
            if (!symbol.isEmpty() && !"N".equals(symbol)
                    && !"V".equals(symbol)) {
                result.add("SYMBOL:" + symbol);
            }
        } else if ("PlaceholderExpression".equals(type)) {
            String function = string(object, "_place_holder_func");
            String count = object.has("_count")
                    ? object.get("_count").getAsString() : "-1";
            if (!function.isEmpty()) {
                result.add("PLACEHOLDER:" + function + "#" + count);
            }
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            collectDependencyTokens(entry.getValue(), result);
        }
    }

    private static String alphaCanonical(
            JsonElement value, AlphaNormalizer alpha) {
        if (value == null || value.isJsonNull()) return "null";
        if (value.isJsonPrimitive()) {
            return GSON.toJson(value.getAsJsonPrimitive());
        }
        if (value.isJsonArray()) {
            StringBuilder result = new StringBuilder("[");
            boolean first = true;
            for (JsonElement element : value.getAsJsonArray()) {
                if (!first) result.append(',');
                first = false;
                result.append(alphaCanonical(element, alpha));
            }
            return result.append(']').toString();
        }
        JsonObject object = value.getAsJsonObject();
        String type = string(object, "_type");
        StringBuilder result = new StringBuilder("{");
        boolean first = true;
        for (String key : new TreeSet<>(object.keySet())) {
            if (!first) result.append(',');
            first = false;
            result.append(GSON.toJson(key)).append(':');
            JsonElement field = object.get(key);
            if ("_exp".equals(key)
                    && ("SymbolExpression".equals(type)
                    || "ConSymbolExp".equals(type))
                    && field != null && field.isJsonPrimitive()) {
                result.append(GSON.toJson(alpha.symbol(
                        field.getAsString())));
            } else if ("_count".equals(key)
                    && "PlaceholderExpression".equals(type)
                    && field != null && field.isJsonPrimitive()) {
                result.append(GSON.toJson(alpha.placeholder(
                        string(object, "_place_holder_func"),
                        field.getAsString())));
            } else {
                result.append(alphaCanonical(field, alpha));
            }
        }
        return result.append('}').toString();
    }

    private static final class AlphaNormalizer {
        private final Set<String> canonicalPorts = new LinkedHashSet<>();
        private final Set<String> canonicalInputs = new LinkedHashSet<>();
        private final Map<String, String> symbols = new LinkedHashMap<>();
        private final Map<String, String> placeholders = new LinkedHashMap<>();

        private AlphaNormalizer(JsonObject summary) {
            collectInputPorts(summary.get("symbolicInputs"));
            JsonElement outputs = summary.get("outputExpressions");
            if (outputs != null && outputs.isJsonObject()) {
                for (String port : outputs.getAsJsonObject().keySet()) {
                    addPort(port);
                }
            }
        }

        /** {@code symbolicInputs} is the importer's array of root names. */
        private void collectInputPorts(JsonElement value) {
            if (value == null || !value.isJsonArray()) return;
            for (JsonElement element : value.getAsJsonArray()) {
                if (!element.isJsonPrimitive()) continue;
                addPort(element.getAsString());
                addInputPort(element.getAsString());
            }
        }

        private void addPort(String candidate) {
            if (looksLikeCanonicalPort(candidate)) {
                canonicalPorts.add(candidate);
            }
        }

        private void addInputPort(String candidate) {
            if (looksLikeCanonicalPort(candidate)) {
                canonicalInputs.add(candidate);
            }
        }

        private String symbol(String raw) {
            if (containsCanonicalPort(raw)) return raw;
            return alpha(symbols, raw, "@symbol.");
        }

        private String placeholder(String function, String count) {
            return alpha(placeholders, firstNonBlank(function, "unknown")
                    + "\u0000" + firstNonBlank(count, "0"),
                    "@placeholder.");
        }

        private boolean containsCanonicalPort(String raw) {
            if (looksLikeCanonicalPort(raw)) return true;
            return containsCanonicalPort(raw, canonicalPorts);
        }

        private boolean containsCanonicalInput(String raw) {
            return containsCanonicalPort(raw, canonicalInputs);
        }

        private static boolean containsCanonicalPort(
                String raw, Set<String> ports) {
            for (String port : ports) {
                int start = raw.indexOf(port);
                while (start >= 0) {
                    int end = start + port.length();
                    boolean left = start == 0 || raw.charAt(start - 1) == '_';
                    boolean right = end == raw.length()
                            || raw.charAt(end) == '_';
                    if (left && right) return true;
                    start = raw.indexOf(port, start + 1);
                }
            }
            return false;
        }

        private static String alpha(
                Map<String, String> values, String raw, String prefix) {
            String existing = values.get(raw);
            if (existing != null) return existing;
            String normalized = prefix + values.size();
            values.put(raw, normalized);
            return normalized;
        }

        /** A cross-run stable port name, kept verbatim rather than
         *  alpha-renamed: cut and region port ids are pure static identities,
         *  so two observations must normalize them to themselves. */
        private static boolean looksLikeCanonicalPort(String value) {
            String candidate = firstNonBlank(value);
            return (candidate.startsWith("REGION.")
                    && (candidate.contains(".in.")
                    || candidate.contains(".out.")))
                    || CommunicationCatalogContract.declaredPortId(candidate);
        }
    }

    private static void component(StringBuilder output, String value) {
        String safe = value == null ? "" : value;
        output.append(safe.length()).append(':').append(safe).append('|');
    }

}
