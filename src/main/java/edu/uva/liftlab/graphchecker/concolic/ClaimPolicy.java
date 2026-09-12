package edu.uva.liftlab.graphchecker.concolic;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The one decision that states what a campaign proved.
 *
 * <p>The campaign acceptance gate used to be jq in the EMIT stage of
 * {@code run_engine.sh}: it read the Composer's stage-local
 * {@code finalStatus}, the solver's {@code reachability} and one degeneracy
 * string, and published {@code SAT_CANDIDATE} from them. That accepted a run
 * whose witness the solver could not tie to any symbolic root -- an
 * {@code UNDECIDED_*} degeneracy verdict was not a refusal, a declared
 * cross-node {@code WIRE_FLOW} that reached no consumer boundary family was
 * not visible to it, and a witness identical under every enumerated valuation
 * read exactly like a witness the target constrains.</p>
 *
 * <p>So the claim is decided here, once, from the recorded evidence, and every
 * reason it is not accepted is published as a named blocker rather than folded
 * into one prose sentence. {@code finalStatus: FINAL_READY} keeps its
 * stage-local meaning -- the emitted formula is structurally complete -- and
 * is one input to this gate instead of the gate itself.</p>
 */
public final class ClaimPolicy {
    /** Where the decision is published inside the reach-condition report. */
    public static final String CLAIM = "campaignClaim";
    static final String KIND = "CAMPAIGN_CLAIM";
    /** The {@code kind} the communication mappings declare each flow with. */
    private static final String WIRE_FLOW_KIND = "WIRE_FLOW";
    /** The {@code kind} the Composer names a consumer boundary family with. */
    private static final String CONSUMER_BOUNDARY_KIND =
            "CONSUMER_BOUNDARY_CASE_DEPENDENCY";
    /** Every region identity the manifest and the runtime plan share. */
    private static final Pattern REGION_ID =
            Pattern.compile("REGION\\.[0-9a-fA-F-]{36}");

    /** A bounded witness the target predicate ties to a symbolic root. */
    public static final String SAT_CANDIDATE = "SAT_CANDIDATE";
    /** The composed bounded model is closed and unsatisfiable. */
    public static final String UNSAT_CLOSED = "UNSAT_CLOSED";
    /** No accepted claim; every reason is a named blocker. */
    public static final String INCONCLUSIVE_PARTIAL = "INCONCLUSIVE_PARTIAL";

    /** The Composer refused the composition it published. */
    static final String COMPOSER_NOT_FINAL_READY =
            "COMPOSER_NOT_FINAL_READY";
    /** A formula or solver gap is still open on the selected path set. */
    static final String COMPOSITION_GAPS_UNRESOLVED =
            "COMPOSITION_GAPS_UNRESOLVED";
    /** The target predicate is provably free of every symbolic root. */
    static final String DEGENERATE_ROOT_SPACE = "DEGENERATE_ROOT_SPACE";
    /** The degeneracy question was never decided, so it is not answered. */
    static final String UNDECIDED_ROOT_SPACE = "UNDECIDED_ROOT_SPACE";
    /** No root flip changed satisfiability: the witness is not fault-sensitive. */
    static final String TARGET_UNCONSTRAINED_BY_ROOTS =
            "TARGET_UNCONSTRAINED_BY_ROOTS";
    /** The experiment declares wire flows the composition never realized. */
    static final String DECLARED_WIRE_FLOWS_UNREALIZED =
            "DECLARED_WIRE_FLOWS_UNREALIZED";
    /** The existential witness carries no information about the target. */
    static final String WITNESS_UNINFORMATIVE = "WITNESS_UNINFORMATIVE";
    /**
     * The witness reads the fatal value out of an initial container state the
     * composition reported it could not reconstruct.
     */
    static final String UNDETERMINED_INITIAL_STATE =
            "UNDETERMINED_INITIAL_STATE";
    /** The solver returned neither sat nor unsat on an enumerated valuation. */
    static final String SOLVER_UNDECIDED_VALUATIONS =
            "SOLVER_UNDECIDED_VALUATIONS";
    /** An UNSAT result without closed selected-path authority is not closed. */
    static final String UNSAT_CLOSURE_INCOMPLETE = "UNSAT_CLOSURE_INCOMPLETE";
    /** The solver stage reached no exact reachability decision. */
    static final String NO_EXACT_REACHABILITY = "NO_EXACT_REACHABILITY";
    /**
     * The experiment injects a fault marker and the target is reachable in
     * both of its polarities with nothing else named to explain the other one.
     */
    static final String FAULT_MARKER_NOT_DETERMINING =
            "FAULT_MARKER_NOT_DETERMINING";

    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private ClaimPolicy() {
    }

    /**
     * Replays the gate on already published artifacts. The recorded
     * composition manifest and reach-condition report are the only evidence,
     * so a final directory from any earlier run can be re-decided without
     * re-running the campaign.
     */
    public static void main(String[] argv) throws Exception {
        Map<String, String> values = new LinkedHashMap<>();
        for (int index = 0; argv != null && index < argv.length; index++) {
            String option = argv[index];
            if (option == null || !option.startsWith("--")
                    || index + 1 >= argv.length) {
                throw new IllegalArgumentException(
                        "Expected --name value, got " + option);
            }
            String key = option.substring(2);
            if (!"manifest".equals(key) && !"reach".equals(key)
                    && !"mappings".equals(key) && !"plan".equals(key)) {
                throw new IllegalArgumentException(
                        "Unknown claim option: --" + key);
            }
            values.put(key, argv[++index]);
        }
        JsonObject manifest = ArtifactIO.readObject(
                required(values, "manifest"));
        JsonObject reach = ArtifactIO.readObject(required(values, "reach"));
        // The plan the composition pinned is the plan that bound its exchange
        // ports, so a replay needs no argument to find it.
        String plan = values.get("plan");
        if (plan == null || plan.trim().isEmpty()) {
            plan = optionalString(object(manifest, "runtimePlanArtifact"),
                    "path");
        }
        JsonObject claim = decide(manifest, reach,
                WireFlowEvidence.read(values.get("mappings"), plan));
        System.out.println(GSON.toJson(claim));
        if (!accepted(optionalString(claim, "claim"))) {
            System.exit(2);
        }
    }

    private static Path required(Map<String, String> values, String key) {
        String value = values.get(key);
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException("Missing --" + key);
        }
        return Paths.get(value);
    }

    private static boolean accepted(String claim) {
        return SAT_CANDIDATE.equals(claim) || UNSAT_CLOSED.equals(claim);
    }

    /**
     * What the experiment declares and where the plan bound each declared
     * flow, so a composition can be asked which flows it realized rather
     * than only how many exist.
     *
     * <p>The plan binds a flow's {@code XCH.<site>.<req|resp>.<flow>} ports
     * to one producer region and one consumer region; the regions are kept
     * here so a report can say what the plan expected. Whether the flow is
     * <em>realized</em> is decided elsewhere and by one thing only: whether
     * the composition lowered the value of a boundary family sitting on one
     * of those ports into a term. Deciding it from the regions instead --
     * asking whether either endpoint's id occurs in the manifest -- accepts a
     * mention in place of a constraint.</p>
     */
    public static final class WireFlowEvidence {
        private final List<String> declared;
        private final Map<String, Set<String>> consumerRegions;
        private final Map<String, Set<String>> producerRegions;

        private WireFlowEvidence(List<String> declared,
                                 Map<String, Set<String>> consumerRegions,
                                 Map<String, Set<String>> producerRegions) {
            this.declared = Collections.unmodifiableList(declared);
            this.consumerRegions = consumerRegions;
            this.producerRegions = producerRegions;
        }

        /** An experiment that declares no cross-node flow. */
        public static WireFlowEvidence none() {
            return new WireFlowEvidence(new ArrayList<String>(),
                    new LinkedHashMap<String, Set<String>>(),
                    new LinkedHashMap<String, Set<String>>());
        }

        /** Declared flows whose ports no plan bound, named in order. */
        public static WireFlowEvidence declaredOnly(List<String> flows) {
            return new WireFlowEvidence(new ArrayList<>(flows),
                    new LinkedHashMap<String, Set<String>>(),
                    new LinkedHashMap<String, Set<String>>());
        }

        /**
         * Reads the declared flows from the communication mappings and their
         * planned exchange ports from the runtime plan. A blank or absent
         * mapping path is an experiment that declares none, which is a
         * single-node experiment rather than an unrealized flow; a blank or
         * absent plan leaves the declared flows without port evidence.
         */
        public static WireFlowEvidence read(String mappings, String plan)
                throws IOException {
            List<String> declared = new ArrayList<>();
            for (JsonObject row : rows(mappings)) {
                String id = optionalString(row, "id");
                if (WIRE_FLOW_KIND.equals(optionalString(row, "kind"))
                        && !id.isEmpty() && !declared.contains(id)) {
                    declared.add(id);
                }
            }
            Map<String, Set<String>> consumers = new LinkedHashMap<>();
            Map<String, Set<String>> producers = new LinkedHashMap<>();
            for (JsonObject row : rows(plan)) {
                collectHandoffs(row, "", consumers, producers);
            }
            return new WireFlowEvidence(declared, consumers, producers);
        }

        private static List<JsonObject> rows(String path) throws IOException {
            if (path == null || path.trim().isEmpty()
                    || !Files.isRegularFile(Paths.get(path.trim()))) {
                return new ArrayList<>();
            }
            return ArtifactIO.readJsonl(Paths.get(path.trim()));
        }

        /**
         * Walks a plan row for {@code communicationHandoffs} and records, per
         * declared flow, the regions the plan bound its consumer ({@code IN})
         * and producer ({@code OUT}) ports to. The flow name is the last
         * segment of the port id.
         */
        private static void collectHandoffs(
                JsonElement element, String regionId,
                Map<String, Set<String>> consumers,
                Map<String, Set<String>> producers) {
            if (element == null || element.isJsonNull()) {
                return;
            }
            if (element.isJsonArray()) {
                for (JsonElement member : element.getAsJsonArray()) {
                    collectHandoffs(member, regionId, consumers, producers);
                }
                return;
            }
            if (!element.isJsonObject()) {
                return;
            }
            JsonObject row = element.getAsJsonObject();
            String region = optionalString(row, "regionId");
            String scope = region.isEmpty() ? regionId : region;
            for (JsonElement handoff : array(row, "communicationHandoffs")) {
                if (!handoff.isJsonObject() || scope.isEmpty()) {
                    continue;
                }
                JsonObject port = handoff.getAsJsonObject();
                String portId = optionalString(port, "portId");
                int separator = portId.lastIndexOf('.');
                if (separator < 0 || separator + 1 >= portId.length()) {
                    continue;
                }
                String flow = portId.substring(separator + 1);
                String side = optionalString(port, "side");
                if ("IN".equals(side)) {
                    add(consumers, flow, scope);
                } else if ("OUT".equals(side)) {
                    add(producers, flow, scope);
                }
            }
            for (Map.Entry<String, JsonElement> member : row.entrySet()) {
                if ("communicationHandoffs".equals(member.getKey())) {
                    continue;
                }
                collectHandoffs(member.getValue(), scope, consumers,
                        producers);
            }
        }

        private static void add(Map<String, Set<String>> index, String key,
                                String value) {
            Set<String> values = index.get(key);
            if (values == null) {
                values = new LinkedHashSet<>();
                index.put(key, values);
            }
            values.add(value);
        }

        public int declaredCount() {
            return declared.size();
        }

        /**
         * The declared flows whose value never constrains this formula.
         *
         * <p>A flow is realized when at least one consumer boundary family
         * carried on one of <em>its</em> ports reached a lowered term. That
         * is the only reading under which the blocker means what its name
         * says. The earlier reading -- a region id of either endpoint
         * occurring anywhere in the manifest text, or any boundary family at
         * all being present -- is satisfied by a mention rather than by a
         * constraint: on hdfs-17899-bug3 it called {@code block-key-id}
         * realized while all eight of its families were unreferenced and no
         * term carried the wire's value.</p>
         */
        List<String> unrealized(List<BoundFamily> ledger) {
            List<String> missing = new ArrayList<>();
            for (String flow : declared) {
                if (!realized(flow, ledger)) missing.add(flow);
            }
            return missing;
        }

        private boolean realized(String flow, List<BoundFamily> ledger) {
            for (BoundFamily family : ledger) {
                if (family.bound && namesFlow(family.portId, flow)) {
                    return true;
                }
            }
            return false;
        }

        /**
         * Whether one exchange port carries one declared flow. The Composer
         * spells a port {@code XCH.<site>.<req|resp>.<flow>}, and a flow id
         * may itself contain '-' but never the '.' that delimits it here.
         */
        private static boolean namesFlow(String portId, String flow) {
            return !flow.isEmpty() && portId.endsWith("." + flow);
        }

        /** The per-flow realization rows the claim publishes as evidence. */
        JsonArray report(List<BoundFamily> ledger) {
            JsonArray rows = new JsonArray();
            for (String flow : declared) {
                JsonObject row = new JsonObject();
                row.addProperty("flow", flow);
                Set<String> consumers = consumerRegions.get(flow);
                Set<String> producers = producerRegions.get(flow);
                int families = 0;
                int bound = 0;
                for (BoundFamily family : ledger) {
                    if (!namesFlow(family.portId, flow)) continue;
                    families++;
                    if (family.bound) bound++;
                }
                row.addProperty("realized", bound > 0);
                row.addProperty("mechanism", "BOUND_BOUNDARY_FAMILY");
                row.addProperty("consumerRegionsPlanned",
                        consumers == null ? 0 : consumers.size());
                row.addProperty("producerRegionsPlanned",
                        producers == null ? 0 : producers.size());
                row.addProperty("familiesObserved", families);
                row.addProperty("familiesBound", bound);
                rows.add(row);
            }
            return rows;
        }
    }

    /** One observed boundary family: the port it sat on, and whether the
     * composition lowered its value into a term. */
    static final class BoundFamily {
        private final String portId;
        private final boolean bound;

        private BoundFamily(String portId, boolean bound) {
            this.portId = portId;
            this.bound = bound;
        }
    }

    /**
     * Every boundary family the composition observed on a declared exchange
     * port, read from the Composer's own handoff ledger.
     *
     * <p>A manifest with no ledger contributes nothing, which is the honest
     * reading of a composition that published no handoff evidence: it did
     * not show that any wire's value constrains it.</p>
     */
    static List<BoundFamily> wireFlowLedger(JsonObject manifest) {
        List<BoundFamily> ledger = new ArrayList<>();
        for (JsonElement element
                : array(manifest, ConcolicSmtComposer.WIRE_FLOW_BINDINGS)) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            String port = optionalString(row, "portId");
            if (port.isEmpty()) continue;
            ledger.add(new BoundFamily(port,
                    optionalBool(row, "valueBound", false)));
        }
        return ledger;
    }

    /**
     * Every region identity the composition drew a case, a read or a witness
     * from. Region ids appear inside occurrence ids, case owners and location
     * keys as well as in their own field, so they are read as identities
     * rather than from one place.
     */
    static Set<String> realizedRegions(JsonObject manifest) {
        Set<String> regions = new LinkedHashSet<>();
        Matcher matcher = REGION_ID.matcher(
                manifest == null ? "" : manifest.toString());
        while (matcher.find()) {
            regions.add(matcher.group());
        }
        return regions;
    }

    /**
     * How many consumer boundary families the composition realized. The
     * Composer publishes them as {@code casePathConditionDependencies} rows;
     * the legacy {@code symbolicPropagation} array is read when a manifest
     * still carries one.
     */
    static int consumerBoundaryFamilies(JsonObject manifest) {
        Set<String> families = new LinkedHashSet<>();
        int unnamed = 0;
        for (JsonElement element
                : array(manifest, "casePathConditionDependencies")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            if (!CONSUMER_BOUNDARY_KIND.equals(optionalString(row, "kind"))) {
                continue;
            }
            String family = optionalString(row, "familyKey");
            if (family.isEmpty()) {
                unnamed++;
            } else {
                families.add(family);
            }
        }
        return families.size() + unnamed
                + array(manifest, "symbolicPropagation").size();
    }

    /** How many arms those consumer boundary families carry in total. */
    static int consumerBoundaryArms(JsonObject manifest) {
        int arms = 0;
        for (JsonElement element
                : array(manifest, "casePathConditionDependencies")) {
            if (element.isJsonObject()
                    && CONSUMER_BOUNDARY_KIND.equals(optionalString(
                            element.getAsJsonObject(), "kind"))) {
                arms += array(element.getAsJsonObject(), "arms").size();
            }
        }
        for (JsonElement element : array(manifest, "symbolicPropagation")) {
            if (element.isJsonObject()) {
                arms += optionalInteger(element.getAsJsonObject(),
                        "armCount", 0);
            }
        }
        return arms;
    }

    /**
     * Carriers whose initial content the Composer reported it could not
     * reconstruct, by the session location key its gap names.
     */
    static Set<String> truncatedCarriers(JsonObject manifest) {
        Set<String> carriers = new LinkedHashSet<>();
        for (JsonElement element
                : array(manifest, "symbolicPropagationGaps")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject gap = element.getAsJsonObject();
            if (SymbolicPropagationClosure.INITIAL_CONTAINER_SNAPSHOT_TRUNCATED
                    .equals(optionalString(gap, "reason"))) {
                String subject = optionalString(gap, "subject");
                if (!subject.isEmpty()) {
                    carriers.add(subject);
                }
            }
        }
        return carriers;
    }

    /**
     * Whether the witness reads the fatal value out of a state nobody
     * reconstructed.
     *
     * <p>A truncated initial container snapshot makes membership over that
     * container a free Boolean.  The Composer publishes that as a propagation
     * gap and still emits the formula, which is right: the other arms of the
     * same read are real, and a witness that uses one of them is unaffected.
     * What must not pass is a witness whose fatal value comes from the
     * <em>initial</em> arm of exactly such a carrier -- there the solver is
     * free to answer "the container never held that key", and the target is
     * satisfied by an admitted hole rather than by the program.  So the
     * selected arm decides: on the path it is a blocker naming the carrier and
     * the arm, off the path it is an information row.</p>
     */
    static JsonObject initialStateEvidence(JsonObject manifest,
                                           JsonObject reach) {
        Set<String> carriers = truncatedCarriers(manifest);
        JsonObject selection = object(reach,
                BooleanReachConditionExtractor.FATAL_STATE_SELECTION);
        JsonObject evidence = new JsonObject();
        evidence.addProperty("truncatedCarrierCount", carriers.size());
        evidence.add("truncatedCarriers", GSON.toJsonTree(carriers));
        evidence.addProperty("fatalArmsResolved",
                optionalBool(selection, "resolved", false));
        JsonArray onPath = new JsonArray();
        JsonArray offPath = new JsonArray();
        for (JsonElement element : array(selection, "arms")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject arm = element.getAsJsonObject();
            if (!carriers.contains(optionalString(arm,
                    "sessionLocationKey"))) {
                continue;
            }
            JsonObject row = new JsonObject();
            row.addProperty("selector", optionalString(arm, "selector"));
            row.addProperty("sessionLocationKey",
                    optionalString(arm, "sessionLocationKey"));
            row.addProperty("locationKey",
                    optionalString(arm, "locationKey"));
            row.addProperty("readIdentity",
                    optionalString(arm, "readIdentity"));
            row.addProperty("initialState",
                    optionalBool(arm, "initialState", false));
            if (optionalBool(arm, "selected", false)) {
                onPath.add(row);
            } else {
                offPath.add(row);
            }
        }
        evidence.add("onSelectedPath", onPath);
        evidence.add("offSelectedPath", offPath);
        evidence.addProperty("fatalCarrierTruncated",
                onPath.size() + offPath.size() > 0);
        return evidence;
    }

    /**
     * The blocker that evidence justifies, or null when it justifies none.
     *
     * <p>Which arm the witness picked does not save a fatal read whose own
     * container was never reconstructed. A truncated snapshot makes
     * {@code assoc_has} over that container free, so "the key was not there"
     * is a zero-cost premise available under every arm and every polarity --
     * the witness that happens to use a writer arm this time is one solver
     * decision away from not needing it. The gap is the read's, so the read
     * is blocked while it stands.</p>
     */
    private static JsonObject initialStateBlocker(JsonObject evidence) {
        JsonArray onPath = array(evidence, "onSelectedPath");
        JsonArray offPath = array(evidence, "offSelectedPath");
        if (onPath.size() + offPath.size() == 0) {
            return null;
        }
        Set<String> carriers = new LinkedHashSet<>();
        List<String> where = new ArrayList<>();
        for (JsonArray arms : Arrays.asList(onPath, offPath)) {
            for (JsonElement element : arms) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject row = element.getAsJsonObject();
                carriers.add(optionalString(row, "sessionLocationKey"));
                if (arms == onPath || optionalBool(row, "initialState",
                        false)) {
                    where.add(optionalString(row, "selector")
                            + (arms == onPath ? " (selected" : " (available")
                            + (optionalBool(row, "initialState", false)
                                    ? ", initial state)" : ")"));
                }
            }
        }
        String how = onPath.size() > 0
                ? "the witness reads the fatal value from"
                : "the fatal read can take its value from";
        return blocker(UNDETERMINED_INITIAL_STATE,
                String.join(",", carriers),
                how + " the initial state of " + carriers.size()
                        + " carrier(s) whose initial content the composition"
                        + " reported truncated, so membership there is a free"
                        + " choice rather than the program's: "
                        + String.join("; ", where));
    }

    /**
     * What the probe actually perturbed, so a reader can see which root the
     * root-space verdict rests on.
     *
     * <p>{@code constrainsRootSpace} says some root decides the target; it
     * does not say which, and a run that injects a fault marker cares very
     * much whether the answer is the marker or a wall clock three nodes away.
     */
    static JsonObject probedRoot(JsonObject reach) {
        JsonObject probe = object(reach, "existentialRootProbe");
        JsonObject result = new JsonObject();
        JsonObject rejected = null;
        int solved = 0;
        for (JsonElement element : array(probe, "perturbations")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            if (!optionalString(row, "rejectedBy").isEmpty()) {
                continue;
            }
            solved++;
            if (rejected == null && "unsat".equals(optionalString(row,
                    "status"))) {
                rejected = row;
            }
        }
        result.addProperty("solvedPerturbations", solved);
        result.addProperty("rejected", rejected != null);
        if (rejected != null) {
            result.addProperty("sourceIdentity",
                    optionalString(rejected, "sourceIdentity"));
            result.addProperty("portId", optionalString(rejected, "portId"));
            result.addProperty("occurrenceId",
                    optionalString(rejected, "occurrenceId"));
            result.addProperty("javaTypeDescriptor",
                    optionalString(rejected, "javaTypeDescriptor"));
            result.addProperty("witnessValue",
                    optionalString(rejected, "witnessValue"));
            result.addProperty("perturbedValue",
                    optionalString(rejected, "perturbedValue"));
        }
        return result;
    }

    /**
     * Whether the injected fault marker is what decides the target.
     *
     * <p>An experiment that injects a marker states a hypothesis: with the
     * fault the target is reached, without it the target is not. The formula
     * answers that in one way only -- the marker's two polarities disagree on
     * satisfiability. When both polarities are satisfiable the hypothesis is
     * refuted unless the composition can say, in mechanism terms, what else
     * reached the target in the polarity that has no fault; and a clock
     * pressed flat against its own window bound says nothing, because a
     * saturated bound is the window's answer and not the program's. So the
     * other polarity has to be explained by a named mechanism strictly inside
     * what the recording allows, or the marker is not determining and no
     * accepted claim may rest on it.</p>
     *
     * <p>"Explained" is measured, not inferred from the witness. A model
     * assigns every free root, so a witness always names something; the
     * extractor's {@code mechanismNecessity} probe puts each named
     * mechanism's roots back to what they recorded and asks whether the
     * polarity survives. A mechanism the polarity survives without is
     * decoration, whatever its skew reads. The saturation census is kept
     * beside it because a reader deciding how much to trust a mechanism still
     * wants to see how much of it was pressed against the window.</p>
     */
    static JsonObject faultMarkerEvidence(JsonObject manifest,
                                          JsonObject reach) {
        JsonArray markers = array(object(reach, "roots"), "booleanInputs");
        JsonObject evidence = new JsonObject();
        evidence.addProperty("declaredMarkers", markers.size());
        JsonArray rows = new JsonArray();
        evidence.add("markers", rows);
        if (markers.size() == 0) {
            return evidence;
        }
        long window = Math.max(0L, ClockRootPhysics.skewOf(manifest));
        Map<String, String> recorded = new LinkedHashMap<>();
        for (JsonElement element
                : array(manifest, ConcolicSmtComposer.RECORDED_ROOT_VALUES)) {
            if (element.isJsonObject()) {
                recorded.put(optionalString(element.getAsJsonObject(),
                        "solverTerm"), optionalString(
                        element.getAsJsonObject(), "recordedValue"));
            }
        }
        JsonArray valuations = array(reach, "valuations");
        for (int index = 0; index < markers.size(); index++) {
            if (!markers.get(index).isJsonObject()) {
                continue;
            }
            JsonObject marker = markers.get(index).getAsJsonObject();
            JsonObject row = new JsonObject();
            row.addProperty("sourceIdentity",
                    optionalString(marker, "sourceIdentity"));
            row.addProperty("portId", optionalString(marker, "portId"));
            row.addProperty("occurrenceId",
                    optionalString(marker, "occurrenceId"));
            boolean recordedPolarity = !"false".equals(recorded.get(
                    optionalString(marker, "solverTerm")));
            row.addProperty("recordedPolarity", recordedPolarity);
            JsonObject atRecorded = polarity(valuations, index,
                    recordedPolarity);
            JsonObject flipped = polarity(valuations, index,
                    !recordedPolarity);
            row.addProperty("recordedPolaritySatisfiable",
                    atRecorded != null && satisfied(atRecorded));
            row.addProperty("flippedPolaritySatisfiable",
                    flipped != null && satisfied(flipped));
            boolean flips = flipped != null && satisfied(flipped)
                    && atRecorded != null && !satisfied(atRecorded);
            JsonArray unsaturated = unsaturatedMechanisms(atRecorded, window);
            JsonArray necessary = necessaryMechanisms(reach,
                    optionalString(marker, "solverTerm"), recordedPolarity);
            row.addProperty("polarityDecides", flips);
            // A reader deciding whether to trust the mechanism needs to see
            // how much of it is pressed against the window: six interior rows
            // out of ten is a different claim from six out of six.
            row.addProperty("otherPolarityMechanismCount",
                    atRecorded == null ? 0
                            : array(atRecorded, "witnessMechanisms").size());
            row.addProperty("otherPolarityUnsaturatedCount",
                    unsaturated.size());
            row.addProperty("clockWindowMillis", window);
            row.add("otherPolarityMechanisms", unsaturated);
            row.add("necessaryMechanisms", necessary);
            row.addProperty("determining", flips || necessary.size() > 0);
            rows.add(row);
        }
        return evidence;
    }

    /** The valuation that assigns this Boolean root that polarity. */
    private static JsonObject polarity(JsonArray valuations, int index,
                                       boolean value) {
        for (int ordinal = 0; ordinal < valuations.size(); ordinal++) {
            JsonObject candidate = row(valuations, ordinal);
            if (candidate == null) {
                continue;
            }
            JsonArray values = array(candidate, "values");
            if (index < values.size()
                    && values.get(index).isJsonPrimitive()
                    && values.get(index).getAsBoolean() == value) {
                return candidate;
            }
        }
        return null;
    }

    /**
     * The named mechanisms the solver showed this polarity cannot do without.
     *
     * <p>Each row is one extra query the extractor already ran: the polarity
     * asserted, the mechanism's roots pinned to their recorded values. An
     * {@code unsat} there is the only evidence that the mechanism carried the
     * polarity rather than merely accompanying it.</p>
     */
    private static JsonArray necessaryMechanisms(JsonObject reach,
                                                 String markerTerm,
                                                 boolean polarity) {
        JsonArray necessary = new JsonArray();
        JsonObject probe = object(reach,
                BooleanReachConditionExtractor.MECHANISM_NECESSITY);
        for (JsonElement element : array(probe, "mechanisms")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            if (optionalBool(row, "necessary", false)
                    && optionalBool(row, "polarity", false) == polarity
                    && optionalString(row, "marker").equals(markerTerm)) {
                necessary.add(row);
            }
        }
        return necessary;
    }

    /**
     * Mechanism rows that name something the recording leaves room for. A
     * clock at exactly its window bound is excluded: the bound is the
     * analysis's own parameter, so a witness that saturates it has been
     * pushed there by the search rather than by the program.
     */
    private static JsonArray unsaturatedMechanisms(JsonObject valuation,
                                                   long window) {
        JsonArray named = new JsonArray();
        if (valuation == null || !satisfied(valuation)) {
            return named;
        }
        for (JsonElement element : array(valuation, "witnessMechanisms")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject mechanism = element.getAsJsonObject();
            String kind = optionalString(mechanism, "kind");
            if (kind.isEmpty() || "MARKER_FLIPPED".equals(kind)) {
                continue;
            }
            if (mechanism.has("skewMillis")) {
                long skew = Math.abs(optionalLongInteger(mechanism,
                        "skewMillis", 0L));
                if (skew >= window) {
                    continue;
                }
            }
            named.add(mechanism);
        }
        return named;
    }

    /** The blocker a non-determining marker justifies, or null. */
    private static JsonObject faultMarkerBlocker(JsonObject evidence) {
        List<String> undetermined = new ArrayList<>();
        List<String> detail = new ArrayList<>();
        for (JsonElement element : array(evidence, "markers")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject marker = element.getAsJsonObject();
            if (optionalBool(marker, "determining", false)) {
                continue;
            }
            undetermined.add(optionalString(marker, "sourceIdentity"));
            detail.add(optionalString(marker, "portId")
                    + ": recorded polarity "
                    + (optionalBool(marker, "recordedPolaritySatisfiable",
                            false) ? "sat" : "unsat")
                    + ", flipped polarity "
                    + (optionalBool(marker, "flippedPolaritySatisfiable",
                            false) ? "sat" : "unsat")
                    + ", "
                    + array(marker, "necessaryMechanisms").size()
                    + " necessary mechanism(s) of "
                    + optionalInteger(marker, "otherPolarityMechanismCount",
                            0)
                    + " named ("
                    + optionalInteger(marker,
                            "otherPolarityUnsaturatedCount", 0)
                    + " inside the recorded window)");
        }
        if (undetermined.isEmpty()) {
            return null;
        }
        return blocker(FAULT_MARKER_NOT_DETERMINING,
                String.join(",", undetermined),
                "the target is reachable in both polarities of "
                        + undetermined.size() + " declared fault marker(s)"
                        + " and no named mechanism inside the recorded window"
                        + " explains the polarity without the fault: "
                        + String.join("; ", detail));
    }

    /**
     * Decides the campaign claim from the Composer's manifest and the
     * reach-condition report, and names every blocker that withholds
     * acceptance.
     *
     * @param manifest the composition manifest the Composer published
     * @param reach the reach-condition report the solver stage published
     * @param flows what the experiment declares and where the plan bound it
     */
    public static JsonObject decide(JsonObject manifest, JsonObject reach,
                                    WireFlowEvidence flows) {
        JsonObject reachCondition = object(reach, "reachCondition");
        String reachability = firstNonEmpty(
                optionalString(reachCondition, "reachability"), "UNKNOWN");
        String degeneracy = firstNonEmpty(
                optionalString(reachCondition, "degeneracyCheck"),
                "UNDECIDED");
        boolean unsatClosureComplete = optionalBool(reach,
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE, false);
        JsonArray valuations = array(reach, "valuations");
        boolean probeConstrains = optionalBool(
                object(reach, "existentialRootProbe"),
                "constrainsRootSpace", false);
        int boundaryFamilies = consumerBoundaryFamilies(manifest);
        List<BoundFamily> wireFlowLedger = wireFlowLedger(manifest);
        List<String> unrealizedFlows = flows.unrealized(wireFlowLedger);

        List<JsonObject> blockers = new ArrayList<>();

        // The Composer's own refusals and the solver's own gaps are the two
        // sources EMIT aggregates into the campaign gap count. Reading them
        // here keeps this decision and that count derived from one set of
        // facts rather than two.
        String refusals = codes(array(manifest, "finalStatusRefusals"));
        String finalStatus = optionalString(manifest, "finalStatus");
        if (!"FINAL_READY".equals(finalStatus)) {
            blockers.add(blocker(COMPOSER_NOT_FINAL_READY, finalStatus,
                    "the Composer published finalStatus="
                            + firstNonEmpty(finalStatus, "none")
                            + " and refused this composition"));
        }
        Set<String> hardGaps = new LinkedHashSet<>();
        for (JsonElement refusal : array(manifest, "finalStatusRefusals")) {
            hardGaps.add("COMPOSE/" + code(refusal));
        }
        for (JsonElement gap : array(reach, "gaps")) {
            hardGaps.add("SOLVE/" + code(gap));
        }
        if (!hardGaps.isEmpty()) {
            blockers.add(blocker(COMPOSITION_GAPS_UNRESOLVED,
                    String.valueOf(hardGaps.size()),
                    "the selected causal path set has " + hardGaps.size()
                            + " unresolved gap(s): "
                            + String.join(",", hardGaps)));
        }

        // DEGENERATE and UNDECIDED are different findings and were both
        // acceptable to the jq gate that UNDECIDED slipped through. A root
        // space the target provably does not constrain is a refutation of the
        // witness; a root space nobody enumerated is an open question. Each
        // blocks a SAT candidate under its own name.
        if (degeneracy.startsWith("DEGENERATE_")) {
            blockers.add(blocker(DEGENERATE_ROOT_SPACE, degeneracy,
                    "the target predicate is unconstrained by every"
                            + " symbolic root"));
        } else if (degeneracy.startsWith("UNDECIDED_")) {
            blockers.add(blocker(UNDECIDED_ROOT_SPACE, degeneracy,
                    "the degeneracy question was not decided: " + degeneracy));
        }

        // A witness is evidence only if the target predicate depends on a
        // root. Two enumerated valuations that differ in one Boolean root and
        // disagree on satisfiability show that dependence exactly; so does a
        // rejected existential perturbation. Without either, the formula and
        // the roots are disconnected and the witness names nothing.
        if ("REACHABLE".equals(reachability)
                && !faultSensitive(valuations, probeConstrains)) {
            blockers.add(blocker(TARGET_UNCONSTRAINED_BY_ROOTS, "",
                    "no symbolic root flips the target predicate across the"
                            + " enumerated valuations, so the witness is not"
                            + " fault-sensitive"));
        }

        // A declared flow the composition never drew either side of is not
        // in the formula the witness satisfies, whatever the formula then
        // satisfies. Which flows those are is the blocker: a count cannot be
        // acted on, and counting one realization mechanism out of two called
        // a realized flow unrealized.
        if (!unrealizedFlows.isEmpty()) {
            blockers.add(blocker(DECLARED_WIRE_FLOWS_UNREALIZED,
                    String.join(",", unrealizedFlows),
                    "no consumer boundary family of "
                            + unrealizedFlows.size() + " of "
                            + flows.declaredCount()
                            + " declared WIRE_FLOW(s) reached a lowered"
                            + " term, so the value each wire carried"
                            + " constrains nothing in this formula: "
                            + String.join(", ", unrealizedFlows)));
        }

        // A composition may publish a propagation gap and still be
        // FINAL_READY with no refusal; the gap is then invisible to a caller
        // that reads only finalStatusRefusals and the solver's own gaps. One
        // such gap changes what a witness means, so it is read here.
        JsonObject initialState = initialStateEvidence(manifest, reach);
        JsonObject initialStateGap = initialStateBlocker(initialState);
        if (initialStateGap != null) {
            blockers.add(initialStateGap);
        }

        // An injected marker is the experiment's own hypothesis, so it is the
        // root the verdict has to rest on. A rejected perturbation of some
        // other root is evidence about that root and no answer about this one.
        JsonObject faultMarkers = faultMarkerEvidence(manifest, reach);
        JsonObject markerGap = faultMarkerBlocker(faultMarkers);
        if (markerGap != null) {
            blockers.add(markerGap);
        }

        JsonObject witnessGap = witnessBlocker(valuations, probeConstrains);
        if (witnessGap != null) {
            blockers.add(witnessGap);
        }

        int undecidedRows = undecidedValuations(valuations);
        if (undecidedRows > 0) {
            blockers.add(blocker(SOLVER_UNDECIDED_VALUATIONS,
                    String.valueOf(undecidedRows),
                    "the solver returned neither sat nor unsat on "
                            + undecidedRows + " enumerated valuation(s)"));
        }

        // Closure is required for a closed refutation and for nothing else:
        // one connected SAT witness stays valid while sibling paths are open.
        if ("UNREACHABLE".equals(reachability) && !unsatClosureComplete) {
            blockers.add(blocker(UNSAT_CLOSURE_INCOMPLETE, "",
                    "the solver reported no valuation but the selected model"
                            + " published no closed path-set authority"));
        }
        if (!"REACHABLE".equals(reachability)
                && !"UNREACHABLE".equals(reachability)) {
            blockers.add(blocker(NO_EXACT_REACHABILITY, reachability,
                    "the solver stage reached no exact reachability"
                            + " decision"));
        }

        String claim = blockers.isEmpty()
                ? ("REACHABLE".equals(reachability)
                        ? SAT_CANDIDATE : UNSAT_CLOSED)
                : INCONCLUSIVE_PARTIAL;

        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", KIND);
        result.addProperty("claim", claim);
        result.addProperty("claimReason", claimReason(claim, reachability,
                blockers, refusals));
        JsonArray blockerRows = new JsonArray();
        for (JsonObject row : blockers) {
            blockerRows.add(row);
        }
        result.add("blockers", blockerRows);
        result.addProperty("blockerCount", blockers.size());
        result.addProperty("whyNotAccepted", whyNotAccepted(claim, blockers));
        JsonObject rootSpace = new JsonObject();
        rootSpace.addProperty("reachability", reachability);
        rootSpace.addProperty("degeneracyCheck", degeneracy);
        rootSpace.addProperty("faultSensitive",
                faultSensitive(valuations, probeConstrains));
        rootSpace.addProperty("declaredWireFlows", flows.declaredCount());
        rootSpace.addProperty("unrealizedWireFlows",
                String.join(",", unrealizedFlows));
        rootSpace.add("wireFlows", flows.report(wireFlowLedger));
        rootSpace.addProperty("consumerBoundaryFamilies", boundaryFamilies);
        rootSpace.addProperty("consumerBoundaryArms",
                consumerBoundaryArms(manifest));
        rootSpace.addProperty("realizedRegions",
                realizedRegions(manifest).size());
        rootSpace.add("initialState", initialState);
        rootSpace.add("faultMarkers", faultMarkers);
        rootSpace.add("probedRoot", probedRoot(reach));
        rootSpace.addProperty(ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE,
                unsatClosureComplete);
        result.add("rootSpace", rootSpace);
        return result;
    }

    /**
     * Whether some symbolic root decides the target predicate. A rejected
     * existential perturbation is the solver's own proof of that; otherwise
     * two enumerated valuations one Boolean root apart must disagree on
     * satisfiability.
     */
    static boolean faultSensitive(JsonArray valuations,
                                  boolean probeConstrains) {
        if (probeConstrains) {
            return true;
        }
        for (int left = 0; left < valuations.size(); left++) {
            JsonObject first = row(valuations, left);
            if (first == null) {
                continue;
            }
            for (int right = left + 1; right < valuations.size(); right++) {
                JsonObject second = row(valuations, right);
                if (second == null) {
                    continue;
                }
                if (satisfied(first) == satisfied(second)) {
                    continue;
                }
                if (differingRoots(first, second) == 1) {
                    return true;
                }
            }
        }
        return false;
    }

    private static int differingRoots(JsonObject first, JsonObject second) {
        JsonArray left = array(first, "values");
        JsonArray right = array(second, "values");
        if (left.size() != right.size() || left.size() == 0) {
            return -1;
        }
        int differing = 0;
        for (int index = 0; index < left.size(); index++) {
            if (!left.get(index).equals(right.get(index))) {
                differing++;
            }
        }
        return differing;
    }

    /**
     * An existential witness that is every-zero, or identical under every
     * enumerated valuation while no perturbation of it was rejected, is a
     * value the target predicate does not read. It is reported rather than
     * accepted as the witness of a bug.
     */
    private static JsonObject witnessBlocker(JsonArray valuations,
                                             boolean probeConstrains) {
        if (probeConstrains) {
            return null;
        }
        List<String> vectors = new ArrayList<>();
        boolean allZero = true;
        int witnessed = 0;
        for (int index = 0; index < valuations.size(); index++) {
            JsonObject candidate = row(valuations, index);
            if (candidate == null || !satisfied(candidate)) {
                continue;
            }
            JsonArray witness = array(candidate, "existentialWitness");
            if (witness.size() == 0) {
                continue;
            }
            witnessed++;
            StringBuilder vector = new StringBuilder();
            for (JsonElement element : witness) {
                String value = element.isJsonObject()
                        ? optionalString(element.getAsJsonObject(), "value")
                        : "";
                vector.append(value).append('\0');
                if (!isZero(value)) {
                    allZero = false;
                }
            }
            vectors.add(vector.toString());
        }
        if (witnessed == 0) {
            return null;
        }
        if (allZero) {
            return blocker(WITNESS_UNINFORMATIVE, "ALL_ZERO",
                    "every existential witness value is zero and no"
                            + " perturbation of one was rejected, so the"
                            + " witness is tied to no root");
        }
        if (vectors.size() < 2) {
            return null;
        }
        for (String vector : vectors) {
            if (!vector.equals(vectors.get(0))) {
                return null;
            }
        }
        return blocker(WITNESS_UNINFORMATIVE, "INVARIANT_ACROSS_VALUATIONS",
                "the existential witness is identical across all "
                        + vectors.size() + " satisfying valuations and no"
                        + " perturbation of it was rejected, so it does not"
                        + " depend on the target predicate");
    }

    private static int undecidedValuations(JsonArray valuations) {
        int undecided = 0;
        for (int index = 0; index < valuations.size(); index++) {
            JsonObject candidate = row(valuations, index);
            if (candidate == null) {
                continue;
            }
            String status = optionalString(candidate, "status");
            if (!"sat".equals(status) && !"unsat".equals(status)) {
                undecided++;
            }
        }
        return undecided;
    }

    private static boolean isZero(String value) {
        String trimmed = value == null ? "" : value.trim();
        return "0".equals(trimmed) || "(- 0)".equals(trimmed)
                || "#x0".equals(trimmed) || "false".equals(trimmed);
    }

    private static JsonObject row(JsonArray rows, int index) {
        JsonElement element = rows.get(index);
        return element != null && element.isJsonObject()
                ? element.getAsJsonObject() : null;
    }

    private static boolean satisfied(JsonObject valuation) {
        return "sat".equals(optionalString(valuation, "status"));
    }

    private static String claimReason(String claim, String reachability,
                                      List<JsonObject> blockers,
                                      String refusals) {
        if (SAT_CANDIDATE.equals(claim)) {
            return "a valuation satisfies the target predicate inside the"
                    + " recorded model and a symbolic root flips it";
        }
        if (UNSAT_CLOSED.equals(claim)) {
            return "no valuation satisfies the target predicate and the"
                    + " selected model is closed";
        }
        StringBuilder reason = new StringBuilder();
        reason.append(blockers.size()).append(" blocker(s) withhold an")
                .append(" accepted claim from a ").append(reachability)
                .append(" solver result: ");
        for (int index = 0; index < blockers.size(); index++) {
            if (index > 0) {
                reason.append(',');
            }
            reason.append(optionalString(blockers.get(index), "code"));
        }
        if (!refusals.isEmpty()) {
            reason.append("; Composer refusals: ").append(refusals);
        }
        return reason.toString();
    }

    /** One line per blocker: the whole reason a run was not accepted. */
    private static String whyNotAccepted(String claim,
                                         List<JsonObject> blockers) {
        if (blockers.isEmpty()) {
            return "";
        }
        StringBuilder summary = new StringBuilder();
        summary.append("claim=").append(claim).append(": ")
                .append(blockers.size())
                .append(" blocker(s) withhold acceptance");
        for (JsonObject row : blockers) {
            String subject = optionalString(row, "subject");
            summary.append(System.lineSeparator()).append("  ")
                    .append(optionalString(row, "code"));
            if (!subject.isEmpty()) {
                summary.append(" [").append(subject).append(']');
            }
            summary.append(": ").append(optionalString(row, "detail"));
        }
        return summary.toString();
    }

    private static JsonObject blocker(String code, String subject,
                                      String detail) {
        JsonObject row = new JsonObject();
        row.addProperty("code", code);
        row.addProperty("subject", subject == null ? "" : subject);
        row.addProperty("detail", detail);
        return row;
    }

    private static String code(JsonElement element) {
        if (element == null) {
            return "";
        }
        if (element.isJsonObject()) {
            JsonObject row = element.getAsJsonObject();
            return firstNonEmpty(optionalString(row, "code"),
                    firstNonEmpty(optionalString(row, "reason"),
                            optionalString(row, "kind")));
        }
        return element.isJsonPrimitive() ? element.getAsString() : "";
    }

    private static String codes(JsonArray rows) {
        Set<String> unique = new LinkedHashSet<>();
        for (JsonElement element : rows) {
            String code = code(element);
            if (!code.isEmpty()) {
                unique.add(code);
            }
        }
        return String.join(",", unique);
    }

    private static String firstNonEmpty(String value, String fallback) {
        return value == null || value.trim().isEmpty() ? fallback : value;
    }
}
