package edu.uva.liftlab.graphchecker.concolic;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
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
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
    /** The solver returned neither sat nor unsat on an enumerated valuation. */
    static final String SOLVER_UNDECIDED_VALUATIONS =
            "SOLVER_UNDECIDED_VALUATIONS";
    /** An UNSAT result without closed selected-path authority is not closed. */
    static final String UNSAT_CLOSURE_INCOMPLETE = "UNSAT_CLOSURE_INCOMPLETE";
    /** The solver stage reached no exact reachability decision. */
    static final String NO_EXACT_REACHABILITY = "NO_EXACT_REACHABILITY";

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
                    && !"mappings".equals(key)) {
                throw new IllegalArgumentException(
                        "Unknown claim option: --" + key);
            }
            values.put(key, argv[++index]);
        }
        JsonObject manifest = ArtifactIO.readObject(
                required(values, "manifest"));
        JsonObject reach = ArtifactIO.readObject(required(values, "reach"));
        JsonObject claim = decide(manifest, reach,
                declaredWireFlows(values.get("mappings")));
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
     * The number of {@code WIRE_FLOW} rows the experiment declares. A blank
     * or absent path is an experiment that declares none, which is a
     * single-node experiment rather than an unrealized flow.
     */
    public static int declaredWireFlows(String mappings) throws IOException {
        if (mappings == null || mappings.trim().isEmpty()) {
            return 0;
        }
        Path path = Paths.get(mappings.trim());
        if (!Files.isRegularFile(path)) {
            return 0;
        }
        int declared = 0;
        for (JsonObject row : ArtifactIO.readJsonl(path)) {
            if (WIRE_FLOW_KIND.equals(optionalString(row, "kind"))) {
                declared++;
            }
        }
        return declared;
    }

    /**
     * Decides the campaign claim from the Composer's manifest and the
     * reach-condition report, and names every blocker that withholds
     * acceptance.
     *
     * @param manifest the composition manifest the Composer published
     * @param reach the reach-condition report the solver stage published
     * @param declaredWireFlows how many wire flows the experiment declares
     */
    public static JsonObject decide(JsonObject manifest, JsonObject reach,
                                    int declaredWireFlows) {
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
        int boundaryFamilies = array(manifest, "symbolicPropagation").size();

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

        // An experiment that declares cross-node flows and composes no
        // consumer boundary family replayed neither side of the wire into the
        // formula, whatever the formula then satisfies.
        if (declaredWireFlows > 0 && boundaryFamilies == 0) {
            blockers.add(blocker(DECLARED_WIRE_FLOWS_UNREALIZED,
                    String.valueOf(declaredWireFlows),
                    "the experiment declares " + declaredWireFlows
                            + " WIRE_FLOW(s) and the composition realized no"
                            + " consumer boundary family"));
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
        rootSpace.addProperty("declaredWireFlows", declaredWireFlows);
        rootSpace.addProperty("consumerBoundaryFamilies", boundaryFamilies);
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
                vector.append(value).append(' ');
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
