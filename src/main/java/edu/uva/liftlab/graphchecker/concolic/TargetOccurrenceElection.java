package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.ComposedManifest;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * Elects which composed target occurrence the campaign claim rests on.
 *
 * <p>The planner plants one target-reach goal per observed occurrence of the
 * annotated site, and a run composes and solves each of them.  Each
 * composition is a formula about one execution of that site, so each carries
 * its own {@link ClaimPolicy} decision, and the run has as many verdicts as
 * the recording had occurrences.  This publishes every one of them and says
 * which the campaign's own artifacts were taken from.
 *
 * <p>Two things decide that, and nothing else.  An occurrence whose own
 * artifacts carry an accepted claim displaces one whose do not -- the target
 * is reached if any of its anchored occurrences reaches it, so an acceptance
 * anywhere is the campaign's acceptance.  Among equals the order is the
 * anchor address, (node, epoch, region, ordinal), which is what an occurrence
 * <em>is</em>; it is stated rather than taken from whatever order the
 * schedule happened to emit.  There is no measure of support here: degrees of
 * evidence -- an explained witness over an unexplained one, fewer blockers
 * over more -- decided which answer a campaign published by a scale nothing
 * in the design defines.  Each occurrence's support is reported, beside every
 * other occurrence's, for a reader to act on.</p>
 *
 * <p>This is not a disjunction over the formulas.  Each is solved on its own
 * and none is weakened by another; what is picked here is which of several
 * finished answers the campaign's top-level artifacts are copied from.</p>
 */
public final class TargetOccurrenceElection {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "TARGET_OCCURRENCE_LEDGER";

    /** A composed occurrence whose satisfying witness the policy explained. */
    static final String SAT_CANDIDATE_EXPLAINED_WITNESS =
            "SAT_CANDIDATE_EXPLAINED_WITNESS";
    static final String SAT_CANDIDATE = "SAT_CANDIDATE";
    static final String UNSAT_CLOSED = "UNSAT_CLOSED";
    static final String INCONCLUSIVE = "INCONCLUSIVE";
    /** A formula the Composer refused: it states nothing about its
     *  occurrence, but it exists, and a run whose every occurrence was
     *  refused still publishes one refusal with its named blockers rather
     *  than nothing at all. */
    static final String REFUSED = "REFUSED";
    /** No formula at all: this occurrence was never composed, so there is
     *  nothing here for a consumer to read.  It can never be elected while
     *  any occurrence has artifacts. */
    static final String NOT_COMPOSED = "NOT_COMPOSED";

    /** The occurrence was planned but its fatal read was never observed in
     *  any summary this run linked, so there was nothing to compose. */
    public static final String SKIPPED_UNOBSERVED = "SKIPPED_UNOBSERVED";
    public static final String COMPOSED = "COMPOSED";


    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private TargetOccurrenceElection() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        JsonObject ledger = elect(ArtifactIO.readJsonl(arguments.reports,
                "Malformed target occurrence report %1$s:%2$d",
                "Non-object target occurrence report %1$s:%2$d"));
        ArtifactIO.replaceJson(arguments.output, ledger, GSON);
        System.out.println(optionalString(ledger, "chosenOccurrenceId"));
    }

    /**
     * One ledger over every reported target occurrence, in anchor-address
     * order, with the one the campaign's artifacts came from flagged.
     */
    static JsonObject elect(List<JsonObject> reports) throws IOException {
        if (reports.isEmpty()) {
            throw new IOException("no target occurrence was reported: a run"
                    + " composes at least the elected target");
        }
        List<JsonObject> rows = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        int composed = 0;
        for (int index = 0; index < reports.size(); index++) {
            JsonObject report = reports.get(index);
            String occurrence = optionalString(report, "occurrenceId");
            if (occurrence.isEmpty()) {
                throw new IOException("target occurrence report " + index
                        + " names no occurrence");
            }
            if (!seen.add(occurrence)) {
                throw new IOException("target occurrence reported twice: "
                        + occurrence);
            }
            JsonObject row = verdict(report);
            if (COMPOSED.equals(optionalString(row, "status"))) {
                composed++;
            }
            rows.add(row);
        }
        Collections.sort(rows, new Comparator<JsonObject>() {
            @Override
            public int compare(JsonObject left, JsonObject right) {
                return anchorAddress(left).compareTo(anchorAddress(right));
            }
        });
        for (int index = 0; index < rows.size(); index++) {
            rows.get(index).addProperty("order", index);
        }
        int elected = 0;
        for (int index = 1; index < rows.size(); index++) {
            if (outranks(rows.get(index), rows.get(elected))) {
                elected = index;
            }
        }
        JsonArray occurrences = new JsonArray();
        for (int index = 0; index < rows.size(); index++) {
            JsonObject row = rows.get(index);
            row.addProperty("chosen", index == elected);
            occurrences.add(row);
        }
        JsonObject chosen = rows.get(elected);
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        result.addProperty("occurrenceCount", rows.size());
        result.addProperty("composedCount", composed);
        result.addProperty("chosenOccurrenceId",
                optionalString(chosen, "occurrenceId"));
        result.addProperty("chosenTaskId", optionalString(chosen, "taskId"));
        result.addProperty("chosenSupport", optionalString(chosen, "support"));
        // Why this one and not another, in the terms the rows carry.  A
        // reader asking "the run says SAT, which execution of the site is
        // that about" gets the answer without re-deriving the order.
        result.addProperty("electionReason", electionReason(rows, elected));
        result.add("occurrences", occurrences);
        return result;
    }

    /** One occurrence's published verdict, read from its own artifacts. */
    private static JsonObject verdict(JsonObject report)
            throws IOException {
        JsonObject row = new JsonObject();
        row.addProperty("occurrenceId", optionalString(report,
                "occurrenceId"));
        row.addProperty("regionId", optionalString(report, "regionId"));
        row.addProperty("goalId", optionalString(report, "goalId"));
        row.addProperty("taskId", optionalString(report, "taskId"));
        row.addProperty("artifactDir", optionalString(report, "artifactDir"));
        row.addProperty("composeWallMillis",
                optionalLongInteger(report, "composeWallMillis", -1L));
        row.addProperty("solveWallMillis",
                optionalLongInteger(report, "solveWallMillis", -1L));
        String status = optionalString(report, "status");
        if (!COMPOSED.equals(status)) {
            row.addProperty("status", status.isEmpty()
                    ? SKIPPED_UNOBSERVED : status);
            row.addProperty("detail", optionalString(report, "detail"));
            row.addProperty("claim", "");
            row.addProperty("claimReason", "");
            row.addProperty("blockerCount", 0);
            row.addProperty("finalStatus", "");
            row.addProperty("finalStatusRefusals", 0);
            row.addProperty("reachability", "");
            row.addProperty("solverState", "");
            row.addProperty("acceptedValuationOrdinal", -1);
            row.addProperty("acceptedWitnessKind", "");
            row.addProperty("support", NOT_COMPOSED);
            return row;
        }
        JsonObject manifest = readRequired(report, "manifest",
                "composition manifest");
        // SOLVE publishes beside the formula it solved, in the same
        // artifact: one anchored occurrence, one file.
        JsonObject reach = object(manifest, ComposedManifest.SOLVER);
        JsonObject claim = object(reach, "campaignClaim");
        if (claim.size() == 0) {
            throw new IOException("the composition manifest for "
                    + optionalString(report, "occurrenceId")
                    + " carries no solver decision: "
                    + optionalString(report, "manifest"));
        }
        JsonObject rootSpace = object(claim, "rootSpace");
        String finalStatus = optionalString(manifest, "finalStatus");
        int refusals = array(manifest, "finalStatusRefusals").size();
        int accepted = optionalInteger(rootSpace,
                "acceptedValuationOrdinal", -1);
        row.addProperty("status", COMPOSED);
        row.addProperty("detail", optionalString(report, "detail"));
        row.addProperty("claim", optionalString(claim, "claim"));
        row.addProperty("claimReason", optionalString(claim, "claimReason"));
        row.addProperty("blockerCount",
                optionalInteger(claim, "blockerCount",
                        array(claim, "blockers").size()));
        row.addProperty("finalStatus", finalStatus);
        row.addProperty("finalStatusRefusals", refusals);
        row.addProperty("reachability",
                optionalString(reach, "reachability"));
        row.addProperty("solverState", optionalString(reach, "state"));
        row.addProperty("acceptedValuationOrdinal", accepted);
        row.addProperty("acceptedWitnessKind",
                optionalString(rootSpace, "acceptedWitnessKind"));
        row.addProperty("support", support(optionalString(claim, "claim"),
                finalStatus, refusals, accepted));
        return row;
    }

    /**
     * How much this occurrence's own artifacts support a campaign claim.
     *
     * <p>A composition the Composer refused states nothing about the site,
     * whatever claim the solver stage then computed over the refusal stub, so
     * it ranks below every composed formula -- but above an occurrence that
     * was never composed, which has no artifacts for a consumer to read at
     * all.  A run whose every occurrence was refused therefore still
     * publishes one refused composition with its named blockers, which is
     * exactly what a run with one target occurrence has always published.</p>
     */
    static String support(String claim, String finalStatus, int refusals,
                          int acceptedValuationOrdinal) {
        if (refusals > 0 || !"FINAL_READY".equals(finalStatus)) {
            return REFUSED;
        }
        if (ClaimPolicy.SAT_CANDIDATE.equals(claim)) {
            return acceptedValuationOrdinal >= 0
                    ? SAT_CANDIDATE_EXPLAINED_WITNESS : SAT_CANDIDATE;
        }
        if (ClaimPolicy.UNSAT_CLOSED.equals(claim)) {
            return UNSAT_CLOSED;
        }
        if (ClaimPolicy.INCONCLUSIVE_PARTIAL.equals(claim)) {
            return INCONCLUSIVE;
        }
        return REFUSED;
    }

    /**
     * An accepted answer displaces an unaccepted one, and nothing else does.
     *
     * <p>Each occurrence is its own question with its own answer, so there
     * are only two things to say about a pair of them: one of them was
     * accepted and the other was not, or neither was.  Equal standing leaves
     * the anchor-address order the rows are already in.</p>
     */
    private static boolean outranks(JsonObject candidate, JsonObject best) {
        return accepted(candidate) && !accepted(best);
    }

    /**
     * One occurrence's sort key: node, epoch, region, ordinal.
     *
     * <p>An occurrence id reads {@code <workload>/<node>#<epoch>/region/<region>#<k>}.
     * The ordinal is compared as a number, zero-padded here rather than
     * parsed, so that #10 follows #9 instead of #1.  An id that does not
     * parse sorts by itself, which keeps the order total without inventing a
     * position for it.</p>
     */
    private static String anchorAddress(JsonObject row) {
        String occurrence = optionalString(row, "occurrenceId");
        int hash = occurrence.lastIndexOf('#');
        if (hash < 0) return occurrence;
        String ordinal = occurrence.substring(hash + 1);
        for (int index = 0; index < ordinal.length(); index++) {
            if (!Character.isDigit(ordinal.charAt(index))) return occurrence;
        }
        StringBuilder padded = new StringBuilder(
                occurrence.substring(0, hash + 1));
        for (int pad = ordinal.length(); pad < 12; pad++) padded.append('0');
        return padded.append(ordinal).toString();
    }

    /** Whether this occurrence's own artifacts carry an accepted claim. */
    private static boolean accepted(JsonObject row) {
        String support = optionalString(row, "support");
        return SAT_CANDIDATE_EXPLAINED_WITNESS.equals(support)
                || SAT_CANDIDATE.equals(support)
                || UNSAT_CLOSED.equals(support);
    }

    private static String electionReason(List<JsonObject> rows, int elected) {
        JsonObject chosen = rows.get(elected);
        String support = optionalString(chosen, "support");
        if (rows.size() == 1) {
            return "the recording observed one occurrence of the annotated"
                    + " target; the campaign claim is its own (support="
                    + support + ")";
        }
        List<String> others = new ArrayList<>();
        for (int index = 0; index < rows.size(); index++) {
            if (index == elected) {
                continue;
            }
            others.add(optionalString(rows.get(index), "occurrenceId") + "="
                    + optionalString(rows.get(index), "support"));
        }
        return "the campaign artifacts are "
                + optionalString(chosen, "occurrenceId") + "'s (support="
                + support + "), the first of " + rows.size()
                + " observed target occurrence(s) in anchor order to carry an"
                + " accepted claim, or the first of them outright when none"
                + " did; the others are " + String.join(", ", others);
    }

    private static JsonObject readRequired(JsonObject report, String field,
                                           String label) throws IOException {
        String raw = optionalString(report, field);
        if (raw.isEmpty()) {
            throw new IOException("a composed target occurrence names no "
                    + label + ": " + optionalString(report, "occurrenceId"));
        }
        Path path = Paths.get(raw);
        if (!Files.isRegularFile(path)) {
            throw new IOException("the " + label + " for "
                    + optionalString(report, "occurrenceId")
                    + " does not exist: " + path);
        }
        return ArtifactIO.readObject(path);
    }

    static final class Arguments {
        private Path reports;
        private Path output;

        static Arguments parse(String[] argv) throws IOException {
            Arguments result = new Arguments();
            for (int index = 0; index < argv.length; index++) {
                String argument = argv[index];
                if (!argument.startsWith("--")) {
                    throw new IOException("unexpected argument: " + argument);
                }
                String key = argument.substring(2);
                if (index + 1 >= argv.length) {
                    throw new IOException("--" + key + " requires a value");
                }
                String value = argv[++index];
                if ("reports".equals(key)) {
                    result.reports = Paths.get(value);
                } else if ("output".equals(key)) {
                    result.output = Paths.get(value);
                } else {
                    throw new IOException("unknown argument: " + argument);
                }
            }
            if (result.reports == null || result.output == null) {
                throw new IOException("usage: TargetOccurrenceElection"
                        + " --reports FILE --output FILE");
            }
            return result;
        }
    }
}
