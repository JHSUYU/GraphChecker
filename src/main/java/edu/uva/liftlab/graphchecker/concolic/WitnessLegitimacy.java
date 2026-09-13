package edu.uva.liftlab.graphchecker.concolic;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Which satisfying witnesses are findings, and which are unexplained freedom.
 *
 * <p>A SAT witness used to be treated as a blocker whenever it appeared in a
 * polarity the experiment did not plant a fault in: both polarities
 * satisfiable refuted the hypothesis, and a clock that moved was decoration
 * unless the solver could show the polarity died without it. That reading
 * discards real findings. Key rotation races and clock drift <em>happen</em>,
 * on the "other" polarity as readily as on the planted one, and a witness that
 * names one is a legitimate finding about the program rather than a defect in
 * the analysis.</p>
 *
 * <p>So a witness is read against a fixed, named set of mechanisms the
 * recording physically allows:</p>
 *
 * <ul>
 *   <li>{@code MARKER_FLIPPED} -- the experiment's own injected fault.</li>
 *   <li>{@code CLOCK_SKEW} inside the configured window, at a wall-clock value
 *   that is a time rather than arithmetic noise.</li>
 *   <li>{@link RecordedOrderRace#KIND} -- the fatal read took the program's own
 *   last writer while the same location is written again later in the recorded
 *   order.</li>
 * </ul>
 *
 * <p>A witness every one of whose mechanisms is in that set, standing on a
 * composition that left the witness no unexplained freedom, is
 * {@link #EXPLAINED}: a finding, reported with its narrative. Anything else is
 * {@link #UNEXPLAINED}, and the freedom is named -- a free INITIAL arm over a
 * snapshot nobody reconstructed, an existential root space nobody enumerated,
 * a wire whose value the composition never bound, a clock outside its window
 * or at a value no clock returns. Only those block.</p>
 */
public final class WitnessLegitimacy {
    /** Where per-valuation findings are published. */
    public static final String FINDINGS = "witnessFindings";
    static final String KIND = "WITNESS_LEGITIMACY";
    static final String AUTHORITY = "RECORDED_MECHANISM_LEGITIMACY_V1";

    /** The injected fault marker, flipped. */
    public static final String MARKER_FLIPPED = "MARKER_FLIPPED";
    /** A wall clock moved off the value it recorded. */
    public static final String CLOCK_SKEW = "CLOCK_SKEW";
    /** A root moved with nothing named about what moved it. */
    public static final String ROOT_MOVED = "ROOT_MOVED";

    /** Every mechanism this witness names is one the world allows. */
    public static final String EXPLAINED = "EXPLAINED";
    /** Some part of this witness is freedom nobody accounted for. */
    public static final String UNEXPLAINED = "UNEXPLAINED";

    /** The witness reads a container state nobody reconstructed. */
    public static final String FREE_INITIAL_ARM = "FREE_INITIAL_ARM";
    /** The existential root space was never enumerated. */
    public static final String UNENUMERATED_EXISTENTIAL_ROOT =
            "UNENUMERATED_EXISTENTIAL_ROOT";
    /** A declared wire carried a value the composition never bound. */
    public static final String UNBOUND_WIRE_VALUE = "UNBOUND_WIRE_VALUE";
    /**
     * This model read a merged wire boundary through a consumer it left
     * active while satisfying none of the boundary's case arms: the value
     * the consumer took is the boundary's fall-through, which nothing
     * binds.  Distinct from {@link #UNBOUND_WIRE_VALUE}, which the
     * composition states about a declared flow and withholds under its own
     * blocker; this one is a property of one model.
     */
    public static final String UNBOUND_WIRE_VALUE_TAKEN =
            "UNBOUND_WIRE_VALUE_TAKEN";
    /** A clock left the window the recording anchors it in. */
    public static final String CLOCK_OUTSIDE_WINDOW = "CLOCK_OUTSIDE_WINDOW";
    /** A wall clock at a value no wall clock returns. */
    public static final String ABSURD_CLOCK_VALUE = "ABSURD_CLOCK_VALUE";
    /** A root moved and no named mechanism says what moved it. */
    public static final String UNEXPLAINED_ROOT_MOVE =
            "UNEXPLAINED_ROOT_MOVE";
    /**
     * The witness read an associative container's absent-key default: the
     * key it asked with is in no PUT of the chain and in none of the state
     * the chain was reconstructed from, so the null it got is the empty
     * map's answer and names nothing the program did.
     */
    public static final String ABSENT_KEY_DEFAULT = "ABSENT_KEY_DEFAULT";
    /**
     * A wall clock moved, and the target reaches with every clock back on
     * the value it recorded.  The move is then decoration: the witness is
     * satisfied by something else and the clock is along for the ride.
     */
    public static final String CLOCK_NOT_NECESSARY = "CLOCK_NOT_NECESSARY";
    /**
     * A wall clock moved and no probe said whether the move was needed.
     *
     * <p>Necessity is the whole content of a clock mechanism: an
     * unconstrained clock differs from its recording under every model, so
     * "it moved" is a property of the solver rather than of the program.
     * A probe that never ran leaves that question open, and an open question
     * is not a mechanism.  This is the freedom that used to be spent as one:
     * {@code ClockNecessity.UNKNOWN} was accepted, and on hdfs-17899-bug3
     * forty clock moves -- the largest 294,961ms against a 300,000ms
     * window -- were published as the witness's mechanism with no probe
     * behind any of them.</p>
     */
    public static final String CLOCK_NECESSITY_UNKNOWN =
            "CLOCK_NECESSITY_UNKNOWN";

    /**
     * The four shapes a satisfying witness may be a finding in.
     *
     * <p>A witness is a finding only where it names one of these, and it
     * names exactly one: the mechanism list may hold several rows, but the
     * claim the campaign publishes is one sentence about one mechanism, and
     * an empty list is not a finding at all.</p>
     *
     * <ul>
     *   <li>{@link #MARKER_FLIPPED} -- a Boolean root moved off the value it
     *   recorded and the fatal predicate is satisfied there.</li>
     *   <li>{@link #ROTATION_RACE} -- the recorded write order states the
     *   race, as {@link RecordedOrderRace} defines it.</li>
     *   <li>{@link #CLOCK_SKEW} -- a wall clock moved inside the declared
     *   window <em>and</em> the necessity probe showed the target does not
     *   reach with the clocks back on record.</li>
     *   <li>{@link #RECORDED_FAILURE_EXPLAINED} -- the fatal predicate is
     *   satisfied with every declared root at the value it recorded, and the
     *   other polarity of each Boolean root is unsat: the recording is the
     *   failing run and the chain shows it is root-determined.  HDFS-17960
     *   is this shape.</li>
     * </ul>
     *
     * <p>Where two apply the first of that list is published, because a
     * flipped marker is a stronger statement than a clock that accompanied
     * it; every mechanism the witness named stays on the row beside it.</p>
     */
    public static final String ROTATION_RACE = RecordedOrderRace.KIND;
    /** The recorded valuation is the failing one, and the flip is unsat. */
    public static final String RECORDED_FAILURE_EXPLAINED =
            "RECORDED_FAILURE_EXPLAINED";
    /** Where a classified witness publishes which of the four it is. */
    public static final String FINDING_KIND = "findingKind";

    /** What the necessity probe said about this witness's clock group. */
    public enum ClockNecessity {
        /** No probe ran, so nothing is claimed either way. */
        UNKNOWN,
        /** The target is unreachable with the clocks back on record. */
        NECESSARY,
        /** The target still reaches with the clocks back on record. */
        NOT_NECESSARY
    }

    /**
     * The degeneracy verdict that says the existential root space is open.
     * It is a prefix because the verdict carries the count.
     */
    static final String UNENUMERATED_ROOTS_VERDICT =
            "UNDECIDED_UNENUMERATED_EXISTENTIAL_ROOTS";

    private WitnessLegitimacy() {
    }

    /** One thing a witness was free to choose that nobody accounted for. */
    public static final class Freedom {
        private final String code;
        private final String subject;
        private final String detail;

        Freedom(String code, String subject, String detail) {
            this.code = code;
            this.subject = subject == null ? "" : subject;
            this.detail = detail == null ? "" : detail;
        }

        public String code() {
            return code;
        }

        public String subject() {
            return subject;
        }

        JsonObject toJson() {
            JsonObject row = new JsonObject();
            row.addProperty("code", code);
            row.addProperty("subject", subject);
            row.addProperty("detail", detail);
            return row;
        }

        @Override
        public String toString() {
            return subject.isEmpty() ? code : code + "[" + subject + "]";
        }
    }

    /**
     * The freedom the composition leaves every witness, whatever model it is.
     *
     * <p>These are properties of the formula rather than of one model, so a
     * witness cannot argue its way out of them by naming a mechanism: an
     * unenumerated root space is freedom under every valuation of it. Each one
     * already has its own blocker in {@link ClaimPolicy}, which is why they are
     * reported here rather than blocked again under a second name.</p>
     *
     * @param degeneracy the solver stage's degeneracy verdict
     * @param freeInitialArms fatal-read arms the model selected that are the
     *                        untouched initial content of a truncated carrier
     * @param unrealizedFlows declared wire flows whose value bound nothing
     */
    public static List<Freedom> compositionFreedoms(String degeneracy) {
        List<Freedom> freedoms = new ArrayList<>();
        if (degeneracy != null
                && degeneracy.startsWith(UNENUMERATED_ROOTS_VERDICT)) {
            freedoms.add(new Freedom(UNENUMERATED_EXISTENTIAL_ROOT, degeneracy,
                    "the existential root space was never enumerated, so a"
                            + " witness over it is free where the recording"
                            + " says nothing"));
        }
        // Two freedoms used to be read here and are gone with what produced
        // them: a witness reading the fatal value out of a reconstructed
        // INITIAL arm -- there are no arms, and the value is the write the
        // replay made -- and a wire whose boundary family nothing lowered,
        // where a wire value is now the producer's own expression.
        return freedoms;
    }

    /**
     * Reads one valuation's witness against the legitimate set.
     *
     * @param valuation one enumerated valuation row of the reach report
     * @param ordinal its position among the enumerated valuations
     * @param windowMillis the configured clock skew, in milliseconds
     * @param composition the freedom the composition leaves every witness
     * @param markerAssignment every declared fault marker's value under this
     *                         valuation, each row flagged {@code flipped} when
     *                         it differs from what that marker recorded
     */
    public static JsonObject classify(JsonObject valuation, int ordinal,
                                      long windowMillis,
                                      List<Freedom> composition,
                                      JsonArray markerAssignment) {
        return classify(valuation, ordinal, windowMillis, composition,
                markerAssignment, ClockNecessity.UNKNOWN, false);
    }

    /**
     * Reads one valuation's witness against the legitimate set.
     *
     * @param clockNecessity what the necessity probe said about this
     *                       witness's clock group.  A clock that moved and
     *                       was shown not to be needed is not the mechanism
     *                       of anything: the target reaches without it, so
     *                       naming it {@code CLOCK_SKEW} states a cause the
     *                       formula does not have.  That is how nine roots
     *                       parked on their window boundaries, none of them
     *                       in any satisfied conjunct, were reported as
     *                       "sat via CLOCK_SKEW x9".
     */
    public static JsonObject classify(JsonObject valuation, int ordinal,
                                      long windowMillis,
                                      List<Freedom> composition,
                                      JsonArray markerAssignment,
                                      ClockNecessity clockNecessity) {
        return classify(valuation, ordinal, windowMillis, composition,
                markerAssignment, clockNecessity, false);
    }

    /**
     * Reads one valuation's witness against the legitimate set.
     *
     * @param recordedFailureExplained whether the composition showed this
     *                                 run's recorded valuation is the failing
     *                                 one -- satisfied with every declared
     *                                 root where the recording left it, and
     *                                 unsat under every enumerated flip of
     *                                 one.  It is a fact about the run and
     *                                 not about this row, so it is decided
     *                                 once by {@link ClaimPolicy} and handed
     *                                 down; a row that moved nothing is the
     *                                 only one it applies to.
     */
    public static JsonObject classify(JsonObject valuation, int ordinal,
                                      long windowMillis,
                                      List<Freedom> composition,
                                      JsonArray markerAssignment,
                                      ClockNecessity clockNecessity,
                                      boolean recordedFailureExplained) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", KIND);
        row.addProperty("authority", AUTHORITY);
        row.addProperty("valuationOrdinal", ordinal);
        String status = valuation == null ? ""
                : optionalString(valuation, "status");
        row.addProperty("status", status);
        if (valuation != null && valuation.has("values")) {
            row.add("values", valuation.get("values"));
        }
        // Which markers this valuation moved, named where they sit. A reader
        // of a two-marker case has to be able to say which call was made to
        // fail, and "values: [false, true]" does not say it.
        JsonArray assignment = markerAssignment == null ? new JsonArray()
                : markerAssignment;
        JsonArray flipped = new JsonArray();
        for (JsonElement element : assignment) {
            if (element.isJsonObject() && element.getAsJsonObject()
                    .has("flipped")
                    && element.getAsJsonObject().get("flipped")
                            .getAsBoolean()) {
                flipped.add(element);
            }
        }
        row.add("markerAssignment", assignment);
        // Whether the polarities these markers are being compared against
        // were recorded at all. A defaulted polarity makes "flips" a guess,
        // and the narrative says so rather than asserting the flip.
        row.addProperty("recordedPolarityStated",
                everyRecordedPolarityStated(assignment));
        row.add("flippedMarkers", flipped);
        row.addProperty("flippedMarkerCount", flipped.size());
        // The world as the recording had it: every declared marker left alone.
        row.addProperty("allRecorded",
                assignment.size() > 0 && flipped.size() == 0);
        JsonArray legitimate = new JsonArray();
        List<Freedom> freedoms = new ArrayList<>();
        if (!"sat".equals(status)) {
            // Only a satisfying valuation carries a witness to read.
            row.addProperty("verdict", EXPLAINED);
            row.add("mechanisms", legitimate);
            row.add("freedoms", new JsonArray());
            // Only a satisfying valuation can be a finding, so the kind is
            // stated empty rather than left off: an absent field would read
            // as an artifact nobody classified.
            row.addProperty(FINDING_KIND, "");
            row.addProperty("narrative", markerPrefix(flipped, assignment)
                    + narrative(status, legitimate, freedoms, ""));
            return row;
        }
        freedoms.addAll(composition == null
                ? Collections.<Freedom>emptyList() : composition);
        for (JsonElement element : array(valuation, "witnessMechanisms")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject mechanism = element.getAsJsonObject();
            Freedom refusal = refuse(mechanism, windowMillis,
                    clockNecessity);
            if (refusal == null) {
                legitimate.add(mechanism);
            } else {
                freedoms.add(refusal);
            }
        }
        // Freedom the solver stage decided from this model rather than from
        // the formula: a wire boundary no arm of which the model satisfied,
        // and a read that answered out of an absent-key default.
        for (JsonElement element : array(valuation,
                "witnessFreedoms")) {
            if (!element.isJsonObject()) continue;
            JsonObject decided = element.getAsJsonObject();
            freedoms.add(new Freedom(optionalString(decided, "code"),
                    optionalString(decided, "subject"),
                    optionalString(decided, "detail")));
        }
        row.addProperty("verdict", freedoms.isEmpty() ? EXPLAINED
                : UNEXPLAINED);
        row.add("mechanisms", legitimate);
        JsonArray freedomRows = new JsonArray();
        for (Freedom freedom : freedoms) {
            freedomRows.add(freedom.toJson());
        }
        row.add("freedoms", freedomRows);
        String kind = findingKind(legitimate, flipped, assignment,
                recordedFailureExplained);
        row.addProperty(FINDING_KIND, kind);
        row.addProperty("narrative", markerPrefix(flipped, assignment)
                + narrative(status, legitimate, freedoms, kind));
        return row;
    }

    /**
     * Which of the four shapes this satisfying witness is, or {@code ""}.
     *
     * <p>Only a mechanism that survived {@link #refuse} counts, so a clock
     * the necessity probe did not answer for is not a {@link #CLOCK_SKEW}
     * finding and a flip measured against a value nobody recorded is not a
     * {@link #MARKER_FLIPPED} one -- an unstated marker never reaches
     * {@code flipped} at all.  An empty answer is the refusal: the witness
     * satisfies the formula and names nothing the world does.</p>
     */
    private static String findingKind(JsonArray legitimate, JsonArray flipped,
                                      JsonArray assignment,
                                      boolean recordedFailureExplained) {
        if (flipped.size() > 0 && namesKind(legitimate, MARKER_FLIPPED)) {
            return MARKER_FLIPPED;
        }
        if (namesKind(legitimate, ROTATION_RACE)) {
            return ROTATION_RACE;
        }
        if (namesKind(legitimate, CLOCK_SKEW)) {
            return CLOCK_SKEW;
        }
        if (recordedFailureExplained && flipped.size() == 0
                && everyRecordedPolarityStated(assignment)) {
            return RECORDED_FAILURE_EXPLAINED;
        }
        return "";
    }

    private static boolean namesKind(JsonArray mechanisms, String kind) {
        for (JsonElement element : mechanisms) {
            if (element.isJsonObject() && kind.equals(optionalString(
                    element.getAsJsonObject(), "kind"))) {
                return true;
            }
        }
        return false;
    }

    /** Whether every marker here was compared against a recorded value. */
    private static boolean everyRecordedPolarityStated(JsonArray assignment) {
        for (JsonElement element : assignment) {
            if (!element.isJsonObject()
                    || !element.getAsJsonObject()
                    .has("recordedPolarityStated")
                    || !element.getAsJsonObject()
                    .get("recordedPolarityStated").getAsBoolean()) {
                return false;
            }
        }
        return assignment.size() > 0;
    }

    /**
     * Which markers this valuation moved, as the front of its narrative.
     *
     * <p>Named, not counted: with two markers on one region the difference
     * between "the constructor's updateBlockKeys" and "the updater thread's
     * getBlockKeys" is the whole finding, and an occurrence id is what tells
     * them apart.</p>
     */
    private static String markerPrefix(JsonArray flipped,
                                       JsonArray assignment) {
        if (flipped.size() == 0) {
            return recordedPrefix(assignment);
        }
        StringBuilder text = new StringBuilder("flips ");
        for (int index = 0; index < flipped.size(); index++) {
            if (index > 0) {
                text.append(" and ");
            }
            JsonObject marker = flipped.get(index).getAsJsonObject();
            text.append(name(marker));
            String where = firstNonEmpty(optionalString(marker, "siteId"),
                    optionalString(marker, "portId"));
            if (!where.isEmpty()) {
                text.append(" (").append(where).append(")");
            }
            String occurrence = optionalString(marker, "occurrenceId");
            if (!occurrence.isEmpty()) {
                text.append(" at ").append(occurrence);
            }
        }
        return text.append("; ").toString();
    }

    /**
     * The front of a narrative whose valuation moved nothing.
     *
     * <p>"No marker flipped" and "every marker sat at the value the
     * recording had" are the same fact, and only the second one is a
     * finding a reader can act on: it says the witness reproduces the
     * recorded case. It is stated only where the recorded values actually
     * were recorded -- a defaulted polarity would make it a claim about a
     * recording nobody read.</p>
     */
    private static String recordedPrefix(JsonArray assignment) {
        if (!everyRecordedPolarityStated(assignment)) {
            return unstatedPrefix(assignment);
        }
        StringBuilder text = new StringBuilder(
                "every declared root at its recorded value (");
        for (int index = 0; index < assignment.size(); index++) {
            if (index > 0) {
                text.append(", ");
            }
            JsonObject marker = assignment.get(index).getAsJsonObject();
            text.append(name(marker)).append(" = ")
                    .append(marker.has("value")
                            && marker.get("value").getAsBoolean());
        }
        return text.append("); ").toString();
    }

    /**
     * The front of a narrative no recorded value can be read against.
     *
     * <p>Saying nothing here is what let a run whose roots nobody recorded
     * read exactly like a run that reproduced its recording.  The roots are
     * named instead, and nothing is assumed about what they held.</p>
     */
    private static String unstatedPrefix(JsonArray assignment) {
        List<String> unstated = new ArrayList<>();
        for (JsonElement element : assignment) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject marker = element.getAsJsonObject();
            if (!marker.has("recordedPolarityStated")
                    || !marker.get("recordedPolarityStated").getAsBoolean()) {
                unstated.add(name(marker));
            }
        }
        if (unstated.isEmpty()) {
            return "";
        }
        return "no recorded value is stated for " + unstated.size()
                + " declared root(s) (" + String.join(", ", unstated)
                + "), so nothing here is a flip or a reproduction; ";
    }

    /** How a marker row names itself. */
    private static String name(JsonObject marker) {
        return firstNonEmpty(optionalString(marker, "sourceIdentity"),
                optionalString(marker, "solverTerm"));
    }

    /**
     * Why this mechanism is not one the world allows, or {@code null}.
     *
     * <p>A marker flip is the experiment's own hypothesis and a rotation race
     * is the recorded order stating itself, so neither can be refused. A clock
     * is refused on two counts and two only: it left the window the recording
     * anchors it in, or it landed on a value that is not a time at all --
     * negative, or the arithmetic floor a 64-bit solver reaches for when
     * nothing constrains it. Anything else the witness moved has no named
     * mechanism behind it, and an unnamed move is freedom.</p>
     */
    private static Freedom refuse(JsonObject mechanism, long windowMillis,
                                  ClockNecessity clockNecessity) {
        String kind = optionalString(mechanism, "kind");
        String where = firstNonEmpty(optionalString(mechanism, "siteId"),
                firstNonEmpty(optionalString(mechanism, "sourceKey"),
                        optionalString(mechanism, "solverTerm")));
        if (MARKER_FLIPPED.equals(kind) || RecordedOrderRace.KIND.equals(kind)) {
            return null;
        }
        if (CLOCK_SKEW.equals(kind)) {
            BigInteger witnessed = integral(optionalString(mechanism,
                    "witnessValue"));
            BigInteger recorded = integral(optionalString(mechanism,
                    "recordedValue"));
            if (absurd(witnessed) || absurd(recorded)) {
                return new Freedom(ABSURD_CLOCK_VALUE, where,
                        "a wall clock at " + optionalString(mechanism,
                                "witnessValue") + " is not a time: no clock"
                                + " returns a negative or floor value");
            }
            long skew = Math.abs(optionalLongInteger(mechanism, "skewMillis",
                    0L));
            if (skew > Math.max(0L, windowMillis)) {
                return new Freedom(CLOCK_OUTSIDE_WINDOW, where,
                        "a clock moved " + skew + "ms, outside the configured"
                                + " +/-" + windowMillis + "ms window the"
                                + " recording anchors it in");
            }
            // A value that differs from the recording is not yet a
            // mechanism.  Every unconstrained clock differs from it: a
            // solver parks a free root wherever its window lets it, and
            // nothing about the target followed from the move.  The
            // mechanism is the move being needed.
            if (clockNecessity == ClockNecessity.NOT_NECESSARY) {
                return new Freedom(CLOCK_NOT_NECESSARY, where,
                        "a clock read " + optionalString(mechanism,
                                "witnessValue") + " where it recorded "
                                + optionalString(mechanism, "recordedValue")
                                + ", and the target still reaches with every"
                                + " clock back on its recorded value, so the"
                                + " move is in no conjunct this witness"
                                + " needs");
            }
            // No probe answered.  "It moved" is then all that is known, and
            // that much is true of every unconstrained clock under every
            // model: nothing here says the program could have done it.
            if (clockNecessity != ClockNecessity.NECESSARY) {
                return new Freedom(CLOCK_NECESSITY_UNKNOWN, where,
                        "a clock read " + optionalString(mechanism,
                                "witnessValue") + " where it recorded "
                                + optionalString(mechanism, "recordedValue")
                                + ", and no necessity probe answered for this"
                                + " witness's clock group, so nothing shows"
                                + " the target needed the move");
            }
            return null;
        }
        return new Freedom(UNEXPLAINED_ROOT_MOVE, where,
                "a root moved from " + optionalString(mechanism,
                        "recordedValue") + " to " + optionalString(mechanism,
                        "witnessValue") + " under kind "
                        + firstNonEmpty(kind, "none") + ", which names no"
                        + " mechanism the recording allows");
    }

    /** Long.MIN_VALUE and every negative absolute time. */
    private static boolean absurd(BigInteger value) {
        return value != null
                && (value.signum() < 0
                || value.equals(BigInteger.valueOf(Long.MIN_VALUE)));
    }

    private static BigInteger integral(String value) {
        String text = value == null ? "" : value.trim();
        if (text.startsWith("(-") && text.endsWith(")")) {
            text = "-" + text.substring(2, text.length() - 1).trim();
        }
        try {
            return new BigInteger(text);
        } catch (NumberFormatException notIntegral) {
            return null;
        }
    }

    /** One sentence a reader can put in a report. */
    private static String narrative(String status, JsonArray legitimate,
                                    List<Freedom> freedoms,
                                    String findingKind) {
        if (!"sat".equals(status)) {
            return "unsat".equals(status)
                    ? "no witness: the target is unreachable under this"
                    + " valuation"
                    : "no witness: the solver returned " + firstNonEmpty(
                            status, "no answer");
        }
        StringBuilder text = new StringBuilder();
        if (legitimate.size() == 0) {
            // "No root moved off its recorded value" is a claim about the
            // recording, and a witness whose roots nobody recorded cannot
            // make it; the prefix above has already named those roots.
            text.append(RECORDED_FAILURE_EXPLAINED.equals(findingKind)
                    ? "sat with every root at the value it recorded"
                    : "sat with no mechanism named");
        } else {
            // Named once each, with a count: a witness that moved ten clocks
            // on one node is one statement about that node, and repeating the
            // row ten times buries it.
            text.append("sat via ");
            int named = 0;
            for (int index = 0; index < legitimate.size(); index++) {
                JsonObject mechanism = legitimate.get(index)
                        .getAsJsonObject();
                String kind = optionalString(mechanism, "kind");
                if (seenEarlier(legitimate, index, kind)) {
                    continue;
                }
                if (named++ > 0) {
                    text.append(", ");
                }
                text.append(kind);
                int count = countOf(legitimate, kind);
                if (count > 1) {
                    text.append(" x").append(count);
                }
                String where = firstNonEmpty(optionalString(mechanism,
                        "siteId"), firstNonEmpty(optionalString(mechanism,
                        SharedStateEvidence.SESSION_LOCATION_FIELD),
                        optionalString(mechanism, "sourceKey")));
                if (!where.isEmpty()) {
                    text.append(" at ").append(where);
                    if (count > 1) {
                        text.append(" and elsewhere");
                    }
                }
                if (mechanism.has("skewMillis")) {
                    text.append(" (").append(optionalLongInteger(mechanism,
                            "skewMillis", 0L)).append("ms)");
                }
            }
        }
        if (freedoms.isEmpty()) {
            // A finding is a finding of something.  An explained witness
            // that names no kind is the case the ruling refuses, and the
            // narrative says which of the two it is rather than printing
            // "finding" over an empty mechanism list.
            text.append(findingKind == null || findingKind.isEmpty()
                    ? "; no named mechanism, so not a finding"
                    : "; finding: " + findingKind);
        } else {
            text.append("; unexplained freedom: ");
            for (int index = 0; index < freedoms.size(); index++) {
                if (index > 0) {
                    text.append(", ");
                }
                text.append(freedoms.get(index));
            }
        }
        return text.toString();
    }

    /** Whether this kind already appeared before {@code index}. */
    private static boolean seenEarlier(JsonArray rows, int index,
                                       String kind) {
        for (int earlier = 0; earlier < index; earlier++) {
            if (kind.equals(optionalString(rows.get(earlier).getAsJsonObject(),
                    "kind"))) {
                return true;
            }
        }
        return false;
    }

    private static int countOf(JsonArray rows, String kind) {
        int count = 0;
        for (JsonElement element : rows) {
            if (kind.equals(optionalString(element.getAsJsonObject(),
                    "kind"))) {
                count++;
            }
        }
        return count;
    }

    private static String firstNonEmpty(String value, String fallback) {
        return value == null || value.trim().isEmpty() ? fallback : value;
    }
}
