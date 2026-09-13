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
    /** A clock left the window the recording anchors it in. */
    public static final String CLOCK_OUTSIDE_WINDOW = "CLOCK_OUTSIDE_WINDOW";
    /** A wall clock at a value no wall clock returns. */
    public static final String ABSURD_CLOCK_VALUE = "ABSURD_CLOCK_VALUE";
    /** A root moved and no named mechanism says what moved it. */
    public static final String UNEXPLAINED_ROOT_MOVE =
            "UNEXPLAINED_ROOT_MOVE";

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
    public static List<Freedom> compositionFreedoms(
            String degeneracy, JsonArray freeInitialArms,
            List<String> unrealizedFlows) {
        List<Freedom> freedoms = new ArrayList<>();
        if (degeneracy != null
                && degeneracy.startsWith(UNENUMERATED_ROOTS_VERDICT)) {
            freedoms.add(new Freedom(UNENUMERATED_EXISTENTIAL_ROOT, degeneracy,
                    "the existential root space was never enumerated, so a"
                            + " witness over it is free where the recording"
                            + " says nothing"));
        }
        JsonArray onPath = freeInitialArms == null ? new JsonArray()
                : freeInitialArms;
        if (onPath.size() > 0) {
            Set<String> carriers = new LinkedHashSet<>();
            for (JsonElement element : onPath) {
                if (element.isJsonObject()) {
                    carriers.add(optionalString(element.getAsJsonObject(),
                            SharedStateEvidence.SESSION_LOCATION_FIELD));
                }
            }
            freedoms.add(new Freedom(FREE_INITIAL_ARM,
                    String.join(",", carriers),
                    "the witness reads the fatal value out of the initial"
                            + " state of " + carriers.size() + " carrier(s)"
                            + " whose initial content the composition reported"
                            + " truncated"));
        }
        if (unrealizedFlows != null && !unrealizedFlows.isEmpty()) {
            freedoms.add(new Freedom(UNBOUND_WIRE_VALUE,
                    String.join(",", unrealizedFlows),
                    "no consumer boundary family of " + unrealizedFlows.size()
                            + " declared wire flow(s) reached a lowered term,"
                            + " so the value each wire carried is unbound"));
        }
        return freedoms;
    }

    /**
     * Reads one valuation's witness against the legitimate set.
     *
     * @param valuation one enumerated valuation row of the reach report
     * @param ordinal its position among the enumerated valuations
     * @param windowMillis the configured clock skew, in milliseconds
     * @param composition the freedom the composition leaves every witness
     */
    public static JsonObject classify(JsonObject valuation, int ordinal,
                                      long windowMillis,
                                      List<Freedom> composition) {
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
        JsonArray legitimate = new JsonArray();
        List<Freedom> freedoms = new ArrayList<>();
        if (!"sat".equals(status)) {
            // Only a satisfying valuation carries a witness to read.
            row.addProperty("verdict", EXPLAINED);
            row.add("mechanisms", legitimate);
            row.add("freedoms", new JsonArray());
            row.addProperty("narrative", narrative(status, legitimate,
                    freedoms));
            return row;
        }
        freedoms.addAll(composition == null
                ? Collections.<Freedom>emptyList() : composition);
        for (JsonElement element : array(valuation, "witnessMechanisms")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject mechanism = element.getAsJsonObject();
            Freedom refusal = refuse(mechanism, windowMillis);
            if (refusal == null) {
                legitimate.add(mechanism);
            } else {
                freedoms.add(refusal);
            }
        }
        row.addProperty("verdict", freedoms.isEmpty() ? EXPLAINED
                : UNEXPLAINED);
        row.add("mechanisms", legitimate);
        JsonArray freedomRows = new JsonArray();
        for (Freedom freedom : freedoms) {
            freedomRows.add(freedom.toJson());
        }
        row.add("freedoms", freedomRows);
        row.addProperty("narrative", narrative(status, legitimate, freedoms));
        return row;
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
    private static Freedom refuse(JsonObject mechanism, long windowMillis) {
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
                                    List<Freedom> freedoms) {
        if (!"sat".equals(status)) {
            return "unsat".equals(status)
                    ? "no witness: the target is unreachable under this"
                    + " valuation"
                    : "no witness: the solver returned " + firstNonEmpty(
                            status, "no answer");
        }
        StringBuilder text = new StringBuilder();
        if (legitimate.size() == 0) {
            text.append("sat with no root moved off its recorded value");
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
            text.append("; finding");
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
