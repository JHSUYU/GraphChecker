package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;

/**
 * Strict, proposal-only classification of an already enumerated symbolic-root
 * candidate set.  It cannot add candidates or directly authorize execution.
 */
public final class SymbolicRootProposal {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "LLM_SYMBOLIC_ROOT_PROPOSAL";
    public static final String AUTHORITY = "PROPOSAL_ONLY";

    private static final Pattern SHA256 = Pattern.compile("[0-9a-f]{64}");
    private static final Set<String> TOP_LEVEL_FIELDS = fields(
            "schemaVersion", "kind", "authority", "inputDigest",
            "decisions");
    private static final Set<String> DECISION_FIELDS = fields(
            "candidateId", "siteRole", "decision", "evidenceIds",
            "rootGroupId");

    public enum SiteRole {
        ROOT,
        CARRIER,
        DERIVED_STATE,
        SELECTOR,
        GUARD,
        STUTTER_NOISE,
        IRRELEVANT,
        REVIEW
    }

    public enum DecisionKind {
        SELECT_ROOT,
        RETAIN_CONTEXT,
        EXCLUDE_SYMBOLIZATION,
        REVIEW
    }

    private final JsonObject encoded;
    private final String inputDigest;
    private final List<Decision> decisions;

    private SymbolicRootProposal(JsonObject source) {
        requireExactFields(source, TOP_LEVEL_FIELDS, "symbolic-root proposal");
        if (!exactSchemaVersion(source)
                || !KIND.equals(exactString(source, "kind"))
                || !AUTHORITY.equals(exactString(source, "authority"))) {
            throw new IllegalArgumentException(
                    "symbolic-root proposal has unsupported schema");
        }
        inputDigest = exactString(source, "inputDigest");
        if (!SHA256.matcher(inputDigest).matches()) {
            throw new IllegalArgumentException(
                    "inputDigest must be a lowercase SHA-256 hex digest");
        }
        JsonElement rows = source.get("decisions");
        if (rows == null || !rows.isJsonArray()) {
            throw new IllegalArgumentException("decisions must be an array");
        }
        List<Decision> decoded = new ArrayList<>();
        Set<String> candidateIds = new LinkedHashSet<>();
        for (JsonElement element : rows.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "decisions entries must be objects");
            }
            Decision decision = new Decision(element.getAsJsonObject());
            if (!candidateIds.add(decision.candidateId())) {
                throw new IllegalArgumentException(
                        "duplicate candidateId: " + decision.candidateId());
            }
            decoded.add(decision);
        }
        decisions = Collections.unmodifiableList(decoded);
        encoded = encode(inputDigest, decisions);
    }

    public static SymbolicRootProposal decode(JsonObject source) {
        if (source == null) {
            throw new IllegalArgumentException(
                    "symbolic-root proposal is required");
        }
        return new SymbolicRootProposal(source.deepCopy());
    }

    public static SymbolicRootProposal create(
            String inputDigest, List<Decision> decisions) {
        if (decisions == null) {
            throw new IllegalArgumentException("decisions are required");
        }
        return decode(encode(inputDigest, decisions));
    }

    public String inputDigest() { return inputDigest; }

    public List<Decision> decisions() { return decisions; }

    public JsonObject json() { return encoded.deepCopy(); }

    private static JsonObject encode(
            String inputDigest, List<Decision> decisions) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        result.addProperty("authority", AUTHORITY);
        result.addProperty("inputDigest", inputDigest);
        JsonArray rows = new JsonArray();
        for (Decision decision : decisions) {
            if (decision == null) {
                throw new IllegalArgumentException(
                        "decisions must not contain null");
            }
            rows.add(decision.json());
        }
        result.add("decisions", rows);
        return result;
    }

    public static final class Decision {
        private final String candidateId;
        private final SiteRole siteRole;
        private final DecisionKind decision;
        private final List<String> evidenceIds;
        private final String rootGroupId;

        private Decision(JsonObject source) {
            requireExactFields(source, DECISION_FIELDS,
                    "symbolic-root decision");
            candidateId = exactNonemptyString(source, "candidateId");
            siteRole = enumValue(SiteRole.class,
                    exactString(source, "siteRole"), "siteRole");
            decision = enumValue(DecisionKind.class,
                    exactString(source, "decision"), "decision");
            requireConsistent(siteRole, decision);

            JsonElement evidence = source.get("evidenceIds");
            if (evidence == null || !evidence.isJsonArray()) {
                throw new IllegalArgumentException(
                        "evidenceIds must be an array");
            }
            List<String> ids = new ArrayList<>();
            for (JsonElement element : evidence.getAsJsonArray()) {
                if (!element.isJsonPrimitive()
                        || !element.getAsJsonPrimitive().isString()) {
                    throw new IllegalArgumentException(
                            "evidenceIds entries must be strings");
                }
                ids.add(exactNonempty(element.getAsString(), "evidenceIds"));
            }
            if (ids.isEmpty()) {
                throw new IllegalArgumentException(
                        "evidenceIds must not be empty");
            }
            evidenceIds = Collections.unmodifiableList(ids);

            JsonElement group = source.get("rootGroupId");
            if (group == null) {
                throw new IllegalArgumentException(
                        "rootGroupId must be explicitly null or a string");
            }
            if (group.isJsonNull()) {
                rootGroupId = null;
            } else if (group.isJsonPrimitive()
                    && group.getAsJsonPrimitive().isString()) {
                rootGroupId = exactNonempty(
                        group.getAsString(), "rootGroupId");
            } else {
                throw new IllegalArgumentException(
                        "rootGroupId must be explicitly null or a string");
            }
        }

        public static Decision create(
                String candidateId, SiteRole siteRole,
                DecisionKind decision, List<String> evidenceIds,
                String rootGroupId) {
            JsonObject row = new JsonObject();
            row.addProperty("candidateId", candidateId);
            row.addProperty("siteRole",
                    siteRole == null ? null : siteRole.name());
            row.addProperty("decision",
                    decision == null ? null : decision.name());
            JsonArray evidence = new JsonArray();
            if (evidenceIds == null) {
                throw new IllegalArgumentException(
                        "evidenceIds are required");
            }
            for (String evidenceId : evidenceIds) evidence.add(evidenceId);
            row.add("evidenceIds", evidence);
            if (rootGroupId == null) {
                row.add("rootGroupId", JsonNull.INSTANCE);
            } else {
                row.addProperty("rootGroupId", rootGroupId);
            }
            return new Decision(row);
        }

        public String candidateId() { return candidateId; }

        public SiteRole siteRole() { return siteRole; }

        public DecisionKind decision() { return decision; }

        public List<String> evidenceIds() { return evidenceIds; }

        public String rootGroupId() { return rootGroupId; }

        public boolean hasRootGroupId() { return rootGroupId != null; }

        public JsonObject json() {
            JsonObject row = new JsonObject();
            row.addProperty("candidateId", candidateId);
            row.addProperty("siteRole", siteRole.name());
            row.addProperty("decision", decision.name());
            JsonArray evidence = new JsonArray();
            for (String evidenceId : evidenceIds) evidence.add(evidenceId);
            row.add("evidenceIds", evidence);
            if (rootGroupId == null) {
                row.add("rootGroupId", JsonNull.INSTANCE);
            } else {
                row.addProperty("rootGroupId", rootGroupId);
            }
            return row;
        }
    }

    private static void requireConsistent(
            SiteRole role, DecisionKind decision) {
        DecisionKind expected;
        switch (role) {
            case ROOT:
                expected = DecisionKind.SELECT_ROOT;
                break;
            case CARRIER:
            case DERIVED_STATE:
            case SELECTOR:
            case GUARD:
                expected = DecisionKind.RETAIN_CONTEXT;
                break;
            case STUTTER_NOISE:
            case IRRELEVANT:
                expected = DecisionKind.EXCLUDE_SYMBOLIZATION;
                break;
            case REVIEW:
                expected = DecisionKind.REVIEW;
                break;
            default:
                throw new IllegalArgumentException(
                        "unsupported siteRole: " + role);
        }
        if (decision != expected) {
            throw new IllegalArgumentException("siteRole " + role
                    + " requires decision " + expected);
        }
    }

    private static boolean exactSchemaVersion(JsonObject source) {
        JsonElement value = source.get("schemaVersion");
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isNumber()
                && Integer.toString(SCHEMA_VERSION).equals(value.getAsString());
    }

    private static String exactString(JsonObject source, String field) {
        JsonElement value = source.get(field);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isString()) {
            throw new IllegalArgumentException(field + " must be a string");
        }
        return value.getAsString();
    }

    private static String exactNonemptyString(
            JsonObject source, String field) {
        return exactNonempty(exactString(source, field), field);
    }

    private static String exactNonempty(String value, String field) {
        if (value == null || value.isEmpty() || !value.equals(value.trim())) {
            throw new IllegalArgumentException(
                    field + " must be a nonempty trimmed string");
        }
        return value;
    }

    private static <E extends Enum<E>> E enumValue(
            Class<E> type, String value, String field) {
        try {
            return Enum.valueOf(type, value);
        } catch (RuntimeException invalid) {
            throw new IllegalArgumentException(
                    field + " has an unsupported value", invalid);
        }
    }

    private static void requireExactFields(
            JsonObject source, Set<String> expected, String label) {
        if (source == null || !expected.equals(source.keySet())) {
            throw new IllegalArgumentException(
                    label + " must have exact current fields " + expected);
        }
    }

    private static Set<String> fields(String... names) {
        return Collections.unmodifiableSet(
                new LinkedHashSet<>(Arrays.asList(names)));
    }
}
