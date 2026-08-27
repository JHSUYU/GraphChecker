package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.required;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Exact VM roots minted at an explicitly configured program source.
 *
 * <p>Wave 3 C1/C3: <em>every entry of a declared mint site mints its own
 * symbol</em>.  A row's identity is therefore
 * {@code (sourceId, sourceOccurrenceId, ordinal)} - the field, the activation
 * that read it, and which entry of that activation - and never the selected
 * source phase, which repeats once per occurrence.  {@code sourcePhaseId}
 * stays on the row as the mint <em>site</em> it was observed at; it no longer
 * decides identity.</p>
 */
public final class SymbolicSourceEvidence {
    public static final String FIELD = "symbolicSourceEvidence";
    /** Member the C2 free roots travel in on a result or summary. */
    public static final String FREE_SYMBOLS_FIELD = "freeSymbols";
    public static final String KIND = "CONFIGURED_SYMBOLIC_SOURCE_FIELD";
    public static final String AUTHORITY = "VM_EXACT_SOURCE_PHASE_FIELD_V2";
    public static final int SCHEMA_VERSION = 2;
    /** Per-(activation, site) entry number of this mint; 1-based, required. */
    public static final String ORDINAL = "ordinal";
    /**
     * Whether this read reused an expression the VM had already propagated.
     * A reused row is not a new root: it references the roots its expression
     * already names.  Required: a row that states neither is not a mint this
     * composer can name.
     */
    public static final String REUSED = "reused";
    /** The runtime's own name for this root, when it published one. */
    public static final String SYMBOL = "symbol";
    private static final Pattern FIELD_SIGNATURE = Pattern.compile(
            "^<[^:]+:\\s+([^()<>\\s]+)\\s+[^()<>\\s]+>(?:#.*)?$");

    private SymbolicSourceEvidence() {
    }

    /** Stable semantic VM label shared by seed and every source replay. */
    public static String engineLabelForPhase(String sourcePhaseId,
                                             String sourceId) {
        return "SRC." + CanonicalJson.sha256(
                requiredPhaseId(sourcePhaseId) + "\n"
                        + required(sourceId, "sourceId"));
    }

    /**
     * Whether one already-propagated expression can honestly be NAMED as
     * the read of one declared source field.
     *
     * <p>A propagated COMPOUND is not nameable: it is a computation over
     * roots that live elsewhere, so binding a writable program source to it
     * would name a root that does not exist.  A bare VM root symbol is: the
     * field carries exactly that symbol and nothing else, so the declared
     * source is one honest name for it.  The test is the one a fresh mint
     * must already pass - {@link #event} raises the same two - so a named
     * read and a minted read publish the same shape, and a read that fails
     * either check files nothing.</p>
     */
    public static boolean namesOneBareVmRoot(String fieldSignature,
                                             JsonElement expression) {
        try {
            JsonObject symbolic = exactSymbol(expression);
            requireDeclaredFieldType(fieldSignature,
                    string(symbolic, "_java_type"));
            // Only the VM's own mint prefix is a root; every other leaf is
            // a fold or a literal this ledger never names.
            return string(symbolic, "_exp").startsWith("M_");
        } catch (RuntimeException notOneRoot) {
            return false;
        }
    }

    /**
     * One mint, with the entry number and root name the runtime published.
     *
     * @param ordinal per-(activation, site) entry count, 1-based
     * @param reused  whether the VM had already propagated an expression here
     * @param symbol  the runtime's own root name, or "" to let the Composer
     *                name the root
     */
    public static JsonObject event(String sourcePhaseId, String sourceId,
                                   String occurrenceId,
                                   String fieldSignature,
                                   JsonElement expression,
                                   int ordinal, boolean reused,
                                   String symbol) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("kind", KIND);
        row.addProperty("authority", AUTHORITY);
        row.addProperty("sourcePhaseId", requiredPhaseId(sourcePhaseId));
        row.addProperty("sourceId", required(sourceId, "sourceId"));
        row.addProperty("sourceOccurrenceId", required(occurrenceId,
                "sourceOccurrenceId"));
        row.addProperty("fieldSignature", required(fieldSignature,
                "fieldSignature"));
        JsonObject symbolic = exactSymbol(expression);
        requireDeclaredFieldType(fieldSignature,
                string(symbolic, "_java_type"));
        row.addProperty("rawSymbol", string(symbolic, "_exp"));
        row.addProperty("javaType", string(symbolic, "_java_type"));
        row.add("expression", symbolic.deepCopy());
        if (ordinal < 1) {
            throw new IllegalArgumentException(
                    FIELD + " requires a 1-based mint ordinal");
        }
        row.addProperty(ORDINAL, ordinal);
        row.addProperty(REUSED, reused);
        if (symbol != null && !symbol.trim().isEmpty()) {
            row.addProperty(SYMBOL, symbol.trim());
        }
        return row;
    }

    /** The 1-based entry number one row states. */
    public static int ordinalOf(JsonObject event) {
        int ordinal = JsonFields.integer(event, ORDINAL, 0);
        if (ordinal < 1) {
            throw new IllegalArgumentException(
                    FIELD + " states no mint ordinal");
        }
        return ordinal;
    }

    /** Whether this row reuses an already-propagated expression. */
    public static boolean isReused(JsonObject event) {
        if (!event.has(REUSED)) {
            throw new IllegalArgumentException(
                    FIELD + " states no reuse");
        }
        return JsonFields.bool(event, REUSED, false);
    }

    public static void writeTo(JsonObject owner, List<JsonObject> events) {
        if (owner == null || events == null || events.isEmpty()) return;
        JsonArray encoded = new JsonArray();
        for (JsonObject event : events) encoded.add(validate(event));
        owner.add(FIELD, encoded);
    }

    public static List<JsonObject> eventsOf(JsonObject owner) {
        if (owner == null) return Collections.emptyList();
        List<JsonObject> result = new ArrayList<>();
        Set<String> identities = new LinkedHashSet<>();
        for (JsonElement element : array(owner, FIELD)) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        FIELD + " entries must be objects");
            }
            JsonObject event = validate(element.getAsJsonObject());
            // Wave 3 C1: one owner legitimately holds many mints of one
            // site - one per entry.  What may not repeat is one entry.
            String identity = identity(event);
            if (!identities.add(identity)) {
                throw new IllegalArgumentException(
                        FIELD + " repeats one source mint: " + identity);
            }
            result.add(event);
        }
        return result;
    }

    /**
     * Canonical identity of one mint: the field, the activation that read it
     * and which entry of that activation.  Shared by every replay of the same
     * entry, distinct for every other entry of the same site.
     */
    public static String identity(JsonObject event) {
        JsonObject valid = validate(event);
        return string(valid, "sourceId") + "\n"
                + string(valid, "sourceOccurrenceId") + "\n#"
                + ordinalOf(valid);
    }

    /**
     * Builds the one-to-one raw-symbol registry consumed by the Composer.
     * A collision is evidence corruption, never a reason to pick one row.
     */
    public static Map<String, String> rawSymbolIdentities(
            Iterable<JsonObject> owners) {
        Map<String, String> result = new LinkedHashMap<>();
        if (owners == null) return result;
        for (JsonObject owner : owners) {
            for (JsonObject event : eventsOf(owner)) {
                // A reused read is not a root: its expression already names
                // the roots it was propagated from (wave 3 C2).
                if (isReused(event)) continue;
                String raw = string(event, "rawSymbol");
                String identity = identity(event);
                String priorIdentity = result.putIfAbsent(raw, identity);
                if (priorIdentity != null
                        && !priorIdentity.equals(identity)) {
                    throw new IllegalArgumentException(
                            "one VM symbol names two configured sources: "
                                    + raw);
                }
            }
        }
        return Collections.unmodifiableMap(result);
    }

    /**
     * The C2 free roots one raw result or imported summary published.
     *
     * <p>A free root is a coverage <em>report</em>, and a composition that
     * carries some is still a composition (the owner's explicit fail-open) -
     * but the census itself is not optional: a producer that found none says
     * so with an empty array, so silence stays distinguishable from "this
     * producer does not report".</p>
     */
    public static List<JsonObject> freeSymbolsOf(JsonObject owner) {
        List<JsonObject> rows = new ArrayList<>();
        if (owner == null) return rows;
        if (!owner.has(FREE_SYMBOLS_FIELD)) {
            throw new IllegalArgumentException(
                    FREE_SYMBOLS_FIELD + " is not stated");
        }
        for (JsonElement element : array(owner, FREE_SYMBOLS_FIELD)) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if (string(row, "symbol").isEmpty()) continue;
            rows.add(row.deepCopy());
        }
        return rows;
    }

    private static JsonObject validate(JsonObject event) {
        if (event == null || !hasOnlyKnownMembers(event)
                || !event.keySet().containsAll(REQUIRED_MEMBERS)) {
            throw new IllegalArgumentException(
                    FIELD + " has an incomplete schema");
        }
        int version = JsonFields.exactInteger(event, "schemaVersion", -1);
        if (version != SCHEMA_VERSION) {
            throw new IllegalArgumentException(
                    FIELD + " has unsupported schemaVersion");
        }
        if (!KIND.equals(string(event, "kind"))
                || !AUTHORITY.equals(string(event, "authority"))) {
            throw new IllegalArgumentException(
                    FIELD + " has unsupported authority");
        }
        required(string(event, "sourceId"), "sourceId");
        requiredPhaseId(string(event, "sourcePhaseId"));
        required(string(event, "sourceOccurrenceId"),
                "sourceOccurrenceId");
        required(string(event, "fieldSignature"), "fieldSignature");
        JsonObject expression = exactSymbol(event.get("expression"));
        requireDeclaredFieldType(string(event, "fieldSignature"),
                string(expression, "_java_type"));
        String raw = string(event, "rawSymbol");
        String phaseMarker = "_field_" + engineLabelForPhase(
                string(event, "sourcePhaseId"),
                string(event, "sourceId")) + "_";
        // A mint's own root carries this phase's label, because this phase
        // asked the VM for it.  A NAMED root cannot: it was minted somewhere
        // else and only travelled here, and the row says so.  So the phase
        // marker is required of a mint and never of a naming - what both owe
        // is that the metadata is the expression's own.
        boolean named = JsonFields.bool(event, REUSED, false);
        if (!raw.equals(string(expression, "_exp"))
                || !string(event, "javaType").equals(
                string(expression, "_java_type"))
                || !raw.startsWith("M_")
                || !named && !raw.contains(phaseMarker)) {
            throw new IllegalArgumentException(
                    FIELD + " symbol metadata differs from expression");
        }
        return event.deepCopy();
    }

    private static final Set<String> REQUIRED_MEMBERS =
            new LinkedHashSet<>(java.util.Arrays.asList("schemaVersion",
                    "kind", "authority", "sourcePhaseId", "sourceId",
                    "sourceOccurrenceId", "fieldSignature", "rawSymbol",
                    "javaType", "expression", ORDINAL, REUSED));
    private static final Set<String> OPTIONAL_MEMBERS =
            new LinkedHashSet<>(java.util.Arrays.asList(SYMBOL));

    private static boolean hasOnlyKnownMembers(JsonObject event) {
        for (Map.Entry<String, JsonElement> member : event.entrySet()) {
            if (!REQUIRED_MEMBERS.contains(member.getKey())
                    && !OPTIONAL_MEMBERS.contains(member.getKey())) {
                return false;
            }
        }
        return true;
    }

    private static JsonObject exactSymbol(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) {
            throw new IllegalArgumentException(
                    FIELD + " expression must be an object");
        }
        JsonObject symbolic = expression.getAsJsonObject();
        String type = string(symbolic, "_type");
        String raw = string(symbolic, "_exp");
        String javaType = string(symbolic, "_java_type");
        if (!"SymbolExpression".equals(type)
                || raw.isEmpty() || javaType.isEmpty()
                || raw.startsWith("Y_") || raw.startsWith("N_")) {
            throw new IllegalArgumentException(
                    FIELD + " must carry one non-constant VM symbol");
        }
        if (SharedStateEvidence.containsVmSerializationTruncation(symbolic)) {
            throw new IllegalArgumentException(
                    FIELD + " contains a truncated VM expression");
        }
        return symbolic;
    }

    /** The VM symbol must have the exact declared field type. */
    private static void requireDeclaredFieldType(String fieldSignature,
                                                 String expressionJavaType) {
        Matcher field = FIELD_SIGNATURE.matcher(required(fieldSignature,
                "fieldSignature"));
        if (!field.matches()) {
            throw new IllegalArgumentException(
                    FIELD + " has a malformed exact field signature");
        }
        String declared = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                field.group(1));
        String observed = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                expressionJavaType);
        if (!declared.equals(observed)) {
            throw new IllegalArgumentException(
                    FIELD + " field type differs from VM expression: "
                            + declared + " != " + observed);
        }
    }

    private static String requiredPhaseId(String value) {
        String result = required(value, "sourcePhaseId");
        if (!result.startsWith("SOURCE_PHASE.")) {
            throw new IllegalArgumentException(
                    "sourcePhaseId must name an exact source phase");
        }
        return result;
    }
}
