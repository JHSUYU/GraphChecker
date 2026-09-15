package edu.uva.liftlab.graphchecker.d3.plan;

import edu.uva.liftlab.graphchecker.d3.smt.CanonicalJson;

import edu.uva.liftlab.graphchecker.d3.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.d3.smt.JsonFields;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.required;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.shallowCopy;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;

/**
 * Exact VM roots minted at an explicitly configured program source.
 *
 * <p>An entry mints a root only when its value does not already carry a
 * propagated expression. A minted row's identity is
 * {@code (sourceId, sourceOccurrenceId, ordinal)} - the field, the activation
 * that read it, and which entry of that activation - and never the selected
 * source phase, which repeats once per occurrence.  {@code sourcePhaseId}
 * stays on the row as the mint <em>site</em> it was observed at; it no longer
 * decides identity.</p>
 */
public final class SymbolicSourceEvidence {
    public static final String FIELD = "symbolicSourceEvidence";
    public static final String KIND = "CONFIGURED_SYMBOLIC_SOURCE_FIELD";
    public static final String AUTHORITY = "VM_EXACT_SOURCE_PHASE_FIELD_V2";
    public static final String MANUAL_KIND = "MANUAL_SYMBOLIC_INPUT";
    public static final String MANUAL_AUTHORITY =
            "PLANNED_MANUAL_SYMBOLIZATION_V1";
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
    /**
     * What the field actually held when this mint read it.
     *
     * <p>A configured source is a root the recording <em>observed</em> rather
     * than one the experiment planted, so its recorded value is the only
     * thing that says which polarity the run had.  Without it a reader has to
     * guess, and guessing inverts every statement about which value reached
     * the target: HDFS-17960's epoch-1 NameNode records
     * {@code snapshot.deletion.ordered = false}, and a default of
     * {@code true} turns a witness that reproduces the recorded failure into
     * a counterfactual that flips it.</p>
     *
     * <p>Optional, and honestly so: a replay that overwrote the field with a
     * model assignment before reading it observed the model's value and not
     * the recording's, so it states none.</p>
     */
    public static final String RECORDED_VALUE = "recordedValue";
    /**
     * The external call whose return this root was minted from.
     *
     * <p>The declaration, not an inference: the plan names the callee on
     * the port that mints the root, so a cell minted through the clock hook
     * says so here and the composer needs no site heuristic to recognise a
     * wall clock.</p>
     */
    public static final String DECLARED_CALLEE = "declaredCallee";
    /**
     * What the execution that minted this root read there.
     *
     * <p>Beside {@link #RECORDED_VALUE}, not instead of it.  For every root
     * but a clock the two are the same value; a clock is the one root each
     * execution genuinely reads differently, so the window centred on the
     * recording and the window centred on this path's own instant are two
     * different windows and each needs its own member.</p>
     */
    public static final String OBSERVED_VALUE = "observedValue";
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
        return event(sourcePhaseId, sourceId, occurrenceId, fieldSignature,
                expression, ordinal, reused, symbol, null);
    }

    /**
     * One mint, with the concrete value the field held when it was read.
     *
     * @param recordedValue what the field held at this mint, or null/"" when
     *                      the runtime could not state it -- a replay that
     *                      had already written a model assignment into the
     *                      field reads the model's value, not the
     *                      recording's, and must say nothing rather than
     *                      publish the model's value as a recording
     */
    public static JsonObject event(String sourcePhaseId, String sourceId,
                                   String occurrenceId,
                                   String fieldSignature,
                                   JsonElement expression,
                                   int ordinal, boolean reused,
                                   String symbol, String recordedValue) {
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
                optionalString(symbolic, "_java_type"));
        row.addProperty("rawSymbol", optionalString(symbolic, "_exp"));
        row.addProperty("javaType", optionalString(symbolic, "_java_type"));
        row.add("expression", symbolic);
        if (ordinal < 1) {
            throw new IllegalArgumentException(
                    FIELD + " requires a 1-based mint ordinal");
        }
        row.addProperty(ORDINAL, ordinal);
        row.addProperty(REUSED, reused);
        if (symbol != null && !symbol.trim().isEmpty()) {
            row.addProperty(SYMBOL, symbol.trim());
        }
        if (recordedValue != null && !recordedValue.isEmpty()) {
            row.addProperty(RECORDED_VALUE, recordedValue);
        }
        return row;
    }

    /** What the field held at this mint, or "" when the row states none. */
    public static String recordedValueOf(JsonObject event) {
        return event == null ? "" : optionalString(event, RECORDED_VALUE);
    }

    /** One root minted by an explicit task {@code SYMBOLIC} input action. */
    public static JsonObject manualEvent(String portId, String occurrenceId,
                                         String fieldSignature,
                                         String javaType, String rawSymbol,
                                         String sourceIdentity) {
        return manualEvent(portId, occurrenceId, fieldSignature, javaType,
                rawSymbol, sourceIdentity, "", "", -1L, "", "");
    }

    /**
     * The same root, with what the mint row states about the read.
     *
     * <p>{@code declaredCallee} is the hook's own declaration: a cell
     * minted through the clock hook is a wall-clock read by construction,
     * and carrying the callee here is what lets the composer window that
     * root instead of pinning it -- without any reader inferring a clock
     * from a site name.  {@code recordedValue} is what the recording read
     * there, which is the value such a window is centred on.</p>
     */
    public static JsonObject manualEvent(String portId, String occurrenceId,
                                         String fieldSignature,
                                         String javaType, String rawSymbol,
                                         String sourceIdentity,
                                         String declaredCallee,
                                         String siteId, long eventSeq,
                                         String recordedValue,
                                         String observedValue) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", required(javaType,
                "javaType"));
        expression.addProperty("_exp", required(rawSymbol, "rawSymbol"));
        exactSymbol(expression);
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("kind", MANUAL_KIND);
        row.addProperty("authority", MANUAL_AUTHORITY);
        row.addProperty("portId", required(portId, "portId"));
        row.addProperty("sourceOccurrenceId", required(occurrenceId,
                "sourceOccurrenceId"));
        // A manual input's identity IS what every reader calls its field:
        // there is no Java field behind a hook's mint, and a row that left
        // the member off was refused as a malformed materialization by the
        // one reader that asks for it.  Stated here, once, rather than by a
        // second builder that filled it in.
        row.addProperty("fieldSignature",
                fieldSignature == null || fieldSignature.trim().isEmpty()
                        ? required(sourceIdentity, "sourceIdentity").trim()
                        : fieldSignature.trim());
        row.addProperty("rawSymbol", rawSymbol);
        row.addProperty("javaType", javaType);
        row.add("expression", expression);
        row.addProperty("sourceIdentity", required(sourceIdentity,
                "sourceIdentity"));
        // The mint row IS the declaration every reader uses, so it states
        // the identity under all three names a materialization asks for
        // rather than letting a second builder invent them from the symbol.
        // The node is the occurrence's own prefix; an address without a
        // region is the node itself.
        row.addProperty("sourcePhaseId", sourceIdentity.trim());
        row.addProperty("sourceId", sourceIdentity.trim());
        row.addProperty("sourceKey", nodeOf(occurrenceId));
        if (declaredCallee != null && !declaredCallee.trim().isEmpty()) {
            row.addProperty(DECLARED_CALLEE, declaredCallee.trim());
        }
        if (siteId != null && !siteId.trim().isEmpty()) {
            row.addProperty("siteId", siteId.trim());
        }
        if (eventSeq >= 0L) {
            row.addProperty("eventSeq", eventSeq);
        }
        if (recordedValue != null && !recordedValue.trim().isEmpty()) {
            row.addProperty(RECORDED_VALUE, recordedValue.trim());
        }
        if (observedValue != null && !observedValue.trim().isEmpty()) {
            row.addProperty(OBSERVED_VALUE, observedValue.trim());
        }
        return validate(row);
    }

    /** What this execution read at the mint, or "" when it states none. */
    public static String observedValueOf(JsonObject event) {
        return event == null ? "" : optionalString(event, OBSERVED_VALUE);
    }

    /**
     * One manual mint row as every reader declares it.
     *
     * <p>The row IS the declaration -- it states the port, the callee the
     * hook declared and both readings -- but a row written before those
     * members existed states its identity only as {@code sourceIdentity}.
     * Completing it here keeps that knowledge in the class that owns the
     * row's shape: the composer used to rebuild a declaration instead, and
     * the rebuilt row, installed over the evidence, lost the port and the
     * callee, so no composition ever listed a clock read.</p>
     */
    public static JsonObject manualDeclaration(JsonObject row) {
        if (row == null) return null;
        // The VM's own observation spells the identity "symbol" and the
        // address "occurrenceId"; a row this class minted spells them
        // "sourceIdentity" and "sourceOccurrenceId".  Both are the same
        // statement, and this is the one place that says so.
        String identity = optionalString(row, "sourceIdentity");
        if (identity.isEmpty()) identity = optionalString(row, SYMBOL);
        if (identity.isEmpty()) return null;
        JsonObject declaration = shallowCopy(row);
        String occurrence = optionalString(row, "sourceOccurrenceId");
        if (occurrence.isEmpty()) {
            occurrence = optionalString(row, "occurrenceId");
            stateIfAbsent(declaration, "sourceOccurrenceId", occurrence);
        }
        stateIfAbsent(declaration, "sourcePhaseId", identity);
        stateIfAbsent(declaration, "sourceId", identity);
        stateIfAbsent(declaration, "fieldSignature", identity);
        stateIfAbsent(declaration, "sourceKey", nodeOf(occurrence));
        return declaration;
    }

    private static void stateIfAbsent(JsonObject row, String member,
                                      String value) {
        if (optionalString(row, member).isEmpty() && !value.isEmpty()) {
            row.addProperty(member, value);
        }
    }

    /** The call whose return this root was minted from, or "". */
    public static String declaredCalleeOf(JsonObject event) {
        return event == null ? "" : optionalString(event, DECLARED_CALLEE);
    }

    public static boolean isManual(JsonObject event) {
        return event != null && MANUAL_KIND.equals(optionalString(event, "kind"));
    }

    /** The 1-based entry number one row states. */
    public static int ordinalOf(JsonObject event) {
        int ordinal = JsonFields.optionalInteger(event, ORDINAL, 0);
        if (ordinal < 1) {
            throw new IllegalArgumentException(
                    FIELD + " states no mint ordinal");
        }
        return ordinal;
    }

    /** Whether this row reuses an already-propagated expression. */
    public static boolean isReused(JsonObject event) {
        if (isManual(event)) return false;
        if (!event.has(REUSED)) {
            throw new IllegalArgumentException(
                    FIELD + " states no reuse");
        }
        return JsonFields.optionalBool(event, REUSED, false);
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
        if (isManual(valid)) return optionalString(valid, "sourceIdentity");
        return optionalString(valid, "sourceId") + "\n"
                + optionalString(valid, "sourceOccurrenceId") + "\n#"
                + ordinalOf(valid);
    }

    /**
     * Builds the one-to-one raw-symbol registry consumed by the Composer.
     * A collision is evidence corruption, never a reason to pick one row.
     */

    /** One VM root may be observed again when the same field object survives
     * into another activation.  The raw root is then the identity authority;
     * occurrence and ordinal describe observations, not new roots. */
    private static boolean sameConfiguredSource(JsonObject left,
                                                JsonObject right) {
        return left != null && right != null
                && !isManual(left) && !isManual(right)
                && optionalString(left, "sourceId").equals(optionalString(right,
                "sourceId"))
                && optionalString(left, "sourcePhaseId").equals(optionalString(right,
                "sourcePhaseId"))
                && optionalString(left, "fieldSignature").equals(optionalString(right,
                "fieldSignature"))
                && optionalString(left, "javaType").equals(optionalString(right,
                "javaType"));
    }

    private static JsonObject validate(JsonObject event) {
        if (event == null || !hasOnlyKnownMembers(event)) {
            throw new IllegalArgumentException(
                    FIELD + " has an incomplete schema");
        }
        int version = JsonFields.exactInteger(event, "schemaVersion", -1);
        if (version != SCHEMA_VERSION) {
            throw new IllegalArgumentException(
                    FIELD + " has unsupported schemaVersion");
        }
        if (MANUAL_KIND.equals(optionalString(event, "kind"))) {
            return validateManual(event);
        }
        if (!event.keySet().containsAll(REQUIRED_MEMBERS)
                || !KIND.equals(optionalString(event, "kind"))
                || !AUTHORITY.equals(optionalString(event, "authority"))) {
            throw new IllegalArgumentException(
                    FIELD + " has unsupported authority");
        }
        required(optionalString(event, "sourceId"), "sourceId");
        requiredPhaseId(optionalString(event, "sourcePhaseId"));
        required(optionalString(event, "sourceOccurrenceId"),
                "sourceOccurrenceId");
        required(optionalString(event, "fieldSignature"), "fieldSignature");
        JsonObject expression = exactSymbol(event.get("expression"));
        requireDeclaredFieldType(optionalString(event, "fieldSignature"),
                optionalString(expression, "_java_type"));
        String raw = optionalString(event, "rawSymbol");
        String phaseMarker = "_field_" + engineLabelForPhase(
                optionalString(event, "sourcePhaseId"),
                optionalString(event, "sourceId")) + "_";
        // A mint's own root carries this phase's label, because this phase
        // asked the VM for it.  A NAMED root cannot: it was minted somewhere
        // else and only travelled here, and the row says so.  So the phase
        // marker is required of a mint and never of a naming - what both owe
        // is that the metadata is the expression's own.
        boolean named = JsonFields.optionalBool(event, REUSED, false);
        if (!raw.equals(optionalString(expression, "_exp"))
                || !optionalString(event, "javaType").equals(
                optionalString(expression, "_java_type"))
                || !raw.startsWith("M_")
                || !named && !raw.contains(phaseMarker)) {
            throw new IllegalArgumentException(
                    FIELD + " symbol metadata differs from expression");
        }
        return shallowCopy(event);
    }

    private static JsonObject validateManual(JsonObject event) {
        if (!event.keySet().containsAll(MANUAL_REQUIRED_MEMBERS)
                || !MANUAL_AUTHORITY.equals(optionalString(event, "authority"))) {
            throw new IllegalArgumentException(
                    FIELD + " has unsupported manual root authority");
        }
        required(optionalString(event, "portId"), "portId");
        required(optionalString(event, "sourceOccurrenceId"),
                "sourceOccurrenceId");
        required(optionalString(event, "sourceIdentity"), "sourceIdentity");
        JsonObject expression = exactSymbol(event.get("expression"));
        if (!optionalString(event, "rawSymbol").equals(optionalString(expression, "_exp"))
                || !optionalString(event, "javaType").equals(
                optionalString(expression, "_java_type"))) {
            throw new IllegalArgumentException(
                    FIELD + " manual root metadata differs from expression");
        }
        return shallowCopy(event);
    }

    private static final Set<String> REQUIRED_MEMBERS =
            new LinkedHashSet<>(java.util.Arrays.asList("schemaVersion",
                    "kind", "authority", "sourcePhaseId", "sourceId",
                    "sourceOccurrenceId", "fieldSignature", "rawSymbol",
                    "javaType", "expression", ORDINAL, REUSED));
    private static final Set<String> OPTIONAL_MEMBERS =
            new LinkedHashSet<>(java.util.Arrays.asList(SYMBOL, "portId",
                    "sourceIdentity", RECORDED_VALUE, OBSERVED_VALUE,
                    DECLARED_CALLEE, "siteId", "eventSeq", "sourceKey"));
    private static final Set<String> MANUAL_REQUIRED_MEMBERS =
            new LinkedHashSet<>(java.util.Arrays.asList("schemaVersion",
                    "kind", "authority", "portId", "sourceOccurrenceId",
                    "rawSymbol", "javaType", "expression",
                    "sourceIdentity"));

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
        String type = optionalString(symbolic, "_type");
        String raw = optionalString(symbolic, "_exp");
        String javaType = optionalString(symbolic, "_java_type");
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

    /**
     * The node and epoch an occurrence ran on, read through the address
     * grammar rather than off the id's text; an id that names no address is
     * the node itself.
     */
    private static String nodeOf(String occurrenceId) {
        String id = occurrenceId == null ? "" : occurrenceId.trim();
        OccurrenceAddress address = OccurrenceAddress.parse(id);
        return address.isNamed() ? address.sourceKey() : id;
    }

}
