package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.smt.CanonicalJson;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

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

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.required;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.shallowCopy;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

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
        return "SRC." + ArtifactIO.sha256(
                requiredPhaseId(sourcePhaseId) + "\n"
                        + required(sourceId, "sourceId"));
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

    public static void writeTo(JsonObject owner, List<JsonObject> events) {
        if (owner == null || events == null || events.isEmpty()) return;
        JsonArray encoded = new JsonArray();
        for (JsonObject event : events) encoded.add(validate(event));
        owner.add(FIELD, encoded);
    }

    /**
     * Builds the one-to-one raw-symbol registry consumed by the Composer.
     * A collision is evidence corruption, never a reason to pick one row.
     */

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

}
