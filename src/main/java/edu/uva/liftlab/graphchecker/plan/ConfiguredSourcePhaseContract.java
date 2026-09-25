package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.UUID;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.required;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.text;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

/** Static hook sites of configured sources and the executions a recording
 *  observed. A declared source is ONE symbol ({@link #phaseId} is the site's
 *  alone), so the number of executions bounds nothing a replay may read. One
 *  codec: rows are the plan wire's {@link JsonObject}s. */
public final class ConfiguredSourcePhaseContract {
    public static final int SCHEMA_VERSION = 1;
    public static final String DECLARATION_FIELD =
            "configuredSourcePhaseDeclarations";
    public static final String TRACE_METHODS_FIELD =
            "configuredSourcePhaseTraceMethods";
    public static final String PLAN_FIELD = "configuredSourcePhases";
    public static final String DECLARATION_KIND =
            "CONFIGURED_SOURCE_PHASE_DECLARATION";
    public static final String DECLARATION_AUTHORITY =
            "EXACT_STATIC_SOURCE_HOOK_SITE_V1";
    public static final String PLAN_KIND = "CONFIGURED_SOURCE_PHASE";
    public static final String PLAN_AUTHORITY =
            "EXACT_RUNTIME_SOURCE_HOOK_EXECUTION_V1";
    private static final Set<String> DECLARATION_FIELDS = names(
            "schemaVersion", "kind", "authority", "phase", "sourceId",
            "fieldSignature", "declarationMethod", "declarationUnitIndex",
            "siteId");
    private static final Set<String> OCCURRENCE_FIELDS = names(
            "schemaVersion", "kind", "authority", "phase", "sourceId",
            "fieldSignature", "declarationMethod", "declarationUnitIndex",
            "siteId", "phaseId", "sourceOccurrenceId",
            "eventSeq", "invocationId",
            "runtimeDeclaredCallee", "enclosingCallIds");

    private ConfiguredSourcePhaseContract() {
    }

    /** Every phase is a mint site: one fresh symbol for one declared field. */
    public enum Phase {
        PUBLISH
    }

    public static JsonObject declaration(
            Phase phase, String sourceId, String fieldSignature,
            String method, int unitIndex) {
        String exactMethod = required(method, "declarationMethod");
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("kind", DECLARATION_KIND);
        row.addProperty("authority", DECLARATION_AUTHORITY);
        row.addProperty("phase", requiredPhase(phase).name());
        row.addProperty("sourceId", required(sourceId, "sourceId"));
        row.addProperty("fieldSignature", trimmed(fieldSignature));
        row.addProperty("declarationMethod", exactMethod);
        row.addProperty("declarationUnitIndex", unitIndex);
        row.addProperty("siteId", SiteId.of(exactMethod, unitIndex));
        validateDeclaration(row);
        return row;
    }

    public static List<Declaration> declarationsOf(JsonElement encoded) {
        if (encoded == null || encoded.isJsonNull()) {
            return Collections.emptyList();
        }
        if (!encoded.isJsonArray()) {
            throw new IllegalArgumentException(
                    DECLARATION_FIELD + " must be an array");
        }
        List<Declaration> result = new ArrayList<>();
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        DECLARATION_FIELD + " entries must be objects");
            }
            result.add(validateDeclaration(element.getAsJsonObject()));
        }
        return Collections.unmodifiableList(result);
    }

    /** Decodes an ordered runtime phase catalog: evidence of where, not a
     *  budget. */
    public static List<Occurrence> occurrencesOf(JsonElement encoded) {
        if (encoded == null || encoded.isJsonNull()) {
            return Collections.emptyList();
        }
        if (!encoded.isJsonArray()) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " must be an array");
        }
        List<Occurrence> result = new ArrayList<>();
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        PLAN_FIELD + " entries must be objects");
            }
            result.add(validateOccurrence(element.getAsJsonObject()));
        }
        validateOccurrenceSequence(result);
        return Collections.unmodifiableList(result);
    }

    private static void validateOccurrenceSequence(List<Occurrence> phases) {
        Set<Long> eventSeqs = new LinkedHashSet<>();
        Set<Long> invocationIds = new LinkedHashSet<>();
        long previousSeq = -1L;
        for (Occurrence phase : phases) {
            // The phase id repeats across executions; the execution (event seq)
            // is unique.
            if (!eventSeqs.add(phase.runtimeEventSeq())
                    || !invocationIds.add(phase.runtimeInvocationId())
                    || phase.runtimeEventSeq() <= previousSeq) {
                throw new IllegalArgumentException(PLAN_FIELD
                        + " must have unique identities in event order");
            }
            previousSeq = phase.runtimeEventSeq();
        }
    }

    public static JsonObject occurrence(
            Declaration declaration, String occurrenceId,
            long runtimeEventSeq, long runtimeInvocationId,
            String declaredCallee, Collection<Long> enclosingCallIds) {
        if (declaration == null) {
            throw new IllegalArgumentException("phase declaration is required");
        }
        String occurrence = required(occurrenceId, "occurrenceId");
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("kind", PLAN_KIND);
        row.addProperty("authority", PLAN_AUTHORITY);
        row.addProperty("phase", declaration.phase().name());
        row.addProperty("sourceId", declaration.sourceId());
        row.addProperty("fieldSignature", declaration.fieldSignature());
        row.addProperty("declarationMethod", declaration.method());
        row.addProperty("declarationUnitIndex",
                declaration.declarationUnitIndex());
        row.addProperty("siteId", declaration.siteId());
        row.addProperty("phaseId", phaseId(declaration.sourceId(),
                declaration.siteId(), declaration.phase()));
        row.addProperty("sourceOccurrenceId", occurrence);
        row.addProperty("eventSeq", runtimeEventSeq);
        row.addProperty("invocationId", runtimeInvocationId);
        row.addProperty("runtimeDeclaredCallee", required(
                declaredCallee, "runtimeDeclaredCallee"));
        JsonArray ancestry = new JsonArray();
        if (enclosingCallIds != null) {
            for (Long callId : enclosingCallIds) ancestry.add(callId);
        }
        row.add("enclosingCallIds", ancestry);
        // Built from a typed declaration; validateOccurrence is for decoded
        // rows.
        return row;
    }

    /**
     * The identity of one configured source: its site, nothing else.
     *
     * <p>One variable per replay: every execution of the site answers the same
     * valuation, so a flip moves them all. Trap: putting the reaching
     * occurrence or execution into the identity splits one site into many
     * variables, and a flip moves only one of them (hdfs-17960 lost its bug
     * this way).</p>
     */
    public static String phaseId(String sourceId, String siteId,
                                 Phase phase) {
        String identity = required(sourceId, "sourceId") + "\n"
                + required(siteId, "siteId") + "\n"
                + requiredPhase(phase).name();
        return "SOURCE_PHASE." + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    /** The VM label one configured source asks the engine for, derived from its
     *  phase. */
    public static String engineLabelForPhase(String sourcePhaseId,
                                             String sourceId) {
        return "SRC." + ArtifactIO.sha256(
                required(sourcePhaseId, "sourcePhaseId") + "\n"
                        + required(sourceId, "sourceId"));
    }

    private static Declaration validateDeclaration(JsonObject row) {
        if (!DECLARATION_FIELDS.equals(row.keySet())
                || !constants(row, DECLARATION_KIND, DECLARATION_AUTHORITY)) {
            throw new IllegalArgumentException(
                    DECLARATION_FIELD + " has an unsupported schema");
        }
        return validateHookSite(row, DECLARATION_FIELD);
    }

    private static boolean constants(JsonObject row, String kind,
                                     String authority) {
        return exactSchemaVersion(row)
                && kind.equals(text(row, "kind"))
                && authority.equals(text(row, "authority"));
    }

    private static boolean exactSchemaVersion(JsonObject row) {
        JsonElement value = row.get("schemaVersion");
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isNumber()
                && Integer.toString(SCHEMA_VERSION).equals(value.getAsString());
    }

    /** The hook-site half shared by declaration and occurrence rows. */
    private static Declaration validateHookSite(JsonObject row, String field) {
        Phase phase;
        try {
            phase = Phase.valueOf(required(text(row, "phase"), "phase"));
        } catch (RuntimeException invalid) {
            throw new IllegalArgumentException(
                    field + " has an invalid phase", invalid);
        }
        String sourceId = required(text(row, "sourceId"), "sourceId");
        String signature = text(row, "fieldSignature");
        String method = required(text(row, "declarationMethod"),
                "declarationMethod");
        int unit = exactInt(row, "declarationUnitIndex");
        if (unit < 0 || FieldPathSpec.declaredField(signature) == null
                || !SiteId.of(method, unit).equals(text(row, "siteId"))) {
            throw new IllegalArgumentException(
                    field + " has an invalid exact hook site");
        }
        return new Declaration(phase, sourceId, signature, method, unit);
    }

    private static Occurrence validateOccurrence(JsonObject row) {
        if (!OCCURRENCE_FIELDS.equals(row.keySet())
                || !constants(row, PLAN_KIND, PLAN_AUTHORITY)) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " has an unsupported schema");
        }
        Declaration declared = validateHookSite(row, PLAN_FIELD);
        String sourceOccurrenceId = required(
                text(row, "sourceOccurrenceId"), "sourceOccurrenceId");
        long eventSeq = exactLong(row, "eventSeq");
        long invocationId = exactLong(row, "invocationId");
        String declaredCallee = required(
                text(row, "runtimeDeclaredCallee"), "runtimeDeclaredCallee");
        String phaseId = required(text(row, "phaseId"), "phaseId");
        if (eventSeq <= 0L || invocationId <= 0L
                || !phaseId.equals(phaseId(declared.sourceId(),
                declared.siteId(), declared.phase()))) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " has an invalid runtime identity");
        }
        JsonElement encodedAncestry = row.get("enclosingCallIds");
        if (encodedAncestry == null || !encodedAncestry.isJsonArray()) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " requires enclosingCallIds");
        }
        List<Long> ancestry = new ArrayList<>();
        for (JsonElement value : encodedAncestry.getAsJsonArray()) {
            long callId = exactLong(value);
            if (callId <= 0L || ancestry.contains(callId)) {
                throw new IllegalArgumentException(
                        PLAN_FIELD + " has invalid enclosingCallIds");
            }
            ancestry.add(callId);
        }
        if (ancestry.isEmpty()) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " requires a non-empty enclosingCallIds");
        }
        return new Occurrence(declared, phaseId, sourceOccurrenceId,
                eventSeq, invocationId, declaredCallee, ancestry);
    }

    /** An exact integral member, or -1 when absent or another shape. */
    private static long exactLong(JsonObject row, String field) {
        return exactLong(row.get(field));
    }

    private static long exactLong(JsonElement value) {
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isNumber()
                ? value.getAsLong() : -1L;
    }

    private static int exactInt(JsonObject row, String field) {
        long value = exactLong(row, field);
        return value == (int) value ? (int) value : -1;
    }

    private static Phase requiredPhase(Phase phase) {
        if (phase == null) {
            throw new IllegalArgumentException("phase is required");
        }
        return phase;
    }

    private static Set<String> names(String... values) {
        return Collections.unmodifiableSet(
                new LinkedHashSet<>(Arrays.asList(values)));
    }

    public static final class Declaration {
        private final Phase phase;
        private final String sourceId;
        private final String fieldSignature;
        private final String method;
        private final int unitIndex;
        private final String siteId;

        private Declaration(Phase phase, String sourceId,
                            String fieldSignature, String method,
                            int unitIndex) {
            this.phase = phase;
            this.sourceId = sourceId;
            this.fieldSignature = fieldSignature;
            this.method = method;
            this.unitIndex = unitIndex;
            this.siteId = SiteId.of(
                    method, unitIndex);
        }

        public Phase phase() { return phase; }

        public String sourceId() { return sourceId; }

        public String fieldSignature() { return fieldSignature; }

        public String method() { return method; }

        public int declarationUnitIndex() { return unitIndex; }

        public String siteId() { return siteId; }

        public String identity() {
            return phase.name() + "\n" + sourceId + "\n" + siteId;
        }
    }

    public static final class Occurrence {
        private final Declaration declared;
        private final String phaseId;
        private final String sourceOccurrenceId;
        private final long runtimeEventSeq;
        private final long runtimeInvocationId;
        private final String runtimeDeclaredCallee;
        private final List<Long> enclosingCallIds;

        private Occurrence(Declaration declared, String phaseId,
                           String sourceOccurrenceId,
                           long runtimeEventSeq, long runtimeInvocationId,
                           String runtimeDeclaredCallee,
                           List<Long> enclosingCallIds) {
            this.declared = declared;
            this.phaseId = phaseId;
            this.sourceOccurrenceId = sourceOccurrenceId;
            this.runtimeEventSeq = runtimeEventSeq;
            this.runtimeInvocationId = runtimeInvocationId;
            this.runtimeDeclaredCallee = runtimeDeclaredCallee;
            this.enclosingCallIds = Collections.unmodifiableList(
                    enclosingCallIds);
        }

        public Phase phase() { return declared.phase(); }

        public String phaseId() { return phaseId; }

        public String sourceId() { return declared.sourceId(); }

        public String fieldSignature() { return declared.fieldSignature(); }

        public String sourceOccurrenceId() { return sourceOccurrenceId; }

        public String siteId() { return declared.siteId(); }

        public String declarationMethod() { return declared.method(); }

        public int declarationUnitIndex() {
            return declared.declarationUnitIndex();
        }

        public long runtimeEventSeq() { return runtimeEventSeq; }

        public long runtimeInvocationId() { return runtimeInvocationId; }

        public String runtimeDeclaredCallee() { return runtimeDeclaredCallee; }

    }
}
