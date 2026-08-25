package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.nio.charset.StandardCharsets;
import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;

/**
 * Static hook sites and their exact dynamic executions for configured sources.
 *
 * <p>A region occurrence may execute one source hook many times.  The static
 * declaration names the hook site; the occurrence row names one execution of
 * that site.  Keeping the two separate prevents a long-lived service-loop task
 * from being treated as if it published one timeless source version.</p>
 */
public final class ConfiguredSourcePhaseContract {
    public static final int SCHEMA_VERSION = 1;
    public static final String DECLARATION_FIELD =
            "configuredSourcePhaseDeclarations";
    public static final String TRACE_METHODS_FIELD =
            "configuredSourcePhaseTraceMethods";
    public static final String PLAN_FIELD = "configuredSourcePhases";
    /** Exact task-relevant subsequence within the replay-call phase catalog. */
    public static final String SELECTED_PLAN_FIELD =
            "selectedConfiguredSourcePhaseIds";
    public static final String DECLARATION_KIND =
            "CONFIGURED_SOURCE_PHASE_DECLARATION";
    public static final String DECLARATION_AUTHORITY =
            "EXACT_STATIC_SOURCE_HOOK_SITE_V1";
    public static final String PLAN_KIND = "CONFIGURED_SOURCE_PHASE";
    public static final String PLAN_AUTHORITY =
            "EXACT_RUNTIME_SOURCE_HOOK_EXECUTION_V1";
    private static final Set<String> OCCURRENCE_FIELDS =
            Collections.unmodifiableSet(new LinkedHashSet<>(java.util.Arrays
                    .asList("schemaVersion", "kind", "authority", "phase",
                            "sourceId", "fieldSignature",
                            "declarationMethod", "declarationUnitIndex",
                            "siteId", "phaseId", "phaseKind",
                            "sourceOccurrenceId", "baselineOrdinal",
                            "eventSeq", "ownerCallId", "invocationId",
                            "runtimeDeclaredCallee", "enclosingCallIds")));

    private ConfiguredSourcePhaseContract() {
    }

    public enum Phase {
        PUBLISH,
        CONSUME
    }

    public static Map<String, Object> declaration(
            Phase phase, String sourceId, String fieldSignature,
            String method, int unitIndex) {
        String exactMethod = required(method, "declarationMethod");
        if (unitIndex < 0) {
            throw new IllegalArgumentException(
                    "declarationUnitIndex must be non-negative");
        }
        String field = normalized(fieldSignature);
        if (phase == Phase.PUBLISH
                && FieldPathSpec.declaredField(field) == null) {
            throw new IllegalArgumentException(
                    "publish phase requires an exact declared field");
        }
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", SCHEMA_VERSION);
        row.put("kind", DECLARATION_KIND);
        row.put("authority", DECLARATION_AUTHORITY);
        row.put("phase", requiredPhase(phase).name());
        row.put("sourceId", required(sourceId, "sourceId"));
        row.put("fieldSignature", field);
        row.put("declarationMethod", exactMethod);
        row.put("declarationUnitIndex", unitIndex);
        row.put("siteId", siteId(exactMethod, unitIndex));
        return validateDeclaration(row).json();
    }

    public static List<Declaration> declarationsOf(Object encoded) {
        if (encoded == null) return Collections.emptyList();
        if (!(encoded instanceof Collection<?>)) {
            throw new IllegalArgumentException(
                    DECLARATION_FIELD + " must be a collection");
        }
        List<Declaration> result = new ArrayList<>();
        for (Object element : (Collection<?>) encoded) {
            if (!(element instanceof Map<?, ?>)) {
                throw new IllegalArgumentException(
                        DECLARATION_FIELD + " entries must be objects");
            }
            result.add(validateDeclaration(stringMap((Map<?, ?>) element)));
        }
        return Collections.unmodifiableList(result);
    }

    public static List<Occurrence> occurrencesOf(Object encoded) {
        return occurrencesOf(encoded, false);
    }

    /**
     * Validates the exact phases a task must observe inside its broader
     * replay-call catalog. Known catalog phases outside this subsequence are
     * no-op landmarks; an execution outside the catalog is a topology change.
     */
    public static List<String> selectedPhaseIdsOf(
            JsonObject task, List<Occurrence> catalog) {
        if (task == null) return Collections.emptyList();
        JsonArray encoded;
        if (!task.has(SELECTED_PLAN_FIELD)) {
            encoded = new JsonArray();
        } else if (!task.get(SELECTED_PLAN_FIELD).isJsonArray()) {
            throw new IllegalArgumentException(
                    SELECTED_PLAN_FIELD + " must be an array");
        } else {
            encoded = task.getAsJsonArray(SELECTED_PLAN_FIELD);
        }
        Map<String, Integer> positions = new LinkedHashMap<>();
        List<Occurrence> phases = catalog == null
                ? Collections.<Occurrence>emptyList() : catalog;
        for (int index = 0; index < phases.size(); index++) {
            positions.put(phases.get(index).phaseId(), index);
        }
        List<String> selected = new ArrayList<>();
        Set<String> unique = new LinkedHashSet<>();
        int previous = -1;
        for (JsonElement element : encoded) {
            if (!element.isJsonPrimitive()
                    || !element.getAsJsonPrimitive().isString()) {
                throw new IllegalArgumentException(SELECTED_PLAN_FIELD
                        + " entries must be phase-id strings");
            }
            String phaseId = required(element.getAsString(), "phaseId");
            Integer position = positions.get(phaseId);
            if (position == null || !unique.add(phaseId)
                    || position <= previous) {
                throw new IllegalArgumentException(SELECTED_PLAN_FIELD
                        + " must be a unique ordered catalog subsequence");
            }
            previous = position;
            selected.add(phaseId);
        }
        return Collections.unmodifiableList(selected);
    }

    /**
     * Decodes an ordered runtime phase catalog.
     *
     * @param completeOccurrence whether every execution of each exact site
     *     must be present. Region-plan rows pass {@code true}; a scheduled
     *     task may carry a strict subsequence and passes {@code false}.
     */
    public static List<Occurrence> occurrencesOf(
            Object encoded, boolean completeOccurrence) {
        if (encoded == null) return Collections.emptyList();
        List<Occurrence> result = new ArrayList<>();
        if (encoded instanceof JsonArray) {
            for (JsonElement element : (JsonArray) encoded) {
                if (!element.isJsonObject()) {
                    throw new IllegalArgumentException(
                            PLAN_FIELD + " entries must be objects");
                }
                result.add(validateOccurrence(jsonMap(
                        element.getAsJsonObject())));
            }
        } else if (!(encoded instanceof Collection<?>)) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " must be a collection");
        } else {
            for (Object element : (Collection<?>) encoded) {
                if (!(element instanceof Map<?, ?>)) {
                    throw new IllegalArgumentException(
                            PLAN_FIELD + " entries must be objects");
                }
                result.add(validateOccurrence(stringMap(
                        (Map<?, ?>) element)));
            }
        }
        validateOccurrenceSequence(result, completeOccurrence);
        return Collections.unmodifiableList(result);
    }

    private static void validateOccurrenceSequence(
            List<Occurrence> phases, boolean completeOccurrence) {
        Set<String> phaseIds = new LinkedHashSet<>();
        Set<Long> eventSeqs = new LinkedHashSet<>();
        Set<Long> invocationIds = new LinkedHashSet<>();
        Map<String, Integer> previousOrdinals = new LinkedHashMap<>();
        long previousSeq = -1L;
        for (Occurrence phase : phases) {
            if (!phaseIds.add(phase.phaseId())
                    || !eventSeqs.add(phase.runtimeEventSeq())
                    || !invocationIds.add(phase.runtimeInvocationId())
                    || phase.runtimeEventSeq() <= previousSeq) {
                throw new IllegalArgumentException(PLAN_FIELD
                        + " must have unique identities in event order");
            }
            previousSeq = phase.runtimeEventSeq();
            String site = phase.phase().name() + "\n" + phase.sourceId()
                    + "\n" + phase.siteId();
            Integer prior = previousOrdinals.put(site,
                    phase.baselineOrdinal());
            if (prior != null && phase.baselineOrdinal() <= prior
                    || completeOccurrence && phase.baselineOrdinal()
                    != (prior == null ? 1 : prior + 1)) {
                throw new IllegalArgumentException(PLAN_FIELD
                        + " has a duplicate, reordered or missing site ordinal");
            }
        }
    }

    public static Map<String, Object> occurrence(
            Declaration declaration, String occurrenceId,
            int baselineOrdinal, long runtimeEventSeq,
            long ownerCallId, long runtimeInvocationId,
            String declaredCallee, Collection<Long> enclosingCallIds) {
        if (declaration == null) {
            throw new IllegalArgumentException("phase declaration is required");
        }
        if (baselineOrdinal <= 0 || runtimeEventSeq <= 0L
                || ownerCallId <= 0L || runtimeInvocationId <= 0L) {
            throw new IllegalArgumentException(
                    "runtime phase identity must be positive");
        }
        String occurrence = required(occurrenceId, "occurrenceId");
        Map<String, Object> row = declaration.json();
        row.put("kind", PLAN_KIND);
        row.put("authority", PLAN_AUTHORITY);
        row.put("phaseId", phaseId(occurrence, declaration.siteId(),
                declaration.phase(), baselineOrdinal));
        row.put("phaseKind", declaration.phase().name());
        row.put("sourceOccurrenceId", occurrence);
        row.put("baselineOrdinal", baselineOrdinal);
        row.put("eventSeq", runtimeEventSeq);
        row.put("ownerCallId", ownerCallId);
        row.put("invocationId", runtimeInvocationId);
        row.put("runtimeDeclaredCallee", required(
                declaredCallee, "runtimeDeclaredCallee"));
        List<Long> ancestry = positiveCallIds(enclosingCallIds);
        if (ancestry.isEmpty() || ancestry.get(0) != ownerCallId) {
            throw new IllegalArgumentException(
                    "enclosingCallIds must begin with ownerCallId");
        }
        row.put("enclosingCallIds", ancestry);
        return validateOccurrence(row).json();
    }

    public static String phaseId(String occurrenceId, String siteId,
                                 Phase phase, int baselineOrdinal) {
        if (baselineOrdinal <= 0) {
            throw new IllegalArgumentException(
                    "baselineOrdinal must be positive");
        }
        String identity = required(occurrenceId, "occurrenceId") + "\n"
                + required(siteId, "siteId") + "\n"
                + requiredPhase(phase).name() + "\n" + baselineOrdinal;
        return "SOURCE_PHASE." + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    public static String siteId(String method, int unitIndex) {
        if (unitIndex < 0) {
            throw new IllegalArgumentException("unitIndex must be non-negative");
        }
        return required(method, "method") + "#u" + unitIndex;
    }

    private static Declaration validateDeclaration(Map<String, Object> row) {
        if (row == null || row.size() != 9
                || integer(row.get("schemaVersion"), -1) != SCHEMA_VERSION
                || !DECLARATION_KIND.equals(text(row.get("kind")))
                || !DECLARATION_AUTHORITY.equals(text(row.get("authority")))) {
            throw new IllegalArgumentException(
                    DECLARATION_FIELD + " has an unsupported schema");
        }
        Phase phase;
        try {
            phase = Phase.valueOf(required(text(row.get("phase")), "phase"));
        } catch (RuntimeException invalid) {
            throw new IllegalArgumentException(
                    DECLARATION_FIELD + " has an invalid phase", invalid);
        }
        String sourceId = required(text(row.get("sourceId")), "sourceId");
        String field = normalized(text(row.get("fieldSignature")));
        String method = required(text(row.get("declarationMethod")),
                "declarationMethod");
        int unit = integer(row.get("declarationUnitIndex"), -1);
        String site = required(text(row.get("siteId")), "siteId");
        if (unit < 0 || !site.equals(siteId(method, unit))
                || phase == Phase.PUBLISH
                && FieldPathSpec.declaredField(field) == null
                || !field.isEmpty()
                && FieldPathSpec.declaredField(field) == null) {
            throw new IllegalArgumentException(
                    DECLARATION_FIELD + " has an invalid exact hook site");
        }
        return new Declaration(row, phase, sourceId, method, site);
    }

    private static Occurrence validateOccurrence(Map<String, Object> row) {
        if (row == null || !OCCURRENCE_FIELDS.equals(row.keySet())
                || integer(row.get("schemaVersion"), -1) != SCHEMA_VERSION
                || !PLAN_KIND.equals(text(row.get("kind")))
                || !PLAN_AUTHORITY.equals(text(row.get("authority")))) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " has an unsupported schema");
        }
        Phase phase;
        try {
            phase = Phase.valueOf(required(text(row.get("phase")), "phase"));
        } catch (RuntimeException invalid) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " has an invalid phase", invalid);
        }
        if (!phase.name().equals(text(row.get("phaseKind")))) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " phaseKind disagrees with phase");
        }
        String sourceId = required(text(row.get("sourceId")), "sourceId");
        String field = normalized(text(row.get("fieldSignature")));
        String method = required(text(row.get("declarationMethod")),
                "declarationMethod");
        int unit = integer(row.get("declarationUnitIndex"), -1);
        String site = required(text(row.get("siteId")), "siteId");
        if (unit < 0 || !site.equals(siteId(method, unit))
                || phase == Phase.PUBLISH
                && FieldPathSpec.declaredField(field) == null
                || !field.isEmpty()
                && FieldPathSpec.declaredField(field) == null) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " has an invalid exact hook site");
        }
        String sourceOccurrenceId = required(
                text(row.get("sourceOccurrenceId")), "sourceOccurrenceId");
        int baselineOrdinal = integer(row.get("baselineOrdinal"), -1);
        long eventSeq = exactLong(row.get("eventSeq"), -1L);
        long ownerCallId = exactLong(row.get("ownerCallId"), -1L);
        long invocationId = exactLong(row.get("invocationId"), -1L);
        String declaredCallee = required(
                text(row.get("runtimeDeclaredCallee")),
                "runtimeDeclaredCallee");
        String phaseId = required(text(row.get("phaseId")), "phaseId");
        if (baselineOrdinal <= 0 || eventSeq <= 0L || ownerCallId <= 0L
                || invocationId <= 0L || !phaseId.equals(phaseId(
                sourceOccurrenceId, site, phase, baselineOrdinal))) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " has an invalid runtime identity");
        }
        Object encodedAncestry = row.get("enclosingCallIds");
        if (!(encodedAncestry instanceof Collection<?>)) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " requires enclosingCallIds");
        }
        List<Long> ancestry = new ArrayList<>();
        for (Object value : (Collection<?>) encodedAncestry) {
            long callId = exactLong(value, -1L);
            if (callId <= 0L || ancestry.contains(callId)) {
                throw new IllegalArgumentException(
                        PLAN_FIELD + " has invalid enclosingCallIds");
            }
            ancestry.add(callId);
        }
        if (ancestry.isEmpty() || ancestry.get(0) != ownerCallId) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " ancestry does not begin at ownerCallId");
        }
        return new Occurrence(row, phase, phaseId, sourceId, field,
                sourceOccurrenceId, site, baselineOrdinal, eventSeq,
                invocationId, declaredCallee, ancestry);
    }

    private static Map<String, Object> stringMap(Map<?, ?> source) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (Map.Entry<?, ?> entry : source.entrySet()) {
            if (!(entry.getKey() instanceof String)) {
                throw new IllegalArgumentException(
                        DECLARATION_FIELD + " keys must be strings");
            }
            result.put((String) entry.getKey(), entry.getValue());
        }
        return result;
    }

    private static Map<String, Object> jsonMap(JsonObject source) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (Map.Entry<String, JsonElement> entry : source.entrySet()) {
            result.put(entry.getKey(), jsonValue(entry.getValue()));
        }
        return result;
    }

    private static Object jsonValue(JsonElement value) {
        if (value == null || value.isJsonNull()) return null;
        if (value.isJsonObject()) return jsonMap(value.getAsJsonObject());
        if (value.isJsonArray()) {
            List<Object> result = new ArrayList<>();
            for (JsonElement element : value.getAsJsonArray()) {
                result.add(jsonValue(element));
            }
            return result;
        }
        if (value.getAsJsonPrimitive().isBoolean()) {
            return value.getAsBoolean();
        }
        if (value.getAsJsonPrimitive().isNumber()) {
            return value.getAsNumber();
        }
        return value.getAsString();
    }

    private static int integer(Object value, int fallback) {
        if (!(value instanceof Number)) return fallback;
        Number number = (Number) value;
        int exact = number.intValue();
        return number.longValue() == exact ? exact : fallback;
    }

    private static long exactLong(Object value, long fallback) {
        if (!(value instanceof Number)) return fallback;
        try {
            return new BigDecimal(value.toString()).longValueExact();
        } catch (RuntimeException invalid) {
            return fallback;
        }
    }

    private static List<Long> positiveCallIds(Collection<Long> values) {
        if (values == null) return Collections.emptyList();
        List<Long> result = new ArrayList<>();
        for (Long value : values) {
            if (value == null || value <= 0L || result.contains(value)) {
                throw new IllegalArgumentException(
                        "enclosingCallIds must be positive and unique");
            }
            result.add(value);
        }
        return result;
    }

    private static Phase requiredPhase(Phase phase) {
        if (phase == null) {
            throw new IllegalArgumentException("phase is required");
        }
        return phase;
    }

    private static String required(String value, String label) {
        String result = normalized(value);
        if (result.isEmpty()) {
            throw new IllegalArgumentException(label + " is required");
        }
        return result;
    }

    private static String normalized(String value) {
        return value == null ? "" : value.trim();
    }

    private static String text(Object value) {
        return value == null ? "" : String.valueOf(value);
    }

    /** One validated static hook site. */
    public static final class Declaration {
        private final Map<String, Object> encoded;
        private final Phase phase;
        private final String sourceId;
        private final String method;
        private final String siteId;

        private Declaration(Map<String, Object> encoded, Phase phase,
                            String sourceId, String method, String siteId) {
            this.encoded = new LinkedHashMap<>(encoded);
            this.phase = phase;
            this.sourceId = sourceId;
            this.method = method;
            this.siteId = siteId;
        }

        public Map<String, Object> json() {
            return new LinkedHashMap<>(encoded);
        }

        public Phase phase() { return phase; }

        public String method() { return method; }

        public String siteId() { return siteId; }

        public String identity() {
            return phase.name() + "\n" + sourceId + "\n" + siteId;
        }
    }

    /** One validated execution of an exact configured-source hook site. */
    public static final class Occurrence {
        private final Map<String, Object> encoded;
        private final Phase phase;
        private final String phaseId;
        private final String sourceId;
        private final String fieldSignature;
        private final String sourceOccurrenceId;
        private final String siteId;
        private final int baselineOrdinal;
        private final long runtimeEventSeq;
        private final long runtimeInvocationId;
        private final String runtimeDeclaredCallee;
        private final List<Long> enclosingCallIds;

        private Occurrence(Map<String, Object> encoded, Phase phase,
                           String phaseId, String sourceId,
                           String fieldSignature, String sourceOccurrenceId,
                           String siteId, int baselineOrdinal,
                           long runtimeEventSeq, long runtimeInvocationId,
                           String runtimeDeclaredCallee,
                           List<Long> enclosingCallIds) {
            this.encoded = new LinkedHashMap<>(encoded);
            this.phase = phase;
            this.phaseId = phaseId;
            this.sourceId = sourceId;
            this.fieldSignature = fieldSignature;
            this.sourceOccurrenceId = sourceOccurrenceId;
            this.siteId = siteId;
            this.baselineOrdinal = baselineOrdinal;
            this.runtimeEventSeq = runtimeEventSeq;
            this.runtimeInvocationId = runtimeInvocationId;
            this.runtimeDeclaredCallee = runtimeDeclaredCallee;
            this.enclosingCallIds = Collections.unmodifiableList(
                    new ArrayList<>(enclosingCallIds));
        }

        public Map<String, Object> json() {
            return new LinkedHashMap<>(encoded);
        }

        public Phase phase() { return phase; }

        public String phaseId() { return phaseId; }

        public String sourceId() { return sourceId; }

        public String fieldSignature() { return fieldSignature; }

        public String sourceOccurrenceId() { return sourceOccurrenceId; }

        public String siteId() { return siteId; }

        /** Static method that contains this exact configured-source hook. */
        public String declarationMethod() {
            return text(encoded.get("declarationMethod"));
        }

        /** Original Jimple unit index of this exact configured-source hook. */
        public int declarationUnitIndex() {
            return ((Number) encoded.get("declarationUnitIndex")).intValue();
        }

        public int baselineOrdinal() { return baselineOrdinal; }

        public long runtimeEventSeq() { return runtimeEventSeq; }

        public long runtimeInvocationId() { return runtimeInvocationId; }

        public String runtimeDeclaredCallee() {
            return runtimeDeclaredCallee;
        }

        public List<Long> enclosingCallIds() { return enclosingCallIds; }
    }
}
