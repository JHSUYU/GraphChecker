package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
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

/**
 * The static mint sites of configured sources and the executions a recording
 * observed (SYMBOL-SCOPE §4.3).  A site is one of two, named by its row's
 * authority: a tree's {@code CausynthSymbolicSource.symbolize} call (a HOOK)
 * or the engine's read of a configuration field ({@code
 * causynth.ConfigRoots}, a CONFIG), whose integral domain the row states.  A
 * declared source is ONE symbol ({@link #engineLabel} is the source's alone),
 * so the number of executions bounds nothing a replay may read.  One codec:
 * rows are the plan wire's {@link JsonObject}s.
 */
public final class ConfiguredSourcePhaseContract {
    public static final int SCHEMA_VERSION = 1;
    public static final String DECLARATION_FIELD =
            "configuredSourcePhaseDeclarations";
    public static final String TRACE_METHODS_FIELD =
            "configuredSourcePhaseTraceMethods";
    public static final String PLAN_FIELD = "configuredSourcePhases";
    public static final String DECLARATION_KIND =
            "CONFIGURED_SOURCE_PHASE_DECLARATION";
    /** A tree's hook call. */
    public static final String DECLARATION_AUTHORITY =
            "EXACT_STATIC_SOURCE_HOOK_SITE_V1";
    /** The engine's read of a configuration field. */
    public static final String CONFIG_DECLARATION_AUTHORITY =
            "EXACT_STATIC_CONFIG_READ_SITE_V1";
    public static final String PLAN_KIND = "CONFIGURED_SOURCE_PHASE";
    public static final String PLAN_AUTHORITY =
            "EXACT_RUNTIME_SOURCE_HOOK_EXECUTION_V1";
    public static final String CONFIG_PLAN_AUTHORITY =
            "EXACT_RUNTIME_CONFIG_READ_EXECUTION_V1";
    private static final Set<String> DECLARATION_FIELDS = names(
            "schemaVersion", "kind", "authority", "phase", "sourceId",
            "fieldSignature", "declarationMethod", "declarationUnitIndex",
            "siteId");
    /** A read's evidence is the read: no invocation. */
    private static final Set<String> CONFIG_OCCURRENCE_FIELDS = union(
            DECLARATION_FIELDS, "phaseId", "sourceOccurrenceId", "eventSeq",
            "runtimeDeclaredCallee", "enclosingCallIds");
    private static final Set<String> OCCURRENCE_FIELDS = union(
            CONFIG_OCCURRENCE_FIELDS, "invocationId");
    /** A CONFIG row's integral domain, from its static anchors. */
    private static final Set<String> DOMAIN_FIELDS = names(
            "domainMin", "domainMax");

    private ConfiguredSourcePhaseContract() {
    }

    /** The one phase: a mint site, one fresh symbol for one declared field. */
    public static final String PUBLISH = "PUBLISH";

    /** A tree's hook call of {@code sourceId} at {@code method#uunitIndex}. */
    public static JsonObject declaration(
            String sourceId, String fieldSignature,
            String method, int unitIndex) {
        JsonObject row = site(DECLARATION_AUTHORITY, sourceId,
                fieldSignature, method, unitIndex);
        validateDeclaration(row);
        return row;
    }

    /**
     * The engine's read of a configuration field at {@code
     * method#uunitIndex}, with the integral domain its static anchors span
     * ({@code ""}: none, a boolean).
     */
    public static JsonObject configDeclaration(
            String sourceId, String fieldSignature, String method,
            int unitIndex, String domainMin, String domainMax) {
        JsonObject row = site(CONFIG_DECLARATION_AUTHORITY, sourceId,
                fieldSignature, method, unitIndex);
        domain(row, domainMin, domainMax);
        validateDeclaration(row);
        return row;
    }

    private static JsonObject site(String authority, String sourceId,
                                   String fieldSignature, String method,
                                   int unitIndex) {
        String exactMethod = required(method, "declarationMethod");
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("kind", DECLARATION_KIND);
        row.addProperty("authority", authority);
        row.addProperty("phase", PUBLISH);
        row.addProperty("sourceId", required(sourceId, "sourceId"));
        row.addProperty("fieldSignature", trimmed(fieldSignature));
        row.addProperty("declarationMethod", exactMethod);
        row.addProperty("declarationUnitIndex", unitIndex);
        row.addProperty("siteId", SiteId.of(exactMethod, unitIndex));
        return row;
    }

    private static void domain(JsonObject row, String min, String max) {
        if (!trimmed(min).isEmpty()) row.addProperty("domainMin", min);
        if (!trimmed(max).isEmpty()) row.addProperty("domainMax", max);
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
                    || phase.invocationId > 0L
                    && !invocationIds.add(phase.invocationId)
                    || phase.runtimeEventSeq() <= previousSeq) {
                throw new IllegalArgumentException(PLAN_FIELD
                        + " must have unique identities in event order");
            }
            previousSeq = phase.runtimeEventSeq();
        }
    }

    /** One recorded execution of a hook site: its call. */
    public static JsonObject occurrence(
            Declaration declaration, String occurrenceId,
            long runtimeEventSeq, long runtimeInvocationId,
            String declaredCallee, Collection<Long> enclosingCallIds) {
        if (declaration == null
                || declaration.category != RootCategory.HOOK) {
            throw new IllegalArgumentException(
                    "a hook site's declaration is required");
        }
        JsonObject row = occurrenceRow(declaration, PLAN_AUTHORITY,
                occurrenceId, runtimeEventSeq, declaredCallee,
                enclosingCallIds);
        row.addProperty("invocationId", runtimeInvocationId);
        return row;
    }

    /** One recorded execution of a configuration read site: the read of
     *  {@code field}, its declared field. */
    public static JsonObject configOccurrence(
            Declaration declaration, String occurrenceId,
            long runtimeEventSeq, String field,
            Collection<Long> enclosingCallIds) {
        if (declaration == null
                || declaration.category != RootCategory.CONFIG) {
            throw new IllegalArgumentException(
                    "a configuration read site's declaration is required");
        }
        JsonObject row = occurrenceRow(declaration, CONFIG_PLAN_AUTHORITY,
                occurrenceId, runtimeEventSeq, field, enclosingCallIds);
        domain(row, declaration.domainMin, declaration.domainMax);
        return row;
    }

    private static JsonObject occurrenceRow(
            Declaration declaration, String authority, String occurrenceId,
            long runtimeEventSeq, String declaredCallee,
            Collection<Long> enclosingCallIds) {
        String occurrence = required(occurrenceId, "occurrenceId");
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("kind", PLAN_KIND);
        row.addProperty("authority", authority);
        row.addProperty("phase", PUBLISH);
        row.addProperty("sourceId", declaration.sourceId());
        row.addProperty("fieldSignature", declaration.fieldSignature());
        row.addProperty("declarationMethod", declaration.method());
        row.addProperty("declarationUnitIndex",
                declaration.declarationUnitIndex());
        row.addProperty("siteId", declaration.siteId());
        row.addProperty("phaseId", phaseId(declaration.sourceId(),
                declaration.siteId()));
        row.addProperty("sourceOccurrenceId", occurrence);
        row.addProperty("eventSeq", runtimeEventSeq);
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
     * The identity of one mint site: its source and site, nothing else.
     *
     * <p>Every execution of the site is the same phase.  Trap: putting the
     * reaching occurrence or execution into the identity splits one site
     * into many, and a flip moves only one of them (hdfs-17960 lost its bug
     * this way).</p>
     */
    public static String phaseId(String sourceId, String siteId) {
        String identity = required(sourceId, "sourceId") + "\n"
                + required(siteId, "siteId") + "\n" + PUBLISH;
        return "SOURCE_PHASE." + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    /**
     * The VM label every mint of one source asks the engine for: the
     * source's alone, so every read of it, at any site, in any occurrence or
     * session, is one symbol, and a flip moves them all.
     */
    public static String engineLabel(String sourceId) {
        return "SRC." + ArtifactIO.sha256(required(sourceId, "sourceId"));
    }

    private static Declaration validateDeclaration(JsonObject row) {
        RootCategory category = categoryOf(row, DECLARATION_AUTHORITY,
                CONFIG_DECLARATION_AUTHORITY);
        if (!DECLARATION_KIND.equals(text(row, "kind"))
                || !exactSchemaVersion(row) || category == null
                || !members(row, DECLARATION_FIELDS, category)) {
            throw new IllegalArgumentException(
                    DECLARATION_FIELD + " has an unsupported schema");
        }
        return validateSite(row, DECLARATION_FIELD, category);
    }

    /** HOOK or CONFIG by the row's authority, or null for any other. */
    private static RootCategory categoryOf(JsonObject row, String hook,
                                           String config) {
        String authority = text(row, "authority");
        if (hook.equals(authority)) return RootCategory.HOOK;
        if (config.equals(authority)) return RootCategory.CONFIG;
        return null;
    }

    /** Exactly the members a row of its category states; a CONFIG row may
     *  state its domain. */
    private static boolean members(JsonObject row, Set<String> required,
                                   RootCategory category) {
        Set<String> stated = new LinkedHashSet<>(row.keySet());
        if (category == RootCategory.CONFIG) stated.removeAll(DOMAIN_FIELDS);
        return required.equals(stated);
    }

    private static boolean exactSchemaVersion(JsonObject row) {
        JsonElement value = row.get("schemaVersion");
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isNumber()
                && Integer.toString(SCHEMA_VERSION).equals(value.getAsString());
    }

    /** The site half shared by declaration and occurrence rows. */
    private static Declaration validateSite(JsonObject row, String field,
                                            RootCategory category) {
        if (!PUBLISH.equals(text(row, "phase"))) {
            throw new IllegalArgumentException(field + " has an invalid phase");
        }
        String sourceId = required(text(row, "sourceId"), "sourceId");
        String signature = text(row, "fieldSignature");
        String method = required(text(row, "declarationMethod"),
                "declarationMethod");
        int unit = exactInt(row, "declarationUnitIndex");
        if (unit < 0 || FieldPathSpec.declaredField(signature) == null
                || !SiteId.of(method, unit).equals(text(row, "siteId"))) {
            throw new IllegalArgumentException(
                    field + " has an invalid exact mint site");
        }
        String min = text(row, "domainMin");
        String max = text(row, "domainMax");
        if (min.isEmpty() != max.isEmpty() || !min.isEmpty()
                && (!min.matches("-?[0-9]+") || !max.matches("-?[0-9]+"))) {
            throw new IllegalArgumentException(
                    field + " states half a domain or a non-integral one");
        }
        return new Declaration(sourceId, signature, method, unit, category,
                min, max);
    }

    private static Occurrence validateOccurrence(JsonObject row) {
        RootCategory category = categoryOf(row, PLAN_AUTHORITY,
                CONFIG_PLAN_AUTHORITY);
        if (!PLAN_KIND.equals(text(row, "kind")) || !exactSchemaVersion(row)
                || category == null
                || !members(row, category == RootCategory.HOOK
                        ? OCCURRENCE_FIELDS : CONFIG_OCCURRENCE_FIELDS,
                        category)) {
            throw new IllegalArgumentException(
                    PLAN_FIELD + " has an unsupported schema");
        }
        Declaration declared = validateSite(row, PLAN_FIELD, category);
        String sourceOccurrenceId = required(
                text(row, "sourceOccurrenceId"), "sourceOccurrenceId");
        long eventSeq = exactLong(row, "eventSeq");
        long invocationId = category == RootCategory.HOOK
                ? exactLong(row, "invocationId") : 0L;
        String declaredCallee = required(
                text(row, "runtimeDeclaredCallee"), "runtimeDeclaredCallee");
        String phaseId = required(text(row, "phaseId"), "phaseId");
        if (eventSeq <= 0L || category == RootCategory.HOOK
                && invocationId <= 0L
                || !phaseId.equals(phaseId(declared.sourceId(),
                declared.siteId()))) {
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
                eventSeq, invocationId, declaredCallee);
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

    private static Set<String> names(String... values) {
        return Collections.unmodifiableSet(
                new LinkedHashSet<>(Arrays.asList(values)));
    }

    private static Set<String> union(Set<String> base, String... more) {
        Set<String> all = new LinkedHashSet<>(base);
        all.addAll(Arrays.asList(more));
        return Collections.unmodifiableSet(all);
    }

    public static final class Declaration {
        private final String sourceId;
        private final String fieldSignature;
        private final String method;
        private final int unitIndex;
        private final String siteId;
        private final RootCategory category;
        private final String domainMin;
        private final String domainMax;

        private Declaration(String sourceId, String fieldSignature,
                            String method, int unitIndex,
                            RootCategory category, String domainMin,
                            String domainMax) {
            this.sourceId = sourceId;
            this.fieldSignature = fieldSignature;
            this.method = method;
            this.unitIndex = unitIndex;
            this.siteId = SiteId.of(method, unitIndex);
            this.category = category;
            this.domainMin = domainMin;
            this.domainMax = domainMax;
        }

        public String sourceId() { return sourceId; }

        public String fieldSignature() { return fieldSignature; }

        public String method() { return method; }

        public int declarationUnitIndex() { return unitIndex; }

        public String siteId() { return siteId; }

        /** HOOK: the site calls the tree's hook; CONFIG: it reads the
         *  configuration field. */
        public RootCategory category() { return category; }
    }

    public static final class Occurrence {
        private final Declaration declared;
        private final String phaseId;
        private final String sourceOccurrenceId;
        private final long runtimeEventSeq;
        /** A hook execution's call; 0 for a read, which is none. */
        private final long invocationId;
        private final String runtimeDeclaredCallee;

        private Occurrence(Declaration declared, String phaseId,
                           String sourceOccurrenceId,
                           long runtimeEventSeq, long invocationId,
                           String runtimeDeclaredCallee) {
            this.declared = declared;
            this.phaseId = phaseId;
            this.sourceOccurrenceId = sourceOccurrenceId;
            this.runtimeEventSeq = runtimeEventSeq;
            this.invocationId = invocationId;
            this.runtimeDeclaredCallee = runtimeDeclaredCallee;
        }

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

        /** What runs at the site: the hook a HOOK site calls, the field a
         *  CONFIG site reads. */
        public String runtimeDeclaredCallee() { return runtimeDeclaredCallee; }

        public RootCategory category() { return declared.category(); }

        /** A CONFIG site's static domain bound, or {@code ""}. */
        public String domainMin() { return declared.domainMin; }

        /** A CONFIG site's static domain bound, or {@code ""}. */
        public String domainMax() { return declared.domainMax; }
    }
}
