package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.textString;

/**
 * Canonical V2 wire contract for activation-local dynamic field bindings.
 *
 * <p>Object tokens are meaningful only inside {@code objectTokenScope}. Replay
 * compares stable selector identity and scope authority, never token ordinals
 * from different executions.</p>
 */
public final class DynamicBindingSpec {
    public static final int SCHEMA_VERSION = 2;
    public static final String MAP_ENTRY_KIND =
            "DYNAMIC_MAP_ENTRY_FIELD_BINDING";
    public static final String CONTAINER_ELEMENT_KIND =
            "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING";
    public static final String MAP_OUTPUT_ELEMENT_KIND =
            "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING";

    private final JsonObject json;
    private final String kind;
    private final SelectorSpec selector;

    private DynamicBindingSpec(JsonObject source) {
        if (integer(source, "schemaVersion", -1) != SCHEMA_VERSION) {
            throw new IllegalArgumentException(
                    "unsupported dynamic binding schema");
        }
        kind = textString(source, "kind");
        if (!MAP_ENTRY_KIND.equals(kind)
                && !CONTAINER_ELEMENT_KIND.equals(kind)
                && !MAP_OUTPUT_ELEMENT_KIND.equals(kind)) {
            throw new IllegalArgumentException(
                    "unsupported dynamic binding kind: " + kind);
        }
        JsonObject encodedSelector = object(source,
                MAP_OUTPUT_ELEMENT_KIND.equals(kind)
                        ? "mapProjectionSelector" : "containerSelector");
        selector = MAP_ENTRY_KIND.equals(kind) ? null
                : SelectorSpec.decode(encodedSelector);
        if (CONTAINER_ELEMENT_KIND.equals(kind)
                && !SelectorSpec.ARRAY_INDEX.equals(selector.kind())
                || MAP_OUTPUT_ELEMENT_KIND.equals(kind)
                && !SelectorSpec.MAP_OUTPUT_ARRAY_INDEX.equals(
                selector.kind())) {
            throw new IllegalArgumentException(
                    "dynamic binding kind does not match selector kind");
        }
        json = source.deepCopy();
    }

    public static DynamicBindingSpec decode(JsonObject source) {
        if (source == null) {
            throw new IllegalArgumentException(
                    "dynamic binding object is required");
        }
        return new DynamicBindingSpec(source);
    }

    public String kind() {
        return kind;
    }

    public String dynamicBindingId() {
        return textString(json, "dynamicBindingId");
    }

    public String baseInputSymbol() {
        return textString(json, "baseInputSymbol");
    }

    public String dynamicFieldSymbol() {
        return textString(json, "dynamicFieldSymbol");
    }

    public String materializationSiteId() {
        return textString(json, "materializationSiteId");
    }

    public int materializationOccurrence() {
        return integer(json, "materializationOccurrence", -1);
    }

    public String fieldSignature() {
        return textString(json, "fieldSignature");
    }

    public List<String> fieldPath() {
        return strings(json, "fieldPath");
    }

    public long leafOwnerObjectToken() {
        return longInteger(json, "leafOwnerObjectToken", 0L);
    }

    public String objectTokenScope() {
        return textString(json, "objectTokenScope");
    }

    public SelectorSpec selector() {
        return selector;
    }

    public boolean complete() {
        return bool(json, "complete", false);
    }

    public JsonObject toJson() {
        return json.deepCopy();
    }

    /**
     * Canonical selector shared by static container declarations, runtime
     * binding evidence and replay model assignments.
     */
    public static final class SelectorSpec {
        public static final String ARRAY_INDEX = "ARRAY_INDEX";
        public static final String MAP_OUTPUT_ARRAY_INDEX =
                "MAP_OUTPUT_ARRAY_INDEX";
        public static final String EXACT_ARRAY_INDEX = "EXACT_ARRAY_INDEX";
        public static final String DISCOVER_UNIQUE_IDENTITY_INDEX =
                "DISCOVER_UNIQUE_IDENTITY_INDEX";
        public static final String MAP_OUTPUT_AUTHORITY =
                "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                        + "EXACT_OUTPUT_IDENTITY";
        public static final String CONTAINER_REPLAY_REBINDING_AUTHORITY =
                "EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                        + "IDENTITY_REBIND_V1";

        private final JsonObject json;
        private final String kind;

        private SelectorSpec(JsonObject source) {
            kind = textString(source, "kind");
            if (!ARRAY_INDEX.equals(kind)
                    && !MAP_OUTPUT_ARRAY_INDEX.equals(kind)) {
                throw new IllegalArgumentException(
                        "unsupported dynamic selector kind: " + kind);
            }
            json = source.deepCopy();
        }

        public static SelectorSpec decode(JsonObject source) {
            if (source == null || source.size() == 0) {
                throw new IllegalArgumentException(
                        "dynamic selector object is required");
            }
            return new SelectorSpec(source);
        }

        public static SelectorSpec decodeOptional(JsonObject source) {
            return source == null || source.size() == 0 ? null
                    : decode(source);
        }

        public static SelectorSpec decodeOptional(
                JsonObject source, String expectedKind) {
            SelectorSpec selector = decodeOptional(source);
            if (selector != null && !expectedKind.equals(selector.kind())) {
                throw new IllegalArgumentException(
                        "selector kind does not match its contract field");
            }
            return selector;
        }

        /**
         * Converts the canonical static V2 ARRAY_ELEMENT_FIELD declaration to
         * the selector shape used by runtime evidence and replay.
         */
        public static SelectorSpec fromContainerDeclaration(
                JsonObject declaration) {
            if (integer(declaration, "schemaVersion", -1) != 2
                    || !"ARRAY_ELEMENT_FIELD".equals(
                    textString(declaration, "kind"))
                    || !"CONTAINER_SNAPSHOT".equals(
                    textString(declaration, "materializationMode"))) {
                throw new IllegalArgumentException(
                        "unsupported container element binding contract");
            }
            JsonObject selector = declaration.deepCopy();
            selector.addProperty("kind", ARRAY_INDEX);
            return new SelectorSpec(selector);
        }

        public String kind() {
            return kind;
        }

        public String bindingId() {
            return textString(json, "bindingId");
        }

        public String baseInputSymbol() {
            return textString(json, "baseInputSymbol");
        }

        public String containerInputPort() {
            return textString(json, "containerInputPort");
        }

        public String containerInputCell() {
            return textString(json, "containerInputCell");
        }

        public String selectorAuthority() {
            return textString(json, "selectorAuthority");
        }

        public String resolvedFromSelectorAuthority() {
            return textString(json, "resolvedFromSelectorAuthority");
        }

        public int elementIndex() {
            return integer(json, "elementIndex",
                    integer(json, "outputIndex", -1));
        }

        public int elementOccurrence() {
            return integer(json, "elementOccurrence", -1);
        }

        public String fieldMaterializationSiteId() {
            return textString(json, "fieldMaterializationSiteId");
        }

        public List<String> fieldPath() {
            return strings(json, "fieldPath");
        }

        public String declaredFieldSignature() {
            return textString(json, "declaredFieldSignature");
        }

        public String declaredFieldOwnerClass() {
            FieldPathSpec.DeclaredField field =
                    FieldPathSpec.declaredField(declaredFieldSignature());
            return field == null ? "" : field.owner();
        }

        public String declaredFieldType() {
            FieldPathSpec.DeclaredField field =
                    FieldPathSpec.declaredField(declaredFieldSignature());
            return field == null ? "" : field.type().trim()
                    .replace('/', '.');
        }

        public String mapInputPort() {
            return textString(json, "mapInputPort");
        }

        public String mapInputCell() {
            return textString(json, "mapInputCell");
        }

        public String outputPort() {
            return textString(json, "outputPort");
        }

        public String outputCell() {
            return textString(json, "outputCell");
        }

        public String mapProjectionOperation() {
            return textString(json, "mapProjectionOperation");
        }

        public long containerObjectToken() {
            return longInteger(json, "containerObjectToken", 0L);
        }

        public long mapObjectToken() {
            return longInteger(json, "mapObjectToken", 0L);
        }

        public long elementObjectToken() {
            return longInteger(json, "elementObjectToken", 0L);
        }

        public long outputArrayObjectToken() {
            return longInteger(json, "outputArrayObjectToken", 0L);
        }

        public String objectTokenScope() {
            return textString(json, "objectTokenScope");
        }

        public String sourceObjectTokenScope() {
            return textString(json, "sourceObjectTokenScope");
        }

        public JsonElement expectedMapKey() {
            JsonElement value = json.get("expectedMapKey");
            return value == null || value.isJsonNull()
                    ? null : value.deepCopy();
        }

        public String outputVerificationAuthority() {
            return textString(json, "outputVerificationAuthority");
        }

        public boolean outputIdentityVerified() {
            return bool(json, "outputIdentityVerified", false);
        }

        public boolean complete() {
            return bool(json, "complete", false);
        }

        public boolean exactArrayIndex() {
            return EXACT_ARRAY_INDEX.equals(selectorAuthority());
        }

        public boolean requiresExactCoverage() {
            return ARRAY_INDEX.equals(kind)
                    && exactArrayIndex()
                    && !bindingId().isEmpty()
                    && !baseInputSymbol().isEmpty()
                    && elementIndex() >= 0
                    && elementOccurrence() > 0
                    && !fieldMaterializationSiteId().isEmpty();
        }

        public boolean completeContainerReplay(
                String replayRebindingAuthority) {
            return ARRAY_INDEX.equals(kind)
                    && !bindingId().isEmpty()
                    && !containerInputPort().isEmpty()
                    && !containerInputCell().isEmpty()
                    && !selectorAuthority().isEmpty()
                    && elementIndex() >= 0
                    && elementOccurrence() > 0
                    && FieldPathSpec.declaredField(
                    declaredFieldSignature()) != null
                    && CONTAINER_REPLAY_REBINDING_AUTHORITY.equals(
                    replayRebindingAuthority);
        }

        public boolean completeMapOutputReplay() {
            long map = mapObjectToken();
            long element = elementObjectToken();
            long output = outputArrayObjectToken();
            return MAP_OUTPUT_ARRAY_INDEX.equals(kind)
                    && !bindingId().isEmpty()
                    && !mapInputPort().isEmpty()
                    && !mapInputCell().isEmpty()
                    && !outputPort().isEmpty()
                    && !outputCell().isEmpty()
                    && "MAP_VALUES_VIEW".equals(mapProjectionOperation())
                    && elementIndex() >= 0 && elementOccurrence() > 0
                    && MAP_OUTPUT_AUTHORITY.equals(
                    textString(json, "authority"))
                    && !objectTokenScope().isEmpty()
                    && !declaredFieldSignature().isEmpty()
                    && map > 0L && element > 0L && output > 0L
                    && map != element && map != output && element != output
                    && !outputVerificationAuthority().isEmpty()
                    && expectedMapKey() != null
                    && "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_"
                    .concat("SNAPSHOT").equals(
                            textString(json, "expectedMapKeyAuthority"))
                    && "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                    .concat("POSITIONAL_REFERENCE_EQUALITY").equals(
                            textString(json, "sourceOutputIndexAuthority"))
                    && "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_"
                    .concat("AND_EXACT_OUTPUT_IDENTITY").equals(
                            textString(json, "replaySelectionAuthority"))
                    && !sourceObjectTokenScope().isEmpty()
                    && "SOURCE_CASE_SELECTOR_VALIDATED_THEN_REPLAY_"
                    .concat("ACTIVATION_SCOPE_REBOUND_TOKENS_NOT_"
                            + "COMPARED_ACROSS_EXECUTIONS").equals(
                            textString(json, "replayScopeRebindingAuthority"))
                    && outputIdentityVerified() && complete();
        }

        public boolean sameArraySelector(SelectorSpec other) {
            return other != null
                    && bindingId().equals(other.bindingId())
                    && containerInputPort().equals(other.containerInputPort())
                    && containerInputCell().equals(other.containerInputCell())
                    && selectorAuthority().equals(other.selectorAuthority())
                    && elementIndex() == other.elementIndex()
                    && elementOccurrence() == other.elementOccurrence()
                    && declaredFieldSignature().equals(
                    other.declaredFieldSignature());
        }

        public JsonObject toJson() {
            return json.deepCopy();
        }
    }

    private static List<String> strings(JsonObject source, String field) {
        JsonElement value = source == null ? null : source.get(field);
        if (value == null || !value.isJsonArray()) {
            return Collections.emptyList();
        }
        List<String> result = new ArrayList<>();
        JsonArray values = value.getAsJsonArray();
        for (JsonElement element : values) {
            if (element.isJsonPrimitive()
                    && element.getAsJsonPrimitive().isString()) {
                result.add(element.getAsString());
            }
        }
        return Collections.unmodifiableList(result);
    }

    private static int integer(JsonObject source, String field, int fallback) {
        JsonElement value = source == null ? null : source.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isNumber()
                ? value.getAsInt() : fallback;
    }

    private static long longInteger(
            JsonObject source, String field, long fallback) {
        JsonElement value = source == null ? null : source.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isNumber()
                ? value.getAsLong() : fallback;
    }

    private static boolean bool(
            JsonObject source, String field, boolean fallback) {
        JsonElement value = source == null ? null : source.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean()
                ? value.getAsBoolean() : fallback;
    }
}
