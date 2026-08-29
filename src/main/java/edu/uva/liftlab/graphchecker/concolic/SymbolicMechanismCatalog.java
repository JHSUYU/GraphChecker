package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.SymbolicRootProposal.Decision;
import edu.uva.liftlab.graphchecker.concolic.SymbolicRootProposal.DecisionKind;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Deterministic compression boundary between scheduler facts and an external
 * semantic classifier.  Dynamic reader and writer repetitions are evidence,
 * not root identity: the scheduler/VM keeps their bounded versions after one
 * mechanism-level decision has been made.
 */
final class SymbolicMechanismCatalog {
    static final int SCHEMA_VERSION = 1;
    static final String KIND = "SYMBOLIC_ROOT_MECHANISM_CATALOG";
    static final String AUTHORITY =
            "SCHEDULER_STRUCTURED_FACTS_ONLY_V1";
    static final String FILE_NAME = "symbolic_root_mechanism_cards.json";
    static final String SELECTION_AUTHORITY =
            "VALIDATED_LLM_SYMBOLIC_ROOT_PROPOSAL_V1";

    /** Stable fields used only when an action has no resolved writer. */
    private static final String[] LOCAL_ORIGIN_FIELDS = {
            "sourceKind", "dependencyRole", "location", "bindingMode",
            "javaType", "definitionMethod", "definitionUnitIndex",
            "definitionSites", "method", "local", "index",
            "argumentIndex", "declaredCallee", "callSiteId",
            "handoffLeafPath", "handoffPath", "manualCarrierClass",
            "manualCarrierDescriptor", "manualCarrierField",
            "captureKind", "outputCaptureKind", "protocolDirection",
            "rootKind", "rootMethod", "staticAccessSiteId", "outputSiteId"
    };

    /** Reader-site detail retained for the LLM, but never hashed as a root. */
    private static final String[] EVIDENCE_FIELDS = {
            "sourceKind", "dependencyRole", "location", "bindingMode",
            "cell", "javaType", "accessFieldSignature",
            "declaredFieldSignature", "leafFieldSignature",
            "fieldSignature", "fieldPath", "fieldPaths",
            "fieldPathDeclarations", "definitionMethod",
            "definitionUnitIndex", "method", "local", "index",
            "argumentIndex", "declaredCallee",
            "accessorImplementationMethod", "callerMethod", "unitIndex",
            "callSiteId", "exchangeSiteKey", "direction", "portRole",
            "handoffLeafPath", "handoffPath", "manualCarrierClass",
            "manualCarrierDescriptor", "manualCarrierField",
            "captureKind", "outputCaptureKind", "protocolDirection",
            "rootKind", "rootMethod", "staticAccessSiteId",
            "outputSiteId", "outputOccurrence", "replayOccurrence",
            "helperActivationBoundedOccurrence", "boundedWriterOccurrence",
            "baselineOrdinal", "symbolicDemand"
    };

    private final JsonObject encoded;
    private final String inputDigest;
    private final Map<String, Card> cards;

    private SymbolicMechanismCatalog(JsonObject inputs,
                                     List<JsonObject> observations,
                                     JsonArray declaredFixedRoots) {
        Map<String, CardBuilder> candidates = new TreeMap<>();
        Set<String> fixedFields = fixedFieldSignatures(declaredFixedRoots);
        for (JsonObject observation : observations == null
                ? Collections.<JsonObject>emptyList() : observations) {
            JsonObject action = objectMember(observation, "action");
            JsonObject baseline = objectMember(observation, "baseline");
            JsonObject context = objectMember(observation, "context");
            JsonArray writerAnchors = arrayMember(observation,
                    "writerAnchors");
            if (action.size() == 0 || baseline.size() == 0
                    || context.size() == 0) {
                throw new IllegalArgumentException(
                        "mechanism observation is incomplete");
            }
            // A static source hook is already an authoritative fixed-root
            // declaration.  Re-encoding its downstream action as another ID
            // would give one root two unrelated identities.
            boolean fixed = "CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED".equals(
                    string(baseline, "symbolicDemand"));
            if (fixed) continue;

            JsonObject semantic = semanticDescriptor(action, writerAnchors);
            String candidateId = candidateIdFromSemantic(semantic);
            boolean symbolizable = "SYMBOLIC".equals(string(action, "mode"))
                    && writerAnchors.size() == 0
                    && Collections.disjoint(fixedFields,
                    fieldDeclarations(action));
            CardBuilder builder = candidates.get(candidateId);
            if (builder == null) {
                builder = new CardBuilder(candidateId, semantic,
                        writerAnchors.size() > 0);
                candidates.put(candidateId, builder);
            }
            builder.observe(context, action, baseline, symbolizable);
        }

        JsonArray candidateRows = new JsonArray();
        Map<String, Card> decodedCards = new LinkedHashMap<>();
        for (CardBuilder builder : candidates.values()) {
            Card card = builder.build();
            candidateRows.add(card.json());
            decodedCards.put(card.candidateId, card);
        }
        Map<String, JsonObject> orderedFixedRows = new TreeMap<>();
        for (JsonElement element : declaredFixedRoots == null
                ? new JsonArray() : declaredFixedRoots) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "declared fixed root must be an object");
            }
            JsonObject row = element.getAsJsonObject().deepCopy();
            String id = string(row, "fixedRootId");
            JsonObject prior = orderedFixedRows.put(id, row);
            if (prior != null && !prior.equals(row)) {
                throw new IllegalArgumentException(
                        "conflicting fixed root declaration: " + id);
            }
        }
        JsonArray fixedRows = new JsonArray();
        for (JsonObject row : orderedFixedRows.values()) {
            fixedRows.add(row);
        }

        JsonObject digestPayload = new JsonObject();
        digestPayload.addProperty("schemaVersion", SCHEMA_VERSION);
        digestPayload.addProperty("kind", KIND);
        digestPayload.addProperty("authority", AUTHORITY);
        digestPayload.add("inputs", inputs == null
                ? new JsonObject() : inputs.deepCopy());
        digestPayload.add("fixedRoots", fixedRows);
        digestPayload.add("candidates", candidateRows);
        inputDigest = CanonicalJson.sha256(digestPayload);

        encoded = digestPayload.deepCopy();
        encoded.addProperty("inputDigest", inputDigest);
        cards = Collections.unmodifiableMap(decodedCards);
    }

    static SymbolicMechanismCatalog create(
            JsonObject inputs, List<JsonObject> observations) {
        return create(inputs, observations, new JsonArray());
    }

    static SymbolicMechanismCatalog create(
            JsonObject inputs, List<JsonObject> observations,
            JsonArray declaredFixedRoots) {
        return new SymbolicMechanismCatalog(inputs, observations,
                declaredFixedRoots);
    }

    JsonObject json() { return encoded.deepCopy(); }

    String inputDigest() { return inputDigest; }

    int candidateCount() { return cards.size(); }

    /** Static hook declarations are fixed roots, never LLM candidates. */
    static JsonArray fixedRootDeclarations(List<JsonObject> regions) {
        Map<String, JsonObject> rows = new TreeMap<>();
        for (JsonObject region : regions == null
                ? Collections.<JsonObject>emptyList() : regions) {
            String regionId = string(region, "regionId");
            JsonElement encoded = region.get(
                    StaticSymbolicSourceDeclaration.FIELD);
            if (encoded == null || !encoded.isJsonArray()) continue;
            for (JsonElement element : encoded.getAsJsonArray()) {
                if (!element.isJsonObject()) continue;
                JsonObject declaration = element.getAsJsonObject();
                JsonObject semantic = new JsonObject();
                semantic.addProperty("sourceId", string(declaration,
                        "sourceId"));
                semantic.addProperty("fieldSignature", string(declaration,
                        "fieldSignature"));
                semantic.addProperty("declarationMethod", string(declaration,
                        "declarationMethod"));
                JsonElement unit = declaration.get("declarationUnitIndex");
                if (unit != null) {
                    semantic.add("declarationUnitIndex", unit.deepCopy());
                }
                String id = "FIXED_ROOT." + CanonicalJson.sha256(semantic);
                JsonObject row = new JsonObject();
                row.addProperty("fixedRootId", id);
                row.addProperty("rootAuthority",
                        "STATIC_SYMBOLIC_SOURCE_HOOK_V1");
                row.add("semantic", semantic);
                JsonObject evidence = new JsonObject();
                evidence.addProperty("declaringRegionId", regionId);
                String evidenceId = "ROOT_EVIDENCE."
                        + CanonicalJson.sha256(id + "\n"
                        + CanonicalJson.render(evidence));
                evidence.addProperty("evidenceId", evidenceId);
                JsonArray evidenceIds = new JsonArray();
                evidenceIds.add(evidenceId);
                row.add("evidenceIds", evidenceIds);
                JsonArray evidenceRows = new JsonArray();
                evidenceRows.add(evidence);
                row.add("evidence", evidenceRows);
                JsonObject prior = rows.put(id, row);
                if (prior != null) {
                    if (!prior.getAsJsonObject("semantic").equals(
                            row.getAsJsonObject("semantic"))) {
                        throw new IllegalArgumentException(
                                "conflicting static root declaration: " + id);
                    }
                    mergeEvidence(prior, row);
                    rows.put(id, prior);
                }
            }
        }
        JsonArray result = new JsonArray();
        for (JsonObject row : rows.values()) result.add(row);
        return result;
    }

    private static void mergeEvidence(JsonObject target, JsonObject source) {
        Map<String, JsonObject> evidence = new TreeMap<>();
        for (JsonObject row : new JsonObject[]{target, source}) {
            for (JsonElement element : row.getAsJsonArray("evidence")) {
                JsonObject item = element.getAsJsonObject().deepCopy();
                evidence.put(string(item, "evidenceId"), item);
            }
        }
        JsonArray ids = new JsonArray();
        JsonArray rows = new JsonArray();
        for (Map.Entry<String, JsonObject> entry : evidence.entrySet()) {
            ids.add(entry.getKey());
            rows.add(entry.getValue());
        }
        target.add("evidenceIds", ids);
        target.add("evidence", rows);
    }

    /** One row per scheduler action, its manual baseline and exact writers. */
    static List<JsonObject> observations(
            JsonObject context, JsonArray actions, JsonArray baseline,
            JsonArray writerAnchors) {
        if (actions == null || baseline == null
                || writerAnchors == null
                || actions.size() != baseline.size()
                || actions.size() != writerAnchors.size()) {
            throw new IllegalArgumentException(
                    "mechanism observations require parallel action arrays");
        }
        List<JsonObject> result = new ArrayList<>();
        for (int index = 0; index < actions.size(); index++) {
            JsonElement action = actions.get(index);
            JsonElement selected = baseline.get(index);
            JsonElement anchors = writerAnchors.get(index);
            if (!action.isJsonObject() || !selected.isJsonObject()) {
                throw new IllegalArgumentException(
                        "mechanism actions must be objects");
            }
            JsonObject row = new JsonObject();
            row.add("context", context.deepCopy());
            row.add("action", action.getAsJsonObject().deepCopy());
            row.add("baseline", selected.getAsJsonObject().deepCopy());
            row.add("writerAnchors", canonicalWriterAnchors(anchors));
            result.add(row);
        }
        return result;
    }

    /**
     * Binds a proposal to this exact catalog.  No missing/unknown candidate,
     * invented evidence, promotion of a concrete-only site, or review item is
     * executable.
     */
    Selection validate(SymbolicRootProposal proposal) {
        if (proposal == null) {
            throw new IllegalArgumentException("symbolic-root proposal missing");
        }
        if (!inputDigest.equals(proposal.inputDigest())) {
            throw new IllegalArgumentException(
                    "symbolic-root proposal inputDigest is stale");
        }
        Map<String, Decision> decisions = new LinkedHashMap<>();
        Set<String> selectedRootGroups = new LinkedHashSet<>();
        for (Decision decision : proposal.decisions()) {
            if (decision.decision() == DecisionKind.REVIEW) {
                throw new IllegalArgumentException(
                        "symbolic-root proposal requires review: "
                                + decision.candidateId());
            }
            Card card = cards.get(decision.candidateId());
            if (card == null) {
                throw new IllegalArgumentException(
                        "symbolic-root proposal names unknown candidate: "
                                + decision.candidateId());
            }
            for (String evidenceId : decision.evidenceIds()) {
                if (!card.evidenceIds.contains(evidenceId)) {
                    throw new IllegalArgumentException(
                            "symbolic-root proposal cites foreign evidence: "
                                    + evidenceId);
                }
            }
            if (card.relationBound
                    && decision.decision() != DecisionKind.RETAIN_CONTEXT) {
                throw new IllegalArgumentException(
                        "relation-bound candidate must retain producer context: "
                                + decision.candidateId());
            }
            if (decision.decision() == DecisionKind.SELECT_ROOT) {
                if (!card.symbolizable) {
                    throw new IllegalArgumentException(
                            "proposal promotes a concrete-only candidate: "
                                    + decision.candidateId());
                }
                if (!decision.hasRootGroupId()) {
                    throw new IllegalArgumentException(
                            "selected root requires rootGroupId: "
                                    + decision.candidateId());
                }
                selectedRootGroups.add(decision.rootGroupId());
            } else if (decision.hasRootGroupId()) {
                throw new IllegalArgumentException(
                        "only selected roots may name rootGroupId: "
                                + decision.candidateId());
            }
            decisions.put(decision.candidateId(), decision);
        }
        if (!decisions.keySet().equals(cards.keySet())) {
            Set<String> missing = new LinkedHashSet<>(cards.keySet());
            missing.removeAll(decisions.keySet());
            throw new IllegalArgumentException(
                    "symbolic-root proposal omits candidates: " + missing);
        }
        if (selectedRootGroups.size() > 1) {
            throw new IllegalArgumentException(
                    "one proposal must name one rootGroupId: "
                            + selectedRootGroups);
        }
        return new Selection(inputDigest, decisions);
    }

    static String candidateId(JsonObject action, JsonArray writerAnchors) {
        return candidateIdFromSemantic(semanticDescriptor(action,
                writerAnchors));
    }

    private static String candidateIdFromSemantic(JsonElement semantic) {
        return "ROOT_CANDIDATE." + CanonicalJson.sha256(semantic);
    }

    static JsonObject semanticDescriptor(JsonObject action,
                                         JsonArray writerAnchors) {
        JsonObject result = new JsonObject();
        JsonArray anchors = canonicalWriterAnchors(writerAnchors);
        if (anchors.size() > 0) {
            result.addProperty("mechanismKind", "RELATION_BOUND_VALUE");
            result.add("writerAnchors", anchors);
            return (JsonObject) CanonicalJson.copy(result);
        }

        JsonArray declarations = canonicalFieldDeclarations(action);
        if (declarations.size() > 0) {
            result.addProperty("mechanismKind", "FIELD_ORIGIN");
            result.add("fieldPathDeclarations", declarations);
            copy(result, action, "fieldPath");
            copy(result, action, "fieldPaths");
            copy(result, action, "javaType");
        } else {
            result.addProperty("mechanismKind", "PROGRAM_INPUT_ORIGIN");
            for (String field : LOCAL_ORIGIN_FIELDS) {
                copy(result, action, field);
            }
            String cell = canonicalCell(string(action, "cell"));
            if (!cell.isEmpty()) result.addProperty("cell", cell);
        }
        if (result.size() == 1) {
            throw new IllegalArgumentException(
                    "symbolic mechanism action has no stable semantics");
        }
        return (JsonObject) CanonicalJson.copy(result);
    }

    private static JsonObject objectMember(JsonObject row, String field) {
        JsonElement value = row == null ? null : row.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static JsonArray arrayMember(JsonObject row, String field) {
        JsonElement value = row == null ? null : row.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    static final class Selection {
        private final String inputDigest;
        private final Map<String, Decision> decisions;

        private Selection(String inputDigest,
                          Map<String, Decision> decisions) {
            this.inputDigest = inputDigest;
            this.decisions = Collections.unmodifiableMap(
                    new LinkedHashMap<>(decisions));
        }

        /** Applies only to actions the scheduler had already deemed symbolic. */
        JsonArray select(JsonArray actions, JsonArray baseline,
                         JsonArray writerAnchors) {
            if (actions == null || baseline == null
                    || writerAnchors == null
                    || actions.size() != baseline.size()
                    || actions.size() != writerAnchors.size()) {
                throw new IllegalArgumentException(
                        "root selection requires parallel action arrays");
            }
            JsonArray selected = new JsonArray();
            for (int index = 0; index < actions.size(); index++) {
                JsonObject action = actions.get(index).getAsJsonObject();
                JsonObject prior = baseline.get(index).getAsJsonObject();
                JsonArray anchors = canonicalWriterAnchors(
                        writerAnchors.get(index));
                if (!"SYMBOLIC".equals(string(action, "mode"))
                        || "CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED".equals(
                        string(prior, "symbolicDemand"))) {
                    selected.add(prior.deepCopy());
                    continue;
                }
                String candidateId = candidateId(action, anchors);
                Decision decision = decisions.get(candidateId);
                if (decision == null) {
                    throw new IllegalStateException(
                            "validated proposal lost candidate " + candidateId);
                }
                JsonObject retained = action.deepCopy();
                if (decision.decision() == DecisionKind.SELECT_ROOT) {
                    retained.addProperty("symbolicSelectionAuthority",
                            SELECTION_AUTHORITY);
                    retained.addProperty("symbolicSelectionDecision",
                            DecisionKind.SELECT_ROOT.name());
                    retained.addProperty("symbolicSelectionRole",
                            decision.siteRole().name());
                    retained.addProperty("symbolicRootCandidateId",
                            candidateId);
                    retained.addProperty("symbolicRootGroupId",
                            decision.rootGroupId());
                    retained.addProperty("symbolicRootCatalogDigest",
                            inputDigest);
                } else if (decision.decision()
                        == DecisionKind.RETAIN_CONTEXT
                        && anchors.size() > 0) {
                    retained.addProperty("symbolicSelectionAuthority",
                            SELECTION_AUTHORITY);
                    retained.addProperty("symbolicSelectionDecision",
                            DecisionKind.RETAIN_CONTEXT.name());
                    retained.addProperty("symbolicSelectionRole",
                            decision.siteRole().name());
                    retained.addProperty("symbolicMechanismCandidateId",
                            candidateId);
                    retained.addProperty("symbolicRootCatalogDigest",
                            inputDigest);
                } else {
                    retained.addProperty("mode", "CONCRETE");
                    retained.addProperty("symbolicDemand",
                            decision.decision()
                                    == DecisionKind.RETAIN_CONTEXT
                                    ? "LLM_CONTEXT_WITHOUT_WRITER"
                                    : "LLM_SYMBOLIC_ROOT_EXCLUDED");
                }
                selected.add(retained);
            }
            return selected;
        }
    }

    private static final class CardBuilder {
        private final String candidateId;
        private final JsonObject semantic;
        private final boolean relationBound;
        private boolean symbolizable;
        private final Map<String, JsonObject> evidence = new TreeMap<>();

        private CardBuilder(String candidateId, JsonObject semantic,
                            boolean relationBound) {
            this.candidateId = candidateId;
            this.semantic = semantic.deepCopy();
            this.relationBound = relationBound;
        }

        private void observe(JsonObject context, JsonObject action,
                             JsonObject baseline, boolean eligible) {
            symbolizable |= eligible;
            JsonObject row = context.deepCopy();
            String port = firstNonempty(string(action, "portId"),
                    string(action, "symbol"));
            if (!port.isEmpty()) row.addProperty("sourcePortId", port);
            JsonObject reader = new JsonObject();
            for (String field : EVIDENCE_FIELDS) copy(reader, action, field);
            if (reader.size() > 0) row.add("reader", reader);
            String baselineDemand = string(baseline, "symbolicDemand");
            if (!baselineDemand.isEmpty()) {
                row.addProperty("manualBaselineDemand", baselineDemand);
            }
            String evidenceId = "ROOT_EVIDENCE."
                    + CanonicalJson.sha256(candidateId + "\n"
                    + CanonicalJson.render(row));
            row.addProperty("evidenceId", evidenceId);
            evidence.put(evidenceId, row);
        }

        private Card build() {
            return new Card(candidateId, semantic, symbolizable,
                    relationBound,
                    new ArrayList<>(evidence.values()));
        }
    }

    private static final class Card {
        private final String candidateId;
        private final JsonObject semantic;
        private final boolean symbolizable;
        private final boolean relationBound;
        private final List<JsonObject> evidence;
        private final Set<String> evidenceIds;

        private Card(String candidateId, JsonObject semantic,
                     boolean symbolizable, boolean relationBound,
                     List<JsonObject> evidence) {
            this.candidateId = candidateId;
            this.semantic = semantic.deepCopy();
            this.symbolizable = symbolizable;
            this.relationBound = relationBound;
            this.evidence = Collections.unmodifiableList(evidence);
            Set<String> ids = new LinkedHashSet<>();
            for (JsonObject row : evidence) ids.add(string(row, "evidenceId"));
            evidenceIds = Collections.unmodifiableSet(ids);
        }

        private JsonObject json() {
            JsonObject row = new JsonObject();
            row.addProperty("candidateId", candidateId);
            row.addProperty("symbolizable", symbolizable);
            row.addProperty("relationBound", relationBound);
            row.add("semantic", semantic.deepCopy());
            JsonArray ids = new JsonArray();
            JsonArray rows = new JsonArray();
            for (JsonObject item : evidence) {
                ids.add(string(item, "evidenceId"));
                rows.add(item.deepCopy());
            }
            row.add("evidenceIds", ids);
            row.add("evidence", rows);
            return row;
        }
    }

    private static String firstNonempty(String first, String second) {
        return first == null || first.isEmpty()
                ? second == null ? "" : second : first;
    }

    private static JsonArray canonicalFieldDeclarations(JsonObject action) {
        JsonArray result = new JsonArray();
        Set<String> represented = new LinkedHashSet<>();
        for (JsonElement element : arrayMember(action,
                "fieldPathDeclarations")) {
            if (element.isJsonPrimitive()
                    && element.getAsJsonPrimitive().isString()
                    && !element.getAsString().trim().isEmpty()
                    && represented.add(element.getAsString())) {
                result.add(element.deepCopy());
            }
        }
        if (result.size() == 0) {
            String value = firstNonempty(
                    string(action, "leafFieldSignature"), firstNonempty(
                    string(action, "declaredFieldSignature"), firstNonempty(
                    string(action, "accessFieldSignature"),
                    string(action, "fieldSignature"))));
            if (!value.isEmpty()) result.add(value);
        }
        return result;
    }

    private static Set<String> fieldDeclarations(JsonObject action) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : canonicalFieldDeclarations(action)) {
            result.add(element.getAsString());
        }
        return result;
    }

    private static Set<String> fixedFieldSignatures(JsonArray roots) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : roots == null ? new JsonArray() : roots) {
            if (!element.isJsonObject()) continue;
            String field = string(objectMember(element.getAsJsonObject(),
                    "semantic"), "fieldSignature");
            if (!field.isEmpty()) result.add(field);
        }
        return result;
    }

    private static JsonArray canonicalWriterAnchors(JsonElement encoded) {
        JsonArray source = encoded != null && encoded.isJsonArray()
                ? encoded.getAsJsonArray() : new JsonArray();
        Map<String, JsonObject> ordered = new TreeMap<>();
        for (JsonElement element : source) {
            if (!element.isJsonObject()
                    || element.getAsJsonObject().size() == 0) {
                throw new IllegalArgumentException(
                        "writer anchor must be a nonempty object");
            }
            JsonObject anchor = (JsonObject) CanonicalJson.copy(element);
            ordered.put(CanonicalJson.render(anchor), anchor);
        }
        JsonArray result = new JsonArray();
        for (JsonObject anchor : ordered.values()) result.add(anchor);
        return result;
    }

    private static void copy(JsonObject target, JsonObject source,
                             String field) {
        JsonElement value = source == null ? null : source.get(field);
        if (value != null && !value.isJsonNull()) {
            target.add(field, CanonicalJson.copy(value));
        }
    }

    private static String canonicalCell(String value) {
        return value == null ? "" : value.replaceAll("#call[0-9]+", "#call");
    }

}
