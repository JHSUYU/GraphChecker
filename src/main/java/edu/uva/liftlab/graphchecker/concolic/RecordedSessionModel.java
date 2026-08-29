package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.BiFunction;
import java.util.function.Function;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import edu.uva.liftlab.graphchecker.contract.PathObservation;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * The recorded session graph, projected onto one target and lowered into one
 */
public final class RecordedSessionModel {

    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "RECORDED_SESSION_MODEL";
    public static final String AUTHORITY =
            "RECORDED_SESSION_ORDER_DOMAIN_V1";

    /** Prefix of the one shared event-position variable family. */
    public static final String POSITION_PREFIX = "event_position__";
    /** Prefix of one guarded read-from selector. */
    public static final String SELECTOR_PREFIX = "rf_selector__";

    /** A sliced read whose cut could not be stated in the order domain. */
    public static final String UNORDERED_READ_CUT =
            "RECORDED_MODEL_UNORDERED_READ_CUT";
    /**
     * The admitted ledger's delivered relation is not a partial order.
     */
    public static final String ORDER_DOMAIN_CYCLE =
            "RECORDED_MODEL_ORDER_DOMAIN_CYCLE";

    /** Query member one path task carries the read cut in. */
    public static final String QUERY_FIELD = "recordedReadCut";
    /** Kind of that member. */
    public static final String QUERY_KIND = "RECORDED_READ_CUT_QUERY";

    /** Stable owner of evidence retained inside one guarded relation case. */
    public static final String CASE_OWNER = "caseOwner";
    /** SMT selector which enables that case-local evidence. */
    public static final String CASE_SELECTOR = "caseSelector";

    private final SessionTargetSlice.Slice slice;
    private final List<OrderVariable> positions = new ArrayList<>();
    private final List<String> selectors = new ArrayList<>();
    private final List<OrderAssertion> assertions = new ArrayList<>();
    private final List<JsonObject> coverageGaps = new ArrayList<>();
    private final JsonArray readChoices = new JsonArray();
    private final List<JsonObject> gatePlans = new ArrayList<>();
    private final Map<String, List<Long>> readEventsBySite;
    private final Map<Long, JsonObject> versionsByReadEvent;
    /** The read row itself, after case-local alpha-renaming. */
    private final Map<Long, JsonObject> readByReadEvent;
    /** The VM's authoritative writer row, addressed by its event/version id. */
    private final Map<Long, JsonObject> writerVersions;
    /** Reads performed by the selected target region. */
    private final Set<Long> targetReadEvents;
    /** Synthetic event id -> its replay/case-local identity. */
    private final Map<Long, EventIdentity> eventIdentities;
    /** Alpha-renamed VM event rows used to prove same-context ownership. */
    private final Map<Long, JsonObject> ledgerEvents;
    /** Exact replay/case scope and local VM id -> synthetic event id. */
    private final Map<String, Map<Long, Long>> eventIdsByScope;
    /**
     * <p>README {@code STATE-1}'s acceptance half asks one question of every
     */
    private final Map<Long, BoundedWriterUniverse> boundedWriterUniverses =
            new LinkedHashMap<>();
    /** LOOP_BODY_ROOT addresses whose declared a1..aK relation is closed. */
    private final Set<String> closedOccurrenceAddresses;
    private final int ledgerSnapshots;
    private final String orderDomainFault;
    private final Set<Long> choiceReadEvents = new LinkedHashSet<>();
    /** Arms proved impossible by their own sparse cut and recorded order. */
    private final Set<String> dominatedReadArmSelectors =
            new LinkedHashSet<>();
    /** README section 6's event-existence Booleans. */
    private final List<String> existenceSymbols = new ArrayList<>();
    /** Every guarded case represented by selected relation evidence. */
    private final Map<String, String> caseSelectors = new LinkedHashMap<>();
    /** Case selectors under which one recorded event was observed. */
    private final Map<Long, Set<String>> eventCaseSelectors =
            new LinkedHashMap<>();
    /** Events seen only inside guarded-case evidence. */
    private final Set<Long> caseEvidenceEvents = new LinkedHashSet<>();
    /** Events supplied by a selected top-level row rather than a case. */
    private final Set<Long> unguardedEvents = new LinkedHashSet<>();
    /** Compact audit rows for interaction/state/handoff case membership. */
    private final List<JsonObject> caseEvidence = new ArrayList<>();
    /** Exact selected case evidence, addressed by its alpha-renaming scope. */
    private final Map<String, CaseEvidence> caseEvidenceByScope =
            new LinkedHashMap<>();
    private boolean partial;

    private RecordedSessionModel(SessionTargetSlice.Slice slice,
                                 Map<String, List<Long>> readEventsBySite,
                                 Map<Long, JsonObject> versionsByReadEvent,
                                 Map<Long, JsonObject> readByReadEvent,
                                 Map<Long, JsonObject> writerVersions,
                                 Collection<Long> targetReadEvents,
                                 Map<Long, EventIdentity> eventIdentities,
                                 Map<Long, JsonObject> ledgerEvents,
                                 Map<String, Map<Long, Long>> eventIdsByScope,
                                 int ledgerSnapshots,
                                 String orderDomainFault,
                                 Collection<String> closedOccurrences) {
        this.slice = slice;
        this.readEventsBySite = readEventsBySite;
        this.versionsByReadEvent = versionsByReadEvent;
        this.readByReadEvent = readByReadEvent;
        this.writerVersions = writerVersions;
        this.targetReadEvents = Collections.unmodifiableSet(
                targetReadEvents == null ? new LinkedHashSet<Long>()
                        : new LinkedHashSet<>(targetReadEvents));
        this.eventIdentities = eventIdentities;
        this.ledgerEvents = ledgerEvents;
        this.eventIdsByScope = eventIdsByScope;
        this.ledgerSnapshots = ledgerSnapshots;
        this.orderDomainFault = orderDomainFault;
        this.closedOccurrenceAddresses = Collections.unmodifiableSet(
                closedOccurrences == null ? new LinkedHashSet<String>()
                        : new LinkedHashSet<>(closedOccurrences));
    }

    /** One bounded integer position in the shared order domain. */
    public static final class OrderVariable {
        public final String name;
        public final int bound;

        private OrderVariable(String name, int bound) {
            this.name = name;
            this.bound = bound;
        }
    }

    /** One named assertion over the shared order domain. */
    public static final class OrderAssertion {
        public final String name;
        public final String term;
        /** Empty for session-wide facts, otherwise the owning case formula. */
        public final String caseGuard;

        private OrderAssertion(String name, String term) {
            this(name, term, "");
        }

        private OrderAssertion(String name, String term, String caseGuard) {
            this.name = name;
            this.term = term;
            this.caseGuard = caseGuard == null ? "" : caseGuard;
        }
    }

    /**
     * One selected relation case, decoded once.
     *
     * <p>Wave 4 {@code CaseEvidence}.  The case's shared-state envelope, VM
     * handoff rows and interaction rows are read off the JSON here and
     * nowhere else; every later pass - ownership retention, the event
     * attribution sets, the manifest audit - reads these members.</p>
     */
    public static final class CaseEvidence {
        public final JsonObject row;
        public final JsonObject recorded;
        public final String owner;
        public final String selector;
        public final String regionId;
        public final String occurrenceId;
        public final String scope;
        public final List<JsonObject> handoffs;
        public final List<JsonObject> interactions;
        /** OCC-1: which activation of the address this case is, or 0. */
        public final int activationOrdinal;
        /** OCC-1: whether that activation satisfied its output boundary. */
        public final boolean activationComplete;

        private CaseEvidence(JsonObject row, String owner, String selector,
                             String regionId, String occurrenceId,
                             String scope) {
            this.row = row;
            this.recorded = object(row, SharedStateEvidence.RECORDED_FIELD);
            this.owner = owner;
            this.selector = selector;
            this.regionId = regionId;
            this.occurrenceId = occurrenceId;
            this.scope = scope;
            this.handoffs = VmHandoffEvidence.eventsOf(row);
            List<JsonObject> rows = new ArrayList<>();
            for (JsonElement element : array(row, "interactionEvents")) {
                if (element.isJsonObject()) rows.add(element.getAsJsonObject());
            }
            this.interactions = rows;
            this.activationOrdinal = integer(row,
                    PathObservation.ACTIVATION_ORDINAL, 0);
            this.activationComplete =
                    bool(row, "relationallyComplete", true);
        }

        /** Whether this case carries evidence the session model can state. */
        private boolean stated() {
            return recorded.size() > 0 || !handoffs.isEmpty()
                    || !interactions.isEmpty();
        }

        /** The same case after collision-free event alpha-renaming. */
        private CaseEvidence rescoped(JsonObject scopedRow, String scope) {
            return new CaseEvidence(scopedRow, owner, selector, regionId,
                    occurrenceId, scope);
        }
    }

    /** One local VM event after collision-free alpha-renaming. */
    private static final class EventIdentity {
        private final String scope;
        private final long localId;
        private final long syntheticId;
        private final boolean qualified;

        private EventIdentity(String scope, long localId, long syntheticId,
                              boolean qualified) {
            this.scope = scope;
            this.localId = localId;
            this.syntheticId = syntheticId;
            this.qualified = qualified;
        }

        private String solverToken() {
            if (!qualified) return String.valueOf(localId);
            String normalized = scope.replaceAll("[^A-Za-z0-9_]", "_");
            if (normalized.isEmpty()) normalized = "case";
            return normalized + "__"
                    + CanonicalJson.sha256(scope).substring(0, 10)
                    + "__" + localId;
        }
    }

    /** Public address of one case-local read used by a consumer binding. */
    public static final class ReadCase {
        public final long readEventId;
        public final String caseGuard;
        public final String resolution;
        public final long chosenFieldVersionId;

        private ReadCase(long readEventId, String caseGuard,
                         String resolution, long chosenFieldVersionId) {
            this.readEventId = readEventId;
            this.caseGuard = caseGuard == null ? "" : caseGuard;
            this.resolution = resolution == null ? "" : resolution;
            this.chosenFieldVersionId = chosenFieldVersionId;
        }
    }

    /** Unique selected case in which one RF arm's writer expression lives. */
    public static final class WriterOwnerResolution {
        public enum Status {
            UNIQUE,
            MISSING,
            AMBIGUOUS,
            READER_LOCAL
        }

        public final Status status;
        public final String owner;
        public final String regionId;
        public final String occurrenceId;
        public final List<String> candidates;
        public final String detail;

        private WriterOwnerResolution(Status status, String owner,
                                      String regionId, String occurrenceId,
                                      Collection<String> candidates,
                                      String detail) {
            this.status = status;
            this.owner = owner == null ? "" : owner;
            this.regionId = regionId == null ? "" : regionId;
            this.occurrenceId = occurrenceId == null ? "" : occurrenceId;
            this.candidates = Collections.unmodifiableList(
                    new ArrayList<>(candidates == null
                            ? Collections.<String>emptyList()
                            : candidates));
            this.detail = detail == null ? "" : detail;
        }

        public boolean usable() {
            return status == Status.UNIQUE || status == Status.READER_LOCAL;
        }
    }

    private static final class PreparedEvidence {
        private final List<CaseEvidence> owners;
        private final List<JsonObject> versionRecords;
        private final JsonObject ledgerEnvelope;
        private final JsonElement targetRoots;
        private final Map<Long, EventIdentity> identities;
        private final Map<String, Map<Long, Long>> idsByScope;
        private final int ledgerSnapshots;

        private PreparedEvidence(List<CaseEvidence> owners,
                                 List<JsonObject> versionRecords,
                                 JsonObject ledgerEnvelope,
                                 JsonElement targetRoots,
                                 Map<Long, EventIdentity> identities,
                                 Map<String, Map<Long, Long>> idsByScope,
                                 int ledgerSnapshots) {
            this.owners = owners;
            this.versionRecords = versionRecords;
            this.ledgerEnvelope = ledgerEnvelope;
            this.targetRoots = targetRoots;
            this.identities = identities;
            this.idsByScope = idsByScope;
            this.ledgerSnapshots = ledgerSnapshots;
        }
    }

    /**
     * Builds the model from the summaries selected for one composition.
     */
    public static RecordedSessionModel of(Collection<JsonObject> summaryRows,
                                          JsonElement targetPredicate,
                                          String targetRegionId) {
        return of(summaryRows, targetPredicate, targetRegionId,
                BoundedLoopComposition.empty());
    }

    /** Builds the model with the selected bounded-occurrence authority. */
    public static RecordedSessionModel of(Collection<JsonObject> summaryRows,
                                          JsonElement targetPredicate,
                                          String targetRegionId,
                                          BoundedLoopComposition loops) {
        PreparedEvidence prepared = prepareEvidence(
                evidenceOwners(summaryRows), targetPredicate, targetRegionId);
        List<JsonObject> versionRecords = prepared.versionRecords;
        Set<Long> targetReads = targetReads(versionRecords,
                targetRegionId);
        // README section 3 asks for send_req < receive_req in the one shared
        SessionTargetSlice.Slice slice = SessionTargetSlice.project(
                versionRecords, prepared.ledgerEnvelope,
                prepared.targetRoots, targetReads,
                handoffExportEventsOfOwners(prepared.owners));
        // A ledger that passed record admission and still delivered a cyclic
        // relation is refused by the order domain itself.  Reporting it here
        String fault = prepared.ledgerEnvelope == null ? ""
                : slice.orderDomain().fault();
        RecordedSessionModel model = new RecordedSessionModel(slice,
                readEventSites(versionRecords),
                versionsByReadEvent(versionRecords),
                readsByReadEvent(versionRecords),
                writerVersions(versionRecords), targetReads,
                prepared.identities,
                ledgerEvents(prepared.ledgerEnvelope),
                prepared.idsByScope, prepared.ledgerSnapshots, fault,
                loops == null ? Collections.<String>emptySet()
                        : loops.closedOccurrenceAddresses());
        model.retainCaseOwnership(prepared.owners);
        if (!fault.isEmpty()) {
            model.coverageGaps.add(gap(ORDER_DOMAIN_CYCLE, "", fault));
        }
        model.lower();
        return model;
    }

    private static PreparedEvidence prepareEvidence(
            List<CaseEvidence> original, JsonElement targetPredicate,
            String targetRegionId) {
        Map<String, Set<Long>> localIds = new LinkedHashMap<>();
        Map<Long, Set<String>> scopesById = new LinkedHashMap<>();
        List<String> scopes = new ArrayList<>();
        long maximum = 0L;
        for (int index = 0; index < original.size(); index++) {
            CaseEvidence owned = original.get(index);
            String scope = evidenceScope(owned, index);
            scopes.add(scope);
            Set<Long> ids = localIds.computeIfAbsent(scope,
                    ignored -> new TreeSet<>());
            collectEventIds(owned.row, ids);
            for (Long id : ids) {
                if (id == null || id <= 0L) continue;
                maximum = Math.max(maximum, id);
                scopesById.computeIfAbsent(id,
                        ignored -> new TreeSet<>()).add(scope);
            }
        }

        Map<String, Map<Long, Long>> idsByScope = new LinkedHashMap<>();
        Map<Long, EventIdentity> identities = new LinkedHashMap<>();
        long next = maximum;
        List<String> orderedScopes = new ArrayList<>(localIds.keySet());
        Collections.sort(orderedScopes);
        for (String scope : orderedScopes) {
            Map<Long, Long> mapping = new LinkedHashMap<>();
            idsByScope.put(scope, mapping);
            for (Long local : localIds.get(scope)) {
                boolean collision = scopesById.get(local).size() > 1;
                long synthetic = collision ? ++next : local;
                mapping.put(local, synthetic);
                identities.put(synthetic, new EventIdentity(scope, local,
                        synthetic, collision));
            }
        }

        List<CaseEvidence> rewritten = new ArrayList<>();
        JsonArray roots = new JsonArray();
        for (int index = 0; index < original.size(); index++) {
            CaseEvidence owned = original.get(index);
            String scope = scopes.get(index);
            JsonObject row = owned.row.deepCopy();
            rewriteEventIds(row, idsByScope.get(scope), scope);
            rewritten.add(owned.rescoped(row, scope));

            // Every case carries its own expression roots. Scanning the row is
            // conservative but bounded: the graph collector ignores metadata
            JsonObject localRoots = row.deepCopy();
            localRoots.remove(SharedStateEvidence.RECORDED_FIELD);
            roots.add(localRoots);
            // A target-path row already carries only that path's constraints.
            // Re-attaching the aggregate predicate would copy every other
            if (targetPredicate != null && !row.has("_targetPathOrdinal")
                    && (original.size() == 1
                    || targetRegionId != null
                    && targetRegionId.equals(owned.regionId))) {
                JsonElement target = targetPredicate.deepCopy();
                rewriteEventIds(target, idsByScope.get(scope), scope);
                roots.add(target);
            }
        }
        if (rewritten.isEmpty() && targetPredicate != null) {
            roots.add(targetPredicate.deepCopy());
        }

        Map<String, JsonObject> versions = new LinkedHashMap<>();
        Map<String, JsonObject> ledgers = new LinkedHashMap<>();
        int ledgerSnapshots = 0;
        for (CaseEvidence owned : rewritten) {
            for (JsonElement element : array(owned.recorded, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject record = element.getAsJsonObject();
                if (!SharedStateEvidence.isVersionsRecord(record)) continue;
                String key = owned.scope + "\n"
                        + string(record, "locationKey");
                if (SharedStateEvidence.later(record, versions.get(key))) {
                    versions.put(key, record);
                }
            }
            JsonObject snapshot = object(owned.recorded, "eventLedger");
            if (SharedStateEvidence.isLedgerRecord(snapshot)) {
                ledgerSnapshots++;
                if (SharedStateEvidence.later(snapshot,
                        ledgers.get(owned.scope))) {
                    ledgers.put(owned.scope, snapshot);
                }
            }
        }
        return new PreparedEvidence(rewritten,
                new ArrayList<>(versions.values()),
                mergeLedgerEnvelopes(ledgers.values()), roots, identities,
                idsByScope, ledgerSnapshots);
    }

    private static String evidenceScope(CaseEvidence owned, int ordinal) {
        if (!owned.owner.isEmpty()) return owned.owner;
        Set<String> sessions = new TreeSet<>();
        for (JsonElement element : array(owned.recorded, "versions")) {
            if (!element.isJsonObject()) continue;
            String session = string(object(element.getAsJsonObject(),
                    RecordedEvidenceIdentity.FIELD), "sessionId");
            if (!session.isEmpty()) sessions.add(session);
        }
        JsonObject ledger = object(owned.recorded, "eventLedger");
        String ledgerSession = string(object(ledger,
                RecordedEvidenceIdentity.FIELD), "sessionId");
        if (!ledgerSession.isEmpty()) sessions.add(ledgerSession);
        if (sessions.size() == 1) return "session:" + sessions.iterator().next();
        return "unowned:" + first(owned.regionId, "region") + "/"
                + first(owned.occurrenceId, "occurrence") + "/" + ordinal;
    }

    private static boolean eventIdMember(String member) {
        return "eventId".equals(member)
                || "fieldVersionId".equals(member)
                || "readEventId".equals(member)
                || "chosenFieldVersionId".equals(member)
                || "selectedEventId".equals(member)
                || "otherEventId".equals(member)
                || "beforeEventId".equals(member)
                || "afterEventId".equals(member)
                || "exportEventId".equals(member)
                || "attachEventId".equals(member);
    }

    private static void collectEventIds(JsonElement element, Set<Long> ids) {
        if (element == null || element.isJsonNull()) return;
        if (element.isJsonArray()) {
            for (JsonElement child : element.getAsJsonArray()) {
                collectEventIds(child, ids);
            }
            return;
        }
        if (!element.isJsonObject()) return;
        JsonObject object = element.getAsJsonObject();
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            if (eventIdMember(entry.getKey())
                    && entry.getValue().isJsonPrimitive()
                    && entry.getValue().getAsJsonPrimitive().isNumber()) {
                long id = entry.getValue().getAsLong();
                if (id > 0L) ids.add(id);
            } else {
                collectEventIds(entry.getValue(), ids);
            }
        }
    }

    private static void rewriteEventIds(JsonElement element,
                                        Map<Long, Long> mapping,
                                        String scope) {
        if (element == null || element.isJsonNull() || mapping == null) return;
        if (element.isJsonArray()) {
            for (JsonElement child : element.getAsJsonArray()) {
                rewriteEventIds(child, mapping, scope);
            }
            return;
        }
        if (!element.isJsonObject()) return;
        JsonObject object = element.getAsJsonObject();
        if (SharedStateEvidence.GUARDED_READ_TYPE.equals(
                string(object, "_type"))) {
            object.addProperty("recordedEventScope", scope);
        }
        for (String member : new ArrayList<>(object.keySet())) {
            JsonElement child = object.get(member);
            if (eventIdMember(member) && child != null
                    && child.isJsonPrimitive()
                    && child.getAsJsonPrimitive().isNumber()) {
                long local = child.getAsLong();
                Long synthetic = mapping.get(local);
                if (synthetic != null) object.addProperty(member, synthetic);
            } else {
                rewriteEventIds(child, mapping, scope);
            }
        }
    }

    /** Disjoint union of already-admitted, alpha-renamed ledger snapshots. */
    private static JsonObject mergeLedgerEnvelopes(
            Collection<JsonObject> records) {
        if (records == null || records.isEmpty()) return null;
        JsonArray events = new JsonArray();
        JsonArray order = new JsonArray();
        for (JsonObject record : records) {
            JsonObject envelope = object(record, "envelope");
            for (JsonElement event : array(envelope, "events")) {
                events.add(event.deepCopy());
            }
            for (JsonElement edge : array(envelope, "order")) {
                order.add(edge.deepCopy());
            }
        }
        JsonObject envelope = new JsonObject();
        envelope.addProperty("schemaVersion", SharedStateEvidence.SCHEMA_VERSION);
        envelope.addProperty("kind", SharedStateEvidence.LEDGER_ENVELOPE_KIND);
        envelope.addProperty("open", true);
        envelope.addProperty("recording", true);
        envelope.addProperty("truncated", false);
        envelope.addProperty("domainSaturated", false);
        envelope.addProperty("partialOrder", true);
        envelope.addProperty("acyclic", true);
        envelope.add("events", events);
        envelope.add("order", order);
        return envelope;
    }

    /**
     * The recorded read each activation performed of each watched location.
     */
    private static Map<String, List<Long>> readEventSites(
            Collection<JsonObject> records) {
        Map<String, List<Long>> bySite = new LinkedHashMap<>();
        for (JsonObject record : records) {
            JsonObject envelope = object(record, "envelope");
            String location = string(record, "locationKey");
            if (location.isEmpty()) {
                location = SharedStateEvidence.locationKey(envelope);
            }
            for (JsonElement element : array(envelope, "reads")) {
                JsonObject read = element.getAsJsonObject();
                String site = SharedStateEvidence.readerSite(read);
                if (location.isEmpty() || site.isEmpty()) continue;
                String key = location + "\n" + site;
                long event = longInteger(read, "readEventId", 0L);
                if (event > 0L) {
                    List<Long> events = bySite.computeIfAbsent(key,
                            ignored -> new ArrayList<>());
                    if (!events.contains(event)) events.add(event);
                }
            }
        }
        return bySite;
    }

    /**
     * The same admitted store under both of its legitimate addresses: the
     */
    private static Map<Long, JsonObject> versionsByReadEvent(
            Collection<JsonObject> records) {
        Map<Long, JsonObject> lookup = new LinkedHashMap<>();
        for (JsonObject record : records) {
            for (JsonElement element
                    : array(object(record, "envelope"), "reads")) {
                if (!element.isJsonObject()) continue;
                long event = longInteger(element.getAsJsonObject(),
                        "readEventId", 0L);
                if (event > 0L) lookup.put(event, record);
            }
        }
        return lookup;
    }

    /** The same one walk's read rows, addressed by their read event id. */
    private static Map<Long, JsonObject> readsByReadEvent(
            Collection<JsonObject> records) {
        Map<Long, JsonObject> lookup = new LinkedHashMap<>();
        for (JsonObject record : records) {
            for (JsonElement element
                    : array(object(record, "envelope"), "reads")) {
                if (!element.isJsonObject()) continue;
                JsonObject read = element.getAsJsonObject();
                long event = longInteger(read, "readEventId", 0L);
                if (event > 0L) lookup.put(event, read);
            }
        }
        return lookup;
    }

    /**
     * The declared field behind the location this read watched.
     */
    private String fieldOf(long readEventId) {
        JsonObject carrier = object(
                versionsByReadEvent.get(readEventId), "carrier");
        String field = RecordedReadFrom.fieldKey(
                string(carrier, "declaringClass"),
                string(carrier, "fieldName"));
        return field.isEmpty() ? null : field;
    }





    /**
     * Indexes writer metadata once from the admitted VM version envelopes.
     */
    private static Map<Long, JsonObject> writerVersions(
            Collection<JsonObject> records) {
        Map<Long, JsonObject> versions = new LinkedHashMap<>();
        Set<Long> ambiguous = new LinkedHashSet<>();
        for (JsonObject record : records) {
            JsonObject envelope = object(record, "envelope");
            for (JsonElement element : array(envelope, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject version = element.getAsJsonObject();
                long id = longInteger(version, "fieldVersionId", 0L);
                if (id <= 0L || ambiguous.contains(id)) continue;
                JsonObject previous = versions.get(id);
                if (previous == null || previous.equals(version)) {
                    versions.put(id, version);
                } else {
                    versions.remove(id);
                    ambiguous.add(id);
                }
            }
        }
        return versions;
    }

    private static Map<Long, JsonObject> ledgerEvents(JsonObject envelope) {
        Map<Long, JsonObject> events = new LinkedHashMap<>();
        for (JsonElement element : array(envelope, "events")) {
            if (!element.isJsonObject()) continue;
            JsonObject event = element.getAsJsonObject();
            long id = longInteger(event, "eventId", 0L);
            if (id > 0L) events.put(id, event.deepCopy());
        }
        return events;
    }

    /**
     * <p>README CASE-1 moved the state, container and ledger evidence of a
     */
    private static List<CaseEvidence> evidenceOwners(
            Collection<JsonObject> summaryRows) {
        List<CaseEvidence> members = new ArrayList<>();
        for (JsonObject summary : nonNull(summaryRows)) {
            String region = string(summary, "regionId");
            String occurrence = string(summary, "occurrenceId");
            String rowOwner = string(summary, CASE_OWNER);
            String rowSelector = string(summary, CASE_SELECTOR);
            if (!rowOwner.isEmpty()
                    && !rowSelector.equals(caseSelector(rowOwner))) {
                rowOwner = "";
                rowSelector = "";
            }
            addEvidenceOwner(summary, rowOwner, rowSelector, region,
                    occurrence, members);
            JsonArray cases = array(object(summary, "regionRelation"),
                    "cases");
            for (int index = 0; index < cases.size(); index++) {
                JsonElement element = cases.get(index);
                if (!element.isJsonObject()) continue;
                JsonObject item = element.getAsJsonObject();
                // OCC-1: the case's own occurrence when it states one.  This
                // string is the alpha-renaming scope for the case's VM event
                // ids, so two activations that share it would silently merge
                // two distinct real events onto one order-domain node.
                String stated = string(item, "occurrenceId");
                String caseOccurrence = stated.isEmpty()
                        ? occurrence : stated;
                String owner = caseOwner(region, caseOccurrence,
                        string(item, "caseId"), index);
                addEvidenceOwner(item, owner, caseSelector(owner), region,
                        caseOccurrence, members);
            }
        }
        return members;
    }

    private static void addEvidenceOwner(JsonObject row, String owner,
                                         String selector,
                                         String regionId,
                                         String occurrenceId,
                                         List<CaseEvidence> members) {
        CaseEvidence evidence = new CaseEvidence(row, owner, selector,
                regionId, occurrenceId, "");
        if (evidence.stated()) members.add(evidence);
    }

    /** Stable ownership key shared with the Composer's guarded case. */
    public static String caseOwner(String regionId, String occurrenceId,
                                   String caseId, int caseIndex) {
        return "region:" + text(regionId) + "/instance:"
                + text(occurrenceId) + "/case:"
                + first(caseId, String.valueOf(caseIndex));
    }

    /** The one SMT selector name used for this case and all of its evidence. */
    public static String caseSelector(String owner) {
        String identity = first(owner, "global");
        String normalized = identity.replaceAll("[^A-Za-z0-9_]", "_");
        if (normalized.isEmpty()) normalized = "anonymous";
        if (Character.isDigit(normalized.charAt(0))) {
            normalized = "n_" + normalized;
        }
        StringBuilder encoded = new StringBuilder();
        for (byte current : identity.getBytes(StandardCharsets.UTF_8)) {
            encoded.append(String.format(Locale.ROOT, "%02x",
                    current & 0xff));
        }
        return "case_selector__" + normalized + "__" + encoded;
    }

    /** Adds the explicit owner/selector pair to a case-local evidence row. */
    public static void writeCaseOwnership(JsonObject row, String owner) {
        if (row == null || owner == null || owner.isEmpty()) return;
        row.addProperty(CASE_OWNER, owner);
        row.addProperty(CASE_SELECTOR, caseSelector(owner));
    }

    private static String first(String first, String fallback) {
        return first == null || first.trim().isEmpty() ? fallback : first;
    }

    private static String text(String value) {
        return value == null ? "" : value;
    }

    private static Set<Long> handoffExportEventsOfOwners(
            Collection<CaseEvidence> owners) {
        Set<Long> events = new TreeSet<>();
        if (owners == null) return events;
        for (CaseEvidence owner : owners) {
            for (JsonObject handoff : owner.handoffs) {
                addEvent(events, handoff,
                        VmHandoffEvidence.EXPORT_EVENT_ID);
            }
        }
        return events;
    }

    /**
     * Retains the guarded case which supplied each interaction, state member
     */
    private void retainCaseOwnership(Collection<CaseEvidence> evidence) {
        for (CaseEvidence owned : evidence) {
            if (!owned.scope.isEmpty()) {
                caseEvidenceByScope.put(owned.scope, owned);
            }
            if (!owned.selector.isEmpty()) {
                caseSelectors.put(owned.owner, owned.selector);
                JsonObject audit = new JsonObject();
                audit.addProperty(CASE_OWNER, owned.owner);
                audit.addProperty(CASE_SELECTOR, owned.selector);
                audit.addProperty("regionId", owned.regionId);
                audit.addProperty("occurrenceId", owned.occurrenceId);
                audit.addProperty("interactionEvents",
                        owned.interactions.size());
                audit.addProperty("recordedSharedState",
                        owned.recorded.size() > 0);
                audit.addProperty("vmHandoffEvents", owned.handoffs.size());
                // OCC-1: an activation that satisfied only part of its output
                // boundary is composed as a case of what it did capture.
                // The mark travels here so the published manifest says which
                // occurrences were partial instead of leaving a reader to
                // infer it from an absent port.
                if (owned.activationOrdinal >= 1) {
                    audit.addProperty(
                            PathObservation.ACTIVATION_ORDINAL,
                            owned.activationOrdinal);
                    audit.addProperty("relationallyComplete",
                            owned.activationComplete);
                }
                caseEvidence.add(audit);
            }
            if (!owned.selector.isEmpty()) {
                caseEvidenceEvents.addAll(evidenceEvents(owned, false));
            }
            // A case-local snapshot is a fact of that replay case as a whole,
            // not only of events whose writer/reader occurrence equals the
            Set<Long> events = evidenceEvents(owned,
                    owned.selector.isEmpty());
            for (Long event : events) {
                if (event == null || event.longValue() <= 0L) continue;
                if (owned.selector.isEmpty()) {
                    unguardedEvents.add(event);
                    eventCaseSelectors.remove(event);
                } else if (!unguardedEvents.contains(event)) {
                    eventCaseSelectors.computeIfAbsent(event,
                            ignored -> new LinkedHashSet<>()).add(
                            owned.selector);
                }
            }
        }
        // A case-local VM reference names the export.  The ledger remains the
        // sole authority for its attach endpoint; copy only the case
        for (JsonObject edge : slice.order()) {
            if (!"VALUE_HANDOFF".equals(string(edge, "edgeKind"))) continue;
            long before = longInteger(edge, "beforeEventId", 0L);
            long after = longInteger(edge, "afterEventId", 0L);
            if (unguardedEvents.contains(before)) {
                unguardedEvents.add(after);
                eventCaseSelectors.remove(after);
                continue;
            }
            Set<String> selectors = eventCaseSelectors.get(before);
            if (selectors != null && !selectors.isEmpty()
                    && !unguardedEvents.contains(after)) {
                eventCaseSelectors.computeIfAbsent(after,
                        ignored -> new LinkedHashSet<>()).addAll(selectors);
            }
        }
    }

    /**
     * The explicit state/handoff ids one case carries.  With {@code owned}
     * the version and read halves are narrowed to the writes and reads this
     * occurrence itself performed; the handoff and interaction halves are
     * the case's evidence either way.
     */
    private static Set<Long> evidenceEvents(CaseEvidence evidence,
                                            boolean owned) {
        Set<Long> events = new LinkedHashSet<>();
        String occurrence = owned ? evidence.occurrenceId : null;
        for (JsonElement member : array(evidence.recorded, "versions")) {
            if (!member.isJsonObject()) continue;
            JsonObject envelope = object(member.getAsJsonObject(), "envelope");
            addStateEvents(events, array(envelope, "versions"),
                    "fieldVersionId", occurrence,
                    SharedStateEvidence.WRITER_OCCURRENCE_ID);
            addStateEvents(events, array(envelope, "reads"), "readEventId",
                    occurrence, SharedStateEvidence.READER_OCCURRENCE_ID);
        }
        for (JsonObject handoff : evidence.handoffs) {
            addEvent(events, handoff, VmHandoffEvidence.EXPORT_EVENT_ID);
        }
        for (JsonObject interaction : evidence.interactions) {
            addEvent(events, interaction, "eventId");
            addEvent(events, interaction, VmHandoffEvidence.EXPORT_EVENT_ID);
        }
        return events;
    }

    private static void addStateEvents(Set<Long> events, JsonArray rows,
                                       String member, String occurrenceId,
                                       String occurrenceMember) {
        for (JsonElement element : rows) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if (occurrenceId != null && !occurrenceId.equals(
                    string(row, occurrenceMember))) {
                continue;
            }
            addEvent(events, row, member);
        }
    }

    private static void addEvent(Set<Long> events, JsonObject row,
                                 String member) {
        long event = longInteger(row, member, 0L);
        if (event > 0L) events.add(event);
    }

    private String caseGuard(long... events) {
        List<String> conjuncts = new ArrayList<>();
        for (long event : events) {
            if (event <= 0L || unguardedEvents.contains(event)) continue;
            Set<String> selectors = eventCaseSelectors.get(event);
            if (selectors == null || selectors.isEmpty()) {
                if (caseEvidenceEvents.contains(event)
                        && !conjuncts.contains("false")) {
                    conjuncts.add("false");
                }
                continue;
            }
            String guard = selectors.size() == 1
                    ? selectors.iterator().next()
                    : disjunction(selectors);
            if (!conjuncts.contains(guard)) conjuncts.add(guard);
        }
        if (conjuncts.isEmpty()) return "";
        if (conjuncts.size() == 1) return conjuncts.get(0);
        StringBuilder term = new StringBuilder("(and");
        for (String guard : conjuncts) term.append(' ').append(guard);
        return term.append(')').toString();
    }

    /** Resolves one VM-local id only inside its exact replay/case domain. */
    public long resolveEventId(String scope, long eventId) {
        if (eventId <= 0L) return 0L;
        String exactScope = scope == null ? "" : scope;
        EventIdentity already = eventIdentities.get(eventId);
        if (already != null) {
            // A synthetic id is still owned by one exact replay.  Supplying it
            // under another replay's scope is a mismatch, not permission to
            // rename it.
            return already.scope.equals(exactScope) ? eventId : 0L;
        }
        Map<Long, Long> exact = eventIdsByScope.get(exactScope);
        Long resolved = exact == null ? null : exact.get(eventId);
        return resolved == null ? 0L : resolved;
    }

    /**
     * Rehomes a copied expression's already-alpha-renamed event id in the
     * exact producer scope which owns that expression.
     */
    public long resolveExpressionEventId(String scope, long eventId) {
        if (eventId <= 0L) return 0L;
        EventIdentity copied = eventIdentities.get(eventId);
        long local = copied == null ? eventId : copied.localId;
        return resolveEventId(scope, local);
    }

    /** Resolves another local event in the same replay as {@code read}. */
    public long resolveEventForRead(long read, long localEventId) {
        EventIdentity identity = eventIdentities.get(read);
        return identity == null ? 0L
                : resolveEventId(identity.scope, localEventId);
    }

    /**
     * Restores the replay-local event names of a copied expression.
     *
     * <p>Composition alpha-renames event ids so different replay cases remain
     * disjoint in the order domain.  Structural value identity, however, is
     * compared with the producer's original output expression.  This copy
     * removes only that bookkeeping rename and its scope annotation; the
     * expression used for SMT lowering remains untouched.</p>
     */
    public JsonElement localEventExpression(JsonElement expression) {
        JsonElement restored = expression == null
                ? null : expression.deepCopy();
        restoreLocalEventIds(restored);
        return restored;
    }

    private void restoreLocalEventIds(JsonElement element) {
        if (element == null || element.isJsonNull()) return;
        if (element.isJsonArray()) {
            for (JsonElement child : element.getAsJsonArray()) {
                restoreLocalEventIds(child);
            }
            return;
        }
        if (!element.isJsonObject()) return;
        JsonObject object = element.getAsJsonObject();
        object.remove("recordedEventScope");
        for (String member : new ArrayList<>(object.keySet())) {
            JsonElement child = object.get(member);
            if (eventIdMember(member) && child != null
                    && child.isJsonPrimitive()
                    && child.getAsJsonPrimitive().isNumber()) {
                EventIdentity identity = eventIdentities.get(
                        child.getAsLong());
                if (identity != null) {
                    object.addProperty(member, identity.localId);
                }
            } else {
                restoreLocalEventIds(child);
            }
        }
    }

    private static String disjunction(Collection<String> selectors) {
        if (selectors == null || selectors.isEmpty()) return "false";
        if (selectors.size() == 1) return selectors.iterator().next();
        StringBuilder term = new StringBuilder("(or");
        for (String selector : selectors) term.append(' ').append(selector);
        return term.append(')').toString();
    }

    /**
     * anything else.  README {@code RPC-1}: one export may be attached at
     */
    public String handoffOrderAssertion(long exportEventId,
                                        long attachEventId,
                                        String caseSelector) {
        if (exportEventId <= 0L || attachEventId <= 0L) return "";
        String scope = caseScope(caseSelector);
        long exportEvent = scopedEventId(scope, exportEventId);
        long attachEvent = scopedEventId(scope, attachEventId);
        if (!caseOwnsEvent(exportEvent, caseSelector)) return "";
        if (!handoffEdgeRecorded(exportEvent, attachEvent)) return "";
        return "recorded_order__" + eventToken(exportEvent) + "__"
                + eventToken(attachEvent);
    }

    /** The evidence scope one case selector owns, or the unscoped domain. */
    private String caseScope(String caseSelector) {
        if (caseSelector == null || caseSelector.isEmpty()) return "";
        for (Map.Entry<String, String> entry : caseSelectors.entrySet()) {
            if (caseSelector.equals(entry.getValue())) return entry.getKey();
        }
        return "";
    }

    /** One replay-local id inside its own scope, or the id as supplied. */
    private long scopedEventId(String scope, long eventId) {
        long scoped = resolveEventId(scope, eventId);
        return scoped > 0L ? scoped : eventId;
    }

    /** Whether this case carried the evidence that named {@code eventId}. */
    private boolean caseOwnsEvent(long eventId, String caseSelector) {
        if (caseSelector == null || caseSelector.isEmpty()) return true;
        if (unguardedEvents.contains(eventId)) return true;
        Set<String> owners = eventCaseSelectors.get(eventId);
        return owners != null && owners.contains(caseSelector);
    }

    /** Whether the recorded domain holds this exact VALUE_HANDOFF edge. */
    private boolean handoffEdgeRecorded(long exportEvent, long attachEvent) {
        for (JsonObject edge : slice.order()) {
            if ("VALUE_HANDOFF".equals(string(edge, "edgeKind"))
                    && longInteger(edge, "beforeEventId", 0L) == exportEvent
                    && longInteger(edge, "afterEventId", 0L) == attachEvent) {
                return true;
            }
        }
        return false;
    }



    /**
     * The recorded reads the target region performed.
     */
    private static Set<Long> targetReads(Collection<JsonObject> records,
                                         String targetRegionId) {
        Set<Long> reads = new TreeSet<>();
        if (targetRegionId == null || targetRegionId.isEmpty()) return reads;
        for (JsonObject record : records) {
            for (JsonElement element
                    : array(object(record, "envelope"), "reads")) {
                JsonObject read = element.getAsJsonObject();
                if (targetRegionId.equals(string(read, "regionId"))) {
                    reads.add(longInteger(read, "readEventId", 0L));
                }
            }
        }
        return reads;
    }

    private void lower() {
        // A guarded read is partial only while its bounded writer universe is
        // open. A dense declared LOOP_BODY_ROOT prefix can close that axis.
        partial = false;
        for (JsonObject recorded : slice.gaps()) {
            String reason = string(recorded, "reason");
            if (SessionTargetSlice.UNRECORDED_CANDIDATE_SET.equals(reason)
                    || SessionTargetSlice.INCOMPLETE_WRITER_SET.equals(reason)
                    || SessionTargetSlice.UNRECORDED_READ.equals(reason)) {
                partial = true;
            }
        }
        Set<Long> events = slice.eventIds();
        if (events.isEmpty()) return;
        int bound = events.size();
        for (Long event : events) {
            positions.add(new OrderVariable(positionFor(event), bound));
        }
        for (JsonObject edge : slice.order()) {
            long before = longInteger(edge, "beforeEventId", 0L);
            long after = longInteger(edge, "afterEventId", 0L);
            assertions.add(new OrderAssertion(
                    "recorded_order__" + eventToken(before) + "__"
                            + eventToken(after),
                    "(< " + positionFor(before) + " "
                            + positionFor(after) + ")",
                    caseGuard(before, after)));
        }
        for (Map.Entry<Long, JsonObject> entry
                : slice.guardedReads().entrySet()) {
            lowerReadCut(entry.getKey(), entry.getValue(), events);
        }
    }

    /**
     * Declares one event's existence Boolean and records what the run
     */
    private String existence(long eventId, boolean recordedPresent) {
        String name = scopedExistenceName(eventId);
        if (existenceSymbols.contains(name)) return name;
        existenceSymbols.add(name);
        String guard = recordedPresent ? caseGuard(eventId) : "";
        assertions.add(new OrderAssertion("recorded_event_exists__" + eventId,
                recordedPresent && !guard.isEmpty()
                        ? "(= " + name + " " + guard + ")"
                        : recordedPresent ? name : "(not " + name + ")"));
        return name;
    }

    public String scopedExistenceName(long eventId) {
        return "event_exists__" + eventToken(eventId);
    }


    public String scopedReadExistsName(long readEventId) {
        return "read_exists__" + eventToken(readEventId);
    }

    /** Every {@code exists(...)} Boolean this model states. */
    public List<String> existenceSymbols() {
        return Collections.unmodifiableList(existenceSymbols);
    }

    /**
     * Lowers one guarded read into its selectors and its sparse read cut.
     */
    private void lowerReadCut(long readEventId, JsonObject guarded,
                              Set<Long> events) {
        // The set this read chooses from is enumerated before anything is
        String location = SharedStateEvidence.locationKey(guarded);
        BoundedWriterUniverse universe = BoundedWriterUniverse.of(guarded,
                versionsByReadEvent.get(readEventId),
                closedOccurrenceAddresses);
        boundedWriterUniverses.put(readEventId, universe);
        coverageGaps.addAll(universe.gaps());
        if (universe.retainsUnknownArm()) partial = true;
        if (!events.contains(readEventId)) {
            coverageGaps.add(gap(UNORDERED_READ_CUT, location,
                    "read " + readEventId
                            + " has no position in the order domain"));
            return;
        }
        List<String> armSelectors = new ArrayList<>();
        JsonArray choice = new JsonArray();
        List<ReadArm<Object>> readArms = armsOf(readEventId,
                array(guarded, "candidates"), null);
        ReadArm<Object> maximalTargetWriter =
                maximalTargetWriter(readEventId, readArms);
        for (ReadArm<Object> candidateArm : readArms) {
            JsonObject candidate = candidateArm.candidate;
            String selector = candidateArm.selector;
            selectors.add(selector);
            armSelectors.add(selector);
            JsonObject row = new JsonObject();
            row.addProperty("selector", selector);
            row.addProperty("arm", candidateArm.arm);
            row.addProperty("readEventId", readEventId);
            row.addProperty("unknown", candidateArm.unknown);
            row.addProperty("fieldVersionId", candidateArm.writerEventId);
            // Wave 3 B: the arm list IS the developer-facing explanation of
            // a read, so every arm names the write it would take.  The
            // version id and the writer's ledger event are the same event -
            // stated under both names so a reader need not know that.
            row.addProperty("writerEventId", candidateArm.writerEventId);
            if (maximalTargetWriter != null && !candidateArm.unknown) {
                if (candidateArm == maximalTargetWriter) {
                    row.addProperty("targetMaximalWriter", true);
                    row.addProperty("maximalWriterAssertion",
                            "recorded_target_maximal_writer__"
                                    + eventToken(readEventId) + "__"
                                    + eventToken(candidateArm.writerEventId));
                } else {
                    dominatedReadArmSelectors.add(selector);
                    row.addProperty("valueTermPruned", true);
                    row.addProperty("dominatedByEventId",
                            maximalTargetWriter.writerEventId);
                    row.addProperty("dominanceAuthority",
                            "TARGET_READ_UNIQUE_MAXIMAL_WRITER_V1");
                }
            }
            choice.add(row);
            if (candidateArm.unknown) {
                row.addProperty("writerExists", false);
                continue;
            }
            long version = candidateArm.writerEventId;
            // Writer existence.  A candidate write the one order domain does
            // not hold is a write this model cannot place at all, so the arm
            row.addProperty("writerExists", events.contains(version));
            // README section 6's event-existence implication, and README
            row.addProperty("existenceSymbol", existence(version,
                    events.contains(version)));
            assertions.add(new OrderAssertion(
                    "recorded_write_exists__" + eventToken(readEventId)
                            + "__" + eventToken(version),
                    "(=> " + selector + " "
                            + scopedExistenceName(version) + ")"));
            if (!events.contains(version)) {
                coverageGaps.add(gap(UNORDERED_READ_CUT,
                        SharedStateEvidence.locationKey(guarded),
                        "candidate write " + version + " of read "
                                + readEventId
                                + " has no position in the order domain"));
                // Kept beside the existence pair that now derives it.  This
                // is the named refusal a reader and the audit look for, and
                assertions.add(new OrderAssertion(
                        "recorded_write_absent__" + readEventId + "__"
                                + version, "(not " + selector + ")"));
                continue;
            }
            assertions.add(new OrderAssertion(
                    "recorded_read_cut__" + eventToken(readEventId) + "__"
                            + eventToken(version),
                    "(=> " + selector + " (< " + positionFor(version) + " "
                            + positionFor(readEventId) + "))"));
            Long dominatedBy = null;
            for (JsonElement other : array(candidate, "orderConstraints")) {
                JsonObject constraint = other.getAsJsonObject();
                if (!"OTHER_WRITE_OUTSIDE_CUT".equals(
                        string(constraint, "kind"))) {
                    continue;
                }
                long competitor = longInteger(constraint, "otherEventId", 0L);
                if (!events.contains(competitor)) continue;
                assertions.add(new OrderAssertion(
                        "recorded_read_cut_outside__" + eventToken(readEventId)
                                + "__" + eventToken(version) + "__"
                                + eventToken(competitor),
                        "(=> " + selector + " (or (< "
                                + positionFor(competitor) + " "
                                + positionFor(version) + ") (< "
                                + positionFor(readEventId) + " "
                                + positionFor(competitor) + ")))"));
                if (dominatedBy == null
                        && slice.orderDomain().orderedBefore(version,
                        competitor)
                        && slice.orderDomain().orderedBefore(competitor,
                        readEventId)) {
                    dominatedBy = competitor;
                }
            }
            if (dominatedBy != null) {
                // This is a derived unit, not a heuristic pin.  The recorded
                // order states version < dominating-write < read, while the
                // sparse cut for this arm requires the dominating write to be
                // outside (version, read).  Under the three events' cases the
                // arm is therefore impossible.  State that consequence once
                // so the solver need not rediscover it through integer order
                // variables before simplifying a large writer expression.
                String assertion = "recorded_read_cut_dominated__"
                        + eventToken(readEventId) + "__"
                        + eventToken(version) + "__"
                        + eventToken(dominatedBy);
                String dominanceGuard = caseGuard(version, dominatedBy,
                        readEventId);
                assertions.add(new OrderAssertion(assertion,
                        "(not " + selector + ")", dominanceGuard));
                row.addProperty("dominatedByEventId", dominatedBy);
                row.addProperty("dominanceAssertion", assertion);
                // When the dominance guard is exactly the read's guard,
                // selector => read_exists makes this arm false everywhere.
                // Composer may therefore replace its otherwise enormous value
                // expression with a neutral term without changing any model.
                if (dominanceGuard.equals(caseGuard(readEventId))) {
                    dominatedReadArmSelectors.add(selector);
                    row.addProperty("valueTermPruned", true);
                }
            }
        }
        // Which of these arms replay could actually observe is knowable now,
        // from the same recorded order the choice is stated over. Learning it
        SparseReadCutGate plan = SparseReadCutGate.compile(guarded,
                slice.orderDomain(), fieldOf(readEventId));
        gatePlans.add(plan.toJson());
        coverageGaps.addAll(plan.refusals());
        for (JsonElement element : choice) {
            JsonObject row = element.getAsJsonObject();
            row.addProperty("enforceable",
                    plan.gateFor(string(row, "arm")).size() > 0);
        }
        if (armSelectors.isEmpty()) return;
        // README {@code READ-1}: the choice belongs to the read, and the read
        String exists = scopedReadExistsName(readEventId);
        if (!existenceSymbols.contains(exists)) existenceSymbols.add(exists);
        StringBuilder exactlyOne = new StringBuilder("(= (+");
        for (int index = 0; index < armSelectors.size(); index++) {
            String selector = armSelectors.get(index);
            exactlyOne.append(" (ite ").append(selector).append(" 1 0)");
            assertions.add(new OrderAssertion(
                    "recorded_read_arm_exists__" + readEventId + "__" + index,
                    "(=> " + selector + " " + exists + ")"));
        }
        exactlyOne.append(") 1)");
        assertions.add(new OrderAssertion(
                "recorded_read_choice__" + readEventId,
                "(=> " + exists + " " + exactlyOne + ")"));
        if (maximalTargetWriter != null) {
            assertions.add(new OrderAssertion(
                    "recorded_target_maximal_writer__"
                            + eventToken(readEventId) + "__"
                            + eventToken(maximalTargetWriter.writerEventId),
                    "(=> " + exists + " "
                            + maximalTargetWriter.selector + ")"));
        }
        choiceReadEvents.add(readEventId);
        JsonObject read = new JsonObject();
        read.addProperty("readEventId", readEventId);
        read.addProperty("existenceSymbol", exists);
        read.addProperty("locationKey", location);
        read.addProperty("locationKind",
                SharedStateEvidence.locationKindOf(location));
        read.addProperty("reason", string(guarded, "reason"));
        read.addProperty("writerSetComplete",
                bool(guarded, "writerSetComplete", false));
        read.addProperty("writerUniverseClosed", universe.closed());
        read.add("candidates", choice);
        readChoices.add(read);
    }

    /**
     * Selects the completed state of one target-local writer activation.
     *
     * <p>This is an existential witness strengthening, not a latest-by-id
     * guess: every mutating candidate must have the same exact case owner,
     * any initial-state arm must be reader-local, and the recorded order must
     * prove one unique writer follows every other candidate. Selecting it
     * states the schedule in which that activation finished updating the
     * shared field before the target read.</p>
     */
    private ReadArm<Object> maximalTargetWriter(
            long readEventId, List<ReadArm<Object>> arms) {
        if (!targetReadEvents.contains(readEventId)) return null;
        List<ReadArm<Object>> known = new ArrayList<>();
        String owner = "";
        for (ReadArm<Object> arm : arms) {
            if (arm.unknown) continue;
            if (arm.writerEventId <= 0L || arm.expressionOwner == null) {
                return null;
            }
            JsonObject version = writerVersion(arm.writerEventId);
            if ("INITIAL".equals(string(version, "versionKind"))) {
                if (arm.expressionOwner.status
                        != WriterOwnerResolution.Status.READER_LOCAL) {
                    return null;
                }
                known.add(arm);
                continue;
            }
            if (arm.expressionOwner.status
                    != WriterOwnerResolution.Status.UNIQUE
                    || arm.expressionOwner.owner.isEmpty()) {
                return null;
            }
            if (owner.isEmpty()) owner = arm.expressionOwner.owner;
            else if (!owner.equals(arm.expressionOwner.owner)) return null;
            known.add(arm);
        }
        if (known.size() < 2) return null;
        ReadArm<Object> winner = null;
        for (ReadArm<Object> candidate : known) {
            boolean followsAll = true;
            for (ReadArm<Object> other : known) {
                if (candidate == other) continue;
                if (!slice.orderDomain().orderedBefore(other.writerEventId,
                        candidate.writerEventId)) {
                    followsAll = false;
                    break;
                }
            }
            if (!followsAll) continue;
            if (winner != null) return null;
            winner = candidate;
        }
        return winner;
    }

    private String eventToken(long eventId) {
        EventIdentity identity = eventIdentities.get(eventId);
        return identity == null ? String.valueOf(eventId)
                : identity.solverToken();
    }

    private String positionFor(long eventId) {
        return POSITION_PREFIX + eventToken(eventId);
    }

    public String scopedPositionName(long eventId) {
        return positionFor(eventId);
    }

    public String scopedSelectorName(long readEventId, String arm) {
        return selectorNameToken(eventToken(readEventId), arm);
    }

    /**
     * One arm of one recorded read, as every layer that lowers it sees it.
     *
     * <p>The order domain, the value lowering and the container state
     * binding all used to re-derive the same four facts from the same
     * candidate object, each with its own spelling of "the selector of this
     * arm".  They are derived once, here.  {@code term} is what the caller's
     * own lowering made of the arm - the Composer's SMT term - so the arms
     * are walked once and no caller has to zip two lists by index.</p>
     */
    public static final class ReadArm<T> {
        public final String arm;
        public final String selector;
        public final boolean unknown;
        public final long writerEventId;
        public final JsonObject candidate;
        public final WriterOwnerResolution expressionOwner;
        public final T term;

        private ReadArm(String selector, JsonObject candidate,
                        WriterOwnerResolution expressionOwner, T term) {
            this.arm = string(candidate, "selector");
            this.selector = selector;
            this.unknown = bool(candidate, "unknown", false);
            this.writerEventId = longInteger(candidate, "fieldVersionId",
                    0L);
            this.candidate = candidate;
            this.expressionOwner = expressionOwner;
            this.term = term;
        }
    }

    /**
     * The arms of one recorded read, in the order the VM recorded them,
     * each carrying what {@code lowering} made of it.  A caller with nothing
     * to lower passes {@code null}.
     */
    public <T> List<ReadArm<T>> armsOf(long readEventId,
                                       JsonArray candidates,
                                       Function<JsonObject, T> lowering) {
        return armsOfWithWriterOwners(readEventId, candidates,
                (candidate, ignored) -> lowering == null
                        ? null : lowering.apply(candidate));
    }

    /** The same arm walk with the exact writer expression owner exposed. */
    public <T> List<ReadArm<T>> armsOfWithWriterOwners(
            long readEventId, JsonArray candidates,
            BiFunction<JsonObject, WriterOwnerResolution, T> lowering) {
        List<ReadArm<T>> arms = new ArrayList<>();
        for (JsonElement element : candidates) {
            if (!element.isJsonObject()) continue;
            JsonObject candidate = element.getAsJsonObject();
            WriterOwnerResolution owner = writerExpressionOwnerForRead(
                    readEventId, candidate);
            arms.add(new ReadArm<>(scopedSelectorName(readEventId,
                    string(candidate, "selector")), candidate, owner,
                    lowering == null ? null : lowering.apply(candidate,
                            owner)));
        }
        return arms;
    }

    /** The one Boolean that selects arm {@code arm} of one recorded read. */
    static String selectorNameToken(String readToken, String arm) {
        String sanitized = arm.replaceAll("[^A-Za-z0-9_]", "_");
        // Admission separates the arms by their raw selector, so the SMT name
        return SELECTOR_PREFIX + readToken + "__" + sanitized
                + (sanitized.equals(arm) ? ""
                : "__" + CanonicalJson.sha256(arm).substring(0, 8));
    }

    private static JsonObject gap(String reason, String locationKey,
                                  String detail) {
        JsonObject gap = new JsonObject();
        gap.addProperty("kind", SessionTargetSlice.GAP_KIND);
        gap.addProperty("schemaVersion", SCHEMA_VERSION);
        gap.addProperty("reason", reason);
        gap.addProperty("authority", SessionTargetSlice.GAP_AUTHORITY);
        gap.addProperty("locationKey", locationKey);
        gap.addProperty("detail", detail);
        return gap;
    }

    private static Collection<JsonObject> nonNull(
            Collection<JsonObject> rows) {
        return rows == null ? Collections.<JsonObject>emptyList() : rows;
    }

    public SessionTargetSlice.Slice slice() {
        return slice;
    }

    /**
     * How many recorded reads this model was built over.
     */
    public int recordedReadCount() {
        int count = 0;
        for (List<Long> events : readEventsBySite.values()) count += events.size();
        return count;
    }

    /**
     * Whether this model is an under-approximation of the run.
     */
    public boolean partial() {
        return partial;
    }

    /** Why the recorded order domain was refused, or "". */
    public String orderDomainFault() {
        return orderDomainFault;
    }

    /** Reads whose exactly-one selection this model already asserted. */
    public Set<Long> choiceReadEvents() {
        return Collections.unmodifiableSet(choiceReadEvents);
    }

    /** Whether the recorded order and sparse cut prove this arm unreachable. */
    public boolean readArmValueTermPruned(long readEventId, String arm) {
        return dominatedReadArmSelectors.contains(
                scopedSelectorName(readEventId, arm));
    }

    /** The guarded read-from terms of the sliced reads, by read event. */
    public Map<Long, JsonObject> guardedReads() {
        return slice.guardedReads();
    }

    /** Whether one event has a position in the shared order domain. */
    public boolean ordersEvent(long eventId) {
        return slice.eventIds().contains(eventId);
    }

    /** Every mutually-exclusive replay case that performed this exact read. */
    public List<ReadCase> readCasesOf(String locationKey, String readerSite) {
        if (locationKey == null || readerSite == null
                || locationKey.isEmpty() || readerSite.isEmpty()) {
            return Collections.emptyList();
        }
        List<Long> events = readEventsBySite.get(
                locationKey + "\n" + readerSite);
        if (events == null) return Collections.emptyList();
        List<ReadCase> cases = new ArrayList<>();
        for (Long event : events) {
            if (event != null && event > 0L) {
                cases.add(new ReadCase(event, caseGuard(event),
                        string(readByReadEvent.get(event), "resolution"),
                        longInteger(readByReadEvent.get(event),
                                "chosenFieldVersionId", 0L)));
            }
        }
        return Collections.unmodifiableList(cases);
    }

    /** Only guarded alternatives; exact reads have no selector value term. */
    public List<ReadCase> guardedReadCasesOf(String locationKey,
                                             String readerSite) {
        List<ReadCase> result = new ArrayList<>();
        for (ReadCase readCase : readCasesOf(locationKey, readerSite)) {
            if (SharedStateEvidence.RESOLUTION_GUARDED.equals(
                    readCase.resolution)
                    && guardedReads().containsKey(readCase.readEventId)) {
                result.add(readCase);
            }
        }
        return Collections.unmodifiableList(result);
    }

    /**
     * Every case-local read of one VM store by one planned reader address.
     *
     * <p>Canonical location keys include the exact activation so that normal
     * joins cannot accidentally merge two executions.  A selected composed
     * edge can nevertheless address several mutually-exclusive target cases
     * of the same store.  This method joins only on the VM's session location
     * identity and the planned reader address; the returned guards retain the
     * cases as separate alternatives.</p>
     */
    public List<ReadCase> readCasesOfSessionLocation(
            String sessionLocationKey, String readerSite) {
        if (sessionLocationKey == null || readerSite == null
                || sessionLocationKey.isEmpty() || readerSite.isEmpty()) {
            return Collections.emptyList();
        }
        String plannedReader = PathObservation.plannedOccurrenceOf(
                readerSite);
        List<Long> events = new ArrayList<>();
        for (Map.Entry<Long, JsonObject> entry : readByReadEvent.entrySet()) {
            JsonObject record = versionsByReadEvent.get(entry.getKey());
            if (record == null || !sessionLocationKey.equals(
                    SharedStateEvidence.sessionLocationKey(record))) {
                continue;
            }
            String recordedReader = SharedStateEvidence.readerSite(
                    entry.getValue());
            if (!readerSite.equals(recordedReader)
                    && !plannedReader.equals(
                    PathObservation.plannedOccurrenceOf(recordedReader))) {
                continue;
            }
            events.add(entry.getKey());
        }
        Collections.sort(events);
        List<ReadCase> cases = new ArrayList<>();
        for (Long event : events) {
            JsonObject read = readByReadEvent.get(event);
            cases.add(new ReadCase(event, caseGuard(event),
                    string(read, "resolution"),
                    longInteger(read, "chosenFieldVersionId", 0L)));
        }
        return Collections.unmodifiableList(cases);
    }

    /** Guarded subset of {@link #readCasesOfSessionLocation}. */
    public List<ReadCase> guardedReadCasesOfSessionLocation(
            String sessionLocationKey, String readerSite) {
        List<ReadCase> result = new ArrayList<>();
        for (ReadCase readCase : readCasesOfSessionLocation(
                sessionLocationKey, readerSite)) {
            if (SharedStateEvidence.RESOLUTION_GUARDED.equals(
                    readCase.resolution)
                    && guardedReads().containsKey(readCase.readEventId)) {
                result.add(readCase);
            }
        }
        return Collections.unmodifiableList(result);
    }

    /** Whether one read is the VM's exact selection of this version. */
    public boolean exactReadSelects(long readEventId, long versionEventId) {
        JsonObject read = readByReadEvent.get(readEventId);
        return SharedStateEvidence.RESOLUTION_EXACT.equals(
                string(read, "resolution"))
                && longInteger(read, "chosenFieldVersionId", 0L)
                == versionEventId;
    }

    /**
     * Offers one order edge the composition wants, with the ledger's own
     */
    public int propose(long before, long after) {
        return slice.orderDomain().propose(before, after);
    }

    /** Bounded integer positions of the one shared order domain. */
    public List<OrderVariable> positions() {
        return Collections.unmodifiableList(positions);
    }

    /** Boolean read-from selectors of the sliced guarded reads. */
    public List<String> selectors() {
        return Collections.unmodifiableList(selectors);
    }

    /** Guarded relation selectors which own imported case evidence. */
    public Collection<String> caseSelectors() {
        return Collections.unmodifiableCollection(caseSelectors.values());
    }

    public List<OrderAssertion> assertions() {
        return Collections.unmodifiableList(assertions);
    }

    /** Authoritative VM metadata for one guarded-read candidate. */
    public JsonObject writerVersion(long fieldVersionId) {
        JsonObject version = writerVersions.get(fieldVersionId);
        return version == null ? new JsonObject() : version;
    }

    public JsonObject writerVersionForRead(long readEventId,
                                           long localVersionId) {
        return writerVersion(resolveEventForRead(readEventId,
                localVersionId));
    }

    /** Alpha-renaming scope which owns one synthetic recorded event. */
    public String eventScope(long eventId) {
        EventIdentity identity = eventIdentities.get(eventId);
        return identity == null ? "" : identity.scope;
    }

    /**
     * Resolves the selected producer case that owns one known RF arm's raw
     * expression.  A reader snapshot contains a copied writer version, so its
     * synthetic event scope is the reader's and is not an expression owner.
     * Join the VM-local event id and the writer's recorded task/region/
     * occurrence back to a selected source case; refuse zero or several
     * matches instead of guessing an activation.
     */
    public WriterOwnerResolution writerExpressionOwnerForRead(
            long readEventId, JsonObject candidate) {
        if (candidate == null || bool(candidate, "unknown", false)) {
            String scope = eventScope(readEventId);
            return new WriterOwnerResolution(
                    WriterOwnerResolution.Status.READER_LOCAL, scope, "", "",
                    scope.isEmpty() ? Collections.<String>emptyList()
                            : Collections.singletonList(scope),
                    "unknown RF arm remains reader-local");
        }
        long statedVersion = longInteger(candidate, "fieldVersionId", 0L);
        long scopedVersion = resolveEventForRead(readEventId, statedVersion);
        JsonObject writer = writerVersion(scopedVersion);
        EventIdentity copiedIdentity = eventIdentities.get(scopedVersion);
        String readerScope = eventScope(readEventId);
        // A copied candidate whose write and read are both recorded in the
        // same exact case already has an unambiguous expression owner.  The
        // separate version store may omit that local write; its case-scoped
        // event identity must not be discarded merely because the duplicate
        // version snapshot is absent.
        if (copiedIdentity != null && !readerScope.isEmpty()
                && readerScope.equals(copiedIdentity.scope)
                && sameCaseLocalWriter(readEventId, scopedVersion,
                candidate, readerScope)) {
            CaseEvidence owner = caseEvidenceByScope.get(readerScope);
            return new WriterOwnerResolution(
                    WriterOwnerResolution.Status.READER_LOCAL, readerScope,
                    owner == null ? "" : owner.regionId,
                    owner == null ? "" : owner.occurrenceId,
                    Collections.singletonList(readerScope),
                    "writer and read share one exact selected case");
        }
        if (scopedVersion <= 0L || writer.size() == 0
                || copiedIdentity == null) {
            return missingWriterOwner(readEventId, statedVersion,
                    "reader snapshot has no admitted writer version");
        }
        String writerTask = first(string(writer, "taskId"),
                string(candidate, "taskId"));
        String writerRegion = first(string(writer, "regionId"),
                string(candidate, "regionId"));
        String writerOccurrence = string(writer,
                SharedStateEvidence.WRITER_OCCURRENCE_ID);
        String writerSource = string(writer,
                SharedStateEvidence.WRITER_SOURCE_KEY);
        if ("INITIAL".equals(string(writer, "versionKind"))) {
            return new WriterOwnerResolution(
                    WriterOwnerResolution.Status.READER_LOCAL, readerScope,
                    "", "", readerScope.isEmpty()
                    ? Collections.<String>emptyList()
                    : Collections.singletonList(readerScope),
                    "initial state is reader-local, not a producer case");
        }
        if (writerTask.isEmpty() || writerRegion.isEmpty()
                || writerOccurrence.isEmpty()) {
            return missingWriterOwner(readEventId, statedVersion,
                    "writer version lacks task, region, or occurrence identity");
        }

        Set<String> matches = new LinkedHashSet<>();
        for (Map.Entry<Long, JsonObject> entry : writerVersions.entrySet()) {
            EventIdentity identity = eventIdentities.get(entry.getKey());
            if (identity == null
                    || identity.localId != copiedIdentity.localId
                    || !sameWriterIdentity(writer, entry.getValue())) {
                continue;
            }
            CaseEvidence owner = caseEvidenceByScope.get(identity.scope);
            if (owner == null || owner.selector.isEmpty()
                    || !writerRegion.equals(owner.regionId)
                    || !writerTask.equals(string(owner.row,
                    "sourceTaskId"))) {
                continue;
            }
            String ownerOccurrence = owner.occurrenceId;
            boolean occurrenceMatches = writerOccurrence.matches(".*#a\\d+$")
                    ? writerOccurrence.equals(ownerOccurrence)
                    : writerOccurrence.equals(
                    PathObservation.plannedOccurrenceOf(ownerOccurrence));
            if (!occurrenceMatches) continue;
            String ownerSource = string(owner.row, "sourceKey");
            if (!writerSource.isEmpty() && !ownerSource.isEmpty()
                    && !writerSource.equals(ownerSource)) {
                continue;
            }
            matches.add(owner.scope);
        }

        if (matches.size() == 1) {
            String scope = matches.iterator().next();
            CaseEvidence owner = caseEvidenceByScope.get(scope);
            return new WriterOwnerResolution(
                    WriterOwnerResolution.Status.UNIQUE, scope,
                    owner.regionId, owner.occurrenceId, matches,
                    "unique selected writer case");
        }
        WriterOwnerResolution.Status status = matches.isEmpty()
                ? WriterOwnerResolution.Status.MISSING
                : WriterOwnerResolution.Status.AMBIGUOUS;
        return new WriterOwnerResolution(status, "", writerRegion,
                writerOccurrence, matches,
                "read " + readEventId + " writer " + statedVersion
                        + " has " + matches.size()
                        + " selected expression-owner cases");
    }

    /**
     * Whether an inline RF candidate's missing duplicate version envelope is
     * nevertheless owned by the reader's exact case.  The case expression
     * names the read; the VM ledger must additionally put its writer in the
     * same entered context, thread, region, location, and program order.
     */
    private boolean sameCaseLocalWriter(long readEventId, long writerEventId,
                                        JsonObject candidate,
                                        String readerScope) {
        CaseEvidence owner = caseEvidenceByScope.get(readerScope);
        JsonObject writer = ledgerEvents.get(writerEventId);
        JsonObject read = ledgerEvents.get(readEventId);
        if (owner == null || writer == null || read == null
                || !"FIELD_WRITE".equals(string(writer, "eventKind"))
                || !"FIELD_READ".equals(string(read, "eventKind"))) {
            return false;
        }
        long context = longInteger(writer, "contextId", 0L);
        long thread = longInteger(writer, "javaThreadId", 0L);
        String region = string(writer, "regionId");
        if (context <= 0L || thread <= 0L || region.isEmpty()
                || context != longInteger(read, "contextId", 0L)
                || thread != longInteger(read, "javaThreadId", 0L)
                || !region.equals(string(read, "regionId"))
                || !region.equals(owner.regionId)
                || !region.equals(string(candidate, "regionId"))
                || context != longInteger(candidate, "writerContextId", 0L)
                || thread != longInteger(candidate,
                "writerJavaThreadId", 0L)
                || !string(candidate, "taskId").equals(
                string(owner.row, "sourceTaskId"))
                || longInteger(writer, "objectSymRid", 0L)
                != longInteger(read, "objectSymRid", 0L)
                || longInteger(writer, "slot", Long.MIN_VALUE)
                != longInteger(read, "slot", Long.MAX_VALUE)
                || longInteger(writer, "step", Long.MAX_VALUE)
                >= longInteger(read, "step", Long.MIN_VALUE)
                || SharedStateEvidence.containsVmSerializationTruncation(
                candidate.get("expression"))) {
            return false;
        }
        boolean ordered = false;
        for (JsonElement element : array(candidate, "orderConstraints")) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            if ("WRITE_BEFORE_READ".equals(string(edge, "kind"))
                    && longInteger(edge, "beforeEventId", 0L)
                    == writerEventId
                    && longInteger(edge, "afterEventId", 0L)
                    == readEventId) {
                ordered = true;
                break;
            }
        }
        if (!ordered || !slice.orderDomain().orderedBefore(
                writerEventId, readEventId)) return false;
        for (JsonObject event : ledgerEvents.values()) {
            if ("REGION_ENTER".equals(string(event, "eventKind"))
                    && context == longInteger(event, "contextId", 0L)
                    && thread == longInteger(event, "javaThreadId", 0L)
                    && region.equals(string(event, "regionId"))
                    && longInteger(event, "eventId", Long.MAX_VALUE)
                    < writerEventId) {
                return true;
            }
        }
        return false;
    }

    private WriterOwnerResolution missingWriterOwner(long readEventId,
                                                       long version,
                                                       String detail) {
        return new WriterOwnerResolution(
                WriterOwnerResolution.Status.MISSING, "", "", "",
                Collections.<String>emptyList(), "read " + readEventId
                + " writer " + version + ": " + detail);
    }

    private static boolean sameWriterIdentity(JsonObject left,
                                              JsonObject right) {
        if (!string(left, "taskId").equals(string(right, "taskId"))
                || !string(left, "regionId").equals(
                string(right, "regionId"))
                || !string(left, SharedStateEvidence.WRITER_OCCURRENCE_ID)
                .equals(string(right,
                        SharedStateEvidence.WRITER_OCCURRENCE_ID))
                || !string(left, "versionKind").equals(
                string(right, "versionKind"))) {
            return false;
        }
        String leftSource = string(left,
                SharedStateEvidence.WRITER_SOURCE_KEY);
        String rightSource = string(right,
                SharedStateEvidence.WRITER_SOURCE_KEY);
        return leftSource.isEmpty() || rightSource.isEmpty()
                || leftSource.equals(rightSource);
    }

    public List<JsonObject> coverageGaps() {
        List<JsonObject> all = new ArrayList<>(slice.gaps());
        all.addAll(coverageGaps);
        return Collections.unmodifiableList(all);
    }

    /** The model as one manifest member. */
    public JsonObject manifest() {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", SCHEMA_VERSION);
        manifest.addProperty("kind", KIND);
        manifest.addProperty("authority", AUTHORITY);
        manifest.addProperty("ledgerSnapshots", ledgerSnapshots);
        manifest.addProperty("orderedEvents", slice.eventIds().size());
        manifest.addProperty("orderConstraints", slice.order().size());
        manifest.addProperty("guardedReads", readChoices.size());
        manifest.addProperty("partial", partial);
        manifest.addProperty("orderDomainFault", orderDomainFault);
        manifest.add("targetSlice", slice.toJson());
        manifest.add("readChoices", readChoices.deepCopy());
        JsonArray universes = new JsonArray();
        for (BoundedWriterUniverse universe : boundedWriterUniverses.values()) {
            universes.add(universe.toJson());
        }
        manifest.add("writerUniverses", universes);
        JsonArray plans = new JsonArray();
        for (JsonObject plan : gatePlans) plans.add(plan.deepCopy());
        manifest.add("readCutGates", plans);
        JsonArray domain = new JsonArray();
        for (JsonObject edge : slice.order()) domain.add(edge.deepCopy());
        manifest.add("order", domain);
        JsonArray ownership = new JsonArray();
        for (JsonObject row : caseEvidence) ownership.add(row.deepCopy());
        manifest.add("caseEvidence", ownership);
        // Fresh replay JVMs reuse small VM event ids.  Every event emitted by
        JsonArray identities = new JsonArray();
        for (EventIdentity identity : eventIdentities.values()) {
            JsonObject row = new JsonObject();
            row.addProperty("scope", identity.scope);
            row.addProperty("localEventId", identity.localId);
            row.addProperty("syntheticEventId", identity.syntheticId);
            row.addProperty("solverToken", identity.solverToken());
            row.addProperty("qualified", identity.qualified);
            identities.add(row);
        }
        manifest.add("eventIdentities", identities);
        return manifest;
    }


    /**
     * <p>README {@code STATE-1} makes an acceptance decision per selected
     */
    public Map<Long, BoundedWriterUniverse> boundedWriterUniverses() {
        return Collections.unmodifiableMap(boundedWriterUniverses);
    }

    /**
     * The part of this model a solver query has to carry to select a read.
     */
    public JsonObject queryPayload() {
        if (selectors.isEmpty()) return new JsonObject();
        JsonObject payload = new JsonObject();
        payload.addProperty("schemaVersion", SCHEMA_VERSION);
        payload.addProperty("kind", QUERY_KIND);
        payload.addProperty("authority", AUTHORITY);
        JsonArray domain = new JsonArray();
        for (OrderVariable position : positions) {
            JsonObject row = new JsonObject();
            row.addProperty("name", position.name);
            row.addProperty("bound", position.bound);
            domain.add(row);
        }
        payload.add("positions", domain);
        JsonArray names = new JsonArray();
        for (String selector : selectors) names.add(selector);
        payload.add("selectors", names);
        // README section 6's event-existence family travels with the
        // selectors, because the assertions below mention it: a consumer that
        JsonArray existence = new JsonArray();
        for (String symbol : existenceSymbols) existence.add(symbol);
        payload.add("existenceSymbols", existence);
        JsonArray terms = new JsonArray();
        for (OrderAssertion assertion : assertions) {
            JsonObject row = new JsonObject();
            row.addProperty("name", assertion.name);
            row.addProperty("term", assertion.caseGuard.isEmpty()
                    ? assertion.term : "(=> " + assertion.caseGuard + " "
                    + assertion.term + ")");
            if (!assertion.caseGuard.isEmpty()) {
                row.addProperty(CASE_SELECTOR, assertion.caseGuard);
            }
            terms.add(row);
        }
        payload.add("assertions", terms);
        payload.add("readChoices", readChoices.deepCopy());
        JsonArray plans = new JsonArray();
        for (JsonObject plan : gatePlans) plans.add(plan.deepCopy());
        payload.add("readCutGates", plans);
        return payload;
    }

    /** Whether {@code payload} is a read-cut query this model produced. */
    public static boolean isQueryPayload(JsonObject payload) {
        return payload != null
                && QUERY_KIND.equals(string(payload, "kind"))
                && AUTHORITY.equals(string(payload, "authority"))
                && array(payload, "selectors").size() > 0;
    }

}
