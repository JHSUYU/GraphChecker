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

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * The recorded session graph, projected onto one target and lowered into one
 * order domain.
 *
 * <p>Composition previously gave every channel its own order: a state channel
 * had {@code state_read_position}/{@code state_write_position} variables, an
 * RPC edge had {@code rpc_caller/send/receive_position} variables, and the two
 * lived in disjoint integer domains. Two events on different channels
 * therefore had no relation at all, and a read cut could be satisfied by an
 * order the run forbids. This class emits the alternative the design asks for:
 * <em>one</em> position variable per recorded event, shared by field,
 * synchronization, value-handoff and region events alike, constrained by the
 * ledger's own partial order.</p>
 *
 * <p>Nothing here linearizes that order. Positions are only related where the
 * ledger related the events; unrelated events stay unrelated, which is what
 * lets a solver choose a read cut at all.</p>
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
     *
     * <p>The envelope claimed acyclicity and the edges it carried closed a
     * cycle - across channels or within one. Nothing is salvaged from such a
     * relation: it is reported here and the composition rejects it before any
     * solve, because every order fact read out of it would be unsound.</p>
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
    private final Map<String, String> fieldByLocation;
    private final Map<String, Long> readEventBySite;
    private final Map<String, JsonObject> versionsByLocation;
    /** The VM's authoritative writer row, addressed by its event/version id. */
    private final Map<Long, JsonObject> writerVersions;
    private final List<JsonObject> writerUniverses = new ArrayList<>();
    private final int ledgerSnapshots;
    private final String orderDomainFault;
    private final Set<Long> choiceReadEvents = new LinkedHashSet<>();
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
    private boolean partial;

    private RecordedSessionModel(SessionTargetSlice.Slice slice,
                                 Map<String, String> fieldByLocation,
                                 Map<String, Long> readEventBySite,
                                 Map<String, JsonObject> versionsByLocation,
                                 Map<Long, JsonObject> writerVersions,
                                 int ledgerSnapshots,
                                 String orderDomainFault) {
        this.slice = slice;
        this.fieldByLocation = fieldByLocation;
        this.readEventBySite = readEventBySite;
        this.versionsByLocation = versionsByLocation;
        this.writerVersions = writerVersions;
        this.ledgerSnapshots = ledgerSnapshots;
        this.orderDomainFault = orderDomainFault;
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

    /** One selected relation case and the selector which owns its evidence. */
    private static final class EvidenceOwner {
        private final JsonObject row;
        private final JsonObject recorded;
        private final String owner;
        private final String selector;
        private final String regionId;
        private final String occurrenceId;

        private EvidenceOwner(JsonObject row, JsonObject recorded,
                              String owner, String selector, String regionId,
                              String occurrenceId) {
            this.row = row;
            this.recorded = recorded;
            this.owner = owner;
            this.selector = selector;
            this.regionId = regionId;
            this.occurrenceId = occurrenceId;
        }
    }

    /**
     * Builds the model from the summaries selected for one composition.
     *
     * @param summaryRows     the selected {@code CONCOLIC_REGION_SUMMARY}
     *                        rows, each possibly carrying recorded shared
     *                        state
     * @param targetPredicate the recorded target condition term
     * @param targetRegionId  the region occurrence the target belongs to;
     *                        its recorded reads become slice roots
     */
    public static RecordedSessionModel of(Collection<JsonObject> summaryRows,
                                          JsonElement targetPredicate,
                                          String targetRegionId) {
        Map<String, JsonObject> versionRecords = new LinkedHashMap<>();
        JsonObject ledger = null;
        int ledgerSnapshots = 0;
        List<EvidenceOwner> evidence = evidenceOwners(summaryRows);
        for (EvidenceOwner owned : evidence) {
            JsonObject recorded = owned.recorded;
            for (JsonElement element : array(recorded, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject record = element.getAsJsonObject();
                if (!SharedStateEvidence.isVersionsRecord(record)) continue;
                String key = string(record, "locationKey");
                // Two regions may each report the same session-wide location.
                // Which read-out is the later one is stated by its snapshot
                // ordinal; it is deliberately not inferred from how many rows
                // each holds, because a bounded store evicts and the later
                // read-out of a busy location is routinely the smaller one.
                if (SharedStateEvidence.later(record,
                        versionRecords.get(key))) {
                    versionRecords.put(key, record);
                }
            }
            JsonObject snapshot = object(recorded, "eventLedger");
            if (SharedStateEvidence.isLedgerRecord(snapshot)) {
                ledgerSnapshots++;
                if (SharedStateEvidence.later(snapshot, ledger)) {
                    ledger = snapshot;
                }
            }
        }
        Set<Long> targetReads = targetReads(versionRecords.values(),
                targetRegionId);
        // README section 3 asks for send_req < receive_req in the one shared
        // order domain.  The VM already recorded that fact - a HANDOFF_EXPORT
        // event, a HANDOFF_ATTACH event and the VALUE_HANDOFF edge between
        // them - but a slice rooted only at field reads never reaches it.
        // The exported deliveries are therefore given a position, as ordered
        // events rather than as slice nodes: they carry no value the target
        // term mentions, and walking them as reads would report every one of
        // them as an unrecorded read.  The attach half arrives with them, as
        // the one adjacent event of another channel.
        SessionTargetSlice.Slice slice = SessionTargetSlice.project(
                versionRecords.values(), ledger, targetPredicate,
                targetReads, handoffExportEvents(summaryRows));
        // A ledger that passed record admission and still delivered a cyclic
        // relation is refused by the order domain itself.  Reporting it here
        // is what turns that refusal into a composition decision instead of a
        // silently empty order model.
        String fault = ledger == null ? ""
                : slice.orderDomain().fault();
        RecordedSessionModel model = new RecordedSessionModel(slice,
                declaredFields(versionRecords.values()),
                readEventSites(versionRecords.values()),
                versionLookup(versionRecords.values()),
                writerVersions(versionRecords.values()),
                ledgerSnapshots, fault);
        model.retainCaseOwnership(evidence);
        if (!fault.isEmpty()) {
            model.coverageGaps.add(gap(ORDER_DOMAIN_CYCLE, "", fault));
        }
        model.lower();
        return model;
    }

    /**
     * The recorded read each activation performed of each watched location.
     *
     * <p>A composed edge names a consumer occurrence and a location; the
     * guarded term names a read event. This is the join between them, and it
     * is the reason a consumer port and the read-from selectors end up in one
     * selector family rather than two. An activation that read one location
     * twice is deliberately not resolved here - the pair no longer addresses
     * one read, so the entry is dropped and the caller reports the gap.</p>
     */
    private static Map<String, Long> readEventSites(
            Collection<JsonObject> records) {
        Map<String, Long> bySite = new LinkedHashMap<>();
        Set<String> ambiguous = new LinkedHashSet<>();
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
                Long held = bySite.get(key);
                if (held != null && held != event) {
                    ambiguous.add(key);
                } else {
                    bySite.put(key, event);
                }
            }
        }
        for (String key : ambiguous) bySite.remove(key);
        return bySite;
    }

    /**
     * The same admitted store under both of its legitimate addresses: the
     * stable cross-replay carrier key and the VM-session key embedded in a
     * {@code ReadFromExpression}.  They are aliases of one record, not two
     * candidate stores.
     */
    private static Map<String, JsonObject> versionLookup(
            Collection<JsonObject> records) {
        Map<String, JsonObject> lookup = new LinkedHashMap<>();
        for (JsonObject record : records) {
            String canonical = string(record, "locationKey");
            String session = SharedStateEvidence.locationKey(
                    object(record, "envelope"));
            if (!canonical.isEmpty()) lookup.put(canonical, record);
            if (!session.isEmpty()) lookup.put(session, record);
        }
        return lookup;
    }

    /**
     * The declared field behind each watched location.
     *
     * <p>The VM addresses a location by its own session identity; only the
     * runtime call site that selected the carrier knows the Java field, and it
     * records that join on the versions record. A gate has to carry the field,
     * because the location identity does not survive into a second session.
     * </p>
     */
    private static Map<String, String> declaredFields(
            Collection<JsonObject> records) {
        Map<String, String> fields = new LinkedHashMap<>();
        for (JsonObject record : records) {
            String field = RecordedReadFrom.fieldKey(
                    string(object(record, "carrier"), "declaringClass"),
                    string(object(record, "carrier"), "fieldName"));
            if (!field.isEmpty()) {
                fields.put(string(record, "locationKey"), field);
            }
        }
        return fields;
    }

    /**
     * Indexes writer metadata once from the admitted VM version envelopes.
     * Guarded-read candidates only name a {@code fieldVersionId}; duplicating
     * the writer guard, task and kind on every candidate creates a second
     * authority and rejects otherwise valid recorded reads when one copy is
     * absent.
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

    /**
     * The export events of every delivery this campaign attested.
     *
     * <p>They are the {@code send} half of {@code send < receive}.  Only the
     * export id is stated on a case-local reference - the VM does not hand
     * back the attach id - and it does not need to be: the ledger's own
     * {@code VALUE_HANDOFF} edge relates the two, so naming the export is
     * enough for the attach to enter the slice with it and for the edge
     * between them to be projected.</p>
     */
    /**
     * The recorded shared state offered by these rows and by their cases.
     *
     * <p>README CASE-1 moved the state, container and ledger evidence of a
     * merged relation <em>into</em> each guarded case, so a merged summary
     * carries none of it at row level and reading only the row silently
     * dropped every version and every ledger snapshot a relation recorded -
     * exactly the reads a target then had no writer for.  A raw region
     * result and the target-reach query still state theirs at row level, so
     * both places are read, and the case is read the same way the export
     * events beside it already are.</p>
     */
    private static List<EvidenceOwner> evidenceOwners(
            Collection<JsonObject> summaryRows) {
        List<EvidenceOwner> members = new ArrayList<>();
        for (JsonObject summary : nonNull(summaryRows)) {
            String region = string(summary, "regionId");
            String occurrence = string(summary, "occurrenceId");
            addEvidenceOwner(summary, "", "", region, occurrence, members);
            JsonArray cases = array(object(summary, "regionRelation"),
                    "cases");
            for (int index = 0; index < cases.size(); index++) {
                JsonElement element = cases.get(index);
                if (!element.isJsonObject()) continue;
                JsonObject item = element.getAsJsonObject();
                String owner = caseOwner(region, occurrence,
                        string(item, "caseId"), index);
                addEvidenceOwner(item, owner, caseSelector(owner), region,
                        occurrence, members);
            }
        }
        return members;
    }

    private static void addEvidenceOwner(JsonObject row, String owner,
                                         String selector,
                                         String regionId,
                                         String occurrenceId,
                                         List<EvidenceOwner> members) {
        JsonObject recorded = object(row,
                SharedStateEvidence.RECORDED_FIELD);
        if (recorded.size() > 0 || !VmHandoffEvidence.eventsOf(row).isEmpty()
                || array(row, "interactionEvents").size() > 0) {
            members.add(new EvidenceOwner(row, recorded, owner, selector,
                    regionId, occurrenceId));
        }
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

    private static Set<Long> handoffExportEvents(
            Collection<JsonObject> summaryRows) {
        Set<Long> events = new TreeSet<>();
        for (JsonObject summary : nonNull(summaryRows)) {
            collectHandoffExportEvents(summary, events);
            for (JsonElement element
                    : array(object(summary, "regionRelation"), "cases")) {
                if (!element.isJsonObject()) continue;
                collectHandoffExportEvents(element.getAsJsonObject(), events);
            }
        }
        return events;
    }

    private static void collectHandoffExportEvents(JsonObject owner,
                                                   Set<Long> events) {
        for (Long exportEvent : VmHandoffEvidence.exportEvents(
                java.util.Collections.singletonList(owner))) {
            if (exportEvent != null && exportEvent.longValue() > 0L) {
                events.add(exportEvent);
            }
        }
    }

    /**
     * Retains the guarded case which supplied each interaction, state member
     * and VM handoff reference.  The recorded payload may be a session-wide
     * snapshot, but its admission into this composition is case-local: an
     * event absent from case A must not become true merely because case B's
     * snapshot contained it.
     */
    private void retainCaseOwnership(Collection<EvidenceOwner> evidence) {
        for (EvidenceOwner owned : evidence) {
            if (!owned.selector.isEmpty()) {
                caseSelectors.put(owned.owner, owned.selector);
                JsonObject audit = new JsonObject();
                audit.addProperty(CASE_OWNER, owned.owner);
                audit.addProperty(CASE_SELECTOR, owned.selector);
                audit.addProperty("regionId", owned.regionId);
                audit.addProperty("occurrenceId", owned.occurrenceId);
                audit.addProperty("interactionEvents",
                        array(owned.row, "interactionEvents").size());
                audit.addProperty("recordedSharedState",
                        owned.recorded.size() > 0);
                audit.addProperty("vmHandoffEvents",
                        VmHandoffEvidence.eventsOf(owned.row).size());
                caseEvidence.add(audit);
            }
            if (!owned.selector.isEmpty()) {
                caseEvidenceEvents.addAll(allEvidenceEvents(owned));
            }
            Set<Long> events = evidenceEvents(owned);
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
        // membership across that already-recorded VALUE_HANDOFF edge.
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

    private static Set<Long> evidenceEvents(EvidenceOwner owned) {
        Set<Long> events = new LinkedHashSet<>();
        for (JsonElement member : array(owned.recorded, "versions")) {
            if (!member.isJsonObject()) continue;
            JsonObject envelope = object(member.getAsJsonObject(), "envelope");
            for (JsonElement element : array(envelope, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject version = element.getAsJsonObject();
                if (owned.occurrenceId.equals(string(version,
                        SharedStateEvidence.WRITER_OCCURRENCE_ID))) {
                    addEvent(events, version, "fieldVersionId");
                }
            }
            for (JsonElement element : array(envelope, "reads")) {
                if (!element.isJsonObject()) continue;
                JsonObject read = element.getAsJsonObject();
                if (owned.occurrenceId.equals(string(read,
                        SharedStateEvidence.READER_OCCURRENCE_ID))) {
                    addEvent(events, read, "readEventId");
                }
            }
        }
        for (JsonObject handoff : VmHandoffEvidence.eventsOf(owned.row)) {
            addEvent(events, handoff, "exportEventId");
        }
        for (JsonElement element : array(owned.row, "interactionEvents")) {
            if (!element.isJsonObject()) continue;
            JsonObject interaction = element.getAsJsonObject();
            addEvent(events, interaction, "eventId");
            addEvent(events, interaction, "exportEventId");
        }
        return events;
    }

    /** All explicit state/handoff ids carried by a case, before attribution. */
    private static Set<Long> allEvidenceEvents(EvidenceOwner owned) {
        Set<Long> events = new LinkedHashSet<>();
        for (JsonElement member : array(owned.recorded, "versions")) {
            if (!member.isJsonObject()) continue;
            JsonObject envelope = object(member.getAsJsonObject(), "envelope");
            for (JsonElement element : array(envelope, "versions")) {
                if (element.isJsonObject()) {
                    addEvent(events, element.getAsJsonObject(),
                            "fieldVersionId");
                }
            }
            for (JsonElement element : array(envelope, "reads")) {
                if (element.isJsonObject()) {
                    addEvent(events, element.getAsJsonObject(),
                            "readEventId");
                }
            }
        }
        for (JsonObject handoff : VmHandoffEvidence.eventsOf(owned.row)) {
            addEvent(events, handoff, "exportEventId");
        }
        for (JsonElement element : array(owned.row, "interactionEvents")) {
            if (!element.isJsonObject()) continue;
            addEvent(events, element.getAsJsonObject(), "eventId");
            addEvent(events, element.getAsJsonObject(), "exportEventId");
        }
        return events;
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

    private static String disjunction(Collection<String> selectors) {
        if (selectors == null || selectors.isEmpty()) return "false";
        if (selectors.size() == 1) return selectors.iterator().next();
        StringBuilder term = new StringBuilder("(or");
        for (String selector : selectors) term.append(' ').append(selector);
        return term.append(')').toString();
    }

    /**
     * The {@code send &lt; receive} assertion of one VM-recorded handoff.
     *
     * <p>Answers the name of the recorded order assertion whose {@code before}
     * is this delivery's export event, or {@code ""} when the domain holds no
     * such fact. It is deliberately a lookup and never a proposal: the order of
     * a handoff is the ledger's, and a composition that could not find it must
     * report that rather than assert one.</p>
     */
    public String handoffOrderAssertion(long exportEventId) {
        return handoffOrderAssertion(exportEventId, "");
    }

    /**
     * The handoff order owned by one exact relation case.  A selector may use
     * an export only when that case carried the VM reference; the same event
     * appearing in another case is not a cross-case authorization.
     */
    public String handoffOrderAssertion(long exportEventId,
                                        String caseSelector) {
        if (exportEventId <= 0L) return "";
        if (caseSelector != null && !caseSelector.isEmpty()
                && !unguardedEvents.contains(exportEventId)) {
            Set<String> owners = eventCaseSelectors.get(exportEventId);
            if (owners == null || !owners.contains(caseSelector)) return "";
        }
        for (JsonObject edge : slice.order()) {
            if (longInteger(edge, "beforeEventId", 0L) != exportEventId) {
                continue;
            }
            long after = longInteger(edge, "afterEventId", 0L);
            if (!"VALUE_HANDOFF".equals(string(edge, "edgeKind"))) continue;
            return "recorded_order__" + exportEventId + "__" + after;
        }
        return "";
    }

    /**
     * The recorded reads the target region performed.
     *
     * <p>An exact read leaves no term in the predicate - the reader was handed
     * its writer's expression - so without this the slice would silently miss
     * exactly the reads whose provenance the VM did prove.</p>
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
        // Every guarded read carries an unconditional unknown-writer arm, and
        // a candidate set the slice could not close carries the same doubt.
        // Either makes the model an under-approximation, which is a property
        // of the model and not of the order domain, so it is decided before
        // the positions are even emitted.
        partial = !slice.guardedReads().isEmpty();
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
            positions.add(new OrderVariable(position(event), bound));
        }
        for (JsonObject edge : slice.order()) {
            long before = longInteger(edge, "beforeEventId", 0L);
            long after = longInteger(edge, "afterEventId", 0L);
            assertions.add(new OrderAssertion(
                    "recorded_order__" + before + "__" + after,
                    "(< " + position(before) + " " + position(after) + ")",
                    caseGuard(before, after)));
        }
        for (Map.Entry<Long, JsonObject> entry
                : slice.guardedReads().entrySet()) {
            lowerReadCut(entry.getKey(), entry.getValue(), events);
        }
    }

    /**
     * Declares one event's existence Boolean and records what the run
     * observed about it.
     *
     * @return the symbol name
     */
    private String existence(long eventId, boolean recordedPresent) {
        String name = existenceName(eventId);
        if (existenceSymbols.contains(name)) return name;
        existenceSymbols.add(name);
        String guard = recordedPresent ? caseGuard(eventId) : "";
        assertions.add(new OrderAssertion("recorded_event_exists__" + eventId,
                recordedPresent && !guard.isEmpty()
                        ? "(= " + name + " " + guard + ")"
                        : recordedPresent ? name : "(not " + name + ")"));
        return name;
    }

    /** {@code exists(e)} for one recorded event. */
    public static String existenceName(long eventId) {
        return "event_exists__" + eventId;
    }

    /**
     * {@code exists(read)} for one guarded read.
     *
     * <p>Kept apart from {@link #existenceName}: that family states what the
     * recorded order domain holds, which is a fact of the run, while this one
     * states whether the composed witness contains the load - a question only
     * the selected cases answer.</p>
     */
    public static String readExistsName(long readEventId) {
        return "read_exists__" + readEventId;
    }

    /** Every {@code exists(...)} Boolean this model states. */
    public List<String> existenceSymbols() {
        return Collections.unmodifiableList(existenceSymbols);
    }

    /**
     * Lowers one guarded read into its selectors and its sparse read cut.
     *
     * <p>The cut is the only order the choice needs: the selected write
     * precedes the read, and every competing write is either before the
     * selected one or after the read. Nothing else is ordered, and the
     * unknown-writer arm carries no order at all - which is what keeps the
     * choice satisfiable when the recorded order rules every observed writer
     * out.</p>
     */
    private void lowerReadCut(long readEventId, JsonObject guarded,
                              Set<Long> events) {
        // The set this read chooses from is enumerated before anything is
        // lowered, so a writer the run materialized and the term offers no
        // arm for is a named finding rather than an absence nothing states -
        // and it is enumerated even for a read the order domain cannot place,
        // because "which writers exist" and "can they be ordered" are two
        // questions and only the second one is about the domain.  The arms
        // themselves stay the VM's: only it knows what a writer installed, so
        // a gap is reported and never repaired with an invented candidate.
        String location = SharedStateEvidence.locationKey(guarded);
        BoundedWriterUniverse universe = BoundedWriterUniverse.of(guarded,
                versionsByLocation.get(location));
        writerUniverses.add(universe.toJson());
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
        for (JsonElement element : array(guarded, "candidates")) {
            JsonObject candidate = element.getAsJsonObject();
            String selector = selectorName(readEventId,
                    string(candidate, "selector"));
            selectors.add(selector);
            armSelectors.add(selector);
            JsonObject row = new JsonObject();
            row.addProperty("selector", selector);
            row.addProperty("arm", string(candidate, "selector"));
            row.addProperty("readEventId", readEventId);
            row.addProperty("unknown", bool(candidate, "unknown", false));
            row.addProperty("fieldVersionId",
                    longInteger(candidate, "fieldVersionId", 0L));
            choice.add(row);
            if (bool(candidate, "unknown", false)) {
                row.addProperty("writerExists", false);
                continue;
            }
            long version = longInteger(candidate, "fieldVersionId", 0L);
            // Writer existence.  A candidate write the one order domain does
            // not hold is a write this model cannot place at all, so the arm
            // is refused rather than left as an unordered free choice: leaving
            // it selectable would let the reader take a value from an event
            // the recorded session never admits.
            row.addProperty("writerExists", events.contains(version));
            // README section 6's event-existence implication, and README
            // section 4's own shape for one arm:
            //
            //   rf_W1 -> exists(W1) AND guard(W1) AND W1 < R AND value(R)=...
            //
            // The guard, the cut and the value are the three assertions
            // below and in the composer; this is the first conjunct, stated
            // as its own Boolean so a reader of the query can see which
            // events the witness needs to have happened.  The existence fact
            // itself is the recorded one - the domain holds the write, or it
            // does not - and is never a free choice.
            row.addProperty("existenceSymbol", existence(version,
                    events.contains(version)));
            assertions.add(new OrderAssertion(
                    "recorded_write_exists__" + readEventId + "__" + version,
                    "(=> " + selector + " " + existenceName(version) + ")"));
            if (!events.contains(version)) {
                coverageGaps.add(gap(UNORDERED_READ_CUT,
                        SharedStateEvidence.locationKey(guarded),
                        "candidate write " + version + " of read "
                                + readEventId
                                + " has no position in the order domain"));
                // Kept beside the existence pair that now derives it.  This
                // is the named refusal a reader and the audit look for, and
                // a refusal that can only be reached by a two-step inference
                // is one nobody finds.
                assertions.add(new OrderAssertion(
                        "recorded_write_absent__" + readEventId + "__"
                                + version, "(not " + selector + ")"));
                continue;
            }
            assertions.add(new OrderAssertion(
                    "recorded_read_cut__" + readEventId + "__" + version,
                    "(=> " + selector + " (< " + position(version) + " "
                            + position(readEventId) + "))"));
            for (JsonElement other : array(candidate, "orderConstraints")) {
                JsonObject constraint = other.getAsJsonObject();
                if (!"OTHER_WRITE_OUTSIDE_CUT".equals(
                        string(constraint, "kind"))) {
                    continue;
                }
                long competitor = longInteger(constraint, "otherEventId", 0L);
                if (!events.contains(competitor)) continue;
                assertions.add(new OrderAssertion(
                        "recorded_read_cut_outside__" + readEventId + "__"
                                + version + "__" + competitor,
                        "(=> " + selector + " (or (< " + position(competitor)
                                + " " + position(version) + ") (< "
                                + position(readEventId) + " "
                                + position(competitor) + ")))"));
            }
        }
        // Which of these arms replay could actually observe is knowable now,
        // from the same recorded order the choice is stated over. Learning it
        // only after solving would turn a named coverage limitation into an
        // unexecutable replay.
        SparseReadCutGate plan = SparseReadCutGate.compile(guarded,
                slice.orderDomain(), fieldByLocation.get(
                        SharedStateEvidence.locationKey(guarded)));
        gatePlans.add(plan.toJson());
        coverageGaps.addAll(plan.refusals());
        for (JsonElement element : choice) {
            JsonObject row = element.getAsJsonObject();
            row.addProperty("enforceable",
                    plan.gateFor(string(row, "arm")).size() > 0);
        }
        if (armSelectors.isEmpty()) return;
        // README {@code READ-1}: the choice belongs to the read, and the read
        // belongs to the case that performed it.  Stating exactly-one
        // unconditionally would assert that this load happened in every model
        // - including the ones whose selected cases never reach it - and its
        // arms would then impose write/read order on events the witness does
        // not contain.  So the read's own existence Boolean gates it, and
        // each arm implies it: a missing read has no arm.  This model does
        // not decide that Boolean, because "which cases contain this read" is
        // not a question the recorded session can answer; the consumer that
        // holds the case algebra states it, and the one that is stated over
        // the observed target path asserts it directly.
        String exists = readExistsName(readEventId);
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

    private static String position(long eventId) {
        return POSITION_PREFIX + eventId;
    }

    /** The one shared position variable of one recorded event. */
    public static String positionName(long eventId) {
        return position(eventId);
    }

    /**
     * The one Boolean that selects arm {@code arm} of read
     * {@code readEventId}.
     *
     * <p>Order, value, writer guard and writer existence are all stated over
     * this same name. There is deliberately no second selector family: a
     * value equation keyed on a different Boolean than the cut would let a
     * model take one writer's value under another writer's order.</p>
     */
    public static String selectorName(long readEventId, String arm) {
        String sanitized = arm.replaceAll("[^A-Za-z0-9_]", "_");
        // Admission separates the arms by their raw selector, so the SMT name
        // has to separate them too.  Sanitizing is not injective - two raw
        // selectors differing only in punctuation would become one Boolean,
        // and the read's exactly-one would then be unsatisfiable for a reason
        // nothing in the model states.  Only a name the sanitizer changed
        // carries the disambiguator, so the VM's own rf1/rf2/rf_unknown keep
        // the names they have always had.
        return SELECTOR_PREFIX + readEventId + "__" + sanitized
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

    /** Whether the recorded graph reaches the target at all. */
    public boolean reachesTarget() {
        return slice.reachesTarget();
    }

    /**
     * Whether this model is an under-approximation of the run.
     *
     * <p>True as soon as one sliced read keeps an unknown-writer arm or an
     * unclosed candidate set. It is the fact that makes an unsatisfiable
     * answer inconclusive, so it travels on the manifest rather than being
     * re-derived by every reader.</p>
     */
    /**
     * How many recorded reads this model was built over.
     *
     * <p>Its completeness claim is <em>about</em> these reads, so a consumer
     * has to be able to tell "explained every read it holds" from "holds no
     * read to explain".  Both conjuncts of that claim are vacuous on an empty
     * model, so without this the two are indistinguishable.</p>
     */
    public int recordedReadCount() {
        return readEventBySite.size();
    }

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

    /** The guarded read-from terms of the sliced reads, by read event. */
    public Map<Long, JsonObject> guardedReads() {
        return slice.guardedReads();
    }

    /** Whether one event has a position in the shared order domain. */
    public boolean ordersEvent(long eventId) {
        return slice.eventIds().contains(eventId);
    }

    /**
     * The read one activation performed of one watched location, or 0.
     *
     * <p>Zero means the recorded evidence does not address that pair with one
     * read - the location was never watched, the activation never read it, or
     * it read it more than once - and a caller must report that rather than
     * pick a read.</p>
     */
    public long readEventOf(String locationKey, String readerSite) {
        if (locationKey == null || readerSite == null
                || locationKey.isEmpty() || readerSite.isEmpty()) {
            return 0L;
        }
        Long event = readEventBySite.get(locationKey + "\n" + readerSite);
        return event == null ? 0L : event;
    }

    /**
     * Offers one order edge the composition wants, with the ledger's own
     * semantics. A cyclic proposal is refused and reported; an admitted one
     * joins the same relation every recorded edge lives in, so a later
     * proposal is checked against it too.
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

    /**
     * Coverage gaps of the recorded model: the slice's own, plus every cut
     * this lowering could not state. They are coverage facts, not composition
     * failures - the formula stays usable and says what it does not cover.
     */
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
        for (JsonObject universe : writerUniverses) {
            universes.add(universe.deepCopy());
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
        return manifest;
    }

    /** Compiled read-cut gate plans, one per sliced guarded read. */
    public List<JsonObject> gatePlans() {
        return Collections.unmodifiableList(gatePlans);
    }

    /**
     * The bounded writer universe of every sliced guarded read.
     *
     * <p>One row per read, in the order the reads were lowered. It is the
     * record of which writer cases the formula's arms rest on and which ones
     * the run could not offer, so a reader does not have to re-derive the set
     * from the arms in order to see what the arms are missing.</p>
     */
    public List<JsonObject> writerUniverses() {
        return Collections.unmodifiableList(writerUniverses);
    }

    /**
     * The part of this model a solver query has to carry to select a read.
     *
     * <p>A solver can only report which writer it chose if the query declares
     * the choice. This payload is that declaration - the shared positions, the
     * selectors, the assertions relating them, the candidate rows a model
     * value maps back onto, and the gates each arm compiled to - and nothing
     * else: the target slice and the coverage findings belong to the
     * composition, not to the query.</p>
     *
     * <p>The empty object means this session recorded no guarded read that
     * reaches the target, which is a different statement from a read whose
     * choice the model left open, and the two must not be confused.</p>
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
        // declared only the selectors would replay a query whose exists(...)
        // terms are undeclared, which is a parse error rather than a model.
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

    /** Assertion names this model contributes, for auditing. */
    public Set<String> assertionNames() {
        Set<String> names = new LinkedHashSet<>();
        for (OrderAssertion assertion : assertions) names.add(assertion.name);
        return names;
    }
}
