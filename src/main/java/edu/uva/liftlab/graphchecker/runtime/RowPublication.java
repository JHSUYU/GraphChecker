package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.VmRows;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.locationId;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

final class RowPublication {
    private RowPublication() {
    }

    static void publish(ActiveRegion active) {
        if (active == null || !RowRuntime.open()) return;
        OccurrenceAddress occurrence = active.d3Address;
        if (occurrence == null) return;
        publishKind("decisions", occurrence,
                () -> decisions(active, occurrence));
        publishKind("roots", occurrence,
                () -> RowPlaceholderMint.roots(active, occurrence));
        publishKind("state", occurrence, () -> writes(active));
        publishKind("target", occurrence, () -> target(active, occurrence));
    }

    static void publishMints(ActiveRegion active) {
        if (active == null || !RowRuntime.open()) return;
        OccurrenceAddress occurrence = active.d3Address;
        if (occurrence == null) return;
        publishKind("mints", occurrence,
                () -> RowPlaceholderMint.mints(active, occurrence));
    }

    private static void publishKind(String kind, OccurrenceAddress occurrence,
                                    Runnable publish) {
        try {
            publish.run();
        } catch (RuntimeException failure) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    occurrence.render(),
                    "the " + kind + " rows of this activation could not be"
                            + " published: "
                            + ConcolicRegionRuntime.rootCause(failure));
        }
    }

    private static void decisions(ActiveRegion active,
                                  OccurrenceAddress occurrence) {
        for (JsonObject mapping : active.branchMappings) {
            String siteId = optionalString(mapping, "siteId");
            int ordinal = optionalInteger(mapping, "occurrence", 1);
            long seq = optionalLongInteger(mapping, "vmEventId", 0L);
            if (!RowRuntime.claimEvent("decision",
                    seq + "#" + siteId + "#" + ordinal)) {
                continue;
            }
            JsonObject written = object(mapping, "siteCondition");
            RowRuntime.decision(occurrence, seq, siteId, ordinal,
                    optionalBool(mapping, "outcome", false),
                    written.size() > 0 ? written : null,
                    optionalBool(mapping, "forced", false)
                            ? Boolean.valueOf(optionalBool(mapping,
                            "concreteOutcome", false)) : null,
                    optionalString(mapping, "via"));
        }
    }

    static String literal(String value) {
        String stated = nonNull(value);
        if (stated.length() > 4 && stated.charAt(0) == 'Y'
                && stated.charAt(1) == '_' && stated.charAt(3) == '_') {
            return stated.substring(4);
        }
        return stated;
    }

    private static void writes(ActiveRegion active) {
        Set<String> published = new LinkedHashSet<String>();
        Map<JsonElement, Boolean> seen =
                new IdentityHashMap<JsonElement, Boolean>();
        Map<String, String> mints = RowPlaceholderMint.mintStores(active);
        for (SharedStateCapture.Filed filed
                : active.sharedStateRecords.values()) {
            if (!filed.walked) LoggedEventSites.index(filed.record);
        }
        for (SharedStateCapture.Filed filed
                : active.sharedStateRecords.values()) {
            if (filed.walked) continue;
            JsonObject record = filed.record;
            String locationKey = optionalString(record, "locationKey");
            LocationId location = locationId(locationKey);
            if (location == null) continue;
            JsonObject envelope = object(record, "envelope");
            for (JsonElement element : array(envelope, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject version = element.getAsJsonObject();
                long id = optionalLongInteger(version, "fieldVersionId", -1L);
                if (!rowed(version, locationKey, mints)) {
                    if (id >= 0L && SharedStateCapture.unattributed(version)) {
                        RowRuntime.storedOutside(location, id,
                                LoggedEventSites.statedSite(version));
                    }
                    continue;
                }
                if (!RowRuntime.claimEvent("write", locationKey + "#" + id)) {
                    continue;
                }
                JsonElement expression = version.get("expression");
                JsonObject written =
                        expression != null && expression.isJsonObject()
                                ? expression.getAsJsonObject() : null;
                OccurrenceAddress performer = LoggedEventSites.performer(
                        version, locationKey, id, true);
                if (performer != null) {
                    String site = LoggedEventSites.site(version, locationKey,
                            id, true);
                    String unrowed = unrowedReferent(
                            active.sharedStateRefusals,
                            active.sharedStateRecords, version, mints);
                    boolean initial = SharedStateCapture.initial(version);
                    RowRuntime.write(performer, id, initial
                                    ? Endpoint.initialSite(site) : site,
                            location, id, written, "",
                            LoggedEventSites.siteIndex(version, locationKey,
                                    id, site, true),
                            unrowed.isEmpty() ? referent(version) : null,
                            unrowed.isEmpty() ? optionalString(version,
                                    SharedStateCapture.REFERENT_STATE_REFUSED)
                                    : unrowed, initial);
                }
                collect(expression, published, seen);
            }
        }
        for (JsonObject mapping : active.branchMappings) {
            collect(mapping.get("witness"), published, seen);
        }
        for (SharedStateCapture.Filed filed
                : active.sharedStateRecords.values()) {
            if (!filed.walked) loggedReads(filed.record, published);
        }
        for (SharedStateCapture.Filed filed
                : active.sharedStateRecords.values()) {
            filed.walked = true;
        }
    }

    private static void loggedReads(JsonObject record,
                                    Set<String> published) {
        Set<String> methods = readSiteMethods;
        if (methods.isEmpty()) return;
        String locationKey = optionalString(record, "locationKey");
        JsonObject envelope = object(record, "envelope");
        Map<Long, JsonElement> values = null;
        for (JsonElement element : array(envelope, "reads")) {
            if (!element.isJsonObject()) continue;
            JsonObject read = element.getAsJsonObject();
            if (!methods.contains(LoggedEventSites.method(read))) continue;
            if (values == null) {
                values = new java.util.HashMap<Long, JsonElement>();
                for (JsonElement version : array(envelope, "versions")) {
                    if (!version.isJsonObject()) continue;
                    values.put(optionalLongInteger(version.getAsJsonObject(),
                            "fieldVersionId", -1L),
                            version.getAsJsonObject().get("expression"));
                }
            }
            long version = VmRows.recordedVersion(read);
            if (!values.containsKey(version)) {
                RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        locationKey, "the read at event " + optionalLongInteger(
                                read, "readEventId", -1L) + " states version "
                                + version + ", which this location's log does"
                                + " not list, so it is no row");
                continue;
            }
            JsonObject observed = object(read, VmRows.OBSERVED_VERSION)
                    .deepCopy();
            JsonElement value = values.get(version);
            if (value != null) observed.add("expression", value);
            JsonObject node = read.deepCopy();
            node.add(VmRows.OBSERVED_VERSION, observed);
            readAt(node, locationKey, published);
        }
        if (values != null && optionalBool(envelope, "readLogTruncated",
                false)) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    locationKey, "the VM's read log of this location was cut"
                            + " at its bound, so its reads before the cut"
                            + " that no expression states are no rows");
        }
    }

    private static volatile Set<String> readSiteMethods =
            java.util.Collections.emptySet();

    static void installReadSites(List<JsonObject> rows) {
        Set<String> found = new java.util.HashSet<String>();
        for (JsonObject row : rows) {
            if (StaticScopeMap.SITE_KIND.equals(optionalString(row, "kind"))
                    && StaticScopeMap.READ_SITE.equals(
                            optionalString(row, "role"))
                    && !optionalString(row, "vmSite").isEmpty()) {
                found.add(optionalString(row, "vmSite"));
            }
        }
        readSiteMethods = java.util.Collections.unmodifiableSet(found);
    }

    private static boolean rowed(JsonObject version, String locationKey,
                                 Map<String, String> mints) {
        long id = optionalLongInteger(version, "fieldVersionId", -1L);
        return id >= 0L && !mints.containsKey(locationKey + "#" + id)
                && !SharedStateCapture.unattributed(version);
    }

    static String unrowedReferent(
            Map<String, String> refusals,
            Map<String, SharedStateCapture.Filed> records, JsonObject version,
            Map<String, String> mints) {
        String key = SharedStateCapture.locationKeyOf(object(version,
                SharedStateCapture.REFERENT_STATE));
        if (key.isEmpty()) return "";
        String refused = refusals.get(key);
        if (refused != null) return refused;
        SharedStateCapture.Filed filed = records.get(key);
        if (filed == null) return "";
        JsonObject record = filed.record;
        long named = optionalLongInteger(object(version,
                SharedStateCapture.REFERENT_STATE), "fieldVersionId", -1L);
        for (JsonElement logged : array(object(record, "envelope"),
                "versions")) {
            if (logged.isJsonObject() && optionalLongInteger(
                    logged.getAsJsonObject(), "fieldVersionId", -2L) == named) {
                return rowed(logged.getAsJsonObject(), key, mints) ? ""
                        : "VERSION_NOT_ROWED";
            }
        }
        return "VERSION_NOT_RETAINED";
    }

    private static WriteRow.Referent referent(JsonObject version) {
        JsonObject state = object(version, SharedStateCapture.REFERENT_STATE);
        LocationId location = locationId(
                SharedStateCapture.locationKeyOf(state));
        return location == null ? null : WriteRow.Referent.of(location,
                optionalLongInteger(state, "fieldVersionId", -1L));
    }

    private static void collect(JsonElement root, Set<String> published,
                                Map<JsonElement, Boolean> seen) {
        if (root == null) return;
        Deque<JsonElement> pending =
                new ArrayDeque<JsonElement>();
        pending.push(root);
        while (!pending.isEmpty()) {
            JsonElement node = pending.pop();
            if (node == null || node.isJsonNull()
                    || node.isJsonPrimitive()) {
                continue;
            }
            if (seen.put(node, Boolean.TRUE) != null) continue;
            if (node.isJsonArray()) {
                for (JsonElement element : node.getAsJsonArray()) {
                    pending.push(element);
                }
                continue;
            }
            JsonObject object = node.getAsJsonObject();
            String type = optionalString(object, "_type");
            if ("ReadFromExpression".equals(type)) {
                readFrom(object, published);
            } else if ("FieldAccessExpression".equals(type)) {
                fieldAccess(object, published);
            }
            for (Map.Entry<String, JsonElement> member : object.entrySet()) {
                pending.push(member.getValue());
            }
        }
    }

    private static void readFrom(JsonObject node, Set<String> published) {
        readAt(node, SharedStateCapture.locationKeyOf(
                object(node, "location")), published);
    }

    private static void readAt(JsonObject node, String locationKey,
                               Set<String> published) {
        LocationId location = locationId(locationKey);
        if (location == null) return;
        long observed = VmRows.joinedVersion(node);
        long event = eventOf(node);
        String identity = readIdentity(locationKey, observed, event);
        if (!published.add(identity)) return;
        String symbol = optionalString(node, "_exp");
        if (symbol.isEmpty()) {
            symbol = versionSymbol(RowRuntime.sessionId(), locationKey,
                    "v" + observed);
        }
        String value = nonNull(ReadRow.returned(node));
        if (observed < 0L && value.isEmpty()) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    locationKey, "a read states neither the version it"
                            + " observed nor the value it returned");
            return;
        }
        publishRead(node, identity, locationKey, location, observed, event,
                symbol, value, VmRows.unnamedWriter(node));
    }

    private static void fieldAccess(JsonObject node,
                                    Set<String> published) {
        JsonElement value = node.get("concreteValue");
        if (value == null || value.isJsonNull()) return;
        JsonObject read = nestedRead(value);
        String locationKey = read == null ? ""
                : SharedStateCapture.locationKeyOf(object(read, "location"));
        LocationId location = locationId(locationKey);
        if (location == null) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    optionalString(node, "ownerClass") + "#"
                            + optionalInteger(node, "fieldOffset", -1),
                    "a projected read states no VM location, so the run"
                            + " cannot say which storage it read");
            return;
        }
        long observed = VmRows.joinedVersion(read);
        long event = eventOf(node);
        if (event < 0L) event = eventOf(value);
        if (event < 0L && read != null) event = eventOf(read);
        String stated = literal(leaf(value));
        if (observed < 0L && stated.isEmpty()) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    locationKey, "a projected read states neither the"
                            + " version it observed nor the value it"
                            + " returned");
            return;
        }
        String identity = readIdentity(locationKey, observed, event);
        if (!published.add(identity)) return;
        String projected = optionalString(node, "_exp");
        if (projected.isEmpty()) {
            projected = versionSymbol(RowRuntime.sessionId(), locationKey,
                    observed >= 0L ? "v" + observed : "e" + event);
        }
        publishRead(node, identity, locationKey, location, observed, event,
                projected, stated, VmRows.unnamedWriter(read));
    }

    private static void publishRead(JsonObject node, String identity,
                                    String locationKey, LocationId location,
                                    long observed, long event, String symbol,
                                    String value, boolean unnamedWriter) {
        if (!RowRuntime.claimEvent("read", identity)) return;
        OccurrenceAddress performer = LoggedEventSites.performer(
                node, locationKey, event, false);
        if (performer == null) return;
        String site = LoggedEventSites.site(node, locationKey, event, false);
        RowRuntime.read(performer, event >= 0L ? event : Math.max(0L, observed),
                site, location, observed, symbol,
                optionalString(node, "_java_type"), value,
                LoggedEventSites.siteIndex(node, locationKey, event, site,
                        false),
                ReadRow.UNKNOWN_VERSION, unnamedWriter);
    }

    static String versionSymbol(String session, String locationKey,
                                String version) {
        return locationKey + "@" + version + "@" + session;
    }

    private static String readIdentity(String locationKey, long observed,
                                       long event) {
        return locationKey + "#" + observed + "#" + event;
    }

    private static long eventOf(JsonElement node) {
        return node == null || !node.isJsonObject() ? -1L
                : VmRows.readEvent(node.getAsJsonObject());
    }

    static JsonObject nestedRead(JsonElement value) {
        for (JsonElement cursor = value;
             cursor != null && cursor.isJsonObject();
             cursor = cursor.getAsJsonObject().get("expression")) {
            JsonObject object = cursor.getAsJsonObject();
            if ("ReadFromExpression".equals(optionalString(object, "_type"))) {
                return object;
            }
        }
        return null;
    }

    private static String leaf(JsonElement value) {
        List<JsonElement> pending = new ArrayList<JsonElement>();
        Set<JsonElement> walked = ExpressionWalk.identitySet();
        pending.add(value);
        while (!pending.isEmpty()) {
            JsonElement node = pending.remove(pending.size() - 1);
            if (node == null || node.isJsonNull()) continue;
            if (node.isJsonPrimitive()) {
                String spelled = node.getAsString();
                if (!spelled.isEmpty()) return spelled;
                continue;
            }
            if (!node.isJsonObject() || !walked.add(node)) continue;
            JsonObject object = node.getAsJsonObject();
            String spelling = optionalString(object, "_exp");
            if (!spelling.isEmpty()) return spelling;
            pending.add(object.get("concreteValue"));
            pending.add(object.get("expression"));
        }
        return "";
    }

    private static void target(ActiveRegion active,
                               OccurrenceAddress occurrence) {
        ConcolicTaskPlan.RuntimeTask task = active.activation;
        JsonObject reach = active.targetReach;
        if (!task.declaresTargetBranch() && reach == null) return;
        boolean reached = reach != null;
        boolean observed = reached && optionalBool(reach, "outcome", false);
        boolean fatalArm = task.declaresTargetBranch()
                ? task.targetBranchRequiredOutcome : observed;
        String anchor = task.declaresTargetBranch()
                ? task.targetBranchLabel()
                : optionalString(reach, "siteId") + "#"
                        + optionalInteger(reach, "occurrence", 1);
        JsonObject condition = null;
        String site = task.declaresTargetBranch() ? task.targetBranchSite
                : optionalString(reach, "siteId");
        int ordinal = task.declaresTargetBranch()
                ? task.targetBranchOccurrence
                : optionalInteger(reach, "occurrence", 1);
        for (JsonObject mapping : active.branchMappings) {
            if (!site.equals(optionalString(mapping, "siteId"))) continue;
            if (optionalInteger(mapping, "occurrence", -1) != ordinal) {
                continue;
            }
            JsonObject witness = object(mapping, "witness");
            JsonElement satisfied = witness.get("sourceSatisfiedPredicate");
            if (satisfied != null && satisfied.isJsonObject()) {
                condition = satisfied.getAsJsonObject();
            }
        }
        long at = reach == null ? 0L
                : optionalLongInteger(reach, "vmEventId", 0L);
        Phi stated = reached ? phi(active.branchMappings,
                task.targetDeciders, condition, observed, fatalArm, at)
                : new Phi("", at, null);
        String phi = stated.phi;
        at = stated.at;
        boolean observedFatal = reached && observed == fatalArm;
        if (reached && task.targetGuards.size() > 1) {
            List<String> arms = new ArrayList<>();
            observedFatal = tookDisjunct(active, arms);
            phi = arms.isEmpty() ? "false" : arms.size() == 1 ? arms.get(0)
                    : "(or " + String.join(" ", arms) + ")";
        }
        long forcedFrom = reached ? ForcedArms.forcedFrom(active) : 0L;
        if (forcedFrom > 0L) {
            long from = Math.min(forcedFrom, at);
            phi = forced(active.branchMappings, from, optionalLongInteger(
                    reach, "vmEventId", 0L), phi);
            at = from;
        }
        if (at <= 0L && reached) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, anchor,
                    "this run reached the anchor on a decision the VM gave"
                            + " no event id, so the row states no position"
                            + " in the event order and the path condition"
                            + " before it cannot be cut");
        }
        RowRuntime.target(occurrence, at, anchor, phi, observedFatal,
                reached, stated.openArm, forcedFrom > 0L);
    }

    static String forced(List<JsonObject> mappings, long from, long target,
                         String phi) {
        List<String> conjuncts = new ArrayList<String>();
        for (JsonObject mapping : mappings) {
            long seq = optionalLongInteger(mapping, "vmEventId", 0L);
            if (seq < from || seq > target || !mapping.has("outcome")) {
                continue;
            }
            boolean outcome = optionalBool(mapping, "outcome", false);
            JsonObject written = object(mapping, "siteCondition");
            String ref = written.size() == 0 ? ""
                    : trimmed(RowRuntime.expressionRef(written));
            if (ref.isEmpty()) {
                if (optionalBool(mapping, ForcedArms.AGAINST, false)) {
                    conjuncts.add("false");
                }
            } else if (seq < target) {
                conjuncts.add(Arms.conjunct(ref, outcome));
            }
        }
        conjuncts.add(phi);
        return conjuncts.size() == 1 ? phi
                : "(and " + String.join(" ", conjuncts) + ")";
    }

    static final class Phi {
        final String phi;
        final long at;
        final TargetRow.OpenArm openArm;

        Phi(String phi, long at, TargetRow.OpenArm openArm) {
            this.phi = phi;
            this.at = at;
            this.openArm = openArm;
        }
    }

    static Phi phi(List<JsonObject> mappings,
                   List<StaticScopeMap.Guard> deciders, JsonObject condition,
                   boolean observed, boolean fatalArm, long at) {
        String own = RowRuntime.fatalTerm(condition, observed == fatalArm);
        if (deciders.isEmpty()) return new Phi(own, at, null);
        String ref = trimmed(RowRuntime.expressionRef(condition));
        Decided decided = decided(mappings, deciders, at, ref.isEmpty()
                ? String.valueOf(observed) : Arms.conjunct(ref, observed),
                observed);
        if (decided == null) return new Phi(own, at, null);
        if (decided.open != null) return new Phi(own, at, decided.open);
        return new Phi(fatalArm ? decided.condition
                : not(decided.condition), decided.at, null);
    }

    static final class Decided {
        final String condition;
        final long at;
        final String askedSiteId;
        final int askedOrdinal;
        final TargetRow.OpenArm open;

        private Decided(String condition, long at, String askedSiteId,
                        int askedOrdinal, TargetRow.OpenArm open) {
            this.condition = condition;
            this.at = at;
            this.askedSiteId = askedSiteId;
            this.askedOrdinal = askedOrdinal;
            this.open = open;
        }
    }

    static Decided decided(List<JsonObject> mappings,
                           List<StaticScopeMap.Guard> deciders, long before,
                           String own, boolean observed) {
        String method = SiteId.methodOf(deciders.get(0).siteId());
        JsonObject latest = null;
        long at = 0L;
        for (JsonObject mapping : mappings) {
            long seq = optionalLongInteger(mapping, "vmEventId", 0L);
            if (seq <= at || seq >= before || !method.equals(
                    SiteId.methodOf(optionalString(mapping, "siteId")))) {
                continue;
            }
            latest = mapping;
            at = seq;
        }
        if (latest == null) return null;
        String site = optionalString(latest, "siteId");
        int ordinal = optionalInteger(latest, "occurrence", -1);
        boolean outcome = optionalBool(latest, "outcome", false);
        StaticScopeMap.Guard took = arm(deciders, site, outcome);
        StaticScopeMap.Guard other = arm(deciders, site, !outcome);
        if (took == null || other == null || ordinal < 1
                || took.verdict() != null
                && took.verdict().booleanValue() != observed) {
            return null;
        }
        String held = trimmed(RowRuntime.expressionRef(
                object(latest, "witness").get("sourceSatisfiedPredicate")));
        Decided nested = !held.isEmpty() || took.deciders().isEmpty() ? null
                : decided(mappings, took.deciders(), at,
                String.valueOf(outcome), outcome);
        if (nested != null && nested.open != null) return nested;
        String askedSite = !held.isEmpty() ? site
                : nested == null ? "" : nested.askedSiteId;
        int askedOrdinal = !held.isEmpty() ? ordinal
                : nested == null ? 0 : nested.askedOrdinal;
        if (other.verdict() == null) {
            return new Decided("", at, askedSite, askedOrdinal,
                    TargetRow.OpenArm.of(site, ordinal, !outcome, askedSite,
                            askedOrdinal));
        }
        if (held.isEmpty() && nested == null) return null;
        String predicate = !held.isEmpty() ? held
                : outcome ? nested.condition : not(nested.condition);
        String taken = took.verdict() == null ? own
                : String.valueOf(observed);
        return new Decided(ite(predicate, taken,
                String.valueOf(other.verdict())),
                !held.isEmpty() ? at : nested.at, askedSite, askedOrdinal,
                null);
    }

    private static StaticScopeMap.Guard arm(
            List<StaticScopeMap.Guard> deciders, String site,
            boolean outcome) {
        for (StaticScopeMap.Guard decider : deciders) {
            if (decider.siteId().equals(site) && decider.outcome() != null
                    && decider.outcome().booleanValue() == outcome) {
                return decider;
            }
        }
        return null;
    }

    static String ite(String condition, String then, String otherwise) {
        if (then.equals(otherwise)) return then;
        if ("true".equals(then) && "false".equals(otherwise)) {
            return condition;
        }
        if ("false".equals(then) && "true".equals(otherwise)) {
            return not(condition);
        }
        return "(ite " + condition + " " + then + " " + otherwise + ")";
    }

    static String not(String term) {
        if ("true".equals(term)) return "false";
        if ("false".equals(term)) return "true";
        if (term.startsWith("(not ") && closes(term)) {
            return term.substring(5, term.length() - 1);
        }
        return Arms.conjunct(term, false);
    }

    private static boolean closes(String term) {
        int depth = 0;
        for (int index = 0; index < term.length(); index++) {
            char c = term.charAt(index);
            if (c == '(') depth++;
            if (c == ')' && --depth == 0) return index == term.length() - 1;
        }
        return false;
    }

    static boolean tookDisjunct(ActiveRegion active, List<String> arms) {
        JsonObject reach = active.targetReach;
        return reach != null && disjunction(active.branchMappings,
                active.activation.targetGuards,
                optionalString(reach, "siteId"),
                optionalInteger(reach, "occurrence", -1), arms);
    }

    static boolean disjunction(List<JsonObject> mappings,
                               Map<String, Boolean> guards,
                               String site, int ordinal,
                               List<String> arms) {
        Map<String, Boolean> pending = new LinkedHashMap<>(guards);
        boolean started = false;
        for (JsonObject mapping : mappings) {
            String decided = optionalString(mapping, "siteId");
            started = started || site.equals(decided)
                    && optionalInteger(mapping, "occurrence", -1) == ordinal;
            Boolean fatalArm = started ? pending.remove(decided) : null;
            if (fatalArm == null) continue;
            boolean took = optionalBool(mapping, "outcome", false)
                    == fatalArm.booleanValue();
            JsonElement satisfied = object(mapping, "witness")
                    .get("sourceSatisfiedPredicate");
            boolean symbolic = satisfied != null && satisfied.isJsonObject();
            if (symbolic) {
                arms.add(RowRuntime.fatalTerm(satisfied.getAsJsonObject(),
                        took));
            }
            if (took) {
                if (!symbolic) {
                    arms.clear();
                    arms.add("true");
                }
                return true;
            }
        }
        return false;
    }}
