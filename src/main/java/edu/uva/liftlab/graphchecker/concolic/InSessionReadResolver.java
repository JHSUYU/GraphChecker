package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * Resolves one replay's expressions to their exact values.
 *
 * <p>A {@code ReadFromExpression} is not a choice.  The composition's older
 * machinery read it as one -- a set of candidate writers to arm over, to be
 * chosen between by a solver -- because it merged many replays offline and
 * had to keep every execution's answer available.  Inside <em>one</em>
 * replay the read is determined: the location had exactly one version when
 * the read happened, that version was written by exactly one event, and the
 * VM recorded that event's expression.  The candidates a read carries are
 * the versions retained at the read, and the one it observed is the latest
 * of them -- version ids are session-monotonic, so the largest id at or
 * before the read event is the value the program saw.</p>
 *
 * <p>The same holds across nodes.  A value that arrived over a declared wire
 * carries a {@code ConsumerBoundaryExpression} of kind {@code RPC_ATTACH},
 * and the replay's {@code vmHandoffEvents} name, for that attach event, the
 * producer's own expression: substituting it continues the walk in the
 * producer's frame, through its reads, to its roots.  So this resolver
 * rewrites an expression until every leaf is one of three things:</p>
 *
 * <ul>
 *   <li>a {@code SymbolExpression} -- a root the recording left free;</li>
 *   <li>a literal a write before tracking left behind, reached through an
 *       {@code INITIAL} version and tagged {@link #INITIAL_TAG} so a reader
 *       can tell "the program computed this" from "the recording started
 *       after it";</li>
 *   <li>a concrete the program itself wrote.</li>
 * </ul>
 *
 * <p>A value reached through an object is resolved the same way.  When a
 * field projection's owner is a symbolic object reference -- the VM writes
 * one as {@code M_L'some/Class'_<rid>} -- that reference and the projection's
 * offset name a location this replay may itself have published, and the walk
 * continues into it.  That is how a key id crosses two objects and a wire in
 * one step-by-step chain: the arriving value projects the sender's object,
 * whose own field was written from the root.  A projection is followed only
 * when the location's value is unambiguous in this replay; a field the replay
 * wrote more than once is refused, because the projection does not say which
 * of those writes it saw.</p>
 *
 * <p>The semantics are exact and single-execution: there is no arm, no
 * selector and no case here, and nothing in this class depends on the
 * guarded-read or candidate machinery.  A path composer builds
 * {@code Fatal_T = OR_p (pi_p AND phi_p)} by resolving each path's own
 * expressions with its own replay's resolver; merging happens between
 * paths, never inside one.</p>
 */
public final class InSessionReadResolver {
    /** Marks a leaf whose value predates the recording. */
    public static final String INITIAL_TAG = "inSessionInitial";
    /**
     * The VM event sequence a decision or a write was recorded at.
     *
     * <p>One clock for the whole replay: the runtime publishes it on branch
     * decisions and on the target anchor, and a write log carries it per
     * version.  It is the only published order over the events of two
     * activations, and the only way a projection over a field written more
     * than once can name the write it read.</p>
     */
    public static final String VM_EVENT_ID = "vmEventId";
    /** Marks a leaf this replay could not determine. */
    public static final String UNRESOLVED_TAG = "inSessionUnresolved";
    /** Why an unresolved leaf could not be determined. */
    public static final String UNRESOLVED_REASON = "inSessionUnresolvedReason";
    private static final int MAX_DEPTH = 512;
    /** The one version a read node says it observed. */
    public static final String OBSERVED_VERSION = "observedVersion";

    /** Anchor -> definition, over every row of the replay. */
    private final Map<String, JsonElement> definitions;
    /** Attach event id -> the producer expression that arrived there. */
    private final Map<Long, JsonElement> handoffs;
    /** "kind/rid#slot\nversion" -> that write's expression. */
    private final Map<String, JsonElement> writes;
    /** The same key -> whether that version predates tracking. */
    private final Set<String> initialVersions;
    /**
     * Expression -> what it resolves to, keyed by the node's own identity.
     *
     * <p>A value reached twice down two branches of one walk is resolved
     * once.  The key has to be the expression, not the location and version
     * it was found under: those name a slot in a replay, and one slot's
     * version is legitimately the subject of several different formulas --
     * a container snapshot is read by a SIZE and by a READ of the same
     * version, and answering one from the other's memo would be a wrong
     * value rather than a slow one.</p>
     */
    private final Map<JsonElement, JsonElement> resolvedValues =
            new IdentityHashMap<>();
    /** "kind/rid#slot" -> its versions in this replay, lowest id first. */
    private final Map<String, TreeMap<Long, String>> locationVersions;
    /**
     * Location -> VM event id of each write -> the version it produced.
     *
     * <p>One replay is one execution, so the value a projection read is the
     * write with the greatest event id below the access.  That is not a
     * choice between writers: it is what happened.</p>
     */
    private final Map<String, TreeMap<Long, Long>> locationWriteEvents;
    /** The VM event the expression now being resolved was read at, or 0. */
    private long atVmEventId;

    private InSessionReadResolver(
            Map<String, JsonElement> definitions,
            Map<Long, JsonElement> handoffs,
            Map<String, JsonElement> writes,
            Set<String> initialVersions,
            Map<String, TreeMap<Long, String>> locationVersions,
            Map<String, TreeMap<Long, Long>> locationWriteEvents) {
        this.definitions = definitions;
        this.handoffs = handoffs;
        this.writes = writes;
        this.initialVersions = initialVersions;
        this.locationVersions = locationVersions;
        this.locationWriteEvents = locationWriteEvents;
    }

    /**
     * Indexes one replay.
     *
     * @param replayRows every region result row of a single replay -- all
     *                   nodes, all activations.  Rows from other replays
     *                   must not be mixed in: the identities here are
     *                   session-local by construction, and two sessions'
     *                   version ids mean different writes.
     */
    public static InSessionReadResolver of(
            Collection<JsonObject> replayRows) {
        Map<String, JsonElement> definitions = new LinkedHashMap<>();
        Map<Long, JsonElement> handoffs = new LinkedHashMap<>();
        Map<String, JsonElement> writes = new LinkedHashMap<>();
        Set<String> initial = new LinkedHashSet<>();
        Map<String, TreeMap<Long, String>> byLocation = new LinkedHashMap<>();
        Map<String, TreeMap<Long, Long>> writeEvents = new LinkedHashMap<>();
        if (replayRows == null) {
            return new InSessionReadResolver(definitions, handoffs, writes,
                    initial, byLocation, writeEvents);
        }
        for (JsonObject row : replayRows) {
            if (row == null) continue;
            for (JsonElement encoded : array(object(row,
                    "sharedExpressionTable"), "definitions")) {
                if (!encoded.isJsonObject()) continue;
                JsonObject definition = encoded.getAsJsonObject();
                String anchor = optionalString(definition,
                        "expressionAnchor");
                // Anchors are content addressed, so two rows that name one
                // anchor name one expression; first writer wins.
                if (!anchor.isEmpty() && definition.has("expression")) {
                    definitions.putIfAbsent(anchor,
                            definition.get("expression"));
                }
            }
            for (JsonElement encoded : array(row, "vmHandoffEvents")) {
                if (!encoded.isJsonObject()) continue;
                JsonObject event = encoded.getAsJsonObject();
                long attach = optionalLongInteger(event, "attachEventId", -1L);
                if (attach >= 0L && event.has("expression")) {
                    handoffs.putIfAbsent(attach, event.get("expression"));
                }
            }
            for (JsonElement encoded : array(row, "sharedFieldVersions")) {
                if (!encoded.isJsonObject()) continue;
                JsonObject record = encoded.getAsJsonObject();
                JsonObject envelope = object(record, "envelope");
                String location = sessionLocation(object(envelope,
                        "location"));
                if (location.isEmpty()) continue;
                for (JsonElement versionElement : array(envelope,
                        "versions")) {
                    if (!versionElement.isJsonObject()) continue;
                    JsonObject version = versionElement.getAsJsonObject();
                    long id = optionalLongInteger(version,
                            "fieldVersionId", -1L);
                    String key = location + "\n" + id;
                    String kind = optionalString(version, "versionKind");
                    if (version.has("expression")) {
                        writes.putIfAbsent(key, version.get("expression"));
                    }
                    if ("INITIAL".equals(kind)) {
                        initial.add(key);
                    }
                    if (id >= 0L) {
                        byLocation.computeIfAbsent(location,
                                ignored -> new TreeMap<>()).putIfAbsent(id,
                                kind);
                    }
                    long event = optionalLongInteger(version,
                            VM_EVENT_ID, 0L);
                    if (id >= 0L && event > 0L
                            && !"INITIAL".equals(kind)) {
                        writeEvents.computeIfAbsent(location,
                                ignored -> new TreeMap<>()).putIfAbsent(
                                event, id);
                    }
                }
            }
        }
        return new InSessionReadResolver(definitions, handoffs, writes,
                initial, byLocation, writeEvents);
    }

    /** {@code kind/rid#slot}, the way a read node addresses a location. */
    static String sessionLocation(JsonObject location) {
        if (location == null || location.size() == 0) return "";
        String kind = optionalString(location, "locationKind");
        if (kind.isEmpty() || !location.has("slot")) return "";
        long owner = optionalLongInteger(location, "ownerSymRid", 0L);
        if (owner == 0L) return "";
        return kind + "/" + owner + "#"
                + optionalLongInteger(location, "slot", 0L);
    }

    /**
     * The version a read observed: the latest one retained at it.
     *
     * <p>Version ids are session-monotonic and a read's candidates are the
     * versions live when it ran, so the largest id among them is the write
     * the program read.  Returns -1 when the node carries no candidate.</p>
     */
    static long observedVersion(JsonArray candidates) {
        long observed = -1L;
        for (JsonElement encoded : candidates) {
            if (!encoded.isJsonObject()) continue;
            long version = optionalLongInteger(encoded.getAsJsonObject(),
                    "fieldVersionId", -1L);
            if (version > observed) observed = version;
        }
        return observed;
    }

    /** The candidate carrying {@code version}, or null. */
    private static JsonObject candidateOf(JsonArray candidates,
                                          long version) {
        for (JsonElement encoded : candidates) {
            if (!encoded.isJsonObject()) continue;
            JsonObject candidate = encoded.getAsJsonObject();
            if (optionalLongInteger(candidate, "fieldVersionId", -1L)
                    == version) {
                return candidate;
            }
        }
        return null;
    }

    /** Rewrites {@code expression} to this replay's exact value. */
    /**
     * Resolve one expression as it was read at {@code vmEventId}.
     *
     * <p>The clock is the VM event sequence the decision that read this
     * expression was recorded at.  It is what lets a projection over a field
     * written several times name the write it saw: the one with the greatest
     * event id below it.  Zero means the caller has no clock, and a
     * projection that needs one then says so rather than guessing.</p>
     */
    public JsonElement resolve(JsonElement expression, long vmEventId) {
        long held = atVmEventId;
        atVmEventId = vmEventId;
        try {
            return resolve(expression);
        } finally {
            atVmEventId = held;
        }
    }

    public JsonElement resolve(JsonElement expression) {
        return rewrite(expression, Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>()), 0);
    }

    /**
     * A cycle is a node that is its own ancestor -- nothing weaker.
     *
     * <p>The guard used to be the location and version a read resolved to,
     * which is not an identity: one version of one container is legitimately
     * read by several different expressions in one replay -- a {@code SIZE}
     * of a map snapshot and a {@code READ} of the same snapshot are two
     * formulas over one shared sub-term.  Keying the guard by
     * {@code (location, version)} made the second of them look like a
     * re-entry of the first whenever the walk reached it from inside the
     * first, and a determined value came back refused.  Substituted
     * expressions are shared objects within one parsed replay, so following
     * a node that is already open on the current path is exactly what a
     * self-referential expression does and nothing else is.</p>
     */
    private JsonElement rewrite(JsonElement expression,
                                Set<JsonElement> visiting, int depth) {
        if (expression == null || expression.isJsonNull()) return expression;
        if (depth > MAX_DEPTH) {
            return unresolved("depth limit reached at " + depth);
        }
        if (expression.isJsonArray()) {
            JsonArray rewritten = new JsonArray();
            for (JsonElement element : expression.getAsJsonArray()) {
                rewritten.add(rewrite(element, visiting, depth + 1));
            }
            return rewritten;
        }
        if (!expression.isJsonObject()) return expression;
        JsonObject node = expression.getAsJsonObject();
        if (!visiting.add(node)) {
            return unresolved("cycle through " + describe(node));
        }
        try {
            return dispatch(node, visiting, depth);
        } finally {
            visiting.remove(node);
        }
    }

    private JsonElement dispatch(JsonObject node, Set<JsonElement> visiting,
                                 int depth) {
        String type = optionalString(node, "_type");
        if ("SharedExpressionReference".equals(type)) {
            String anchor = optionalString(node, "expressionAnchor");
            JsonElement held = definitions.get(anchor);
            if (held == null) {
                return unresolved("no definition for anchor " + anchor);
            }
            return rewrite(held, visiting, depth + 1);
        }
        if ("ConsumerBoundaryExpression".equals(type)) {
            long event = optionalLongInteger(node, "eventId", -1L);
            // The boundary's own inner expression already names the
            // producer's location, in the producer's numbering: the VM
            // substituted the sender's term here when the value arrived.
            // The matching vmHandoffEvents row points at this same node --
            // it records that the hop happened and who produced it, not a
            // second expression -- so following it instead re-enters this
            // node and the cycle guard refuses a value that was determined.
            JsonElement source = node.get(VmExpressionIr.EXPRESSION);
            if (source == null) {
                source = unwrapBoundary(handoffs.get(event), event);
            }
            if (source == null) {
                return unresolved("boundary " + event + " carries nothing");
            }
            return rewrite(source, visiting, depth + 1);
        }
        if ("ReadFromExpression".equals(type)) {
            return rewriteRead(node, visiting, depth);
        }
        if ("FieldAccessExpression".equals(type)) {
            JsonElement projected = rewriteProjection(node, visiting, depth);
            if (projected != null) return projected;
        }
        JsonObject rewritten = new JsonObject();
        for (Map.Entry<String, JsonElement> field : node.entrySet()) {
            rewritten.add(field.getKey(),
                    rewrite(field.getValue(), visiting, depth + 1));
        }
        return rewritten;
    }

    private JsonElement rewriteRead(JsonObject node,
                                    Set<JsonElement> visiting, int depth) {
        // The version this read saw.  A node published under the current
        // schema names it outright; one published under the older schema
        // names every version retained at the read, of which the one it saw
        // is the newest -- version ids are session-monotonic.
        JsonObject observedVersion = object(node, OBSERVED_VERSION);
        JsonArray candidates = array(node, "candidates");
        long observed = observedVersion.size() > 0
                ? optionalLongInteger(observedVersion, "fieldVersionId", -1L)
                : observedVersion(candidates);
        String location = sessionLocation(object(node, "location"));
        if (observed < 0L) {
            return unresolved("read of " + location + " retained no version");
        }
        String key = location + "\n" + observed;
        JsonObject candidate = observedVersion.size() > 0
                ? observedVersion : candidateOf(candidates, observed);
        boolean initial = initialVersions.contains(key)
                || (candidate != null && "INITIAL".equals(
                optionalString(candidate, "versionKind")));
        // The version row carries the write's own expression; the write log
        // is the fallback for a node that published only the id.
        JsonElement value = candidate == null
                ? null : candidate.get(VmExpressionIr.EXPRESSION);
        if (value == null) value = writes.get(key);
        if (value == null) {
            return unresolved("no write of " + location + " at version "
                    + observed);
        }
        JsonElement resolved = resolveValue(value, visiting, depth);
        if (initial && resolved.isJsonObject()) {
            // A value the recording did not watch being produced is still
            // the value; saying so is what keeps it from being read as
            // something the program computed.
            resolved.getAsJsonObject().addProperty(INITIAL_TAG, true);
        }
        return resolved;
    }

    /**
     * Resolves one expression, once per expression.
     *
     * <p>Always hands back a copy, because callers stamp their own reading
     * on what they get -- an INITIAL leaf, say -- and the memo must keep the
     * value it computed.</p>
     */
    private JsonElement resolveValue(JsonElement value,
                                     Set<JsonElement> visiting, int depth) {
        JsonElement memo = resolvedValues.get(value);
        if (memo != null) return memo.deepCopy();
        JsonElement resolved = rewrite(value, visiting, depth + 1);
        if (!unresolved(resolved)) {
            resolvedValues.put(value, resolved.deepCopy());
        }
        return resolved;
    }

    /**
     * A field read through a symbolic object reference, or null.
     *
     * <p>The VM names an object it is tracking {@code M_L'some/Class'_<rid>},
     * and that {@code rid} is the same owner id a location key carries.  So a
     * projection whose owner resolves to such a reference names the location
     * {@code INSTANCE_FIELD/<rid>#<offset>}, and if this replay published that
     * location the walk continues into the value written there.  Returning
     * null means "not a projection this resolver can follow", and the caller
     * keeps the node with its children rewritten -- the behaviour before this
     * existed.</p>
     */
    private JsonElement rewriteProjection(JsonObject node,
                                          Set<JsonElement> visiting,
                                          int depth) {
        if (!node.has("fieldOffset") || !node.has("owner")) return null;
        JsonElement owner = rewrite(node.get("owner"), visiting, depth + 1);
        long rid = referencedObject(owner);
        if (rid <= 0L) return null;
        String location = "INSTANCE_FIELD/" + rid + "#"
                + optionalLongInteger(node, "fieldOffset", 0L);
        TreeMap<Long, String> versions = locationVersions.get(location);
        if (versions == null || versions.isEmpty()) return null;
        long written = -1L;
        int writeCount = 0;
        for (Map.Entry<Long, String> version : versions.entrySet()) {
            if ("INITIAL".equals(version.getValue())) continue;
            writeCount++;
            written = version.getKey();
        }
        boolean initial = writeCount == 0;
        if (writeCount > 1) {
            // One execution wrote this field several times, and the value the
            // projection read is the write that was live when it ran: the
            // greatest event id strictly below the access.  That is the
            // in-session rule itself, not a choice between writers -- a
            // single execution has exactly one live write at any event.
            TreeMap<Long, Long> events = locationWriteEvents.get(location);
            if (atVmEventId <= 0L) {
                return unresolved("field " + location + " was written "
                        + writeCount + " times and the decision that read it"
                        + " carries no vmEventId, so which write it saw is"
                        + " unstated");
            }
            if (events == null || events.size() < writeCount) {
                return unresolved("field " + location + " was written "
                        + writeCount + " times and the write log carries a"
                        + " vmEventId for " + (events == null ? 0
                        : events.size()) + " of them, so which write the"
                        + " access at event " + atVmEventId + " saw is"
                        + " unstated");
            }
            Map.Entry<Long, Long> live = events.lowerEntry(atVmEventId);
            if (live == null) {
                // Every write happened after the access: what it read is
                // whatever was there before this recording tracked the
                // location, which is the INITIAL version.
                initial = true;
            } else {
                written = live.getValue();
            }
        }
        long observed = initial ? versions.firstKey() : written;
        String key = location + "\n" + observed;
        JsonElement value = writes.get(key);
        if (value == null) {
            return unresolved("no value of " + location + " at version "
                    + observed);
        }
        JsonElement resolved = resolveValue(value, visiting, depth);
        if (initial && resolved.isJsonObject()) {
            resolved.getAsJsonObject().addProperty(INITIAL_TAG, true);
        }
        return resolved;
    }

    /**
     * The rid inside {@code M_L'some/Class'_<rid>}, or -1.
     *
     * <p>Only an object reference carries one.  A primitive symbol, a root
     * the source phase introduced, and anything that is not a symbol at all
     * are all "no object here", and the projection over them stays a
     * projection.</p>
     */
    static long referencedObject(JsonElement owner) {
        if (owner == null || !owner.isJsonObject()) return -1L;
        JsonObject node = owner.getAsJsonObject();
        if (!"SymbolExpression".equals(optionalString(node, "_type"))) {
            return -1L;
        }
        String symbol = optionalString(node, "_exp");
        int quoted = symbol.lastIndexOf("'_");
        if (!symbol.startsWith("M_L'") || quoted < 0) return -1L;
        String digits = symbol.substring(quoted + 2);
        if (digits.isEmpty()) return -1L;
        for (int index = 0; index < digits.length(); index++) {
            if (!Character.isDigit(digits.charAt(index))) return -1L;
        }
        try {
            return Long.parseLong(digits);
        } catch (NumberFormatException notAnObject) {
            return -1L;
        }
    }

    /**
     * The expression a handoff carried, below its own boundary node.
     *
     * <p>A {@code vmHandoffEvents} entry records the attached expression as
     * the consumer sees it, which is the boundary node <em>wrapping</em> the
     * producer's value.  Substituting it for that same node re-enters the
     * node -- the resolver's cycle guard then refuses a value it could have
     * determined, which is how every consumer-side key write on
     * hdfs-17899-bug3 came back {@code UNRESOLVED<cycle through …>}.  Only
     * the wrapper is peeled, and only when it names this event: a boundary
     * of some other event inside the carried expression is a real hop and is
     * followed.</p>
     */
    private static JsonElement unwrapBoundary(JsonElement carried,
                                              long event) {
        JsonElement value = carried;
        while (value != null && value.isJsonObject()) {
            JsonObject node = value.getAsJsonObject();
            if (!"ConsumerBoundaryExpression".equals(
                    optionalString(node, "_type"))
                    || optionalLongInteger(node, "eventId", -1L) != event) {
                return value;
            }
            value = node.get(VmExpressionIr.EXPRESSION);
        }
        return value;
    }

    /** Names the node a refusal is about, without printing the tree. */
    private static String describe(JsonObject node) {
        String type = optionalString(node, "_type");
        if ("SharedExpressionReference".equals(type)) {
            return "anchor " + optionalString(node, "expressionAnchor");
        }
        if ("ReadFromExpression".equals(type)) {
            return "read of " + sessionLocation(object(node, "location"));
        }
        if ("ConsumerBoundaryExpression".equals(type)) {
            return "boundary " + optionalLongInteger(node, "eventId", -1L);
        }
        return type.isEmpty() ? "an expression" : type;
    }

    private static JsonObject unresolved(String reason) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "UnresolvedExpression");
        node.addProperty(UNRESOLVED_TAG, true);
        node.addProperty(UNRESOLVED_REASON, reason);
        return node;
    }

    /** Whether a resolved tree still contains an undetermined leaf. */
    public static boolean unresolved(JsonElement resolved) {
        if (resolved == null || resolved.isJsonNull()) return false;
        if (resolved.isJsonArray()) {
            for (JsonElement element : resolved.getAsJsonArray()) {
                if (unresolved(element)) return true;
            }
            return false;
        }
        if (!resolved.isJsonObject()) return false;
        JsonObject node = resolved.getAsJsonObject();
        if (node.has(UNRESOLVED_TAG)) return true;
        for (Map.Entry<String, JsonElement> field : node.entrySet()) {
            if (unresolved(field.getValue())) return true;
        }
        return false;
    }
}
