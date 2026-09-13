package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

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
    /** Marks a leaf this replay could not determine. */
    public static final String UNRESOLVED_TAG = "inSessionUnresolved";
    /** Why an unresolved leaf could not be determined. */
    public static final String UNRESOLVED_REASON = "inSessionUnresolvedReason";
    private static final int MAX_DEPTH = 512;

    /** Anchor -> definition, over every row of the replay. */
    private final Map<String, JsonElement> definitions;
    /** Attach event id -> the producer expression that arrived there. */
    private final Map<Long, JsonElement> handoffs;
    /** "kind/rid#slot\nversion" -> that write's expression. */
    private final Map<String, JsonElement> writes;
    /** The same key -> whether that version predates tracking. */
    private final Set<String> initialVersions;
    private final Map<String, JsonElement> resolvedReads =
            new LinkedHashMap<>();

    private InSessionReadResolver(Map<String, JsonElement> definitions,
                                  Map<Long, JsonElement> handoffs,
                                  Map<String, JsonElement> writes,
                                  Set<String> initialVersions) {
        this.definitions = definitions;
        this.handoffs = handoffs;
        this.writes = writes;
        this.initialVersions = initialVersions;
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
        if (replayRows == null) {
            return new InSessionReadResolver(definitions, handoffs, writes,
                    initial);
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
                    String key = location + "\n" + optionalLongInteger(
                            version, "fieldVersionId", -1L);
                    if (version.has("expression")) {
                        writes.putIfAbsent(key, version.get("expression"));
                    }
                    if ("INITIAL".equals(optionalString(version,
                            "versionKind"))) {
                        initial.add(key);
                    }
                }
            }
        }
        return new InSessionReadResolver(definitions, handoffs, writes,
                initial);
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
    public JsonElement resolve(JsonElement expression) {
        return rewrite(expression, new ArrayDeque<>(), 0);
    }

    private JsonElement rewrite(JsonElement expression, Deque<String> visiting,
                                int depth) {
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
        String type = optionalString(node, "_type");
        if ("SharedExpressionReference".equals(type)) {
            String anchor = optionalString(node, "expressionAnchor");
            JsonElement held = definitions.get(anchor);
            if (held == null) {
                return unresolved("no definition for anchor " + anchor);
            }
            return guarded("anchor:" + anchor, held, visiting, depth);
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
            return guarded("boundary:" + event, source, visiting, depth);
        }
        if ("ReadFromExpression".equals(type)) {
            return rewriteRead(node, visiting, depth);
        }
        JsonObject rewritten = new JsonObject();
        for (Map.Entry<String, JsonElement> field : node.entrySet()) {
            rewritten.add(field.getKey(),
                    rewrite(field.getValue(), visiting, depth + 1));
        }
        return rewritten;
    }

    private JsonElement rewriteRead(JsonObject node, Deque<String> visiting,
                                    int depth) {
        JsonArray candidates = array(node, "candidates");
        long observed = observedVersion(candidates);
        String location = sessionLocation(object(node, "location"));
        if (observed < 0L) {
            return unresolved("read of " + location + " retained no version");
        }
        String key = location + "\n" + observed;
        JsonObject candidate = candidateOf(candidates, observed);
        boolean initial = initialVersions.contains(key)
                || (candidate != null && "INITIAL".equals(
                optionalString(candidate, "versionKind")));
        // The candidate carries the write's own expression; the version
        // table is the fallback for a node that published only the id.
        JsonElement value = candidate == null
                ? null : candidate.get(VmExpressionIr.EXPRESSION);
        if (value == null) value = writes.get(key);
        if (value == null) {
            return unresolved("no write of " + location + " at version "
                    + observed);
        }
        // One version has one value, so a second arrival at it -- through a
        // different read node, deeper in the same walk -- is a join in the
        // value DAG rather than a loop.  Answering it from what the first
        // arrival computed is both cheaper and the only reading under which
        // the walk terminates with a value instead of with a refusal.
        JsonElement memo = resolvedReads.get(key);
        if (memo != null) return memo.deepCopy();
        JsonElement resolved = guarded("read:" + key, value, visiting, depth);
        if (initial && resolved.isJsonObject()) {
            // A value the recording did not watch being produced is still
            // the value; saying so is what keeps it from being read as
            // something the program computed.
            resolved.getAsJsonObject().addProperty(INITIAL_TAG, true);
        }
        if (!unresolved(resolved)) resolvedReads.put(key, resolved);
        return resolved;
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

    private JsonElement guarded(String token, JsonElement expression,
                                Deque<String> visiting, int depth) {
        if (visiting.contains(token)) {
            return unresolved("cycle through " + token);
        }
        visiting.addLast(token);
        try {
            return rewrite(expression, visiting, depth + 1);
        } finally {
            visiting.removeLast();
        }
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
