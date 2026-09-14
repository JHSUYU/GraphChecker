package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
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
 * VM recorded that event's expression, and the node states which version
 * that was.  Nothing here chooses between versions, and nothing infers one:
 * a node that states none is refused.</p>
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
     * The session event sequence a branch decision was recorded at.
     *
     * <p>The same counter that numbers field versions, reads and wire
     * events, so this one <em>can</em> be compared with a
     * {@code fieldVersionId}: the write live at a decision is the greatest
     * version id strictly below the decision's event.  Scoped per session,
     * like the ids it is compared against.</p>
     */
    public static final String SESSION_EVENT_ID = "eventId";
    /**
     * The version a read or a projection observed.
     *
     * <p>The VM states it on the node: a read inside one replay saw exactly
     * one version, and which one is a fact of the recording rather than
     * something to reconstruct from the versions it did not see.</p>
     */
    public static final String OBSERVED_VERSION = "observedVersion";
    /**
     * What the read a joined value stands for actually observed.
     *
     * <p>A projection the walk followed becomes the writer's expression, and
     * the recording's own reading of it -- the {@code concreteValue} the VM
     * stated beside the projection -- would otherwise be dropped with the
     * node.  Stamping it here keeps one fact available to a composition: at
     * this replay's valuation that expression had this value.</p>
     */
    public static final String RECORDED_READING = "inSessionRecordedReading";
    /** Marks a leaf this replay could not determine. */
    public static final String UNRESOLVED_TAG = "inSessionUnresolved";
    /** Why an unresolved leaf could not be determined. */
    public static final String UNRESOLVED_REASON = "inSessionUnresolvedReason";
    private static final int MAX_DEPTH = 512;

    /** Anchor -> definition, over every row of the replay. */
    private final Map<String, JsonElement> definitions;
    /** Attach event id -> the producer expression that arrived there. */
    /** The whole handoff row, by attach event: the source of {@code v_H}. */
    private final Map<Long, JsonObject> handoffRows;
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
    /** The session event the expression now being resolved was read at. */
    private long atSessionEventId;

    private InSessionReadResolver(
            Map<String, JsonElement> definitions,
            Map<Long, JsonObject> handoffRows,
            Map<String, JsonElement> writes,
            Set<String> initialVersions,
            Map<String, TreeMap<Long, String>> locationVersions) {
        this.definitions = definitions;
        this.handoffRows = handoffRows;
        this.writes = writes;
        this.initialVersions = initialVersions;
        this.locationVersions = locationVersions;
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
        Map<Long, JsonObject> handoffRows = new LinkedHashMap<>();
        Map<String, JsonElement> writes = new LinkedHashMap<>();
        Set<String> initial = new LinkedHashSet<>();
        Map<String, TreeMap<Long, String>> byLocation = new LinkedHashMap<>();
        if (replayRows == null) {
            return new InSessionReadResolver(definitions,
                    handoffRows, writes,
                    initial, byLocation);
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
                if (attach >= 0L) handoffRows.putIfAbsent(attach, event);
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
                }
            }
        }
        return new InSessionReadResolver(definitions,
                handoffRows, writes,
                initial, byLocation);
    }

    /** {@code kind/rid#slot}, the way a read node addresses a location. */
    public static String sessionLocation(JsonObject location) {
        if (location == null || location.size() == 0) return "";
        String kind = optionalString(location, "locationKind");
        if (kind.isEmpty() || !location.has("slot")) return "";
        long owner = optionalLongInteger(location, "ownerSymRid", 0L);
        if (owner == 0L) return "";
        return kind + "/" + owner + "#"
                + optionalLongInteger(location, "slot", 0L);
    }


    /**
     * Resolve one expression as it was read at {@code sessionEventId}.
     *
     * <p>The clock is the <em>session</em> event sequence the decision that
     * read this expression was recorded at -- the counter that also numbers
     * field versions.  It lets a projection over a field written several
     * times name the write it saw: the greatest version id below it.  Zero
     * means the caller has no clock, and a projection that needs one then
     * says so rather than guessing.</p>
     */
    public JsonElement resolve(JsonElement expression, long sessionEventId) {
        long held = atSessionEventId;
        atSessionEventId = sessionEventId;
        try {
            return resolve(expression);
        } finally {
            atSessionEventId = held;
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
            String boundaryKind = optionalString(node,
                    VmExpressionIr.BOUNDARY_KIND);
            // Two boundaries, two rules, and they do not overlap.
            //
            // RPC_ATTACH is a value that crossed a wire.  It is a free
            // variable of this replay's formula -- the handoff variable the
            // runtime minted at that attach -- and the producer's own path
            // and the expression it delivered are joined to it once, at
            // compose time, as the family constraint over that handoff.
            // Reading the producer's term out of the node instead would
            // inline one producer path into the consumer's formula, which is
            // what made a consumer flip need a producer replay, so there is
            // no such reading here: a row that mints no variable is refused.
            if (VmExpressionIr.RPC_ATTACH.equals(boundaryKind)) {
                JsonElement minted = handoffSymbol(handoffRows.get(event));
                if (minted == null) {
                    return unresolved("wire arrival at boundary " + event
                            + " mints no " + HANDOFF_SYMBOL);
                }
                return minted;
            }
            // FIELD_READ is a guarded read of shared state whose producer
            // the write log already names.  It is resolved as any read is --
            // by the version the node observed -- and the boundary is only
            // the shell the VM wrapped it in.  laneBN's every boundary is
            // this kind, and 17960 has no wire at all.
            JsonElement source = node.get(VmExpressionIr.EXPRESSION);
            if (source == null) {
                return unresolved("boundary " + event + " of kind "
                        + (boundaryKind.isEmpty() ? "<unstated>"
                        : boundaryKind) + " carries no value");
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

    /** Member the runtime states one handoff's minted symbol under. */
    public static final String HANDOFF_SYMBOL = "handoffSymbol";
    /** Member the runtime states one handoff occurrence's identity under. */
    public static final String HANDOFF_PHASE_ID = "handoffPhaseId";

    /** The free variable one handoff row mints, or null when it mints none. */
    static JsonElement handoffSymbol(JsonObject row) {
        if (row == null) return null;
        String symbol = optionalString(row, HANDOFF_SYMBOL);
        if (symbol.isEmpty()
                || optionalString(row, HANDOFF_PHASE_ID).isEmpty()) {
            return null;
        }
        JsonObject minted = new JsonObject();
        minted.addProperty("_type", "SymbolExpression");
        minted.addProperty("_exp", symbol);
        String javaType = optionalString(row, "javaType");
        if (!javaType.isEmpty()) minted.addProperty("_java_type", javaType);
        return minted;
    }

    /** The version id a node states it observed, or -1. */
    private static long observedVersionOf(JsonObject node) {
        JsonElement stated = node.get(OBSERVED_VERSION);
        if (stated == null || stated.isJsonNull()) return -1L;
        if (stated.isJsonPrimitive()
                && stated.getAsJsonPrimitive().isNumber()) {
            return stated.getAsLong();
        }
        return stated.isJsonObject()
                ? optionalLongInteger(stated.getAsJsonObject(),
                "fieldVersionId", -1L) : -1L;
    }

    private JsonElement rewriteRead(JsonObject node,
                                    Set<JsonElement> visiting, int depth) {
        // The version this read saw.  A node published under the current
        // schema names it outright.  It used to publish every version
        // retained at the read instead, and this took the newest of them --
        // the candidate set was the stitcher's, and reconstructing "which one
        // did it see" from it is the arm this design deleted.  The VM states
        // the version now, so a node that does not is unresolved.
        JsonObject observedVersion = object(node, OBSERVED_VERSION);
        long observed = observedVersion.size() > 0
                ? optionalLongInteger(observedVersion, "fieldVersionId", -1L)
                : observedVersionOf(node);
        String location = sessionLocation(object(node, "location"));
        if (observed < 0L) {
            return unresolved("read of " + location + " states no "
                    + OBSERVED_VERSION);
        }
        String key = location + "\n" + observed;
        JsonObject candidate = observedVersion.size() > 0
                ? observedVersion : null;
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
        long slot = optionalLongInteger(node, "fieldOffset", 0L);
        long rid = referencedObject(owner);
        if (rid <= 0L) rid = containerElement(owner, slot);
        if (rid <= 0L) return null;
        String location = "INSTANCE_FIELD/" + rid + "#" + slot;
        TreeMap<Long, String> versions = locationVersions.get(location);
        if (versions == null || versions.isEmpty()) return null;
        // The node states the version it read, so nothing is inferred from
        // it.  The VM emits this on a projection exactly as it does on a
        // read; the counting below is only for a node that carries none.
        long stated = observedVersionOf(node);
        if (stated >= 0L) {
            return stamp(node, valueOf(location, stated,
                    "INITIAL".equals(versions.get(stated)), visiting, depth),
                    visiting, depth);
        }
        // The writes this replay made to the slot, and which of them are
        // before the read.  The session event counter is the one that
        // numbers versions, so it is what "before" means and the write live
        // at the read is the greatest of them -- one order, one answer, not
        // a choice between writers.  The branch marker's per-thread
        // sequence is not that counter and is never compared here.  A node
        // with no event to order against has no such order: several writes
        // then say nothing about which one it saw, and it is refused with
        // the versions it could not choose between.
        List<Long> written = new ArrayList<>();
        Long live = null;
        for (Map.Entry<Long, String> version : versions.entrySet()) {
            if ("INITIAL".equals(version.getValue())) continue;
            written.add(version.getKey());
            if (atSessionEventId <= 0L
                    || version.getKey() < atSessionEventId) {
                live = version.getKey();
            }
        }
        if (atSessionEventId <= 0L && written.size() > 1) {
            return unresolved("field " + location + " was written "
                    + written.size() + " times " + written
                    + ", the node states no " + OBSERVED_VERSION
                    + " and the decision that read it carries no "
                    + SESSION_EVENT_ID + ", so which write it saw is "
                    + "unstated");
        }
        // No write before the read: what it read is what was there before
        // this recording tracked the location.
        boolean initial = live == null;
        return stamp(node, valueOf(location,
                initial ? versions.firstKey() : live,
                initial, visiting, depth), visiting, depth);
    }

    /**
     * Carries the projection's own reading onto the value it joined to.
     *
     * <p>The pair the VM states beside a projection -- the object read from
     * and what its field then held -- is evidence about this execution, not
     * the value of the read: the value is the write's expression, which is
     * what continues the chain.  So the reading rides along under
     * {@link #RECORDED_READING}, for a caller that states each path's own
     * valuation.</p>
     */
    private JsonElement stamp(JsonObject node, JsonElement joined,
                              Set<JsonElement> visiting, int depth) {
        JsonElement observed = node.get("concreteValue");
        if (observed == null || observed.isJsonNull()
                || !joined.isJsonObject() || unresolved(joined)) {
            return joined;
        }
        JsonElement value = rewrite(observed, visiting, depth + 1);
        if (unresolved(value)) return joined;
        joined.getAsJsonObject().add(RECORDED_READING, value);
        return joined;
    }

    /** One location's value at one version, tagged when it predates tracking. */
    private JsonElement valueOf(String location, long observed,
                                boolean initial, Set<JsonElement> visiting,
                                int depth) {
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
     * The object an element read out of a container names, or -1.
     *
     * <p>A read through an iterator -- {@code for (BlockKey k : map.values())
     * k.getExpiryDate()} -- has no reference for an owner: the owner is the
     * relation chain that put the elements there, {@code VALUE(NEXT(ITERATOR(
     * ENTRY_VIEW(PUT(PUT(SNAPSHOT_BASE(STATE))))))).}  The elements
     * themselves are recorded in it, as the references the PUTs stored, so
     * where exactly one of them is an object this replay published the slot
     * for, that element is the one read and the walk continues into it.
     * Several are several objects and the relation does not say which was
     * reached, so nothing is chosen -- the projection stays a projection and
     * is pinned to the value the recording states for it.</p>
     */
    private long containerElement(JsonElement owner, long slot) {
        Set<Long> named = new LinkedHashSet<>();
        collectReferences(owner, named, 0);
        long only = -1L;
        for (Long candidate : named) {
            if (!locationVersions.containsKey(
                    "INSTANCE_FIELD/" + candidate + "#" + slot)) {
                continue;
            }
            if (only > 0L) return -1L;
            only = candidate;
        }
        return only;
    }

    /** Every object reference inside one already-resolved expression. */
    private static void collectReferences(JsonElement expression,
                                          Set<Long> into, int depth) {
        if (expression == null || depth > MAX_DEPTH) return;
        if (expression.isJsonArray()) {
            for (JsonElement element : expression.getAsJsonArray()) {
                collectReferences(element, into, depth + 1);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        long rid = referencedObject(expression);
        if (rid > 0L) into.add(rid);
        for (Map.Entry<String, JsonElement> field
                : expression.getAsJsonObject().entrySet()) {
            collectReferences(field.getValue(), into, depth + 1);
        }
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
        return referencedObjectRid(optionalString(node, "_exp"));
    }

    /**
     * The rid inside a raw {@code M_L'some/Class'_<rid>} symbol, or -1.
     *
     * <p>The one reader of that spelling: a projection's owner is asked for
     * it here, and so is a lowering deciding whether a symbol denotes an
     * object this execution held.</p>
     */
    public static long referencedObjectRid(String symbol) {
        if (symbol == null) return -1L;
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
