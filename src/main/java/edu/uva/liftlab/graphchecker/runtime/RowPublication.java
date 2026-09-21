package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;

import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.runtime.RowRuntime;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.locationId;

/**
 * Publishes one finished activation as contract rows.
 *
 * <p>One translation, run once per activation, from what the replay has
 * assembled -- its decisions, its write log, its mints and its anchor -- to
 * the per-kind row set the contract defines.  It reads only what the
 * activation already published, so nothing here changes the execution and
 * no row exists that the single-row result does not also state.</p>
 *
 * <p>{@link #publish} is the one entry point anywhere.  Two halves of the
 * translation live beside it, because they are other notions and not other
 * doors: {@link RowPlaceholderMint} answers what this activation MINTED,
 * and {@link LoggedEventSites} answers where and by whom one event the VM
 * logged happened.  What stays here is the decisions, the write and read
 * rows, the anchor row, and the readers of the VM's own value spellings
 * that all three share.</p>
 */
final class RowPublication {
    private RowPublication() {
    }

    /** Every row this activation can state, in the contract's shapes. */
    static void publish(ActiveRegion active) {
        if (active == null || !RowRuntime.open()) return;
        OccurrenceAddress occurrence = active.d3Address;
        if (occurrence == null) return;
        publishKind("decisions", active, occurrence);
        publishKind("roots", active, occurrence);
        publishKind("state", active, occurrence);
        publishKind("target", active, occurrence);
    }

    /**
     * One kind, and its own refusal.
     *
     * <p>A row kind that cannot be built is that kind's gap: publishing them
     * under one try left a refused read suppressing the anchor row of the
     * same activation, which reads afterwards as an occurrence that never
     * reached its target.</p>
     */
    private static void publishKind(String kind, ActiveRegion active,
                                    OccurrenceAddress occurrence) {
        try {
            if ("decisions".equals(kind)) {
                decisions(active, occurrence);
            } else if ("roots".equals(kind)) {
                RowPlaceholderMint.roots(active, occurrence);
            } else if ("state".equals(kind)) {
                writes(active);
            } else {
                target(active, occurrence);
            }
        } catch (RuntimeException failure) {
            // The rows describe a run; a translation that throws must not
            // end one.  It says so instead, which is the difference between
            // "this run published no writes" and "this run made none".
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    occurrence.render(),
                    "the " + kind + " rows of this activation could not be"
                            + " published: "
                            + ConcolicRegionRuntime.rootCause(failure));
        }
    }

    /**
     * One row per decision, with the predicate the taken arm satisfied.
     *
     * <p>The term is the satisfied predicate as published -- no second
     * negation anywhere -- and the outcome states which arm that was.</p>
     *
     * <p>I3 -- THE ROW IS ADDRESSED BY THE OCCURRENCE THAT PERFORMED THE
     * BRANCH, and that is what {@code active.d3Address} is: the occurrence
     * running on the thread when this activation was entered
     * ({@code Identity#currentOccurrence}, read by {@code
     * RowRuntime#beginActivation}), which under I1 is the occurrence every
     * site executed synchronously below it belongs to.  It is the same
     * answer {@link #writes} gets from the VM's own statement -- {@code
     * LoggedEventSites#performer} resolves an event's {@code
     * regionEnterEventId} through the very address filed for it at {@code
     * RowRuntime#journalRegion} -- so a decision and a write of one
     * execution point now name one occurrence.  A branch this activation
     * could not perform is not in {@code branchMappings} at all: once an
     * activation closes, {@code ConcolicRegionRuntime#activeRegion} answers
     * nothing for the rest of its frame (I3, silence), so no later branch is
     * handed to another activation's list.  The ordinal beside the site is
     * counted on the same occurrence ({@code Identity#nextBranchOrdinal}),
     * which is what makes (occurrence, site, ordinal) the address an
     * obligation's flip is written at.</p>
     */
    private static void decisions(ActiveRegion active,
                                  OccurrenceAddress occurrence) {
        for (JsonObject mapping : active.branchMappings) {
            String siteId = optionalString(mapping, "siteId");
            int ordinal = optionalInteger(mapping, "occurrence", 1);
            long seq = optionalLongInteger(mapping, "vmEventId", 0L);
            // One branch event, one occurrence: the VM's event range is read
            // out per activation and overlaps every activation the branch
            // ran inside.
            if (!RowRuntime.claimEvent("decision",
                    seq + "#" + siteId + "#" + ordinal)) {
                continue;
            }
            // The row states the site, the arm it took and the predicate as
            // written; nothing here applies one to the other
            // (CONTRACT-SPEC §2), and nothing reads the old witness shapes.
            JsonObject written = object(mapping, "siteCondition");
            RowRuntime.decision(occurrence, seq, siteId, ordinal,
                    optionalBool(mapping, "outcome", false),
                    written.size() > 0 ? written : null);
        }
    }

    /**
     * The VM's constant spelling as the literal it stands for.
     *
     * <p>{@code Y_I_119992} is the VM's name for the int constant 119992 --
     * {@code Y} marks a concrete value, the letter after it is the JVM type
     * and the rest is the value.  A row states the value.</p>
     */
    static String literal(String value) {
        String stated = safe(value);
        if (stated.length() > 4 && stated.charAt(0) == 'Y'
                && stated.charAt(1) == '_' && stated.charAt(3) == '_') {
            return stated.substring(4);
        }
        return stated;
    }

    /**
     * The bound every expression walk in this file stops at, and the row
     * that states it stopped.
     *
     * <p>Two answers used to be one: a walk that found no symbol and a walk
     * that was cut before it could look both returned {@code ""}, so a root
     * named from a deep tree read downstream exactly like a root the VM
     * never named.  The bound stays -- a container's expression on
     * hdfs-17960 nests one relation per recorded operation and the leaves
     * these walks look for are near the top -- and a cut says so, once per
     * walk and subject, in the session's own gap rows.</p>
     */
    static final int WALK_DEPTH = 8;

    /** States that one walk stopped at {@link #WALK_DEPTH}. */
    static boolean cut(String walk, int depth) {
        if (depth <= WALK_DEPTH) return false;
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, walk,
                "this expression walk stopped at depth " + WALK_DEPTH
                        + ", so \"no answer\" here is the walk's bound and"
                        + " not the expression's silence");
        return true;
    }

    /**
     * One row per write version, and one per read the expressions state.
     *
     * <p>The write log is by location and version; the reads are the
     * {@code ReadFromExpression} nodes inside the expressions this
     * activation published, each of which names the version it observed.
     * Both halves of an endpoint come from the run itself: the VM states the
     * bytecode site of every version and read it logs (REPORT-VM21), and the
     * frames those events stood on come from the activation's own frame
     * journal, aligned to the event id (FrameJournal).  The row belongs to
     * the activation that PERFORMED the event, which the VM also states, not
     * to this one -- this activation is only the one whose read-out found the
     * event first (see {@link LoggedEventSites#performer}).</p>
     */
    private static void writes(ActiveRegion active) {
        // One activation, one population of reads: the same node is reached
        // from many versions of one location, and a row per reachable path
        // would count one read many times.
        Set<String> published = new LinkedHashSet<String>();
        Map<JsonElement, Boolean> seen =
                new IdentityHashMap<JsonElement, Boolean>();
        // The mint stores of this activation, by the one key the row's
        // mintVersion is: (location, version).  A declared region input is a
        // READ, so its store is no write and states no WriteRow -- and the
        // key is the store itself, never the spelling of its symbol: the
        // mint row's leaf reads `P_L'...'` where the version the VM
        // published carries `M_L'...'`, so a symbol-set test let five
        // "writes nobody performed" through (v86 the MARKER root's store,
        // v203/v210/v269/v276 the FsImage reference mints).
        Map<String, String> mints = RowPlaceholderMint.mintStores(active);
        // The read log first, and for every location: a read node inside one
        // location's value is a read OF ANOTHER location, and the activation
        // that logged it is what its own log record states.
        // What the VM's log says about every event of one location.
        // Session-wide and keyed by event id, which is one monotone counter
        // for versions and reads alike: a ReadFromExpression node names its
        // read event id but not the activation that ran it, and the log
        // record of the same event does.
        for (JsonObject record : active.sharedStateRecords.values()) {
            LoggedEventSites.index(record);
        }
        for (JsonObject record : active.sharedStateRecords.values()) {
            String locationKey = optionalString(record, "locationKey");
            LocationId location = locationId(locationKey);
            if (location == null) continue;
            JsonObject envelope = object(record, "envelope");
            for (JsonElement element : array(envelope, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject version = element.getAsJsonObject();
                long id = optionalLongInteger(version, "fieldVersionId", -1L);
                if (id < 0L
                        || mints.containsKey(locationKey + "#" + id)) {
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
                    RowRuntime.write(performer, id,
                            LoggedEventSites.site(version, locationKey, id, true),
                            location, id, written, "",
                            LoggedEventSites.frames(version, locationKey, id, true));
                }
                collect(expression, published, seen);
            }
        }
        for (JsonObject mapping : active.branchMappings) {
            collect(mapping.get("witness"), published, seen);
        }
    }

    /**
     * Every read one expression tree states, by the version it observed.
     *
     * <p>Iteratively, over an explicit stack: a container's expression nests
     * one relation per operation the recording saw, which on hdfs-17960's
     * snapshot list is hundreds deep -- a recursion guard cuts the walk
     * before the reads, and publishing no read row reads afterwards as a
     * path that read nothing.</p>
     */
    private static void collect(JsonElement root, Set<String> published,
                                Map<JsonElement, Boolean> seen) {
        if (root == null) return;
        java.util.Deque<JsonElement> pending =
                new java.util.ArrayDeque<JsonElement>();
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

    /** A read the write log covers: the location, and the version it saw. */
    private static void readFrom(JsonObject node, Set<String> published) {
        JsonObject where = object(node, "location");
        String locationKey = SharedStateCapture.locationKeyOf(where);
        LocationId location = locationId(locationKey);
        if (location == null) return;
        long observed = versionOf(node);
        long event = eventOf(node);
        String identity = readIdentity(locationKey, observed, event);
        if (!published.add(identity)) return;
        String symbol = optionalString(node, "_exp");
        if (symbol.isEmpty()) {
            // A guarded read names no symbol of its own: what it read is
            // the version of the location, and that is what the row says.
            symbol = locationKey + "@v" + observed;
        }
        // What this read node says the read returned, or "".
        JsonElement returned = node.get("concreteValue");
        if (returned == null || returned.isJsonNull()) {
            returned = object(node, "observedVersion").get("concreteValue");
        }
        String value = literal(returned == null || returned.isJsonNull() ? ""
                : returned.isJsonObject()
                        ? optionalString(returned.getAsJsonObject(), "_exp")
                        : returned.getAsString());
        if (observed < 0L && value.isEmpty()) {
            // Neither a version to join nor a value to pin: the row would
            // say nothing a reader could use, and saying so is the point.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    locationKey, "a read states neither the version it"
                            + " observed nor the value it returned");
            return;
        }
        if (!RowRuntime.claimRead(identity)) return;
        OccurrenceAddress performer = LoggedEventSites.performer(
                node, locationKey, event, false);
        if (performer == null) return;
        RowRuntime.read(performer, event >= 0L ? event : Math.max(0L, observed),
                LoggedEventSites.site(node, locationKey, event, false),
                location, observed, symbol,
                optionalString(node, "_java_type"), value,
                LoggedEventSites.frames(node, locationKey, event, false));
    }

    /**
     * A read the log does not cover: the object read from and what its
     * field then held, which is the pair the VM states (REPORT15).
     *
     * <p>The value the VM states here is an expression, not always a
     * constant: a field read whose value came from another read carries
     * that read, and with it the version it observed and the location it
     * observed it at.  A row states the version when there is one and the
     * literal when there is not -- never neither -- and spells the
     * location the way the write log spells it, so the two sides of one
     * location join.</p>
     */
    private static void fieldAccess(JsonObject node,
                                    Set<String> published) {
        JsonElement value = node.get("concreteValue");
        if (value == null || value.isJsonNull()) return;
        JsonObject read = nestedRead(value, 0);
        String locationKey = read == null ? ""
                : SharedStateCapture.locationKeyOf(object(read, "location"));
        LocationId location = locationId(locationKey);
        if (location == null) {
            // The location is the VM's or there is none.  Building it out of
            // the projection's own ownerClass and fieldOffset -- and the
            // literal owner "<unstated>" when even the class was absent --
            // named `INSTANCE/<class>#<offset>` while every write of the
            // same storage is logged as `INSTANCE_FIELD/<rid>#<slot>`: the
            // row joined no write version, and its symbol then named a
            // location nothing else in the corpus spells.  Every projected
            // read whose nested read node states no admissible location is
            // this class, whatever its ownerClass says.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    optionalString(node, "ownerClass") + "#"
                            + optionalInteger(node, "fieldOffset", -1),
                    "a projected read states no VM location, so the run"
                            + " cannot say which storage it read");
            return;
        }
        long observed = versionOf(node);
        if (observed < 0L && read != null) observed = versionOf(read);
        long event = eventOf(node);
        if (event < 0L) event = eventOf(value);
        if (event < 0L && read != null) event = eventOf(read);
        String stated = literal(leaf(value, 0));
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
            // One symbol per READ, not per field: the same name on every
            // read of one field is one unknown the whole run shares.
            projected = locationKey + (observed >= 0L ? "@v" + observed
                    : "@e" + event);
        }
        if (!RowRuntime.claimRead(identity)) return;
        OccurrenceAddress performer = LoggedEventSites.performer(
                node, locationKey, event, false);
        if (performer == null) return;
        RowRuntime.read(performer, event >= 0L ? event : Math.max(0L, observed),
                LoggedEventSites.site(node, locationKey, event, false),
                location, observed, projected,
                optionalString(node, "_java_type"), stated,
                LoggedEventSites.frames(node, locationKey, event, false));
    }

    /**
     * One read event, wherever it is reached from.
     *
     * <p>A read happened once, inside one occurrence; the expression trees
     * of every activation that later used the value carry the same node,
     * and a row per tree counts one read many times.  The first activation
     * to publish it states it -- activations finish innermost first, so
     * that is the innermost region the read ran in.</p>
     */
    private static String readIdentity(String locationKey, long observed,
                                       long event) {
        return locationKey + "#" + observed + "#" + event;
    }

    /** The version a node observed, or {@code -1}. */
    static long versionOf(JsonObject node) {
        JsonElement stated = node == null ? null : node.get("observedVersion");
        if (stated == null) return -1L;
        if (stated.isJsonObject()) {
            return optionalLongInteger(stated.getAsJsonObject(),
                    "fieldVersionId", -1L);
        }
        return stated.isJsonPrimitive() ? stated.getAsLong() : -1L;
    }

    /** The VM event a node names, or {@code -1}. */
    private static long eventOf(JsonElement node) {
        if (node == null || !node.isJsonObject()) return -1L;
        JsonObject object = node.getAsJsonObject();
        long read = optionalLongInteger(object, "readEventId", -1L);
        return read >= 0L ? read
                : optionalLongInteger(object, "eventId", -1L);
    }

    /** The read a value node states under the VM's boundary wrappers. */
    static JsonObject nestedRead(JsonElement value, int depth) {
        if (cut("nestedRead", depth)) return null;
        if (value == null || !value.isJsonObject()) return null;
        JsonObject object = value.getAsJsonObject();
        if ("ReadFromExpression".equals(optionalString(object, "_type"))) {
            return object;
        }
        return nestedRead(object.get("expression"), depth + 1);
    }

    /** The literal a value node states, under the VM's wrappers. */
    private static String leaf(JsonElement value, int depth) {
        if (cut("leaf", depth)) return "";
        if (value == null || value.isJsonNull()) return "";
        if (value.isJsonPrimitive()) return value.getAsString();
        if (!value.isJsonObject()) return "";
        JsonObject object = value.getAsJsonObject();
        String spelling = optionalString(object, "_exp");
        if (!spelling.isEmpty()) return spelling;
        String nested = leaf(object.get("expression"), depth + 1);
        if (!nested.isEmpty()) return nested;
        return leaf(object.get("concreteValue"), depth + 1);
    }

    /**
     * The anchor, with phi in the FATAL polarity whichever arm ran.
     *
     * <p>The recorded decision's predicate is the arm this run took; the
     * task declares which arm is fatal.  So the row states the fatal arm of
     * that predicate and, separately, whether this run took it -- and no
     * reader downstream re-derives a polarity (the second negation is
     * exactly the bug the phi-polarity fix removed).</p>
     */
    private static void target(ActiveRegion active,
                               OccurrenceAddress occurrence) {
        ConcolicTaskPlan.RuntimeTask task = active.activation;
        JsonObject reach = active.targetReach;
        if (!task.declaresTargetBranch() && reach == null) return;
        boolean reached = reach != null;
        boolean observed = reached && optionalBool(reach, "outcome", false);
        // The fatal arm is the one the case declared; a seed task that
        // captured the reach without declaring the arm states the arm it
        // observed, which is a fact of the run rather than a derivation.
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
            // The arm this run took, as the VM published it.
            JsonElement satisfied = witness.get("sourceSatisfiedPredicate");
            if (satisfied != null && satisfied.isJsonObject()) {
                condition = satisfied.getAsJsonObject();
            }
        }
        long at = reach == null ? 0L
                : optionalLongInteger(reach, "vmEventId", 0L);
        // A TARGET ROW WITH NO VM CLOCK CANNOT SAY WHERE ITS PATH WAS CUT.
        // seq == 0 states "no VM clock" and never borrows the run's latest
        // event, and the composer cuts a path's prefix strictly before the
        // target (P1, Arms#pathCondition(decisions, target.seq())): at 0
        // that prefix is EMPTY, so pi_p would be weaker than the run's --
        // the satisfiable direction, where a claim can be made on a path
        // whose real condition was stronger.  It happens when the anchor
        // was reached on a CONCRETE decision, which ActiveRegion
        // #recordConcreteDecision records with vmEventId 0.  Named, so the
        // gate withholds instead of the composer quietly composing a
        // shorter path; 0 such rows on either kept corpus (every target
        // seq there is positive).
        if (at <= 0L && reached) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, anchor,
                    "this run reached the anchor on a decision the VM gave"
                            + " no event id, so the row states no position"
                            + " in the event order and the path condition"
                            + " before it cannot be cut");
        }
        RowRuntime.target(occurrence, at, anchor, condition,
                observed == fatalArm,
                reached && observed == fatalArm, reached);
    }}
