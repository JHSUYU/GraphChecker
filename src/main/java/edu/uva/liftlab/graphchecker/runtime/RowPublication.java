package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
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

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.locationId;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * Publishes one finished activation as contract rows: decisions, writes,
 * reads and the anchor.  It reads only what the activation already
 * published, so it never changes the execution.
 *
 * <p>{@link #publish} is the one entry point.  {@link RowPlaceholderMint}
 * answers what the activation minted; {@link LoggedEventSites} answers where
 * and by whom a logged event happened.</p>
 */
final class RowPublication {
    private RowPublication() {
    }

    /** Every row this activation can state, in the contract's shapes. */
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

    /**
     * The mints of an abandoned activation, whose other rows are withheld.
     *
     * <p>Its mints are already in the VM; a symbol with no row reads
     * downstream as "nobody's".  Every mint is either refused at the mint
     * ({@code RootMint#mintUnattributed}) or rowed here.</p>
     */
    static void publishMints(ActiveRegion active) {
        if (active == null || !RowRuntime.open()) return;
        OccurrenceAddress occurrence = active.d3Address;
        if (occurrence == null) return;
        publishKind("mints", occurrence,
                () -> RowPlaceholderMint.mints(active, occurrence));
    }

    /**
     * One kind, and its own refusal: a kind that cannot be built is that
     * kind's gap only, so a failed read never suppresses the anchor row.
     */
    private static void publishKind(String kind, OccurrenceAddress occurrence,
                                    Runnable publish) {
        try {
            publish.run();
        } catch (RuntimeException failure) {
            // A failed translation must not end the run; the gap tells
            // "published no writes" apart from "made none".
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    occurrence.render(),
                    "the " + kind + " rows of this activation could not be"
                            + " published: "
                            + ConcolicRegionRuntime.rootCause(failure));
        }
    }

    /**
     * One row per decision, with the predicate the taken arm satisfied (as
     * published, never negated a second time) and which arm that was.
     *
     * <p>I3: the row is addressed by the occurrence that performed the
     * branch, {@code active.d3Address} ({@code Identity#currentOccurrence}
     * at entry), the same answer {@code LoggedEventSites#performer} gives a
     * write.  The ordinal is counted on that occurrence
     * ({@code Identity#nextBranchOrdinal}), so (occurrence, site, ordinal)
     * is the address a flip is written at.</p>
     */
    private static void decisions(ActiveRegion active,
                                  OccurrenceAddress occurrence) {
        for (JsonObject mapping : active.branchMappings) {
            String siteId = optionalString(mapping, "siteId");
            int ordinal = optionalInteger(mapping, "occurrence", 1);
            long seq = optionalLongInteger(mapping, "vmEventId", 0L);
            // One branch event, one row: the VM's event range overlaps every
            // enclosing activation.
            if (!RowRuntime.claimEvent("decision",
                    seq + "#" + siteId + "#" + ordinal)) {
                continue;
            }
            // Site, arm and predicate as written; nothing applies one to the
            // other (CONTRACT-SPEC §2).
            JsonObject written = object(mapping, "siteCondition");
            RowRuntime.decision(occurrence, seq, siteId, ordinal,
                    optionalBool(mapping, "outcome", false),
                    written.size() > 0 ? written : null);
        }
    }

    /**
     * The VM's constant spelling as its literal: {@code Y_I_119992} is the
     * int 119992 ({@code Y}, JVM type letter, value).
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
     * The depth every recursive expression walk here stops at.  A cut is
     * stated as a gap, so "cut" never reads as "the VM named nothing".
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
     * One row per write version, and one per read node
     * ({@code ReadFromExpression}) the published expressions contain.
     *
     * <p>Site from the VM log (REPORT-VM21), index from the frame journal.
     * A row belongs to the activation that PERFORMED the event
     * ({@link LoggedEventSites#performer}), not to the one that found it.</p>
     */
    private static void writes(ActiveRegion active) {
        // One read node is reachable from many versions: count it once.
        Set<String> published = new LinkedHashSet<String>();
        Map<JsonElement, Boolean> seen =
                new IdentityHashMap<JsonElement, Boolean>();
        // Mint stores by (location, version): a declared input is a READ and
        // states no WriteRow.  Key by the store, never the symbol spelling
        // (the mint row says `P_L'...'`, the VM version `M_L'...'`).
        Map<String, String> mints = RowPlaceholderMint.mintStores(active);
        // Index every location's log first: a read node inside one value
        // reads ANOTHER location, and only its log record names the
        // activation that ran it (by event id).
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
                // A store outside every region has no performer to row, and
                // a scalar's INITIAL no store at all.
                if (id < 0L
                        || mints.containsKey(locationKey + "#" + id)
                        || SharedStateCapture.unattributed(version)
                        || SharedStateCapture.scalarInitial(version,
                        location)) {
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
                    RowRuntime.write(performer, id, site, location, id,
                            written, "", LoggedEventSites.siteIndex(version,
                                    locationKey, id, site, true));
                }
                collect(expression, published, seen);
            }
        }
        for (JsonObject mapping : active.branchMappings) {
            collect(mapping.get("witness"), published, seen);
        }
    }

    /**
     * Every read one expression tree states.  Iterative on purpose: a
     * container's expression can nest hundreds deep, and a depth guard would
     * drop reads silently.
     */
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
            // A guarded read has no symbol: name the version it read.
            symbol = versionSymbol(RowRuntime.sessionId(), locationKey,
                    "v" + observed);
        }
        JsonElement returned = node.get("concreteValue");
        if (returned == null || returned.isJsonNull()) {
            returned = object(node, "observedVersion").get("concreteValue");
        }
        if ((returned == null || returned.isJsonNull())
                && LoggedEventSites.storedOutsideEveryRegion(observed)) {
            // No write row will state it: what a store outside every region
            // left is a constant, and that is what the read returned.
            JsonElement stored = object(node, "observedVersion")
                    .get("expression");
            if (stored != null && stored.isJsonObject() && "ConstExpr".equals(
                    optionalString(stored.getAsJsonObject(), "_type"))) {
                returned = stored;
            }
        }
        String value = literal(returned == null || returned.isJsonNull() ? ""
                : returned.isJsonObject()
                        ? optionalString(returned.getAsJsonObject(), "_exp")
                        : returned.getAsString());
        if (observed < 0L && value.isEmpty()) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    locationKey, "a read states neither the version it"
                            + " observed nor the value it returned");
            return;
        }
        publishRead(node, identity, locationKey, location, observed, event,
                symbol, value);
    }

    /**
     * A read the log does not cover: the object and what its field held
     * (REPORT15).  The value may nest another read, which supplies version
     * and location.  The row states the version or the literal, never
     * neither, and spells the location as the write log does so they join.
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
            // The location is the VM's or none: one built from ownerClass
            // and fieldOffset would never join the `INSTANCE_FIELD/<rid>#<slot>`
            // spelling of the writes.
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
            // One symbol per READ, not per field.
            projected = versionSymbol(RowRuntime.sessionId(), locationKey,
                    observed >= 0L ? "v" + observed : "e" + event);
        }
        publishRead(node, identity, locationKey, location, observed, event,
                projected, stated);
    }

    /**
     * One read row, claimed once, at the occurrence that performed it; a
     * read the write log names is no placeholder, so it has no mint version.
     */
    private static void publishRead(JsonObject node, String identity,
                                    String locationKey, LocationId location,
                                    long observed, long event, String symbol,
                                    String value) {
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
                ReadRow.UNKNOWN_VERSION);
    }

    /**
     * The name of a read the VM named nothing: the version (or event) it
     * read, in this session.  A rid and a version count within one run, so
     * without the session two replays that diverged spell two objects alike
     * -- hdfs-17897 v67: {@code INSTANCE_FIELD/203#24@v927} a Long's value
     * in one session and a Boolean's in another, one name at two sorts.
     */
    static String versionSymbol(String session, String locationKey,
                                String version) {
        return locationKey + "@" + version + "@" + session;
    }

    /**
     * One read event, wherever it is reached from.  The first activation to
     * publish it wins, which is the innermost (activations finish innermost
     * first).
     */
    private static String readIdentity(String locationKey, long observed,
                                       long event) {
        return locationKey + "#" + observed + "#" + event;
    }

    /** The version a node observed, or {@code -1}. */
    static long versionOf(JsonObject node) {
        if (!VmRows.joinable(node)) return -1L;
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
     * The anchor row: the predicate of the arm this run took, plus whether
     * that arm is the fatal one the task declares.  No reader re-derives a
     * polarity (a second negation is the trap).
     */
    private static void target(ActiveRegion active,
                               OccurrenceAddress occurrence) {
        ConcolicTaskPlan.RuntimeTask task = active.activation;
        JsonObject reach = active.targetReach;
        if (!task.declaresTargetBranch() && reach == null) return;
        boolean reached = reach != null;
        boolean observed = reached && optionalBool(reach, "outcome", false);
        // An undeclared seed task states the arm it observed.
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
        // A concrete target testing the constant a helper returned
        // (causynth.BooleanReturns): the helper's last decision before it,
        // at the helper's fatal arm, is the predicate, and stands where that
        // decision stands, so the prefix is cut before it and not after.
        boolean takenIsFatal = observed == fatalArm;
        if (condition == null && reached
                && !task.targetDeciderSite.isEmpty()) {
            long latest = 0L;
            for (JsonObject mapping : active.branchMappings) {
                long seq = optionalLongInteger(mapping, "vmEventId", 0L);
                JsonElement satisfied = object(mapping, "witness")
                        .get("sourceSatisfiedPredicate");
                if (!task.targetDeciderSite.equals(
                        optionalString(mapping, "siteId"))
                        || seq <= latest || seq >= at
                        || satisfied == null || !satisfied.isJsonObject()) {
                    continue;
                }
                latest = seq;
                condition = satisfied.getAsJsonObject();
                takenIsFatal = optionalBool(mapping, "outcome", false)
                        == task.targetDeciderOutcome;
            }
            if (latest > 0L) at = latest;
        }
        String phi = RowRuntime.fatalTerm(condition, takenIsFatal);
        boolean observedFatal = reached && observed == fatalArm;
        if (reached && task.targetGuards.size() > 1) {
            List<String> arms = new ArrayList<>();
            observedFatal = disjunction(active.branchMappings,
                    task.targetGuards, site, ordinal, arms);
            phi = arms.isEmpty() ? "" : arms.size() == 1 ? arms.get(0)
                    : "(or " + String.join(" ", arms) + ")";
        }
        // seq == 0 means "no VM clock" (a CONCRETE decision stands after the
        // last VM event, ActiveRegion#recordConcreteDecision).  The composer
        // cuts the prefix before target.seq() (P1), so at 0 pi_p would be
        // empty and too weak; state a BLOCKING gap instead.
        if (at <= 0L && reached) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, anchor,
                    "this run reached the anchor on a decision the VM gave"
                            + " no event id, so the row states no position"
                            + " in the event order and the path condition"
                            + " before it cannot be cut");
        }
        RowRuntime.target(occurrence, at, anchor, phi, observedFatal,
                reached);
    }

    /**
     * A disjunctive guard ({@code a || b}) as one evaluation decided it:
     * every test jumps to the throw, so phi is the OR of their fatal arms,
     * each test's first decision from the target branch's on.  The target
     * stands at that first test, so none of them is in the prefix.  A test
     * decided concretely states no arm; one that took its fatal arm ends the
     * evaluation, and a concrete one leaves phi empty (the fatal observed).
     *
     * @return whether a test took its fatal arm
     */
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
                if (!symbolic) arms.clear();
                return true;
            }
        }
        return false;
    }}
