package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * WHERE and BY WHOM one VM-logged event happened: its bytecode site, its
 * performing activation, and its frames ({@link FrameJournal}).  Keyed by
 * the session-wide event id, because a {@code ReadFromExpression} names its
 * read event id but not its activation.  {@link RowPublication} owns what
 * an activation observed.
 */
final class LoggedEventSites {
    private LoggedEventSites() {
    }

    /**
     * Indexes every logged event of one location's read-out record, the one
     * every activation already performs.
     */
    static void index(JsonObject record) {
        JsonObject envelope = object(record, "envelope");
        for (JsonElement element : array(envelope, "versions")) {
            if (!element.isJsonObject()) continue;
            index(element.getAsJsonObject(), "fieldVersionId");
        }
        for (JsonElement element : array(envelope, "reads")) {
            if (!element.isJsonObject()) continue;
            index(element.getAsJsonObject(), "readEventId");
        }
    }

    /** One logged event, by the id the VM numbered it with. */
    private static void index(JsonObject node, String idKey) {
        long id = optionalLongInteger(node, idKey, -1L);
        if (id < 0L) return;
        LOGGED.putIfAbsent(Long.valueOf(id), new Logged(node));
    }

    /**
     * Where one logged event ran, and under which activation.  Only these
     * fields: keeping the record would retain its whole value expression.
     */
    private static final class Logged {
        private final long activation;
        private final String className;
        private final String method;
        private final String descriptor;
        private final int bci;

        private Logged(JsonObject node) {
            this.activation = optionalLongInteger(node,
                    "regionEnterEventId", -1L);
            JsonObject site = object(node, "site");
            this.className = site == null ? ""
                    : optionalString(site, "className");
            this.method = site == null ? ""
                    : optionalString(site, "methodName");
            this.descriptor = site == null ? ""
                    : optionalString(site, "methodDescriptor");
            this.bci = site == null ? -1
                    : optionalInteger(site, "bci", -1);
        }

        private boolean states() {
            return !className.isEmpty() && !method.isEmpty();
        }
    }

    /** Every logged event of this session, by version or read event id. */
    private static final Map<Long, Logged> LOGGED =
            new java.util.concurrent.ConcurrentHashMap<Long, Logged>();

    /**
     * The one spelling of a logged event's site, and the one place a VM class
     * name is converted to source form.  The descriptor separates overloads;
     * per-run JVM names are stabilised ({@link JvmNames#stable}).  An event
     * with no stated site is a gap spelled by its location.
     */
    static String site(JsonObject node, String locationKey,
                                     long eventId, boolean write) {
        Logged own = node == null ? null : new Logged(node);
        Logged record = eventId < 0L ? null
                : LOGGED.get(Long.valueOf(eventId));
        Logged site = own != null && own.states() ? own
                : record != null && record.states() ? record : null;
        if (site == null) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    locationKey + "#" + eventId,
                    "the VM states no bytecode site for this "
                            + (write ? "version" : "read")
                            + ", so the endpoint's site is its location and"
                            + " distinguishes no event of it");
            return Endpoint.stateSite(locationKey, "UNSTATED_SITE", 0, write);
        }
        // Stabilise BEFORE slashes become dots: in <Outer>$$Lambda$14/123
        // the slash separates the hash, not a package.
        return Endpoint.stateSite(
                JvmNames.stable(site.className).replace('/', '.'),
                site.method, site.descriptor, Math.max(0, site.bci), write);
    }

    /**
     * The occurrence that performed one logged event, or null with a gap.
     * The VM-stated activation, never whichever occurrence published the
     * location's log.
     */
    static OccurrenceAddress performer(JsonObject node,
                                               String locationKey,
                                               long eventId, boolean write) {
        long activation = activationOf(node, eventId);
        OccurrenceAddress performer = RowRuntime.occurrenceAt(activation);
        if (performer != null) return performer;
        RowRuntime.gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                locationKey + "#" + eventId,
                "this " + (write ? "version" : "read") + " states activation "
                        + activation + ", which is no activation of this"
                        + " session, so the run cannot say which occurrence"
                        + " performed it and states no row for it");
        return null;
    }

    /** The activation the event states, its own or its log record's. */
    private static long activationOf(JsonObject node, long eventId) {
        long activation = optionalLongInteger(node, "regionEnterEventId", -1L);
        if (activation > 0L) return activation;
        Logged record = eventId < 0L ? null
                : LOGGED.get(Long.valueOf(eventId));
        return record == null ? -1L : record.activation;
    }

    /** The frames one logged event stood on, or {@code ""} with a gap. */
    static String frames(JsonObject node, String locationKey,
                                       long eventId, boolean write) {
        long activation = activationOf(node, eventId);
        String frames = RowRuntime.framesOf(activation, eventId);
        // "" (no frames: the region's own method) is placed; only null is
        // a gap.
        if (frames != null) return frames;
        RowRuntime.gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                locationKey + "#" + eventId,
                "this " + (write ? "version" : "read")
                        + (activation <= 0L
                        ? " states no region activation, so no frame journal"
                        + " can place it"
                        : " ran under activation " + activation
                        + " with no frame journal entry below its event id")
                        + "; the endpoint carries the empty site index");
        return "";
    }}
