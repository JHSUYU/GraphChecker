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
 * What the VM's log says about every event it numbered, and the endpoint
 * identity a row built from one of those events carries.
 *
 * <p>Split out of {@link RowPublication}: the row kinds there are about
 * what an activation observed, and this is about WHERE and BY WHOM one
 * logged event happened -- the bytecode site the VM states for it, the
 * activation the VM says performed it, and the frames that activation's
 * journal says its thread stood on at that point of the session's event
 * clock.  Session-wide and keyed by event id, which is one monotone counter
 * for versions and reads alike: a {@code ReadFromExpression} node names its
 * read event id but not the activation that ran it, and the log record of
 * the same event does.</p>
 */
final class LoggedEventSites {
    private LoggedEventSites() {
    }

    /**
     * Indexes every logged event of one location's read-out record.
     *
     * <p>Populated from the read-out every activation already performs --
     * the VM returns each selected location's complete version and read log
     * -- so nothing is asked of the engine twice and no event is looked up
     * before its log is seen.</p>
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

    /**
     * One logged event, by the id the VM numbered it with.
     *
     * <p>Populated from the read-out every activation already performs --
     * the VM returns each selected location's complete version and read log
     * -- so nothing is asked of the engine twice and no event is looked up
     * before its log is seen.</p>
     */
    private static void index(JsonObject node, String idKey) {
        long id = optionalLongInteger(node, idKey, -1L);
        if (id < 0L) return;
        LOGGED.putIfAbsent(Long.valueOf(id), new Logged(node));
    }

    /**
     * What one logged event states about itself: where, and under which
     * activation.
     *
     * <p>Only these fields, not the log record: a record carries the whole
     * value expression of its version, and keeping every record of the
     * session alive to answer "which activation ran event 77" would retain
     * every expression tree the run ever published.</p>
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
     * The one spelling of a logged event's site.
     *
     * <p>The components are the VM's own ({@code site} on every version,
     * read record and {@code ReadFromExpression}); the class is put in source
     * form here, which is the one place a VM name is converted, and the
     * descriptor travels because two overloads of one name are two methods.
     * An event the VM states no site for is named as a gap and spelled by
     * its location, which distinguishes nothing and says so.</p>
     *
     * <p>Converting the name is also where a name the JVM minted PER RUN
     * stops being an identity ({@link JvmNames#stable}): a write inside an
     * inflated reflective call stands in {@code
     * sun.reflect.GeneratedMethodAccessor23} in one recording and {@code
     * ...Accessor22} in the next, for no reason the exploration can act
     * on.</p>
     */
    static String site(JsonObject node, String locationKey,
                                     long eventId, boolean write) {
        // The site this event states: its own, or its log record's.
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
            return Endpoint.stateSite(locationKey, Endpoint.UNSTATED_SITE, 0,
                    write);
        }
        // The per-run number comes out BEFORE the slashes become dots: a
        // lambda proxy's name is <Outer>$$Lambda$14/1234567890, and that
        // slash is the VM's separator for the hash, not a package.
        return Endpoint.stateSite(
                JvmNames.stable(site.className).replace('/', '.'),
                site.method, site.descriptor, Math.max(0, site.bci), write);
    }

    /**
     * The occurrence that performed one logged event, or null with a gap.
     *
     * <p>The VM names the activation on every record it keeps, and that
     * activation is what the row is a row OF: a read the deletion region
     * made is not a read of the occurrence that happened to publish the
     * location's log first, and a path through the publisher would carry a
     * read it never performed.  An event whose activation this session has
     * no occurrence for states so and publishes no row -- attributing it to
     * the publisher is the thing this replaces.</p>
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

    /**
     * The frames one logged event stood on, or {@code ""} with a gap.
     *
     * <p>The event states the activation it ran inside
     * ({@code regionEnterEventId}) and its own id; the journal of that
     * activation states the frames its thread stood on at that point of the
     * session's event clock.  A node that carries no log record of its own
     * takes the activation from the record of the same event id.</p>
     */
    static String frames(JsonObject node, String locationKey,
                                       long eventId, boolean write) {
        long activation = activationOf(node, eventId);
        String frames = RowRuntime.framesOf(activation, eventId);
        // "" is placed on no frames -- the store or read is in the region's
        // own method -- and the bci of the site is then what distinguishes
        // it.  Only an event the journal could not place is a gap.
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
