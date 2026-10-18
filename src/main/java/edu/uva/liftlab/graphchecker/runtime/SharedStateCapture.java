package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.VmExpressionTable;
import edu.uva.liftlab.graphchecker.smt.VmRows;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.members;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.rootCause;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.textString;

/**
 * The write log of one activation, read out by object.
 *
 * <p>The runtime names no locations: it asks the VM for every location the
 * session tracked at or after this activation's entry event and publishes
 * {@code location#version -> expression}, keyed by
 * {@code (kind, ownerSymRid, slot)} -- the same key the read nodes carry.</p>
 */
final class SharedStateCapture {
    private SharedStateCapture() {
    }

    /**
     * Reads out every location this activation touched, paging until the VM
     * says the answer is complete.  Called while the owner thread holds the VM
     * context.  Each page goes to the decoding thread as soon as it is
     * read ({@link SharedStateReadOut#decodeLater}), where it is decoded
     * while the next is read, and this activation's publication waits for
     * its pages ({@link SharedStateReadOut#awaitDecoded}); no page waits for the rest of
     * the read-out, and none outlives its decoding (SB12's obligation
     * replay held 8 pages, 220 MB, a fifth of its live heap at its peak,
     * awaiting decoding once the region closed).  A page is read once
     * there is room for it among those still undecoded ({@code
     * ConcolicResultPublisher#awaitDecodeRoom}), which it then takes.
     *
     * <p>The session's pages are one channel: each states the definitions
     * no earlier page stated (VM.md §8), so the decoding thread must import
     * every page's table in the order the VM numbered them.  A page is read
     * and handed on under {@link #READ_OUT_ORDER}, with nothing between that
     * waits: no thread reads a page between another's reading and its
     * hand-on, and none that is read stays behind (the read-outs of the
     * session's threads take turns, page by page: the VM renders a page in
     * about 30 ms).  A short page that names
     * no resume point is a gap: a short write log reads as "never
     * written".</p>
     */
    static SharedStateReadOut captureRecordedSharedState(
            ActiveRegion active, ConcolicVmBroker api) {
        SharedStateReadOut readOut = new SharedStateReadOut();
        String fault = "";
        long after = active == null ? 0L : active.vmRegionEnterEventId;
        for (int page = 0; page < MAX_READ_OUT_PAGES; page++) {
            final String serialized;
            synchronized (READ_OUT_ORDER) {
                // Room is taken by the page handed on below, under the same
                // lock: no other reader takes it meanwhile.
                if (!ConcolicResultPublisher.awaitDecodeRoom(
                        READ_OUT_PAGE_BYTES)) {
                    // Withheld: this activation submits after the end.
                    fault = "the replay ended before this read-out completed";
                    break;
                }
                long asked = System.nanoTime();
                try {
                    serialized = api.readOutTrackedLocations(after,
                            READ_OUT_PAGE_BYTES);
                    READ_OUT_NANOS.addAndGet(System.nanoTime() - asked);
                    READ_OUT_PAGES.incrementAndGet();
                    READ_OUT_CHARS.addAndGet(serialized.length());
                } catch (Throwable throwable) {
                    fault = "tracked-location read-out failed: "
                            + rootCause(throwable);
                    break;
                }
                if (!readOut.decodeLater(serialized, active)) {
                    fault = "a tracked-location read-out page could not be"
                            + " handed to the decoding thread";
                    break;
                }
            }
            JsonObject header = pageHeader(serialized);
            if (header == null) {
                fault = "tracked-location read-out returned no JSON object";
                break;
            }
            if (optionalBool(header, COMPLETE, false)) {
                return readOut;
            }
            long next = optionalLongInteger(header, NEXT_AFTER_EVENT_ID, 0L);
            if (next <= after) {
                fault = "a partial tracked-location read-out states no event "
                        + "to resume from after " + after;
                break;
            }
            after = next;
        }
        if (fault.isEmpty()) {
            fault = "tracked-location read-out did not complete in "
                    + MAX_READ_OUT_PAGES + " pages";
        }
        readOut.fault = fault;
        return readOut;
    }

    /**
     * Held while a page is read out and handed to the decoding thread
     * ({@link #captureRecordedSharedState}): the pages reach the decoding
     * thread in the order the VM numbered their tables.
     */
    private static final Object READ_OUT_ORDER = new Object();

    /** What the region closes' read-outs cost this session ({@link
     *  #readOutSummary}): the pages, their text, the VM's time serializing
     *  them on the closing threads, the decoding thread's work, the
     *  versions they listed. */
    private static final AtomicLong READ_OUT_PAGES = new AtomicLong();
    private static final AtomicLong READ_OUT_CHARS = new AtomicLong();
    private static final AtomicLong READ_OUT_NANOS = new AtomicLong();
    private static final AtomicLong DECODE_NANOS = new AtomicLong();
    private static final AtomicLong VERSIONS = new AtomicLong();
    /** Location envelopes filed, and of them decoded (the rest were held
     *  from an earlier read-out stating them alike). */
    private static final AtomicLong FILED = new AtomicLong();
    private static final AtomicLong DECODED = new AtomicLong();

    /** Whether any region close read out its log this session. */
    static boolean readOutsTaken() {
        return READ_OUT_PAGES.get() > 0L;
    }

    /** One line: what the session's read-outs cost (closeSession), the
     *  records its store holds for read-outs to come among it. */
    static String readOutSummary() {
        return String.format(java.util.Locale.ROOT, "%d page(s), %.1f MB,"
                        + " %.1f s in the VM, %.1f s decoding, %d version(s)"
                        + " listed, %d location envelope(s) filed, %d of"
                        + " them decoded; ",
                READ_OUT_PAGES.get(), READ_OUT_CHARS.get() / 1e6,
                READ_OUT_NANOS.get() / 1e9, DECODE_NANOS.get() / 1e9,
                VERSIONS.get(), FILED.get(), DECODED.get())
                + ConcolicRegionRuntime.workloadExpressionStore
                .repeatedSummary();
    }

    static void resetForTests() {
        for (AtomicLong counter : new AtomicLong[] {READ_OUT_PAGES,
                READ_OUT_CHARS, READ_OUT_NANOS, DECODE_NANOS, VERSIONS,
                FILED, DECODED}) {
            counter.set(0L);
        }
    }

    /** A page's members that say whether it is the last, and where the
     *  next one resumes. */
    private static final String COMPLETE = "complete";
    private static final String NEXT_AFTER_EVENT_ID = "nextAfterEventId";

    /**
     * What one page says of itself ({@link #COMPLETE},
     * {@link #NEXT_AFTER_EVENT_ID}), streamed off its top-level members
     * ({@link ConcolicRegionRuntime#members}): the locations before them
     * are skipped and the expression table after them is not read.  The
     * owner thread holds the VM context meanwhile; parsed whole, a 64 MB
     * page took it eight times as long.  A blank page says nothing; null
     * when it is no JSON object.
     */
    static JsonObject pageHeader(String serialized) {
        return members(serialized, COMPLETE, NEXT_AFTER_EVENT_ID);
    }

    /**
     * The most pages one read-out may take; hitting it is a stated gap, not a
     * truncation.  It stops a VM that never advances from hanging the run.
     */
    private static final int MAX_READ_OUT_PAGES = 4096;

    /**
     * The byte budget of one page; the VM stops at a location boundary, and
     * every page repeats the expression closure its locations share.
     * Measured (solr-18406's V17 seed replay; SB12's obligation
     * 0a1a085e98d056aa, whose read-outs are 50-60 MB): at 64 MB the seed
     * peaked at 328 MB live after a full collection, at 16 and 8 MB at 229
     * and 225; the obligation at 1480, 1290 and 1145 MB, reading 1.6 and 2
     * times 64 MB's text.  Below one location's closure every page repeats
     * it: the seed at 4 MB read 20 times its text in 198 pages and passed
     * 2 GB resident, at 2 MB 4 GB.  16 MB keeps four times that away.
     */
    private static final int READ_OUT_PAGE_BYTES = 16 * 1024 * 1024;

    /**
     * Files what decoding the read-out refused, at the activation's
     * publication, where its pages' decoding used to run: the read-out's
     * fault, then each page's refusals in page order.  A publication that
     * is withheld files none of them, as one that never decoded.
     */
    static void assembleRecordedSharedState(
            ActiveRegion active, SharedStateReadOut readOut) {
        if (readOut == null) return;
        if (!readOut.fault.isEmpty()) {
            refuse(MALFORMED_ENVELOPE, "", readOut.fault);
        }
        for (Runnable refusal : readOut.refusals) refusal.run();
    }

    /**
     * One page of the read-out: location envelopes over the page's
     * expression table, read one location at a time
     * ({@link VmExpressionTable.Store#importReadOutPage}), each filed as its
     * write log record; the page is never parsed or copied whole (a Solr
     * region's 52 MB page was its replay's largest tree).  A page that
     * states another schema, kind or location count than this decoder
     * reads files nothing; its table is imported all the same.
     */
    private static void decodeTrackedLocations(String serialized,
                                               ActiveRegion active,
                                               SharedStateReadOut readOut) {
        long started = System.nanoTime();
        try {
            decodePage(serialized, active, readOut);
        } finally {
            DECODE_NANOS.addAndGet(System.nanoTime() - started);
        }
    }

    /**
     * {@link #decodeTrackedLocations}, untimed.  A location envelope a
     * read-out states again unchanged -- every activation's close reads out
     * every location touched since its entry, so the enclosing ones state
     * an inner one's again -- is filed as the decoding of its first reading
     * ({@link VmExpressionTable.Store#importReadOutPage}), not decoded
     * again; the others are decoded at once by the record decoders ({@code
     * ConcolicResultPublisher#recordDecoders}) and filed in page order.  A
     * page the session withholds ({@code ConcolicResultPublisher#withholds}:
     * the replay ended early) imports its table and files nothing; one
     * withheld while it decodes stops at its next record ({@link Withheld}).
     * A version's expressions are scanned for the VM serializer's truncation
     * marker only once the session's store holds one ({@link
     * VmExpressionTable.Store#truncationMarked}): read-out pages never do,
     * and the scan was a sixth of their decoding (07, replay-e).
     */
    private static void decodePage(String serialized, ActiveRegion active,
                                   SharedStateReadOut readOut) {
        VmExpressionTable.Store store =
                ConcolicRegionRuntime.expressionStore(active);
        store.importReadOutPage(serialized, LOCATIONS, header -> {
            if (readOut != null
                    && ConcolicResultPublisher.withholds(readOut)) {
                return false;
            }
            if (!TRACKED_LOCATIONS_KIND.equals(
                    optionalString(header, "kind"))
                    || optionalInteger(header, "schemaVersion", -1)
                    != PAGE_SCHEMA_VERSION) {
                refuse(MALFORMED_ENVELOPE, "", "tracked-location read-out"
                        + " page of kind " + optionalString(header, "kind")
                        + " and schema " + optionalInteger(header,
                        "schemaVersion", -1) + ", and this jar reads "
                        + TRACKED_LOCATIONS_KIND + " schema "
                        + PAGE_SCHEMA_VERSION);
                return false;
            }
            int stated = optionalInteger(header, "locationCount", -1);
            int carried = optionalInteger(header,
                    VmExpressionTable.RECORD_COUNT, -1);
            if (stated >= 0 && stated != carried) {
                refuse(MALFORMED_ENVELOPE, "",
                        "tracked-location read-out states " + stated
                                + " locations and carries " + carried);
                return false;
            }
            return true;
        }, Filed.class, element -> {
            if (readOut != null && ConcolicResultPublisher.withholds(readOut)) {
                throw Withheld.INSTANCE;
            }
            return decoded(element, store.truncationMarked());
        }, filed -> file(filed, active),
                ConcolicResultPublisher.recordDecoders(),
                ConcolicResultPublisher.RECORD_DECODERS);
    }

    /** A page's decoding stopped: no publication reads it any more. */
    private static final class Withheld extends RuntimeException {
        private static final long serialVersionUID = 1L;
        static final Withheld INSTANCE = new Withheld();

        private Withheld() {
            super("withheld", null, false, false);
        }
    }

    /**
     * One location envelope as the read-out states it: its write log record,
     * or the refusal that replaces it.  Shared by every activation whose
     * read-out states the envelope unchanged, so it is a function of the
     * envelope's text and the session's expression store alone (the store
     * expands each node once and keeps it): it reads nothing an activation
     * or the session's progress holds.
     */
    static final class Filed {
        final String locationKey;
        /** The write log record ({@link #writeLogRecord}); null when the
         *  envelope was refused. */
        final JsonObject record;
        /** Why the envelope was refused; "" when filed. */
        final String fault;
        /** How many versions it lists. */
        final int versions;
        /**
         * Whether a publication walked this record whole ({@code
         * RowPublication#writes}): a later publication holding the same
         * record finds nothing it did not, and walks it no more.  Read and
         * written on the publication thread only.
         */
        boolean walked;

        Filed(String locationKey, JsonObject record, String fault,
              int versions) {
            this.locationKey = locationKey;
            this.record = record;
            this.fault = fault;
            this.versions = versions;
        }
    }

    /**
     * One location envelope's decoding ({@link Filed}): its versions
     * checked -- their expressions scanned for the truncation marker when
     * {@code marked} -- then reduced to its write log record.  Counted as
     * decoded.  Any thread: it reads only the envelope.
     */
    private static Filed decoded(JsonElement element, boolean marked) {
        DECODED.incrementAndGet();
        if (!element.isJsonObject()) {
            return new Filed("", null, "tracked location is not an object",
                    0);
        }
        JsonObject envelope = element.getAsJsonObject();
        int versions = array(envelope, "versions").size();
        // An envelope's versions share their subexpressions: a node scanned
        // clean once is not scanned again.
        String fault = versionsFault(envelope, marked
                ? Collections.newSetFromMap(
                        new IdentityHashMap<JsonElement, Boolean>())
                : null);
        String locationKey = locationKey(envelope);
        return fault.isEmpty()
                ? new Filed(locationKey, writeLogRecord(locationKey,
                envelope), "", versions)
                : new Filed(locationKey, null, fault, versions);
    }

    /**
     * Files one location's write log with the active region, or names the
     * fault that replaced it (and files nothing).
     */
    private static void file(Filed filed, ActiveRegion active) {
        FILED.incrementAndGet();
        VERSIONS.addAndGet(filed.versions);
        if (!filed.fault.isEmpty()) {
            if (active != null && !filed.locationKey.isEmpty()) {
                active.sharedStateRefusals.put(filed.locationKey,
                        filed.fault);
            }
            refuse(expressionSerializationTruncationFault(filed.fault)
                            ? EXPRESSION_SERIALIZATION_TRUNCATED
                            : containerBaseUnstatedFault(filed.fault)
                            ? CONTAINER_BASE_UNSTATED
                            : MALFORMED_ENVELOPE,
                    filed.locationKey, filed.fault);
            return;
        }
        if (active != null) {
            active.sharedStateRecords.put(filed.locationKey, filed);
        }
    }

    /** The member a read-out page holds its location envelopes in. */
    private static final String LOCATIONS = "locations";

    private static final String TRACKED_LOCATIONS_KIND =
            "SHARED_TRACKED_LOCATIONS";
    /** The page this decoder reads: 2, whose table is the read-out
     *  channel's next (VM.md §8); a page of another schema is refused by
     *  name. */
    private static final int PAGE_SCHEMA_VERSION = 2;

    /**
     * One admitted location's write log, reduced to what the rows read:
     * {@code location#version -> expression} plus where each version and
     * read ran.
     *
     * <p>{@code fieldVersionId} is on the same session-global counter as the
     * decisions' {@code vmEventId}, so "latest write before this access" is a
     * comparison within one {@code sessionId} (the counter restarts per
     * session).</p>
     */
    static JsonObject writeLogRecord(String locationKey, JsonObject envelope) {
        JsonArray versions = new JsonArray();
        for (JsonElement element : array(envelope, "versions")) {
            if (!element.isJsonObject()) continue;
            JsonObject version = element.getAsJsonObject();
            JsonObject entry = new JsonObject();
            copyIfPresent(version, entry, "fieldVersionId");
            // Its kind: an INITIAL is a write row flagged as one.
            copyIfPresent(version, entry, "versionKind");
            // Site and activation: the two halves of the WriteRow's
            // endpoint identity (IDENTITY §4); dropping them merges
            // distinct writes into one endpoint.
            copyIfPresent(version, entry, "site");
            copyIfPresent(version, entry, "regionEnterEventId");
            copyIfPresent(version, entry, "expression");
            // A reference write's container state, or why none is stated.
            copyIfPresent(version, entry, REFERENT_STATE);
            copyIfPresent(version, entry, REFERENT_STATE_REFUSED);
            versions.add(entry);
        }
        // The read log, by event id: it supplies the activation a
        // ReadFromExpression node does not name, and states each read under
        // the node's names -- the version its plan chose and how far that
        // is the value it read -- so a read no published expression holds
        // is a row too (RowPublication#loggedReads).  No value: an exact
        // read returned its version's.
        JsonArray reads = new JsonArray();
        for (JsonElement element : array(envelope, "reads")) {
            if (!element.isJsonObject()) continue;
            JsonObject read = element.getAsJsonObject();
            JsonObject entry = new JsonObject();
            copyIfPresent(read, entry, "readEventId");
            copyIfPresent(read, entry, "regionEnterEventId");
            copyIfPresent(read, entry, "site");
            copyIfPresent(read, entry, VmRows.OBSERVED_VERSION);
            copyIfPresent(read, entry, VmRows.OBSERVED_EXACT);
            copyIfPresent(read, entry, VmRows.WRITER_SET_COMPLETE);
            copyIfPresent(read, entry, VmRows.UNNAMED_WRITER);
            copyIfPresent(read, entry, "_java_type");
            reads.add(entry);
        }
        JsonObject kept = new JsonObject();
        kept.add("versions", versions);
        kept.add("reads", reads);
        JsonObject record = new JsonObject();
        record.addProperty("locationKey", locationKey);
        record.add("envelope", kept);
        return record;
    }

    private static void copyIfPresent(JsonObject from, JsonObject to,
                                      String field) {
        JsonElement value = from.get(field);
        if (value != null && !value.isJsonNull()) to.add(field, value);
    }

    /**
     * One refused location: no write version, stated as an UNSTATED_VALUE
     * diagnostic gap, since every read of it reaches the formula with no
     * read-from arm.
     */
    private static void refuse(int status, String locationKey,
                               String detail) {
        List<Runnable> deferred = DECODING.get();
        if (deferred != null) {
            deferred.add(() -> refuse(status, locationKey, detail));
            return;
        }
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                // A blank subject would refuse inside Fields.text.
                firstNonBlank(nonNull(locationKey), STAGE_VERSIONS,
                        RowRuntime.sessionId()),
                reason(status) + ": " + nonNull(detail));
    }

    /**
     * The refusals of the page the decoding thread is decoding, held for
     * its activation's publication ({@link #assembleRecordedSharedState}),
     * or null outside a page's decoding.
     */
    private static final ThreadLocal<List<Runnable>> DECODING =
            new ThreadLocal<List<Runnable>>();

    /**
     * One activation's read-out: its pages are decoded into the activation
     * on the decoding thread as they are read; what is left for its
     * publication, once they are ({@link #awaitDecoded}), is what that
     * decoding refused, and the read-out's fault.
     */
    static final class SharedStateReadOut {
        /** Written by the owner thread before the publication is queued. */
        private String fault = "";
        /** Appended to on the decoding thread, read by the publication
         *  once every page is decoded. */
        private final List<Runnable> refusals = new ArrayList<>();
        /** Pages handed to the decoding thread and not yet decoded. */
        private int pending;
        /** Its publication's place in submission order, 0 until submitted;
         *  guarded by the publisher's lock ({@code ConcolicResultPublisher
         *  #withholds}). */
        long ordinal;

        /**
         * Queues one page's decoding on the decoding thread, behind every
         * page read before it, without a wait ({@code
         * ConcolicResultPublisher#decodeInOrder}): its table is imported
         * there whatever happens to its records, which a page the session
         * withholds by then does not file ({@code ConcolicResultPublisher
         * #withholds}).
         *
         * @return false when the decoding thread refused the work
         */
        private boolean decodeLater(String page, ActiveRegion active) {
            synchronized (this) {
                pending++;
            }
            boolean handed = ConcolicResultPublisher.decodeInOrder(
                    page.length(), () -> {
                        DECODING.set(refusals);
                        try {
                            decodeTrackedLocations(page, active, this);
                        } catch (Withheld withheld) {
                            // Its publication is withheld: nothing to file.
                        } catch (Throwable throwable) {
                            refuse(MALFORMED_ENVELOPE, "",
                                    rootCause(throwable));
                        } finally {
                            DECODING.remove();
                            decoded();
                        }
                    });
            if (!handed) decoded();
            return handed;
        }

        private synchronized void decoded() {
            pending--;
            notifyAll();
        }

        /**
         * Waits until every page handed on is decoded: the publication reads
         * what they filed into its activation, and what they refused.
         */
        synchronized void awaitDecoded() {
            boolean interrupted = false;
            while (pending > 0) {
                try {
                    wait();
                } catch (InterruptedException ignored) {
                    interrupted = true;
                }
            }
            if (interrupted) Thread.currentThread().interrupt();
        }
    }

    // ---- the VM's shared-state vocabulary (this decoder is its one reader)

    /**
     * Schema of the VM's version-store envelope this vocabulary reads: 2,
     * whose read log states each read's chosen version (VM.md §5.2).  An
     * envelope of another schema -- an image older than its jar -- is
     * refused by name, never read as a log of unversioned reads.
     */
    private static final int SCHEMA_VERSION = 2;

    /** Envelope kind of one selected location's version store. */
    private static final String VERSIONS_ENVELOPE_KIND =
            "SHARED_FIELD_VERSIONS";
    /** Node type emitted where the VM serializer bounded one expression. */
    private static final String TRUNCATED_EXPRESSION_TYPE =
            "TruncatedExpression";
    /** Authority proving that a truncated node came from the VM serializer. */
    private static final String VM_SERIALIZATION_TRUNCATION_AUTHORITY =
            "VM_SERIALIZATION_TRUNCATION_V1";

    static final String STAGE_VERSIONS = "VERSIONS";

    private static final int OK = 0;

    /**
     * The one refusal this decoder raises on its own: an envelope it will not
     * admit.  Undeclared statuses read as {@link #UNDECLARED_REASON}.
     */
    private static final int MALFORMED_ENVELOPE = -1002;
    /** One expression root was serialized only up to the VM's safety bound. */
    private static final int EXPRESSION_SERIALIZATION_TRUNCATED = -1007;
    /**
     * A container's INITIAL version states no base contents, so every read of
     * it (base plus mutation chain) stands on nothing.  The gap names the
     * class the VM has no walker for, because that is the fix.
     */
    private static final int CONTAINER_BASE_UNSTATED = -1012;

    /** Exact coverage reason for a VM-bounded expression tree. */
    private static final String VM_EXPRESSION_SERIALIZATION_TRUNCATED =
            "VM_EXPRESSION_SERIALIZATION_TRUNCATED";

    private static final String REASON_PREFIX = "SHARED_STATE_";
    /** Reason used for any status this build does not declare. */
    private static final String UNDECLARED_REASON =
            REASON_PREFIX + "UNDECLARED_STATUS";

    /** Location kind of one selected map's whole immutable state. */
    private static final String LOCATION_KIND_MAP_STATE = "MAP_STATE";
    /** The reserved slot of a whole-state location. */
    private static final int MAP_STATE_SLOT = -3;

    private static final Set<String> LOCATION_KINDS = names("INSTANCE_FIELD",
            "STATIC_FIELD", "ARRAY_ELEMENT", LOCATION_KIND_MAP_STATE);
    /**
     * Kinds of published version a location may carry: the VM's
     * {@code STATE_<operation>} vocabulary (SharedFieldVersions::version_label),
     * and UNOBSERVED: a word the read found that no hooked store left, which
     * names no writer.  Trap: an operation missing here fails the whole
     * envelope, so the location loses every version.
     */
    private static final Set<String> VERSION_KINDS = names("INITIAL", "WRITE",
            "RMW", "UNOBSERVED", "STATE", "STATE_PUT", "STATE_PUT_IF",
            "STATE_PUT_ALL", "STATE_REMOVE", "STATE_REMOVE_IF", "STATE_CLEAR",
            "STATE_REMOVE_AT", "STATE_CLEAR_VIEW", "STATE_ADD",
            "STATE_APPEND", "STATE_INSERT", "STATE_WRITE", "STATE_POLL",
            "STATE_COLLECT", "STATE_ATTACH");
    /**
     * A reference write's container state (R3-REFCONT §1.1): {@code
     * {ownerSymRid, slot, locationKind: MAP_STATE, fieldVersionId}}, the
     * canonical container's location and its version live at the store;
     * or {@link #REFERENT_STATE_REFUSED}, why none is stated.  Only on a
     * WRITE or RMW of a field or an array element.
     */
    static final String REFERENT_STATE = "referentState";
    static final String REFERENT_STATE_REFUSED = "referentStateRefused";
    /** The version kind every location may publish, whatever its shape. */
    private static final String INITIAL_VERSION_KIND = "INITIAL";

    private static String reason(int status) {
        switch (status) {
            case OK:
                return "";
            case MALFORMED_ENVELOPE:
                return REASON_PREFIX + "MALFORMED_ENVELOPE";
            case EXPRESSION_SERIALIZATION_TRUNCATED:
                return VM_EXPRESSION_SERIALIZATION_TRUNCATED;
            case CONTAINER_BASE_UNSTATED:
                return REASON_PREFIX + "CONTAINER_BASE_UNSTATED";
            default:
                return UNDECLARED_REASON;
        }
    }

    /** Whether an expression tree contains the VM's truncation marker. */
    private static boolean containsVmSerializationTruncation(
            JsonElement expression, Set<JsonElement> clean) {
        if (expression == null) return false;
        Deque<JsonElement> pending = new ArrayDeque<>();
        Set<JsonElement> visited = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
        pending.push(expression);
        while (!pending.isEmpty()) {
            JsonElement current = pending.pop();
            if (current != null && !current.isJsonNull()
                    && !current.isJsonPrimitive()
                    && (clean.contains(current)
                    || !visited.add(current))) continue;
            if (current.isJsonArray()) {
                for (JsonElement child : current.getAsJsonArray()) {
                    if (child != null) pending.push(child);
                }
                continue;
            }
            if (!current.isJsonObject()) continue;
            JsonObject term = current.getAsJsonObject();
            if (TRUNCATED_EXPRESSION_TYPE.equals(textString(term, "_type"))
                    && VM_SERIALIZATION_TRUNCATION_AUTHORITY.equals(
                    optionalString(term, "expressionAuthority"))) {
                return true;
            }
            for (String field : term.keySet()) {
                JsonElement child = term.get(field);
                if (child != null) pending.push(child);
            }
        }
        // Scanned whole and found clean: no later scan re-enters it.
        clean.addAll(visited);
        return false;
    }

    /** Whether {@code fault} names exactly this serializer-bound refusal. */
    private static boolean expressionSerializationTruncationFault(
            String fault) {
        return fault != null
                && (VM_EXPRESSION_SERIALIZATION_TRUNCATED.equals(fault)
                || fault.startsWith(
                VM_EXPRESSION_SERIALIZATION_TRUNCATED + ":"));
    }

    /** The location key one version-store envelope describes. */
    private static String locationKey(JsonObject envelope) {
        return locationKeyOf(object(envelope, "location"));
    }

    /**
     * The same key for any VM location node: the one spelling and admission
     * shared by write envelopes and read nodes.  An undeclared kind, a zero
     * owner rid, an absent slot, or a whole-state location off the reserved
     * slot names no location ({@code ""}).
     */
    static String locationKeyOf(JsonObject location) {
        if (location == null || location.size() == 0) return "";
        String kind = optionalString(location, "locationKind");
        if (!LOCATION_KINDS.contains(kind)) return "";
        long owner = optionalLongInteger(location, "ownerSymRid", 0L);
        if (owner == 0L || !location.has("slot")) return "";
        int slot = optionalInteger(location, "slot", 0);
        if (LOCATION_KIND_MAP_STATE.equals(kind) && slot != MAP_STATE_SLOT) {
            return "";
        }
        return kind + "/" + owner + "#" + slot;
    }

    /**
     * The contract location one VM location key names, or {@code null}.  No
     * default kind: defaulting to {@code INSTANCE} makes a read that joins
     * nothing.
     */
    static LocationId locationId(
            String locationKey) {
        String key = nonNull(locationKey);
        int separator = key.indexOf('/');
        int slot = key.lastIndexOf('#');
        if (separator <= 0 || slot <= separator) return null;
        String kind = key.substring(0, separator);
        LocationKind declared;
        if ("INSTANCE_FIELD".equals(kind)) {
            declared = LocationKind.INSTANCE;
        } else if ("STATIC_FIELD".equals(kind)) {
            declared = LocationKind.STATIC;
        } else if ("ARRAY_ELEMENT".equals(kind)) {
            declared = LocationKind.ARRAY;
        } else if (LOCATION_KIND_MAP_STATE.equals(kind)) {
            declared = LocationKind.MAP;
        } else {
            return null;
        }
        return LocationId.of(declared,
                key.substring(separator + 1, slot), key.substring(slot + 1));
    }

    /** Whether {@code versionKind} publishes one immutable whole state. */
    private static boolean stateVersionKind(String versionKind) {
        return versionKind != null && (versionKind.equals("STATE")
                || versionKind.startsWith("STATE_"));
    }

    /** Admits one version-store envelope: {@code ""} or the refusal
     *  reason; {@code clean} null: no expression holds the truncation
     *  marker, so none is scanned for it. */
    private static String versionsFault(JsonObject envelope,
                                        Set<JsonElement> clean) {
        if (envelope == null || envelope.size() == 0) {
            return "no version envelope";
        }
        if (!VERSIONS_ENVELOPE_KIND.equals(optionalString(envelope, "kind"))) {
            return "envelope is not an authoritative version store";
        }
        int schema = optionalInteger(envelope, "schemaVersion", -1);
        if (schema != SCHEMA_VERSION) {
            return "version store of schema " + schema + ", and this jar"
                    + " reads schema " + SCHEMA_VERSION + " (a VM image"
                    + " whose read log states no read's version?)";
        }
        if (!booleanMember(envelope, "selected")
                || !optionalBool(envelope, "selected", false)) {
            return "location was never selected as a carrier";
        }
        if (locationKey(envelope).isEmpty()) {
            return "envelope names no addressable location";
        }
        if (!booleanMember(envelope, "writerSetComplete")) {
            return "envelope omits writer-set completeness";
        }
        JsonElement versionsMember = envelope.get("versions");
        if (versionsMember == null || !versionsMember.isJsonArray()) {
            return "envelope carries no version array";
        }
        if (!booleanMember(envelope, "serializationTruncated")) {
            return "envelope omits version serialization completeness";
        }
        // Before the count: an envelope cut before its first version is
        // truncated, not empty.
        if (optionalBool(envelope, "serializationTruncated", false)) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": version envelope";
        }
        JsonArray versions = array(envelope, "versions");
        if (versions.size() == 0) {
            // Selection publishes an INITIAL, so empty means no selection.
            return "selected location published no version";
        }
        // A selected map's whole state (#locationKeyOf's spelling).
        boolean mapState = locationKey(envelope).startsWith(
                LOCATION_KIND_MAP_STATE + "/");
        Set<Long> versionIds = new LinkedHashSet<>();
        for (JsonElement element : versions) {
            if (!element.isJsonObject()) return "version is not an object";
            String fault = versionFault(element.getAsJsonObject(), mapState,
                    clean);
            if (!fault.isEmpty()) return fault;
            long id = optionalLongInteger(element.getAsJsonObject(),
                    "fieldVersionId", 0L);
            if (!versionIds.add(id)) {
                return "duplicate fieldVersionId " + id;
            }
        }
        JsonElement readsMember = envelope.get("reads");
        if (readsMember == null || !readsMember.isJsonArray()) {
            return "envelope carries no read array";
        }
        JsonArray reads = readsMember.getAsJsonArray();
        if (!booleanMember(envelope, "readLogTruncated")) {
            return "envelope omits read-log completeness";
        }
        for (JsonElement element : reads) {
            if (!element.isJsonObject()) return "read is not an object";
            String fault = readFault(element.getAsJsonObject());
            if (!fault.isEmpty()) return fault;
        }
        return "";
    }

    /**
     * Why a container's INITIAL version states no base, or {@code ""}.  A
     * missing snapshot is an older VM image; {@code stated:false} means no
     * walker for the class.
     */
    private static String containerBaseFault(JsonObject version,
                                             String versionKind,
                                             boolean mapState) {
        if (!mapState || !INITIAL_VERSION_KIND.equals(versionKind)) return "";
        JsonElement encoded = version.get("initialSnapshot");
        if (encoded == null || !encoded.isJsonObject()) {
            return CONTAINER_BASE_UNSTATED_FAULT
                    + ": INITIAL states no container base";
        }
        JsonObject snapshot = encoded.getAsJsonObject();
        if (!snapshot.has("stated")
                || optionalBool(snapshot, "stated", false)) {
            return "";
        }
        String unsupported = optionalString(snapshot, "unsupportedClass");
        return CONTAINER_BASE_UNSTATED_FAULT + ": the VM walks no container "
                + "of class " + (unsupported.isEmpty() ? "<unnamed>"
                : unsupported);
    }

    /** Fault prefix that maps to {@link #CONTAINER_BASE_UNSTATED}. */
    private static final String CONTAINER_BASE_UNSTATED_FAULT =
            "CONTAINER_BASE_UNSTATED";

    /** Whether {@code fault} is an unstated container base. */
    private static boolean containerBaseUnstatedFault(String fault) {
        return fault != null && fault.startsWith(CONTAINER_BASE_UNSTATED_FAULT);
    }

    /**
     * Whether a version is its location's INITIAL: the value from before
     * every store the log names, which whichever access first observed the
     * location started its log with -- a scalar's word, a container's
     * members (the base its chain of mutations stands on).  No occurrence
     * wrote it (WriteRow#initial).
     */
    static boolean initial(JsonObject version) {
        return INITIAL_VERSION_KIND.equals(
                optionalString(version, "versionKind"));
    }

    /** Whether a version was stored outside every region: it names no
     *  writer context, region, task or activation at all. */
    static boolean unattributed(JsonObject version) {
        return optionalLongInteger(version, "writerContextId", 0L) == 0L
                && optionalLongInteger(version, "regionEnterEventId", 0L) == 0L
                && optionalString(version, "regionId").isEmpty()
                && optionalString(version, "taskId").isEmpty();
    }

    private static String versionFault(JsonObject version, boolean mapState,
                                       Set<JsonElement> clean) {
        long id = optionalLongInteger(version, "fieldVersionId", 0L);
        if (id <= 0L) return "version has no fieldVersionId";
        String versionKind = optionalString(version, "versionKind");
        if (!VERSION_KINDS.contains(versionKind)) {
            return "version " + id + " has kind \"" + versionKind
                    + "\", which this jar does not know (a VM image newer"
                    + " than its jar?)";
        }
        if (!INITIAL_VERSION_KIND.equals(versionKind)
                && stateVersionKind(versionKind) != mapState) {
            return "version " + id + " has kind " + versionKind
                    + " that its location kind does not publish";
        }
        // All three name the region that wrote it; none of them, a store
        // outside every region (a thread with no concolic context), which
        // is a version with no writer row.  Some of them is malformed.
        if (!unattributed(version)
                && (optionalLongInteger(version, "regionEnterEventId", 0L) <= 0L
                || optionalString(version, "regionId").isEmpty()
                || optionalString(version, "taskId").isEmpty())) {
            return "version " + id + " names no writer case";
        }
        if (!version.has("pathGuard")) {
            // Explicit null is the empty conjunction; absent is uncaptured.
            return "version " + id + " omits its writer path guard";
        }
        String base = containerBaseFault(version, versionKind, mapState);
        if (!base.isEmpty()) return base;
        String referent = referentFault(version, id, versionKind, mapState);
        if (!referent.isEmpty()) return referent;
        JsonElement expression = version.get("expression");
        if (expression == null || expression.isJsonNull()) {
            return "version " + id + " carries no value expression";
        }
        if (clean == null) return "";
        if (containsVmSerializationTruncation(expression, clean)) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": version " + id + " value expression";
        }
        if (containsVmSerializationTruncation(version.get("pathGuard"),
                clean)) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": version " + id + " path guard";
        }
        return "";
    }

    /**
     * Why a version's referent members are malformed, or {@code ""}: they
     * belong to a WRITE or RMW of a field or an element, at most one of
     * them, and a state names a MAP_STATE location's version older than
     * this one.
     */
    private static String referentFault(JsonObject version, long id,
                                        String versionKind,
                                        boolean mapState) {
        JsonElement state = version.get(REFERENT_STATE);
        JsonElement refused = version.get(REFERENT_STATE_REFUSED);
        if (state == null && refused == null) return "";
        if (mapState || !("WRITE".equals(versionKind)
                || "RMW".equals(versionKind))) {
            return "version " + id + " of kind " + versionKind
                    + " states a referent";
        }
        if (state != null && refused != null) {
            return "version " + id + " states a referent and refuses it";
        }
        if (refused != null) {
            return refused.isJsonPrimitive()
                    && !refused.getAsString().trim().isEmpty() ? ""
                    : "version " + id + " refuses its referent by no name";
        }
        JsonObject named = state.isJsonObject() ? state.getAsJsonObject()
                : new JsonObject();
        long at = optionalLongInteger(named, "fieldVersionId", 0L);
        if (!locationKeyOf(named).startsWith(LOCATION_KIND_MAP_STATE + "/")
                || at <= 0L || at >= id) {
            return "version " + id + " states a referent that is no older "
                    + "MAP_STATE version";
        }
        return "";
    }

    private static String readFault(JsonObject read) {
        long readEvent = optionalLongInteger(read, "readEventId", 0L);
        if (readEvent <= 0L) return "read has no readEventId";
        if (optionalLongInteger(read, "regionEnterEventId", 0L) <= 0L
                || optionalString(read, "regionId").isEmpty()
                || optionalString(read, "taskId").isEmpty()) {
            return "read " + readEvent + " names no reader case";
        }
        if (VmRows.recordedVersion(read) <= 0L
                || !booleanMember(read, VmRows.OBSERVED_EXACT)
                || !booleanMember(read, VmRows.WRITER_SET_COMPLETE)) {
            return "read " + readEvent + " states no version it observed";
        }
        return "";
    }

    private static boolean booleanMember(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean();
    }

    private static Set<String> names(String... values) {
        return Collections.unmodifiableSet(
                new LinkedHashSet<>(Arrays.asList(values)));
    }
}
