package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.AccessSites;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadsFrom;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * THE VERSIONS A REPLAY'S WORLD CHOSE, held and checked.
 *
 * <p>A shared location holds many versions and a read observes the one that
 * is live when it runs.  The focus row names, for the reads its question
 * rests on, the write each observes ({@code contract.ReadsFrom}): the
 * version z3 chose among the writers the read could have observed, or the
 * recording's own where the writer ran on another thread.  The weave puts a
 * hook before and after every shared-state access of the replayed classes
 * ({@code CausynthPipeline#instrumentSharedAccess}), and this is the rule
 * they call:</p>
 * <ul>
 *   <li>a HELD READ waits until its writer's version is the live one;</li>
 *   <li>a WRITE waits while the live version is owed to a held read that has
 *       not read it yet -- going first, it would take the version from under
 *       the read;</li>
 *   <li>everything else runs free.  The partial order a replay holds is
 *       exactly the reads-from its world chose; program order, the messages
 *       and the program's own locks order the rest.</li>
 * </ul>
 *
 * <p>An access is named at its hook as its row will name it: the VM site of
 * the access ({@code contract.AccessSites}), the occurrence the VM states for
 * the thread's region, and the frames its journal stands on
 * ({@code FrameJournal}) -- the function {@code LoggedEventSites} names a
 * logged event with.  Which version is live the VM answers itself
 * ({@code ConcolicVmBroker#liveSharedVersion}), because only the VM knows
 * that a view and the map it views are one location; the version of a held
 * writer is mapped to its endpoint when that write is done.</p>
 *
 * <p>UNREACHABLE.  A held read that waits out {@link #TIMEOUT_PROPERTY}
 * waits for a version the program's own coordination keeps from it -- a lock
 * its writer needs, a message its thread must send first -- and the owner's
 * rule is that such a choice cannot be hit: the read goes on and is
 * UNREALIZED ({@code VERSION_UNREALIZED}), which the verdict carries.  A
 * write that waits out the same timeout goes on too, and the reads still
 * owed are left to their own check: a read that never comes has observed
 * nothing, and one that comes and finds another version is unrealized
 * there.  The rows are the last word: a held read whose row names another
 * writer is unrealized whatever the gate saw, since a write no hook stands
 * before can still take a version.</p>
 */
public final class Versions {
    /** How long a held access may wait, in ms. */
    public static final String TIMEOUT_PROPERTY =
            "causynth.versions.timeout.ms";
    /** The directory of the woven classes a replay runs. */
    public static final String CLASSES_PROPERTY = "causynth.concolic.classes";
    static final long DEFAULT_TIMEOUT_MS = 60000L;
    private static final long SLICE_MS = 200L;

    private static final Object LOCK = new Object();
    private static final int UNLOADED = 0;
    private static final int IDLE = 1;
    private static final int HOLDING = 2;
    /** Whether any read is held: the one test every hook pays for. */
    private static volatile int state = UNLOADED;

    /** Woven site id -> VM site of the access it stands before. */
    private static AccessSites sites;
    /** Reader endpoint id -> the writer endpoint id it observes. */
    private static final Map<String, String> WRITER_OF =
            new HashMap<String, String>();
    private static final Set<String> READ_SITES = new HashSet<String>();
    private static final Set<String> WRITE_SITES = new HashSet<String>();
    /** Writer endpoint id -> the held reads of its version still to come. */
    private static final Map<String, Set<String>> OWED =
            new HashMap<String, Set<String>>();
    /** VM version id -> the held writer whose write published it. */
    private static final Map<Long, String> WRITER_OF_VERSION =
            new HashMap<Long, String>();
    /** Held writers whose write is done (for an untracked location). */
    private static final Set<String> WROTE = new HashSet<String>();
    /** How many held reads are still owed their version, in all. */
    private static int owedReads;
    /** Reader endpoint id -> why its version was not realized. */
    private static final Map<String, String> UNREALIZED =
            new LinkedHashMap<String, String>();
    /** (location, version) -> the endpoint the rows state wrote it. */
    private static final Map<String, String> PUBLISHED =
            new HashMap<String, String>();
    /** Reader endpoint id -> the (location, version) its row observed. */
    private static final Map<String, String> OBSERVED =
            new LinkedHashMap<String, String>();

    /** One access between its two hooks, on the thread making it. */
    private static final class Access {
        final Object owner;
        final String declaring;
        final String field;
        final String descriptor;
        final boolean write;
        final String site;
        /** The held reader or writer this access is, or null. */
        String endpoint;

        Access(Object owner, String declaring, String field,
               String descriptor, boolean write, String site) {
            this.owner = owner;
            this.declaring = declaring;
            this.field = field;
            this.descriptor = descriptor;
            this.write = write;
            this.site = site;
        }
    }

    private static final ThreadLocal<Access> PENDING =
            new ThreadLocal<Access>();

    private Versions() {
    }

    /** Before one read of shared state at a woven site. */
    static void read(Object owner, String declaring, String field,
                     String descriptor, String site) {
        if (holding()) before(new Access(owner, declaring, field, descriptor,
                false, site));
    }

    /** Before one write of shared state at a woven site. */
    static void write(Object owner, String declaring, String field,
                      String descriptor, String site) {
        if (holding()) before(new Access(owner, declaring, field, descriptor,
                true, site));
    }

    /** After the access the last hook of this thread stood before. */
    static void done(String site) {
        if (!holding()) return;
        Access access = PENDING.get();
        if (access == null || !access.site.equals(site)) return;
        PENDING.remove();
        if (access.endpoint == null) return;
        synchronized (LOCK) {
            if (access.write) {
                long live = live(access);
                if (live > 0L) WRITER_OF_VERSION.put(live, access.endpoint);
                WROTE.add(access.endpoint);
            } else {
                settle(access.endpoint);
            }
            LOCK.notifyAll();
        }
    }

    private static void before(Access access) {
        String vmSite = sites.vmSite(access.site);
        if (vmSite == null) return;
        synchronized (LOCK) {
            if (access.write) {
                yieldOwedVersion(access);
                if (WRITE_SITES.contains(vmSite)) {
                    access.endpoint = here(vmSite);
                }
            } else if (READ_SITES.contains(vmSite)) {
                String reader = here(vmSite);
                String writer = reader == null ? null : WRITER_OF.get(reader);
                if (writer != null) {
                    access.endpoint = reader;
                    awaitVersion(access, writer);
                }
            }
        }
        if (access.endpoint != null) PENDING.set(access);
    }

    /** A held read is no longer owed its version. */
    private static void settle(String reader) {
        Set<String> owed = OWED.get(WRITER_OF.get(reader));
        if (owed != null && owed.remove(reader)) owedReads--;
    }

    /** Holds a read until the version of {@code writer} is live. */
    private static void awaitVersion(Access access, String writer) {
        long deadline = System.currentTimeMillis() + timeout();
        while (true) {
            long live = live(access);
            String liveWriter = live > 0L ? WRITER_OF_VERSION.get(live)
                    : WROTE.contains(writer) ? writer : null;
            if (writer.equals(liveWriter)) return;
            long left = deadline - System.currentTimeMillis();
            if (left <= 0L) {
                unrealized(access.endpoint, "the read waited "
                        + timeout() + " ms for the version of writer "
                        + writer + " and the location held "
                        + (live <= 0L ? "no version a hook saw"
                        : liveWriter == null ? "version " + live
                        + " of a writer the world did not choose"
                        : "the version of writer " + liveWriter));
                settle(access.endpoint);
                return;
            }
            waitSlice(left);
        }
    }

    /**
     * Holds a write while the live version of its location is owed to a
     * held read that has not read it.
     */
    private static void yieldOwedVersion(Access access) {
        long deadline = System.currentTimeMillis() + timeout();
        while (owedReads > 0) {
            long live = live(access);
            String liveWriter = live > 0L ? WRITER_OF_VERSION.get(live)
                    : null;
            Set<String> owed = liveWriter == null ? null
                    : OWED.get(liveWriter);
            if (owed == null || owed.isEmpty()) return;
            long left = deadline - System.currentTimeMillis();
            if (left <= 0L) {
                // The reads still owed are left to their own check: one that
                // never comes observed nothing.  They no longer hold writes.
                owedReads -= owed.size();
                owed.clear();
                return;
            }
            waitSlice(left);
        }
    }

    private static void waitSlice(long left) {
        try {
            LOCK.wait(Math.min(left, SLICE_MS));
        } catch (InterruptedException interrupted) {
            // The workload's interrupt is the workload's: keep it pending.
            Thread.currentThread().interrupt();
        }
    }

    /** The version live at the location an access touches, or 0. */
    private static long live(Access access) {
        try {
            return ConcolicVmBroker.engine().liveSharedVersion(access.owner,
                    access.declaring, access.field, access.descriptor, -1);
        } catch (Throwable unanswered) {
            return 0L;
        }
    }

    /**
     * The endpoint id the rows will name the access at {@code vmSite} by,
     * or null when this thread stands in no activation of this session.
     */
    private static String here(String vmSite) {
        try {
            ConcolicVmBroker vm = ConcolicVmBroker.engine();
            long activation = vm.currentRegionEnterEventId();
            OccurrenceAddress performer = RowRuntime.occurrenceAt(activation);
            if (performer == null) return null;
            String frames = RowRuntime.framesOf(activation,
                    vm.currentEventId() + 1L);
            return Endpoint.of(performer, vmSite,
                    ExecutionIndex.parse(frames == null ? "" : frames), 0)
                    .id();
        } catch (Throwable unnamed) {
            return null;
        }
    }

    private static void unrealized(String reader, String why) {
        if (UNREALIZED.containsKey(reader)) return;
        UNREALIZED.put(reader, why);
        RowRuntime.gap(GapKind.VERSION_UNREALIZED, GapClass.DIAGNOSTIC,
                reader, why);
    }

    // ---- the rows ---------------------------------------------------------

    /** One write this run published. */
    static void published(LocationId location, long version,
                          Endpoint writer) {
        if (location == null || writer == null || !versioned()) return;
        synchronized (LOCK) {
            PUBLISHED.put(key(location, version), writer.id());
        }
    }

    /** One read this run published, with the version it observed. */
    static void observed(Endpoint reader, LocationId location,
                         long version) {
        if (reader == null || location == null || !versioned()) return;
        synchronized (LOCK) {
            if (WRITER_OF.containsKey(reader.id())) {
                OBSERVED.put(reader.id(), key(location, version));
            }
        }
    }

    /**
     * Why the world's versions were not realized, or {@code ""}: the reads
     * the gate could not give their version, and the published reads whose
     * row names another writer than the world chose.
     */
    static String unrealized() {
        load();
        synchronized (LOCK) {
            Map<String, String> why =
                    new LinkedHashMap<String, String>(UNREALIZED);
            for (Map.Entry<String, String> read : OBSERVED.entrySet()) {
                String writer = PUBLISHED.get(read.getValue());
                String chosen = WRITER_OF.get(read.getKey());
                if (chosen.equals(writer) || why.containsKey(read.getKey())) {
                    continue;
                }
                why.put(read.getKey(), "the read observed " + read.getValue()
                        + (writer == null ? ", which no write of this run "
                        + "states" : ", written by " + writer)
                        + ", where the world chose writer " + chosen);
            }
            if (why.isEmpty()) return "";
            Map.Entry<String, String> first = why.entrySet().iterator().next();
            return "the world's versions were not realized at " + why.size()
                    + " read(s); the first, " + first.getKey() + ": "
                    + first.getValue();
        }
    }

    /** The held reads the run published a row for. */
    static Set<String> readersObserved() {
        synchronized (LOCK) {
            return new LinkedHashSet<String>(OBSERVED.keySet());
        }
    }

    /** Every held read, by its endpoint id, with its writer's. */
    static Map<String, String> held() {
        load();
        synchronized (LOCK) {
            return new LinkedHashMap<String, String>(WRITER_OF);
        }
    }

    private static String key(LocationId location, long version) {
        return location.kind() + "/" + location.owner() + "#"
                + location.slot() + "@" + version;
    }

    // ---- loading ----------------------------------------------------------

    /** Whether the gate holds accesses: versions, and a table to name them. */
    private static boolean holding() {
        if (state == UNLOADED) load();
        return state == HOLDING;
    }

    /** Whether this replay's world chose any version: the rows are checked. */
    private static boolean versioned() {
        if (state == UNLOADED) load();
        synchronized (LOCK) {
            return !WRITER_OF.isEmpty();
        }
    }

    /**
     * Reads the world's versions and the site table once.  The focus row is
     * read before this class's lock is taken: the replay's verdict asks this
     * class under the focus row's lock, so the two locks are only ever taken
     * in that order.
     */
    private static void load() {
        if (state != UNLOADED) return;
        List<ReadsFrom> versions = FocusedReplay.versions();
        String classes = System.getProperty(CLASSES_PROPERTY);
        AccessSites table;
        try {
            table = AccessSites.read(classes == null || classes.isEmpty()
                    ? null : Paths.get(classes));
        } catch (IOException unreadable) {
            table = null;
        }
        synchronized (LOCK) {
            if (state != UNLOADED) return;
            for (ReadsFrom version : versions) {
                WRITER_OF.put(version.reader(), version.writer());
                READ_SITES.add(version.readerSite());
                WRITE_SITES.add(version.writerSite());
                Set<String> owed = OWED.get(version.writer());
                if (owed == null) {
                    owed = new HashSet<String>();
                    OWED.put(version.writer(), owed);
                }
                if (owed.add(version.reader())) owedReads++;
            }
            sites = table;
            if (!WRITER_OF.isEmpty() && (sites == null || sites.isEmpty())) {
                // Held reads with no table to name an access by: every one
                // of them is unrealized, and the verdict says why.
                for (String reader : WRITER_OF.keySet()) {
                    UNREALIZED.put(reader, "the replay's woven classes "
                            + "state no access sites ("
                            + AccessSites.FILE + " under " + classes
                            + "), so no read could be held");
                }
            }
            state = WRITER_OF.isEmpty() || sites == null || sites.isEmpty()
                    ? IDLE : HOLDING;
        }
    }

    private static long timeout() {
        String configured = System.getProperty(TIMEOUT_PROPERTY);
        if (configured != null) {
            try {
                long millis = Long.parseLong(configured.trim());
                if (millis > 0L) return millis;
            } catch (NumberFormatException ignored) {
                // The default stands; the property is not this rule's to
                // refuse a run over.
            }
        }
        return DEFAULT_TIMEOUT_MS;
    }

    static void resetForTests() {
        synchronized (LOCK) {
            state = UNLOADED;
            sites = null;
            WRITER_OF.clear();
            READ_SITES.clear();
            WRITE_SITES.clear();
            OWED.clear();
            WRITER_OF_VERSION.clear();
            WROTE.clear();
            UNREALIZED.clear();
            PUBLISHED.clear();
            OBSERVED.clear();
            owedReads = 0;
        }
    }
}
