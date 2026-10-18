package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.function.BiConsumer;

/**
 * WHAT A CORPUS HOLDS OF ITS SESSIONS' READS, WRITES AND GAPS: at most
 * {@link #bytes} of their files' text (as it decodes, {@link
 * ArtifactIO#decodedSize}), the ones asked for least recently let go first
 * ({@link SessionReader#reads}).  A session's rows let go of are read again
 * from its files when next asked, value for value the rows it read (a
 * landed session's files never change), so a reader of the corpus sees the
 * rows it would have seen with every session held.
 *
 * <p>COMPOSE's corpus ({@code explore.Corpus#holding}): one path's
 * composition asks of most sessions their decisions, activations, exports
 * and expressions (the arms of its families: every sender's pi and export),
 * of a few their reads and writes (the path's own session and the producers
 * whose arms it closes: 1-8 of SGF8-adhoc-39's 71 sessions, 55 touched), and
 * those are most of a corpus's heap: SGF8-adhoc-13's 201 sessions held 1260
 * MB with them, 516 without; SGF8-adhoc-07's 358 sessions, 28.4 GB of rows of
 * which 14.6 GB reads and writes and 1.9 GB gaps, filled 85 % of its
 * composer's old generation, and one of its 309 paths was composed.</p>
 *
 * <p>Two units a session: its reads and writes together ({@link
 * Kind#STATE}: what the corpus indexes them by goes with them, {@link
 * #released}), and its gaps.  Thread-safe; a unit is let go of only by a
 * load of another one, never the one loaded.</p>
 */
public final class RowHold {
    /** What one session holds apart. */
    public enum Kind {
        /** Its reads and writes. */
        STATE,
        /** Its gaps. */
        GAPS
    }

    /** One session's unit, held. */
    private static final class Unit {
        final SessionReader session;
        final Kind kind;
        final long size;

        Unit(SessionReader session, Kind kind, long size) {
            this.session = session;
            this.kind = kind;
            this.size = size;
        }
    }

    /** The most text it holds, in decoded bytes. */
    private final long bytes;
    /** Told of each unit let go of, after it is: what was built of it goes
     *  too. */
    private final BiConsumer<SessionReader, Kind> released;
    /** Session id and kind -> its unit, least recently asked first. */
    private final LinkedHashMap<String, Unit> held =
            new LinkedHashMap<String, Unit>(16, 0.75f, true);
    private long holding;
    /** How many units were read again, and their text. */
    private long reads;
    private long readBytes;

    public RowHold(long bytes, BiConsumer<SessionReader, Kind> released) {
        this.bytes = Math.max(0L, bytes);
        this.released = released;
    }

    /** The most text it holds, in decoded bytes. */
    public long bytes() {
        return bytes;
    }

    /** The text it holds now, in decoded bytes. */
    public synchronized long holding() {
        return holding;
    }

    /** How many units it read again, and their text in decoded bytes. */
    public synchronized long[] readAgain() {
        return new long[] {reads, readBytes};
    }

    /**
     * Takes {@code session}, read whole, into the hold: its reads, writes
     * and gaps are held, and may be let go of from now on.  A session not
     * read whole ({@link SessionReader#incomplete}) is held for good: what
     * its read refused is its rows.
     */
    public void take(SessionReader session) {
        if (!session.incomplete().isEmpty()) return;
        session.heldBy(this);
        held(session, Kind.STATE);
        held(session, Kind.GAPS);
    }

    /** {@code kind} of {@code session} was asked for, and is held. */
    public synchronized void used(SessionReader session, Kind kind) {
        held.get(key(session, kind));
    }

    /** {@code kind} of {@code session}, let go of, is read again ({@link
     *  #held}). */
    void loaded(SessionReader session, Kind kind) {
        synchronized (this) {
            reads++;
            readBytes += size(session, kind);
        }
        held(session, kind);
    }

    /**
     * {@code kind} of {@code session} is held (read, or read again): the
     * units asked for least recently are let go of while the hold is past
     * its bytes, never this one.
     */
    private void held(SessionReader session, Kind kind) {
        long size = size(session, kind);
        List<Unit> out = new ArrayList<Unit>();
        synchronized (this) {
            Unit unit = new Unit(session, kind, size);
            Unit was = held.put(key(session, kind), unit);
            holding += size - (was == null ? 0L : was.size);
            for (Iterator<Unit> eldest = held.values().iterator();
                 holding > bytes && eldest.hasNext(); ) {
                Unit next = eldest.next();
                if (next == unit) continue;
                eldest.remove();
                holding -= next.size;
                out.add(next);
            }
        }
        for (Unit unit : out) {
            unit.session.release(unit.kind);
            released.accept(unit.session, unit.kind);
        }
    }

    private static String key(SessionReader session, Kind kind) {
        return kind.name() + "|" + session.sessionId();
    }

    /** What one unit's files decode to ({@link SessionReader#heldBytes}). */
    private static long size(SessionReader session, Kind kind) {
        return session.heldBytes(kind);
    }

    /** What the files of one unit decode to. */
    static long decoded(Path... files) {
        long size = 0L;
        try {
            for (Path file : files) {
                if (Files.isRegularFile(file)) {
                    size += ArtifactIO.decodedSize(file);
                }
            }
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        return size;
    }
}
