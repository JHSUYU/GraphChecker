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
import java.util.function.Consumer;

/**
 * WHAT A CORPUS HOLDS OF ITS SESSIONS' READS AND WRITES: at most {@link
 * #bytes} of their files' text (as it decodes, {@link
 * ArtifactIO#decodedSize}), the sessions asked for least recently let go of
 * first ({@link SessionReader#reads}).  A session's reads and writes let go
 * of are read again from its files when next asked, value for value the
 * rows it read (a landed session's files never change), so a reader of the
 * corpus sees the rows it would have seen with every session held.
 *
 * <p>COMPOSE's corpus ({@code explore.Corpus#holding}): one path's
 * composition asks of most sessions their decisions, activations, exports
 * and expressions (the arms of its families: every sender's pi and export),
 * of a few their reads and writes (the path's own session and the producers
 * whose arms it closes: 1-8 of SGF8-adhoc-39's 71 sessions, 55 touched), and
 * those are most of a corpus's heap: SGF8-adhoc-13's 201 sessions held 1260
 * MB with them, 516 without; SGF8-adhoc-07's 358 sessions, 28.4 GB of rows
 * of which 14.6 GB reads and writes, filled 85 % of its composer's old
 * generation, and one of its 309 paths was composed.</p>
 *
 * <p>What the corpus builds of a session's reads and writes goes with them
 * ({@link #released}).  Thread-safe; a session is let go of only by a load
 * of another one, never the one loaded.</p>
 */
public final class RowHold {
    /** One session held, and what its reads and writes decode to. */
    private static final class Unit {
        final SessionReader session;
        final long size;

        Unit(SessionReader session, long size) {
            this.session = session;
            this.size = size;
        }
    }

    /** The most text it holds, in decoded bytes. */
    private final long bytes;
    /** Told of each session let go of, after it is: what was built of its
     *  reads and writes goes too. */
    private final Consumer<SessionReader> released;
    /** Session id -> its unit, least recently asked first. */
    private final LinkedHashMap<String, Unit> held =
            new LinkedHashMap<String, Unit>(16, 0.75f, true);
    private long holding;
    /** How many sessions were read again, and their text. */
    private long reads;
    private long readBytes;

    public RowHold(long bytes, Consumer<SessionReader> released) {
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

    /** How many sessions it read again, and their text in decoded bytes. */
    public synchronized long[] readAgain() {
        return new long[] {reads, readBytes};
    }

    /**
     * Takes {@code session}, read whole, into the hold: its reads and writes
     * are held, and may be let go of from now on.  A session not read whole
     * ({@link SessionReader#incomplete}) is held for good: what its read
     * refused is its rows.
     */
    public void take(SessionReader session) {
        if (!session.incomplete().isEmpty()) return;
        session.heldBy(this);
        held(session);
    }

    /** {@code session}'s reads and writes were asked for, and are held. */
    public synchronized void used(SessionReader session) {
        held.get(session.sessionId());
    }

    /** {@code session}'s reads and writes, let go of, are read again
     *  ({@link #held}). */
    void loaded(SessionReader session) {
        synchronized (this) {
            reads++;
            readBytes += session.heldBytes();
        }
        held(session);
    }

    /**
     * {@code session}'s reads and writes are held (read, or read again): the
     * sessions asked for least recently are let go of while the hold is past
     * its bytes, never this one.
     */
    private void held(SessionReader session) {
        long size = session.heldBytes();
        List<Unit> out = new ArrayList<Unit>();
        synchronized (this) {
            Unit unit = new Unit(session, size);
            Unit was = held.put(session.sessionId(), unit);
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
            unit.session.release();
            released.accept(unit.session);
        }
    }

    /** What the files of one session's reads and writes decode to. */
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
