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

public final class RowHold {
    private static final class Unit {
        final SessionReader session;
        final long size;

        Unit(SessionReader session, long size) {
            this.session = session;
            this.size = size;
        }
    }

    private final long bytes;
    private final Consumer<SessionReader> released;
    private final LinkedHashMap<String, Unit> held =
            new LinkedHashMap<String, Unit>(16, 0.75f, true);
    private long holding;
    private long reads;
    private long readBytes;

    public RowHold(long bytes, Consumer<SessionReader> released) {
        this.bytes = Math.max(0L, bytes);
        this.released = released;
    }

    public long bytes() {
        return bytes;
    }

    public synchronized long holding() {
        return holding;
    }

    public synchronized long[] readAgain() {
        return new long[] {reads, readBytes};
    }

    public void take(SessionReader session) {
        if (!session.incomplete().isEmpty()) return;
        session.heldBy(this);
        held(session);
    }

    public synchronized void used(SessionReader session) {
        held.get(session.sessionId());
    }

    void loaded(SessionReader session) {
        synchronized (this) {
            reads++;
            readBytes += session.heldBytes();
        }
        held(session);
    }

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
