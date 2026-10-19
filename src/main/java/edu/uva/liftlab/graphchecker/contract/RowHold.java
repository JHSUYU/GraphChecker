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
import java.util.function.DoubleSupplier;

public final class RowHold {
    private static final class Unit {
        final SessionReader session;
        final long size;

        Unit(SessionReader session, long size) {
            this.session = session;
            this.size = size;
        }
    }

    public static final double SHARE = 0.6;

    private final DoubleSupplier swept;
    private final Consumer<SessionReader> released;
    private final LinkedHashMap<String, Unit> held =
            new LinkedHashMap<String, Unit>(16, 0.75f, true);
    private long bytes = Long.MAX_VALUE;
    private double answered = -1.0;
    private long holding;
    private long reads;
    private long readBytes;

    public RowHold(DoubleSupplier swept, Consumer<SessionReader> released) {
        this.swept = swept;
        this.released = released;
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
        double full = swept.getAsDouble();
        List<Unit> out = new ArrayList<Unit>();
        String bounded = "";
        synchronized (this) {
            Unit unit = new Unit(session, size);
            Unit was = held.put(session.sessionId(), unit);
            holding += size - (was == null ? 0L : was.size);
            if (full >= SHARE && full != answered) {
                answered = full;
                bytes = Math.min(bytes, holding / 2);
                bounded = "hold: the old generation " + Math.round(full * 100)
                        + " % full after a sweep: at most " + (bytes >> 20)
                        + " of the " + (holding >> 20) + " MB of reads' and"
                        + " writes' text held from now on";
            }
            for (Iterator<Unit> eldest = held.values().iterator();
                 holding > bytes && eldest.hasNext(); ) {
                Unit next = eldest.next();
                if (next == unit) continue;
                eldest.remove();
                holding -= next.size;
                out.add(next);
            }
        }
        if (!bounded.isEmpty()) System.err.println(bounded);
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
