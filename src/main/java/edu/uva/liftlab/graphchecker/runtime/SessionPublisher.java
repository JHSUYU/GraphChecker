package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SharedExpressionTable;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionManifest;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * Writes one replay session's rows, one file per kind, through the
 * contract's codec.  Every row is flushed at once: the JVM is halted with no
 * shutdown hook, and a lost row reads as a site that never ran.
 */
public final class SessionPublisher {
    private static final Object LOCK = new Object();
    /** How often a live session's expression table is written again. */
    private static final long REWRITE_MS = 30_000L;
    private static final Map<String, SessionPublisher> SESSIONS =
            new LinkedHashMap<String, SessionPublisher>();

    private final SessionDir layout;
    private final Map<String, BufferedWriter> writers =
            new LinkedHashMap<String, BufferedWriter>();
    private final Map<String, JsonObject> expressions =
            new LinkedHashMap<String, JsonObject>();
    /** Hashes each expression node once, however often the table is
     *  written again. */
    private final SharedExpressionTable.Codec codec =
            new SharedExpressionTable.Codec();
    /** When the table was last written, to write it again by the clock. */
    private long tableWrittenAt;
    /**
     * Statements written under the key the contract makes them one row by:
     * a root per (occurrence, rootId), an unreached target per (occurrence,
     * anchor).  A LOOP_BODY_ROOT's bodies share one address, and a door read
     * again mints its one symbol again ({@code RootMint#configuredSource}),
     * so both restate a written row; a restatement that differs is written,
     * for IMPORT to name (invariants 4 and 8).
     */
    private final Set<String> stated = new HashSet<String>();
    private boolean failed;
    /** Once closed, every further expression is written as it is filed. */
    private boolean closed;

    private SessionPublisher(SessionDir layout) {
        this.layout = layout;
    }

    /** The publisher of one session, created once per JVM. */
    public static SessionPublisher of(Path iteration, String sessionId) {
        return at(SessionDir.of(iteration, sessionId));
    }

    /** The publisher of one session under an explicit sessions root. */
    static SessionPublisher at(SessionDir layout) {
        String key = layout.dir().toAbsolutePath().toString();
        synchronized (LOCK) {
            SessionPublisher publisher = SESSIONS.get(key);
            if (publisher == null) {
                publisher = new SessionPublisher(layout);
                publisher.open();
                SESSIONS.put(key, publisher);
            }
            return publisher;
        }
    }

    /**
     * Creates every file empty (an absent file means "not published", not
     * "none") and writes the manifest now, not at close, since a halted JVM
     * never closes.  The role is what {@link FocusedReplay} was handed.
     */
    private void open() {
        synchronized (LOCK) {
            try {
                layout.create();
                for (Path file : new Path[] {layout.activations(),
                        layout.decisions(), layout.exports(),
                        layout.attaches(), layout.writes(), layout.reads(),
                        layout.roots(), layout.targets(), layout.gaps(),
                        layout.schedule()}) {
                    if (!Files.exists(file)) Files.createFile(file);
                }
                RowCodec.writeManifest(layout.manifest(),
                        SessionManifest.of(layout.sessionId(),
                                FocusedReplay.focusedSession()
                                        ? SessionManifest.Role.FOCUSED
                                        : SessionManifest.Role.SEED,
                                FocusedReplay.obligationIds()));
            } catch (IOException unwritable) {
                fail(unwritable);
            }
        }
        writeExpressions();
    }

    public void activation(ActivationRow row) {
        if (row != null) append(layout.activations(),
                RowCodec.writeActivation(row));
    }

    public void decision(DecisionRow row) {
        if (row != null) append(layout.decisions(),
                RowCodec.writeDecision(row));
    }

    public void export(ExportRow row) {
        if (row != null) append(layout.exports(), RowCodec.writeExport(row));
    }

    public void attach(AttachRow row) {
        if (row != null) append(layout.attaches(), RowCodec.writeAttach(row));
    }

    public void write(WriteRow row) {
        if (row != null) append(layout.writes(), RowCodec.writeWrite(row));
    }

    public void read(ReadRow row) {
        if (row != null) append(layout.reads(), RowCodec.writeRead(row));
    }

    /**
     * One root mint row in {@code roots.jsonl}.  Domains come from the case's
     * {@code --root-domains}, not from here.
     */
    public void rootMint(RootMintRow row) {
        if (row != null && once(row.occurrence().id() + "|" + row.rootId()
                + "|" + row.symbol() + "|" + row.recordedValue())) {
            append(layout.roots(), RowCodec.writeRootMint(row));
        }
    }

    public void target(TargetRow row) {
        if (row != null && (row.reachedAnchor() || once(row.occurrence().id()
                + "|" + row.anchorSiteId()))) {
            append(layout.targets(), RowCodec.writeTarget(row));
        }
    }

    /** Whether this statement is written for the first time. */
    private boolean once(String key) {
        synchronized (LOCK) {
            return stated.add(key);
        }
    }

    public void gap(GapRow row) {
        if (row != null) append(layout.gaps(), RowCodec.writeGap(row));
    }

    /** One scheduling event, in the order the run made it. */
    public void schedule(JsonObject event) {
        if (event != null) append(layout.schedule(), event);
    }

    /** What one obligation's focused replay settled. */
    public void obligationResult(ObligationResult row) {
        if (row == null) return;
        append(layout.obligations(),
                RowCodec.writeObligationResult(row));
    }

    /** Files one expression under the ref the rows name it by. */
    public void expression(String ref, JsonObject expression) {
        String key = Text.safe(ref);
        if (key.isEmpty() || expression == null) return;
        synchronized (LOCK) {
            if (expressions.containsKey(key)) return;
            expressions.put(key, expression);
            // The table is one JSON object, written whole: again at most
            // every REWRITE_MS while the run lasts (a killed replay keeps a
            // usable table), at close, and at once for any expression after
            // close.  By count it was rewritten every 64th expression, which
            // is quadratic in a session of 350,000.
            long now = System.currentTimeMillis();
            if (!closed && now - tableWrittenAt < REWRITE_MS) return;
            tableWrittenAt = now;
        }
        writeExpressions();
    }

    private void writeExpressions() {
        synchronized (LOCK) {
            if (failed || withdrawn()) return;
            try {
                // Always written, even empty.
                RowCodec.writeExpressions(layout.expressions(),
                        ExpressionTable.of(expressions), codec);
            } catch (IOException unwritable) {
                fail(unwritable);
            }
        }
    }

    private void append(Path file, JsonObject row) {
        synchronized (LOCK) {
            if (failed) return;
            try {
                BufferedWriter writer = writer(file);
                if (writer == null) return;
                writer.write(RowCodec.toLine(row));
                writer.newLine();
                writer.flush();
            } catch (IOException unwritable) {
                fail(unwritable);
            }
        }
    }

    /** The open writer of one row file, or null once withdrawn. */
    private BufferedWriter writer(Path file) throws IOException {
        String key = file.toString();
        BufferedWriter writer = writers.get(key);
        if (writer != null) return writer;
        if (withdrawn()) return null;
        BufferedWriter fresh = new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(file.toFile(), true),
                StandardCharsets.UTF_8));
        writers.put(key, fresh);
        return fresh;
    }

    /**
     * Whether the campaign took this session's directory away after
     * {@link #open} made it -- a replay killed at its bound is withdrawn while
     * its JVM still shuts down.  Nothing recreates it: a late table rewrite
     * brought back a directory holding only expressions.json, and IMPORT
     * refused hdfs-11741 v85 over it.
     */
    private boolean withdrawn() {
        return !Files.isDirectory(layout.dir());
    }

    /**
     * A session that cannot write says so once and stops (rule 5: silence
     * would read as "the site did not run").
     */
    private void fail(IOException unwritable) {
        failed = true;
        System.err.println("Causynth could not write session rows to "
                + layout.dir() + ": " + unwritable);
    }

    /** Closes every open file of this session. */
    public void close() {
        synchronized (LOCK) {
            closed = true;
            writeExpressions();
            for (BufferedWriter writer : writers.values()) {
                try {
                    writer.flush();
                    writer.close();
                } catch (IOException ignored) {
                    // Rows are already flushed.
                }
            }
            writers.clear();
        }
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            for (SessionPublisher publisher : SESSIONS.values()) {
                publisher.close();
            }
            SESSIONS.clear();
        }
    }
}
