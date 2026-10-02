package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionExpressionLog;
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
import java.nio.file.StandardCopyOption;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Writes one replay session's rows, one file per kind, through the
 * contract's codec.  Every row is flushed at once: the JVM is halted with no
 * shutdown hook, and a lost row reads as a site that never ran.
 */
public final class SessionPublisher {
    private static final Object LOCK = new Object();
    private static final Map<String, SessionPublisher> SESSIONS =
            new LinkedHashMap<String, SessionPublisher>();

    private final SessionDir layout;
    private final Map<String, BufferedWriter> writers =
            new LinkedHashMap<String, BufferedWriter>();
    /** The refs filed, each once. */
    private final Set<String> expressionRefs = new HashSet<String>();
    /** Numbers the nodes the expression log holds. */
    private final SessionExpressionLog.Writer expressionLog =
            new SessionExpressionLog.Writer();
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
    /** The manifest {@link #open} wrote. */
    private SessionManifest manifest;
    /** Closed: the run ended ({@link #close}), so nothing is written. */
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
                if (!Files.exists(layout.expressions())) {
                    append(layout.expressions(),
                            SessionExpressionLog.header());
                }
                manifest = SessionManifest.of(layout.sessionId(),
                        FocusedReplay.focusedSession()
                                ? SessionManifest.Role.FOCUSED
                                : SessionManifest.Role.SEED,
                        FocusedReplay.obligationIds());
                RowCodec.writeManifest(layout.manifest(), manifest);
            } catch (IOException unwritable) {
                fail(unwritable);
            }
        }
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

    /**
     * Restates the manifest at the run's end with what no row can state
     * ({@link SessionManifest}): the region entries unnamed work made, the
     * declared roots read where none was minted, and those found derived.
     */
    public void atClose(Map<String, Integer> entries,
                        Map<String, Map<String, String>> readings,
                        Set<String> derived) {
        synchronized (LOCK) {
            if (failed || closed || manifest == null || withdrawn()) return;
            try {
                manifest = manifest.atClose(entries, readings, derived);
                RowCodec.writeManifest(layout.manifest(), manifest);
            } catch (IOException unwritable) {
                fail(unwritable);
            }
        }
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

    /** Files one expression under the ref the rows name it by: the nodes
     *  the log does not hold yet, then the ref. */
    public void expression(String ref, JsonObject expression) {
        String key = Text.safe(ref);
        if (key.isEmpty() || expression == null) return;
        synchronized (LOCK) {
            if (failed || !expressionRefs.add(key)) return;
            append(layout.expressions(), expressionLog.lines(key, expression));
        }
    }

    private void append(Path file, JsonObject row) {
        append(file, Collections.singletonList(row));
    }

    private void append(Path file, List<JsonObject> rows) {
        synchronized (LOCK) {
            if (failed || closed) return;
            try {
                BufferedWriter writer = writer(file);
                if (writer == null) return;
                for (JsonObject row : rows) {
                    writer.write(RowCodec.toLine(row));
                    writer.newLine();
                }
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
     * A session that cannot write says so once and stops (silence
     * would read as "the site did not run").
     */
    private void fail(IOException unwritable) {
        failed = true;
        EngineConsole.println("Causynth could not write session rows to "
                + layout.dir() + ": " + unwritable);
    }

    /**
     * Closes every open file of this session, for good: the run has ended
     * ({@code JUnitMethodRunner#exit}), and a row a cluster thread files
     * after its verdict is about no run (hdfs-17899-bug1 r1: attaches after
     * the close, into a VM session opened anew, filed 55 BLOCKING refusals
     * of handles the old session had made).
     */
    public void close() {
        synchronized (LOCK) {
            closed = true;
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

    /**
     * Closes this session and moves its directory out of the corpus, to
     * {@code <quarantine>/<sessionId>}, in one rename: a replay a refusal
     * decided publishes no session ({@code FocusedReplay#refusedAt}), and
     * it knows so before any stage can read one.
     *
     * @return {@code ""} once moved, else why it was not
     */
    String withdrawTo(Path quarantine) {
        synchronized (LOCK) {
            close();
            try {
                Files.createDirectories(quarantine);
                Files.move(layout.dir(),
                        quarantine.resolve(layout.sessionId()),
                        StandardCopyOption.ATOMIC_MOVE);
                return "";
            } catch (IOException | RuntimeException unmoved) {
                return unmoved.toString();
            }
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
