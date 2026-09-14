package edu.uva.liftlab.graphchecker.runtime.d3;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
import edu.uva.liftlab.graphchecker.d3.contract.TargetRow;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Writes one replay session's rows, one file per kind, through the
 * contract's own codec.
 *
 * <p>The replay used to publish ONE row kind -- a {@code
 * CONCOLIC_REGION_RESULT} line with ten arrays inside it -- so every reader
 * re-parsed whole results to reach one member and no reader could join on a
 * kind it did not own (RUNTIME-INVENTORY §6.3).  Here each kind is its own
 * JSONL file under the session directory, written by {@code RowCodec}, so
 * the runtime and every reader spell one row shape.</p>
 *
 * <p>Every row is flushed as it is written.  A campaign halts the JVM
 * ({@code Runtime.halt}) as soon as the selected result settles, which runs
 * no shutdown hook: a buffered row is a lost row, and a lost row is
 * indistinguishable from a site that never ran.</p>
 */
public final class SessionPublisher {
    private static final Object LOCK = new Object();
    private static final Map<String, SessionPublisher> SESSIONS =
            new LinkedHashMap<String, SessionPublisher>();
    /** Results of the obligations this replay was handed. */
    public static final String OBLIGATION_RESULTS = "obligations.jsonl";
    /** Roots whose declared domain resolved to absolute bounds. */
    public static final String ROOT_DOMAINS = "root-domains.jsonl";

    private final SessionDir layout;
    private final Map<String, BufferedWriter> writers =
            new LinkedHashMap<String, BufferedWriter>();
    private final Map<String, JsonObject> expressions =
            new LinkedHashMap<String, JsonObject>();
    private boolean failed;

    private SessionPublisher(SessionDir layout) {
        this.layout = layout;
    }

    /** The publisher of one session, created once per JVM. */
    public static SessionPublisher of(Path iteration, String sessionId) {
        String key = iteration.toAbsolutePath() + "\n" + Text.safe(sessionId);
        synchronized (LOCK) {
            SessionPublisher publisher = SESSIONS.get(key);
            if (publisher == null) {
                publisher = new SessionPublisher(
                        SessionDir.of(iteration, sessionId));
                SESSIONS.put(key, publisher);
            }
            return publisher;
        }
    }

    public String sessionId() {
        return layout.sessionId();
    }

    public Path dir() {
        return layout.dir();
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
     * One root, and its domain when the declaration resolved one.
     *
     * <p>{@code root-domains.jsonl} carries the same row for the roots that
     * have absolute bounds, so a composer reading domains never parses the
     * mint log to find them.</p>
     */
    public void rootMint(RootMintRow row) {
        if (row == null) return;
        JsonObject json = RowCodec.writeRootMint(row);
        append(layout.roots(), json);
        if (!row.pinned()) {
            append(layout.dir().resolve(ROOT_DOMAINS), json);
        }
    }

    public void target(TargetRow row) {
        if (row != null) append(layout.targets(), RowCodec.writeTarget(row));
    }

    public void gap(GapRow row) {
        if (row != null) append(layout.gaps(), RowCodec.writeGap(row));
    }

    /** What one obligation's focused replay settled. */
    public void obligationResult(ObligationResult row) {
        if (row == null) return;
        JsonObject json = new JsonObject();
        json.addProperty("obligationId", row.obligationId());
        json.addProperty("verdict", row.verdict().name());
        json.addProperty("sessionId", row.sessionId());
        json.addProperty("detail", row.detail());
        append(layout.dir().resolve(OBLIGATION_RESULTS), json);
    }

    /** Files one expression under the ref the rows name it by. */
    public void expression(String ref, JsonObject expression) {
        String key = Text.safe(ref);
        if (key.isEmpty() || expression == null) return;
        synchronized (LOCK) {
            if (expressions.containsKey(key)) return;
            expressions.put(key, expression);
        }
        writeExpressions();
    }

    /** Whether this session already holds the expression named by a ref. */
    public boolean holdsExpression(String ref) {
        synchronized (LOCK) {
            return expressions.containsKey(Text.safe(ref));
        }
    }

    private void writeExpressions() {
        synchronized (LOCK) {
            if (failed) return;
            try {
                layout.create();
                RowCodec.writeExpressions(layout.expressions(),
                        ExpressionTable.of(expressions));
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
                writer.write(RowCodec.toLine(row));
                writer.newLine();
                writer.flush();
            } catch (IOException unwritable) {
                fail(unwritable);
            }
        }
    }

    private BufferedWriter writer(Path file) throws IOException {
        String key = file.toString();
        BufferedWriter writer = writers.get(key);
        if (writer != null) return writer;
        layout.create();
        BufferedWriter fresh = new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(file.toFile(), true),
                StandardCharsets.UTF_8));
        writers.put(key, fresh);
        return fresh;
    }

    /**
     * A session that cannot write says so once and stops.
     *
     * <p>Rule 5: a publisher that fails silently turns "the run did not
     * write this" into "the site did not run", which is the one confusion
     * no reader downstream is able to detect.</p>
     */
    private void fail(IOException unwritable) {
        failed = true;
        System.err.println("Causynth could not write session rows to "
                + layout.dir() + ": " + unwritable);
    }

    /** Closes every open file of this session. */
    public void close() {
        synchronized (LOCK) {
            if (!expressions.isEmpty()) writeExpressions();
            for (BufferedWriter writer : writers.values()) {
                try {
                    writer.flush();
                    writer.close();
                } catch (IOException ignored) {
                    // The rows are already flushed; closing adds nothing.
                }
            }
            writers.clear();
        }
    }

    /** Closes every session this JVM opened. */
    public static void closeAll() {
        synchronized (LOCK) {
            for (SessionPublisher publisher : SESSIONS.values()) {
                publisher.close();
            }
        }
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            closeAll();
            SESSIONS.clear();
        }
    }
}
