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
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

public final class SessionPublisher {
    private static final Object LOCK = new Object();
    private static final Map<String, SessionPublisher> SESSIONS =
            new LinkedHashMap<String, SessionPublisher>();

    private final SessionDir layout;
    private final Map<String, BufferedWriter> writers =
            new LinkedHashMap<String, BufferedWriter>();
    private final Set<String> expressionRefs = new HashSet<String>();
    private final SessionExpressionLog.Writer expressionLog =
            new SessionExpressionLog.Writer();
    private final Set<String> stated = new HashSet<String>();
    private boolean failed;
    private SessionManifest manifest;
    private boolean closed;

    private SessionPublisher(SessionDir layout) {
        this.layout = layout;
    }

    public static SessionPublisher of(Path iteration, String sessionId) {
        return at(SessionDir.of(iteration, sessionId));
    }

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
                        FocusedReplay.forcing() ? SessionManifest.Role.FORCED
                                : FocusedReplay.focusedSession()
                                ? SessionManifest.Role.FOCUSED
                                : SessionManifest.Role.SEED,
                        FocusedReplay.obligationIds());
                writeManifest();
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

    private boolean once(String key) {
        synchronized (LOCK) {
            return stated.add(key);
        }
    }

    public void gap(GapRow row) {
        if (row != null) append(layout.gaps(), RowCodec.writeGap(row));
    }

    public void atClose(Map<String, Integer> entries,
                        Map<String, Map<String, String>> readings,
                        Set<String> derived, Map<String, String> spelled,
                        Set<String> doorsOnly, Set<String> serving) {
        synchronized (LOCK) {
            if (failed || closed || manifest == null || withdrawn()) return;
            try {
                manifest = manifest.atClose(entries, readings, derived,
                        spelled, doorsOnly, serving);
                writeManifest();
            } catch (IOException unwritable) {
                fail(unwritable);
            }
        }
    }

    public void schedule(JsonObject event) {
        if (event != null) append(layout.schedule(), event);
    }

    public void obligationResult(ObligationResult row) {
        if (row == null) return;
        append(layout.obligations(),
                RowCodec.writeObligationResult(row));
    }

    public void expression(String ref, JsonObject expression) {
        String key = trimmed(ref);
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
        ConcolicVmBroker.asEngineWork(() -> {
            List<String> lines = new ArrayList<String>(rows.size());
            for (JsonObject row : rows) lines.add(RowCodec.toLine(row));
            synchronized (LOCK) {
                if (failed || closed) return;
                try {
                    BufferedWriter writer = writer(file);
                    if (writer == null) return;
                    for (String line : lines) {
                        writer.write(line);
                        writer.newLine();
                    }
                    writer.flush();
                } catch (IOException unwritable) {
                    fail(unwritable);
                }
            }
        });
    }

    private void writeManifest() throws IOException {
        IOException[] failed = new IOException[1];
        ConcolicVmBroker.asEngineWork(() -> {
            try {
                RowCodec.writeManifest(layout.manifest(), manifest);
            } catch (IOException unwritable) {
                failed[0] = unwritable;
            }
        });
        if (failed[0] != null) throw failed[0];
    }

    private BufferedWriter writer(Path file) throws IOException {
        String key = file.toString();
        BufferedWriter writer = writers.get(key);
        if (writer != null) return writer;
        if (withdrawn()) return null;
        BufferedWriter fresh = new BufferedWriter(new OutputStreamWriter(
                ArtifactIO.appending(file), StandardCharsets.UTF_8));
        writers.put(key, fresh);
        return fresh;
    }

    private boolean withdrawn() {
        return !Files.isDirectory(layout.dir());
    }

    private void fail(IOException unwritable) {
        failed = true;
        EngineConsole.println("Causynth could not write session rows to "
                + layout.dir() + ": " + unwritable);
    }

    public void close() {
        synchronized (LOCK) {
            closed = true;
            ConcolicVmBroker.asEngineWork(() -> {
                for (BufferedWriter writer : writers.values()) {
                    try {
                        writer.flush();
                        writer.close();
                    } catch (IOException ignored) {
                    }
                }
            });
            writers.clear();
        }
    }

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
}
