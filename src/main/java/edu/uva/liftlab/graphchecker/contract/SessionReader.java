package edu.uva.liftlab.graphchecker.contract;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * One replay session's rows, one file per kind, read once.
 *
 * <p>Every reader of the corpus goes through this class, so the contract's
 * file layout is read in one place and not once per module.  A session is
 * read whole because both stages join across its kinds -- a decision names a
 * symbol a mint row declared and an attach minted -- and because a raw
 * symbol, a version id and an expression ref are all session-local names.</p>
 *
 * <p>Nothing here interprets a row, and nothing here lowers one: the session
 * is a recording, what it means is decided by the stage that reads it, and a
 * lowering cache belongs to the stage that lowers.</p>
 */
public final class SessionReader {
    private final SessionDir directory;
    private final List<ActivationRow> activations;
    private final List<DecisionRow> decisions;
    private final List<ExportRow> exports;
    private final List<AttachRow> attaches;
    private final List<WriteRow> writes;
    private final List<ReadRow> reads;
    private final List<RootMintRow> roots;
    private final List<TargetRow> targets;
    private final List<GapRow> gaps;
    private final ExpressionTable expressions;

    private SessionReader(SessionDir directory,
                          List<ActivationRow> activations,
                          List<DecisionRow> decisions,
                          List<ExportRow> exports, List<AttachRow> attaches,
                          List<WriteRow> writes, List<ReadRow> reads,
                          List<RootMintRow> roots, List<TargetRow> targets,
                          List<GapRow> gaps, ExpressionTable expressions) {
        this.directory = directory;
        this.activations = Collections.unmodifiableList(activations);
        this.decisions = Collections.unmodifiableList(decisions);
        this.exports = Collections.unmodifiableList(exports);
        this.attaches = Collections.unmodifiableList(attaches);
        this.writes = Collections.unmodifiableList(writes);
        this.reads = Collections.unmodifiableList(reads);
        this.roots = Collections.unmodifiableList(roots);
        this.targets = Collections.unmodifiableList(targets);
        this.gaps = Collections.unmodifiableList(gaps);
        this.expressions = expressions;
    }

    /** Reads one session directory of an iteration. */
    public static SessionReader read(Path iteration, String sessionId)
            throws IOException {
        return read(SessionDir.of(iteration, sessionId));
    }

    /** Reads one session directory. */
    public static SessionReader read(SessionDir dir) throws IOException {
        return new SessionReader(dir,
                RowCodec.readAll(dir.activations(), RowCodec::readActivation),
                RowCodec.readAll(dir.decisions(), RowCodec::readDecision),
                RowCodec.readAll(dir.exports(), RowCodec::readExport),
                RowCodec.readAll(dir.attaches(), RowCodec::readAttach),
                RowCodec.readAll(dir.writes(), RowCodec::readWrite),
                RowCodec.readAll(dir.reads(), RowCodec::readRead),
                RowCodec.readAll(dir.roots(), RowCodec::readRootMint),
                RowCodec.readAll(dir.targets(), RowCodec::readTarget),
                RowCodec.readAll(dir.gaps(), RowCodec::readGap),
                RowCodec.readExpressions(dir.expressions()));
    }

    /** Every session of one iteration, in the layout's own order. */
    public static List<SessionReader> readAll(Path iteration)
            throws IOException {
        List<SessionReader> sessions = new ArrayList<SessionReader>();
        for (SessionDir dir : SessionDir.sessionsIn(iteration)) {
            sessions.add(read(dir));
        }
        return sessions;
    }

    public String sessionId() {
        return directory.sessionId();
    }

    public List<ActivationRow> activations() {
        return activations;
    }

    public List<DecisionRow> decisions() {
        return decisions;
    }

    public List<ExportRow> exports() {
        return exports;
    }

    public List<AttachRow> attaches() {
        return attaches;
    }

    public List<WriteRow> writes() {
        return writes;
    }

    public List<ReadRow> reads() {
        return reads;
    }

    public List<RootMintRow> roots() {
        return roots;
    }

    public List<TargetRow> targets() {
        return targets;
    }

    public ExpressionTable expressions() {
        return expressions;
    }

    /**
     * Whether this session explored a focused occurrence.
     *
     * <p>The seed replay runs everything concretely and focuses nothing; an
     * exploration replay focuses exactly the occurrence its task names.  So
     * "was this the recording, or a counterfactual" is a fact of the rows
     * and needs no naming convention on the session id.</p>
     */
    public boolean explored() {
        return focused() != null;
    }

    /** The occurrence this session's task focused, or null. */
    public OccurrenceAddress focused() {
        for (ActivationRow activation : activations) {
            if (activation.focused()) return activation.occurrence();
        }
        return null;
    }

    /** The same rule, over sessions a caller already read. */
    public static String seedSessionId(List<SessionReader> sessions) {
        List<String> unfocused = unfocusedSessionIds(sessions);
        return unfocused.size() == 1 ? unfocused.get(0) : null;
    }

    /** Every session that focused nothing: what the gap names. */
    public static List<String> unfocusedSessionIds(
            List<SessionReader> sessions) {
        List<String> unfocused = new ArrayList<String>();
        if (sessions == null) return unfocused;
        for (SessionReader session : sessions) {
            if (!session.explored()) unfocused.add(session.sessionId());
        }
        return unfocused;
    }

    @Override
    public String toString() {
        return "session " + sessionId() + " (" + decisions.size()
                + " decisions, " + attaches.size() + " attaches)";
    }
}
