package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;

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
    private final List<ObligationResult> obligations;
    private final List<DoorRow> doors;
    private final ExpressionTable expressions;
    private final SessionManifest manifest;
    private final String incomplete;

    private SessionReader(SessionDir directory,
                          List<ActivationRow> activations,
                          List<DecisionRow> decisions,
                          List<ExportRow> exports, List<AttachRow> attaches,
                          List<WriteRow> writes, List<ReadRow> reads,
                          List<RootMintRow> roots, List<TargetRow> targets,
                          List<GapRow> gaps,
                          List<ObligationResult> obligations,
                          List<DoorRow> doors, ExpressionTable expressions,
                          SessionManifest manifest, String incomplete) {
        this.manifest = manifest;
        this.incomplete = incomplete;
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
        this.obligations = Collections.unmodifiableList(obligations);
        this.doors = Collections.unmodifiableList(doors);
        this.expressions = expressions;
    }

    /** Reads one session directory of an iteration. */
    public static SessionReader read(Path iteration, String sessionId)
            throws IOException {
        return read(SessionDir.of(iteration, sessionId));
    }

    /**
     * Reads one session directory, naming what it could not read.
     *
     * <p>A file the codec refuses -- a row the kill truncated, a manifest
     * that states no role -- is not an exception thrown at whatever stage
     * happened to open the corpus first.  It is recorded on the session, and
     * IMPORT names it {@code SESSION_INCOMPLETE} (BLOCKING) with the file
     * and the reason.  The kinds it COULD read are still here, because
     * naming which file is short is the whole point; nothing downstream may
     * read a short kind as "this session had none", which is why the
     * statement is BLOCKING and not a diagnostic.</p>
     */
    public static SessionReader read(SessionDir dir) throws IOException {
        Partial partial = new Partial();
        List<ActivationRow> activations = partial.rows(dir.activations(),
                RowCodec::readActivation);
        List<DecisionRow> decisions = partial.rows(dir.decisions(),
                RowCodec::readDecision);
        List<ExportRow> exports = partial.rows(dir.exports(),
                RowCodec::readExport);
        List<AttachRow> attaches = partial.rows(dir.attaches(),
                RowCodec::readAttach);
        List<WriteRow> writes = partial.rows(dir.writes(),
                RowCodec::readWrite);
        List<ReadRow> reads = partial.rows(dir.reads(), RowCodec::readRead);
        List<RootMintRow> roots = partial.rows(dir.roots(),
                RowCodec::readRootMint);
        List<TargetRow> targets = partial.rows(dir.targets(),
                RowCodec::readTarget);
        List<GapRow> gaps = partial.rows(dir.gaps(), RowCodec::readGap);
        List<ObligationResult> obligations = partial.rows(dir.obligations(),
                RowCodec::readObligationResult);
        List<DoorRow> doors = partial.rows(dir.doors(), RowCodec::readDoor);
        ExpressionTable expressions;
        try {
            expressions = RowCodec.readExpressions(dir.expressions());
        } catch (RuntimeException unreadable) {
            partial.note(dir.expressions(), unreadable);
            expressions = ExpressionTable.empty();
        }
        SessionManifest manifest;
        try {
            manifest = RowCodec.readManifest(dir.manifest());
        } catch (RuntimeException unstated) {
            partial.note(dir.manifest(), unstated);
            manifest = null;
        }
        return new SessionReader(dir, activations, decisions, exports,
                attaches, writes, reads, roots, targets, gaps, obligations,
                doors, expressions, manifest, partial.reason);
    }

    /** One session's read, and the first file of it that would not read. */
    private static final class Partial {
        private String reason = "";

        private <T> List<T> rows(Path file, Function<JsonObject, T> reader)
                throws IOException {
            try {
                return RowCodec.readAll(file, reader);
            } catch (RuntimeException unreadable) {
                note(file, unreadable);
                return new ArrayList<T>();
            }
        }

        private void note(Path file, RuntimeException unreadable) {
            if (!reason.isEmpty()) return;
            Path name = file.getFileName();
            reason = (name == null ? file.toString() : name.toString())
                    + " could not be read: " + unreadable.getMessage();
        }
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

    /**
     * WHAT THIS REPLAY SETTLED, one row per obligation it ran.
     *
     * <p>The verdict, and the only statement of it a reader of the corpus
     * may take: the replay owns whether the focused prefix reproduced and
     * the flipped decision was taken.  A SEED session states none -- it was
     * asked nothing -- and none is not a verdict.</p>
     */
    public List<ObligationResult> obligations() {
        return obligations;
    }

    /** Which occurrence each message of this run left and entered by. */
    public List<DoorRow> doors() {
        return doors;
    }

    /**
     * ONLY AN ADMITTED REPLAY STATES A TOPOLOGY, AND THIS IS THAT RULE.
     *
     * <p>Whether this session RAN the world it was asked for, read off its
     * own result rows and nothing else -- never the wave's aggregate file,
     * which is the planner's copy and not the run's statement.  The rule:
     * a session states the world it ran only when every obligation it ran
     * came back {@link Verdict#ADMITTED}; one that states no result row at
     * all states nothing, because an absence is not a verdict.  A SEED is
     * asked nothing and is always an authority: it IS the recording.</p>
     *
     * <p>What it costs to skip it: hdfs-11741 campaign #2's NOT_ADMITTED
     * session -- its mint planted nothing, so it never ran the clock skew
     * the wave asked of it -- paired eight consumers with producers the
     * skeleton does not carry.  Read as a topology, that emptied wave 1 of
     * every candidate and filed eight BLOCKING rows, and one replay that
     * did not run the world it was asked halted the campaign.</p>
     */
    public boolean admitted() {
        if (seed()) return true;
        if (obligations.isEmpty()) return false;
        for (ObligationResult result : obligations) {
            if (result.verdict() != Verdict.ADMITTED) return false;
        }
        return true;
    }

    public ExpressionTable expressions() {
        return expressions;
    }

    /**
     * The role this session STATES, or null when it states none.
     *
     * <p>Read, never inferred.  "The seed is the session whose activations
     * focused nothing" was the rule, and it has no answer for a corpus whose
     * focused replays were cut before their occurrence activated: on 11741
     * campaign #2 nine of eighty-one sessions focused nothing and COMPOSE
     * refused the lot.</p>
     */
    public SessionManifest manifest() {
        return manifest;
    }

    /** Whether this session states it is the recording. */
    public boolean seed() {
        return manifest != null && manifest.seed();
    }

    /** Why this session could not be read whole, or {@code ""}. */
    public String incomplete() {
        return incomplete;
    }

    /**
     * The session that states it is the recording, or null when that has no
     * single answer.
     *
     * <p>Exactly one SEED: with none, no declaration has a recording it was
     * written about, and with two, nothing says which.  Both are refusals
     * the caller names -- naming a counterfactual as the recording is how a
     * claim comes to be about the wrong execution.</p>
     */
    public static String seedSessionId(List<SessionReader> sessions) {
        List<String> stated = seedSessionIds(sessions);
        return stated.size() == 1 ? stated.get(0) : null;
    }

    /** Every session that states SEED: what such a refusal names. */
    public static List<String> seedSessionIds(List<SessionReader> sessions) {
        List<String> stated = new ArrayList<String>();
        if (sessions == null) return stated;
        for (SessionReader session : sessions) {
            if (session.seed()) stated.add(session.sessionId());
        }
        return stated;
    }

    @Override
    public String toString() {
        return "session " + sessionId() + " (" + decisions.size()
                + " decisions, " + attaches.size() + " attaches)";
    }
}
