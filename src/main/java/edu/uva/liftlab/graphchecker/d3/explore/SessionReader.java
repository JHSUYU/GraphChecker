package edu.uva.liftlab.graphchecker.d3.explore;

import edu.uva.liftlab.graphchecker.d3.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
import edu.uva.liftlab.graphchecker.d3.contract.TargetRow;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Reads one replay session's rows, one file per kind.
 *
 * <p>Every reader of the corpus goes through this class, so the contract's
 * file layout is read in one place and not once per module.  A session is
 * read whole because exploration joins across its kinds -- a decision names a
 * symbol a mint row declared and an attach minted -- and because a raw
 * symbol, a version id and an expression ref are all session-local names.</p>
 */
public final class SessionReader {
    private SessionReader() {
    }

    /** One session's rows, with its expressions and their lowering. */
    public static final class Session {
        public final String sessionId;
        public final List<ActivationRow> activations;
        public final List<DecisionRow> decisions;
        public final List<ExportRow> exports;
        public final List<AttachRow> attaches;
        public final List<WriteRow> writes;
        public final List<ReadRow> reads;
        public final List<RootMintRow> roots;
        public final List<TargetRow> targets;
        public final ExpressionTable expressions;
        private final SmtLowering lowering;

        Session(String sessionId, List<ActivationRow> activations,
                List<DecisionRow> decisions, List<ExportRow> exports,
                List<AttachRow> attaches, List<WriteRow> writes,
                List<ReadRow> reads, List<RootMintRow> roots,
                List<TargetRow> targets, ExpressionTable expressions) {
            this.sessionId = sessionId;
            this.activations = Collections.unmodifiableList(activations);
            this.decisions = Collections.unmodifiableList(decisions);
            this.exports = Collections.unmodifiableList(exports);
            this.attaches = Collections.unmodifiableList(attaches);
            this.writes = Collections.unmodifiableList(writes);
            this.reads = Collections.unmodifiableList(reads);
            this.roots = Collections.unmodifiableList(roots);
            this.targets = Collections.unmodifiableList(targets);
            this.expressions = expressions;
            this.lowering = SmtLowering.of(expressions);
        }

        /** This session's expressions, lowered by the one shared lowering. */
        public SmtLowering lowering() {
            return lowering;
        }
    }

    /** Reads one session directory of an iteration. */
    public static Session read(Path iteration, String sessionId)
            throws IOException {
        return read(SessionDir.of(iteration, sessionId));
    }

    /** Reads one session directory. */
    public static Session read(SessionDir dir) throws IOException {
        return new Session(dir.sessionId(),
                RowCodec.readAll(dir.activations(), RowCodec::readActivation),
                RowCodec.readAll(dir.decisions(), RowCodec::readDecision),
                RowCodec.readAll(dir.exports(), RowCodec::readExport),
                RowCodec.readAll(dir.attaches(), RowCodec::readAttach),
                RowCodec.readAll(dir.writes(), RowCodec::readWrite),
                RowCodec.readAll(dir.reads(), RowCodec::readRead),
                RowCodec.readAll(dir.roots(), RowCodec::readRootMint),
                RowCodec.readAll(dir.targets(), RowCodec::readTarget),
                RowCodec.readExpressions(dir.expressions()));
    }

    /** Every session of one iteration, in the layout's own order. */
    public static List<Session> readAll(Path iteration) throws IOException {
        List<Session> sessions = new ArrayList<Session>();
        for (SessionDir dir : SessionDir.sessionsIn(iteration)) {
            sessions.add(read(dir));
        }
        return sessions;
    }
}
