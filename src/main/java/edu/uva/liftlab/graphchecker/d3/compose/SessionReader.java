package edu.uva.liftlab.graphchecker.d3.compose;

import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
import edu.uva.liftlab.graphchecker.d3.contract.TargetRow;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

/**
 * One replay session's rows, each kind read from its own file.
 *
 * <p>A reader of one kind never parses another kind's file, which is what
 * lets a session be written incrementally and read by whoever needs only a
 * part of it.  Nothing here interprets a row: the session is a recording,
 * and what it means is decided in {@link Composer}.</p>
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
        this.activations = activations;
        this.decisions = decisions;
        this.exports = exports;
        this.attaches = attaches;
        this.writes = writes;
        this.reads = reads;
        this.roots = roots;
        this.targets = targets;
        this.gaps = gaps;
        this.expressions = expressions;
    }

    /** Every row of one session under {@code <iteration>/sessions/<id>}. */
    public static SessionReader read(Path iteration, String sessionId)
            throws IOException {
        return read(SessionDir.of(iteration, sessionId));
    }

    /** Every row of one session directory. */
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

    public String sessionId() {
        return directory.sessionId();
    }

    public Path directory() {
        return directory.dir();
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

    public List<GapRow> gaps() {
        return gaps;
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
        for (ActivationRow activation : activations) {
            if (activation.focused()) return true;
        }
        return false;
    }

    @Override
    public String toString() {
        return "session " + sessionId() + " (" + decisions.size()
                + " decisions, " + attaches.size() + " attaches)";
    }
}
