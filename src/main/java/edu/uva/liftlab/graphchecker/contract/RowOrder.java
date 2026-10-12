package edu.uva.liftlab.graphchecker.contract;

/**
 * THE ORDER OF A SESSION'S ROWS (CONTRACT-SPEC §2.2).  A row's {@code seq}
 * is the VM's one event clock.  A row the engine states itself -- a store's
 * or a node's view's write or read, which no VM event of its own carries --
 * stands after every VM event so far ({@code seq} = the last event + 1) and
 * takes a {@code tie} >= 1, one JVM-wide count per seq in the order the
 * engine stated them ({@code runtime.Identity#enginePosition}); a VM row's
 * tie is 0, and a row read without one reads 0.  So an engine row at seq S
 * stands after VM event S - 1, before VM event S, and after every engine row
 * of S stated before it: several stated with no VM event between them (a
 * decode, then the guard that reads its objects) are ordered, not tied.
 * Seq 0 -- no VM clock, an INITIAL -- orders nothing.
 */
public final class RowOrder {
    private RowOrder() {
    }

    /** Where one engine-stated row stands: its seq and its tie. */
    public static final class Position {
        public final long seq;
        public final int tie;

        public Position(long seq, int tie) {
            this.seq = seq;
            this.tie = tie;
        }
    }

    /** Whether the row at ({@code seq}, {@code tie}) stands before the row
     *  at ({@code otherSeq}, {@code otherTie}). */
    public static boolean before(long seq, int tie, long otherSeq,
                                 int otherTie) {
        if (seq <= 0L || otherSeq <= 0L) return false;
        if (seq != otherSeq) return seq < otherSeq;
        return tie > 0 && (otherTie == 0 || tie < otherTie);
    }

    /**
     * Whether the row at ({@code seq}, {@code tie}) stands before VM event
     * {@code event} (a decision's, a cutoff's): an earlier seq, or an
     * engine row stated at seq {@code event}, after event - 1.  A row with
     * no clock (seq 0) stands before every event, as {@code seq < event}
     * reads it.
     */
    public static boolean beforeEvent(long seq, int tie, long event) {
        return beforeCut(seq, tie, event, 0);
    }

    /**
     * Whether the row at ({@code seq}, {@code tie}) stands before a cut at
     * ({@code cutSeq}, {@code cutTie}): a VM event's ({@code cutTie} 0,
     * {@link #beforeEvent}) or an engine row's -- a writer reached through
     * its engine-stated store write is cut there, so its reads stated after
     * that write at the same seq are past it.  A row with no clock (seq 0)
     * stands before every cut, as {@code seq < cut} reads it.
     */
    public static boolean beforeCut(long seq, int tie, long cutSeq,
                                    int cutTie) {
        return seq < cutSeq || seq == cutSeq && tie > 0
                && (cutTie == 0 || tie < cutTie);
    }

    /**
     * The one order as a comparison, for picking the last of several rows
     * or sorting them: seq, then at one seq the engine's rows by tie, then
     * its VM event (tie 0).  Seq 0 -- no clock, an INITIAL -- sorts first,
     * as a comparison of seqs alone sorts it.
     */
    public static int compare(long seq, int tie, long otherSeq,
                              int otherTie) {
        if (seq != otherSeq) return Long.compare(seq, otherSeq);
        return Integer.compare(tie == 0 ? Integer.MAX_VALUE : tie,
                otherTie == 0 ? Integer.MAX_VALUE : otherTie);
    }

    /** {@link #compare} of two writes. */
    public static int compare(WriteRow write, WriteRow other) {
        return compare(write.seq(), write.tie(), other.seq(), other.tie());
    }

    /** Whether this read stands before this write. */
    public static boolean before(ReadRow read, WriteRow write) {
        return before(read.seq(), read.tie(), write.seq(), write.tie());
    }

    /** Whether this write stands before this read. */
    public static boolean before(WriteRow write, ReadRow read) {
        return before(write.seq(), write.tie(), read.seq(), read.tie());
    }
}
