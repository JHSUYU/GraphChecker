package edu.uva.liftlab.graphchecker.contract;

public final class RowOrder {
    private RowOrder() {
    }

    public static final class Position {
        public final long seq;
        public final int tie;

        public Position(long seq, int tie) {
            this.seq = seq;
            this.tie = tie;
        }
    }

    public static boolean before(long seq, int tie, long otherSeq,
                                 int otherTie) {
        if (seq <= 0L || otherSeq <= 0L) return false;
        if (seq != otherSeq) return seq < otherSeq;
        return tie > 0 && (otherTie == 0 || tie < otherTie);
    }

    public static boolean beforeEvent(long seq, int tie, long event) {
        return beforeCut(seq, tie, event, 0);
    }

    public static boolean beforeCut(long seq, int tie, long cutSeq,
                                    int cutTie) {
        return seq < cutSeq || seq == cutSeq && tie > 0
                && (cutTie == 0 || tie < cutTie);
    }

    public static int compare(long seq, int tie, long otherSeq,
                              int otherTie) {
        if (seq != otherSeq) return Long.compare(seq, otherSeq);
        return Integer.compare(tie == 0 ? Integer.MAX_VALUE : tie,
                otherTie == 0 ? Integer.MAX_VALUE : otherTie);
    }

    public static int compare(WriteRow write, WriteRow other) {
        return compare(write.seq(), write.tie(), other.seq(), other.tie());
    }

    public static boolean before(ReadRow read, WriteRow write) {
        return before(read.seq(), read.tie(), write.seq(), write.tie());
    }

    public static boolean before(WriteRow write, ReadRow read) {
        return before(write.seq(), write.tie(), read.seq(), read.tie());
    }
}
