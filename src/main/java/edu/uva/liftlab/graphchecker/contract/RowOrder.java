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

    /** Whether this read stands before this write. */
    public static boolean before(ReadRow read, WriteRow write) {
        return before(read.seq(), read.tie(), write.seq(), write.tie());
    }

    /** Whether this write stands before this read. */
    public static boolean before(WriteRow write, ReadRow read) {
        return before(write.seq(), write.tie(), read.seq(), read.tie());
    }
}
