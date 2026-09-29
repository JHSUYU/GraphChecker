package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC 2: a root the session minted, with its domain already
 * resolved to absolute bounds (both null: pinned).  An undeclared root is
 * evidence, not a degree of freedom.  {@code seq} keeps a root minted after an
 * export from being read as carried by it.
 */
public final class RootMintRow extends Value {
    private final String sessionId;
    private final long seq;
    private final OccurrenceAddress occurrence;
    private final String rootId;
    private final String symbol;
    private final RootKind kind;
    private final String recordedValue;
    private final String domainMin;
    private final String domainMax;
    private final boolean declared;
    private final long clockNanos;

    private RootMintRow(String sessionId, long seq,
                        OccurrenceAddress occurrence, String rootId,
                        String symbol, RootKind kind, String recordedValue,
                        String domainMin, String domainMax, boolean declared,
                        long clockNanos) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.occurrence = occurrence;
        this.rootId = rootId;
        this.symbol = symbol;
        this.kind = kind;
        this.recordedValue = recordedValue;
        this.domainMin = domainMin;
        this.domainMax = domainMax;
        this.declared = declared;
        this.clockNanos = clockNanos;
    }

    public static RootMintRow of(String sessionId, long seq,
                                 OccurrenceAddress occurrence, String rootId,
                                 String symbol, RootKind kind,
                                 String recordedValue, String domainMin,
                                 String domainMax, boolean declared,
                                 long clockNanos) {
        RootKind stated = Fields.required(kind, "kind");
        if ((stated == RootKind.CLOCK) != (clockNanos > 0L)) {
            throw new IllegalArgumentException("clockNanos: a CLOCK root "
                    + "states its tick and no other root does: " + stated
                    + " " + clockNanos);
        }
        return new RootMintRow(Fields.text(sessionId, "sessionId"),
                Fields.nonNegative(seq, "seq"),
                Fields.required(occurrence, "occurrence"),
                Fields.text(rootId, "rootId"), Fields.text(symbol, "symbol"),
                stated,
                Fields.required(recordedValue, "recordedValue"),
                Fields.optional(domainMin), Fields.optional(domainMax),
                declared, clockNanos);
    }

    public String sessionId() {
        return sessionId;
    }

    public long seq() {
        return seq;
    }

    public OccurrenceAddress occurrence() {
        return occurrence;
    }

    public String rootId() {
        return rootId;
    }

    /** The solver name of this root: one name per root, everywhere. */
    public String symbol() {
        return symbol;
    }

    public RootKind kind() {
        return kind;
    }

    public String recordedValue() {
        return recordedValue;
    }

    /** The resolved absolute lower bound, or {@code null} when pinned. */
    public String domainMin() {
        return domainMin;
    }

    /** The resolved absolute upper bound, or {@code null} when pinned. */
    public String domainMax() {
        return domainMax;
    }

    /** Whether the case declared this root. */
    public boolean declared() {
        return declared;
    }

    /**
     * A CLOCK's tick: the nanoseconds one unit of its reading is (1 for
     * {@code nanoTime}, 1,000,000 for {@code currentTimeMillis}); 0 for any
     * other root.  A clock's window and margin are spans of time, stated in
     * its own ticks.
     */
    public long clockNanos() {
        return clockNanos;
    }

    /** Whether the root may move at all: an undeclared or undomained root. */
    public boolean pinned() {
        return domainMin == null && domainMax == null;
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, occurrence, rootId, symbol, kind,
                recordedValue, domainMin, domainMax, declared, clockNanos};
    }

    @Override
    public String toString() {
        return "RootMintRow{" + sessionId + "#" + seq + " " + rootId + " "
                + kind + " " + symbol + "=" + recordedValue + "}";
    }
}
