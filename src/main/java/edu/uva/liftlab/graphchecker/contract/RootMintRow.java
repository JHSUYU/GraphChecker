package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §2.2: a root the session minted, with its domain already
 * resolved to absolute bounds (both null: pinned).  An undeclared root is
 * evidence, not a degree of freedom.  {@code seq} keeps a root minted after an
 * export from being read as carried by it.
 */
public final class RootMintRow extends Value {
    /** The member a CLOCK row states its skew in; absent when 0. */
    public static final String CLOCK_SKEW = "clockSkew";
    /** The member a CLOCK row states its JVM clock in; absent when none. */
    public static final String CLOCK_SOURCE = "clockSource";

    private final String sessionId;
    private final long seq;
    private final OccurrenceAddress occurrence;
    private final String rootId;
    private final String symbol;
    private final RootKind kind;
    private final RootCategory category;
    private final String recordedValue;
    private final String domainMin;
    private final String domainMax;
    private final boolean declared;
    private final Clock clock;
    private final long clockSkew;

    private RootMintRow(String sessionId, long seq,
                        OccurrenceAddress occurrence, String rootId,
                        String symbol, RootKind kind, RootCategory category,
                        String recordedValue, String domainMin,
                        String domainMax, boolean declared, Clock clock,
                        long clockSkew) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.occurrence = occurrence;
        this.rootId = rootId;
        this.symbol = symbol;
        this.kind = kind;
        this.category = category;
        this.recordedValue = recordedValue;
        this.domainMin = domainMin;
        this.domainMax = domainMax;
        this.declared = declared;
        this.clock = clock;
        this.clockSkew = clockSkew;
    }

    /**
     * @param category  where the root's value enters the world; the CLOCK
     *                  category is exactly the CLOCK kind
     * @param clock     a CLOCK's clock, null for any other root
     * @param clockSkew how far a CLOCK's node clock ran off the host's
     *                  reading here ({@link #clockSkew}); 0 for any other
     */
    public static RootMintRow of(String sessionId, long seq,
                                 OccurrenceAddress occurrence, String rootId,
                                 String symbol, RootKind kind,
                                 RootCategory category,
                                 String recordedValue, String domainMin,
                                 String domainMax, boolean declared,
                                 Clock clock, long clockSkew) {
        RootKind stated = Fields.required(kind, "kind");
        if ((stated == RootKind.CLOCK) != (clock != null)) {
            throw new IllegalArgumentException("clock: a CLOCK root states "
                    + "its clock and no other root does: " + stated + " "
                    + clock);
        }
        RootCategory from = Fields.required(category, "category");
        if ((stated == RootKind.CLOCK) != (from == RootCategory.CLOCK)) {
            throw new IllegalArgumentException("category: a CLOCK root is "
                    + "of the CLOCK category and no other root is: " + stated
                    + " " + from);
        }
        if (clockSkew != 0L && (stated != RootKind.CLOCK
                || !Fields.required(recordedValue, "recordedValue").trim()
                .matches("-?[0-9]+"))) {
            throw new IllegalArgumentException("clockSkew: only a CLOCK "
                    + "root that states an instant runs off the host's "
                    + "reading: " + stated + " " + recordedValue + " "
                    + clockSkew);
        }
        return new RootMintRow(Fields.text(sessionId, "sessionId"),
                Fields.nonNegative(seq, "seq"),
                Fields.required(occurrence, "occurrence"),
                Fields.text(rootId, "rootId"), Fields.text(symbol, "symbol"),
                stated, from,
                Fields.required(recordedValue, "recordedValue"),
                Fields.optional(domainMin), Fields.optional(domainMax),
                declared, clock, clockSkew);
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

    /** Where the root's value enters the world: a decision reaching a FAULT
     *  marker is a fault flip site, one reaching a CONFIG flag is not. */
    public RootCategory category() {
        return category;
    }

    /**
     * The value the region ran the root at; for a CLOCK the instant its
     * node's clock read there, which is {@link #hostReading} moved by
     * {@link #clockSkew}.
     */
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

    /** A CLOCK's clock: the JVM clock it wraps and its tick; null for
     *  any other root. */
    public Clock clock() {
        return clock;
    }

    /**
     * A CLOCK's tick: the nanoseconds one unit of its reading is (1 for
     * {@code nanoTime}, 1,000,000 for {@code currentTimeMillis}); 0 for any
     * other root.  A clock's window and margin are spans of time, stated in
     * its own ticks.
     */
    public long clockNanos() {
        return clock == null ? 0L : clock.nanos();
    }

    /**
     * How far a CLOCK's node clock ran off the host's reading at this cell
     * (a replay's plant, or the jump before it the clock ran on from,
     * {@code runtime.NodeClocks}); 0 for the host's own instant and for any
     * other root.
     */
    public long clockSkew() {
        return clockSkew;
    }

    /**
     * What the host's clock read at this cell: {@link #recordedValue} less
     * {@link #clockSkew}.  A clock's counterfactual is a skew off it (the
     * focus row's {@code clockDeltas}); the seed plants nothing, so there
     * it is the recorded value.
     */
    public String hostReading() {
        if (clockSkew == 0L) return recordedValue;
        return new java.math.BigInteger(recordedValue.trim())
                .subtract(java.math.BigInteger.valueOf(clockSkew)).toString();
    }

    /** Whether the root may move at all: an undeclared or undomained root. */
    public boolean pinned() {
        return domainMin == null && domainMax == null;
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, occurrence, rootId, symbol, kind,
                category, recordedValue, domainMin, domainMax, declared,
                clock, clockSkew};
    }

    @Override
    public String toString() {
        return "RootMintRow{" + sessionId + "#" + seq + " " + rootId + " "
                + kind + "/" + category + " " + symbol + "=" + recordedValue
                + "}";
    }
}
