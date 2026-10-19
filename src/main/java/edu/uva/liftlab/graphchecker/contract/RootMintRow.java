package edu.uva.liftlab.graphchecker.contract;

public final class RootMintRow extends Value {
    public static final String CLOCK_SKEW = "clockSkew";
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
    private final Validity valid;

    private RootMintRow(String sessionId, long seq,
                        OccurrenceAddress occurrence, String rootId,
                        String symbol, RootKind kind, RootCategory category,
                        String recordedValue, String domainMin,
                        String domainMax, boolean declared, Clock clock,
                        long clockSkew, Validity valid) {
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
        this.valid = valid;
    }

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
                declared, clock, clockSkew, Validity.ANY);
    }

    public RootMintRow validated(Validity admitted) {
        return new RootMintRow(sessionId, seq, occurrence, rootId, symbol,
                kind, category, recordedValue, domainMin, domainMax,
                declared, clock, clockSkew,
                admitted == null ? Validity.ANY : admitted);
    }

    public Validity valid() {
        return valid;
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

    public String symbol() {
        return symbol;
    }

    public RootKind kind() {
        return kind;
    }

    public RootCategory category() {
        return category;
    }

    public String recordedValue() {
        return recordedValue;
    }

    public String domainMin() {
        return domainMin;
    }

    public String domainMax() {
        return domainMax;
    }

    public boolean declared() {
        return declared;
    }

    public Clock clock() {
        return clock;
    }

    public long clockNanos() {
        return clock == null ? 0L : clock.nanos();
    }

    public long clockSkew() {
        return clockSkew;
    }

    public String hostReading() {
        if (clockSkew == 0L) return recordedValue;
        return new java.math.BigInteger(recordedValue.trim())
                .subtract(java.math.BigInteger.valueOf(clockSkew)).toString();
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, occurrence, rootId, symbol, kind,
                category, recordedValue, domainMin, domainMax, declared,
                clock, clockSkew, valid};
    }

    @Override
    public String toString() {
        return "RootMintRow{" + sessionId + "#" + seq + " " + rootId + " "
                + kind + "/" + category + " " + symbol + "=" + recordedValue
                + "}";
    }
}
