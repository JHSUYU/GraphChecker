package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: a root the session minted, with its resolved domain.
 *
 * <p>Domains are declared relative to the recorded value and resolved to
 * absolute bounds here, so the composer and the flip solver read one number
 * rather than each applying the offset themselves.  A root with no domain
 * ({@code domainMin} and {@code domainMax} null) is pinned everywhere, and
 * {@code declared} says whether the case declared it at all -- an undeclared
 * root is evidence, not a degree of freedom.</p>
 */
public final class RootMintRow {
    private final String sessionId;
    private final OccurrenceAddress occurrence;
    private final String rootId;
    private final String symbol;
    private final RootKind kind;
    private final String recordedValue;
    private final String domainMin;
    private final String domainMax;
    private final boolean declared;

    private RootMintRow(String sessionId, OccurrenceAddress occurrence,
                        String rootId, String symbol, RootKind kind,
                        String recordedValue, String domainMin,
                        String domainMax, boolean declared) {
        this.sessionId = sessionId;
        this.occurrence = occurrence;
        this.rootId = rootId;
        this.symbol = symbol;
        this.kind = kind;
        this.recordedValue = recordedValue;
        this.domainMin = domainMin;
        this.domainMax = domainMax;
        this.declared = declared;
    }

    public static RootMintRow of(String sessionId, OccurrenceAddress occurrence,
                                 String rootId, String symbol, RootKind kind,
                                 String recordedValue, String domainMin,
                                 String domainMax, boolean declared) {
        return new RootMintRow(Fields.text(sessionId, "sessionId"),
                Fields.required(occurrence, "occurrence"),
                Fields.text(rootId, "rootId"), Fields.text(symbol, "symbol"),
                Fields.required(kind, "kind"),
                Fields.stated(recordedValue, "recordedValue"),
                Fields.optional(domainMin), Fields.optional(domainMax),
                declared);
    }

    public String sessionId() {
        return sessionId;
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

    /** Whether the root may move at all: an undeclared or undomained root. */
    public boolean pinned() {
        return domainMin == null && domainMax == null;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof RootMintRow)) return false;
        RootMintRow other = (RootMintRow) value;
        return declared == other.declared && kind == other.kind
                && sessionId.equals(other.sessionId)
                && occurrence.equals(other.occurrence)
                && rootId.equals(other.rootId) && symbol.equals(other.symbol)
                && recordedValue.equals(other.recordedValue)
                && Objects.equals(domainMin, other.domainMin)
                && Objects.equals(domainMax, other.domainMax);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, occurrence, rootId, symbol, kind,
                recordedValue, domainMin, domainMax, declared);
    }

    @Override
    public String toString() {
        return "RootMintRow{" + sessionId + " " + rootId + " " + kind + " "
                + symbol + "=" + recordedValue + "}";
    }
}
