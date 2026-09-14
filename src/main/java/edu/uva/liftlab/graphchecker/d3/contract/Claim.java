package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * CONTRACT-SPEC 4: the conclusion, with what it took and what it stepped over.
 *
 * <p>{@code valuationOrdinal} is which enumerated valuation carried it (0 is
 * the recorded one); {@code movedRoots} names every root that had to move and
 * to what; {@code polarityDecides} says the seed disjunct is unsat at the
 * recorded valuation, which is what separates an explanation from a formula
 * that was always satisfiable.  The gaps travel with the claim so that a report
 * can never state the conclusion without the diagnostics it stands on.</p>
 */
public final class Claim {
    private final ClaimKind kind;
    private final int valuationOrdinal;
    private final Map<String, String> movedRoots;
    private final boolean polarityDecides;
    private final List<GapRow> gaps;

    private Claim(ClaimKind kind, int valuationOrdinal,
                  Map<String, String> movedRoots, boolean polarityDecides,
                  List<GapRow> gaps) {
        this.kind = kind;
        this.valuationOrdinal = valuationOrdinal;
        this.movedRoots = movedRoots;
        this.polarityDecides = polarityDecides;
        this.gaps = gaps;
    }

    public static Claim of(ClaimKind kind, int valuationOrdinal,
                           Map<String, String> movedRoots,
                           boolean polarityDecides, List<GapRow> gaps) {
        return new Claim(Fields.required(kind, "kind"),
                Fields.count(valuationOrdinal, "valuationOrdinal"),
                Fields.copy(movedRoots), polarityDecides, Fields.copy(gaps));
    }

    public ClaimKind kind() {
        return kind;
    }

    /** Which enumerated valuation carried the claim; 0 is the recorded one. */
    public int valuationOrdinal() {
        return valuationOrdinal;
    }

    /** Root symbol to the value the witness moved it to. */
    public Map<String, String> movedRoots() {
        return movedRoots;
    }

    /** Whether the seed disjunct is unsat at the recorded valuation. */
    public boolean polarityDecides() {
        return polarityDecides;
    }

    public List<GapRow> gaps() {
        return gaps;
    }

    /** Whether any gap this claim carries blocks it. */
    public boolean blocked() {
        for (GapRow gap : gaps) {
            if (gap.blocking()) return true;
        }
        return false;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof Claim)) return false;
        Claim other = (Claim) value;
        return kind == other.kind
                && valuationOrdinal == other.valuationOrdinal
                && polarityDecides == other.polarityDecides
                && movedRoots.equals(other.movedRoots)
                && gaps.equals(other.gaps);
    }

    @Override
    public int hashCode() {
        return Objects.hash(kind, valuationOrdinal, movedRoots,
                polarityDecides, gaps);
    }

    @Override
    public String toString() {
        return "Claim{" + kind + " at valuation " + valuationOrdinal
                + (movedRoots.isEmpty() ? "" : " moving " + movedRoots) + "}";
    }
}
