package edu.uva.liftlab.graphchecker.contract;

import java.util.List;
import java.util.Map;

public final class Claim extends Value {
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
                Fields.nonNegative(valuationOrdinal, "valuationOrdinal"),
                Fields.copy(movedRoots), polarityDecides, Fields.copy(gaps));
    }

    public ClaimKind kind() {
        return kind;
    }

    public int valuationOrdinal() {
        return valuationOrdinal;
    }

    public Map<String, String> movedRoots() {
        return movedRoots;
    }

    public boolean polarityDecides() {
        return polarityDecides;
    }

    public List<GapRow> gaps() {
        return gaps;
    }

    public boolean blocked() {
        for (GapRow gap : gaps) {
            if (gap.blocking()) return true;
        }
        return false;
    }

    @Override
    Object[] parts() {
        return new Object[] {kind, valuationOrdinal, movedRoots,
                polarityDecides, gaps};
    }

    @Override
    public String toString() {
        return "Claim{" + kind + " at valuation " + valuationOrdinal
                + (movedRoots.isEmpty() ? "" : " moving " + movedRoots) + "}";
    }
}
