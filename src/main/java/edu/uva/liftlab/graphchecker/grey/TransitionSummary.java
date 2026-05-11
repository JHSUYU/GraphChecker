package edu.uva.liftlab.graphchecker.grey;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

public final class TransitionSummary {
    private final String method;
    private final String summaryType;
    private final String formula;
    private final List<String> evidence;

    public TransitionSummary(String method, String summaryType, String formula, List<String> evidence) {
        this.method = method;
        this.summaryType = summaryType;
        this.formula = formula;
        this.evidence = evidence == null
                ? Collections.<String>emptyList()
                : Collections.unmodifiableList(new ArrayList<String>(evidence));
    }

    public String getMethod() {
        return method;
    }

    public String getSummaryType() {
        return summaryType;
    }

    public String getFormula() {
        return formula;
    }

    public List<String> getEvidence() {
        return evidence;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TransitionSummary)) {
            return false;
        }
        TransitionSummary that = (TransitionSummary) o;
        return Objects.equals(method, that.method)
                && Objects.equals(summaryType, that.summaryType)
                && Objects.equals(formula, that.formula)
                && Objects.equals(evidence, that.evidence);
    }

    @Override
    public int hashCode() {
        return Objects.hash(method, summaryType, formula, evidence);
    }
}
