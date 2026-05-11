package edu.uva.liftlab.graphchecker.grey;

import java.util.Objects;

public final class UnknownEdge {
    private final String reason;
    private final String source;
    private final String impact;

    public UnknownEdge(String reason, String source, String impact) {
        this.reason = reason;
        this.source = source;
        this.impact = impact;
    }

    public String getReason() {
        return reason;
    }

    public String getSource() {
        return source;
    }

    public String getImpact() {
        return impact;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof UnknownEdge)) {
            return false;
        }
        UnknownEdge that = (UnknownEdge) o;
        return Objects.equals(reason, that.reason)
                && Objects.equals(source, that.source)
                && Objects.equals(impact, that.impact);
    }

    @Override
    public int hashCode() {
        return Objects.hash(reason, source, impact);
    }
}
