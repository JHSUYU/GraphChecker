package edu.uva.liftlab.graphchecker.grey;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public final class GreyStateAnalysisResult {
    private final List<SemanticEvent> events = new ArrayList<SemanticEvent>();
    private final List<TransitionSummary> transitionSummaries = new ArrayList<TransitionSummary>();
    private final List<UnknownEdge> unknowns = new ArrayList<UnknownEdge>();

    public void addEvent(SemanticEvent event) {
        if (event != null && !events.contains(event)) {
            events.add(event);
        }
    }

    public void addSummary(TransitionSummary summary) {
        if (summary != null && !transitionSummaries.contains(summary)) {
            transitionSummaries.add(summary);
        }
    }

    public void addUnknown(UnknownEdge unknown) {
        if (unknown != null && !unknowns.contains(unknown)) {
            unknowns.add(unknown);
        }
    }

    public List<SemanticEvent> getEvents() {
        return Collections.unmodifiableList(events);
    }

    public List<TransitionSummary> getTransitionSummaries() {
        return Collections.unmodifiableList(transitionSummaries);
    }

    public List<UnknownEdge> getUnknowns() {
        return Collections.unmodifiableList(unknowns);
    }
}
