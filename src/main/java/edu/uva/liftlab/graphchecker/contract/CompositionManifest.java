package edu.uva.liftlab.graphchecker.contract;

import java.util.List;

public final class CompositionManifest {
    private final OccurrenceAddress anchor;
    private final List<PathEntry> paths;
    private final List<Family> families;
    private final List<RootDomain> roots;
    private final int valuations;
    private final Claim claim;

    private CompositionManifest(OccurrenceAddress anchor,
                                List<PathEntry> paths, List<Family> families,
                                List<RootDomain> roots, int valuations,
                                Claim claim) {
        this.anchor = anchor;
        this.paths = paths;
        this.families = families;
        this.roots = roots;
        this.valuations = valuations;
        this.claim = claim;
    }

    public static CompositionManifest of(OccurrenceAddress anchor,
                                         List<PathEntry> paths,
                                         List<Family> families,
                                         List<RootDomain> roots,
                                         int valuations, Claim claim) {
        return new CompositionManifest(Fields.required(anchor, "anchor"),
                Fields.copy(paths), Fields.copy(families), Fields.copy(roots),
                Fields.nonNegative(valuations, "valuations"),
                Fields.required(claim, "claim"));
    }
}
