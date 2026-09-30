package edu.uva.liftlab.graphchecker.contract;

import java.util.List;

/**
 * CONTRACT-SPEC §4: everything one anchor's composition stands on, including
 * the {@code .smt2} that with z3's verdict is the deliverable; without it the
 * claim cannot be re-checked.  Written by Gson (ComposeMain), field by
 * field: the fields are the manifest's shape.
 */
public final class CompositionManifest {
    private final OccurrenceAddress anchor;
    private final List<PathEntry> paths;
    private final List<Family> families;
    private final List<RootDomain> roots;
    private final int valuations;
    private final Claim claim;
    private final String smt2Path;

    private CompositionManifest(OccurrenceAddress anchor,
                                List<PathEntry> paths, List<Family> families,
                                List<RootDomain> roots, int valuations,
                                Claim claim, String smt2Path) {
        this.anchor = anchor;
        this.paths = paths;
        this.families = families;
        this.roots = roots;
        this.valuations = valuations;
        this.claim = claim;
        this.smt2Path = smt2Path;
    }

    public static CompositionManifest of(OccurrenceAddress anchor,
                                         List<PathEntry> paths,
                                         List<Family> families,
                                         List<RootDomain> roots,
                                         int valuations, Claim claim,
                                         String smt2Path) {
        return new CompositionManifest(Fields.required(anchor, "anchor"),
                Fields.copy(paths), Fields.copy(families), Fields.copy(roots),
                Fields.nonNegative(valuations, "valuations"),
                Fields.required(claim, "claim"),
                Fields.text(smt2Path, "smt2Path"));
    }
}
