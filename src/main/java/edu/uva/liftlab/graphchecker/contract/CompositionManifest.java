package edu.uva.liftlab.graphchecker.contract;

import java.util.List;

/**
 * CONTRACT-SPEC §4: everything one anchor's composition stands on; with the
 * {@code .smt2} beside it and z3's verdict, the deliverable, and without
 * them the claim cannot be re-checked.  Written by Gson (ComposeMain), field
 * by field: the fields are the manifest's shape.  It names no location, so
 * a composition copied elsewhere is the same bytes.
 */
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
