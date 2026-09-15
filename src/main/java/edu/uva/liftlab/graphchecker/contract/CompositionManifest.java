package edu.uva.liftlab.graphchecker.contract;

import java.util.List;
import java.util.Objects;

/**
 * CONTRACT-SPEC 4: everything one anchor's composition stands on.
 *
 * <p>The anchor, the consumer paths that were composed, the interaction
 * families their controls read, the root domains the enumeration ran over, how
 * many valuations it took, the claim, and the {@code .smt2} the solver was
 * given -- which, with z3's verdict, is the deliverable (no VALIDATE stage).
 * A manifest that cannot name its {@code .smt2} is a claim nobody can
 * re-check.</p>
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
                Fields.count(valuations, "valuations"),
                Fields.required(claim, "claim"),
                Fields.text(smt2Path, "smt2Path"));
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof CompositionManifest)) return false;
        CompositionManifest other = (CompositionManifest) value;
        return valuations == other.valuations && anchor.equals(other.anchor)
                && paths.equals(other.paths) && families.equals(other.families)
                && roots.equals(other.roots) && claim.equals(other.claim)
                && smt2Path.equals(other.smt2Path);
    }

    @Override
    public int hashCode() {
        return Objects.hash(anchor, paths, families, roots, valuations, claim,
                smt2Path);
    }

    @Override
    public String toString() {
        return "CompositionManifest{" + anchor + " " + paths.size()
                + " paths " + families.size() + " families " + claim + "}";
    }
}
