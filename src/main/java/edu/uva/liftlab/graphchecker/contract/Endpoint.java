package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.util.Objects;

/**
 * IDENTITY-IMPL A: one side of an interaction, {@code (occurrence, site,
 * siteIndex, attempt)}.  The site index (frames from region entry to the
 * site) replaces an ordinal, which moves when an unrelated event is inserted.
 *
 * <p>Site: the declared port id (WIRE), or {@code <class>#<method>#<bci>:KIND}
 * spelled only by {@link #stateSite}, so writer and joiner cannot drift.
 * One endpoint does not identify an {@link Interaction}.</p>
 */
public final class Endpoint {
    private final OccurrenceAddress occurrence;
    private final String site;
    private final ExecutionIndex siteIndex;
    private final int attempt;
    /** {@link #id()}, cached: lookups ask every filed endpoint for it. */
    private String id;

    private Endpoint(OccurrenceAddress occurrence, String site,
                     ExecutionIndex siteIndex, int attempt) {
        this.occurrence = occurrence;
        this.site = site;
        this.siteIndex = siteIndex;
        this.attempt = attempt;
    }

    public static Endpoint of(OccurrenceAddress occurrence, String site,
                              ExecutionIndex siteIndex, int attempt) {
        return new Endpoint(Fields.required(occurrence, "occurrence"),
                Fields.text(site, "site"),
                Fields.required(siteIndex, "siteIndex"),
                Fields.nonNegative(attempt, "attempt"));
    }

    /** The one spelling of a STATE endpoint's site, no descriptor stated. */
    public static String stateSite(String className, String method, int bci,
                                   boolean write) {
        return stateSite(className, method, "", bci, write);
    }

    /**
     * The one spelling of a STATE endpoint's site,
     * {@code <class>#<method><descriptor>#<bci>:<KIND>}.  {@code descriptor}
     * (e.g. {@code ()I}) keeps overloads apart; {@code ""} means none was
     * stated.  Normalizes nothing (the VM-log reader puts the class in source
     * form once).
     */
    public static String stateSite(String className, String method,
                                   String descriptor, int bci, boolean write) {
        String stated = descriptor == null ? "" : descriptor.trim();
        return Fields.text(className, "className") + "#"
                + Fields.text(method, "method") + stated + "#"
                + Fields.nonNegative(bci, "bci") + ":"
                + (write ? "WRITE" : "READ");
    }

    public OccurrenceAddress occurrence() {
        return occurrence;
    }

    /** The declared port id (WIRE), the read/write site, or the allocation. */
    public String site() {
        return site;
    }

    /** The frames from the region entry to this event. */
    public ExecutionIndex siteIndex() {
        return siteIndex;
    }

    /** The retry number, 0 when the transport did not retry. */
    public int attempt() {
        return attempt;
    }

    public String id() {
        String digested = id;
        if (digested == null) {
            digested = ArtifactIO.digest(occurrence.id() + "/" + site + "/"
                    + siteIndex.hash() + "/" + attempt, 16);
            id = digested;
        }
        return digested;
    }

    // Trap: this digest is recursive (occurrence -> Anchor context ->
    // producer endpoint -> its occurrence), so one unreproduced link changes
    // the id.  Do not truncate the chain: producers that differ only in their
    // chain then collide (TOPOLOGY_DIVERGENCE).  The open fix is a
    // reproducible per-message ordinal digested in place of the chain.

    /** The canonical spelling, for reports and refusals. */
    public String render() {
        return occurrence.render() + "/site:" + site + "/sidx:"
                + siteIndex.render() + "/att:" + attempt;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof Endpoint)) return false;
        Endpoint other = (Endpoint) value;
        return attempt == other.attempt && site.equals(other.site)
                && siteIndex.equals(other.siteIndex)
                && occurrence.equals(other.occurrence);
    }

    @Override
    public int hashCode() {
        return Objects.hash(occurrence, site, siteIndex, attempt);
    }

    @Override
    public String toString() {
        return render();
    }
}
