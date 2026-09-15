package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * IDENTITY-IMPL A: one side of an interaction.
 *
 * <p>{@code (occurrence, site, siteIndex, attempt)} -- which occurrence, which
 * declared port or read/write site inside it, WHERE in the region's control
 * structure that event happened (the frames from the region entry to the site),
 * and the retry number when the transport retried.  The site index replaces
 * v2's "k-th event of that site": an ordinal moves when an unrelated earlier
 * event is inserted, an execution index does not.</p>
 *
 * <p>The site is the declared port id for a WIRE endpoint (e.g.
 * {@code XCH.<uuid>.resp.block-key-id}), {@code <class>#<method>#<bci>:<READ|
 * WRITE>} for a STATE endpoint, and {@code <class>#<method>#<bci>:NEW} or
 * {@code :NEWARRAY} for an allocation -- {@link #stateSite} and
 * {@link #allocationSite} spell those so the runtime that writes them and the
 * composer that joins on them cannot drift.</p>
 *
 * <p>Neither endpoint alone identifies an interaction: the consumer side admits
 * a different producer that served the same attach, the producer side a
 * different consumer.  That is why this type exists separately from
 * {@link Interaction}.</p>
 */
public final class Endpoint {
    private final OccurrenceAddress occurrence;
    private final String site;
    private final ExecutionIndex siteIndex;
    private final int attempt;

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
                Fields.count(attempt, "attempt"));
    }

    /** The one spelling of a STATE endpoint's site. */
    public static String stateSite(String className, String method, int bci,
                                   boolean write) {
        return site(className, method, bci, write ? "WRITE" : "READ");
    }

    /** The one spelling of an allocation site (IDENTITY-V3 sec 5). */
    public static String allocationSite(String className, String method,
                                        int bci, boolean array) {
        return site(className, method, bci, array ? "NEWARRAY" : "NEW");
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
        return Ids.sha16(occurrence.id() + "/" + site + "/"
                + siteIndex.hash() + "/" + attempt);
    }

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

    private static String site(String className, String method, int bci,
                               String kind) {
        return Fields.text(className, "className") + "#"
                + Fields.text(method, "method") + "#"
                + Fields.count(bci, "bci") + ":" + kind;
    }
}
