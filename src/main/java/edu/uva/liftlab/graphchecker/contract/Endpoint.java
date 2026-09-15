package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
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

    /** The one spelling of a STATE endpoint's site, no descriptor stated. */
    public static String stateSite(String className, String method, int bci,
                                   boolean write) {
        return stateSite(className, method, "", bci, write);
    }

    /**
     * The one spelling of a STATE endpoint's site.
     *
     * <p>{@code descriptor} is the JVM method descriptor of the method the
     * event stood in, as the VM's log states it ({@code ()I}), and it is part
     * of the member because two overloads of one name are two methods: a site
     * spelled without it would merge the reads of {@code get()} and
     * {@code get(int)} into one endpoint.  The empty descriptor is a site the
     * run states no descriptor for, not a claim about the signature.</p>
     */
    public static String stateSite(String className, String method,
                                   String descriptor, int bci, boolean write) {
        return site(className, method, descriptor, bci,
                write ? "WRITE" : "READ");
    }

    /** The one spelling of an allocation site (IDENTITY-V3 sec 5). */
    public static String allocationSite(String className, String method,
                                        int bci, boolean array) {
        return site(className, method, "", bci,
                array ? "NEWARRAY" : "NEW");
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
        return ArtifactIO.digest(occurrence.id() + "/" + site + "/"
                + siteIndex.hash() + "/" + attempt, 16);
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

    /**
     * The one renderer of every read/write/allocation site.
     *
     * <p>{@code <class>#<member>#<bci>:<KIND>}, where the member is the
     * method name followed by its descriptor when the run states one.  It
     * renders what it is given and normalizes nothing: the one place that
     * reads a site out of the VM's log puts the class in source form there,
     * so a name is converted once rather than at every render.</p>
     */
    private static String site(String className, String method,
                               String descriptor, int bci, String kind) {
        String stated = descriptor == null ? "" : descriptor.trim();
        return Fields.text(className, "className") + "#"
                + Fields.text(method, "method") + stated + "#"
                + Fields.count(bci, "bci") + ":" + kind;
    }
}
