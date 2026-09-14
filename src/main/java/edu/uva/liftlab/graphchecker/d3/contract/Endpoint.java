package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 1: one side of an interaction.
 *
 * <p>{@code (occurrence, site, ordinal, attempt)} -- which activation, which
 * declared port or which read/write site inside it, the k-th event of that site
 * in that activation, and the retry number when the transport retried
 * (INTERACTION-ID sec 1).  The site is the declared port id for a WIRE endpoint
 * (e.g. {@code XCH.<uuid>.resp.block-key-id}) and
 * {@code <class>#<method>#<bci>:<READ|WRITE>} for a STATE endpoint, which
 * {@link #stateSite} spells so that the runtime that writes it and the composer
 * that joins on it cannot drift.</p>
 *
 * <p>Neither endpoint alone identifies an interaction: the consumer side admits
 * a different producer that served the same k-th attach, the producer side a
 * different consumer.  That is why this type exists separately from
 * {@link Interaction}.</p>
 */
public final class Endpoint {
    private final OccurrenceAddress occurrence;
    private final String site;
    private final int ordinal;
    private final int attempt;

    private Endpoint(OccurrenceAddress occurrence, String site, int ordinal,
                     int attempt) {
        this.occurrence = occurrence;
        this.site = site;
        this.ordinal = ordinal;
        this.attempt = attempt;
    }

    public static Endpoint of(OccurrenceAddress occurrence, String site,
                              int ordinal, int attempt) {
        return new Endpoint(Fields.required(occurrence, "occurrence"),
                Fields.text(site, "site"), Fields.ordinal(ordinal, "ordinal"),
                Fields.count(attempt, "attempt"));
    }

    /** The one spelling of a STATE endpoint's site. */
    public static String stateSite(String className, String method, int bci,
                                   boolean write) {
        return Fields.text(className, "className") + "#"
                + Fields.text(method, "method") + "#"
                + Fields.count(bci, "bci") + ":" + (write ? "WRITE" : "READ");
    }

    public OccurrenceAddress occurrence() {
        return occurrence;
    }

    /** The declared port id (WIRE) or the read/write site (STATE). */
    public String site() {
        return site;
    }

    /** The k-th event of this site inside this occurrence, 1-based. */
    public int ordinal() {
        return ordinal;
    }

    /** The retry number, 0 when the transport did not retry. */
    public int attempt() {
        return attempt;
    }

    public String id() {
        return Ids.sha16(occurrence.id() + "\n" + site + "\n" + ordinal
                + "\n" + attempt);
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof Endpoint)) return false;
        Endpoint other = (Endpoint) value;
        return ordinal == other.ordinal && attempt == other.attempt
                && site.equals(other.site)
                && occurrence.equals(other.occurrence);
    }

    @Override
    public int hashCode() {
        return Objects.hash(occurrence, site, ordinal, attempt);
    }

    @Override
    public String toString() {
        return occurrence.render() + " " + site + "#" + ordinal
                + (attempt == 0 ? "" : " attempt " + attempt);
    }
}
