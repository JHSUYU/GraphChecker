package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * IDENTITY-IMPL A and D: what a case declaration selects, before resolution.
 *
 * <p>A human writes {@code node#epoch/region/REGION.x@src#epoch/api#k}, not an
 * execution index.  {@link OccurrenceAddress#parseSelector} reads that into
 * this: the component, the region, the api when one is given, and k.  The
 * scheduler resolves it against the SEED session -- the occurrences on that
 * component whose region matches and, when an api is given, whose
 * {@link CausalContext.Anchor} arrived on that api, taken in seed order, k-th.
 * That last step is the scheduler's: this type answers only "is this occurrence
 * one of the candidates".</p>
 *
 * <p>The component is optional because a selector may be written without one,
 * but it is read and kept when the declaration spells it: two components of one
 * session can run the same region, and a selector that dropped the node would
 * hand the k-th match on the wrong node to the campaign.</p>
 *
 * <p>A selector is deliberately not an address and never becomes one by
 * parsing.  A resolved id is published in the manifest; exploration and
 * composition use ids only.</p>
 */
public final class Selector {
    private final String regionId;
    private final String api;
    private final int k;
    private final NodeId node;

    private Selector(String regionId, String api, int k, NodeId node) {
        this.regionId = regionId;
        this.api = api;
        this.k = k;
        this.node = node;
    }

    public static Selector of(String regionId, String api, int k, NodeId node) {
        return new Selector(Fields.text(regionId, "regionId"),
                Fields.optional(api), Fields.ordinal(k, "k"), node);
    }

    public String regionId() {
        return regionId;
    }

    /** The v1 {@code <source>#epoch<N>/<api>} segment, or {@code null}. */
    public String api() {
        return api;
    }

    /** Which match, in the seed session's order. */
    public int k() {
        return k;
    }

    /** The component the declaration named, or {@code null}. */
    public NodeId node() {
        return node;
    }

    /**
     * Whether {@code occurrence} is one of this selector's candidates.
     *
     * <p>{@code rpcSiteApi} is the api the caller read out of the occurrence's
     * anchor -- the contract does not know how a deployment spells an RPC
     * static site, so the one thing it will not do is guess the api out of it.
     * A selector that names an api matches no occurrence that no message
     * started, and one that names a component matches nothing on another.</p>
     */
    public boolean matches(OccurrenceAddress occurrence, String rpcSiteApi) {
        if (occurrence == null || !regionId.equals(occurrence.regionId())) {
            return false;
        }
        if (node != null && !node.equals(occurrence.node())) return false;
        if (api == null) return true;
        return occurrence.context().form() == CausalContext.Form.ANCHOR
                && api.equals(rpcSiteApi);
    }

    /** The selector as a case declaration spells it. */
    public String render() {
        return (node == null ? "" : node.render())
                + OccurrenceAddress.REGION_MARKER + regionId
                + (api == null ? "" : "@" + api) + "#" + k;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof Selector)) return false;
        Selector other = (Selector) value;
        return k == other.k && regionId.equals(other.regionId)
                && Objects.equals(api, other.api)
                && Objects.equals(node, other.node);
    }

    @Override
    public int hashCode() {
        return Objects.hash(regionId, api, k, node);
    }

    @Override
    public String toString() {
        return render();
    }
}
