package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §1, IDENTITY §9: what a case declaration selects, before
 * resolution ({@link OccurrenceAddress#parseSelector}).  This type answers
 * only "is this occurrence a candidate"; the scheduler picks the k-th in
 * seed order.  The node is optional but kept when spelled.  Never an
 * address: only resolved ids reach exploration and composition.
 */
public final class Selector extends Value {
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

    /** The selector's {@code @api} segment, or {@code null}. */
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
     * Whether {@code occurrence} is a candidate.  {@code rpcSiteApi} comes
     * from the caller, since the contract cannot parse an RPC site; an api
     * selector matches only ANCHOR occurrences.
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
    Object[] parts() {
        return new Object[] {regionId, api, k, node};
    }

    @Override
    public String toString() {
        return render();
    }
}
