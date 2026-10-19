package edu.uva.liftlab.graphchecker.contract;

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

    public String api() {
        return api;
    }

    public int k() {
        return k;
    }

    public NodeId node() {
        return node;
    }

    public boolean matches(OccurrenceAddress occurrence, String rpcSiteApi) {
        if (occurrence == null || !regionId.equals(occurrence.regionId())) {
            return false;
        }
        if (node != null && !node.equals(occurrence.node())) return false;
        if (api == null) return true;
        return occurrence.context().form() == CausalContext.Form.ANCHOR
                && api.equals(rpcSiteApi);
    }

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
