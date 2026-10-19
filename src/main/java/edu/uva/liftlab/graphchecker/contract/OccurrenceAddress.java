package edu.uva.liftlab.graphchecker.contract;


public final class OccurrenceAddress extends Value {
    public static final String REGION_MARKER = "/region/";
    public static final String ROLE_REGION = "ROLE.";
    private static final String CONTEXT_MARKER = "/ctx:";
    private static final String INDEX_MARKER = "/idx:";

    private final NodeId node;
    private final String regionId;
    private final CausalContext context;
    private final ExecutionIndex index;
    private String id;

    private OccurrenceAddress(NodeId node, String regionId,
                              CausalContext context, ExecutionIndex index) {
        this.node = node;
        this.regionId = regionId;
        this.context = context;
        this.index = index;
    }

    public static OccurrenceAddress of(NodeId node, String regionId,
                                       CausalContext context,
                                       ExecutionIndex index) {
        String region = Fields.text(regionId, "regionId");
        if (region.indexOf('/') >= 0) {
            throw new IllegalArgumentException(
                    "a region id carries no '/': " + regionId);
        }
        return new OccurrenceAddress(Fields.required(node, "node"), region,
                Fields.required(context, "context"),
                Fields.required(index, "index"));
    }

    public static OccurrenceAddress parse(String rendered) {
        String value = rendered == null ? "" : rendered.trim();
        int context = value.indexOf(CONTEXT_MARKER);
        int index = value.lastIndexOf(INDEX_MARKER);
        if (context <= 0 || index <= context) {
            throw malformed(rendered, "no " + CONTEXT_MARKER + " and "
                    + INDEX_MARKER + " segments");
        }
        int region = value.lastIndexOf(REGION_MARKER, context);
        if (region <= 0) {
            throw malformed(rendered, "no " + REGION_MARKER + " segment");
        }
        return of(NodeId.parse(value.substring(0, region)),
                value.substring(region + REGION_MARKER.length(), context),
                CausalContext.parse(value.substring(
                        context + CONTEXT_MARKER.length(), index)),
                ExecutionIndex.parse(
                        value.substring(index + INDEX_MARKER.length())));
    }

    public static Selector parseSelector(String v1) {
        String value = v1 == null ? "" : v1.trim();
        int region = value.lastIndexOf(REGION_MARKER);
        if (region < 0) {
            throw malformed(v1, "no " + REGION_MARKER + " segment");
        }
        NodeId node = region == 0 ? null
                : NodeId.parse(value.substring(0, region));
        String tail = value.substring(region + REGION_MARKER.length());
        int ordinal = tail.lastIndexOf('#');
        int k = Fields.trailingNumber(tail, ordinal, 1);
        if (k < 0) throw malformed(v1, "no trailing #k");
        String head = tail.substring(0, ordinal);
        int at = head.indexOf('@');
        return at < 0 ? Selector.of(head, null, k, node)
                : Selector.of(head.substring(0, at), head.substring(at + 1), k,
                node);
    }

    public NodeId node() {
        return node;
    }

    public String regionId() {
        return regionId;
    }

    public CausalContext context() {
        return context;
    }

    public ExecutionIndex index() {
        return index;
    }

    public boolean role() {
        return regionId.startsWith(ROLE_REGION);
    }

    public OccurrenceAddress anyDelivery() {
        if (!(context instanceof CausalContext.Anchor)) return this;
        CausalContext.Anchor delivered =
                ((CausalContext.Anchor) context).anyDelivery();
        return delivered == context ? this
                : new OccurrenceAddress(node, regionId, delivered, index);
    }

    public OccurrenceAddress anyTurn() {
        if (!(context instanceof CausalContext.Root)) return this;
        CausalContext.Root turned = ((CausalContext.Root) context).anyTurn();
        return turned == context ? this
                : new OccurrenceAddress(node, regionId, turned, index);
    }

    public boolean lineageLost() {
        return context.isLost();
    }

    public String render() {
        return node.render() + REGION_MARKER + regionId + CONTEXT_MARKER
                + context.render() + INDEX_MARKER + index.render();
    }

    public String id() {
        String digested = id;
        if (digested == null) {
            digested = Digests.digest(node.render() + "/" + regionId + "/"
                    + context.render() + "/" + index.hash(), 16);
            id = digested;
        }
        return digested;
    }

    @Override
    Object[] parts() {
        return new Object[] {node, regionId, context, index};
    }

    @Override
    public String toString() {
        return render();
    }

    private static IllegalArgumentException malformed(String rendered,
                                                      String why) {
        return new IllegalArgumentException(
                "not an occurrence address (" + why + "): " + rendered);
    }
}
