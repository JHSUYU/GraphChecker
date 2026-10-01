package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

/**
 * CONTRACT-SPEC §1, IDENTITY §1: the one address of a region occurrence,
 * {@code node#epochN/region/REGION.x/ctx:<why>/idx:<where>} -- node and epoch,
 * static region, the {@link CausalContext} that started it, and the
 * {@link ExecutionIndex} from scope root to region entry.  Nothing else (no
 * thread id, object address or ordinal: an ordinal shifts when a flip inserts
 * an unrelated invocation).  Two occurrences are the same iff their
 * {@link #id()}s are equal.
 *
 * <p>Cases declare a {@link Selector} ({@link #parseSelector}), which the
 * scheduler resolves against the seed; it never becomes an address by
 * parsing.</p>
 */
public final class OccurrenceAddress extends Value {
    /** The one spelling of the region separator in a rendered address. */
    public static final String REGION_MARKER = "/region/";
    /** The region slot of work under no region: {@code ROLE.<role>}. */
    public static final String ROLE_REGION = "ROLE.";
    private static final String CONTEXT_MARKER = "/ctx:";
    private static final String INDEX_MARKER = "/idx:";

    private final NodeId node;
    private final String regionId;
    private final CausalContext context;
    private final ExecutionIndex index;
    /**
     * {@link #id()}, cached: admission asks it per comparison.  Unsynchronized
     * on purpose; racing threads compute the same string.
     */
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

    /** Reads {@link #render()}; refuses anything else, never half-parses. */
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

    /**
     * Reads a case's v1 selector ({@code node#epochN/region/REGION.x@api#k}
     * or {@code .../REGION.x#k}); without a node prefix it selects on every
     * component.
     */
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

    /** The component instance and epoch this occurrence ran on. */
    public NodeId node() {
        return node;
    }

    public String regionId() {
        return regionId;
    }

    /** Why this occurrence ran. */
    public CausalContext context() {
        return context;
    }

    /** Where in the component's control structure it ran. */
    public ExecutionIndex index() {
        return index;
    }

    /** Whether this is work under no region, named by its role. */
    public boolean role() {
        return regionId.startsWith(ROLE_REGION);
    }

    /**
     * This occurrence as every delivery of its stored message is addressed
     * ({@link CausalContext.Anchor#anyDelivery}); itself for any other.
     */
    public OccurrenceAddress anyDelivery() {
        if (!(context instanceof CausalContext.Anchor)) return this;
        CausalContext.Anchor delivered =
                ((CausalContext.Anchor) context).anyDelivery();
        return delivered == context ? this
                : new OccurrenceAddress(node, regionId, delivered, index);
    }

    /** Whether the context is {@link CausalContext.Lost} (derived). */
    public boolean lineageLost() {
        return context.isLost();
    }

    public String render() {
        return node.render() + REGION_MARKER + regionId + CONTEXT_MARKER
                + context.render() + INDEX_MARKER + index.render();
    }

    /** The id every row joins on; uses the index's fold, so constant-size. */
    public String id() {
        String digested = id;
        if (digested == null) {
            digested = ArtifactIO.digest(node.render() + "/" + regionId + "/"
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
