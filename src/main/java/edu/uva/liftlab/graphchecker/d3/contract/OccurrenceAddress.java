package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * IDENTITY-IMPL A: the one address of a region occurrence.
 *
 * <p>{@code node#epochN / region/REGION.x / ctx:<why it ran> / idx:<where>} --
 * the component instance and its topology epoch, the static region, the
 * {@link CausalContext} that started it (recursively, through the producer
 * endpoint id of an {@link CausalContext.Anchor}), and the
 * {@link ExecutionIndex} of the path from the scope root to the region entry.
 * Nothing else: no thread id, no object address, no session counter, no k-th
 * activation.</p>
 *
 * <p>That is the point of v3.  A flat ordinal ("the k-th activation under the
 * parent") shifts as soon as an unrelated invocation is inserted, which is
 * exactly what a branch flip does; an execution index moves only when the path
 * to this point moves.  Two occurrences in two replays are THE SAME iff their
 * {@link #id()}s are equal.</p>
 *
 * <p>Humans do not write execution indexes: a case declares a {@link Selector}
 * in the v1 spelling and {@link #parseSelector} reads it.  A selector is not an
 * address and never becomes one by parsing -- the scheduler resolves it against
 * a seed session's occurrences.</p>
 */
public final class OccurrenceAddress {
    /** The one spelling of the region separator in a rendered address. */
    public static final String REGION_MARKER = "/region/";
    private static final String CONTEXT_MARKER = "/ctx:";
    private static final String INDEX_MARKER = "/idx:";

    private final NodeId node;
    private final String regionId;
    private final CausalContext context;
    private final ExecutionIndex index;

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

    /**
     * Reads {@link #render()}.
     *
     * <p>Refuses anything else naming the string: a half-read address is how a
     * replay ends up answering with an occurrence that is not the planned
     * one.</p>
     */
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
     * Reads a case declaration's v1 selector -- NOT an address.
     *
     * <p>Both v1 spellings: {@code node#epochN/region/REGION.x@src#epochM/api#k}
     * and {@code node#epochN/region/REGION.x#k}.  The node prefix is read and
     * dropped: a selector is resolved against one seed session, which already
     * fixes the component, and the parts that select are the region, the api
     * when one is given, and k.</p>
     */
    public static Selector parseSelector(String v1) {
        String value = v1 == null ? "" : v1.trim();
        int region = value.lastIndexOf(REGION_MARKER);
        if (region <= 0) {
            throw malformed(v1, "no " + REGION_MARKER + " segment");
        }
        String tail = value.substring(region + REGION_MARKER.length());
        int ordinal = tail.length() - 1;
        while (ordinal >= 0 && Character.isDigit(tail.charAt(ordinal))) {
            ordinal--;
        }
        if (ordinal < 0 || ordinal == tail.length() - 1
                || tail.charAt(ordinal) != '#' || ordinal == 0) {
            throw malformed(v1, "no trailing #k");
        }
        int k = Integer.parseInt(tail.substring(ordinal + 1));
        String head = tail.substring(0, ordinal);
        int at = head.indexOf('@');
        return at < 0 ? Selector.of(head, null, k)
                : Selector.of(head.substring(0, at), head.substring(at + 1), k);
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

    /**
     * Whether the scope behind this occurrence was unattributable.
     *
     * <p>Derived, not stored: v3 states the degradation as the context's
     * {@link CausalContext.Lost} form, so there is one place that says it and
     * the id carries it.</p>
     */
    public boolean lineageLost() {
        return context.isLost();
    }

    public String render() {
        return node.render() + REGION_MARKER + regionId + CONTEXT_MARKER
                + context.render() + INDEX_MARKER + index.render();
    }

    /**
     * The id every row joins on.
     *
     * <p>Composed from the index's fold rather than its frames, so an id is
     * constant-size however deep the path was.</p>
     */
    public String id() {
        return Ids.sha16(node.render() + "/" + regionId + "/"
                + context.render() + "/" + index.hash());
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof OccurrenceAddress)) return false;
        OccurrenceAddress other = (OccurrenceAddress) value;
        return node.equals(other.node) && regionId.equals(other.regionId)
                && context.equals(other.context)
                && index.equals(other.index);
    }

    @Override
    public int hashCode() {
        return Objects.hash(node, regionId, context, index);
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
