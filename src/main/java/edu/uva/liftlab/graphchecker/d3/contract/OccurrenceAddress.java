package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * CONTRACT-SPEC 1: the one address of a region occurrence.
 *
 * <p>{@code node#epoch<N> / hop / ... / region/REGION.x#k} -- the component
 * instance and its epoch, the control lineage that reached the region (each hop
 * a scope role, an api and the k among its parent's children of that role and
 * api), the region, and the k-th activation of it (IDENTITY-V2 sec 0).  A
 * lineage is a type; the ordinals separate its instances.</p>
 *
 * <p>{@link #parse} also reads the two v1 spellings so that a case declaration
 * written against v1 still names its occurrence:
 * {@code node#epochN/region/REGION.x@src#epochM/api#k} becomes one
 * {@link Role#REQUEST} hop {@code REQUEST@src/api#k}, and
 * {@code node#epochN/region/REGION.x#k} an address with no lineage at all --
 * which is byte-identical to what this type renders for an empty lineage.</p>
 *
 * <p>{@code lineageLost} says the runtime could not attribute some hop and the
 * address degraded to what it could name (INTERACTION-ID R-I1).  It is a
 * property of the evidence, not of the address: it is deliberately absent from
 * {@link #render()} and therefore from {@link #id()}, so a degraded row and a
 * complete row about the same activation still join.  It does take part in
 * {@link #equals}, which compares the value, not the identity.</p>
 */
public final class OccurrenceAddress {
    /** The one spelling of the region separator in a rendered address. */
    public static final String REGION_MARKER = "/region/";
    /** The v1 separator between a region and the request that reached it. */
    private static final char REQUEST_MARKER = '@';

    private final NodeId node;
    private final List<LineageHop> lineage;
    private final String regionId;
    private final int k;
    private final boolean lineageLost;

    private OccurrenceAddress(NodeId node, List<LineageHop> lineage,
                              String regionId, int k, boolean lineageLost) {
        this.node = node;
        this.lineage = lineage;
        this.regionId = regionId;
        this.k = k;
        this.lineageLost = lineageLost;
    }

    public static OccurrenceAddress of(NodeId node, List<LineageHop> lineage,
                                       String regionId, int k,
                                       boolean lineageLost) {
        return new OccurrenceAddress(Fields.required(node, "node"),
                Fields.copy(lineage), Fields.text(regionId, "regionId"),
                Fields.ordinal(k, "k"), lineageLost);
    }

    /**
     * Reads the v2 render or either v1 spelling.
     *
     * <p>Refuses anything else naming the string: a half-read address is how a
     * replay ends up matching an activation that is not the planned one.</p>
     */
    public static OccurrenceAddress parse(String rendered) {
        String value = rendered == null ? "" : rendered.trim();
        int marker = value.lastIndexOf(REGION_MARKER);
        if (marker <= 0) {
            throw malformed(rendered, "no " + REGION_MARKER + " segment");
        }
        String head = value.substring(0, marker);
        String tail = value.substring(marker + REGION_MARKER.length());

        int ordinalMarker = trailingOrdinalMarker(tail);
        if (ordinalMarker < 0) {
            throw malformed(rendered, "no trailing #k");
        }
        int k = Integer.parseInt(tail.substring(ordinalMarker + 1));
        String region = tail.substring(0, ordinalMarker);

        // The v1 case-declaration spelling carries the request that reached the
        // region behind the region itself; a region id never contains '@'.
        String request = "";
        int at = region.indexOf(REQUEST_MARKER);
        if (at >= 0) {
            request = region.substring(at + 1);
            region = region.substring(0, at);
        }

        int epoch = epochMarker(head);
        if (epoch < 0) {
            throw malformed(rendered, "no node#epoch<N>");
        }
        NodeId node = NodeId.parse(head.substring(0, epoch));
        String hops = head.substring(epoch);
        if (!hops.isEmpty()) {
            if (hops.charAt(0) != '/') {
                throw malformed(rendered, "no node#epoch<N>");
            }
            hops = hops.substring(1);
        }

        if (!request.isEmpty() && !hops.isEmpty()) {
            throw malformed(rendered,
                    "both a v2 lineage and a v1 request segment");
        }
        List<LineageHop> lineage;
        if (!request.isEmpty()) {
            lineage = new ArrayList<>(1);
            lineage.add(LineageHop.of(Role.REQUEST, request, k));
        } else {
            lineage = parseLineage(rendered, hops);
        }
        return of(node, lineage, region, k, false);
    }

    /** The component instance and epoch this occurrence ran on. */
    public NodeId node() {
        return node;
    }

    /** The control lineage that reached the region, outermost hop first. */
    public List<LineageHop> lineage() {
        return lineage;
    }

    public String regionId() {
        return regionId;
    }

    /** The k in "k-th activation of this region under this lineage". */
    public int k() {
        return k;
    }

    /** Whether a hop could not be attributed and the address degraded. */
    public boolean lineageLost() {
        return lineageLost;
    }

    public String render() {
        StringBuilder rendered = new StringBuilder(node.render());
        for (LineageHop hop : lineage) {
            rendered.append('/').append(hop.render());
        }
        return rendered.append(REGION_MARKER).append(regionId)
                .append('#').append(k).toString();
    }

    /** sha16 of {@link #render()}: the id every row joins on. */
    public String id() {
        return Ids.sha16(render());
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof OccurrenceAddress)) return false;
        OccurrenceAddress other = (OccurrenceAddress) value;
        return k == other.k && lineageLost == other.lineageLost
                && node.equals(other.node)
                && lineage.equals(other.lineage)
                && regionId.equals(other.regionId);
    }

    @Override
    public int hashCode() {
        return Objects.hash(node, lineage, regionId, k, lineageLost);
    }

    @Override
    public String toString() {
        return lineageLost ? render() + " (lineage lost)" : render();
    }

    /**
     * The index of the {@code #} of a trailing {@code #<digits>}, or -1.
     */
    private static int trailingOrdinalMarker(String value) {
        int index = value.length() - 1;
        while (index >= 0 && Character.isDigit(value.charAt(index))) {
            index--;
        }
        if (index < 0 || index == value.length() - 1) return -1;
        return value.charAt(index) == '#' && index > 0 ? index : -1;
    }

    /**
     * The end of the leading {@code <node>#epoch<N>} of a rendered head, or -1.
     *
     * <p>A node name carries slashes of its own, so the node ends at the first
     * {@code #epoch<digits>} that a segment boundary or the head's end
     * follows -- never at the first slash.</p>
     */
    private static int epochMarker(String head) {
        int found = head.indexOf(NodeId.EPOCH_MARKER);
        while (found >= 0) {
            int digits = found + NodeId.EPOCH_MARKER.length();
            int index = digits;
            while (index < head.length()
                    && Character.isDigit(head.charAt(index))) {
                index++;
            }
            if (index > digits
                    && (index == head.length() || head.charAt(index) == '/')) {
                return index;
            }
            found = head.indexOf(NodeId.EPOCH_MARKER, found + 1);
        }
        return -1;
    }

    /**
     * Reads {@code ROLE[@api]#k} hops separated by {@code /}.
     *
     * <p>An api carries both slashes and hashes (the v1 request segment is
     * {@code <source>#epoch<N>/<api>}), so a hop ends at the first
     * {@code #<digits>} that the string or another hop follows -- the one
     * boundary that reads every spelling this contract renders.</p>
     */
    private static List<LineageHop> parseLineage(String rendered, String text) {
        List<LineageHop> hops = new ArrayList<>();
        int index = 0;
        while (index < text.length()) {
            int roleEnd = roleEnd(text, index);
            Role role = role(rendered, text.substring(index, roleEnd));
            if (roleEnd >= text.length()) {
                throw malformed(rendered, "hop states no ordinal");
            }
            String api = null;
            int hash = roleEnd;
            if (text.charAt(roleEnd) == '@') {
                hash = hopEnd(rendered, text, roleEnd + 1);
                api = text.substring(roleEnd + 1, hash);
                if (api.isEmpty()) {
                    throw malformed(rendered, "hop states an empty api");
                }
            } else if (text.charAt(roleEnd) != '#') {
                throw malformed(rendered,
                        "hop " + text.substring(index) + " is not ROLE[@api]#k");
            }
            int digits = hash + 1;
            int end = digits;
            while (end < text.length()
                    && Character.isDigit(text.charAt(end))) {
                end++;
            }
            if (end == digits) {
                throw malformed(rendered, "hop states no ordinal");
            }
            hops.add(LineageHop.of(role, api,
                    Integer.parseInt(text.substring(digits, end))));
            if (end < text.length() && text.charAt(end) != '/') {
                throw malformed(rendered, "hop ordinal runs into "
                        + text.substring(end));
            }
            index = end + 1;
        }
        return hops;
    }

    private static int roleEnd(String text, int from) {
        int index = from;
        while (index < text.length()
                && (text.charAt(index) == '_'
                || (text.charAt(index) >= 'A' && text.charAt(index) <= 'Z'))) {
            index++;
        }
        return index;
    }

    private static Role role(String rendered, String name) {
        for (Role role : Role.values()) {
            if (role.name().equals(name)) return role;
        }
        throw malformed(rendered, "unknown lineage role " + name);
    }

    /** The index of the {@code #} that ends the hop whose api starts at from. */
    private static int hopEnd(String rendered, String text, int from) {
        for (int index = from; index < text.length(); index++) {
            if (text.charAt(index) != '#') continue;
            int end = index + 1;
            while (end < text.length()
                    && Character.isDigit(text.charAt(end))) {
                end++;
            }
            if (end == index + 1) continue;
            if (end == text.length()) return index;
            if (text.charAt(end) == '/' && startsHop(text, end + 1)) {
                return index;
            }
        }
        throw malformed(rendered, "hop states no ordinal");
    }

    private static boolean startsHop(String text, int from) {
        int end = roleEnd(text, from);
        if (end == from || end >= text.length()) return false;
        if (text.charAt(end) != '@' && text.charAt(end) != '#') return false;
        String name = text.substring(from, end);
        for (Role role : Role.values()) {
            if (role.name().equals(name)) return true;
        }
        return false;
    }

    private static IllegalArgumentException malformed(String rendered,
                                                      String why) {
        return new IllegalArgumentException(
                "not an occurrence address (" + why + "): " + rendered);
    }
}
