package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 1: one hop of a control lineage, rendered {@code ROLE[@api]#k}.
 *
 * <p>{@code k} counts this hop among its parent's children of the same role and
 * api, so a lineage is a TYPE and the per-hop ordinals separate its instances
 * (IDENTITY-V2).  The api is the entry point the hop was entered through and is
 * absent for a scope that has none, such as a daemon tick.</p>
 */
public final class LineageHop {
    private final Role role;
    private final String api;
    private final int k;

    private LineageHop(Role role, String api, int k) {
        this.role = role;
        this.api = api;
        this.k = k;
    }

    public static LineageHop of(Role role, String api, int k) {
        return new LineageHop(Fields.required(role, "role"),
                Fields.optional(api), Fields.ordinal(k, "k"));
    }

    public Role role() {
        return role;
    }

    /** The entry point this hop was entered through, or {@code null}. */
    public String api() {
        return api;
    }

    /** The k in "k-th child of this role and api under the same parent". */
    public int k() {
        return k;
    }

    public String render() {
        return role.name() + (api == null ? "" : "@" + api) + "#" + k;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof LineageHop)) return false;
        LineageHop other = (LineageHop) value;
        return k == other.k && role == other.role
                && Objects.equals(api, other.api);
    }

    @Override
    public int hashCode() {
        return Objects.hash(role, api, k);
    }

    @Override
    public String toString() {
        return render();
    }
}
