package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * The symbolic roots one closure wave actually has, as expression leaves.
 *
 * <p>A campaign's search space is its declared roots and nothing else: a
 * configured symbolic source ({@link SymbolicSourceEvidence#KIND}) or an
 * explicit {@code SYMBOLIC} input action ({@link
 * SymbolicSourceEvidence#MANUAL_KIND}). Every other {@code SymbolExpression}
 * a region summary carries is a placeholder for a value the recording already
 * fixed - a receiver reference, an array length, a container state the region
 * consumed at its boundary. Those placeholders are free in a region-local
 * query only because the region is queried in isolation; across the linked
 * closure their value is whatever the replay produced, and the only thing a
 * replay may vary is a root.</p>
 *
 * <p>This inventory is what lets the planner say "this branch condition
 * cannot depend on anything the campaign can vary" without asking a solver.
 * It is deliberately conservative in both directions:</p>
 *
 * <ul>
 *   <li>It is built from the <em>whole wave</em>, never one member, so a root
 *       minted in one region is still a root when another region consumes
 *       it.</li>
 *   <li>{@link #usable()} is false whenever the wave states no root at all, or
 *       a region that declares a symbolic input reported no path here. An
 *       unusable inventory prunes nothing: incomplete dependency information
 *       is a reason to keep solving, never a licence to skip.</li>
 *   <li>A leaf minted at a configured source is recognised by
 *       {@link SymbolicSourceEvidence#engineLabelForPhase} shape as well as by
 *       name, so a source whose evidence row did not reach this wave still
 *       counts as a root rather than being pruned away.</li>
 * </ul>
 */
public final class SymbolicRootInventory {
    /** The engine label every configured-source leaf carries. */
    private static final String CONFIGURED_SOURCE_MARK = "SRC.";
    /**
     * The prefix every handoff variable carries.
     *
     * <p>A value that crossed a wire is free in the consumer's formula and
     * the campaign can vary it -- the runtime answers an assignment to it at
     * the attach -- so a decision over one is root-dependent and worth
     * flipping, exactly like a decision over a configured source.</p>
     */
    private static final String HANDOFF_MARK = "M_H_";
    private static final SymbolicRootInventory EMPTY =
            new SymbolicRootInventory(Collections.<String>emptySet(),
                    "NO_DECLARED_ROOT");

    private final Set<String> leaves;
    private final String incompleteReason;

    private SymbolicRootInventory(Set<String> leaves,
                                  String incompleteReason) {
        this.leaves = Collections.unmodifiableSet(leaves);
        this.incompleteReason = incompleteReason;
    }

    /** An inventory that admits nothing, so that no obligation is pruned. */
    public static SymbolicRootInventory disabled() {
        return EMPTY;
    }

    /**
     * The roots of one wave.
     *
     * @param summaries every summary of the wave, in any order
     * @param tasks     every execution task of the wave
     */
    public static SymbolicRootInventory of(Collection<JsonObject> summaries,
                                           Collection<JsonObject> tasks) {
        Set<String> leaves = new TreeSet<>();
        Set<String> observedRegions = new LinkedHashSet<>();
        if (summaries != null) {
            for (JsonObject summary : summaries) {
                collect(summary, leaves);
                String region = optionalString(summary, "regionId");
                if (!region.isEmpty()) observedRegions.add(region);
            }
        }
        if (leaves.isEmpty()) {
            return new SymbolicRootInventory(leaves, "NO_DECLARED_ROOT");
        }
        String unobserved = unobservedSymbolicRegion(tasks, observedRegions);
        if (!unobserved.isEmpty()) {
            return new SymbolicRootInventory(leaves,
                    "SYMBOLIC_INPUT_REGION_NOT_OBSERVED:" + unobserved);
        }
        return new SymbolicRootInventory(leaves, "");
    }

    /**
     * A region that declares a symbolic input but reported no path here.
     *
     * <p>This is the one way a root can be missing from the leaf set while
     * still being able to reach a branch condition. A declared input that
     * <em>did</em> run and minted nothing is not such a case: the importer
     * writes a {@link SymbolicSourceEvidence#MANUAL_KIND} row for every mint
     * and none for a read that reused an already-propagated expression, and a
     * read that minted nothing introduced no leaf, so nothing can depend on
     * it. An unobserved region has made no such statement either way, so the
     * filter is withheld for the whole wave.</p>
     */
    private static String unobservedSymbolicRegion(
            Collection<JsonObject> tasks, Set<String> observedRegions) {
        if (tasks == null) return "";
        for (JsonObject task : tasks) {
            String region = optionalString(task, "regionId");
            if (region.isEmpty() || observedRegions.contains(region)) {
                continue;
            }
            for (JsonElement element : array(task, "inputActions")) {
                if (element == null || !element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                if ("SYMBOLIC".equals(optionalString(action, "mode"))) {
                    return region;
                }
            }
        }
        return "";
    }

    private static void collect(JsonObject owner, Set<String> leaves) {
        if (owner == null) return;
        for (JsonElement element : array(owner, SymbolicSourceEvidence.FIELD)) {
            if (element == null || !element.isJsonObject()) continue;
            JsonObject event = element.getAsJsonObject();
            String raw = optionalString(event, "rawSymbol");
            if (raw.isEmpty()) continue;
            leaves.add(leafKey(optionalString(event, "javaType"), raw));
        }
    }

    /** The key {@link BranchPredicateAlgebra#symbolicSupport} produces. */
    static String leafKey(String javaType, String symbol) {
        return javaType + BranchPredicateAlgebra.SUPPORT_LEAF_SEPARATOR
                + symbol;
    }

    /** Whether this inventory may be used to prune. */
    public boolean usable() {
        return incompleteReason.isEmpty() && !leaves.isEmpty();
    }

    /** Why pruning is withheld, or "" when it is not. */
    public String incompleteReason() {
        return incompleteReason;
    }

    public Set<String> leaves() {
        return leaves;
    }

    /**
     * Whether a branch condition's symbolic support names a root.
     *
     * <p>Answers {@code true} for an unusable inventory: the caller must then
     * treat every obligation as possibly root-dependent.</p>
     *
     * @param support the leaf set of one predicate, as
     *                {@link BranchPredicateAlgebra#symbolicSupport} returns it
     */
    public boolean namesRoot(Set<String> support) {
        if (!usable()) return true;
        if (support == null || support.isEmpty()) return false;
        for (String leaf : support) {
            if (leaves.contains(leaf)) return true;
            // A configured source mints "SRC.<sha>"-labelled leaves.  One that
            // reached a predicate without its evidence row reaching this wave
            // is still the campaign's root, not a recorded placeholder.
            if (leaf.startsWith(HANDOFF_MARK)) return true;
            if (leaf.contains(CONFIGURED_SOURCE_MARK)) return true;
        }
        return false;
    }
}
