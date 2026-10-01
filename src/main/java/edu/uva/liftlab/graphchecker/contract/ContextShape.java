package edu.uva.liftlab.graphchecker.contract;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

/**
 * A causal context as the question {@code (r,c)} compares it, whatever its
 * invocation index {@code i}: per anchor hop, outermost last, the RPC site
 * the message arrived on and the node that sent it, then the root's role and
 * api -- the chain {@code runtime.Identity} renders, without the per-site
 * invocation counts (the root's window index, a sender's execution index,
 * site index and retry), which a flip may move.  A hop whose sender nothing
 * names ends the chain with {@link #UNKNOWN_HOP}, which {@link #same} reads
 * as unknown, never as a difference.
 *
 * <p>One rule for every stage that asks whether an occurrence is the
 * question's: PLAN's walk origins ({@code
 * causynth.RuntimeSelectedRegionFinalizer}) and EXPLORE's branch stops
 * ({@code explore.Branches}).</p>
 */
public final class ContextShape {
    /** The hop a shape states for a sender nothing names. */
    public static final String UNKNOWN_HOP = "?";

    private ContextShape() {
    }

    /** Where a message's sender stood when it sent: its node and context. */
    public static final class Stance {
        private final String node;
        private final CausalContext context;

        public Stance(String node, CausalContext context) {
            this.node = node;
            this.context = context;
        }

        public String node() {
            return node;
        }

        public CausalContext context() {
            return context;
        }

        /** A schedule SEND's context, {@code node|context[|...]}; null when
         *  it states no context. */
        public static Stance ofSend(String sendContext) {
            String[] parts = sendContext.split("\\|", 3);
            return parts.length < 2 ? null
                    : new Stance(parts[0], CausalContext.parse(parts[1]));
        }
    }

    /**
     * The shape of {@code context}, each anchor's sender read off {@code
     * senders} (producer endpoint id to the stance it was sent from, null
     * when nothing names it).
     */
    public static List<String> of(CausalContext context,
                                  Function<String, Stance> senders) {
        List<String> hops = new ArrayList<String>();
        Set<String> walked = new HashSet<String>();
        CausalContext cursor = context;
        while (cursor instanceof CausalContext.Anchor) {
            CausalContext.Anchor anchor = (CausalContext.Anchor) cursor;
            String producer = anchor.producerEndpointId();
            Stance sender = senders.apply(producer);
            if (!walked.add(producer) || sender == null) {
                hops.add(UNKNOWN_HOP);
                return hops;
            }
            hops.add(anchor.rpcSite() + "@" + sender.node());
            cursor = sender.context();
        }
        if (cursor instanceof CausalContext.Root) {
            CausalContext.Root root = (CausalContext.Root) cursor;
            hops.add("Root:" + root.role().name()
                    + (root.api().isEmpty() ? "" : "/" + root.api()));
        } else {
            hops.add(cursor.render());
        }
        return hops;
    }

    /**
     * Whether {@code ran} is an occurrence of the question {@code (r,c)} that
     * {@code question} names: the same region, on the same node, under a
     * context of the same shape ({@code shapes}), at any invocation index.
     */
    public static boolean sameQuestion(OccurrenceAddress ran,
            OccurrenceAddress question,
            Function<CausalContext, List<String>> shapes) {
        return ran.regionId().equals(question.regionId())
                && ran.node().equals(question.node())
                && same(shapes.apply(ran.context()),
                        shapes.apply(question.context()));
    }

    /**
     * Two shapes agree hop by hop up to the first hop either side could not
     * name: an unnamed sender is not known to differ, and an occurrence is
     * set apart from the question only on a known difference.
     */
    public static boolean same(List<String> one, List<String> other) {
        int hops = Math.min(one.size(), other.size());
        for (int hop = 0; hop < hops; hop++) {
            String mine = one.get(hop);
            String theirs = other.get(hop);
            if (UNKNOWN_HOP.equals(mine) || UNKNOWN_HOP.equals(theirs)) {
                return true;
            }
            if (!mine.equals(theirs)) return false;
        }
        return one.size() == other.size();
    }
}
