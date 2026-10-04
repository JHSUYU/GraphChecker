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
 * causynth.RuntimeSelectedRegionFinalizer}), EXPLORE's branch stops
 * ({@code explore.Branches}) and a replay's answer to the declared
 * occurrence ({@link #answers}, {@code runtime.ConcolicTaskPlan}).</p>
 */
public final class ContextShape {
    /** The hop a shape states for a sender nothing names. */
    public static final String UNKNOWN_HOP = "?";
    /** How a shape's last hop names the root its chain began at. */
    private static final String ROOT_HOP = "Root:";

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

        /** Where an occurrence stands: its node and causal context. */
        public static Stance of(OccurrenceAddress occurrence) {
            return new Stance(occurrence.node().render(),
                    occurrence.context());
        }

        /** {@code node|context}: a schedule context without its handoffs. */
        public String render() {
            return node + "|" + context.render();
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
            hops.add(ROOT_HOP + root.role().name()
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
     * Whether {@code ran}, an occurrence a replay ran at an address no task
     * plans, answers the declared occurrence {@code declared}: the same
     * region, on the same node, under a chain of anchors whose shape is the
     * declared one's hop for hop ({@code ranShape}, {@code declaredShape},
     * both off their own run's senders) and known up to the root it began
     * at ({@link #rootedInWindow}).  Stricter than {@link #sameQuestion},
     * which keeps an occurrence in the question unless a hop is known to
     * differ: here the run's occurrence takes the declared address, which
     * only a chain known end to end may do; an unnamed sender or a {@code
     * Lost} context names none.
     */
    public static boolean answers(OccurrenceAddress ran,
                                  OccurrenceAddress declared,
                                  List<String> ranShape,
                                  List<String> declaredShape) {
        return ran.regionId().equals(declared.regionId())
                && ran.node().equals(declared.node())
                && rootedInWindow(ranShape)
                && ranShape.equals(declaredShape);
    }

    /**
     * Whether a shape's chain is known end to end, back to the root it began
     * at: every message on it was sent inside the window by a sender the
     * order names, so a replay held to the window's order holds the whole
     * chain.  A message sent before the window ends a chain with {@link
     * #UNKNOWN_HOP}, as does any sender nothing names, and a {@code Lost}
     * context (a turn begun before the window) has no root.  What was sent
     * before the window ran inside or before it as each run's timing fell
     * (round HG2's hdfs-adhoc-19: the DataNode's first block report, sent
     * before the window, answered inside it in the recording and before it
     * in the replay).
     */
    public static boolean rootedInWindow(List<String> shape) {
        return !shape.isEmpty()
                && shape.get(shape.size() - 1).startsWith(ROOT_HOP);
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
