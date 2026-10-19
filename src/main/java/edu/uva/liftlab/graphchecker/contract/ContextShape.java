package edu.uva.liftlab.graphchecker.contract;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

public final class ContextShape {
    public static final String UNKNOWN_HOP = "?";
    private static final String ROOT_HOP = "Root:";

    private ContextShape() {
    }

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

        public static Stance of(OccurrenceAddress occurrence) {
            return new Stance(occurrence.node().render(),
                    occurrence.context());
        }

        public String render() {
            return node + "|" + context.render();
        }

        public static Stance ofSend(String sendContext) {
            String[] parts = sendContext.split("\\|", 3);
            if (parts.length < 2 || VIEW_STANCE.equals(parts[1])) return null;
            return new Stance(parts[0], CausalContext.parse(parts[1]));
        }

        public static final String VIEW_STANCE = "VIEW";
    }

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

    public static boolean sameQuestion(OccurrenceAddress ran,
            OccurrenceAddress question,
            Function<CausalContext, List<String>> shapes) {
        return ran.regionId().equals(question.regionId())
                && ran.node().equals(question.node())
                && same(shapes.apply(ran.context()),
                        shapes.apply(question.context()));
    }

    public static boolean answers(OccurrenceAddress ran,
                                  OccurrenceAddress declared,
                                  List<String> ranShape,
                                  List<String> declaredShape) {
        return ran.regionId().equals(declared.regionId())
                && ran.node().equals(declared.node())
                && rootedInWindow(ranShape)
                && ranShape.equals(declaredShape);
    }

    public static boolean rootedInWindow(List<String> shape) {
        return !shape.isEmpty()
                && shape.get(shape.size() - 1).startsWith(ROOT_HOP);
    }

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
