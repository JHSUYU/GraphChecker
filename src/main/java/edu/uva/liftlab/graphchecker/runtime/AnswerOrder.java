package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

final class AnswerOrder {
    private AnswerOrder() {
    }

    interface Planned {
        OccurrenceAddress address();

        List<String> shape();

        Set<String> recordedBeside();

        long recordedRootCall();

        String rootHookGroup();
    }

    interface Offer<R> {
        List<? extends Planned> tasks();

        boolean offered(int index);

        R refusal(int index);

        OccurrenceAddress observed(R refusal);

        boolean live(int index);

        void take(int index, boolean byShape);

        void unaddressed(int index, R refusal);

        void recordedHere(int index, R refusal);

        boolean openedNone();
    }

    static <R> int select(Offer<R> offer,
                          Function<CausalContext, List<String>> shapes) {
        List<? extends Planned> tasks = offer.tasks();
        int answering = -1;
        R answered = null;
        for (int index = 0; index < tasks.size(); index++) {
            if (!offer.offered(index)) continue;
            Planned task = tasks.get(index);
            R refused = offer.refusal(index);
            if (refused != null) {
                if (!offer.live(index)
                        && answers(task, offer.observed(refused), shapes)
                        && (answering < 0
                        || earlier(task, tasks.get(answering)))) {
                    if (answering >= 0) {
                        offer.unaddressed(answering, answered);
                    }
                    answering = index;
                    answered = refused;
                    continue;
                }
                offer.unaddressed(index, refused);
                continue;
            }
            if (offer.live(index)) continue;
            offer.take(index, false);
            if (answered != null) {
                offer.unaddressed(answering, answered);
            }
            return index;
        }
        if (answering < 0) return -1;
        if (!answeredHere(offer, answering, answered)) return -1;
        offer.take(answering, true);
        return answering;
    }

    static <R> boolean answeredHere(Offer<R> offer, int index, R answered) {
        Planned task = offer.tasks().get(index);
        OccurrenceAddress observed = offer.observed(answered);
        if (recorded(task, observed)) {
            offer.recordedHere(index, answered);
            return false;
        }
        if (occupies(offer.tasks(), task.rootHookGroup(), observed)
                || offer.openedNone()) {
            offer.unaddressed(index, answered);
            return false;
        }
        return true;
    }

    static boolean answers(Planned task, OccurrenceAddress observed,
                           Function<CausalContext, List<String>> shapes) {
        OccurrenceAddress address = task.address();
        return !task.shape().isEmpty() && address != null && observed != null
                && observed.regionId().equals(address.regionId())
                && observed.node().equals(address.node())
                && ContextShape.answers(observed, address,
                shapes.apply(observed.context()), task.shape());
    }

    static boolean earlier(Planned task, Planned other) {
        return task.recordedRootCall() >= 0L
                && (other.recordedRootCall() < 0L
                || task.recordedRootCall() < other.recordedRootCall());
    }

    static boolean recorded(Planned task, OccurrenceAddress observed) {
        return observed != null
                && task.recordedBeside().contains(observed.id());
    }

    static boolean occupies(List<? extends Planned> tasks,
                            String rootHookGroup, OccurrenceAddress address) {
        for (Planned task : tasks) {
            if (task.address() != null
                    && task.rootHookGroup().equals(rootHookGroup)
                    && task.address().regionId().equals(address.regionId())
                    && task.address().node().equals(address.node())
                    && task.address().context().render().equals(
                    address.context().render())) {
                return true;
            }
        }
        return false;
    }

    static boolean receiverFits(String receiverRuntimeClass,
                                Object receiver) {
        return receiverRuntimeClass.isEmpty()
                || receiver != null && receiverRuntimeClass.equals(
                receiver.getClass().getName());
    }

    static Function<CausalContext, List<String>> shapes() {
        final Map<CausalContext, List<String>> read =
                new HashMap<CausalContext, List<String>>();
        return context -> read.computeIfAbsent(context, ScheduleLog::shape);
    }
}
