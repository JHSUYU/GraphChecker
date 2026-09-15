package edu.uva.liftlab.graphchecker.d3.explore;

import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Which writer occurrences a read of one location could have observed.
 *
 * <p>INTERACTION-ID R-I7.1: the alternatives for a reader occurrence R on
 * location L are the writer OCCURRENCES HB-CONCURRENT with R — not ordered
 * before or after it by program order (same thread, by seq), by message
 * causality (the {@code CausalContext.Anchor} chain), or by thread
 * start/join. A writer ordered before R contributes its version as a fact; one
 * ordered after contributes nothing. Locks are not constraints: they forbid
 * overlap, not order, and we do not record them.</p>
 *
 * <p>Granularity is the OCCURRENCE: a writer's writes to L move as a block,
 * wholly before or wholly after R's reads of L, and every read of L inside R
 * takes the same choice. Interposing one writer between two reads of one
 * occurrence would synthesise an interleaving a lock may forbid, and we have
 * not recorded the locks.</p>
 *
 * <p>Only ATTESTED writers are alternatives — a writer occurrence with a
 * recorded path. An unattested one, or one whose context is {@code Lost},
 * states its delivery and no more: with the scope unattributable there is no
 * happens-before to reason from, so it yields no alternative.</p>
 *
 * <p>What this stage can compute is stated plainly: program order inside ONE
 * occurrence (rows of one activation are one thread's, ordered by seq), and
 * message causality through the anchor chain. The contract rows carry no
 * thread id and no start/join edge, so two occurrences of one node that no
 * message relates are treated as concurrent — the permissive direction, which
 * offers the solver an interleaving rather than hiding one; every alternative
 * it takes is published, so a reader can see which.</p>
 */
final class StateEligibility {
    private StateEligibility() {
    }

    /** One writer occurrence a read could have taken its value from. */
    static final class Alternative {
        /** The write this choice binds the read to. */
        final WriteRow write;
        /** Whether this is the pairing the run recorded. */
        final boolean observed;
        final boolean attested;

        private Alternative(WriteRow write, boolean observed,
                            boolean attested) {
            this.write = write;
            this.observed = observed;
            this.attested = attested;
        }

        OccurrenceAddress writer() {
            return write.endpoint().occurrence();
        }
    }

    /**
     * Every writer occurrence eligible for one read, the observed one first.
     *
     * <p>A writer occurrence contributes ONE write — its last to that location
     * in its own session — because its writes move as a block: if the block
     * lands before R, what R reads is the last of it.</p>
     */
    static List<Alternative> alternatives(Corpus corpus, ReadRow read) {
        List<Alternative> alternatives = new ArrayList<Alternative>();
        WriteRow observed = corpus.writeOf(read.sessionId(), read.location(),
                read.observedVersion());
        Set<String> writers = new LinkedHashSet<String>();
        if (observed != null) {
            alternatives.add(new Alternative(observed, true,
                    corpus.ranFocused(observed.sessionId(),
                            observed.endpoint().occurrence())));
            writers.add(observed.endpoint().occurrence().id());
        }
        Map<String, WriteRow> lastByWriter = new LinkedHashMap<String, WriteRow>();
        for (WriteRow write : corpus.writesOf(read.location())) {
            OccurrenceAddress writer = write.endpoint().occurrence();
            if (writers.contains(writer.id())) continue;
            if (writer.context().isLost()) continue;
            if (!corpus.ranFocused(write.sessionId(), writer)) continue;
            if (!concurrent(corpus, writer, read.endpoint().occurrence())) {
                continue;
            }
            String key = write.sessionId() + "|" + writer.id();
            WriteRow held = lastByWriter.get(key);
            if (held == null || write.seq() > held.seq()) {
                lastByWriter.put(key, write);
            }
        }
        for (WriteRow write : lastByWriter.values()) {
            alternatives.add(new Alternative(write, false, true));
        }
        return alternatives;
    }

    /**
     * Whether the recorded pairing contradicts the run's own order.
     *
     * <p>Not "an earlier version by seq": two occurrences of one session
     * interleave, so seq orders events only INSIDE one activation. What
     * contradicts is a read that observed a version its own activation wrote
     * later, or one written by an occurrence the read's own occurrence caused
     * — a message cannot be answered before it is sent.</p>
     */
    static boolean contradictsOrder(Corpus corpus, ReadRow read,
                                    WriteRow observed) {
        OccurrenceAddress reader = read.endpoint().occurrence();
        OccurrenceAddress writer = observed.endpoint().occurrence();
        if (reader.equals(writer)) {
            return observed.sessionId().equals(read.sessionId())
                    && observed.seq() >= read.seq();
        }
        return orderedBefore(corpus, reader, writer);
    }

    /** Neither occurrence is ordered before the other. */
    static boolean concurrent(Corpus corpus, OccurrenceAddress left,
                              OccurrenceAddress right) {
        return !left.equals(right) && !orderedBefore(corpus, left, right)
                && !orderedBefore(corpus, right, left);
    }

    /**
     * Whether {@code earlier} caused {@code later}, through the anchor chain.
     *
     * <p>A consumer's causal context names the producer ENDPOINT that started
     * it, and that endpoint's occurrence carries its own context: the chain
     * is message causality, and it is the one cross-activation order the rows
     * state.</p>
     */
    static boolean orderedBefore(Corpus corpus, OccurrenceAddress earlier,
                                 OccurrenceAddress later) {
        Set<String> seen = new LinkedHashSet<String>();
        OccurrenceAddress cursor = later;
        while (cursor != null && seen.add(cursor.id())) {
            if (!(cursor.context() instanceof CausalContext.Anchor)) {
                return false;
            }
            Endpoint producer = corpus.endpoint(
                    ((CausalContext.Anchor) cursor.context())
                            .producerEndpointId());
            if (producer == null) return false;
            if (producer.occurrence().equals(earlier)) return true;
            cursor = producer.occurrence();
        }
        return false;
    }

    /** The eligible set, as a reader of the obligation's gaps sees it. */
    static String render(List<Alternative> alternatives) {
        List<String> named = new ArrayList<String>();
        for (Alternative alternative : alternatives) {
            named.add(alternative.writer().render()
                    + (alternative.observed ? " (observed)" : ""));
        }
        return named.isEmpty() ? "(none)" : String.join(", ", named);
    }

    static List<Alternative> none() {
        return Collections.emptyList();
    }
}
