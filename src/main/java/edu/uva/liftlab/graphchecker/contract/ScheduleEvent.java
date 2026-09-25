package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * One scheduling event of a run: {@code (kind, c, site, k)}.
 *
 * <p>The schedule of a run is the total order of these events, one file per
 * session ({@link SessionDir#SCHEDULE}).  A focused replay is held to the
 * prefix of the schedule of the session its task was cut from, so the
 * occurrences it re-runs before the flip are the ones that session ran, in
 * the same order, under the same addresses.</p>
 *
 * <p>Every component is a quantity the identity already has: {@code c} is the
 * causal context of the thread at the event -- the node the attribution rule
 * names, then the rendered {@link CausalContext} -- {@code site} the static
 * site, {@code k} the k-th event of that {@code (kind, c, site)} in the log.
 * No thread id and no time: two replays compare events by what they ARE,
 * never by which pool thread happened to make them or when.</p>
 *
 * <p>{@code occurrence} is where the event happened, the id of the region
 * occurrence open on the thread (or {@code ""} outside every region).  It is
 * not part of the event's key: it is what a task's prefix is cut at -- the
 * first event of the occurrence the task focuses.</p>
 */
public final class ScheduleEvent {
    /** What kind of handoff the event is. */
    public enum Kind {
        /** A work start: {@code Thread.start}, a submission, a queue put. */
        START,
        /** Started work begins to run on the thread that took it. */
        CLAIM,
        /** A message leaves. */
        SEND,
        /** A message is installed on the thread that serves it. */
        RECV,
        /**
         * A timed wait's TIMEOUT ended it: the next turn of a service loop
         * begins.  A wait a signal ended is no event -- the notifier's own
         * events order it.
         */
        WAKE,
        /**
         * A daemon turn (a tick) the window saw begin has ended: what it
         * wrote is in the world from here on.  A turn's writes are no
         * message, so its WAKE alone ordered where it started and nothing
         * of what it did -- hdfs-17899-bug2's NameNode monitor rotated the
         * keys and marked every DataNode for a key update inside one tick,
         * and a replay's heartbeat reached the NameNode before the marking
         * that the recording's heartbeat had found done.
         */
        END,
        /**
         * A timed wait the workload's INTERRUPT ended.  Not a turn time
         * handed the thread: the interrupter's own events order it, so it is
         * written where it happens and never held, and a held wait is ended
         * by virtual time only at a WAKE -- a recording whose daemon was
         * stopped by an interrupt does not hand its replay a timeout.
         */
        INTERRUPT
    }

    private final long seq;
    private final Kind kind;
    private final String context;
    private final String site;
    private final int k;
    private final String occurrence;
    /**
     * The producer endpoint a SEND minted for its message ({@code ""} for
     * every other event): what the message's receiver runs under as its
     * ANCHOR, so the sender of a served message is a fact the rows state.
     */
    private final String endpoint;

    private ScheduleEvent(long seq, Kind kind, String context, String site,
                          int k, String occurrence, String endpoint) {
        this.seq = seq;
        this.kind = kind;
        this.context = context;
        this.site = site;
        this.k = k;
        this.occurrence = occurrence;
        this.endpoint = endpoint;
    }

    public static ScheduleEvent of(long seq, Kind kind, String context,
                                   String site, int k, String occurrence) {
        return of(seq, kind, context, site, k, occurrence, "");
    }

    public static ScheduleEvent of(long seq, Kind kind, String context,
                                   String site, int k, String occurrence,
                                   String endpoint) {
        if (seq < 0L) {
            throw new IllegalArgumentException("seq must be >= 0: " + seq);
        }
        if (k < 0) {
            throw new IllegalArgumentException("k must be >= 0: " + k);
        }
        return new ScheduleEvent(seq, Fields.required(kind, "kind"),
                context == null ? "" : context,
                Fields.text(site, "site"), k,
                occurrence == null ? "" : occurrence,
                endpoint == null ? "" : endpoint);
    }

    /**
     * What two runs compare an event by: its kind, context and site.
     *
     * <p>Not {@code k}: the k-th event of a key is its position among the
     * events of that key, which is what the order itself states.</p>
     */
    public static String key(Kind kind, String context, String site) {
        return (kind == null ? "" : kind.name()) + "\n"
                + (context == null ? "" : context) + "\n"
                + (site == null ? "" : site);
    }

    public String key() {
        return key(kind, context, site);
    }

    public long seq() {
        return seq;
    }

    public Kind kind() {
        return kind;
    }

    public String context() {
        return context;
    }

    public String site() {
        return site;
    }

    public int k() {
        return k;
    }

    public String occurrence() {
        return occurrence;
    }

    public String endpoint() {
        return endpoint;
    }

    /** One line a report can print: {@code KIND site#k @ c}. */
    public String render() {
        return kind.name() + " " + site + "#" + k + " @ " + context;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof ScheduleEvent)) return false;
        ScheduleEvent other = (ScheduleEvent) value;
        return seq == other.seq && k == other.k && kind == other.kind
                && context.equals(other.context) && site.equals(other.site)
                && occurrence.equals(other.occurrence)
                && endpoint.equals(other.endpoint);
    }

    @Override
    public int hashCode() {
        return Objects.hash(seq, kind, context, site, k, occurrence,
                endpoint);
    }

    @Override
    public String toString() {
        return "ScheduleEvent{" + seq + " " + render() + "}";
    }
}
