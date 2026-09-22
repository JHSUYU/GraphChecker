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
 *
 * <p>{@code signalled} says how a WAKE's wait ended: by a notify, a signal or
 * an unpark ({@code true}), or by its timeout.  Not part of the key either --
 * it is the same turn of the same loop either way -- but what a replay held
 * to the prefix must reproduce: virtual time stands in for the CLOCK, never
 * for the notifier, so a turn the recording was woken into is not taken
 * before something wakes it.</p>
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
        /** A timed wait returns: the next turn of a service loop begins. */
        WAKE
    }

    private final long seq;
    private final Kind kind;
    private final String context;
    private final String site;
    private final int k;
    private final String occurrence;
    private final boolean signalled;

    private ScheduleEvent(long seq, Kind kind, String context, String site,
                          int k, String occurrence, boolean signalled) {
        this.seq = seq;
        this.kind = kind;
        this.context = context;
        this.site = site;
        this.k = k;
        this.occurrence = occurrence;
        this.signalled = signalled;
    }

    public static ScheduleEvent of(long seq, Kind kind, String context,
                                   String site, int k, String occurrence) {
        return of(seq, kind, context, site, k, occurrence, false);
    }

    /**
     * An event whose wait ended by a signal: only a WAKE is ever signalled,
     * and a {@code true} on any other kind is a caller's error.
     */
    public static ScheduleEvent of(long seq, Kind kind, String context,
                                   String site, int k, String occurrence,
                                   boolean signalled) {
        if (signalled && kind != Kind.WAKE) {
            throw new IllegalArgumentException(
                    "only a WAKE is signalled: " + kind);
        }
        if (seq < 0L) {
            throw new IllegalArgumentException("seq must be >= 0: " + seq);
        }
        if (k < 0) {
            throw new IllegalArgumentException("k must be >= 0: " + k);
        }
        return new ScheduleEvent(seq, Fields.required(kind, "kind"),
                context == null ? "" : context,
                Fields.text(site, "site"), k,
                occurrence == null ? "" : occurrence, signalled);
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

    /** Whether this WAKE's wait ended by a signal rather than its timeout. */
    public boolean signalled() {
        return signalled;
    }

    /** One line a report can print: {@code KIND site#k @ c}. */
    public String render() {
        return kind.name() + " " + site + "#" + k
                + (signalled ? " (signalled)" : "") + " @ " + context;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof ScheduleEvent)) return false;
        ScheduleEvent other = (ScheduleEvent) value;
        return seq == other.seq && k == other.k && kind == other.kind
                && context.equals(other.context) && site.equals(other.site)
                && occurrence.equals(other.occurrence)
                && signalled == other.signalled;
    }

    @Override
    public int hashCode() {
        return Objects.hash(seq, kind, context, site, k, occurrence,
                signalled);
    }

    @Override
    public String toString() {
        return "ScheduleEvent{" + seq + " " + render() + "}";
    }
}
