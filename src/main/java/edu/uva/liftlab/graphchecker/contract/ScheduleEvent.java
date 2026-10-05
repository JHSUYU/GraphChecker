package edu.uva.liftlab.graphchecker.contract;

/**
 * One scheduling event {@code (kind, c, site, k)}; a session's schedule
 * ({@link SessionDir#SCHEDULE}) is their order, and a focused replay is held
 * to its source session's prefix.  {@code c} is node plus rendered
 * {@link CausalContext}, {@code k} the k-th event of {@code (kind, c, site)}:
 * no thread id, no time.  {@code occurrence} (open region id, or {@code ""})
 * is not part of the key; it is where a prefix is cut.
 */
public final class ScheduleEvent extends Value {
    /**
     * The mark of a run cut at its witness ({@code RowCodec
     * #writeScheduleMark}): its log orders nothing after the witness, so a
     * replay held to it lets no WAKE its order never made go before the
     * order has drained ({@code runtime.ScheduleLog}).
     */
    public static final String WITNESS = "WITNESS";

    /**
     * The mark stating which invocation of a parameterized workload test the
     * run is ({@code RowCodec#writeScheduleInvocation}): a replay held to a
     * run that ran another is refused ({@code runtime.ScheduleLog
     * #invocation}).
     */
    public static final String INVOCATION = "INVOCATION";

    /**
     * The mark of one taker completing a startup step an adapter names
     * ({@code RowCodec#writeScheduleStartup}: {@code step}, {@code who}),
     * in completion order: a replay holds a taker at the step until those
     * marked before it there completed it, whatever either run's window
     * ({@code runtime.StartupOrder}).
     */
    public static final String STARTUP = "STARTUP";

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
         * A timed wait's TIMEOUT ended it (a new service-loop turn).  A wait
         * a signal ended is no event: the notifier's events order it.
         */
        WAKE,
        /**
         * A daemon tick the window saw begin has ended: its writes are
         * visible from here.  Needed because WAKE orders only a tick's start,
         * not the writes it made.
         */
        END,
        /**
         * A timed wait the workload's interrupt ended.  Never held (the
         * interrupter's events order it) and never turned into a timeout in
         * the replay; only a WAKE ends a held wait by virtual time.
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
     * The producer endpoint a SEND minted (its receiver's ANCHOR), or the
     * one a RECV took into the receiver's own context, which it does not
     * anchor (a DataTransfer op a DataNode's turn received), else "".
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

    /** What two runs compare an event by: kind, context, site (not k). */
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

    /**
     * The message a RECV took in -- the producer endpoint its context is
     * anchored on, else the one it names -- or "" (any other event).
     */
    public String received() {
        if (kind != Kind.RECV) return "";
        try {
            ContextShape.Stance stance = ContextShape.Stance.ofSend(context);
            if (stance != null
                    && stance.context() instanceof CausalContext.Anchor) {
                return ((CausalContext.Anchor) stance.context())
                        .producerEndpointId();
            }
        } catch (IllegalArgumentException unnamed) {
            // A context no CausalContext spells is anchored on nothing.
        }
        return endpoint;
    }

    /** One line a report can print: {@code KIND site#k @ c}. */
    public String render() {
        return kind.name() + " " + site + "#" + k + " @ " + context;
    }

    @Override
    Object[] parts() {
        return new Object[] {seq, kind, context, site, k, occurrence,
                endpoint};
    }

    @Override
    public String toString() {
        return "ScheduleEvent{" + seq + " " + render() + "}";
    }
}
