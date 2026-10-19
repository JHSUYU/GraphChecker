package edu.uva.liftlab.graphchecker.contract;

public final class ScheduleEvent extends Value {
    public static final String WITNESS = "WITNESS";

    public static final String INVOCATION = "INVOCATION";

    public static final String STARTUP = "STARTUP";

    public enum Kind {
        START,
        CLAIM,
        SEND,
        WRITE,
        READ,
        RECV,
        WAKE,
        END,
        INTERRUPT,
        PUBLISH
    }

    private final long seq;
    private final Kind kind;
    private final String context;
    private final String site;
    private final int k;
    private final String occurrence;
    private final String endpoint;
    private final long vmEvent;

    private ScheduleEvent(long seq, Kind kind, String context, String site,
                          int k, String occurrence, String endpoint,
                          long vmEvent) {
        this.seq = seq;
        this.kind = kind;
        this.context = context;
        this.site = site;
        this.k = k;
        this.occurrence = occurrence;
        this.endpoint = endpoint;
        this.vmEvent = vmEvent;
    }

    public static ScheduleEvent of(long seq, Kind kind, String context,
                                   String site, int k, String occurrence,
                                   String endpoint) {
        return of(seq, kind, context, site, k, occurrence, endpoint, 0L);
    }

    public static ScheduleEvent of(long seq, Kind kind, String context,
                                   String site, int k, String occurrence,
                                   String endpoint, long vmEvent) {
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
                endpoint == null ? "" : endpoint, Math.max(0L, vmEvent));
    }

    public static String written(String transport, String location) {
        return (transport == null ? "" : transport) + ":"
                + (location == null ? "" : location);
    }

    public static String published(String transport, String path,
                                   long version) {
        return written(transport, path) + "@" + version;
    }

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

    public long vmEvent() {
        return vmEvent;
    }

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
        }
        return endpoint;
    }

    public String render() {
        return kind.name() + " " + site + "#" + k + " @ " + context;
    }

    @Override
    Object[] parts() {
        return new Object[] {seq, kind, context, site, k, occurrence,
                endpoint, vmEvent};
    }

    @Override
    public String toString() {
        return "ScheduleEvent{" + seq + " " + render() + "}";
    }
}
