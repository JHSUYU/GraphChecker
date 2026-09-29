package edu.uva.liftlab.graphchecker.runtime;

/**
 * THE message doors a system's transports call, whatever the system: a
 * request or a response leaves (outbound) carrying the sender's GraphChecker
 * context and the symbolic values it exports, and arrives (inbound) where the
 * receiver installs them for as long as it serves that message.  Plus the
 * workload's side of attribution: nodes and their aliases, request scopes, the
 * recorded window, daemon ticks and scopes carried across a queue.
 *
 * <p>A transport keeps only what is its own: where its header travels (a
 * Hadoop RPC header field, an HTTP header), how it names an exchange (its
 * correlation id) and which half a message is.  The Hadoop shim ({@code
 * org.apache.hadoop.ipc.CausynthMessagePropagation}: IPC and the SASL
 * exchange) and the Solr trees (HTTP) call this class.</p>
 *
 * <p>One inbound exchange per thread: installing the next one ends the one
 * before it, and so does an outbound message, whose sender is no longer
 * serving what it received.</p>
 */
public final class MessageDoors {
    public static final String REQUEST = "REQUEST";
    public static final String RESPONSE = "RESPONSE";

    private static final ThreadLocal<Inbound> CURRENT = new ThreadLocal<>();

    private MessageDoors() {
    }

    /**
     * The request scope of the calling thread, as a value the work it is
     * creating can carry to whatever thread later sends it.
     */
    public static Object captureScope() {
        return CausynthTraceRecorder.captureScope();
    }

    /**
     * One message leaves: its trace context and the symbolic values the
     * sender exported, to travel with it.
     *
     * @param scope the scope the work carries ({@link #captureScope}), or
     *              {@code null} for the calling thread's own
     */
    public static Outbound outbound(String transport, String correlationId,
                                    String attemptId, String half,
                                    Object localOwner, Object scope) {
        String trace = CausynthTraceRecorder.outboundExchange(transport,
                correlationId, attemptId, half, localOwner, scope);
        String symbolic = SymbolicMessageEnvelope.takeOutbound();
        return trace.isEmpty() && symbolic.isEmpty() ? Outbound.EMPTY
                : new Outbound(correlationId, attemptId, trace, symbolic);
    }

    /**
     * One message arrives: ends the exchange the thread was serving and
     * installs this one.
     *
     * @param keepSymbolic keep the values earlier messages of the same
     *                     multi-message exchange carried (a SASL handshake)
     */
    public static Inbound inbound(String trace, String symbolic,
                                  String transport, String correlationId,
                                  String attemptId, String half,
                                  Object localOwner, boolean keepSymbolic) {
        endInbound(!keepSymbolic);
        if (!keepSymbolic) {
            SymbolicMessageEnvelope.clearInbound();
        }
        boolean hasTrace = trace != null && !trace.isEmpty();
        boolean hasSymbolic = symbolic != null && !symbolic.isEmpty();
        if (!hasTrace && !hasSymbolic) {
            return Inbound.EMPTY;
        }
        long token = hasTrace
                ? CausynthTraceRecorder.inboundExchange(trace, transport,
                correlationId, attemptId, half, localOwner)
                : 0L;
        if (hasSymbolic) {
            SymbolicMessageEnvelope.installInbound(symbolic);
        }
        Inbound scope = new Inbound(token, correlationId, attemptId, half);
        CURRENT.set(scope);
        return scope;
    }

    /** Ends {@code scope} if the thread still serves it. */
    public static void endInbound(Inbound scope) {
        if (scope == null || scope == Inbound.EMPTY || CURRENT.get() != scope) {
            // Already ended by the next message's install: not an error.
            return;
        }
        endInbound();
    }

    /** Ends whatever exchange the thread serves. */
    public static void endInbound() {
        endInbound(true);
    }

    private static void endInbound(boolean clearSymbolic) {
        Inbound scope = CURRENT.get();
        if (scope == null) {
            return;
        }
        CURRENT.remove();
        if (clearSymbolic) {
            SymbolicMessageEnvelope.clearInbound();
        }
        if (scope.token > 0L) {
            CausynthTraceRecorder.endInboundExchange(scope.token);
        }
    }

    /** The exchange the thread serves, or {@code null}. */
    public static Inbound current() {
        return CURRENT.get();
    }

    /**
     * Sets the served exchange aside, unended, while the thread runs an
     * exchange of its own as a client; {@link #restore} gives it back.
     */
    public static Inbound setAside() {
        Inbound serving = CURRENT.get();
        if (serving != null) {
            CURRENT.remove();
        }
        return serving;
    }

    /** Gives back what {@link #setAside} took. */
    public static void restore(Inbound serving) {
        if (serving != null) {
            CURRENT.set(serving);
        }
    }

    /**
     * Enters the scope a queued unit of work carried from where it was made:
     * the dequeue half of a queue handoff.
     */
    public static long enterCarriedScope(Object scope, String role,
                                         String api) {
        return CausynthTraceRecorder.enterCarriedScope(scope, role, api);
    }

    /** Leaves the scope {@link #enterCarriedScope} entered. */
    public static void exitCarriedScope(long token) {
        CausynthTraceRecorder.exitCarriedScope(token);
    }

    /** Opens one daemon tick as a root of its own: a service-loop turn. */
    public static long beginTick(Object owner, String role) {
        return CausynthTraceRecorder.beginDaemonTick(owner, role);
    }

    /** Closes the tick {@link #beginTick} opened. */
    public static void endTick(long token) {
        CausynthTraceRecorder.endDaemonTick(token);
    }

    /** Opens the recorded window: the workload's recording boundary. */
    public static void startRecording() {
        CausynthTraceRecorder.startRecording();
    }

    /**
     * Whether this run is a concolic replay: a world the engine chose, where a
     * workload's check of the RECORDING's world is not the workload's to make.
     */
    public static boolean replaying() {
        return CausynthTraceRecorder.replaying();
    }

    public static void registerSource(Object anchor, String kind, String role,
                                      String sourceId, long epoch) {
        CausynthTraceRecorder.registerSource(anchor, kind, role, sourceId,
                epoch);
    }

    public static void registerSourceAlias(Object alias, Object anchor) {
        CausynthTraceRecorder.registerSourceAlias(alias, anchor);
    }

    /**
     * Registers one node: its anchor as the source, and every object the node
     * runs its work through as the same node -- what the attribution rule
     * finds on a thread's frames.  A null or repeated alias is skipped.
     */
    public static void registerNode(Object anchor, String kind, String role,
                                    String sourceId, Object... aliases) {
        registerSource(anchor, kind, role, sourceId, 0L);
        if (aliases == null) {
            return;
        }
        for (Object alias : aliases) {
            if (alias == null || alias == anchor) {
                continue;
            }
            registerSourceAlias(alias, anchor);
        }
    }

    public static void restartSource(Object anchor, String kind, String role,
                                     String sourceId, long epoch) {
        CausynthTraceRecorder.restartSource(anchor, kind, role, sourceId,
                epoch);
    }

    public static long beginRequest(Object source, String api) {
        endInbound();
        return CausynthTraceRecorder.beginSourceRequest(source, api);
    }

    public static void endRequest(long request, String api) {
        endInbound();
        CausynthTraceRecorder.endSourceRequest(request, api);
    }

    /**
     * One client operation the workload itself makes, a request root of its
     * own ({@link CausynthTraceRecorder#beginWorkloadCall}); 0, and nothing
     * begun, on a node's own thread.
     */
    public static long beginWorkloadCall(String api) {
        return CausynthTraceRecorder.beginWorkloadCall(api);
    }

    public static void endWorkloadCall(long call, String api) {
        if (call != 0L) endRequest(call, api);
    }

    /** The outbound of a message that carries nothing. */
    public static Outbound outboundNone() {
        return Outbound.EMPTY;
    }

    /** What one outbound message carries. */
    public static final class Outbound {
        static final Outbound EMPTY = new Outbound("", "", "", "");
        public final String correlationId;
        public final String attemptId;
        public final String trace;
        public final String symbolic;

        private Outbound(String correlationId, String attemptId, String trace,
                         String symbolic) {
            this.correlationId = correlationId;
            this.attemptId = attemptId;
            this.trace = trace;
            this.symbolic = symbolic == null ? "" : symbolic;
        }

        public boolean active() {
            return !trace.isEmpty() || !symbolic.isEmpty();
        }
    }

    /** One installed inbound exchange. */
    public static final class Inbound {
        static final Inbound EMPTY = new Inbound(0L, "", "", "");
        private final long token;
        public final String correlationId;
        public final String attemptId;
        public final String half;

        private Inbound(long token, String correlationId, String attemptId,
                        String half) {
            this.token = token;
            this.correlationId = correlationId;
            this.attemptId = attemptId;
            this.half = half;
        }
    }
}
