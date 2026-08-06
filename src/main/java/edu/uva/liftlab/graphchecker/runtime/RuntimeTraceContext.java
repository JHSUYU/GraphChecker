package edu.uva.liftlab.graphchecker.runtime;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Trace-local causal context for runtime region discovery.
 *
 * <p>The identifiers produced here are evidence inside one concrete trace;
 * they are deliberately not replay identities.  A local owner partitions
 * node/service-local state, a lane preserves same-thread program order, and a
 * span identifies one root activation.  Soot-inserted call hooks capture
 * parent context at thread/task submission.  RPC hooks add a remote parent
 * without changing the application payload.</p>
 */
final class RuntimeTraceContext {
    private static final Object LOCK = new Object();
    private static final AtomicLong IDS = new AtomicLong(1L);
    private static final IdentityHashMap<Object, Owner> OWNERS =
            new IdentityHashMap<>();
    private static final IdentityHashMap<Object, Seed> ASYNC_SEEDS =
            new IdentityHashMap<>();
    private static final Map<String, Deque<RpcParent>> RPC_SENDS =
            new LinkedHashMap<>();
    private static final ThreadLocal<State> CURRENT =
            ThreadLocal.withInitial(RuntimeTraceContext::initialState);

    private RuntimeTraceContext() {
    }

    static long registerOwner(Object owner, String label) {
        if (owner == null) return 0L;
        synchronized (LOCK) {
            Owner existing = OWNERS.get(owner);
            if (existing != null) return existing.id;
            Owner created = new Owner(nextId(), safe(label));
            OWNERS.put(owner, created);
            return created.id;
        }
    }

    /** Captures the current owner/span for a Thread, Runnable, or Callable. */
    static void captureAsync(Object carrier) {
        if (carrier == null) return;
        State state = CURRENT.get();
        View view = state.view();
        synchronized (LOCK) {
            ASYNC_SEEDS.put(carrier, new Seed(view.ownerId,
                    view.spanId, view.laneId));
        }
    }

    /** Starts one root activation; nested methods reuse its span. */
    static View enterRoot(Object receiver) {
        State state = CURRENT.get();
        Seed seed = takeSeed(Thread.currentThread());
        if (seed == null) seed = takeSeed(receiver);

        long ownerId = seed == null ? state.ownerId : seed.ownerId;
        long parentSpanId = seed == null ? state.currentSpan() : seed.parentSpanId;
        if (receiver != null && seed == null
                && (ownerId == 0L || ownerId == state.fallbackOwnerId)) {
            ownerId = registerOwner(receiver, receiver.getClass().getName());
        }
        if (ownerId == 0L) {
            ownerId = state.fallbackOwnerId;
        }
        if (seed != null || state.laneId == 0L) {
            state.laneId = nextId();
        }
        long spanId = nextId();
        // A receive scope belongs to the server lane until the next receive
        // replaces it.  Do not let an adapter/parser root consume it before
        // the actual handler root starts.
        long remoteParentSpanId = state.pendingRemoteParentSpanId;
        Frame frame = new Frame(spanId, parentSpanId, remoteParentSpanId,
                state.ownerId, ownerId);
        state.ownerId = ownerId;
        state.frames.push(frame);
        return state.view();
    }

    static void exitRoot(long spanId) {
        State state = CURRENT.get();
        Frame frame = state.frames.peek();
        if (frame == null || frame.spanId != spanId) return;
        state.frames.pop();
        state.ownerId = frame.previousOwnerId;
    }

    static View current() {
        return CURRENT.get().view();
    }

    /**
     * Registers an RPC endpoint.  SEND stores the caller span; RECEIVE binds
     * the matching caller as remote parent and may establish the local owner.
     */
    static View rpc(String direction, String transport, String correlationId,
                    Object localOwner) {
        State state = CURRENT.get();
        if (localOwner != null) {
            state.ownerId = registerOwner(localOwner,
                    localOwner.getClass().getName());
            Frame frame = state.frames.peek();
            if (frame != null) frame.ownerId = state.ownerId;
        }
        String key = safe(transport) + "\n" + safe(correlationId);
        if ("SEND".equalsIgnoreCase(safe(direction))) {
            View view = state.view();
            synchronized (LOCK) {
                RPC_SENDS.computeIfAbsent(key, ignored -> new ArrayDeque<>())
                        .addLast(new RpcParent(view.ownerId, view.laneId,
                                view.spanId));
            }
            return view;
        }
        if ("RECEIVE".equalsIgnoreCase(safe(direction))) {
            RpcParent parent = null;
            synchronized (LOCK) {
                Deque<RpcParent> parents = RPC_SENDS.get(key);
                if (parents != null) {
                    parent = parents.pollFirst();
                    if (parents.isEmpty()) RPC_SENDS.remove(key);
                }
            }
            if (parent != null) {
                state.pendingRemoteParentSpanId = parent.spanId;
                Frame frame = state.frames.peek();
                if (frame != null) {
                    frame.remoteParentSpanId = parent.spanId;
                }
            }
        }
        return state.view();
    }

    static void resetForTests() {
        synchronized (LOCK) {
            OWNERS.clear();
            ASYNC_SEEDS.clear();
            RPC_SENDS.clear();
        }
        CURRENT.remove();
        IDS.set(1L);
    }

    private static Seed takeSeed(Object carrier) {
        if (carrier == null) return null;
        synchronized (LOCK) {
            return ASYNC_SEEDS.remove(carrier);
        }
    }

    private static State initialState() {
        long laneId = nextId();
        return new State(laneId, nextId());
    }

    private static long nextId() {
        return IDS.getAndIncrement();
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }

    static final class View {
        final long ownerId;
        final long laneId;
        final long spanId;
        final long parentSpanId;
        final long remoteParentSpanId;

        private View(long ownerId, long laneId, long spanId,
                     long parentSpanId, long remoteParentSpanId) {
            this.ownerId = ownerId;
            this.laneId = laneId;
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
        }
    }

    private static final class State {
        private long laneId;
        private final long fallbackOwnerId;
        private long ownerId;
        private long pendingRemoteParentSpanId;
        private final Deque<Frame> frames = new ArrayDeque<>();

        private State(long laneId, long fallbackOwnerId) {
            this.laneId = laneId;
            this.fallbackOwnerId = fallbackOwnerId;
            this.ownerId = fallbackOwnerId;
        }

        private long currentSpan() {
            Frame frame = frames.peek();
            return frame == null ? 0L : frame.spanId;
        }

        private View view() {
            Frame frame = frames.peek();
            return new View(frame == null ? ownerId : frame.ownerId,
                    laneId, frame == null ? 0L : frame.spanId,
                    frame == null ? 0L : frame.parentSpanId,
                    frame == null ? pendingRemoteParentSpanId
                            : frame.remoteParentSpanId);
        }
    }

    private static final class Frame {
        private final long spanId;
        private final long parentSpanId;
        private long remoteParentSpanId;
        private final long previousOwnerId;
        private long ownerId;

        private Frame(long spanId, long parentSpanId,
                      long remoteParentSpanId, long previousOwnerId,
                      long ownerId) {
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.previousOwnerId = previousOwnerId;
            this.ownerId = ownerId;
        }
    }

    private static final class Owner {
        private final long id;
        @SuppressWarnings("unused")
        private final String label;

        private Owner(long id, String label) {
            this.id = id;
            this.label = label;
        }
    }

    private static final class Seed {
        private final long ownerId;
        private final long parentSpanId;
        @SuppressWarnings("unused")
        private final long parentLaneId;

        private Seed(long ownerId, long parentSpanId, long parentLaneId) {
            this.ownerId = ownerId;
            this.parentSpanId = parentSpanId;
            this.parentLaneId = parentLaneId;
        }
    }

    private static final class RpcParent {
        @SuppressWarnings("unused")
        private final long ownerId;
        @SuppressWarnings("unused")
        private final long laneId;
        private final long spanId;

        private RpcParent(long ownerId, long laneId, long spanId) {
            this.ownerId = ownerId;
            this.laneId = laneId;
            this.spanId = spanId;
        }
    }
}
