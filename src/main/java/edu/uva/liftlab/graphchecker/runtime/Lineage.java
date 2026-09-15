package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Role;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;

/**
 * The control lineage of the running activation: the chain of scope frames
 * it entered under, each one a {@code (role, api, k)} hop.
 *
 * <p>IDENTITY-V2 §1.  A lineage is a TYPE and the per-hop {@code k}
 * separates two instances of it; {@code k} counts within the PARENT hop, so
 * two callers of one api never share a count and two activations never
 * share an address.  Roles are scope KINDS -- never thread names -- and a
 * hop nothing can attribute is pushed all the same, marked lost, because
 * "the value arrived under a scope this run cannot name" is a fact the row
 * has to state rather than a reason to publish no row.</p>
 *
 * <p>The stack is inheritable so a thread created inside a scope starts
 * where its creator was, exactly as the request scope does; the explicit
 * {@link #capture()} / {@link #restore} pair is what carries a scope to a
 * pool thread that was created before it -- {@code Thread.start}, an
 * executor submission, and the IPC {@code Server.Call} queue, none of which
 * an {@code InheritableThreadLocal} reaches.</p>
 */
public final class Lineage {
    /** k for the root hops of one (node, role, api) in this window. */
    private static final Map<String, AtomicInteger> COUNTERS =
            new ConcurrentHashMap<String, AtomicInteger>();
    private static final AtomicLong TOKENS = new AtomicLong(1L);
    private static final InheritableThreadLocal<List<Frame>> STACK =
            new InheritableThreadLocal<List<Frame>>() {
                @Override
                protected List<Frame> initialValue() {
                    return new ArrayList<Frame>();
                }

                @Override
                protected List<Frame> childValue(List<Frame> parent) {
                    // A thread created inside a scope starts inside it.
                    return parent == null ? new ArrayList<Frame>()
                            : new ArrayList<Frame>(parent);
                }
            };

    private Lineage() {
    }

    /** One hop of the chain: its scope kind, and what opened it. */
    private static final class Frame {
        private final long token;
        private final Role role;
        /** The window index of this hop, which only a ROOT hop carries. */
        private final int k;
        /** The producer endpoint whose message opened this scope, or "". */
        private String anchor = "";
        /** The transport site that message crossed, or "". */
        private String rpcSite = "";

        private Frame(long token, Role role, int k) {
            this.token = token;
            this.role = role;
            this.k = k;
        }
    }

    /** One captured lineage, carried with the work that was created in it. */
    public static final class Carried {
        private final List<Frame> frames;
        private final String nodeKey;
        /** The endpoint of the submission that carried it, or "". */
        private final String startedBy;

        private Carried(List<Frame> frames, String nodeKey,
                        String startedBy) {
            this.frames = frames;
            this.nodeKey = nodeKey;
            this.startedBy = startedBy;
        }

        /** The endpoint id of the start/submit that carried this. */
        public String startedBy() {
            return startedBy;
        }

        /** Whether this carries a lineage at all. */
        public boolean names() {
            return !frames.isEmpty();
        }

        public String nodeKey() {
            return nodeKey;
        }
    }

    /**
     * Enters one scope frame and returns the token that leaves it.
     *
     * <p>{@code k} counts the ROOT hops of one (node, role, api) inside the
     * recording window, because that k is the only one any address reads
     * ({@link #rootWindowIndex}, the window index of a
     * {@link edu.uva.liftlab.graphchecker.contract.CausalContext.Root}).  A
     * hop entered inside another counts nothing: IDENTITY-V3 SS4 replaced the
     * rendered lineage list with the causal anchor, so nothing asks a nested
     * hop which one it is.  A node this run cannot name still gets its hop,
     * marked lost: the activation ran, and a guessed node is a wrong causal
     * chain.</p>
     */
    public static long push(String nodeKey, Role role, String api) {
        List<Frame> stack = STACK.get();
        String node = Text.safe(nodeKey);
        Role kind = role == null ? Role.UNKNOWN : role;
        int k = stack.isEmpty()
                ? counter(node + "\n" + kind.name() + "\n"
                        + Text.safe(api)).incrementAndGet()
                : 0;
        long token = TOKENS.getAndIncrement();
        stack.add(new Frame(token, kind, k));
        return token;
    }

    /**
     * Leaves the frame {@code token} opened, and every frame opened inside
     * it that a non-local exit left behind.
     */
    public static void pop(long token) {
        List<Frame> stack = STACK.get();
        for (int i = stack.size() - 1; i >= 0; i--) {
            if (stack.get(i).token != token) continue;
            while (stack.size() > i) stack.remove(stack.size() - 1);
            return;
        }
    }

    /** The same, naming the endpoint of the submission that carries it. */
    public static Carried capture(String nodeKey, String startedByEndpoint) {
        return new Carried(new ArrayList<Frame>(STACK.get()),
                Text.safe(nodeKey), Text.safe(startedByEndpoint));
    }

    /** The endpoint that started the work running on this thread, or "". */
    public static String startedBy() {
        String started = STARTED_BY.get();
        return started == null ? "" : started;
    }

    /** States which submission's frame this thread inherited. */
    public static void startedBy(String endpointId) {
        STARTED_BY.set(Text.safe(endpointId));
    }

    private static final ThreadLocal<String> STARTED_BY =
            new ThreadLocal<String>();

    /**
     * Installs a carried lineage and opens one hop inside it.
     *
     * <p>This is the dequeue half of every queue that outlives its
     * enqueueing thread: the IPC {@code Server.Call} queue, an executor's
     * work queue, a thread the workload started.  Returns the token that
     * both closes the hop and restores the thread's own lineage.</p>
     */
    public static long restore(Object carried, String nodeKey, Role role,
                               String api) {
        List<Frame> stack = STACK.get();
        final List<Frame> restored = new ArrayList<Frame>(stack);
        final String startedBy = startedBy();
        long token;
        if (carried instanceof Carried && ((Carried) carried).names()) {
            Carried scope = (Carried) carried;
            if (!scope.startedBy().isEmpty()) startedBy(scope.startedBy());
            stack.clear();
            stack.addAll(scope.frames);
            String node = Text.safe(nodeKey).isEmpty()
                    ? scope.nodeKey() : Text.safe(nodeKey);
            token = push(node, role, api);
        } else {
            token = push(nodeKey, role, api);
        }
        RESTORED.get().put(token, restored);
        STARTERS.get().put(token, startedBy);
        return token;
    }

    /** Leaves a restored scope and puts back the thread's own lineage. */
    public static void release(long token) {
        // The submission this thread ran under is the restored scope's, and
        // it ends with it: a pool thread that kept the last task's starter
        // would hand the next root an anchor that started something else.
        String starter = STARTERS.get().remove(token);
        if (starter != null) startedBy(starter);
        List<Frame> restored = RESTORED.get().remove(token);
        if (restored == null) {
            pop(token);
            return;
        }
        List<Frame> stack = STACK.get();
        stack.clear();
        stack.addAll(restored);
    }

    /** The starter each restored scope displaced, by its token. */
    private static final ThreadLocal<Map<Long, String>> STARTERS =
            new ThreadLocal<Map<Long, String>>() {
                @Override
                protected Map<Long, String> initialValue() {
                    return new java.util.LinkedHashMap<Long, String>();
                }
            };

    private static final ThreadLocal<Map<Long, List<Frame>>> RESTORED =
            new ThreadLocal<Map<Long, List<Frame>>>() {
                @Override
                protected Map<Long, List<Frame>> initialValue() {
                    return new java.util.LinkedHashMap<Long, List<Frame>>();
                }
            };

    /** Whether the calling thread is inside any scope frame at all. */
    public static boolean named() {
        return !STACK.get().isEmpty();
    }

    /** The role of the innermost frame, or {@link Role#UNKNOWN}. */
    public static Role role() {
        List<Frame> stack = STACK.get();
        return stack.isEmpty() ? Role.UNKNOWN
                : stack.get(stack.size() - 1).role;
    }

    /**
     * States which message opened the innermost scope.
     *
     * <p>IDENTITY-V3: the causal context of everything inside this scope is
     * that producer's endpoint, which carries the producer's own occurrence
     * and where in it the export was -- recursively, all the way back to a
     * workload action or a tick.</p>
     */
    public static void anchor(String producerEndpointId, String rpcSite) {
        List<Frame> stack = STACK.get();
        if (stack.isEmpty()) return;
        Frame frame = stack.get(stack.size() - 1);
        frame.anchor = Text.safe(producerEndpointId);
        frame.rpcSite = Text.safe(rpcSite);
    }

    /** The producer endpoint of the message that opened this scope, or "". */
    public static String anchor() {
        List<Frame> stack = STACK.get();
        for (int i = stack.size() - 1; i >= 0; i--) {
            if (!stack.get(i).anchor.isEmpty()) return stack.get(i).anchor;
        }
        return "";
    }

    /** The transport site of that message, or "". */
    public static String rpcSite() {
        List<Frame> stack = STACK.get();
        for (int i = stack.size() - 1; i >= 0; i--) {
            if (!stack.get(i).anchor.isEmpty()) return stack.get(i).rpcSite;
        }
        return "";
    }

    /** The role of the OUTERMOST frame: the root this scope descends from. */
    public static Role rootRole() {
        List<Frame> stack = STACK.get();
        return stack.isEmpty() ? Role.UNKNOWN : stack.get(0).role;
    }

    /** The window index of that root, or 0. */
    public static int rootWindowIndex() {
        List<Frame> stack = STACK.get();
        return stack.isEmpty() ? 0 : stack.get(0).k;
    }

    /** Opens the recording window: k counts from here, in every replay. */
    public static void openWindow() {
        COUNTERS.clear();
    }

    private static AtomicInteger counter(String scope) {
        AtomicInteger counter = COUNTERS.get(scope);
        if (counter != null) return counter;
        AtomicInteger fresh = new AtomicInteger();
        AtomicInteger raced = COUNTERS.putIfAbsent(scope, fresh);
        return raced == null ? fresh : raced;
    }

    /**
     * The role this name spells, or {@link Role#UNKNOWN}.
     *
     * <p>Here rather than on the contract enum because the name comes from
     * a workload string -- a transport, a daemon's declared role -- and an
     * unknown one is a scope kind this build does not model, not a
     * malformed contract value.</p>
     */
    public static Role roleOf(String name) {
        String value = Text.safe(name).toUpperCase(java.util.Locale.ROOT);
        for (Role role : Role.values()) {
            if (role.name().equals(value)) return role;
        }
        return Role.UNKNOWN;
    }

    /** Test hook: one window, one thread, nothing carried over. */
    public static void resetForTests() {
        COUNTERS.clear();
        STACK.remove();
        RESTORED.remove();
        STARTERS.remove();
        STARTED_BY.remove();
    }
}
