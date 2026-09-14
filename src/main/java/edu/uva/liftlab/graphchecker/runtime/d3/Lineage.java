package edu.uva.liftlab.graphchecker.runtime.d3;

import edu.uva.liftlab.graphchecker.d3.contract.LineageHop;
import edu.uva.liftlab.graphchecker.d3.contract.Role;
import java.util.ArrayList;
import java.util.Collections;
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
    /** Counters are window-local: k counts inside the recording window. */
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

    /** One hop of the chain, and whether this run could attribute it. */
    private static final class Frame {
        private final long token;
        private final Role role;
        private final String api;
        private final int k;
        private final boolean lost;

        private Frame(long token, Role role, String api, int k,
                      boolean lost) {
            this.token = token;
            this.role = role;
            this.api = api;
            this.k = k;
            this.lost = lost;
        }

        private LineageHop hop() {
            return LineageHop.of(role, api, k);
        }
    }

    /** One captured lineage, carried with the work that was created in it. */
    public static final class Carried {
        private final List<Frame> frames;
        private final String nodeKey;

        private Carried(List<Frame> frames, String nodeKey) {
            this.frames = frames;
            this.nodeKey = nodeKey;
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
     * <p>{@code k} is taken from a counter keyed by the node, the parent's
     * rendered path, the role and the api -- the four things the hop counts
     * within.  A node this run cannot name still gets its hop, marked lost:
     * the activation ran, and a guessed node is a wrong causal chain.</p>
     */
    public static long push(String nodeKey, Role role, String api) {
        List<Frame> stack = STACK.get();
        String node = Text.safe(nodeKey);
        String scope = node + "\n" + path(stack) + "\n"
                + (role == null ? Role.UNKNOWN : role).name() + "\n"
                + Text.safe(api);
        int k = counter(scope).incrementAndGet();
        long token = TOKENS.getAndIncrement();
        stack.add(new Frame(token, role == null ? Role.UNKNOWN : role,
                Text.safe(api), k, node.isEmpty()));
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

    /** The lineage of the calling thread, as a value work can carry. */
    public static Carried capture(String nodeKey) {
        return new Carried(new ArrayList<Frame>(STACK.get()),
                Text.safe(nodeKey));
    }

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
        long token;
        if (carried instanceof Carried && ((Carried) carried).names()) {
            Carried scope = (Carried) carried;
            stack.clear();
            stack.addAll(scope.frames);
            String node = Text.safe(nodeKey).isEmpty()
                    ? scope.nodeKey() : Text.safe(nodeKey);
            token = push(node, role, api);
        } else {
            token = push(nodeKey, role, api);
        }
        RESTORED.get().put(token, restored);
        return token;
    }

    /** Leaves a restored scope and puts back the thread's own lineage. */
    public static void release(long token) {
        List<Frame> restored = RESTORED.get().remove(token);
        if (restored == null) {
            pop(token);
            return;
        }
        List<Frame> stack = STACK.get();
        stack.clear();
        stack.addAll(restored);
    }

    private static final ThreadLocal<Map<Long, List<Frame>>> RESTORED =
            new ThreadLocal<Map<Long, List<Frame>>>() {
                @Override
                protected Map<Long, List<Frame>> initialValue() {
                    return new java.util.LinkedHashMap<Long, List<Frame>>();
                }
            };

    /** The hops of the calling thread, outermost first. */
    public static List<LineageHop> hops() {
        List<Frame> stack = STACK.get();
        List<LineageHop> hops = new ArrayList<LineageHop>(stack.size());
        for (Frame frame : stack) hops.add(frame.hop());
        return Collections.unmodifiableList(hops);
    }

    /** Whether any hop of the current lineage is unattributable. */
    public static boolean lost() {
        for (Frame frame : STACK.get()) {
            if (frame.lost) return true;
        }
        return false;
    }

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

    /** The k of the innermost frame, or 0. */
    public static int k() {
        List<Frame> stack = STACK.get();
        return stack.isEmpty() ? 0 : stack.get(stack.size() - 1).k;
    }

    /** The rendered lineage path, {@code ""} at a root. */
    public static String path() {
        return path(STACK.get());
    }

    /**
     * The next window-local ordinal of one counted thing.
     *
     * <p>Daemon roots have no parent to count within, so their k is a raw
     * window ordinal: IDENTITY-V2 §0 rules that acceptable because the
     * closure makes it harmless -- a tick the anchor never reads is outside
     * the closure, and one it does read is identified by the version it
     * wrote, not by k.</p>
     */
    public static int windowOrdinal(String subject) {
        return counter("WINDOW\n" + Text.safe(subject)).incrementAndGet();
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

    private static String path(List<Frame> stack) {
        if (stack.isEmpty()) return "";
        StringBuilder rendered = new StringBuilder();
        for (Frame frame : stack) {
            if (rendered.length() > 0) rendered.append('/');
            rendered.append(frame.hop().render());
        }
        return rendered.toString();
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
    }
}
