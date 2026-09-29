package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Role;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;

/**
 * The control lineage of the running activation: the chain of scope frames
 * it entered under, each one a {@code (role, api, k)} hop (IDENTITY-V2 §1).
 *
 * <p>Roles are scope KINDS, never thread names.  A hop nothing can
 * attribute is still pushed, marked lost: the row states it.</p>
 *
 * <p>The stack is inheritable, so a new thread starts in its creator's
 * scope, a pool's own worker excepted ({@link PoolWorkers});
 * {@link #capture()} / {@link #restore} carry a scope to a pool thread
 * (executor, IPC {@code Server.Call} queue), which an
 * {@code InheritableThreadLocal} does not reach.</p>
 */
public final class Lineage {
    /** k for the root hops of one (window, node, role, api). */
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
                    return parent == null || PoolWorkers.constructing()
                            ? new ArrayList<Frame>()
                            : new ArrayList<Frame>(parent);
                }
            };

    private Lineage() {
    }

    /** One hop of the chain: its scope kind, and what opened it. */
    private static final class Frame {
        private final long token;
        private final Role role;
        /** The api k was counted under, or "" (IDENTITY-V3 §1). */
        private final String api;
        /** The window index of this hop, which only a ROOT hop carries. */
        private final int k;
        /** Whether this hop is a root: nothing opened it but the node. */
        private final boolean root;
        /** Whether this root is a TURN of a loop ({@link #pushRoot}). */
        private final boolean turn;
        /** The window this hop was entered in ({@link RecordingWindow}). */
        private final int window;
        /** The producer endpoint whose message opened this scope, or "". */
        private String anchor = "";
        /** The transport site that message crossed, or "". */
        private String rpcSite = "";

        private Frame(long token, Role role, String api, int k,
                      boolean root, boolean turn, int window) {
            this.token = token;
            this.role = role;
            this.api = api;
            this.k = k;
            this.root = root;
            this.turn = turn;
            this.window = window;
        }
    }

    /** One captured lineage, carried with the work that was created in it. */
    public static final class Carried {
        private final List<Frame> frames;

        private Carried(List<Frame> frames) {
            this.frames = frames;
        }

        /** Whether this carries a lineage at all. */
        public boolean names() {
            return !frames.isEmpty();
        }
    }

    /**
     * Enters one scope frame and returns the token that leaves it.
     *
     * <p>{@code k} counts only ROOT hops of one (node, role, api) inside the
     * window: that is the only k an address reads ({@link #rootWindowIndex},
     * {@link edu.uva.liftlab.graphchecker.contract.CausalContext.Root}).
     * Nested hops count nothing (IDENTITY-V3 §4: the anchor replaced the
     * lineage list).  An unnameable node still gets its hop, marked lost; a
     * guessed node is a wrong causal chain.</p>
     */
    public static long push(String nodeKey, Role role, String api) {
        return push(nodeKey, role, api, STACK.get().isEmpty(), false);
    }

    /**
     * Enters one ROOT hop, whatever the thread already stands in: a daemon
     * tick is its own root, never nested in the request it runs under.
     */
    public static long pushRoot(String nodeKey, Role role, String api) {
        return push(nodeKey, role, api, true, true);
    }

    /**
     * Enters one ROOT hop that is a request, not a turn: a call the workload
     * makes is its own root, never nested in the request it runs under, and
     * keeps its k whenever it began.
     */
    public static long pushCallRoot(String nodeKey, Role role, String api) {
        return push(nodeKey, role, api, true, false);
    }

    private static long push(String nodeKey, Role role, String api,
                             boolean root, boolean turn) {
        List<Frame> stack = STACK.get();
        String node = Text.safe(nodeKey);
        Role kind = role == null ? Role.UNKNOWN : role;
        String family = Text.safe(api);
        int window = RecordingWindow.index();
        int k = root
                ? COUNTERS.computeIfAbsent(window + "\n" + node + "\n"
                        + kind.name() + "\n" + family,
                        scope -> new AtomicInteger()).incrementAndGet()
                : 0;
        long token = TOKENS.getAndIncrement();
        stack.add(new Frame(token, kind, family, k, root, turn, window));
        return token;
    }

    /** Leaves frame {@code token} and any frame a non-local exit left. */
    public static void pop(long token) {
        List<Frame> stack = STACK.get();
        for (int i = stack.size() - 1; i >= 0; i--) {
            if (stack.get(i).token != token) continue;
            while (stack.size() > i) stack.remove(stack.size() - 1);
            return;
        }
    }

    /** The frames this thread stands in, as a value the work carries. */
    public static Carried capture() {
        return new Carried(new ArrayList<Frame>(STACK.get()));
    }

    /**
     * Installs a carried lineage and opens one hop inside it: the dequeue
     * half of every queue that outlives its enqueueing thread.  The token
     * both closes the hop and restores the thread's own lineage.
     */
    public static long restore(Carried carried, String nodeKey, Role role,
                               String api) {
        List<Frame> stack = STACK.get();
        List<Frame> restored = new ArrayList<Frame>(stack);
        if (carried.names()) {
            // Inside a carried lineage the hop is no root.
            stack.clear();
            stack.addAll(carried.frames);
        }
        long token = push(nodeKey, role, api);
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
                    return new LinkedHashMap<Long, List<Frame>>();
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

    /** States the message that opened this scope: its causal context. */
    public static void anchor(String producerEndpointId, String rpcSite) {
        List<Frame> stack = STACK.get();
        if (stack.isEmpty()) return;
        Frame frame = stack.get(stack.size() - 1);
        frame.anchor = Text.safe(producerEndpointId);
        frame.rpcSite = Text.safe(rpcSite);
    }

    /** What the scope running here stands on, read in one scan. */
    static final class Here {
        /** The producer endpoint of the message that opened it, or "". */
        final String anchor;
        /** The transport site that message crossed, or "". */
        final String rpcSite;
        final Role rootRole;
        final String rootApi;
        final int rootWindowIndex;

        private Here(Frame anchored, Frame root) {
            this.anchor = anchored == null ? "" : anchored.anchor;
            this.rpcSite = anchored == null ? "" : anchored.rpcSite;
            this.rootRole = root == null ? Role.UNKNOWN : root.role;
            this.rootApi = root == null ? "" : root.api;
            this.rootWindowIndex = windowIndex(root);
        }
    }

    /**
     * The innermost root hop and the hop whose message opened the scope.
     *
     * <p>The anchor is searched outwards and STOPPED at the innermost root
     * (whose own anchor counts): a root descends from nothing ({@link
     * #pushRoot}), so a tick inside a request must not inherit the request's
     * {@code Anchor} form, or two ticks share one address.  Turns of a tick
     * differ by the root's window index ({@code
     * Identity.Hop#STARTED_ROOT}).</p>
     */
    static Here here() {
        List<Frame> stack = STACK.get();
        Frame anchored = null;
        for (int i = stack.size() - 1; i >= 0; i--) {
            Frame frame = stack.get(i);
            if (anchored == null && !frame.anchor.isEmpty()) anchored = frame;
            if (frame.root) return new Here(anchored, frame);
        }
        return new Here(anchored, null);
    }

    /** The innermost ROOT hop, which this scope descends from. */
    private static Frame root() {
        List<Frame> stack = STACK.get();
        for (int index = stack.size() - 1; index >= 0; index--) {
            if (stack.get(index).root) return stack.get(index);
        }
        return null;
    }

    /** The role of that root, or {@link Role#UNKNOWN}. */
    public static Role rootRole() {
        Frame root = root();
        return root == null ? Role.UNKNOWN : root.role;
    }

    /**
     * The window index of that root, or 0.
     *
     * <p>A TURN begun before the window stands at 0, as a pre-window frame
     * stands at iteration 0 ({@code Identity}): its k counted wall-clock
     * turns and would collide with the window's own turns.  A pre-window
     * REQUEST keeps its k: the workload decides it.</p>
     */
    public static int rootWindowIndex() {
        return windowIndex(root());
    }

    private static int windowIndex(Frame root) {
        if (root == null) return 0;
        return root.turn && root.window != RecordingWindow.index()
                ? 0 : root.k;
    }

    /**
     * The token of that root, or 0: which root hop is running here.
     *
     * <p>The lifetime of an execution-index level's counters ({@code
     * Identity.Level}); without it the thread base level counts for the whole
     * thread, a run-length ordinal IDENTITY-V3 §1 forbids.  Tokens are
     * thread-local and never published: replays compare the k they produce.
     * Carried frames are shared by reference ({@link #capture}), so pool work
     * counts under the root that created it.</p>
     */
    public static long rootToken() {
        Frame root = root();
        return root == null ? 0L : root.token;
    }

    /** The api that root's window index was counted under, or {@code ""}. */
    public static String rootApi() {
        Frame root = root();
        return root == null ? "" : root.api;
    }

    /**
     * Whether the root hop {@code token} is still standing on this thread;
     * {@code 0} (no root hop) is a thread state and always standing.
     */
    public static boolean isOpenRoot(long token) {
        if (token == 0L) return true;
        List<Frame> stack = STACK.get();
        for (int index = stack.size() - 1; index >= 0; index--) {
            Frame frame = stack.get(index);
            if (frame.root && frame.token == token) return true;
        }
        return false;
    }

    /** Test hook: one window, one thread, nothing carried over. */
    public static void resetForTests() {
        COUNTERS.clear();
        STACK.remove();
        RESTORED.remove();
    }
}
