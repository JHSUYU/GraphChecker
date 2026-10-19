package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Role;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

public final class Lineage {
    private static final Map<String, AtomicInteger> COUNTERS =
            new ConcurrentHashMap<String, AtomicInteger>();
    private static final AtomicLong TOKENS = new AtomicLong(1L);
    private static final InheritableThreadLocal<List<Frame>> STACK =
            new InheritedState<List<Frame>>() {
                @Override
                protected List<Frame> initialValue() {
                    return new ArrayList<Frame>();
                }

                @Override
                protected List<Frame> inherit(List<Frame> parent) {
                    return parent == null || PoolWorkers.constructing()
                            ? new ArrayList<Frame>()
                            : carried(parent);
                }
            };

    private Lineage() {
    }

    private static final class Frame {
        private final long token;
        private final Role role;
        private final String api;
        private final int k;
        private final boolean root;
        private final boolean turn;
        private final int window;
        private final AtomicInteger counter;
        private volatile boolean named;
        private String anchor = "";
        private String rpcSite = "";

        private Frame(long token, Role role, String api, int k,
                      boolean root, boolean turn, int window,
                      AtomicInteger counter) {
            this.token = token;
            this.role = role;
            this.api = api;
            this.k = k;
            this.root = root;
            this.turn = turn;
            this.window = window;
            this.counter = counter;
        }
    }

    private static final ThreadLocal<Boolean> QUIET =
            new ThreadLocal<Boolean>();

    public static final class Carried {
        private final List<Frame> frames;

        private Carried(List<Frame> frames) {
            this.frames = frames;
        }

        public boolean names() {
            return !frames.isEmpty();
        }
    }

    public static long push(String nodeKey, Role role, String api) {
        return push(nodeKey, role, api, STACK.get().isEmpty(), false);
    }

    public static long pushRoot(String nodeKey, Role role, String api) {
        return push(nodeKey, role, api, true, true);
    }

    public static long pushCallRoot(String nodeKey, Role role, String api) {
        return push(nodeKey, role, api, true, false);
    }

    private static long push(String nodeKey, Role role, String api,
                             boolean root, boolean turn) {
        List<Frame> stack = STACK.get();
        String node = trimmed(nodeKey);
        Role kind = role == null ? Role.UNKNOWN : role;
        String family = trimmed(api);
        int window = RecordingWindow.index();
        AtomicInteger counter = root
                ? COUNTERS.computeIfAbsent(window + "\n" + node + "\n"
                        + kind.name() + "\n" + family,
                        scope -> new AtomicInteger())
                : null;
        int k = counter == null ? 0 : counter.incrementAndGet();
        long token = TOKENS.getAndIncrement();
        stack.add(new Frame(token, kind, family, k, root, turn, window,
                counter));
        return token;
    }

    public static void pop(long token) {
        List<Frame> stack = STACK.get();
        for (int i = stack.size() - 1; i >= 0; i--) {
            if (stack.get(i).token != token) continue;
            while (stack.size() > i) {
                Frame left = stack.remove(stack.size() - 1);
                if (left.turn && !left.named) {
                    left.counter.compareAndSet(left.k, left.k - 1);
                }
            }
            return;
        }
    }

    static void name(long token) {
        List<Frame> stack = STACK.get();
        for (int i = stack.size() - 1; i >= 0; i--) {
            if (stack.get(i).token == token) stack.get(i).named = true;
        }
    }

    static <T> T quietly(java.util.function.Supplier<T> read) {
        Boolean outer = QUIET.get();
        QUIET.set(Boolean.TRUE);
        try {
            return read.get();
        } finally {
            QUIET.set(outer);
        }
    }

    public static Carried capture() {
        return new Carried(carried(STACK.get()));
    }

    private static List<Frame> carried(List<Frame> frames) {
        for (Frame frame : frames) {
            if (frame.turn) frame.named = true;
        }
        return new ArrayList<Frame>(frames);
    }

    public static long restore(Carried carried, String nodeKey, Role role,
                               String api) {
        List<Frame> stack = STACK.get();
        List<Frame> restored = new ArrayList<Frame>(stack);
        if (carried.names()) {
            stack.clear();
            stack.addAll(carried.frames);
        }
        long token = push(nodeKey, role, api);
        RESTORED.get().put(token, restored);
        return token;
    }

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

    public static boolean named() {
        return !STACK.get().isEmpty();
    }

    public static Role role() {
        List<Frame> stack = STACK.get();
        return stack.isEmpty() ? Role.UNKNOWN
                : stack.get(stack.size() - 1).role;
    }

    public static void anchor(String producerEndpointId, String rpcSite) {
        List<Frame> stack = STACK.get();
        if (stack.isEmpty()) return;
        Frame frame = stack.get(stack.size() - 1);
        frame.anchor = trimmed(producerEndpointId);
        frame.rpcSite = trimmed(rpcSite);
    }

    static final class Here {
        final String anchor;
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

    private static Frame root() {
        List<Frame> stack = STACK.get();
        for (int index = stack.size() - 1; index >= 0; index--) {
            if (stack.get(index).root) return stack.get(index);
        }
        return null;
    }

    public static Role rootRole() {
        Frame root = root();
        return root == null ? Role.UNKNOWN : root.role;
    }

    public static int rootWindowIndex() {
        return windowIndex(root());
    }

    private static int windowIndex(Frame root) {
        if (root == null) return 0;
        if (root.turn && QUIET.get() == null) root.named = true;
        return root.turn && root.window != RecordingWindow.index()
                ? 0 : root.k;
    }

    public static long rootToken() {
        Frame root = root();
        return root == null ? 0L : root.token;
    }

    public static String rootApi() {
        Frame root = root();
        return root == null ? "" : root.api;
    }

    public static boolean isOpen(long token) {
        if (token == 0L) return true;
        List<Frame> stack = STACK.get();
        for (int index = stack.size() - 1; index >= 0; index--) {
            if (stack.get(index).token == token) return true;
        }
        return false;
    }

    public static long contextToken() {
        List<Frame> stack = STACK.get();
        for (int index = stack.size() - 1; index >= 0; index--) {
            Frame frame = stack.get(index);
            if (!frame.anchor.isEmpty() || frame.root) return frame.token;
        }
        return 0L;
    }

    public static void resetForTests() {
        COUNTERS.clear();
        STACK.remove();
        RESTORED.remove();
    }
}
