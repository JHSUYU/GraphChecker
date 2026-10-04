package edu.uva.liftlab.graphchecker.runtime;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;

/**
 * THE attribution rule: which node the running thread's work belongs to,
 * resolved lazily at the event that needs it, by four rules in order:
 *
 * <ol>
 *   <li>the innermost EXPLICIT scope on this thread
 *       ({@link RuntimeTraceContext#explicitSource}); a scope is a frame and
 *       nothing it names outlives it;</li>
 *   <li>else the innermost frame whose RECEIVER is registered
 *       ({@link Identity#receivers}), whatever pool thread runs it;</li>
 *   <li>else, on a thread that claimed no start, the node its creator
 *       carried when it constructed it
 *       ({@link RuntimeTraceContext#inheritedSource});</li>
 *   <li>else the node of whatever STARTED this work ({@link Reference}):
 *       its starter's by these same rules, resolved now, so a registration
 *       made after the start still counts.</li>
 * </ol>
 *
 * <p>A node's startup is that node's explicit scope while it stands, and
 * what it starts or creates carries the node in rules 3 and 4 ({@link
 * RuntimeTraceContext#beginNodeStartup}).  All four failing
 * answers {@code null} (LINEAGE_LOST), never a guess.</p>
 */
final class Attribution {
    /** How far a chain of starters is followed before it is given up. */
    private static final int MAX_CHAIN = 32;

    private Attribution() {
    }

    /**
     * Where some work was started, resolved when asked by the four rules as
     * they stood for its starter: the explicit scope and the inherited node
     * are fixed at the start; receivers are held weakly and their
     * registration is asked at use time.
     */
    static final class Reference {
        private final SourceRef explicit;
        private final List<WeakReference<Object>> receivers;
        private final SourceRef inherited;
        private final Reference parent;

        private Reference(SourceRef explicit, List<Object> receivers,
                          SourceRef inherited, Reference parent) {
            this.explicit = explicit;
            this.receivers = new ArrayList<WeakReference<Object>>(
                    receivers.size());
            for (Object receiver : receivers) {
                this.receivers.add(new WeakReference<Object>(receiver));
            }
            this.inherited = inherited;
            this.parent = parent;
        }

        /**
         * A creator's reference: its receivers and its own starter (what it
         * carried, the new thread inherits itself, rule 3).
         */
        static Reference of(List<Object> receivers, Reference parent) {
            return new Reference(null, receivers, null, parent);
        }

        SourceRef resolve() {
            Reference cursor = this;
            for (int depth = 0; cursor != null && depth < MAX_CHAIN;
                    depth++) {
                if (cursor.explicit != null) return cursor.explicit;
                List<Object> alive = new ArrayList<Object>(
                        cursor.receivers.size());
                for (WeakReference<Object> held : cursor.receivers) {
                    Object receiver = held.get();
                    if (receiver != null) alive.add(receiver);
                }
                SourceRef registered =
                        RuntimeTraceContext.firstRegistered(alive);
                if (registered != null) return registered;
                if (cursor.inherited != null) return cursor.inherited;
                cursor = cursor.parent;
            }
            return null;
        }
    }

    /**
     * The reference a work started HERE carries: this thread's node by the
     * four rules, its inherited node included -- a thread a node's startup
     * created under no request is that node only by rule 3, and work it
     * handed to a shared executor before the node registered named none
     * (round HN1: a DataNode's actor's IPC sends from Hadoop's one sender
     * pool, CLAIMed as workload/unregistered).
     */
    static Reference capture() {
        return new Reference(RuntimeTraceContext.carriedNode(),
                Identity.receivers(),
                Identity.adoptedStarter() ? null
                        : RuntimeTraceContext.inheritedSource(),
                Identity.starter());
    }

    /**
     * The node this thread's work belongs to, or null.
     *
     * @param receiver the asking activation's receiver (innermost frame even
     *                 if not yet standing); null for a non-activation
     */
    static SourceRef resolve(Object receiver) {
        SourceRef explicit = RuntimeTraceContext.explicitSource();
        if (explicit != null) return explicit;
        List<Object> frames = Identity.receivers();
        if (receiver != null) frames.add(0, receiver);
        SourceRef registered = RuntimeTraceContext.firstRegistered(frames);
        if (registered != null) return registered;
        // Rule 3: an unclaimed thread inherits its creator's scope.
        if (!Identity.adoptedStarter()) {
            SourceRef inherited = RuntimeTraceContext.inheritedSource();
            if (inherited != null) return inherited;
        }
        Reference starter = Identity.starter();
        return starter == null ? null : starter.resolve();
    }
}
