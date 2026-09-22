package edu.uva.liftlab.graphchecker.runtime;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;

/**
 * THE attribution rule: which node the running thread's work belongs to.
 *
 * <p>One resolver, evaluated lazily -- at the event that needs a node, never
 * as a string frozen when a thread was created -- by three rules in order:</p>
 *
 * <ol>
 *   <li>An EXPLICIT scope: the innermost request, carried scope, inbound
 *       exchange with a registered local owner, tick owner or service-loop
 *       turn standing on this thread ({@link RuntimeTraceContext#explicitSource}).
 *       A scope is a frame: it is opened and closed, and nothing it names
 *       outlives it.</li>
 *   <li>Else the innermost application frame whose RECEIVER is registered:
 *       the frames of the execution index carry their receivers
 *       ({@link Identity#receivers}), so a NameNode handler serving
 *       {@code Server.call} is the registered RPC server's, whatever pool
 *       thread runs it.  This is the rule the recording used to apply
 *       offline, over its trace, for the planner alone.</li>
 *   <li>Else the node of whatever STARTED this work, kept as a reference and
 *       resolved now ({@link Reference}): the starter's explicit scope, else
 *       its registered receivers, else its own starter.  A daemon thread
 *       started before its node was registered belongs to that node the
 *       moment the node is registered, because the reference names the
 *       DataNode object and not a snapshot of what it was called then.</li>
 * </ol>
 *
 * <p>When all three fail the answer is {@code null}: the thread belongs to no
 * node the run can name, and the address that says so is a diagnostic
 * (LINEAGE_LOST), never a node guessed for it.</p>
 */
final class Attribution {
    /** How far a chain of starters is followed before it is given up. */
    private static final int MAX_CHAIN = 32;

    private Attribution() {
    }

    /**
     * Where some work was started: resolved when asked, not when filed.
     *
     * <p>The starter's explicit scope is a fact of the start (it was, or was
     * not, inside a request) and is kept as the source it named.  Its
     * receivers are kept weakly, as objects: whether one of them is
     * registered is asked at use time, which is what lets a registration
     * made after the start still attribute the work.</p>
     */
    static final class Reference {
        private final SourceRef explicit;
        private final List<WeakReference<Object>> receivers;
        private final Reference parent;

        private Reference(SourceRef explicit, List<Object> receivers,
                          Reference parent) {
            this.explicit = explicit;
            this.receivers = new ArrayList<WeakReference<Object>>(
                    receivers.size());
            for (Object receiver : receivers) {
                this.receivers.add(new WeakReference<Object>(receiver));
            }
            this.parent = parent;
        }

        /** A creator's reference: its receivers and its own starter. */
        static Reference of(List<Object> receivers, Reference parent) {
            return new Reference(null, receivers, parent);
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
                cursor = cursor.parent;
            }
            return null;
        }
    }

    /**
     * The reference a work started HERE carries: this thread's explicit
     * scope, its receivers innermost first, and its own starter.
     */
    static Reference capture() {
        return new Reference(RuntimeTraceContext.explicitSource(),
                Identity.receivers(), Identity.starter());
    }

    /**
     * The node this thread's work belongs to, by the three rules, or null.
     *
     * @param receiver the receiver of the activation asking, which is the
     *                 innermost frame whether or not its level is standing
     *                 yet; null when the asker is not an activation
     */
    static SourceRef resolve(Object receiver) {
        SourceRef explicit = RuntimeTraceContext.explicitSource();
        if (explicit != null) return explicit;
        List<Object> frames = Identity.receivers();
        if (receiver != null) frames.add(0, receiver);
        SourceRef registered = RuntimeTraceContext.firstRegistered(frames);
        if (registered != null) return registered;
        // Rule 3.  A thread that claimed no start of its own was started by
        // whatever created it, inside whatever scope that creator stood in.
        if (!Identity.adoptedStarter()) {
            SourceRef inherited = RuntimeTraceContext.inheritedSource();
            if (inherited != null) return inherited;
        }
        Reference starter = Identity.starter();
        return starter == null ? null : starter.resolve();
    }
}
