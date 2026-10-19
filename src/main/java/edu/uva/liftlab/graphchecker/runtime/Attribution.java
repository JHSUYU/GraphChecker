package edu.uva.liftlab.graphchecker.runtime;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;

final class Attribution {
    private static final int MAX_CHAIN = 32;

    private Attribution() {
    }

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

    static Reference capture() {
        return new Reference(RuntimeTraceContext.carriedNode(),
                Identity.receivers(),
                Identity.adoptedStarter() ? null
                        : RuntimeTraceContext.inheritedSource(),
                Identity.starter());
    }

    static SourceRef resolve(Object receiver) {
        SourceRef explicit = RuntimeTraceContext.explicitSource();
        if (explicit != null) return explicit;
        List<Object> frames = Identity.receivers();
        if (receiver != null) frames.add(0, receiver);
        SourceRef registered = RuntimeTraceContext.firstRegistered(frames);
        if (registered != null) return registered;
        if (!Identity.adoptedStarter()) {
            SourceRef inherited = RuntimeTraceContext.inheritedSource();
            if (inherited != null) return inherited;
        }
        Reference starter = Identity.starter();
        return starter == null ? null : starter.resolve();
    }
}
