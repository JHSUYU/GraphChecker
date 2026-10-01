package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §1, IDENTITY §2: why an occurrence ran, in exactly three
 * forms (sealed by the private constructor; switch on {@link #form()}
 * exhaustively):
 * {@link Anchor} (producer {@link Endpoint} id plus RPC site), {@link Root}
 * (k-th workload action or daemon tick per (node, role, api) in the window),
 * {@link Lost} (unattributable; degraded but still an identity).
 */
public abstract class CausalContext extends Value {
    /** Which of the three forms a context is. */
    public enum Form {
        ANCHOR,
        ROOT,
        LOST
    }

    /** The one separator between a root's role and the api it counts. */
    private static final char API_MARKER = '/';

    private static final String ANCHOR_PREFIX = "Anchor:";
    private static final String ROOT_PREFIX = "Root:";
    private static final String LOST_PREFIX = "Lost:";

    private CausalContext() {
    }

    /** The occurrence was started by a message from that producer endpoint. */
    public static Anchor of(String producerEndpointId, String rpcSite) {
        return new Anchor(Fields.text(producerEndpointId, "producerEndpointId"),
                Fields.text(rpcSite, "rpcSite"));
    }

    /**
     * The w-th root of that role and api in the window.  The api is part of
     * the context because {@code Lineage.push} counts per (node, role, api);
     * {@code ""} (undeclared, a daemon tick) renders without the segment.
     */
    public static Root of(Role role, String api, int windowIndex) {
        String declared = Fields.optional(api);
        return new Root(Fields.required(role, "role"),
                declared == null ? "" : declared,
                Fields.ordinal(windowIndex, "windowIndex"));
    }

    /** The scope was unattributable; the role is all that could be named. */
    public static Lost of(Role role) {
        return new Lost(Fields.required(role, "role"));
    }

    /** Reads any of the three rendered forms. */
    public static CausalContext parse(String rendered) {
        String value = rendered == null ? "" : rendered.trim();
        if (value.startsWith(ANCHOR_PREFIX)) {
            String body = value.substring(ANCHOR_PREFIX.length());
            int marker = body.indexOf('@');
            if (marker <= 0 || marker + 1 >= body.length()) {
                throw malformed(rendered);
            }
            return of(body.substring(0, marker), body.substring(marker + 1));
        }
        if (value.startsWith(ROOT_PREFIX)) {
            String body = value.substring(ROOT_PREFIX.length());
            int marker = body.lastIndexOf('#');
            if (marker <= 0 || marker + 1 >= body.length()) {
                throw malformed(rendered);
            }
            // Roles are [A-Z0-9_], so the first '/' separates the api.
            String head = body.substring(0, marker);
            int api = head.indexOf(API_MARKER);
            try {
                return of(Role.of(api < 0 ? head : head.substring(0, api)),
                        api < 0 ? "" : head.substring(api + 1),
                        Integer.parseInt(body.substring(marker + 1)));
            } catch (NumberFormatException notAnOrdinal) {
                throw malformed(rendered);
            }
        }
        if (value.startsWith(LOST_PREFIX)) {
            return of(Role.of(value.substring(LOST_PREFIX.length())));
        }
        throw malformed(rendered);
    }

    public abstract Form form();

    /** The canonical spelling: part of every occurrence id. */
    public abstract String render();

    /** Whether the scope behind this occurrence was unattributable. */
    public final boolean isLost() {
        return form() == Form.LOST;
    }

    @Override
    public final String toString() {
        return render();
    }

    private static IllegalArgumentException malformed(String rendered) {
        return new IllegalArgumentException(
                "not a causal context: " + rendered);
    }

    /** A message started this occurrence. */
    public static final class Anchor extends CausalContext {
        private final String producerEndpointId;
        private final String rpcSite;

        private Anchor(String producerEndpointId, String rpcSite) {
            this.producerEndpointId = producerEndpointId;
            this.rpcSite = rpcSite;
        }

        /** The {@link Endpoint#id()} of the export that started this. */
        public String producerEndpointId() {
            return producerEndpointId;
        }

        /** The RPC static site the message arrived on. */
        public String rpcSite() {
            return rpcSite;
        }

        @Override
        public Form form() {
            return Form.ANCHOR;
        }

        @Override
        public String render() {
            return ANCHOR_PREFIX + producerEndpointId + "@" + rpcSite;
        }

        /**
         * The context every delivery of one stored message to one watcher
         * shares: this one without the delivery ordinal {@code
         * runtime.MessageDoors#fetched} names the second delivery on of a
         * version by ({@code TRANSPORT.KIND.n/api}).  How many deliveries a
         * run takes is the store's timing, never a cause.
         */
        public Anchor anyDelivery() {
            int api = rpcSite.indexOf('/');
            String head = api < 0 ? rpcSite : rpcSite.substring(0, api);
            int ordinal = head.lastIndexOf('.');
            if (ordinal < 0 || head.indexOf('.') == ordinal
                    || ordinal + 1 >= head.length()) {
                return this;
            }
            for (int at = ordinal + 1; at < head.length(); at++) {
                if (!Character.isDigit(head.charAt(at))) return this;
            }
            return new Anchor(producerEndpointId, head.substring(0, ordinal)
                    + (api < 0 ? "" : rpcSite.substring(api)));
        }

        @Override
        Object[] parts() {
            return new Object[] {producerEndpointId, rpcSite};
        }
    }

    /** A workload action or a daemon tick started this occurrence. */
    public static final class Root extends CausalContext {
        private final Role role;
        private final String api;
        private final int windowIndex;

        private Root(Role role, String api, int windowIndex) {
            this.role = role;
            this.api = api;
            this.windowIndex = windowIndex;
        }

        public Role role() {
            return role;
        }

        /** The api this root's window index was counted under, or "". */
        public String api() {
            return api;
        }

        /** The k-th root of this role and api in the recording window. */
        public int windowIndex() {
            return windowIndex;
        }

        @Override
        public Form form() {
            return Form.ROOT;
        }

        @Override
        public String render() {
            return ROOT_PREFIX + role.name()
                    + (api.isEmpty() ? "" : API_MARKER + api)
                    + "#" + windowIndex;
        }

        @Override
        Object[] parts() {
            return new Object[] {role, api, windowIndex};
        }
    }

    /** Nothing could be attributed but the role. */
    public static final class Lost extends CausalContext {
        private final Role role;

        private Lost(Role role) {
            this.role = role;
        }

        public Role role() {
            return role;
        }

        @Override
        public Form form() {
            return Form.LOST;
        }

        @Override
        public String render() {
            return LOST_PREFIX + role.name();
        }

        @Override
        Object[] parts() {
            return new Object[] {Form.LOST, role};
        }
    }
}
