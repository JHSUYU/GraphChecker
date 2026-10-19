package edu.uva.liftlab.graphchecker.contract;

public abstract class CausalContext extends Value {
    public enum Form {
        ANCHOR,
        ROOT,
        LOST
    }

    private static final char API_MARKER = '/';

    private static final String ANCHOR_PREFIX = "Anchor:";
    private static final String ROOT_PREFIX = "Root:";
    private static final String LOST_PREFIX = "Lost:";

    private CausalContext() {
    }

    public static Anchor of(String producerEndpointId, String rpcSite) {
        return new Anchor(Fields.text(producerEndpointId, "producerEndpointId"),
                Fields.text(rpcSite, "rpcSite"));
    }

    public static Root of(Role role, String api, int windowIndex) {
        String declared = Fields.optional(api);
        return new Root(Fields.required(role, "role"),
                declared == null ? "" : declared,
                Fields.ordinal(windowIndex, "windowIndex"));
    }

    public static Lost of(Role role) {
        return new Lost(Fields.required(role, "role"));
    }

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

    public abstract String render();

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

    public static final class Anchor extends CausalContext {
        private final String producerEndpointId;
        private final String rpcSite;

        private Anchor(String producerEndpointId, String rpcSite) {
            this.producerEndpointId = producerEndpointId;
            this.rpcSite = rpcSite;
        }

        public String producerEndpointId() {
            return producerEndpointId;
        }

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

    public static final int ANY_TURN = -1;

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

        public String api() {
            return api;
        }

        public int windowIndex() {
            return windowIndex;
        }

        public Root anyTurn() {
            return Role.WAKE.equals(role) && windowIndex != ANY_TURN
                    ? new Root(role, api, ANY_TURN) : this;
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
