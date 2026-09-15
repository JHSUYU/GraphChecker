package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * IDENTITY-IMPL A: why an occurrence ran, in exactly three forms.
 *
 * <p>{@link Anchor} -- a message started it, and the incoming anchor is the
 * producer's {@link Endpoint} id (which recursively carries the producer's own
 * context) together with the RPC static site.  {@link Root} -- a workload
 * action or a daemon tick with no incoming message, numbered by the k-th such
 * root of its role inside the recording window.  {@link Lost} -- the scope
 * could not be attributed: degraded, and still an identity rather than a
 * guess.</p>
 *
 * <p>Sealed by construction: the constructor is private, so the three nested
 * forms are the only ones there are and a reader may switch on {@link #form()}
 * exhaustively.</p>
 */
public abstract class CausalContext {
    /** Which of the three forms a context is. */
    public enum Form {
        ANCHOR,
        ROOT,
        LOST
    }

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

    /** The w-th root of that role inside the recording window. */
    public static Root of(Role role, int windowIndex) {
        return new Root(Fields.required(role, "role"),
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
            try {
                return of(role(body.substring(0, marker), rendered),
                        Integer.parseInt(body.substring(marker + 1)));
            } catch (NumberFormatException notAnOrdinal) {
                throw malformed(rendered);
            }
        }
        if (value.startsWith(LOST_PREFIX)) {
            return of(role(value.substring(LOST_PREFIX.length()), rendered));
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

    private static Role role(String name, String rendered) {
        for (Role role : Role.values()) {
            if (role.name().equals(name)) return role;
        }
        throw malformed(rendered);
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

        @Override
        public boolean equals(Object value) {
            if (this == value) return true;
            if (!(value instanceof Anchor)) return false;
            Anchor other = (Anchor) value;
            return producerEndpointId.equals(other.producerEndpointId)
                    && rpcSite.equals(other.rpcSite);
        }

        @Override
        public int hashCode() {
            return Objects.hash(producerEndpointId, rpcSite);
        }
    }

    /** A workload action or a daemon tick started this occurrence. */
    public static final class Root extends CausalContext {
        private final Role role;
        private final int windowIndex;

        private Root(Role role, int windowIndex) {
            this.role = role;
            this.windowIndex = windowIndex;
        }

        public Role role() {
            return role;
        }

        /** The k-th root of this role inside the recording window. */
        public int windowIndex() {
            return windowIndex;
        }

        @Override
        public Form form() {
            return Form.ROOT;
        }

        @Override
        public String render() {
            return ROOT_PREFIX + role.name() + "#" + windowIndex;
        }

        @Override
        public boolean equals(Object value) {
            if (this == value) return true;
            if (!(value instanceof Root)) return false;
            Root other = (Root) value;
            return windowIndex == other.windowIndex && role == other.role;
        }

        @Override
        public int hashCode() {
            return Objects.hash(role, windowIndex);
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
        public boolean equals(Object value) {
            if (this == value) return true;
            if (!(value instanceof Lost)) return false;
            return role == ((Lost) value).role;
        }

        @Override
        public int hashCode() {
            return Objects.hash(Form.LOST, role);
        }
    }
}
