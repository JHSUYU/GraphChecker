package org.example.decoded;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

public final class Decoded {
    public static final class Client {
        public final Object connection = new Object();
    }

    public static final class Slice {
        public final String name;
        public final String state;

        public Slice(String name, String state) {
            this.name = name;
            this.state = state;
        }
    }

    public static class Router {
        public static final Router DEFAULT = new Router();
        public static final Map<String, Router> ROUTERS =
                new LinkedHashMap<>();
        static {
            ROUTERS.put("implicit", new Implicit());
        }
        public final String name = "compositeId";
    }

    public static final class Implicit extends Router {
    }

    public static final class States implements Supplier<Slice> {
        public final Slice held;

        public States(Slice held) {
            this.held = held;
        }

        @Override
        public Slice get() {
            return held;
        }
    }

    public static final class Collection {
        public final Map<String, Slice> slices = new LinkedHashMap<>();
        public Router router = Router.DEFAULT;
        public States states;
        public final Slice[] active;
        public final List<Slice> listed;
        public final Supplier<Object> lazy;
        public final Inner inner;

        public Collection(Client client, Slice... slices) {
            for (Slice slice : slices) this.slices.put(slice.name, slice);
            this.active = slices;
            this.listed = Arrays.asList(slices);
            this.lazy = () -> client;
            this.inner = new Inner();
        }

        public final class Inner {
            public final String label = "inner";
        }
    }

    private Decoded() {
    }
}
