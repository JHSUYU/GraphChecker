package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.stream.JsonReader;

import java.io.IOException;
import java.io.StringReader;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

public final class RowPool {
    private final Map<Object, Object> held =
            new ConcurrentHashMap<Object, Object>();

    @SuppressWarnings("unchecked")
    <T> T shared(T value) {
        Object had = held.putIfAbsent(value, value);
        return had == null ? value : (T) had;
    }

    JsonReader reader(String line) {
        return new JsonReader(new StringReader(line)) {
            @Override
            public String nextName() throws IOException {
                return shared(super.nextName());
            }

            @Override
            public String nextString() throws IOException {
                return shared(super.nextString());
            }
        };
    }
}
