package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.stream.JsonReader;

import java.io.IOException;
import java.io.StringReader;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * What one read of rows shares: each string its lines parse to, and each
 * address part its rows are built of, held once.  Every row spells its
 * occurrence, call sites and field names out in full, and a row read on its
 * own held its own copy of each: solr-18413's corpus (40 sessions, 2.2 GB of
 * JSONL; one session's 2.6M string tokens are 41K distinct) was 52M strings,
 * 5.5 GB of the 8.3 GB EXPLORE and COMPOSE held.
 *
 * <p>Equal values only, never a JSON node: the expression walks go by node
 * identity ({@code smt.ExpressionWalk}), so a node stays its line's own.</p>
 */
final class RowPool {
    /** Concurrent: a corpus's sessions are read in parallel
     *  ({@code SessionReader#readAll}). */
    private final Map<Object, Object> held =
            new ConcurrentHashMap<Object, Object>();

    /** The instance held for a value equal to {@code value}; the first one
     *  asked for is the one held. */
    @SuppressWarnings("unchecked")
    <T> T shared(T value) {
        Object had = held.putIfAbsent(value, value);
        return had == null ? value : (T) had;
    }

    /** A reader of one line that takes each name and string (a number's
     *  spelling too) from this pool. */
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
