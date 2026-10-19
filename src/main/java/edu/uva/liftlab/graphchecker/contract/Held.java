package edu.uva.liftlab.graphchecker.contract;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public final class Held {
    private Held() {
    }

    public static <K, T> void trimmed(Map<K, List<T>> index) {
        for (List<T> list : index.values()) {
            if (list instanceof ArrayList) ((ArrayList<T>) list).trimToSize();
        }
    }
}
