package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * The names one guarded read is known by, shared by the three stages that
 * have to agree on them: the closure that stamps a candidate selector, the
 * composer that emits it, and the flip solver that re-encodes it.
 *
 * <p>Every name here is content addressed, so agreement is not a
 * convention the three stages keep separately -- a selector the composer
 * computes from a read's identities has to be the selector the closure
 * already wrote into the row, and both refuse the read when it is not.</p>
 */
final class GuardedReadNaming {
    private static final String SELECTOR_PREFIX = "read_selector__";
    private static final String PROJECTION_PREFIX = "READ_CANDIDATES.v1.";
    private static final String USE_PREFIX = "RF_USE.";

    private GuardedReadNaming() {
    }

    /** The selector of one candidate arm of one stable read. */
    static String selector(String readIdentity, String candidateIdentity) {
        if (readIdentity.isEmpty() || candidateIdentity.isEmpty()) {
            return "";
        }
        return SELECTOR_PREFIX + CanonicalJson.sha256(
                readIdentity + "\n" + candidateIdentity);
    }

    /**
     * One read site may execute repeatedly inside a bounded loop.  Its
     * stable read identity names the site/case; the already
     * content-addressed candidate identities distinguish the value seen
     * at each execution without hashing the expanded expression DAG.
     */
    static String projectionIdentity(JsonObject read) {
        List<String> candidates = new ArrayList<>();
        int index = 0;
        for (JsonElement encoded : array(read, "candidates")) {
            String identity = encoded.isJsonObject()
                    ? optionalString(encoded.getAsJsonObject(),
                    SymbolicPropagationClosure.READ_CANDIDATE_IDENTITY)
                    : "";
            candidates.add(firstNonBlank(identity,
                    "MISSING_CANDIDATE_" + index++));
        }
        Collections.sort(candidates);
        return PROJECTION_PREFIX + CanonicalJson.sha256(
                String.join("\n", candidates));
    }

    /**
     * One exact use of a guarded read: the projection it selected from,
     * under the activation guard that reached it.  Two uses that share
     * both are one use, and the same projection under one activation may
     * not stand for two different candidate sets.
     */
    static String useIdentity(String projectionIdentity, String activation) {
        return USE_PREFIX + CanonicalJson.sha256(
                projectionIdentity + "\n" + activation);
    }
}
