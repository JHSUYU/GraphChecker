package edu.uva.liftlab.graphchecker.runtime.d3;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Resolving a case's declared occurrence against the seed session.
 *
 * <p>IDENTITY-IMPL §D.  Humans do not write execution indexes: a case
 * declares the v1 spelling — {@code node#epoch/region/REGION.x@src#epoch/api#k}
 * or {@code node#epoch/region/REGION.x#k} — and the campaign resolves it
 * ONCE, against the session that recorded the run: same region, same api on
 * the incoming anchor when the selector gives one, k-th match in seed
 * order.  Everything downstream uses the resolved id and never the
 * string.</p>
 */
public final class Selectors {
    private Selectors() {
    }

    /** One declared selector: the region, the api it was reached by, k. */
    public static final class Selector {
        private final String regionId;
        private final String api;
        private final int k;

        private Selector(String regionId, String api, int k) {
            this.regionId = regionId;
            this.api = api;
            this.k = k;
        }

        public String regionId() {
            return regionId;
        }

        /** The api of the request that reached it, or {@code ""}. */
        public String api() {
            return api;
        }

        public int k() {
            return k;
        }

        public boolean isNamed() {
            return !regionId.isEmpty() && k >= 1;
        }

        @Override
        public String toString() {
            return regionId + (api.isEmpty() ? "" : "@" + api) + "#" + k;
        }
    }

    /** Reads a v1 case declaration as a selector; never throws. */
    public static Selector parse(String declaration) {
        String value = Text.safe(declaration);
        int region = value.indexOf("/region/");
        if (region < 0) return new Selector("", "", 0);
        String tail = value.substring(region + "/region/".length());
        int hash = tail.lastIndexOf('#');
        if (hash <= 0) return new Selector("", "", 0);
        int k;
        try {
            k = Integer.parseInt(tail.substring(hash + 1));
        } catch (NumberFormatException notAnOrdinal) {
            return new Selector("", "", 0);
        }
        String head = tail.substring(0, hash);
        int at = head.indexOf('@');
        if (at < 0) return new Selector(head, "", k);
        String family = head.substring(at + 1);
        int api = family.lastIndexOf('/');
        return new Selector(head.substring(0, at),
                api < 0 ? family : family.substring(api + 1), k);
    }

    /**
     * The occurrence a selector names in one seed session, or {@code ""}.
     *
     * <p>Matching is by the row's own statements: the region it is an
     * activation of, and — when the selector gives an api — the api on the
     * anchor it entered under, which {@code identity.jsonl} states.  The
     * k-th match in the session's own order is the answer, and there being
     * fewer than k is an error the caller names rather than a silent
     * first-match.</p>
     */
    public static String resolve(Selector selector, Path iteration,
                                 String sessionId) {
        if (selector == null || !selector.isNamed()) return "";
        SessionDir session = SessionDir.of(iteration, sessionId);
        Map<String, String> contexts = contexts(session);
        List<String> matches = new ArrayList<String>();
        try {
            for (JsonObject line : RowCodec.readJsonl(session.activations())) {
                ActivationRow row = RowCodec.readActivation(line);
                String address = row.occurrence().render();
                if (!row.occurrence().regionId().equals(selector.regionId())) {
                    continue;
                }
                if (!selector.api().isEmpty()) {
                    String context = contexts.get(address);
                    if (context == null
                            || !context.endsWith("#" + selector.api())) {
                        continue;
                    }
                }
                matches.add(row.occurrence().id());
            }
        } catch (IOException unreadable) {
            return "";
        }
        return matches.size() >= selector.k()
                ? matches.get(selector.k() - 1) : "";
    }

    /** address -> the causal context the identity file states for it. */
    private static Map<String, String> contexts(SessionDir session) {
        Map<String, String> contexts = new LinkedHashMap<String, String>();
        Path file = session.dir().resolve(SessionPublisher.IDENTITIES);
        if (!Files.isReadable(file)) return contexts;
        try {
            for (JsonObject row : RowCodec.readJsonl(file)) {
                if (!row.has("address") || !row.has("context")) continue;
                contexts.put(row.get("address").getAsString(),
                        row.get("context").getAsString());
            }
        } catch (IOException unreadable) {
            return contexts;
        }
        return contexts;
    }
}
