package edu.uva.liftlab.graphchecker.contract;

import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A schedule event's context as another run of the same world names it,
 * whatever a loop before it counted (PIPELINE §10b): a context spells the
 * invocation counts of its frames ({@code @n}) and names each message it
 * serves by its producer endpoint, whose id hashes the sender's counts too,
 * so a poll that ran another number of times before a send renames every
 * context the send started (solr-18413 IB1: the MIGRATE task polled
 * REQUESTSTATUS three times in the confirmed session and twice natively, so
 * its SPLIT request, and the node work it started, had another endpoint id
 * in every native run).  Here a context drops its frames' counts, and a
 * message hop names its sender's stable context and the send's site, only
 * when that send was the sender's first of its site: a later one is a
 * loop's, no fixed point of the world, and its hop has no stable name.
 * Fed a run's SENDs in schedule order; one per run.
 */
public final class StableEventNames {
    private static final Pattern COUNT = Pattern.compile("@[0-9]+");
    private static final Pattern ANCHOR = Pattern.compile("Anchor:([0-9a-f]+)@");

    /** A producer endpoint's stable sender name; null when it has none. */
    private final Map<String, String> senders = new HashMap<String, String>();
    /** Sends so far per stable sender and site. */
    private final Map<String, Integer> sends = new HashMap<String, Integer>();

    /** A SEND made from {@code context} at {@code site} as {@code endpoint}. */
    public void sent(String context, String site, String endpoint) {
        if (endpoint == null || endpoint.isEmpty()
                || senders.containsKey(endpoint)) {
            return;
        }
        String sender = context(context);
        String name = null;
        if (sender != null) {
            String key = sender + " >" + site;
            Integer before = sends.put(key, sends.getOrDefault(key, 0) + 1);
            if (before == null) name = key;
        }
        senders.put(endpoint, name);
    }

    /**
     * {@code context}'s stable name: without its frames' counts, each message
     * hop {@code Anchor:{<sender> ><site>}}; null when a hop's send was not
     * its sender's first of its site, or no send of this run named it.
     */
    public String context(String context) {
        StringBuilder name = new StringBuilder();
        Matcher hop = ANCHOR.matcher(context);
        int at = 0;
        while (hop.find()) {
            String sender = senders.get(hop.group(1));
            if (sender == null) return null;
            name.append(COUNT.matcher(context.substring(at, hop.start()))
                    .replaceAll(""));
            name.append("Anchor:{").append(sender).append("}@");
            at = hop.end();
        }
        return name.append(COUNT.matcher(context.substring(at))
                .replaceAll("")).toString();
    }
}
