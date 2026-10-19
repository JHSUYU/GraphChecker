package edu.uva.liftlab.graphchecker.contract;

import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public final class StableEventNames {
    private static final Pattern COUNT = Pattern.compile("@[0-9]+");
    private static final Pattern ANCHOR = Pattern.compile("Anchor:([0-9a-f]+)@");

    private final Map<String, String> senders = new HashMap<String, String>();
    private final Map<String, Integer> sends = new HashMap<String, Integer>();

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

    public String context(String context) {
        context = turnFamily(context);
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

    private static final String TIMED_WAIT_TURN =
            "Root:" + Role.WAKE.name() + "/";

    public static boolean timedWaitTurn(String context) {
        return context.startsWith(TIMED_WAIT_TURN, context.indexOf('|') + 1);
    }

    public static String turnFamily(String context) {
        if (!timedWaitTurn(context)) return context;
        int node = context.indexOf('|');
        int frames = context.indexOf('|', node + 1);
        int end = frames < 0 ? context.length() : frames;
        int number = context.lastIndexOf('#', end - 1);
        return number <= node ? context
                : context.substring(0, number) + "#*" + context.substring(end);
    }
}
