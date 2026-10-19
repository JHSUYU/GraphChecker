package edu.uva.liftlab.graphchecker.contract;

import java.util.ArrayList;
import java.util.List;

public final class Endpoint extends Value {
    private final OccurrenceAddress occurrence;
    private final String site;
    private final ExecutionIndex siteIndex;
    private final int attempt;
    private String id;

    private Endpoint(OccurrenceAddress occurrence, String site,
                     ExecutionIndex siteIndex, int attempt) {
        this.occurrence = occurrence;
        this.site = site;
        this.siteIndex = siteIndex;
        this.attempt = attempt;
    }

    public static Endpoint of(OccurrenceAddress occurrence, String site,
                              ExecutionIndex siteIndex, int attempt) {
        return new Endpoint(Fields.required(occurrence, "occurrence"),
                Fields.text(site, "site"),
                Fields.required(siteIndex, "siteIndex"),
                Fields.nonNegative(attempt, "attempt"));
    }

    public static String messageSite(String transport, String half,
                                     String verb) {
        String site = (transport == null ? "" : transport) + "#"
                + (half == null ? "" : half);
        String named = verb(verb);
        return named.isEmpty() ? site : site + ":" + named;
    }

    public static boolean replySite(String site) {
        int half = site == null ? -1 : site.indexOf('#');
        if (half < 0) return false;
        int verb = site.indexOf(':', half);
        return REPLY.equals(verb < 0 ? site.substring(half + 1)
                : site.substring(half + 1, verb));
    }

    public static final String REPLY = "RESPONSE";

    public static String verb(String verb) {
        if (verb == null) return "";
        if (verb.indexOf('/') >= 0 || verb.indexOf('@') >= 0) {
            throw new IllegalArgumentException("a message verb spells no '/'"
                    + " or '@': " + verb);
        }
        return verb;
    }

    public static String stateSite(String className, String method, int bci,
                                   boolean write) {
        return stateSite(className, method, "", bci, write);
    }

    public static String stateSite(String className, String method,
                                   String descriptor, int bci, boolean write) {
        String stated = descriptor == null ? "" : descriptor.trim();
        return Fields.text(className, "className") + "#"
                + Fields.text(method, "method") + stated + "#"
                + Fields.nonNegative(bci, "bci") + ":"
                + (write ? "WRITE" : "READ");
    }

    public static String initialSite(String observedAt) {
        return observedAt.substring(0, observedAt.lastIndexOf(':') + 1)
                + "INITIAL";
    }

    public OccurrenceAddress occurrence() {
        return occurrence;
    }

    public String site() {
        return site;
    }

    public ExecutionIndex siteIndex() {
        return siteIndex;
    }

    public int attempt() {
        return attempt;
    }

    public String id() {
        String digested = id;
        if (digested == null) {
            digested = Digests.digest(occurrence.id() + "/" + site + "/"
                    + siteIndex.hash() + "/" + attempt, 16);
            id = digested;
        }
        return digested;
    }

    public String activation() {
        return activation(occurrence, ExecutionIndex.of(activationFrames()));
    }

    public List<Frame> activationFrames() {
        List<Frame> frames = siteIndex.frames();
        int last = frames.size() - 1;
        boolean eventFrame = last >= 0 && frames.get(last).callSite()
                .equals(site.replace('/', '.'));
        return eventFrame ? frames.subList(0, last) : frames;
    }

    public Endpoint anyTurn() {
        List<Frame> turned = new ArrayList<Frame>();
        for (Frame frame : siteIndex.frames()) {
            turned.add(Frame.of(frame.callSite(), 0));
        }
        return new Endpoint(occurrence, site, ExecutionIndex.of(turned),
                attempt);
    }

    public Endpoint anyDelivery() {
        OccurrenceAddress delivered = occurrence.anyDelivery();
        return delivered == occurrence ? this
                : new Endpoint(delivered, site, siteIndex, attempt);
    }

    public static String activation(OccurrenceAddress occurrence,
                                    ExecutionIndex frames) {
        return occurrence.id() + "|" + frames.render();
    }

    public String render() {
        return occurrence.render() + "/site:" + site + "/sidx:"
                + siteIndex.render() + "/att:" + attempt;
    }

    @Override
    Object[] parts() {
        return new Object[] {occurrence, site, siteIndex, attempt};
    }

    @Override
    public String toString() {
        return render();
    }
}
