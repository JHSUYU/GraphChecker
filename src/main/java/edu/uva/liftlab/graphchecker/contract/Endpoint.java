package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.util.ArrayList;
import java.util.List;

/**
 * CONTRACT-SPEC §1, IDENTITY §4: one side of an interaction, {@code
 * (occurrence, site, siteIndex, attempt)}.  The site index (frames from
 * region entry to the site) replaces an ordinal, which moves when an
 * unrelated event is inserted.
 *
 * <p>Site: the declared port id (WIRE), or {@code <class>#<method>#<bci>:KIND}
 * spelled only by {@link #stateSite}, so writer and joiner cannot drift.
 * One endpoint does not identify an {@link Interaction}.</p>
 */
public final class Endpoint extends Value {
    private final OccurrenceAddress occurrence;
    private final String site;
    private final ExecutionIndex siteIndex;
    private final int attempt;
    /** {@link #id()}, cached: lookups ask every filed endpoint for it. */
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

    /**
     * The one spelling of a whole message's site: {@code <transport>#<half>},
     * or {@code <transport>#<half>:<verb>} where its door names the operation
     * the message asks for (a Hadoop RPC's {@code DatanodeProtocol.sendHeartbeat}),
     * so its endpoint's k counts messages asking for that operation and two
     * turns that send other operations first still name it alike (IDENTITY
     * §4).  A verb, like every site, spells no {@code /} or {@code @}.
     */
    public static String messageSite(String transport, String half,
                                     String verb) {
        String site = (transport == null ? "" : transport) + "#"
                + (half == null ? "" : half);
        String named = verb(verb);
        return named.isEmpty() ? site : site + ":" + named;
    }

    /**
     * A message's verb as a site spells it, {@code ""} for none: no {@code
     * /} or {@code @}, which separate an index's frames and a frame's k.
     */
    public static String verb(String verb) {
        if (verb == null) return "";
        if (verb.indexOf('/') >= 0 || verb.indexOf('@') >= 0) {
            throw new IllegalArgumentException("a message verb spells no '/'"
                    + " or '@': " + verb);
        }
        return verb;
    }

    /** The one spelling of a STATE endpoint's site, no descriptor stated. */
    public static String stateSite(String className, String method, int bci,
                                   boolean write) {
        return stateSite(className, method, "", bci, write);
    }

    /**
     * The one spelling of a STATE endpoint's site,
     * {@code <class>#<method><descriptor>#<bci>:<KIND>}.  {@code descriptor}
     * (e.g. {@code ()I}) keeps overloads apart; {@code ""} means none was
     * stated.  Normalizes nothing (the VM-log reader puts the class in source
     * form once).
     */
    public static String stateSite(String className, String method,
                                   String descriptor, int bci, boolean write) {
        String stated = descriptor == null ? "" : descriptor.trim();
        return Fields.text(className, "className") + "#"
                + Fields.text(method, "method") + stated + "#"
                + Fields.nonNegative(bci, "bci") + ":"
                + (write ? "WRITE" : "READ");
    }

    /**
     * The site of a location's INITIAL ({@code WriteRow#initial}) at the
     * STATE site of the access that first observed it: its own kind, so it
     * is no event of that access (a log a store starts states the INITIAL
     * and the store at one event).
     */
    public static String initialSite(String observedAt) {
        return observedAt.substring(0, observedAt.lastIndexOf(':') + 1)
                + "INITIAL";
    }

    public OccurrenceAddress occurrence() {
        return occurrence;
    }

    /** The declared port id (WIRE), the read/write site, or the allocation. */
    public String site() {
        return site;
    }

    /** The frames from the region entry to this event. */
    public ExecutionIndex siteIndex() {
        return siteIndex;
    }

    /** The retry number, 0 when the transport did not retry. */
    public int attempt() {
        return attempt;
    }

    /**
     * Trap: this digest is recursive (occurrence -> Anchor context ->
     * producer endpoint -> its occurrence), so one unreproduced link changes
     * the id.  Do not truncate the chain: producers that differ only in their
     * chain then collide (TOPOLOGY_DIVERGENCE).  The open fix is a
     * reproducible per-message ordinal digested in place of the chain.
     */
    public String id() {
        String digested = id;
        if (digested == null) {
            digested = ArtifactIO.digest(occurrence.id() + "/" + site + "/"
                    + siteIndex.hash() + "/" + attempt, 16);
            id = digested;
        }
        return digested;
    }

    /**
     * The method activation this event ran in: its occurrence and the frames
     * from the region entry, without the event's own {@code (site, k)} frame.
     * The unit a CONFIRM order gate holds ({@code runtime.Confirmation}).
     */
    public String activation() {
        return activation(occurrence, ExecutionIndex.of(activationFrames()));
    }

    /** The frames of {@link #activation()}: the site index without the
     *  event's own frame. */
    public List<Frame> activationFrames() {
        List<Frame> frames = siteIndex.frames();
        int last = frames.size() - 1;
        boolean eventFrame = last >= 0 && frames.get(last).callSite()
                .equals(site.replace('/', '.'));
        return eventFrame ? frames.subList(0, last) : frames;
    }

    /**
     * This endpoint at any turn of the loops on its path: its frames'
     * iteration counts dropped.  How many turns a loop that polls for a
     * write takes before the write lands is that write's timing.
     */
    public Endpoint anyTurn() {
        List<Frame> turned = new ArrayList<Frame>();
        for (Frame frame : siteIndex.frames()) {
            turned.add(Frame.of(frame.callSite(), 0));
        }
        return new Endpoint(occurrence, site, ExecutionIndex.of(turned),
                attempt);
    }

    /** This endpoint as every delivery of its occurrence's stored message
     *  states it ({@link OccurrenceAddress#anyDelivery}). */
    public Endpoint anyDelivery() {
        OccurrenceAddress delivered = occurrence.anyDelivery();
        return delivered == occurrence ? this
                : new Endpoint(delivered, site, siteIndex, attempt);
    }

    /** The one spelling of an activation key. */
    public static String activation(OccurrenceAddress occurrence,
                                    ExecutionIndex frames) {
        return occurrence.id() + "|" + frames.render();
    }

    /** The canonical spelling, for reports and refusals. */
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
