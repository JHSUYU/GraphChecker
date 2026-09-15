package edu.uva.liftlab.graphchecker.plan;


import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.Selector;
import edu.uva.liftlab.graphchecker.contract.SessionDir;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

/**
 * IDENTITY-IMPL D: which occurrence a case's declaration names.
 *
 * <p>A case declares its target in the v1 spelling a human can write --
 * {@code node#epoch0/region/REGION.x@src#epoch0/api#k} -- because nobody
 * writes an execution index by hand. That string is a {@link Selector}, not
 * an address: which component, which region, optionally which api the message
 * that started the occurrence arrived on, and which match. Resolving it
 * happens once per campaign, against the SEED session, because the seed is
 * the recording the declaration was written about. Afterwards the anchor
 * travels as an id and no later stage sees the declaration again.</p>
 *
 * <p>Seed order is the resolution order: activation rows are in the order the
 * seed replay reached them, which is what a case author counted. Deliberately
 * not the execution index's order -- an index sorts by call path, and "the
 * second checksum" means the second one that ran.</p>
 *
 * <p>A selector that matches nothing is not an exception. It resolves to a
 * degraded address of the region it names, which no session's rows equal, so
 * the composition answers DECLARATION_MISSING and the campaign reads why out
 * of an artifact instead of a stack trace.</p>
 *
 * <p>One home for this: the composer asked the same question first, because
 * PLAN did not yet, and two implementations of "which occurrence did the case
 * mean" is exactly the disagreement an identity is supposed to end.</p>
 */
public final class SelectorResolution {
    /** What an already-resolved address carries and a selector never does. */
    private static final String RESOLVED_MARKER = "/ctx:";

    private SelectorResolution() {
    }

    /**
     * The occurrence {@code declared} names among {@code seed}'s activations.
     *
     * @param declared a full rendered address, or a v1 selector string
     * @param seed     the seed session's activation rows, in write order
     */
    public static OccurrenceAddress resolve(String declared,
                                            List<ActivationRow> seed) {
        String value = declared == null ? "" : declared.trim();
        if (value.contains(RESOLVED_MARKER)) {
            // Already an id: PLAN resolved it, or a re-run passed back what a
            // previous manifest published.
            return OccurrenceAddress.parse(value);
        }
        Selector selector = OccurrenceAddress.parseSelector(value);
        int matched = 0;
        if (seed != null) {
            for (ActivationRow activation : seed) {
                OccurrenceAddress occurrence = activation.occurrence();
                if (!selector.matches(occurrence, apiOf(selector, occurrence))) {
                    continue;
                }
                if (++matched == selector.k()) return occurrence;
            }
        }
        return unresolved(selector);
    }

    /** The same resolution, reading the seed session off the iteration. */
    public static OccurrenceAddress resolve(String declared, Path iteration,
                                            String seedSession)
            throws IOException {
        SessionDir dir = SessionDir.of(iteration, seedSession);
        return resolve(declared, RowCodec.readAll(dir.activations(),
                RowCodec::readActivation));
    }

    /** Whether {@code occurrence} is one nothing in the seed matched. */
    public static boolean unresolved(OccurrenceAddress occurrence) {
        return occurrence != null && occurrence.context().isLost()
                && "unresolved".equals(occurrence.node().node());
    }

    private static OccurrenceAddress unresolved(Selector selector) {
        return OccurrenceAddress.of(selector.node() == null
                        ? NodeId.of("unresolved", 0) : selector.node(),
                selector.regionId(), CausalContext.of(Role.UNKNOWN),
                ExecutionIndex.empty());
    }

    /**
     * The api of the message that started this occurrence, or {@code ""}.
     *
     * <p>The contract will not guess an api out of a deployment's RPC static
     * site spelling, and is right not to; this is the rule for the spelling
     * the cases meet. A v1 declaration writes the api as the tail of the
     * source it came from, so the two are compared on their last path
     * segment: {@code …/striped-file-checksum} selects the site whose last
     * segment is {@code striped-file-checksum}, and an exact site spelling
     * still matches itself. The selector's own spelling is handed back where
     * the two name one api, so the contract's equality decides and this rule
     * only says which spellings are the same api.</p>
     */
    public static String apiOf(Selector selector,
                               OccurrenceAddress occurrence) {
        if (occurrence.context().form() != CausalContext.Form.ANCHOR) {
            return "";
        }
        String site = ((CausalContext.Anchor) occurrence.context()).rpcSite();
        if (selector.api() == null) return site;
        return sameApi(selector.api(), site) ? selector.api() : site;
    }

    private static boolean sameApi(String declared, String site) {
        if (declared.equals(site)) return true;
        String left = tail(declared);
        return !left.isEmpty() && left.equals(tail(site));
    }

    private static String tail(String value) {
        int slash = value.lastIndexOf('/');
        return slash < 0 ? value : value.substring(slash + 1);
    }
}
