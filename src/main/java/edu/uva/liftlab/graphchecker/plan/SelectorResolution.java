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

/** IDENTITY-IMPL D: which occurrence a case's v1 {@link Selector} ({@code
 *  node#epoch0/region/REGION.x@src#epoch0/api#k}) names; resolved once, against
 *  the SEED, counting the k-th match in seed activation order. No match yields
 *  a degraded address (composition: DECLARATION_MISSING). The only resolver of
 *  "which occurrence did the case mean". */
public final class SelectorResolution {
    /** What an already-resolved address carries and a selector never does. */
    private static final String RESOLVED_MARKER = "/ctx:";

    private SelectorResolution() {
    }

    /** The occurrence {@code declared} (address or v1 selector) names among the
     *  seed's activations, in write order. */
    public static OccurrenceAddress resolve(String declared,
                                            List<ActivationRow> seed) {
        String value = declared == null ? "" : declared.trim();
        if (value.contains(RESOLVED_MARKER)) {
            // Already an id (resolved by PLAN or a previous manifest).
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

    /** The api of the message that started this occurrence, or ""; v1 apis
     *  match on the last path segment. */
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
