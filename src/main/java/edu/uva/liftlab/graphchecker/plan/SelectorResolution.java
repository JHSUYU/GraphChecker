package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.Selector;

import java.util.Collections;
import java.util.List;
import java.util.function.Predicate;

/** IDENTITY §9: which occurrence a case's v1 {@link Selector} ({@code
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
        ActivationRow named = kth(seed == null
                        ? Collections.<ActivationRow>emptyList() : seed,
                activation -> names(selector, activation.occurrence()),
                selector.k());
        return named == null ? unresolved(selector) : named.occurrence();
    }

    /** THE k-th-match rule: the {@code k}-th of {@code candidates}, in order,
     *  that {@code names} holds for; null when fewer match. */
    public static <T> T kth(Iterable<T> candidates, Predicate<T> names,
                            int k) {
        int matched = 0;
        for (T candidate : candidates) {
            if (names.test(candidate) && ++matched == k) return candidate;
        }
        return null;
    }

    /** Whether {@code selector} names {@code occurrence}, k aside. */
    public static boolean names(Selector selector,
                                OccurrenceAddress occurrence) {
        return selector.matches(occurrence, apiOf(selector, occurrence));
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
    private static String apiOf(Selector selector,
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
