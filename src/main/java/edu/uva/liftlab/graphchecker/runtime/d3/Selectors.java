package edu.uva.liftlab.graphchecker.runtime.d3;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.Selector;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * Resolving a case's declared occurrence against the seed session.
 *
 * <p>IDENTITY-IMPL §D.  Humans do not write execution indexes: a case
 * declares the v1 spelling -- {@code node#epoch/region/REGION.x@src#epoch/api#k}
 * or {@code node#epoch/region/REGION.x#k} -- and the campaign resolves it
 * ONCE, against the session that recorded the run: same region, same api on
 * the incoming anchor when the selector gives one, k-th match in seed
 * order.  Everything downstream uses the resolved id and never the
 * string.</p>
 *
 * <p>Called from PLAN, which is the stage that reads the seed and elects the
 * anchor; {@code d3.explore}'s task planning calls the same method, so the
 * two ends cannot resolve one declaration differently.</p>
 */
public final class Selectors {
    private Selectors() {
    }

    /** Reads a v1 case declaration as a selector; never throws. */
    public static Selector parse(String declaration) {
        try {
            return OccurrenceAddress.parseSelector(Text.safe(declaration));
        } catch (RuntimeException notASelector) {
            return null;
        }
    }

    /**
     * The occurrence a selector names in one seed session, or {@code ""}.
     *
     * <p>The k-th match in the session's own order; fewer than k matches is
     * an empty answer the caller names, never a silent first match.</p>
     */
    public static String resolve(Selector selector, Path iteration,
                                 String sessionId) {
        OccurrenceAddress occurrence = resolveAddress(selector, iteration,
                sessionId);
        return occurrence == null ? "" : occurrence.id();
    }

    /** The same resolution, as the address itself. */
    public static OccurrenceAddress resolveAddress(Selector selector,
                                                   Path iteration,
                                                   String sessionId) {
        if (selector == null) return null;
        SessionDir session = SessionDir.of(iteration, sessionId);
        List<OccurrenceAddress> matches = new ArrayList<OccurrenceAddress>();
        try {
            for (JsonObject line : RowCodec.readJsonl(session.activations())) {
                ActivationRow row = RowCodec.readActivation(line);
                OccurrenceAddress address = row.occurrence();
                if (selector.matches(address, rpcApi(address))) {
                    matches.add(address);
                }
            }
        } catch (IOException unreadable) {
            return null;
        }
        return matches.size() >= selector.k()
                ? matches.get(selector.k() - 1) : null;
    }

    /** The api of the message that started this occurrence, or {@code ""}. */
    private static String rpcApi(OccurrenceAddress occurrence) {
        CausalContext context = occurrence.context();
        if (!(context instanceof CausalContext.Anchor)) return "";
        String site = ((CausalContext.Anchor) context).rpcSite();
        int api = site.lastIndexOf('#');
        return api < 0 ? site : site.substring(api + 1);
    }
}
