package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeSet;

/**
 * WHERE THE WORKLOAD'S OWN CALLS FAIL (owner 2026-10-16).  Every fault door
 * an occurrence of the closure ran is a flip site (PIPELINE §7.2), except
 * where the workload's client calls a dependency of the system directly,
 * past the system under test: in a client root context only the doors of the
 * transports the system names fail ({@code --client-fault-transports}, Solr's
 * SOLR_HTTP and SOLR_HTTP2: a request to the cluster), and a door of the
 * system's catalog of another transport (the test's own ZooKeeper writes: a
 * configset upload, a {@code makePath}) is no flip site there.  SGF7 round 0
 * of solr-adhoc-10, -39 and -40 flipped 276 such doors, and none of their
 * replays ran the declared occurrence (the test failed in its setup), while
 * every fault root of the five Solr fault bugs is a server's ZooKeeper write
 * or the client's request to the cluster.  A door a demanded guard rests on
 * is flipped wherever it is (ClosurePlanner): only the blanket fault sites
 * are cut.
 */
final class ClientFaults {
    /** No cut: no system catalog, or no transport named. */
    static final ClientFaults NONE = new ClientFaults(
            Collections.<String>emptySet(), Collections.<String>emptySet());

    /** The system catalog's door methods whose transport a client root
     *  context does not fail. */
    private final Set<String> unfailed;
    /** The transports a client root context fails, as named. */
    private final Set<String> transports;

    private ClientFaults(Set<String> unfailed, Set<String> transports) {
        this.unfailed = unfailed;
        this.transports = transports;
    }

    /**
     * The cut the system's door catalog ({@code doors}, the rows with a
     * {@code method}) and the transports a client root context fails make;
     * {@link #NONE} when no transport is named.
     */
    static ClientFaults read(Path doors, Collection<String> transports)
            throws IOException {
        if (transports.isEmpty()) return NONE;
        if (doors == null) {
            throw new IllegalArgumentException("--client-fault-transports "
                    + "names the transports a client fails over the system's "
                    + "door catalog: pass --system-doors");
        }
        Set<String> unfailed = new LinkedHashSet<String>();
        for (JsonObject row : RowCodec.readJsonl(doors)) {
            String method = JsonFields.optionalString(row, "method");
            if (!method.isEmpty() && !transports.contains(
                    JsonFields.optionalString(row, "transport"))) {
                unfailed.add(method);
            }
        }
        return new ClientFaults(unfailed, new TreeSet<String>(transports));
    }

    /** Whether the fault door at {@code siteId} ({@code <method>#u<n>})
     *  fails in {@code occurrence}. */
    boolean fails(OccurrenceAddress occurrence, String siteId) {
        if (unfailed.isEmpty() || !clientRoot(occurrence)) return true;
        int unit = siteId.lastIndexOf('#');
        return !unfailed.contains(unit < 0 ? siteId
                : siteId.substring(0, unit));
    }

    /** Why a cut door is no flip site, for its round's gap row. */
    String why() {
        return "in the workload client's root contexts only the doors of "
                + transports + " fail (--client-fault-transports): a door "
                + "of another transport there is the client calling a "
                + "dependency past the system";
    }

    private static boolean clientRoot(OccurrenceAddress occurrence) {
        CausalContext context = occurrence.context();
        return context instanceof CausalContext.Root
                && ((CausalContext.Root) context).role() == Role.CLIENT;
    }
}
