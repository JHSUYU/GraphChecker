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

final class ClientFaults {
    static final ClientFaults NONE = new ClientFaults(
            Collections.<String>emptySet(), Collections.<String>emptySet());

    private final Set<String> unfailed;
    private final Set<String> transports;

    private ClientFaults(Set<String> unfailed, Set<String> transports) {
        this.unfailed = unfailed;
        this.transports = transports;
    }

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

    boolean fails(OccurrenceAddress occurrence, String siteId) {
        if (unfailed.isEmpty() || !clientRoot(occurrence)) return true;
        int unit = siteId.lastIndexOf('#');
        return !unfailed.contains(unit < 0 ? siteId
                : siteId.substring(0, unit));
    }

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
