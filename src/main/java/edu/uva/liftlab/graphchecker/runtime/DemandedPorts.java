package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Which codec ports the plan demands (WIRE-CODEC §3.3, §4.2): the one thing
 * the static side hands the runtime about codecs.  A walk exports only the
 * leaves of demanded ports; a port only decides which values travel, never
 * which value was delivered.
 *
 * <p>SEED publishes the ports as {@code CODEC_PORT} catalog rows ({@link
 * CommunicationCatalogContract#CODEC_PORT}); {@link #configured} reads such
 * rows from the file {@link #PROPERTY} (else {@link #ENVIRONMENT}) names, and
 * only their {@code portId}.  Unnamed, no port is demanded and every codec
 * walk exports nothing.</p>
 */
interface DemandedPorts {
    String PROPERTY = "causynth.codec.ports";
    String ENVIRONMENT = "CAUSYNTH_CODEC_PORTS";

    /** Whether the port with this id ({@code codecPortId}) is demanded. */
    boolean demanded(String portId);

    /** The ports of the configured file of {@code CODEC_PORT} rows. */
    static DemandedPorts configured() throws IOException {
        String named = System.getProperty(PROPERTY);
        if (named == null || named.trim().isEmpty()) {
            named = System.getenv(ENVIRONMENT);
        }
        if (named == null || named.trim().isEmpty()) {
            return of(Collections.<String>emptySet());
        }
        Path file = Paths.get(named.trim());
        Set<String> ports = new LinkedHashSet<>();
        int line = 0;
        for (String text : Files.readAllLines(file, StandardCharsets.UTF_8)) {
            line++;
            if (text.trim().isEmpty()) continue;
            JsonElement row = JsonParser.parseString(text);
            JsonObject port = row.isJsonObject() ? row.getAsJsonObject()
                    : null;
            JsonElement kind = port == null ? null
                    : port.get(CommunicationCatalogContract.KIND);
            JsonElement id = port == null ? null
                    : port.get(CommunicationCatalogContract.PORT_ID);
            if (kind == null || !CommunicationCatalogContract.CODEC_PORT
                    .equals(kind.getAsString()) || id == null
                    || !CommunicationCatalogContract.declaredPortId(
                            id.getAsString())) {
                throw new IOException("codec ports at " + file + ":" + line
                        + " state a " + CommunicationCatalogContract.CODEC_PORT
                        + " row with its portId: " + text);
            }
            ports.add(id.getAsString());
        }
        return of(ports);
    }

    /** Exactly these ports. */
    static DemandedPorts of(Set<String> portIds) {
        Set<String> ports = Collections.unmodifiableSet(
                new LinkedHashSet<>(portIds));
        return ports::contains;
    }
}
