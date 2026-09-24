package edu.uva.liftlab.graphchecker.contract;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * THE SHARED-STATE ACCESSES A REPLAY CAN HOLD: every access the weave put a
 * hook before, by the hook's woven site id, with the site the VM names the
 * same access by.
 *
 * <p>A read or write endpoint's site is the VM's -- the bytecode it stood at,
 * {@code class#method(desc)#bci:READ|WRITE} ({@link Endpoint#stateSite}) --
 * while a hook stands before a statement, whose bytecode index exists only
 * once the class is written.  INSTRUMENT reads the woven classes back and
 * states, for every access hook, the VM site of the access it stands before
 * ({@code causynth.AccessSiteTable}).  A replay names an access at its hook by
 * that site, the name its row will carry, and a world holds a read to a
 * writer only where both are sites of this table: a write no hook stands
 * before is one no replay could wait for.</p>
 *
 * <p>One file beside the woven classes, one row per hook: the woven site id,
 * a tab, the VM site.</p>
 */
public final class AccessSites {
    /** The file, in the directory of the woven classes. */
    public static final String FILE = "shared_access_sites.tsv";
    /** Where an iteration keeps its woven classes. */
    public static final String CLASSES = "instrumented-classes";

    private static final AccessSites NONE = new AccessSites(
            Collections.<String, String>emptyMap());

    private final Map<String, String> vmSiteOf;
    private final Set<String> held;

    private AccessSites(Map<String, String> vmSiteOf) {
        this.vmSiteOf = Collections.unmodifiableMap(vmSiteOf);
        this.held = Collections.unmodifiableSet(
                new LinkedHashSet<String>(vmSiteOf.values()));
    }

    /** The table of one directory of woven classes; none when absent. */
    public static AccessSites read(Path classes) throws IOException {
        Path file = classes == null ? null : classes.resolve(FILE);
        if (file == null || !Files.isRegularFile(file)) return NONE;
        Map<String, String> sites = new LinkedHashMap<String, String>();
        for (String line : Files.readAllLines(file, StandardCharsets.UTF_8)) {
            int tab = line.indexOf('\t');
            if (tab <= 0 || tab == line.length() - 1) continue;
            sites.put(line.substring(0, tab), line.substring(tab + 1));
        }
        return new AccessSites(sites);
    }

    /** The table of an iteration's woven classes. */
    public static AccessSites ofIteration(Path iteration) throws IOException {
        return read(iteration == null ? null : iteration.resolve(CLASSES));
    }

    /** Writes one table, woven site id to VM site, in the given order. */
    public static void write(Path classes, Map<String, String> sites)
            throws IOException {
        List<String> lines = new ArrayList<String>();
        for (Map.Entry<String, String> site : sites.entrySet()) {
            lines.add(site.getKey() + "\t" + site.getValue());
        }
        Files.write(classes.resolve(FILE), lines, StandardCharsets.UTF_8);
    }

    /** The VM site of the access one hook stands before, or null. */
    public String vmSite(String wovenSite) {
        return vmSiteOf.get(wovenSite);
    }

    /** Whether a hook stands before the access the VM names this way. */
    public boolean holds(String vmSite) {
        return held.contains(vmSite);
    }

    public boolean isEmpty() {
        return vmSiteOf.isEmpty();
    }
}
