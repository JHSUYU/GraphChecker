package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * CONTRACT-SPEC §2.1: the role one session states it ran as ({@code
 * manifest.json}, written when the session opens) -- the only answer to
 * "which session is the recording".  Never inferred from activations: a
 * FOCUSED replay that activated nothing is still FOCUSED.  At the run's end
 * it also counts the region entries unnamed work made, by {@code
 * <node>/region/<regionId>}: each opened no occurrence (IDENTITY §1), so no
 * row of the session states what ran there; and it states what a declared
 * root was read at where the replay minted none ({@link #concreteReadings})
 * and which declared roots held a value computed from others where it read
 * them ({@link #derivedRoots}), the names its nodes had only in this
 * run ({@link #runSpellings}), and the occurrences it ran for their doors
 * alone ({@link #doorsOnly}).  Schema 2; a manifest of another schema is
 * refused.
 */
public final class SessionManifest {
    /** What a session ran as: the recording, one counterfactual of it, or
     *  the recording's world with the declared occurrence's branches
     *  forced to the throw (PIPELINE §7.10), whose rows are read only as
     *  its forced path. */
    public enum Role { SEED, FOCUSED, FORCED }

    public static final String KIND = "SESSION_MANIFEST";
    /** The schema this contract reads and writes. */
    public static final int SCHEMA = 2;

    private final String sessionId;
    private final Role role;
    private final List<String> obligationIds;
    private final Map<String, Integer> unnamedEntries;
    private final Map<String, Map<String, String>> concreteReadings;
    private final Set<String> derivedRoots;
    private final RunSpellings runSpellings;
    private final Set<String> doorsOnly;

    private SessionManifest(String sessionId, Role role,
                            List<String> obligationIds,
                            Map<String, Integer> unnamedEntries,
                            Map<String, Map<String, String>> readings,
                            Set<String> derived, Map<String, String> spelled,
                            Set<String> doorsOnly) {
        this.sessionId = sessionId;
        this.role = role;
        this.obligationIds = Collections.unmodifiableList(obligationIds);
        this.unnamedEntries = Collections.unmodifiableMap(
                new TreeMap<String, Integer>(unnamedEntries));
        Map<String, Map<String, String>> sorted =
                new TreeMap<String, Map<String, String>>();
        for (Map.Entry<String, Map<String, String>> root
                : readings.entrySet()) {
            sorted.put(root.getKey(), Collections.unmodifiableMap(
                    new TreeMap<String, String>(root.getValue())));
        }
        this.concreteReadings = Collections.unmodifiableMap(sorted);
        this.derivedRoots = Collections.unmodifiableSet(
                new TreeSet<String>(derived));
        this.runSpellings = RunSpellings.of(spelled);
        this.doorsOnly = Collections.unmodifiableSet(
                new TreeSet<String>(doorsOnly));
    }

    /** Obligation ids come from the worker's {@code focused_task.jsonl}. */
    public static SessionManifest of(String sessionId, Role role,
                                     List<String> obligationIds) {
        List<String> ids = new ArrayList<String>();
        if (obligationIds != null) {
            for (String id : obligationIds) {
                String stated = Fields.text(id, "obligationId");
                if (!ids.contains(stated)) ids.add(stated);
            }
        }
        return new SessionManifest(Fields.text(sessionId, "sessionId"),
                Fields.required(role, "role"), ids,
                Collections.<String, Integer>emptyMap(),
                Collections.<String, Map<String, String>>emptyMap(),
                Collections.<String>emptySet(),
                Collections.<String, String>emptyMap(),
                Collections.<String>emptySet());
    }

    /** This manifest, with what only the run's end can state. */
    public SessionManifest atClose(Map<String, Integer> entries,
                                   Map<String, Map<String, String>> readings,
                                   Set<String> derived,
                                   Map<String, String> spelled,
                                   Set<String> doorsOnly) {
        return new SessionManifest(sessionId, role, obligationIds,
                entries == null ? Collections.<String, Integer>emptyMap()
                        : entries,
                readings == null
                        ? Collections.<String, Map<String, String>>emptyMap()
                        : readings,
                derived == null ? Collections.<String>emptySet() : derived,
                spelled == null ? Collections.<String, String>emptyMap()
                        : spelled,
                doorsOnly == null ? Collections.<String>emptySet()
                        : doorsOnly);
    }

    /**
     * The rendered occurrences this replay ran for their doors alone (a
     * control producer's or a store fetch's task, {@code
     * RuntimeSelectedRegionFinalizer#DOORS_ONLY}): their guards and roots ran
     * paused, so this session captured no value of them ({@code
     * explore.ClosurePlanner#plan}).
     */
    public Set<String> doorsOnly() {
        return doorsOnly;
    }

    /**
     * Root id -> rendered occurrence -> the value a declared source held
     * when this replay first read it there, at an occurrence it ran
     * concretely and so minted no root for (CONTRACT-SPEC §2.1): what that
     * occurrence's rows were computed from, though no symbol stands for it.
     */
    public Map<String, Map<String, String>> concreteReadings() {
        return concreteReadings;
    }

    /**
     * The declared roots whose source already carried an expression where
     * this replay read it (a field computed from a clock's reading, say): a
     * value moved by other inputs, so no reading of it, anywhere, is the
     * root's own.
     */
    public Set<String> derivedRoots() {
        return derivedRoots;
    }

    /** The names this run's nodes had only in it, each standing for its
     *  node ({@link RunSpellings}); none where the run did not close. */
    public RunSpellings runSpellings() {
        return runSpellings;
    }

    /** Whether this session states it is the recording. */
    public boolean seed() {
        return role == Role.SEED;
    }

    /** Whether this session states it ran forced (PIPELINE §7.10). */
    public boolean forced() {
        return role == Role.FORCED;
    }

    /** The obligations this replay was handed, in the focus row's order. */
    public List<String> obligationIds() {
        return obligationIds;
    }

    public JsonObject toJson() {
        JsonObject json = new JsonObject();
        json.addProperty("schemaVersion", SCHEMA);
        json.addProperty("kind", KIND);
        json.addProperty("sessionId", sessionId);
        json.addProperty("role", role.name());
        JsonArray ids = new JsonArray();
        for (String id : obligationIds) {
            ids.add(id);
        }
        json.add("obligationIds", ids);
        JsonObject unnamed = new JsonObject();
        for (Map.Entry<String, Integer> entry : unnamedEntries.entrySet()) {
            unnamed.addProperty(entry.getKey(), entry.getValue());
        }
        json.add("unnamedEntries", unnamed);
        JsonObject readings = new JsonObject();
        for (Map.Entry<String, Map<String, String>> root
                : concreteReadings.entrySet()) {
            JsonObject at = new JsonObject();
            for (Map.Entry<String, String> reading
                    : root.getValue().entrySet()) {
                at.addProperty(reading.getKey(), reading.getValue());
            }
            readings.add(root.getKey(), at);
        }
        json.add("concreteReadings", readings);
        JsonArray derived = new JsonArray();
        for (String rootId : derivedRoots) {
            derived.add(rootId);
        }
        json.add("derivedRoots", derived);
        JsonObject spelled = new JsonObject();
        for (Map.Entry<String, String> spelling
                : runSpellings.asMap().entrySet()) {
            spelled.addProperty(spelling.getKey(), spelling.getValue());
        }
        json.add("runSpellings", spelled);
        JsonArray doors = new JsonArray();
        for (String occurrence : doorsOnly) {
            doors.add(occurrence);
        }
        json.add("doorsOnly", doors);
        return json;
    }

    /** Reads one manifest; another schema, or an absent or unknown role, is
     *  refused, never SEED. */
    public static SessionManifest fromJson(JsonObject json) {
        int schema = JsonFields.optionalInteger(json, "schemaVersion", -1);
        if (schema != SCHEMA) {
            throw new IllegalArgumentException("manifest states schema "
                    + schema + "; this contract reads schema " + SCHEMA);
        }
        String role = JsonFields.optionalString(json, "role");
        Role parsed;
        try {
            parsed = Role.valueOf(role);
        } catch (IllegalArgumentException unstated) {
            throw new IllegalArgumentException(
                    "manifest states no role this contract has: \"" + role
                            + "\"");
        }
        Map<String, Integer> unnamed = new TreeMap<String, Integer>();
        if (json.has("unnamedEntries")
                && json.get("unnamedEntries").isJsonObject()) {
            for (Map.Entry<String, com.google.gson.JsonElement> entry
                    : json.getAsJsonObject("unnamedEntries").entrySet()) {
                unnamed.put(entry.getKey(), entry.getValue().getAsInt());
            }
        }
        Map<String, Map<String, String>> readings =
                new TreeMap<String, Map<String, String>>();
        if (json.has("concreteReadings")
                && json.get("concreteReadings").isJsonObject()) {
            for (Map.Entry<String, com.google.gson.JsonElement> root
                    : json.getAsJsonObject("concreteReadings").entrySet()) {
                if (!root.getValue().isJsonObject()) continue;
                Map<String, String> at = new TreeMap<String, String>();
                for (Map.Entry<String, com.google.gson.JsonElement> reading
                        : root.getValue().getAsJsonObject().entrySet()) {
                    at.put(reading.getKey(),
                            reading.getValue().getAsString());
                }
                readings.put(root.getKey(), at);
            }
        }
        Map<String, String> spelled = new TreeMap<String, String>();
        if (json.has("runSpellings")
                && json.get("runSpellings").isJsonObject()) {
            for (Map.Entry<String, com.google.gson.JsonElement> spelling
                    : json.getAsJsonObject("runSpellings").entrySet()) {
                spelled.put(spelling.getKey(),
                        spelling.getValue().getAsString());
            }
        }
        SessionManifest manifest = of(
                JsonFields.optionalString(json, "sessionId"), parsed,
                JsonFields.strings(json, "obligationIds"));
        return new SessionManifest(manifest.sessionId, manifest.role,
                manifest.obligationIds, unnamed, readings,
                new TreeSet<String>(JsonFields.strings(json, "derivedRoots")),
                spelled,
                new TreeSet<String>(JsonFields.strings(json, "doorsOnly")));
    }

    @Override
    public String toString() {
        return role + " " + sessionId
                + (obligationIds.isEmpty() ? "" : " " + obligationIds);
    }
}
