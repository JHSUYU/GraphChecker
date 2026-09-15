package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.LocationKind;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ActiveRegion;
import edu.uva.liftlab.graphchecker.runtime.d3.D3Runtime;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;

/**
 * Publishes one finished activation as Design 3 rows.
 *
 * <p>One translation, run once per activation, from what the replay has
 * assembled -- its decisions, its write log, its mints and its anchor -- to
 * the per-kind row set the contract defines.  It reads only what the
 * activation already published, so nothing here changes the execution and
 * no row exists that the single-row result does not also state.</p>
 */
final class D3RowPublication {
    private D3RowPublication() {
    }

    /** Every row this activation can state, in the contract's shapes. */
    static void publish(ActiveRegion active) {
        if (active == null || !D3Runtime.open()) return;
        OccurrenceAddress occurrence = active.d3Address;
        if (occurrence == null) return;
        publishKind("decisions", active, occurrence);
        publishKind("roots", active, occurrence);
        publishKind("state", active, occurrence);
        publishKind("target", active, occurrence);
        D3Runtime.endActivation(active.token);
    }

    /**
     * One kind, and its own refusal.
     *
     * <p>A row kind that cannot be built is that kind's gap: publishing them
     * under one try left a refused read suppressing the anchor row of the
     * same activation, which reads afterwards as an occurrence that never
     * reached its target.</p>
     */
    private static void publishKind(String kind, ActiveRegion active,
                                    OccurrenceAddress occurrence) {
        try {
            if ("decisions".equals(kind)) {
                decisions(active, occurrence);
            } else if ("roots".equals(kind)) {
                roots(active, occurrence);
            } else if ("state".equals(kind)) {
                writes(active);
            } else {
                target(active, occurrence);
            }
        } catch (RuntimeException failure) {
            // The rows describe a run; a translation that throws must not
            // end one.  It says so instead, which is the difference between
            // "this run published no writes" and "this run made none".
            D3Runtime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    occurrence.render(),
                    "the " + kind + " rows of this activation could not be"
                            + " published: "
                            + ConcolicRegionRuntime.rootCause(failure));
        }
    }

    /**
     * One row per decision, with the predicate the taken arm satisfied.
     *
     * <p>The term is the satisfied predicate as published -- no second
     * negation anywhere -- and the outcome states which arm that was.</p>
     */
    private static void decisions(ActiveRegion active,
                                  OccurrenceAddress occurrence) {
        for (JsonObject mapping : active.branchMappings) {
            String siteId = optionalString(mapping, "siteId");
            int ordinal = optionalInteger(mapping, "occurrence", 1);
            long seq = optionalLongInteger(mapping, "vmEventId", 0L);
            // One branch event, one occurrence: the VM's event range is read
            // out per activation and overlaps every activation the branch
            // ran inside.
            if (!D3Runtime.claimEvent("decision",
                    seq + "#" + siteId + "#" + ordinal)) {
                continue;
            }
            // The row states the site, the arm it took and the predicate as
            // written; nothing here applies one to the other
            // (CONTRACT-SPEC §2), and nothing reads the old witness shapes.
            JsonObject written = object(mapping, "siteCondition");
            D3Runtime.decision(occurrence, seq, siteId, ordinal,
                    optionalBool(mapping, "outcome", false),
                    written.size() > 0 ? written : null);
        }
    }

    private static JsonObject predicate(JsonObject witness) {
        JsonElement satisfied = witness.get("sourceSatisfiedPredicate");
        return satisfied != null && satisfied.isJsonObject()
                ? satisfied.getAsJsonObject() : null;
    }

    /**
     * The roots this activation minted, and the placeholders it did not.
     *
     * <p>A DECLARED root is a marker, a clock or a configured source: the
     * case names it and the search may move it.  A region's declared input
     * is not a root at all -- it is a READ PLACEHOLDER, the symbol standing
     * for what that read returned -- and publishing it as a root is what
     * pins it: the composer pins every domain-less root to its recorded
     * value, and a placeholder that is pinned AND joined to its writer's
     * expression makes every moved valuation unsatisfiable.</p>
     */
    private static void roots(ActiveRegion active,
                              OccurrenceAddress occurrence) {
        Map<String, String[]> installed = mintedLocations(active);
        Set<String> stated = new LinkedHashSet<String>();
        for (JsonObject row : active.symbolizedRows) {
            String symbol = vmSymbol(row);
            if (symbol.isEmpty()) continue;
            stated.add(optionalString(row, "portId"));
            String sourceId = optionalString(row, "sourceId");
            // The kind is read off the declaration, once
            // (see #kindOf): a configured source states no javaType of its
            // own and carries it on the symbol it minted, which is why a
            // declared boolean root read INTEGRAL while the composer looked
            // for a range with two values in it.
            RootKind kind = kindOf(row);
            if (sourceId.isEmpty() && kind == RootKind.INTEGRAL) {
                placeholder(occurrence, row, symbol, installed);
                continue;
            }
            String rootId = sourceId.isEmpty()
                    ? optionalString(row, "portId") : sourceId;
            D3Runtime.rootMint(occurrence,
                    optionalLongInteger(row, "eventSeq", 0L), rootId, symbol,
                    kind, literal(optionalString(row, "recordedValue")),
                    optionalString(row, "domainMin"),
                    optionalString(row, "domainMax"), true);
        }
        refusedDeclarations(active, occurrence, stated);
    }

    /**
     * Every declared region input this activation never symbolized.
     *
     * <p>A declaration the replay silently does not reach is the one
     * failure mode that reads downstream as "this branch is concrete":
     * hdfs-17960's empty phi was exactly that, a declared read that neither
     * minted nor refused.  The row names the port so the absence is
     * answerable from the session rather than from a replay trace.</p>
     */
    private static void refusedDeclarations(ActiveRegion active,
                                            OccurrenceAddress occurrence,
                                            Set<String> stated) {
        for (ConcolicRegionRuntime.SymbolizeAction action
                : active.activation.symbolize) {
            if (!action.declaredSymbolicRoot
                    || stated.contains(action.symbol)) {
                continue;
            }
            D3Runtime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    action.symbol, "a declared region input was never"
                            + " symbolized in this activation: site="
                            + action.siteId + " cell=" + action.cell);
        }
    }

    /**
     * One declared region input, as the read it stands for.
     *
     * <p>The symbol is the placeholder the mint installed; the location is
     * the field it was installed on; the value is what the field held when
     * it was.  A reader joins it to the write of that location exactly as
     * it joins any other read.</p>
     */
    private static void placeholder(OccurrenceAddress occurrence,
                                    JsonObject row, String symbol,
                                    Map<String, String[]> installed) {
        String signature = optionalString(row, "fieldSignature");
        // A read placeholder, session-wide, so no activation's write log
        // offers the mint's own version as a write of that location.
        D3Runtime.placeholderSymbol(symbol);
        // The location is the VM's own -- owner rid, slot offset -- so this
        // read and every write of the same storage spell one location.
        // Naming the Java field signature instead left the read saying
        // AtomicInteger#value while the write log said
        // INSTANCE_FIELD/<rid>#<offset>.
        // The mint this row is of, found by the symbol when the row carries
        // the VM's own (an integral mint states its rawSymbol) and by the
        // name the runtime REQUESTED otherwise: the VM answers a request for
        // `field_<portId>` with `M_<sort>_field_<portId>`, so a reference
        // mint -- whose row states no rawSymbol and whose expression leaf is
        // the identity spelling `P_L'...'` -- is the same mint under the
        // same request.  One spelling per symbol: the row publishes the VM's
        // (which is what the version's expression and expressions.json
        // carry), never the identity leaf.
        String[] installedAt = installed.get(symbol);
        String minted = symbol;
        if (installedAt == null) {
            String requested = "_field_" + optionalString(row, "symbol");
            for (Map.Entry<String, String[]> mint : installed.entrySet()) {
                if (!mint.getKey().endsWith(requested)) continue;
                installedAt = mint.getValue();
                minted = mint.getKey();
                break;
            }
        }
        String locationKey = installedAt == null ? "" : installedAt[0];
        LocationId location = location(locationKey);
        // The version this read OBSERVED.  The mint's own version is not a
        // write -- nobody stored it, and no WriteRow states it (see
        // #mintStores) -- so the version the read observed is the last
        // REAL write of the location before it, which the VM's version log
        // already holds.  That is what makes this row a JOIN to the writer
        // occurrence: on hdfs-17960 the two deletion occurrences write the
        // counter and the anchor reads what they left.  When no write
        // precedes the mint the row states -1 and pins the plain decimal,
        // which is the never-neither rule and not an invented version.
        long observed = location == null ? ReadRow.UNKNOWN_VERSION
                : Long.parseLong(installedAt[2]);
        if (location == null) {
            JsonObject read = nestedRead(row.get("expression"), 0);
            locationKey = read == null ? ""
                    : locationKey(object(read, "location"));
            location = location(locationKey);
            observed = location == null ? ReadRow.UNKNOWN_VERSION
                    : versionOf(read);
        }
        if (location == null) {
            locationKey = signature;
            location = fieldLocation(signature);
        }
        if (location == null) {
            D3Runtime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    symbol, "a declared region input states no field to"
                            + " read: " + optionalString(row, "portId"));
            return;
        }
        String declared = javaDescriptor(optionalString(row, "javaType"));
        String sort = mintedSort(minted);
        if (!sort.isEmpty() && sort.charAt(0) != declared.charAt(0)) {
            // The mint symbolized the OBJECT, not the cell: on hdfs-17960
            // REGION.9492ec77 declares <Snapshot: int id> and the row came
            // back with the VM's reference symbol P_L'...Snapshot'_ beside
            // javaType I, so one row stated an int read and a reference
            // unknown.  A reader that declares the symbol by the row's type
            // and resolves it by the table's gets two sorts for one name,
            // which no lowering can hold; the run states the disagreement
            // instead of a row that hides it.
            D3Runtime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    minted, "a declared region input minted a " + sort
                            + "-sorted symbol for a " + declared + " cell ("
                            + optionalString(row, "fieldSignature")
                            + "), so this read states no one sort: "
                            + optionalString(row, "portId"));
            return;
        }
        String value = optionalString(row, "observedValue");
        if (value.isEmpty()) value = optionalString(row, "recordedValue");
        if (value.isEmpty() && declared.charAt(0) == 'L') {
            // A reference cell records no decimal.  What the run states of
            // it is the identity the VM spells on the leaf -- the same
            // spelling FieldAccess.concreteValue carries, so one identity
            // lowering serves both -- and "N" for null.
            String identity = symbolLeaf(row.get("expression"), 0);
            if (identity.startsWith("M_L'") || identity.startsWith("P_L'")
                    || "N".equals(identity)) {
                value = identity;
            }
        }
        if (observed < 0L && literal(value).isEmpty()) {
            D3Runtime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    symbol, "a declared region input states no value it"
                            + " read: " + optionalString(row, "portId"));
            return;
        }
        // One row per read EVENT.  Each declared port's mint is its own
        // read -- two calls of a declared accessor in one occurrence are two
        // values, and a `<Timer: long now()>.return` cell proves it -- so
        // the key is the event, not the cell: the occurrence, the location
        // and the event this mint is.  Keying it on the cell alone would
        // discard the second port's statement; keying it on the PLANNED
        // occurrenceId (what it did before) let one event through twice,
        // because two mints in one activation carry different planned ids,
        // and the anchor stated INSTANCE/2#24 twice in every session of the
        // P2f' corpus (seed seq 242/308, focused 185/209 and 208/210).
        long event = optionalLongInteger(row, "eventSeq", 0L);
        if (!D3Runtime.claimEvent("placeholder", occurrence.id() + "#"
                + locationKey + "#" + event)) {
            D3Runtime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    symbol, "this occurrence already states read event "
                            + event + " of " + locationKey
                            + ", so this mint publishes no second row for"
                            + " it: " + optionalString(row, "portId"));
            return;
        }
        D3Runtime.read(occurrence, event,
                Endpoint.stateSite(locationKey, "PLACEHOLDER", 0, false),
                location, observed, minted,
                declared, literal(value),
                optionalString(row, "siteIndex"),
                installedAt == null ? ReadRow.UNKNOWN_VERSION
                        : Long.parseLong(installedAt[1]));
    }

    /**
     * The sort the VM spelled into one of its symbols, or {@code ""}.
     *
     * <p>A VM symbol carries its own sort: {@code M_I_field_...},
     * {@code M_Z_field_...}, {@code M_L_field_...}, {@code P_L'...'_}.  The
     * SORT is what has to agree with the cell -- L against any reference
     * descriptor, I against I -- because a reference symbol does not spell
     * which class the cell is declared as, and demanding the whole
     * descriptor refused every reference mint (P2l).  A symbol the runtime
     * made instead ({@code INSTANCE_FIELD/2#24@v178}) spells no sort and
     * claims none, so nothing is inferred from its absence.</p>
     */
    private static String mintedSort(String symbol) {
        String name = safe(symbol);
        if (name.length() < 4 || name.charAt(1) != '_') return "";
        char sort = name.charAt(2);
        char after = name.charAt(3);
        if (after != '_' && after != '\'') return "";
        return "ZBCSIJFDL".indexOf(sort) < 0 ? "" : String.valueOf(sort);
    }

    /**
     * Whether one symbol is a mint of THIS activation's declared inputs.
     *
     * <p>A version whose whole value is a bare symbol is not by itself a
     * mint: the VM writes a named reference's identity the same way
     * ({@code M_L'org/apache/...FsImage...'}), and a field assigned a
     * symbolized object carries that object's symbol.  Treating every such
     * version as a mint suppressed four real writes of hdfs-17960 --
     * INSTANCE/39#96@226, 35#64@233, 43#96@251, 37#64@263 -- and the reads
     * that observed them lost their writer, which took the anchor's
     * admitted paths from 2 to 0.  A mint is a symbol a DECLARED INPUT of
     * this activation asked for: the VM answers a request for
     * {@code field_<portId>} with {@code M_<sort>_field_<portId>}, and a row
     * that knows its own {@code rawSymbol} states it outright.  The key the
     * suppression and {@code mintVersion} share is still (location,
     * version); this is only which versions are mints at all.</p>
     */
    private static boolean declaredMint(ActiveRegion active, String symbol) {
        for (JsonObject row : active.symbolizedRows) {
            if (symbol.equals(optionalString(row, "rawSymbol"))) return true;
            String requested = optionalString(row, "symbol");
            if (!requested.isEmpty()
                    && symbol.endsWith("_field_" + requested)) {
                return true;
            }
        }
        return D3Runtime.isPlaceholderSymbol(symbol);
    }

    /**
     * Every mint store of this activation, keyed {@code location#version}.
     *
     * <p>The same scan {@link #mintedLocations} performs, keyed the other
     * way round: there by the symbol a placeholder row is found by, here by
     * the store a WriteRow would have been published for.  One rule decides
     * both -- a version whose whole value is the symbol a declared input
     * minted is that mint's shadow store, and nobody wrote it.</p>
     */
    private static Map<String, String> mintStores(ActiveRegion active) {
        Map<String, String> stores = new java.util.LinkedHashMap<String,
                String>();
        Set<String> minted = mintedLocations(active).keySet();
        if (minted.isEmpty()) return stores;
        // EVERY version whose whole value is a mint's symbol, not the first
        // one per symbol: mintedLocations keeps the first because a
        // placeholder row states one mint version, and a symbol that
        // reaches a second store would then have left that store published
        // as a write (v201 `M_L_field_REGION.692d5ed3...` survived exactly
        // that way).  A store is a store wherever it stands.
        for (JsonObject record : active.sharedStateRecords.values()) {
            String locationKey = optionalString(record, "locationKey");
            if (location(locationKey) == null) continue;
            for (JsonElement element
                    : array(object(record, "envelope"), "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject version = element.getAsJsonObject();
                long id = optionalLongInteger(version, "fieldVersionId", -1L);
                JsonElement written = version.get("expression");
                if (id < 0L || written == null || !written.isJsonObject()) {
                    continue;
                }
                JsonObject node = written.getAsJsonObject();
                if (!optionalString(node, "_type").contains("Symbol")) {
                    continue;
                }
                String symbol = optionalString(node, "_exp");
                if (minted.contains(symbol) && declaredMint(active, symbol)) {
                    stores.put(locationKey + "#" + id, symbol);
                }
            }
        }
        return stores;
    }

    /**
     * Where the VM says each minted symbol lives: symbol -&gt; location key.
     *
     * <p>A mint installs a symbol INTO a field the VM versions, so the
     * write log already names the location and the exact version whose
     * whole value that symbol is -- hdfs-17960's counter is version 172 of
     * {@code INSTANCE_FIELD/19#24}, and the anchor's own branch reads that
     * version.  Only a version whose expression IS the symbol counts (a
     * later version computed FROM it is a different value), and the first
     * such version wins.</p>
     */
    private static Map<String, String[]> mintedLocations(ActiveRegion active) {
        Map<String, String[]> bySymbol =
                new java.util.LinkedHashMap<String, String[]>();
        for (JsonObject record : active.sharedStateRecords.values()) {
            String locationKey = optionalString(record, "locationKey");
            if (location(locationKey) == null) continue;
            for (JsonElement element
                    : array(object(record, "envelope"), "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject version = element.getAsJsonObject();
                long id = optionalLongInteger(version, "fieldVersionId", -1L);
                JsonElement written = version.get("expression");
                if (id < 0L || written == null || !written.isJsonObject()) {
                    continue;
                }
                JsonObject node = written.getAsJsonObject();
                if (!optionalString(node, "_type").contains("Symbol")) {
                    continue;
                }
                String symbol = optionalString(node, "_exp");
                if (symbol.isEmpty() || !declaredMint(active, symbol)) {
                    continue;
                }
                // Only a write EARLIER than the mint is the one the read
                // observed; a later store is a value this read never saw.
                long observed = -1L;
                for (JsonElement candidate
                        : array(object(record, "envelope"), "versions")) {
                    if (!candidate.isJsonObject()) continue;
                    JsonObject other = candidate.getAsJsonObject();
                    long otherId = optionalLongInteger(other,
                            "fieldVersionId", -1L);
                    JsonElement value = other.get("expression");
                    boolean symbolLeaf = value != null
                            && value.isJsonObject()
                            && optionalString(value.getAsJsonObject(),
                            "_type").contains("Symbol");
                    if (!symbolLeaf && otherId >= 0L && otherId < id
                            && otherId > observed) {
                        observed = otherId;
                    }
                }
                if (!bySymbol.containsKey(symbol)) {
                    bySymbol.put(symbol, new String[]{locationKey,
                            Long.toString(id), Long.toString(observed)});
                }
            }
        }
        return bySymbol;
    }

    /** {@code <Class: type field>} as the location it names. */
    private static LocationId fieldLocation(String fieldSignature) {
        String signature = safe(fieldSignature);
        int owner = signature.indexOf(':');
        int field = signature.lastIndexOf(' ');
        if (!signature.startsWith("<") || owner <= 1 || field <= owner) {
            return null;
        }
        return LocationId.of(LocationKind.INSTANCE,
                signature.substring(1, owner),
                signature.substring(field + 1).replace(">", ""));
    }

    /** A source type name as the JVM descriptor a row states. */
    private static String javaDescriptor(String javaType) {
        String type = safe(javaType);
        if (type.isEmpty()) return "Ljava/lang/Object;";
        if (type.length() == 1) return type;
        if ("boolean".equals(type)) return "Z";
        if ("byte".equals(type)) return "B";
        if ("char".equals(type)) return "C";
        if ("short".equals(type)) return "S";
        if ("int".equals(type)) return "I";
        if ("long".equals(type)) return "J";
        if ("float".equals(type)) return "F";
        if ("double".equals(type)) return "D";
        return "L" + type.replace('.', '/') + ";";
    }

    /**
     * The VM's constant spelling as the literal it stands for.
     *
     * <p>{@code Y_I_119992} is the VM's name for the int constant 119992 --
     * {@code Y} marks a concrete value, the letter after it is the JVM type
     * and the rest is the value.  A row states the value.</p>
     */
    static String literal(String value) {
        String stated = safe(value);
        if (stated.length() > 4 && stated.charAt(0) == 'Y'
                && stated.charAt(1) == '_' && stated.charAt(3) == '_') {
            return stated.substring(4);
        }
        return stated;
    }

    /**
     * The one spelling of a symbol.
     *
     * <p>A row's symbol and the symbol leaf inside the expressions the
     * same session publishes have to be the same string: the composer
     * binds a root by finding its name in a lowered term, and a row that
     * names {@code REGION.r.in.uuid} while every term says {@code
     * M_J_field_REGION.r.in.uuid.occ.<hash>_java/lang/Long} binds
     * nothing.  The VM's name is the one that appears in the terms, so
     * that is the one the row states.</p>
     */
    private static String vmSymbol(JsonObject row) {
        String raw = optionalString(row, "rawSymbol");
        if (!raw.isEmpty()) return raw;
        // A configured source mints through the VM's own label and states
        // no raw symbol of its own; the expression it published names it.
        String leaf = symbolLeaf(row.get("expression"), 0);
        return leaf.isEmpty() ? optionalString(row, "symbol") : leaf;
    }

    /** The first symbol leaf an expression states, or {@code ""}. */
    private static String symbolLeaf(JsonElement node, int depth) {
        if (node == null || node.isJsonNull() || depth > 8) return "";
        if (node.isJsonArray()) {
            for (JsonElement element : node.getAsJsonArray()) {
                String found = symbolLeaf(element, depth + 1);
                if (!found.isEmpty()) return found;
            }
            return "";
        }
        if (!node.isJsonObject()) return "";
        JsonObject object = node.getAsJsonObject();
        if (optionalString(object, "_type").contains("Symbol")) {
            return optionalString(object, "_exp");
        }
        for (Map.Entry<String, JsonElement> member : object.entrySet()) {
            String found = symbolLeaf(member.getValue(), depth + 1);
            if (!found.isEmpty()) return found;
        }
        return "";
    }

    /**
     * What kind of root one mint row states.
     *
     * <p>A clock declares its callee, a marker mints a boolean, everything
     * else is integral.  The kind decides how the composer may move it --
     * a clock is unbounded with a floor, a marker has two values -- so it
     * is read from the declaration, never guessed from the value.</p>
     */
    private static RootKind kindOf(JsonObject row) {
        if (!optionalString(row, "declaredCallee").isEmpty()) {
            return RootKind.CLOCK;
        }
        String javaType = javaTypeOf(row);
        return "Z".equals(javaType) || "boolean".equals(javaType)
                ? RootKind.MARKER : RootKind.INTEGRAL;
    }

    /**
     * The Java type a mint row states, or the one its expression does.
     *
     * <p>A configured source mints through the VM's own label and states
     * no type of its own; the symbol it minted carries it.  Without this
     * a boolean configured root -- hdfs-17960's
     * {@code HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED} -- is published
     * INTEGRAL, and a composer then looks for a range where there are two
     * values.</p>
     */
    private static String javaTypeOf(JsonObject row) {
        String stated = optionalString(row, "javaType");
        return stated.isEmpty() ? symbolType(row.get("expression"), 0)
                : stated;
    }

    /** The type of the first symbol leaf an expression states. */
    private static String symbolType(JsonElement node, int depth) {
        if (node == null || node.isJsonNull() || depth > 8) return "";
        if (node.isJsonArray()) {
            for (JsonElement element : node.getAsJsonArray()) {
                String found = symbolType(element, depth + 1);
                if (!found.isEmpty()) return found;
            }
            return "";
        }
        if (!node.isJsonObject()) return "";
        JsonObject object = node.getAsJsonObject();
        if (optionalString(object, "_type").contains("Symbol")) {
            return optionalString(object, "_java_type");
        }
        for (Map.Entry<String, JsonElement> member : object.entrySet()) {
            String found = symbolType(member.getValue(), depth + 1);
            if (!found.isEmpty()) return found;
        }
        return "";
    }

    /**
     * One row per write version, and one per read the expressions state.
     *
     * <p>The write log is by location and version; the reads are the
     * {@code ReadFromExpression} nodes inside the expressions this
     * activation published, each of which names the version it observed.
     * Both halves of an endpoint come from the run itself: the VM states the
     * bytecode site of every version and read it logs (REPORT-VM21), and the
     * frames those events stood on come from the activation's own frame
     * journal, aligned to the event id (FrameJournal).  The row belongs to
     * the activation that PERFORMED the event, which the VM also states, not
     * to this one -- this activation is only the one whose read-out found the
     * event first (see {@link #performer}).</p>
     */
    private static void writes(ActiveRegion active) {
        // One activation, one population of reads: the same node is reached
        // from many versions of one location, and a row per reachable path
        // would count one read many times.
        Set<String> published = new LinkedHashSet<String>();
        Map<JsonElement, Boolean> seen =
                new IdentityHashMap<JsonElement, Boolean>();
        // The mint stores of this activation, by the one key the row's
        // mintVersion is: (location, version).  A declared region input is a
        // READ, so its store is no write and states no WriteRow -- and the
        // key is the store itself, never the spelling of its symbol: the
        // mint row's leaf reads `P_L'...'` where the version the VM
        // published carries `M_L'...'`, so a symbol-set test let five
        // "writes nobody performed" through (v86 the MARKER root's store,
        // v203/v210/v269/v276 the FsImage reference mints).
        Map<String, String> mints = mintStores(active);
        // The read log first, and for every location: a read node inside one
        // location's value is a read OF ANOTHER location, and the activation
        // that logged it is what its own log record states.
        for (JsonObject record : active.sharedStateRecords.values()) {
            indexLoggedEvents(record);
        }
        for (JsonObject record : active.sharedStateRecords.values()) {
            String locationKey = optionalString(record, "locationKey");
            LocationId location = location(locationKey);
            if (location == null) continue;
            JsonObject envelope = object(record, "envelope");
            for (JsonElement element : array(envelope, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject version = element.getAsJsonObject();
                long id = optionalLongInteger(version, "fieldVersionId", -1L);
                if (id < 0L
                        || mints.containsKey(locationKey + "#" + id)) {
                    continue;
                }
                if (!D3Runtime.claimEvent("write", locationKey + "#" + id)) {
                    continue;
                }
                JsonElement expression = version.get("expression");
                JsonObject written =
                        expression != null && expression.isJsonObject()
                                ? expression.getAsJsonObject() : null;
                OccurrenceAddress performer = performer(version, locationKey,
                        id, true);
                if (performer != null) {
                    D3Runtime.write(performer, id,
                            loggedSite(version, locationKey, id, true),
                            location, id, written, "",
                            loggedFrames(version, locationKey, id, true));
                }
                collect(expression, published, seen);
            }
        }
        for (JsonObject mapping : active.branchMappings) {
            collect(mapping.get("witness"), published, seen);
        }
    }

    /**
     * What the VM's log says about every event of one location.
     *
     * <p>Session-wide and keyed by event id, which is one monotone counter
     * for versions and reads alike: a {@code ReadFromExpression} node names
     * its read event id but not the activation that ran it, and the log
     * record of the same event does.  Populated from the read-out every
     * activation already performs -- the VM returns each selected location's
     * complete version and read log -- so nothing is asked of the engine
     * twice and no event is looked up before its log is seen.</p>
     */
    private static void indexLoggedEvents(JsonObject record) {
        JsonObject envelope = object(record, "envelope");
        for (JsonElement element : array(envelope, "versions")) {
            if (!element.isJsonObject()) continue;
            index(element.getAsJsonObject(), "fieldVersionId");
        }
        for (JsonElement element : array(envelope, "reads")) {
            if (!element.isJsonObject()) continue;
            index(element.getAsJsonObject(), "readEventId");
        }
    }

    private static void index(JsonObject node, String idKey) {
        long id = optionalLongInteger(node, idKey, -1L);
        if (id < 0L) return;
        LOGGED.putIfAbsent(Long.valueOf(id), new Logged(node));
    }

    /**
     * What one logged event states about itself: where, and under which
     * activation.
     *
     * <p>Only these fields, not the log record: a record carries the whole
     * value expression of its version, and keeping every record of the
     * session alive to answer "which activation ran event 77" would retain
     * every expression tree the run ever published.</p>
     */
    private static final class Logged {
        private final long activation;
        private final String className;
        private final String method;
        private final String descriptor;
        private final int bci;

        private Logged(JsonObject node) {
            this.activation = optionalLongInteger(node,
                    "regionEnterEventId", -1L);
            JsonObject site = object(node, "site");
            this.className = site == null ? ""
                    : optionalString(site, "className");
            this.method = site == null ? ""
                    : optionalString(site, "methodName");
            this.descriptor = site == null ? ""
                    : optionalString(site, "methodDescriptor");
            this.bci = site == null ? -1
                    : optionalInteger(site, "bci", -1);
        }

        private boolean states() {
            return !className.isEmpty() && !method.isEmpty();
        }
    }

    /** Every logged event of this session, by version or read event id. */
    private static final Map<Long, Logged> LOGGED =
            new java.util.concurrent.ConcurrentHashMap<Long, Logged>();

    /**
     * The one spelling of a logged event's site.
     *
     * <p>The components are the VM's own ({@code site} on every version,
     * read record and {@code ReadFromExpression}); the class is put in source
     * form here, which is the one place a VM name is converted, and the
     * descriptor travels because two overloads of one name are two methods.
     * An event the VM states no site for is named as a gap and spelled by
     * its location, which distinguishes nothing and says so.</p>
     */
    private static String loggedSite(JsonObject node, String locationKey,
                                     long eventId, boolean write) {
        Logged site = statedSite(node, eventId);
        if (site == null) {
            D3Runtime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    locationKey + "#" + eventId,
                    "the VM states no bytecode site for this "
                            + (write ? "version" : "read")
                            + ", so the endpoint's site is its location and"
                            + " distinguishes no event of it");
            return Endpoint.stateSite(locationKey, "UNSTATED_SITE", 0, write);
        }
        return Endpoint.stateSite(site.className.replace('/', '.'),
                site.method, site.descriptor, Math.max(0, site.bci), write);
    }

    /** The site this event states: its own, or its log record's. */
    private static Logged statedSite(JsonObject node, long eventId) {
        Logged own = node == null ? null : new Logged(node);
        if (own != null && own.states()) return own;
        Logged record = eventId < 0L ? null
                : LOGGED.get(Long.valueOf(eventId));
        return record != null && record.states() ? record : null;
    }

    /**
     * The occurrence that performed one logged event, or null with a gap.
     *
     * <p>The VM names the activation on every record it keeps, and that
     * activation is what the row is a row OF: a read the deletion region
     * made is not a read of the occurrence that happened to publish the
     * location's log first, and a path through the publisher would carry a
     * read it never performed.  An event whose activation this session has
     * no occurrence for states so and publishes no row -- attributing it to
     * the publisher is the thing this replaces.</p>
     */
    private static OccurrenceAddress performer(JsonObject node,
                                               String locationKey,
                                               long eventId, boolean write) {
        long activation = loggedActivation(node, eventId);
        OccurrenceAddress performer = D3Runtime.occurrenceAt(activation);
        if (performer != null) return performer;
        D3Runtime.gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                locationKey + "#" + eventId,
                "this " + (write ? "version" : "read") + " states activation "
                        + activation + ", which is no activation of this"
                        + " session, so the run cannot say which occurrence"
                        + " performed it and states no row for it");
        return null;
    }

    /** The activation the event states, its own or its log record's. */
    private static long loggedActivation(JsonObject node, long eventId) {
        long activation = optionalLongInteger(node, "regionEnterEventId", -1L);
        if (activation > 0L) return activation;
        Logged record = eventId < 0L ? null
                : LOGGED.get(Long.valueOf(eventId));
        return record == null ? -1L : record.activation;
    }

    /**
     * The frames one logged event stood on, or {@code ""} with a gap.
     *
     * <p>The event states the activation it ran inside
     * ({@code regionEnterEventId}) and its own id; the journal of that
     * activation states the frames its thread stood on at that point of the
     * session's event clock.  A node that carries no log record of its own
     * takes the activation from the record of the same event id.</p>
     */
    private static String loggedFrames(JsonObject node, String locationKey,
                                       long eventId, boolean write) {
        long activation = loggedActivation(node, eventId);
        String frames = D3Runtime.framesOf(activation, eventId);
        // "" is placed on no frames -- the store or read is in the region's
        // own method -- and the bci of the site is then what distinguishes
        // it.  Only an event the journal could not place is a gap.
        if (frames != null) return frames;
        D3Runtime.gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                locationKey + "#" + eventId,
                "this " + (write ? "version" : "read")
                        + (activation <= 0L
                        ? " states no region activation, so no frame journal"
                        + " can place it"
                        : " ran under activation " + activation
                        + " with no frame journal entry below its event id")
                        + "; the endpoint carries the empty site index");
        return "";
    }

    /**
     * Every read one expression tree states, by the version it observed.
     *
     * <p>Iteratively, over an explicit stack: a container's expression nests
     * one relation per operation the recording saw, which on hdfs-17960's
     * snapshot list is hundreds deep -- a recursion guard cuts the walk
     * before the reads, and publishing no read row reads afterwards as a
     * path that read nothing.</p>
     */
    private static void collect(JsonElement root, Set<String> published,
                                Map<JsonElement, Boolean> seen) {
        if (root == null) return;
        java.util.Deque<JsonElement> pending =
                new java.util.ArrayDeque<JsonElement>();
        pending.push(root);
        while (!pending.isEmpty()) {
            JsonElement node = pending.pop();
            if (node == null || node.isJsonNull()
                    || node.isJsonPrimitive()) {
                continue;
            }
            if (seen.put(node, Boolean.TRUE) != null) continue;
            if (node.isJsonArray()) {
                for (JsonElement element : node.getAsJsonArray()) {
                    pending.push(element);
                }
                continue;
            }
            JsonObject object = node.getAsJsonObject();
            String type = optionalString(object, "_type");
            if ("ReadFromExpression".equals(type)) {
                readFrom(object, published);
            } else if ("FieldAccessExpression".equals(type)) {
                fieldAccess(object, published);
            }
            for (Map.Entry<String, JsonElement> member : object.entrySet()) {
                pending.push(member.getValue());
            }
        }
    }

    /** A read the write log covers: the location, and the version it saw. */
    private static void readFrom(JsonObject node, Set<String> published) {
        JsonObject where = object(node, "location");
        String locationKey = locationKey(where);
        LocationId location = location(locationKey);
        if (location == null) return;
        long observed = versionOf(node);
        long event = eventOf(node);
        String identity = readIdentity(locationKey, observed, event);
        if (!published.add(identity)) return;
        String symbol = optionalString(node, "_exp");
        if (symbol.isEmpty()) {
            // A guarded read names no symbol of its own: what it read is
            // the version of the location, and that is what the row says.
            symbol = locationKey + "@v" + observed;
        }
        String value = literal(concreteOf(node));
        if (observed < 0L && value.isEmpty()) {
            // Neither a version to join nor a value to pin: the row would
            // say nothing a reader could use, and saying so is the point.
            D3Runtime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    locationKey, "a read states neither the version it"
                            + " observed nor the value it returned");
            return;
        }
        if (!D3Runtime.claimRead(identity)) return;
        OccurrenceAddress performer = performer(node, locationKey, event,
                false);
        if (performer == null) return;
        D3Runtime.read(performer, event >= 0L ? event : Math.max(0L, observed),
                loggedSite(node, locationKey, event, false),
                location, observed, symbol,
                optionalString(node, "_java_type"), value,
                loggedFrames(node, locationKey, event, false));
    }

    /**
     * A read the log does not cover: the object read from and what its
     * field then held, which is the pair the VM states (REPORT15).
     *
     * <p>The value the VM states here is an expression, not always a
     * constant: a field read whose value came from another read carries
     * that read, and with it the version it observed and the location it
     * observed it at.  A row states the version when there is one and the
     * literal when there is not -- never neither -- and spells the
     * location the way the write log spells it, so the two sides of one
     * location join.</p>
     */
    private static void fieldAccess(JsonObject node,
                                    Set<String> published) {
        JsonElement value = node.get("concreteValue");
        if (value == null || value.isJsonNull()) return;
        String ownerClass = optionalString(node, "ownerClass");
        int offset = optionalInteger(node, "fieldOffset", -1);
        JsonObject read = nestedRead(value, 0);
        String locationKey = read == null ? ""
                : locationKey(object(read, "location"));
        LocationId location = location(locationKey);
        if (location == null) {
            locationKey = "INSTANCE_FIELD/" + ownerClass + "#" + offset;
            location = LocationId.of(LocationKind.INSTANCE,
                    ownerClass.isEmpty() ? "<unstated>" : ownerClass,
                    String.valueOf(offset));
        }
        long observed = versionOf(node);
        if (observed < 0L && read != null) observed = versionOf(read);
        long event = eventOf(node);
        if (event < 0L) event = eventOf(value);
        if (event < 0L && read != null) event = eventOf(read);
        String stated = literal(leaf(value, 0));
        if (observed < 0L && stated.isEmpty()) {
            D3Runtime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    locationKey, "a projected read states neither the"
                            + " version it observed nor the value it"
                            + " returned");
            return;
        }
        String identity = readIdentity(locationKey, observed, event);
        if (!published.add(identity)) return;
        String projected = optionalString(node, "_exp");
        if (projected.isEmpty()) {
            // One symbol per READ, not per field: the same name on every
            // read of one field is one unknown the whole run shares.
            projected = locationKey + (observed >= 0L ? "@v" + observed
                    : "@e" + event);
        }
        if (!D3Runtime.claimRead(identity)) return;
        OccurrenceAddress performer = performer(node, locationKey, event,
                false);
        if (performer == null) return;
        D3Runtime.read(performer, event >= 0L ? event : Math.max(0L, observed),
                loggedSite(node, locationKey, event, false),
                location, observed, projected,
                optionalString(node, "_java_type"), stated,
                loggedFrames(node, locationKey, event, false));
    }

    /**
     * One read event, wherever it is reached from.
     *
     * <p>A read happened once, inside one occurrence; the expression trees
     * of every activation that later used the value carry the same node,
     * and a row per tree counts one read many times.  The first activation
     * to publish it states it -- activations finish innermost first, so
     * that is the innermost region the read ran in.</p>
     */
    private static String readIdentity(String locationKey, long observed,
                                       long event) {
        return locationKey + "#" + observed + "#" + event;
    }

    /** The version a node observed, or {@code -1}. */
    private static long versionOf(JsonObject node) {
        JsonElement stated = node == null ? null : node.get("observedVersion");
        if (stated == null) return -1L;
        if (stated.isJsonObject()) {
            return optionalLongInteger(stated.getAsJsonObject(),
                    "fieldVersionId", -1L);
        }
        return stated.isJsonPrimitive() ? stated.getAsLong() : -1L;
    }

    /** The VM event a node names, or {@code -1}. */
    private static long eventOf(JsonElement node) {
        if (node == null || !node.isJsonObject()) return -1L;
        JsonObject object = node.getAsJsonObject();
        long read = optionalLongInteger(object, "readEventId", -1L);
        return read >= 0L ? read
                : optionalLongInteger(object, "eventId", -1L);
    }

    /** The read a value node states under the VM's boundary wrappers. */
    private static JsonObject nestedRead(JsonElement value, int depth) {
        if (value == null || !value.isJsonObject() || depth > 8) return null;
        JsonObject object = value.getAsJsonObject();
        if ("ReadFromExpression".equals(optionalString(object, "_type"))) {
            return object;
        }
        return nestedRead(object.get("expression"), depth + 1);
    }

    /** The literal a value node states, under the VM's wrappers. */
    private static String leaf(JsonElement value, int depth) {
        if (value == null || value.isJsonNull() || depth > 8) return "";
        if (value.isJsonPrimitive()) return value.getAsString();
        if (!value.isJsonObject()) return "";
        JsonObject object = value.getAsJsonObject();
        String spelling = optionalString(object, "_exp");
        if (!spelling.isEmpty()) return spelling;
        String nested = leaf(object.get("expression"), depth + 1);
        if (!nested.isEmpty()) return nested;
        return leaf(object.get("concreteValue"), depth + 1);
    }

    /** What a read node says the read returned, or {@code ""}. */
    private static String concreteOf(JsonObject node) {
        JsonElement value = node.get("concreteValue");
        if (value == null || value.isJsonNull()) {
            JsonObject version = object(node, "observedVersion");
            value = version.get("concreteValue");
        }
        if (value == null || value.isJsonNull()) return "";
        return value.isJsonObject()
                ? optionalString(value.getAsJsonObject(), "_exp")
                : value.getAsString();
    }

    /** {@code KIND/owner#slot}, as the VM states one location. */
    private static String locationKey(JsonObject location) {
        if (location == null || location.size() == 0) return "";
        String kind = optionalString(location, "locationKind");
        long owner = optionalLongInteger(location, "ownerSymRid", 0L);
        if (kind.isEmpty() || owner == 0L || !location.has("slot")) {
            return "";
        }
        return kind + "/" + owner + "#"
                + optionalInteger(location, "slot", 0);
    }

    /** The contract location one VM location key names. */
    private static LocationId location(String locationKey) {
        String key = safe(locationKey);
        int separator = key.indexOf('/');
        int slot = key.lastIndexOf('#');
        if (separator <= 0 || slot <= separator) return null;
        String kind = key.substring(0, separator);
        return LocationId.of(kindOfLocation(kind),
                key.substring(separator + 1, slot), key.substring(slot + 1));
    }

    private static LocationKind kindOfLocation(String kind) {
        if (kind.startsWith("STATIC")) return LocationKind.STATIC;
        if (kind.startsWith("ARRAY")) return LocationKind.ARRAY;
        if (kind.startsWith("MAP")) return LocationKind.MAP;
        return LocationKind.INSTANCE;
    }

    /**
     * The anchor, with phi in the FATAL polarity whichever arm ran.
     *
     * <p>The recorded decision's predicate is the arm this run took; the
     * task declares which arm is fatal.  So the row states the fatal arm of
     * that predicate and, separately, whether this run took it -- and no
     * reader downstream re-derives a polarity (the second negation is
     * exactly the bug the phi-polarity fix removed).</p>
     */
    private static void target(ActiveRegion active,
                               OccurrenceAddress occurrence) {
        ConcolicTaskPlan.RuntimeTask task = active.activation;
        JsonObject reach = active.targetReach;
        if (!task.declaresTargetBranch() && reach == null) return;
        boolean reached = reach != null;
        boolean observed = reached && optionalBool(reach, "outcome", false);
        // The fatal arm is the one the case declared; a seed task that
        // captured the reach without declaring the arm states the arm it
        // observed, which is a fact of the run rather than a derivation.
        boolean fatalArm = task.declaresTargetBranch()
                ? task.targetBranchRequiredOutcome : observed;
        String anchor = task.declaresTargetBranch()
                ? task.targetBranchLabel()
                : optionalString(reach, "siteId") + "#"
                        + optionalInteger(reach, "occurrence", 1);
        JsonObject condition = null;
        String site = task.declaresTargetBranch() ? task.targetBranchSite
                : optionalString(reach, "siteId");
        int ordinal = task.declaresTargetBranch()
                ? task.targetBranchOccurrence
                : optionalInteger(reach, "occurrence", 1);
        for (JsonObject mapping : active.branchMappings) {
            if (!site.equals(optionalString(mapping, "siteId"))) continue;
            if (optionalInteger(mapping, "occurrence", -1) != ordinal) {
                continue;
            }
            JsonObject witness = object(mapping, "witness");
            if (witness.size() > 0) condition = predicate(witness);
        }
        D3Runtime.target(occurrence,
                reach == null ? 0L : optionalLongInteger(reach, "vmEventId",
                        0L), anchor, condition, observed == fatalArm,
                reached && observed == fatalArm, reached);
    }
}
